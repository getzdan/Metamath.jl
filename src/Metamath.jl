__precompile__()
module Metamath

using Compat

import Base: empty!, show

export mmverify!

type MetamathException <: Exception
  text::AbstractString
end
metamath_error(x...) = throw(MetamathException(string(x...)))
metamath_warn(x...) = warn("(Metamath) ",x...)
macro warn_and_ret(rv,x...)
  :(metamath_warn($x...) ; return $rv)
end

typealias Expression Vector{Symbol}
typealias Hypothesis Pair{Expression,Bool}

# An axiom or theorem
immutable Assertion
  hypotheses::Vector{Symbol}
  disjvars::Set{Pair{Symbol,Symbol}}
  expression::Expression
  Assertion(expression) = new(Symbol[],Set{Pair{Symbol,Symbol}}(),expression)
end

type Scope
  activevariables::Set{Symbol}
  activehyp::Vector{Symbol}
  disjvars::Vector{Set{Symbol}}
  floatinghyp::Dict{Symbol,Symbol}
  Scope() = new(Set{Symbol}(),Symbol[],Set{Symbol}[],Dict{Symbol,Symbol}())
end

# An environment holding truths and definitions accumulated by verifier
immutable Environment
  filenames::Set{String}
  tokens::Vector{Symbol}
  compressedproofs::Vector{String}
  constants::Set{Symbol}
  hypotheses::Dict{Symbol,Hypothesis}
  variables::Set{Symbol}
  assertions::Dict{Symbol,Assertion}
  scopes::Vector{Scope}
  substitutionssrc::Vector{Symbol}
  substitutionsdst::Vector{Expression}
  dirty::Vector{Bool}
  Environment() = new(Set{String}(),Symbol[],String[],Set{Symbol}(),
    Dict{Symbol,Hypothesis}(), Set{Symbol}(), Dict{Symbol,Assertion}(),
    Scope[Scope()],Symbol[],Expression[],Bool[false])
end

"""a global Metamath.Environment variable for defualt use by mmverify!"""
const globalenv = Environment()

# true if label already used in hypotheses or assertions in env
labelused(env,label) = haskey(env.hypotheses,label) || haskey(env.assertions,label)

# return floating hypothesis in which variable appears
function getfloatinghyp(env,variable)
  for scope in env.scopes
    if haskey(scope.floatinghyp,variable)
      return scope.floatinghyp[variable]
    end
  end
  return :dummytoken
end

# Character set not allowed in Metamath labels
const tokenspecials = Set(['.','-','_'])

# true if ch is a Metamath whitespace
ismmws(ch) = return ch == ' ' || ch == '\n' || ch == '\t' || ch == '\f' || ch == '\r'
# true if sym represent a string which is legal Metamath label
islabeltoken(str) = findfirst(c->!(c in tokenspecials || isalnum(c)),str)==0
# true if str is a legal Metamath symbol
ismathsymboltoken(str::String) = findfirst(str,'$')==0
# true is sym represents a string which is legal Metamth symbol
ismathsymboltoken(sym::Symbol) = ismathsymboltoken(string(sym))
# true if c is not uppercase or question mark
isntupperorq(c) = !(isupper(c) || c=='?')
# true is str has only upper-case letters or question marks
containsonlyupperorq(str) = findfirst(isntupperorq,str)==0

# true if str is an active variable according to env
isactivevariable(env,str) = any(scope->str in scope.activevariables,env.scopes)
# true if str is an active hypothesis according to env
isactivehyp(env,str) = any(scope->str in scope.activehyp,env.scopes)

# true if str1 and str2 should be distinct according to env
function isdvr(env,str1,str2)
  if str1==str2
    return false
  end
  for scope in env.scopes
    for dvset in scope.disjvars
      if str1 in dvset && str2 in dvset
        return true
      end
    end
  end
  return false
end

# Output a string summary representation of an Environment type
function show(io::IO,env::Environment)
  print(io,"<Metamath environment: ")
  print(io,join([length(getfield(env,f)) for f in fieldnames(Environment)],","))
  print(io,">")
end
   
function readchar(io::IOBuffer)
  @inbounds c = io.data[io.ptr]
  io.ptr += 1
  return Char(c)
end

# Return a single token from buffer discarding surrounding whitespace.
function nexttoken(stream,buf::IOBuffer = IOBuffer())
  c = ' '
  while !eof(stream) && ismmws(c)
    c = readchar(stream)
  end
  while !ismmws(c)
    if c<'!' || c>'~'
      @warn_and_ret("","Invalid character read with code $(UInt8(c))")
    end
    write(buf,c)
    if eof(stream)
      break
    end
    c = readchar(stream)
  end
  return String(take!(buf))
end

# Parse filename into tokens and compressed proofs and store
# parsed output into environment. Discard comments and read
# other included files.
function readtokens!(env, filename; use_mmap::Bool=true)
  if filename in env.filenames
    return nothing
  else
    push!(env.filenames,filename)
  end

  isfile(filename) || throw(ArgumentError("\"$filename\" is not a valid or existing filename"))
  stream = IOBuffer(use_mmap ? Mmap.mmap(filename) : open(readbytes,filename))

  incomment = false
  infileinclusion = false
  newfilename = ""
  state = 0

  strtoken = ""
  buf = IOBuffer()
  compressedbuf = IOBuffer()
  while (strtoken = nexttoken(stream,buf))!=""
    if incomment
      if strtoken == "\$)"
        incomment = false
        continue
      end
      if !isempty(search(strtoken,"\$("))
        metamath_error("Character \$( found in comment")
      end
      if !isempty(search(strtoken,"\$)"))
        metamath_error("Character \$) found in comment")
      end
      continue
    end

    if strtoken=="\$("
      incomment = true
      continue
    end

    if infileinclusion
      if newfilename == ""
        if findfirst(strtoken,'$')!=0
          metamath_error("Filename contains a \$")
        end
        newfilename = strtoken
        continue
      else
        if strtoken != "\$]"
          metamath_error("Didn't find closing file inclusion delimeter")
        end
        readtokens(env,newfilename,use_mmap=user_mmap)
        newfilename = ""
        continue
      end
    end

    if strtoken == "\$["
      infileinclusion = true
      continue
    end

    if state == 0 && strtoken == "\$p"
      state = 1
    elseif state == 1 && strtoken == "\$="
      state = 2
    elseif state == 2 && strtoken == "("
      state = 3
    elseif state == 3 && strtoken == ")"
      state = 4
    elseif state == 4
      if strtoken != "\$."
        if !containsonlyupperorq(strtoken)
          metamath_error("Compressed proof $strtoken contains bogus character")
        end
        write(compressedbuf, strtoken)
      else
        push!(env.compressedproofs,String(take!(compressedbuf)))
        state = 0
      end
      continue
    elseif state > 0 && strtoken == "\$."
      state = 0
    end
    push!(env.tokens,Symbol(strtoken))
  end
  if !eof(stream)
    metamath_error("Error reading from $filename")
  end
  if incomment
    metamath_error("Unclosed comment in $filename")
  end
  if infileinclusion
    metamath_error("Unfinished file inclusion command in $filename")
  end
  if state > 0 || nb_available(compressedbuf) != 0
    metamath_error("Compressed proof parsing confused in $filename")
  end
  return nothing
end

# Construct Assertion from expression by determining mandatory
# hypotheses and disjoint variable restrictions. Assertion is inserted
# into environment and returned
function constructassertion(env,label, expression)
  assertion = Assertion(expression)
  varsused = Set{Symbol}()
  for token in expression
    if token in env.variables
      push!(varsused, token)
    end
  end
  for scope in reverse(env.scopes)
    for hyp in reverse(scope.activehyp)
      ind = Base.ht_keyindex(env.hypotheses,hyp)
      if ind != -1
        if last(env.hypotheses.vals[ind]) && (first(env.hypotheses.vals[ind])[2] in varsused)
          unshift!(assertion.hypotheses,hyp)
        elseif !last(env.hypotheses.vals[ind])
          unshift!(assertion.hypotheses,hyp)
          for token in first(env.hypotheses.vals[ind])
            if token in env.variables
              push!(varsused, token)
            end
          end
        end
      end
    end
  end
  varusedvec = collect(varsused)
  for scope in env.scopes
    for dvset in scope.disjvars
      dvec = intersect(varusedvec,dvset)
      if length(dvec)<2 continue ; end
      for i=1:length(dvec)
        for j=(i+1):length(dvec)
          push!(assertion.disjvars,dvec[i]=>dvec[j])
        end
      end
    end
  end
  return assertion
end

# Return token expressions appearing in various statements
function readexpression!(env,stattype::Char, label, terminator)
  expression = Expression()
  if isempty(env.tokens)
    metamath_error("Unfinished \$$stattype statement $label")
  end
  token = shift!(env.tokens)
  if !(token in env.constants)
    metamath_error("First symbol in \$$stattype statement $label"*
      " is $token which is not a constant")
  end
  push!(expression, token)
  while !isempty(env.tokens)
    token = shift!(env.tokens)
    if token == terminator
      break
    end
    if !(token in env.constants) && getfloatinghyp(env,token)==:dummytoken
      metamath_error("In \$$stattype statement $label"*
        " $token found which is not a constant or a variable"*
        " in an active \$f statement")
    end
    push!(expression, token)
  end
  if isempty(env.tokens) && token != terminator
    metamath_error("Unfinished \$$stattype statement $label")
  end
  return expression
end

# Return number vector encoded alphabetically in compressed proof
function getproofnumbers(label, proof)
  proofnumbers = Vector{Int}()
  sizehint!(proofnumbers,length(proof))
  justgotnum = false
  num = zero(UInt)
  for c in proof
    if c <= 'T'
      addval = c-('A'-1)
      if num > typemax(UInt)/20 || 20*num > typemax(UInt)-addval
        metamath_error("Overflow computing numbers in compressed"*
          " proof of $label")
      end
      push!(proofnumbers, 20*num+addval)
      num = zero(UInt)
      justgotnum = true
    elseif c <= 'Y'
      addval = c-'T'
      if num > typemax(UInt)/5 || 5*num > typemax(UInt)-addval
        metamath_error("Overflow computing numbers in compressed"*
          " proof of $label")
      end
      num = 5*num+addval
      justgotnum = false
    else # it must be 'Z'
      if !justgotnum
        metamath_error("Stray Z found in compressed proof of $label")
      end
      push!(proofnumbers,0)
      justgotnum = false
    end
  end
  if num != 0
    metamath_error("Compressed proof of theorem $label ends"*
      " in unfinished number")
  end
  return proofnumbers
end

# Perform substitutions of variables specified in substmap and return
# resulting Expression
function makesubstitution(original, substmapsrc, substmapdst)
  destination = Expression()
  for token in original
    ind = findfirst(substmapsrc,token)
    if ind != 0
      append!(destination,substmapdst[ind])
    else
      push!(destination,token)
    end
  end
  return destination
end

# Verify a proof step referencing assertion (i.e. not hypothesis)
function verifyassertionref(env, thlabel, reflabel, stack)
  assertion = env.assertions[reflabel]
  if length(stack)<length(assertion.hypotheses)
    metamath_error("In proof of theorem $thlabel not enough"*
      " items found on stack")
  end
  base = length(stack)-length(assertion.hypotheses)
  # empty!(substitutions)
  empty!(env.substitutionssrc)
  empty!(env.substitutionsdst)
  for i=1:length(assertion.hypotheses)
    hypothesis = env.hypotheses[assertion.hypotheses[i]]
    if last(hypothesis)
      # Floating hypothesis
      if first(hypothesis)[1] != stack[base+i][1]
        metamath_error("In proof of theorem $thlabel the"*
          " unification failed")
      end
      subst = copy(stack[base+i])
      shift!(subst)
      # substitutions[first(hypothesis)[2]] = subst
      push!(env.substitutionssrc,first(hypothesis)[2])
      push!(env.substitutionsdst,subst)
    else
      # Essential hypothesis
      dest = makesubstitution(first(hypothesis),env.substitutionssrc,env.substitutionsdst)
      if dest != stack[base+i]
        metamath_error("In proof of theorem $thlabel unification failed")
      end
    end
  end
  resize!(stack,base)
  # Verify disjoint variable conditions
  for vpair in assertion.disjvars
    exp1 = env.substitutionsdst[findfirst(env.substitutionssrc,first(vpair))]
    exp2 = env.substitutionsdst[findfirst(env.substitutionssrc,last(vpair))]
    # exp2 = substitutions[last(vpair)]
    exp1vars = Set{Symbol}()
    for token in exp1
      if token in env.variables
        push!(exp1vars,token)
      end
    end
    exp2vars = Set{Symbol}()
    for token in exp2
      if token in env.variables
        push!(exp2vars,token)
      end
    end
    for exp1var in exp1vars
      for exp2var in exp2vars
        if !isdvr(env,exp1var,exp2var)
          metamath_error("In proof of theorem $thlabel disjoint"*
            " variable restriction violated")
        end
      end
    end
  end
  dest = makesubstitution(assertion.expression, env.substitutionssrc, env.substitutionsdst)
  push!(stack,dest)
  return nothing
end

# Verify regular proof
function verifyregularproof(env, label, theorem, proof)
  stack = Vector{Expression}()
  for proofstep in proof
    if haskey(env.hypotheses,proofstep)
      push!(stack, first(env.hypotheses[proofstep]))
      continue
    end
    verifyassertionref(env, label, proofstep, stack)
  end
  if length(stack) != 1
    metamath_error("Proof of theorem $label does not end"*
      " with only one item on the stack")
  end
  if stack[1] != theorem.expression
    metamath_error("Proof of theorem $label proves wrong statement")
  end
  return nothing
end

# Verify compressed proof
function verifycompressedproof(env,label,theorem,labels,proofnumbers)
  stack = Vector{Expression}()
  mandhypt = length(theorem.hypotheses)
  labelt = mandhypt+length(labels)
  savedsteps = Vector{Expression}()
  for pn in proofnumbers
    if pn==0
      push!(savedsteps,last(stack))
      continue
    end
    if pn<=mandhypt
      push!(stack,first(env.hypotheses[theorem.hypotheses[pn]]))
    elseif pn<=labelt
      proofstep = labels[pn-mandhypt]
      if haskey(env.hypotheses,proofstep)
        push!(stack,first(env.hypotheses[proofstep]))
        continue
      end
      verifyassertionref(env,label, proofstep, stack)
    else
      if pn > labelt+length(savedsteps)
        metamath_error("Number in compressed proof of $label"*
          " is too high")
      end
      push!(stack, savedsteps[pn-labelt])
    end
  end
  if length(stack) != 1
    metamath_error("Proof of theorem $label does not end with"*
      " only one item on the stack")
  end
  if first(stack) != theorem.expression
    metamath_error("Proof of theorem $label proves the wrong statement")
  end
  return nothing
end

# Parse $p statement
function parsep!(env,label)
  newtheorem = readexpression!(env,'p', label, Symbol("\$="))
  assertion = constructassertion(env,label, newtheorem)
  env.assertions[label] = assertion
  if isempty(env.tokens)
    metamath_error("Unfinished \$p statement")
  end
  token = shift!(env.tokens)
  if token == Symbol("(")
    # Compressed proof
    labels = Vector{Symbol}()
    while !isempty(env.tokens)
      token = shift!(env.tokens)
      if token == Symbol(")")
        break
      end
      push!(labels, token)
      if token == label
        metamath_error("Proof of theorem $label refers to itself")
      elseif token in assertion.hypotheses
        metamath_error("Compressed proof of theorem $label has"*
          " mandatory hypothesis $token in label list")
      elseif !haskey(env.assertions,token) && !isactivehyp(env,token)
        metamath_error("Proof of theorem $label refers to $token"*
          " which is not an active statement")
      end
    end
    if isempty(env.tokens)
      metamath_error("Unfinished \$p statement $label")
    end
    if isempty(env.compressedproofs)
      metamath_error("Missing compressed proof for $label")
    end
    proof = shift!(env.compressedproofs)
    if isempty(proof)
      metamath_error("Theorem $label has no proof")
    end
    if findfirst(proof,'?')!=0
      metamath_error("Proof of theorem $label is incomplete")
    end
    proofnumbers = getproofnumbers(label, proof)
    verifycompressedproof(env,label, assertion, labels, proofnumbers)
  else
    # Regular (uncompressed) proof
    proof = Vector{Symbol}()
    push!(proof,token)
    incomplete = false
    token = :dummytoken
    while !isempty(env.tokens)
      token = shift!(env.tokens)
      if token == Symbol("\$.")
        break
      end
      push!(proof, token)
      if token == Symbol("?")
        incomplete = true
      elseif token == label
        metamath_error("Proof of theorem $label refers to itself")
      elseif !haskey(env.assertions,token) && !isactivehyp(env,token)
        metamath_error("Proof of theorem $label refers to $token"*
          " which is not an active statement")
      end
    end
    if isempty(env.tokens) && token != Symbol("\$.")
      metamath_error("Unfinished \$p statement")
    end
    if isempty(proof)
      metamath_error("Theorem $label has no proof")
    end
    if incomplete
      @warn_and_ret(nothing, "Warning: Proof of theorem $label is incomplete")
    end
    verifyregularproof(env,label, assertion, proof)
  end
  return nothing
end

# Parse $e statement
function parsee!(env,label)
  newhyp = readexpression!(env,'e', label, Symbol("\$."))
  env.hypotheses[label] = newhyp=>false
  push!(last(env.scopes).activehyp,label)
  return nothing
end

# Parse $a statement
function parsea!(env,label)
  newaxiom = readexpression!(env,'a',label,Symbol("\$."))
  assertion = constructassertion(env,label, newaxiom)
  env.assertions[label] = assertion
  return nothing
end

# Parse $f statement
function parsef!(env,label)
  if isempty(env.tokens)
    metamath_error("Unfinished \$f statement $label")
  end
  typetoken = shift!(env.tokens)
  if !(typetoken in env.constants)
    metamath_error("First symbol in \$f statement $label is $typetoken"*
      " which is not a constant")
  end
  if isempty(env.tokens)
    metamath_error("Unfinished \$f statement $label")
  end
  variable = shift!(env.tokens)
  if !isactivevariable(env,variable)
    metamath_error("Second symbol in \$f statement $label is $variable"*
      " which is not an active variable")
  end
  if !(getfloatinghyp(env,variable)==:dummytoken)
    metamath_error("The variable $variable appears in a second"*
      " \$f statement $label")
  end
  if isempty(env.tokens)
    metamath_error("Unfinished \$f statement $label")
  end
  token = shift!(env.tokens)
  if token != Symbol("\$.")
    metamath_error("Expected end of \$f statement but found $token")
  end
  newhyp = Expression()
  push!(newhyp, typetoken)
  push!(newhyp, variable)
  env.hypotheses[label] = newhyp=>true
  push!(last(env.scopes).activehyp,label)
  last(env.scopes).floatinghyp[variable] = label
  return nothing
end

# Parse labeled statement
function parselabel!(env,label)
  if label in env.constants
    metamath_error("Attempt to reuse constant $label as a label")
  end
  if label in env.variables
    metamath_error("Attempt to reuse variable $label as a label")
  end
  if labelused(env,label)
    metamath_error("Attempt to reuse label $label")
  end
  if isempty(env.tokens)
    metamath_error("Unfinished labeled statement")
  end
  labeltype = shift!(env.tokens)
  if labeltype == Symbol("\$p")
    parsep!(env,label)
  elseif labeltype == Symbol("\$e")
    parsee!(env,label)
  elseif labeltype == Symbol("\$a")
    parsea!(env,label)
  elseif labeltype == Symbol("\$f")
    parsef!(env,label)
  else
    metamath_error("Unexpected token $labeltype encountered")
  end
  return nothing
end

# Parse $d statement
function parsed!(env)
  dvars = Set{Symbol}()
  token = :dummytoken
  while !isempty(env.tokens)
    token = shift!(env.tokens)
    if token == Symbol("\$.")
      break
    end
    if !isactivevariable(env,token)
      metamath_error("Token $token is not an active variable but was"*
        " found in a \$d statement")
    end
    if token in dvars
      metamath_error("\$d statement mentions $token twice")
    end
    push!(dvars, token)
  end
  if isempty(env.tokens) && token != Symbol("\$.")
    metamath_error("Unfinished \$d statement")
  end
  if length(dvars)<2
    metamath_error("Not enough variables in \$d statement")
  end
  push!(last(env.scopes).disjvars, dvars)
  return nothing
end

# Parse $c statement
function parsec!(env)
  if length(env.scopes)>1
    metamath_error("\$c statement occurs in inner block")
  end
  token = ""
  listempty = true
  while !isempty(env.tokens)
    token = shift!(env.tokens)
    if token == Symbol("\$.")
      break
    end
    listempty = false
    if !ismathsymboltoken(token)
      metamath_error("Attempt to declare $token as a constant")
    end
    if token in env.variables
      metamath_error("Attempt to redeclare variable $token as a constant")
    end
    if labelused(env,token)
      metamath_error("Attempt to reuse label $token as a constant")
    end
    if token in env.constants
      metamath_error("Attempt to redeclare constant $token")
    end
    push!(env.constants, token)
  end
  if isempty(env.tokens) && token != Symbol("\$.")
    metamath_error("Unterminated \$c declaration")
  end
  if listempty
    metamath_error("Empty \$c statement")
  end
  return nothing
end

# Parse $v statement
function parsev!(env)
  token = ""
  listempty = true
  while !isempty(env.tokens)
    token = shift!(env.tokens)
    if token == Symbol("\$.")
      break
    end
    listempty = false
    if !ismathsymboltoken(token)
      metamath_error("Attempt to declare $token as a variable")
    end
    if token in env.constants
      metamath_error("Attempt to redeclare constant $token as a variable")
    end
    if labelused(env,token)
      metamath_error("Attempt to reuse label $token as a variable")
    end
    if isactivevariable(env,token)
      metamath_error("Attempt to redeclare active variable $token")
    end
    push!(env.variables,token)
    push!(last(env.scopes).activevariables,token)
  end
  if isempty(env.tokens) && token != "\$."
    metamath_error("Unterminated \$v statement")
  end
  if listempty
    metamath_error("Empty \$v statement")
  end
  return nothing
end

"""`mmverify!(env,filename)` verifies database in filename using and then return env"""
function mmverify!(env::Environment,filename::AbstractString;
             use_mmap::Bool=true)
  if env.dirty[1]
    metamath_warn("Starting verification of $filename with dirty"*
      " environment")
  else
    env.dirty[1] = true
  end
  readtokens!(env,filename)

  while length(env.tokens)>0
    token = shift!(env.tokens)
    if islabeltoken(string(token))
      parselabel!(env,token)
    elseif token==Symbol("\$d")
      parsed!(env)
    elseif token==Symbol("\${")
      push!(env.scopes,Scope())
    elseif token==Symbol("\$}")
      pop!(env.scopes)
      if isempty(env.scopes)
        metamath_error("\$} without corresponding \${")
      end
    elseif token==Symbol("\$c")
      parsec!(env)
    elseif token==Symbol("\$v")
      parsev!(env)
    else
      metamath_error("Unexpected token $token encountered")
    end
  end
  if length(env.scopes)>1
    metamath_error("\${ without corresponding \$}")
  end
  empty!(env.substitutionssrc)
  empty!(env.substitutionsdst)
  env.dirty[1] = false
  return nothing
end

"""`main(filename ; use_mmap=true, use_globalenv=true)`

Verify contents of filename with a new environment or `globalenv` by default.
`use_mmap`, true by default, makes file processing faster, may be impossible
with other data sources.

Return value: the Metamath environment after processing file.

Example: `Metamath.main("set.mm")`
"""
function main(filename::AbstractString;
             use_mmap::Bool=true,use_globalenv::Bool=true)
  if use_globalenv
    env = globalenv
  else
    env = Environment()
  end
  mmverify!(env,filename)
  return env
end

# Restore scope to initial state without reallocating scope
function empty!(scope::Scope)
  empty!(scope.activevariables)
  empty!(scope.activehyp)
  empty!(scope.disjvars)
  empty!(scope.floatinghyp)
  return scope
end

"""`empty!(env)` returns `env` to initial empty state and returns `env`"""
function empty!(env::Environment)
  empty!(env.filenames)
  empty!(env.tokens)
  empty!(env.compressedproofs)
  empty!(env.constants)
  empty!(env.hypotheses)
  empty!(env.variables)
  empty!(env.assertions)
  resize!(env.scopes,1)
  empty!(env.scopes[1])
  empty!(env.substitutionssrc)
  empty!(env.substitutionsdst)
  env.dirty[1] = false
  return env
end

end # module

