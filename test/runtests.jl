using Metamath
using Test

getenvsig(env) = map(f->length(getfield(env,f)),fieldnames(Metamath.Environment))
mmexample(fname) = joinpath(dirname(pathof(Metamath)),"..", "data",fname)

env = Metamath.main(mmexample("demo.mm"))
@test all(getenvsig(env) .== [1,0,0,6,5,3,12,1,0,0,1])

@test env == Metamath.globalenv

empty!(env)
@test all(getenvsig(env) .== [0,0,0,0,0,0,0,1,0,0,1])

mmverify!(env,mmexample("hol.mm"))
@test all(getenvsig(env) .== [1,0,0,31,289,18,209,1,0,0,1])

empty!(env)
mmverify!(env,mmexample("miu.mm"))
@test all(getenvsig(env) .== [1,0,0,5,6,2,11,1,0,0,1])

