# Metamath.jl

[![Build Status](https://travis-ci.org/getzdan/Metamath.jl.svg?branch=master)](https://travis-ci.org/getzdan/Metamath.jl)
[![Build status](https://ci.appveyor.com/api/projects/status/86f1o182nfeb1yyg?svg=true)](https://ci.appveyor.com/project/getzdan/metamath-jl)
[![Coverage Status](https://coveralls.io/repos/github/getzdan/Metamath.jl/badge.svg?branch=master)](https://coveralls.io/github/getzdan/Metamath.jl?branch=master)

This package provides a standalone verifier for Metamath database files.

For more information on the Metamath language see: http://us.metamath.org.

The code is written in Julia and inspired by `checkmm.cpp` by Eric Schmidt (see
http://us.metamath.org/downloads/checkmm.cpp).

## Installation

Install this package within Julia using:
```julia
Pkg.add("Metamath")
```

or (while the package is not in the official METADATA):
```julia
Pkg.clone("git://github.com/getzdan/Metamath.jl")
```

## Usage

The package comes with sample Metamath databases in the `data` directory of the
package. To test verification (without downloading anything), try:

```julia
using Metamath
Metamath.main(joinpath(Pkg.dir("Metamath"),"data","demo.mm"))
```

A more interesting database file is `set.mm` (containing axioms and theorems
from Set Theory and beyond). To verify it:

1. Download the updated `set.mm` to the current directory from the Metamath website.
2. Use the following code:

```julia 
using Metamath
Metamath.main("set.mm")
```

There is also a test script which verifies the sample databases which can be run using:

```julia
Pkg.test("Metamath")
```

## Exports and useful internals

The package exports a single function `mmverify!` which accepts a Metamath.Environment
variable and a filename and verifies it. The verification throws a MetamathException
if something goes wrong (with a, hopefully, informative message and a backtrace).

Internally, the function `Metamath.main` verifies a file with a new environment or the package
internal global environment `Metamath.globalenv`.

Redefinition of entities such as constants, variables and axioms is not allowed. So to reuse
a `Metamath.Environment` it may be returned to the initial state with `empty!(env)` (overloaded
from Base).

## Performance

A benchmark test consisting of verification of `set.mm` was conducted on June 11th 2016 with
the latest versions of 4 verifiers. The results are as follows:

| Time (s)  | Verifier    | Computer language         |
| --------: | :---------- | ------------------------- |
| 108.1     | mmverify.py | Python (3.4.3)            |
|  25.2     | MM Tool     | Javascript (V8 5.0.71.49) |
|  15.5     | checkmm.cpp | C++ (g++ 4.8.4)           |
|  10.1     | Metamath.jl | Julia (0.4.6pre)          |

or graphically:

| Verifier    | Bar chart of time                    |
| :---------- | ------------------------------------ |
| mmverify.py | #################################### |
| MM Tool     | ########                             |
| checkmm.cpp | #####                                |
| Metamath.jl | ###                                  |

## Notes

(from Eric's notes on `checkmm.cpp`)

1. The code assumes that the character set is compatible with ASCII.
2. According to the spec, file inclusion commands should not include a file
that has already been included. Unfortunately, determing whether two
different strings refer to the same file is not easy, and, worse, is
system-dependant. This program ignores the issue entirely and assumes
that distinct strings name different files. This should be adequate for
the present, at least.

3. If the verifier finds an error, it will throw an error and quit. It will not
attempt to recover and find more errors. The only condition that generates
a diagnostic message but doesn't halt the program is an incomplete proof,
specified by a question mark. In that case, as per the spec, a warning is
issued and checking continues.

## Acknowledgements

Acknowledgements are due to Norm Megill, creator of the Metamath language and software
ecosystem.
And to Eric Schmidt who wrote `checkmm.cpp` which served as a basis for this package.
