# Lisp-Z3 Interface

This library provides an interface through which one can use the
[Z3](https://github.com/Z3Prover/z3/) Satisfiability Modulo Theories
(SMT) solver from inside of Common Lisp. In short, this interface
allows one to leverage Z3's ability to solve constraints involving
variables over numbers, strings, bitvectors, uninterpreted functions,
and more, including optimization problems.

This version of the interface is associated with the ACL2 Workshop 2025
paper "An ACL2s Interface to Z3". The latest version of the interface
is maintained at [https://github.com/mister-walter/cl-z3](https://github.com/mister-walter/cl-z3).

## Setup

### Prerequisites
- A Common Lisp implementation (tested on SBCL and Clozure CL)
- Quicklisp
- Z3, version 4.8.15 or greater (see below)

### Installing Z3
To use this library, you first need to install Z3 onto your
system. Many package managers offer a prepackaged version of Z3, so it
is likely easiest to install Z3 using your package manager rather than
building it from source. If you're on macOS, Homebrew provides
prebuilt Z3 packages as well.

Depending on your operating system, you may also need to install
a "z3-dev" package. On Ubuntu, this package is called `libz3-dev`.

To use the library as-is, you will need to have version 4.8.15 of Z3
or greater. The library has been tested on Z3 versions up to 4.13.4. A
version of Z3 before 4.8.15 may be usable with this package, but you
will need to regenerate the FFI files; see `scripts/update-ffi.sh` for
more information about how to do this. A version of Z3 later than
4.13.4 will likely load correctly (barring the removal of any
functions or types) but it may exhibit issues at runtime when
values that it doesn't expect are encountered.

You will also need a working C compiler to use the interface. On
Ubuntu, the `build-essential` package should include everything you
need, though it is fairly large and contains some unneeded
software. One could also try just installing `gcc` or `clang`.

### Installing the interface
The easiest way to install and use this library is to clone this
repository inside of your Quicklisp `local-projects` directory, which
typically is located at `~/quicklisp/local-projects`. I will refer to
this directory as <ql-local-projects> below.

To test that everything has been installed properly, start SBCL inside
the `<ql-local-projects>/cl-z3/examples/` directory and run the
commands inside of the `<ql-local-projects>/cl-z3/examples/basic.lisp`
file. If no errors occur, then you're all set.

## Usage

If the library was successfully installed, you should be able to load
it from Lisp using the following code, assuming that Quicklisp is
already loaded:
```lisp
(ql:register-local-projects)
(ql:quickload :cl-z3)
```

The examples should provide a fairly good overview of various features
of the library, but the `operators.md` file inside of this directory
contains additional information about the operators we support
converting to Z3 statements.

## Documentation

Generated documentation for this library is available at
[www.atwalter.com/cl-z3](https://www.atwalter.com/cl-z3/). The
user-facing API is contained in the [cl-z3/z3
system](https://www.atwalter.com/cl-z3/cl-z3/z3/), so that part of the
documentation is likely to be the most useful. The low-level bindings
to the Z3 C API are also documented (in the [cl-z3/ffi
system](https://www.atwalter.com/cl-z3/cl-z3/ffi/)) but the
documentation there is automatically extracted from the Z3 C API on a
best-effort basis. The Z3 project hosts a [much better
version](https://z3prover.github.io/api/html/group__capi.html) of this
documentation for the interested user.
