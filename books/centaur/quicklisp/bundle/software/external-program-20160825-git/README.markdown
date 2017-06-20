`EXTERNAL-PROGRAM` enables running programs outside the Lisp process. It is an attempt to make the `RUN-PROGRAM` functionality in implementations like SBCL and CCL as portable as possible without sacrificing much in the way of power.

**Note**: This library is available via [Quicklisp](https://quicklisp.org/).

Here are some of the differences:

* splits `START` (async) and `RUN` (sync) into two separate functions, rather than using a single function with a `WAIT` parameter that changes the function's specification;
* offers a `REPLACE-ENVIRONMENT-P` parameter that indicates whether provided env vars should build on or replace the current environment.

Read [the API documention](https://github.com/sellout/external-program/wiki/API) for details. It’s a bit spartan, but should explain a lot.

Not all functionality is available on all platforms. `EXTERNAL-PROGRAM` provides warnings and errors when these limitations are encountered. But I'll try my best to work around them.

There is currently at least some support for:

* Allegro (blocking only)
* Armed Bear (blocking only)
* CLisp
* Clozure CL (née OpenMCL)
* CMUCL
* ECL
* LispWorks
* SBCL

In addition to some implementations only providing blocking calls, some don’t use `$PATH` – the ones that don’t won’t find bareword commands, you’ll need to use a pathname.
