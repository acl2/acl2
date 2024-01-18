# global-vars

Define efficient global variables in Common Lisp.

## Synopsis

    ;; Similar to defparameter with regard to redefinitions
    (define-global-parameter -x- 3)

    ;; Similar to defvar with regard to redefinitions
    (define-global-var -y- 4)

    ;; ...

    (setf -x- 5)
    (setf -y- 6)

## Description

In Common Lisp, a special variable that is never dynamically bound
typically serves as a stand-in for a global variable. The
`global-vars` library provides true global variables that are
implemented by some compilers. An attempt to rebind a global variable
properly results in a compiler error. That is, a global variable
cannot be dynamically bound.

Global variables therefore allow us to communicate an intended usage
that differs from special variables. Global variables are also more
efficient than special variables, especially in the presence of
threads.

## API

* [macro] **`define-global-var`** `name` `value` *`&optional`* `documentation`

  Define a global variable with a compile-time value.

  Subsequent redefinitions will not change the value (like `defvar`).

  The `value` argument is evaluated at compile-time. On SBCL, this
  permits optimizations based upon the invariant that `name` is always
  bound.

* [macro] **`define-global-var*`** `name` `value` *`&optional`* `documentation`

  Same as `define-global-var` except `value` is evaluated at load time,
  not compile time.

* [macro] **`define-global-parameter`** `name` `value` *`&optional`* `documentation`

  Same as `define-global-var` except subsequent redefinitions will
  update the value (like `defparameter`).

* [macro] **`define-global-parameter*`** `name` `value` *`&optional`* `documentation`

  Same as `define-global-parameter` except `value` is evaluated at
  load time, not compile time.

## Detail

`global-vars` wraps the following implementation-specific features:

* [SBCL](http://www.sbcl.org/manual/#Global-and-Always_002dBound-variables): `sb-ext:defglobal` and `sb-ext:define-load-time-global`.

* [CCL](http://ccl.clozure.com/manual/chapter4.8.html): `ccl:defstatic` and `ccl:defstaticvar`.

* [LispWorks](http://www.lispworks.com/documentation/lw61/LW/html/lw-122.htm): `hcl:special-global`, in particular `defglobal-parameter` and `defglobal-variable`.

For these implementations, rebinding a global variable is a
compilation error.

On other implementations, a global variable is implemented as a symbol
macro which expands to a `symbol-value` form. Rebinding a global
variable will (unfortunately) not signal an error.

It is recommended to use a naming convention for global variables,
such as `-foo-`. This makes it clear that `(let ((-foo- 9)) ...)` is a
mistake even if the compiler doesn't catch it.

## Author

James M. Lawrence <llmjjmll@gmail.com>
