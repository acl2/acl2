; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "coretypes")
(local (include-book "arithmetic/top" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc syscalls
  :parents (mlib)
  :short "Functions for working with system functions like @('$bits') and
  @('$random').")

(local (xdoc::set-default-parents syscalls))

(define vl-sysfunexpr-p ((x vl-expr-p))
  :returns bool
  :short "Recognize atomic expressions that are system function names."
  :inline t
  (and (vl-fast-atom-p x)
       (vl-fast-sysfunname-p (vl-atom->guts x))))

(define vl-sysfunexpr->name ((x vl-expr-p))
  :guard (vl-sysfunexpr-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :short "Get the name from a @(see vl-sysfunexpr-p) as a string, e.g., @('\"$bits\"')."
  :guard-hints(("Goal" :in-theory (enable vl-sysfunexpr-p)))
  :inline t
  (vl-sysfunname->name (vl-atom->guts x)))


(define vl-0ary-syscall-p
  :short "Recognize calls of a particular zero-ary system function call."
  ((name stringp   "Name of the particular system call, e.g., @('$time').")
   (x    vl-expr-p "Expression to test."))
  :long "<p>For instance, to see if @('x') is a call of @('$time'), you could
         write:</p>
         @({
           (vl-0ary-syscall-p \"$time\" x)
         })"
  (b* (((when (vl-fast-atom-p x))
        nil)
       ((vl-nonatom x))
       ((unless (and (eq x.op :vl-syscall)
                     (consp x.args)
                     (atom (cdr x.args))))
        nil)
       (fn (first x.args))
       ((unless (vl-sysfunexpr-p fn))
        nil))
    (equal (vl-sysfunexpr->name fn) (string-fix name)))
  ///
  (defthm arity-stuff-about-vl-0ary-syscall-p
    (implies (vl-0ary-syscall-p name x)
             (and (not (equal (vl-expr-kind x) :atom))
                  (equal (vl-nonatom->op x) :vl-syscall)
                  (consp (vl-nonatom->args x))
                  (not (consp (cdr (vl-nonatom->args x))))))
    :rule-classes :forward-chaining))


(define vl-unary-syscall-p
  :short "Recognize calls of a particular unary system function call."
  ((name stringp   "Name of the particular system call, e.g., @('$bits').")
   (x    vl-expr-p "Expression to test."))
  :long "<p>For instance, to see if @('x') is a call of @('$bits'), you could
         write:</p>
         @({
           (vl-unary-syscall-p \"$bits\" x)
         })"
  (b* (((when (vl-fast-atom-p x))
        nil)
       ((vl-nonatom x))
       ((unless (and (eq x.op :vl-syscall)
                     (consp x.args)
                     (consp (cdr x.args))
                     (atom (cddr x.args))))
        nil)
       (fn (first x.args))
       ((unless (vl-sysfunexpr-p fn))
        nil))
    (equal (vl-sysfunexpr->name fn) (string-fix name)))
  ///
  (defthm arity-stuff-about-vl-unary-syscall-p
    (implies (vl-unary-syscall-p name x)
             (and (not (equal (vl-expr-kind x) :atom))
                  (equal (vl-nonatom->op x) :vl-syscall)
                  (consp (vl-nonatom->args x))
                  (consp (cdr (vl-nonatom->args x)))
                  (vl-expr-p (cadr (vl-nonatom->args x)))))
    :rule-classes :forward-chaining))


(defsection vl-unary-syscall->arg
  :short "Access the argument to a @(see vl-unary-syscall-p), not including the
function name."
  :long "<p>This is mostly intended to avoid confusion since the function name
is the first argument to the @(':vl-syscall').</p>
  @(def vl-unary-syscall->arg)"

  (defmacro vl-unary-syscall->arg (x)
    `(second (vl-nonatom->args ,x))))



(define vl-*ary-syscall-p
  :short "Recognize calls of a particular system function call, without any
          arity checking."
  ((name stringp   "Name of the particular system call, e.g., @('$size').")
   (x    vl-expr-p "Expression to test."))
  :long "<p>For instance, to see if @('x') is a call of @('$size'), you could
         write:</p>
         @({
           (vl-*ary-syscall-p \"$size\" x)
         })"
  (b* (((when (vl-fast-atom-p x))
        nil)
       ((vl-nonatom x))
       ((unless (and (eq x.op :vl-syscall)
                     (consp x.args)))
        nil)
       (fn (first x.args))
       ((unless (vl-sysfunexpr-p fn))
        nil))
    (equal (vl-sysfunexpr->name fn) (string-fix name)))
  ///
  (defthm arity-stuff-about-vl-*ary-syscall-p
    (implies (vl-*ary-syscall-p name x)
             (and (not (equal (vl-expr-kind x) :atom))
                  (equal (vl-nonatom->op x) :vl-syscall)
                  (consp (vl-nonatom->args x))))
    :rule-classes :forward-chaining))

(defsection vl-*ary-syscall->args
  :parents (vl-*ary-syscall-p)
  :short "Access the argument to a @(see vl-*ary-syscall-p), not including the
  function name."
  :long "<p>This is mostly intended to avoid confusion since the function name
is the first argument to the @(':vl-syscall').</p>
  @(def vl-*ary-syscall->args)"

  (defmacro vl-*ary-syscall->args (x)
    `(second (vl-nonatom->args ,x))))



(define vl-$random-expr-p ((x vl-expr-p))
  :short "Recognize calls of the @('$random') system function."

  :long "<p>The @('$random') system call is described in Verilog-2005, Section
17.9.1 on page 311, or in SystemVerilog-2012 Section 20.15.  In either case the
syntax is:</p>

@({random_function ::= $random[ '(' seed ')' ]})

<p>Note that the @('seed') is supposed to be a reg, integer, or time variable,
but we do not check for this here.</p>"

  (or (vl-0ary-syscall-p "$random" x)
      (vl-unary-syscall-p "$random" x))
  ///
  (defthm vl-expr-kind-when-vl-$random-expr-p
    (implies (vl-$random-expr-p x)
             (and (equal (vl-expr-kind x) :nonatom)
                  (equal (vl-nonatom->op x) :vl-syscall)))
    :rule-classes ((:forward-chaining))))


(make-event
 `(define vl-syscall->returninfo
    :short "(Attempt to) look up the return type of a system function call."
    ((x vl-expr-p))
    :guard (and (not (vl-atom-p x))
                (equal (vl-nonatom->op x) :vl-syscall))
    :returns
    (info (iff (vl-coredatatype-info-p info) info)
          "Information about the return type for this system call, if available.")

    :long "<p>Some system calls don't necessarily have a well-defined or sensible
return type, for instance, what is the return type of @('$finish')?  So, in
some cases we will return @('nil').</p>

<p>Even if certain system calls don't make sense in the context of synthesis,
it is generally useful (e.g., for linting) to be able to look up their return
types.  So, it would be good to extend this function to make it more
complete.</p>"

    (cond ((vl-0ary-syscall-p "$time" x)
           ;; SystemVerilog 20.3.1: $time returns an integer that is a
           ;; 64-bit time, scaled to the time unit of the module that
           ;; invoked it.
           ',(vl-coretypename->info :vl-time))

          ((vl-unary-syscall-p "$bits" x)
           ;; SystemVerilog 20.6.2: The return type is integer.
           ',(vl-coretypename->info :vl-integer))

          ((or (vl-*ary-syscall-p "$left" x)
               (vl-*ary-syscall-p "$right" x)
               (vl-*ary-syscall-p "$low" x)
               (vl-*ary-syscall-p "$high" x)
               (vl-*ary-syscall-p "$increment" x)
               (vl-*ary-syscall-p "$size" x))
           ;; SystemVerilog 20.7 -- The return type is integer.
           ',(vl-coretypename->info :vl-integer))

          ((or (vl-unary-syscall-p "$dimensions" x)
               (vl-unary-syscall-p "$unpacked_dimensions" x))
           ;; SystemVerilog 20.7 -- The return type is integer.
           ',(vl-coretypename->info :vl-integer))

          ((vl-unary-syscall-p "$clog2" x)
           ;; SystemVerilog 20.8.1 -- return type isn't really specified
           ;; but it at least says "shall return... the log rounded up to
           ;; an integer value."  We'll have to resort to testing to make
           ;; sure the result type is an integer.
           ',(vl-coretypename->info :vl-integer))

          ((or (vl-unary-syscall-p "$ln" x)
               (vl-unary-syscall-p "$log10" x))
           ;; SystemVerilog 20.8.2 -- return type is real.  There are many more
           ;; functions here, none of which we support in any sensible way.  I
           ;; mostly wanted to put this here to ensure that this function can
           ;; sometimes return :vl-real.
           ',(vl-coretypename->info :vl-real))

          ((or (vl-*ary-syscall-p "$countbits" x)
               (vl-unary-syscall-p "$countones" x))
           ;; SystemVerilog 20.9 -- return type is int.  I guess this is
           ;; assuredly 2 valued, perhaps because it treats X/Z bits
           ;; nonconservatively.
           ',(vl-coretypename->info :vl-int))

          ((or (vl-unary-syscall-p "$onehot" x)
               (vl-unary-syscall-p "$onehot0" x)
               (vl-unary-syscall-p "$isunknown" x))
           ;; SystemVerilog 20.9 -- return type is bit.  Again this is 2
           ;; valued, presumably treating X/Z bits nonconservatively.
           ',(vl-coretypename->info :vl-bit))

          ((vl-$random-expr-p x)
           ;; SystemVerilog 20.15.1 -- return type is a signed integer.
           ',(vl-coretypename->info :vl-integer))

          (t
           ;; BOZO.  Eventually it would be good (for linting especially)
           ;; to expand this with other SystemVerilog functions.  For now,
           ;; we will just fail to size them.
           nil))))


(define vl-sysfun-should-size-args-p
  :short "Should we size the arguments to this system call?"
  ((name stringp "E.g., @('$bits')."))
  :returns bool
  :long "<p>This is used among functions like @(see vl-expr-expandsizes) and
our notion of @(see welltyped) expressions to decide whether calls of system
functions should have their arguments sized normally.</p>

<p>Motivation: consider the system function @('$bits'), which can take either a
type or an expression as its argument.  We don't want to size @('$bits')
normally because we don't normally have types in expressions.</p>

<p>However, for functions like @('$clog2') or @('$random'), we should go ahead
and size the arguments.</p>"

  (let ((name (string-fix name)))
    ;; BOZO are there others?
    (not (equal name "$bits"))))

