; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "coretypes")
(include-book "../util/defs")
(local (include-book "arithmetic/top" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc syscalls
  :parents (mlib)
  :short "Functions for working with system functions like @('$bits') and
  @('$random').")

(local (xdoc::set-default-parents syscalls))


(define vl-simple-id-name ((x vl-scopeexpr-p))
  :short "If x is a simple name with no scoping, return the name, otherwise nil."
  :returns (name maybe-stringp :rule-classes :type-prescription)
  (vl-scopeexpr-case x
    :end (vl-hidexpr-case x.hid
           :end x.hid.name
           :otherwise nil)
    :otherwise nil)
  ///
  (defret stringp-of-vl-simple-id-name
    (iff (stringp name) name)))

(define vl-0ary-syscall-p
  :short "Recognize calls of a particular zero-ary system function call."
  ((name stringp   "Name of the particular system call, e.g., @('$time').")
   (x    vl-expr-p "Expression to test."))
  :long "<p>For instance, to see if @('x') is a call of @('$time'), you could
         write:</p>
         @({
           (vl-0ary-syscall-p \"$time\" x)
         })"
  (vl-expr-case x
    :vl-call (and x.systemp
                  (equal (vl-simple-id-name x.name) (string-fix name))
                  (atom x.plainargs)
                  (atom x.namedargs))
    :otherwise nil)
  ///
  (defthm arity-stuff-about-vl-0ary-syscall-p
    (implies (vl-0ary-syscall-p name x)
             (vl-expr-case x
               :vl-call (and x.systemp
                             (equal (vl-simple-id-name x.name) (string-fix name))
                             (atom x.plainargs)
                             (atom x.namedargs))
               :otherwise nil))
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
  (vl-expr-case x
    :vl-call (and x.systemp
                  (equal (vl-simple-id-name x.name) (string-fix name))
                  ;; BOZO Can these system functions be called with a named
                  ;; arg?  We don't allow it for now.
                  (eql (len x.plainargs) 1)
                  (car x.plainargs)
                  (atom x.namedargs))
    :otherwise nil)
  ///
  (defthm arity-stuff-about-vl-unary-syscall-p
    (implies (vl-unary-syscall-p name x)
             (vl-expr-case x
               :vl-call (and x.systemp
                             (equal (vl-simple-id-name x.name) (string-fix name))
                             (eql (len x.plainargs) 1)
                             (consp x.plainargs)
                             (car x.plainargs)
                             (atom x.namedargs))
               :otherwise nil))
    :rule-classes :forward-chaining))

(defsection vl-unary-syscall->arg
  :short "Access the argument to a @(see vl-unary-syscall-p), not including the
function name."
  :long "<p>This is mostly intended to avoid confusion since the function name
is the first argument to the @(':vl-syscall').</p>
  @(def vl-unary-syscall->arg)"

  (defmacro vl-unary-syscall->arg (x)
    `(first (vl-call->args ,x))))


(define vl-typearg-syscall-p
  :short "Recognize calls of a particular typearg system function call."
  ((name stringp   "Name of the particular system call, e.g., @('$bits').")
   (x    vl-expr-p "Expression to test."))
  :long "<p>For instance, to see if @('x') is a call of @('$bits'), you could
         write:</p>
         @({
           (vl-typearg-syscall-p \"$bits\" x)
         })"
  (vl-expr-case x
    :vl-call (and x.systemp
                  (equal (vl-simple-id-name x.name) (string-fix name))
                  x.typearg
                  (atom x.plainargs)
                  (atom x.namedargs))
    :otherwise nil)
  ///
  (defthm arity-stuff-about-vl-typearg-syscall-p
    (implies (vl-typearg-syscall-p name x)
             (vl-expr-case x
               :vl-call (and x.systemp
                             (equal (vl-simple-id-name x.name) (string-fix name))
                             x.typearg
                             (not (consp x.plainargs))
                             (not (consp x.namedargs)))
               :otherwise nil))
    :rule-classes :forward-chaining))



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
  (vl-expr-case x
    :vl-call (and x.systemp
                  (equal (vl-simple-id-name x.name) (string-fix name)))
    :otherwise nil)
  ///
  (defthm arity-stuff-about-vl-*ary-syscall-p
    (implies (vl-*ary-syscall-p name x)
             (vl-expr-case x
               :vl-call (and x.systemp
                             (equal (vl-simple-id-name x.name) (string-fix name)))
               :otherwise nil))
    :rule-classes :forward-chaining))


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
             (vl-expr-case x
               :vl-call x.systemp
               :otherwise nil))
    :rule-classes ((:forward-chaining))))


(make-event
 `(define vl-syscall->returninfo
    :short "(Attempt to) look up the return type of a system function call."
    ((x vl-expr-p))
    :guard (vl-expr-case x :vl-call x.systemp :otherwise nil)
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

          ((or (vl-unary-syscall-p "$bits" x)
               (vl-typearg-syscall-p "$bits" x))
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

          ((vl-unary-syscall-p "$test$plusargs" x)
           ;; SystemVerilog 21.6 -- returns "... a nonzero integer ... or the
           ;; integer value zero", so that seems like an integer.
           ',(vl-coretypename->info :vl-integer))

          (t
           ;; BOZO.  Eventually it would be good (for linting especially)
           ;; to expand this with other SystemVerilog functions.  For now,
           ;; we will just fail to size them.
           nil))))


;; (define vl-sysfun-should-size-args-p
;;   :short "Should we size the arguments to this system call?"
;;   ((name stringp "E.g., @('$bits')."))
;;   :returns bool
;;   :long "<p>This is used among functions like @(see vl-expr-expandsizes) and
;; our notion of @(see welltyped) expressions to decide whether calls of system
;; functions should have their arguments sized normally.</p>

;; <p>Motivation: consider the system function @('$bits'), which can take either a
;; type or an expression as its argument.  We don't want to size @('$bits')
;; normally because we don't normally have types in expressions.</p>

;; <p>However, for functions like @('$clog2') or @('$random'), we should go ahead
;; and size the arguments.</p>"

;;   (let ((name (string-fix name)))
;;     ;; BOZO are there others?
;;     (not (equal name "$bits"))))

