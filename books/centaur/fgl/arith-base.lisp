; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (std::add-default-post-define-hook :fix))

(fty::deffixequiv acl2::bool->bit$inline :args ((x booleanp)))

(defxdoc fgl-bitvector
  :parents (fgl-object)
  :short "Bitvector representation in FGL"
  :long "<p>The @(see g-integer) symbolic object kind in FGL uses a list of
Boolean function objects (see @(see bfr)) representing the bits of the number.
The representation is least-significant-bit first, sign-extended by the final
bit.  See @(see bools->int) to convert between a concrete bitvector (list of
Booleans) and an integer.</p>")

;; Get the integer value of a bitvector represented as a Boolean list.  LSB first.
(define bools->int ((x boolean-listp))
  :parents (fgl-object-eval fgl-bitvector)
  :short "Convert a list of Booleans into an integer."
  :long "<p>Produces a two's-complement integer from a list of bits,
least-significant first.  The last element of the list determines the sign of
the value.  Some examples:</p>
<ul>
<li>@('(t)') and @('(t t t)') both evaluate to -1</li>
<li>@('nil'), @('(nil)'), and @('(nil nil nil)') all evaluate to 0</li>
<li>@('(t t t nil)') evaluates to 7</li>
<li>@('(nil nil t)') evaluates to -4.</li>
</ul>"
  (mbe :logic (if (atom (cdr x))
                  (- (bool->bit (car x)))
                (logcons (bool->bit (car x))
                         (bools->int (cdr x))))
       :exec (cond ((atom x) 0)
                   ((atom (cdr x)) (- (bool->bit (car x))))
                   (t (logcons (bool->bit (car x))
                               (bools->int (cdr x))))))
  ///
  (defthm bools->int-of-true-list-fix
    (equal (bools->int (true-list-fix x))
           (bools->int x)))

  (local (in-theory (enable acl2::boolean-list-fix))))

(define bools->uint ((x boolean-listp))
  :returns (uint natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (logcons (bool->bit (car x))
             (bools->uint (cdr x))))
  ///
  ;; default may be weaker than the one derived by natp-of-bools->uint
  (in-theory (disable (:type-prescription bools->uint)))

  (defthm bools->uint-of-true-list-fix
    (equal (bools->uint (true-list-fix x))
           (bools->uint x)))

  (defthm logcar-of-bools->uint
    (equal (logcar (bools->uint x))
           (bool->bit (car x)))
    :hints(("Goal" :in-theory (e/d (bool->bit) (logcar))
            :expand ((bools->uint x))
            :do-not-induct t)))

  (defthm logcdr-of-bools->uint
    (equal (logcdr (bools->uint x))
           (bools->uint (cdr x)))
    :hints(("Goal" :in-theory (e/d (bool->bit) (logcdr))
            :expand ((bools->uint x))
            :do-not-induct t)))

  (local (in-theory (enable acl2::boolean-list-fix))))

;; Like logcons, but takes a Boolean as the first element rather than an
;; integer.  For convenience in creating rewrite rules.  Unify algorithm treats
;; this specially.
(define intcons ((b booleanp)
                 (x integerp))
  :returns (val)
  :enabled t
  (logcons (bool->bit b) x))


;; Same as intcons, but will unify with any integer as opposed to just ones
;; that (syntactically) appear to have more than 1 bit.
(define intcons* ((b booleanp)
                  (x integerp))
  :returns (val)
  :enabled t
  (logcons (bool->bit b) x))

;; Returns 0 or -1 depending on B.  Treated specially by the unification
;; algorithm, matching 0 and -1 as well as symbolic integers that syntactically
;; have only 1 bit.
(define endint ((b booleanp))
  :returns (val)
  :enabled t
  (- (bool->bit b)))


(define intcar ((x integerp))
  :returns (val)
  :enabled t
  (eql (logcar x) 1))

(define intcdr ((x integerp))
  :returns (val)
  :enabled t
  (logcdr x))

(define int-endp ((x integerp))
  (or (zip x)
      (eql x -1)))

(define s-endp ((v true-listp))
  :parents (fgl-bitvector)
  :short "Are we at the end of a signed bit vector?"
  :inline t
  ;; MBE just for a simpler logical definition
  (atom (cdr v))
  ///
  (defthm s-endp-of-list-fix
    (equal (s-endp (acl2::list-fix x))
           (s-endp x)))

  (defthm not-s-endp-compound-recognizer
    (implies (not (s-endp x))
             (consp x))
    :rule-classes :compound-recognizer))


(local (defthm acl2-count-of-list-fix
         (<= (acl2-count (list-fix x)) (acl2-count x))
         :rule-classes :linear))

(define scdr ((v true-listp))
  :returns (cdr true-listp :rule-classes :type-prescription)
  :parents (fgl-bitvector)
  :short "Like @(see logcdr) for signed bit vectors."
  :long "<p>For a signed bit vector, the final bit is the
sign bit, which we must implicitly extend out to infinity.</p>"
  :inline t
  ;; MBE just for a simpler logical definition
  (let ((v (llist-fix v)))
    (if (atom (cdr v))
        ;; No more bits, so don't CDR the vector any more.
        v
      (cdr v)))
  ///

  (defthm scdr-of-list-fix
    (equal (scdr (acl2::list-fix x))
           (acl2::list-fix (scdr x))))

  (defthm scdr-count-weak
    (<= (acl2-count (scdr v)) (acl2-count v))
    :hints(("Goal" :in-theory (enable s-endp scdr)))
    :rule-classes :linear)

  (defthm scdr-count-strong
    (implies (not (s-endp v))
             (< (acl2-count (scdr v)) (acl2-count v)))
    :hints(("Goal" :in-theory (enable s-endp scdr)))
    :rule-classes :linear)

  (defthm scdr-len-strong
    (implies (not (s-endp v))
             (< (len (scdr v)) (len v)))
    :hints(("Goal" :in-theory (enable s-endp scdr)))
    :rule-classes :linear)

  (defthm scdr-len-weak
    (<= (len (scdr v)) (len v))
    :hints(("Goal" :in-theory (enable s-endp scdr)))
    :rule-classes :linear)

  (defthm s-endp-of-scdr
    (implies (s-endp b)
             (s-endp (scdr b)))
    :hints(("Goal" :in-theory (enable s-endp scdr))))

  (defthm scdr-when-s-endp
    (implies (s-endp x)
             (equal (scdr x) (list-fix x)))
    :hints(("Goal" :in-theory (enable scdr s-endp)))
    ;; :rule-classes ((:rewrite :backchain-limit-lst 0))
    ))

(define scons (bit0 (rest-bits true-listp))
  :returns (bits true-listp)
  :inline t
  (if (and 
       (mbe :logic (atom (cdr rest-bits))
            :exec (or (atom rest-bits) (atom (cdr rest-bits))))
       (hons-equal bit0 (mbe :logic (car rest-bits)
                             :exec (and (consp rest-bits) (car rest-bits)))))
      (mbe :logic (true-list-fix rest-bits)
           :exec rest-bits)
    (cons bit0
          (if (atom rest-bits)
              '(nil)
            (mbe :logic (true-list-fix rest-bits)
                 :exec rest-bits))))
  ///

  (local (defthm bit-identity
           (implies (bitp x)
                    (equal (+ x (* 2 (- x))) (- x)))))

  (defret bools->int-of-scons
    (equal (bools->int bits)
           (intcons bit0 (bools->int rest-bits)))
    :hints(("Goal" :in-theory (enable bools->int))))

  (defret member-of-scons
    (implies (and (not (equal v bit0))
                  (not (member v rest-bits))
                  v)
             (not (member v bits)))))


(define first/rest/end ((x true-listp))
  :parents (fgl-bitvector)
  :short "Deconstruct a signed bit vector."
  :enabled t
  (declare (xargs :guard t
                  :guard-hints ('(:in-theory (enable scdr s-endp)))))
  (mbe :logic (mv (car x) (scdr x) (s-endp x))
       :exec (cond ((atom x)       (mv nil x t))
                   ((atom (cdr x)) (mv (car x) x t))
                   (t              (mv (car x) (cdr x) nil)))))


;; Unifies with any integer or g-integer
(define int (x)
  :enabled t
  (ifix x))

;; Unifies with any Boolean or g-boolean
(define bool (x)
  :enabled t
  (bool-fix x))

;; Unifies with any concrete value.
(define concrete (x)
  :enabled t
  x)


(define int->bools ((x integerp))
  :measure (integer-length x)
  (b* ((x (lifix x))
       ((when (eql x 0)) '(nil))
       ((when (eql x -1)) '(t)))
    (cons (intcar x)
          (int->bools (intcdr x)))))

      


;; Catchall: simple functions that will be given various behavior by the interpreter.
(encapsulate
  (((fgl-toplevel-sat-check-config) => *))
  (local (defun fgl-toplevel-sat-check-config () nil)))


(define fgl-sat-check ((params "Parameters for the SAT check -- depending on the
                                attachment for the pluggable checker.")
                       (x "Object to check for satisfiability."))
  :parents (fgl-solving)
  :short "Checking satisfiability of intermediate terms during FGL interpretation."
  :long "

<p>Logically, @('(fgl-sat-check params x)') just returns @('x') fixed to a
Boolean value.  But when FGL symbolic execution encounters an
@('fgl-sat-check') term, it checks Boolean satisfiability of @('x') and if it
is able to prove that all evaluations of @('x') are NIL, then it returns NIL;
otherwise, it returns @('x') unchanged.  To instead perform a validity check,
you could do:</p>
@({
 (not (fgl-sat-check params (not x)))
 })

<p>It isn't necessary to call this around the entire conclusion of the theorem
you wish to prove -- FGL SAT-checks the final result of symbolically
executing the conclusion by default; see @(see fgl-solving).  The purpose of
@('fgl-sat-check') is to force SAT checks during symbolic execution, so as
to e.g. avoid unnecessary execution paths.</p>

<p>The counterexamples from intermediate SAT checks may be pulled out of the
interpreter state during symbolic execution using @(see syntax-bind) forms.
For example, the rewrite rule @('show-counterexample-rw') demonstrates how to
extract a counterexample from SAT and print it when a @('show-counterexample')
term is encountered.</p>

<p>See also @(see fgl-sat-check/print-counterexample) for a version that prints
counterexample info for the stack frame from which it is called.</p>"
  (declare (ignore params))
  (if x t nil))


(defun show-counterexample (params msg)
  (declare (ignore params msg))
  nil)

(defun show-top-counterexample (params msg)
  (declare (ignore params msg))
  nil)

(defun fgl-pathcond-fix (x)
  (declare (xargs :guard t))
  x)




(defmacro fgl-validity-check (params x)
  `(not (fgl-sat-check ,params (not ,x))))
