; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "bfr")
(include-book "ihs/logops-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(defsection bvec
  :parents (reference)
  :short "Internal representations of symbolic bit vectors."

  :long "<p>GL's core symbolic arithmetic functions operate on lists of @(see
BFR)s, which may be interpreted either as signed or unsigned symbolic
integers.</p>

<p>For unsigned bit vectors this is entirely straightforward.  We use an
LSB-first encoding of the bits, so the @(see car) of a BFR list represents the
least significant bit of the natural number, a la @(see logcar), whereas the
@(see cdr) of the BFR represents its more significant bits, a la @(see
logcdr).</p>

<p>For signed bit vectors, we use a similar encoding except that we interpret
the final bit of the number as the sign bit.  So, when working on a signed bit
vector, we generally use @(see scdr) instead of just @(see cdr).</p>")

(local (xdoc::set-default-parents bvec))

(define bfr-eval-list (x env)
  :returns (bools boolean-listp)
  :short "Evaluate a list of BFRs, return the list of the (Boolean) results."
  (if (atom x)
      nil
    (cons (bfr-eval (car x) env)
          (bfr-eval-list (cdr x) env)))
  ///
  (defthm bfr-eval-list-when-atom
    (implies (atom x)
             (equal (bfr-eval-list x env) nil)))

  (defthm bfr-eval-list-of-cons
    (equal (bfr-eval-list (cons a x) env)
           (cons (bfr-eval a env)
                 (bfr-eval-list x env))))

  (defthm consp-of-bfr-eval-list
    (equal (consp (bfr-eval-list x env))
           (consp x)))

  (defthm bfr-eval-list-of-append
    (equal (bfr-eval-list (append a b) env)
           (append (bfr-eval-list a env)
                   (bfr-eval-list b env))))

  (defthmd boolean-list-bfr-eval-list
    (implies (boolean-listp x)
             (equal (bfr-eval-list x env) x))
    :hints (("goal" :in-theory (enable bfr-eval-list boolean-listp))))

  (defthm boolean-list-bfr-eval-list-const
    (implies (and (syntaxp (quotep x))
                  (boolean-listp x))
             (equal (bfr-eval-list x env) x))
    :hints (("goal" :in-theory (enable bfr-eval-list boolean-listp))))

  (defthm bfr-eval-list-of-list-fix
    (equal (bfr-eval-list (acl2::list-fix x) env)
           (bfr-eval-list x env))))


(define bfr-eval-alist (al env)
  :short "Evaluate an alist that maps names to BFRs, returning an alist mapping
the same names to their (Boolean) results."
  :parents (bfr-eval)
  :enabled t
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al)
                    (bfr-eval (cdar al) env))
              (bfr-eval-alist (cdr al) env))
      (bfr-eval-alist (cdr al) env))))


(define pbfr-list-depends-on (k p x)
  :verify-guards nil
  (if (atom x)
      nil
    (or (pbfr-depends-on k p (car x))
        (pbfr-list-depends-on k p (cdr x))))
  ///
  (defthm pbfr-list-depends-on-of-list-fix
    (equal (pbfr-list-depends-on k p (acl2::list-fix x))
           (pbfr-list-depends-on k p x))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))

  (defthm bfr-eval-list-of-set-non-dep
    (implies (and (not (pbfr-list-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-eval-list x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-eval-list x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))

  (defthm pbfr-depends-on-car
    (implies (not (pbfr-list-depends-on k p x))
             (not (pbfr-depends-on k p (car x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on default-car))))

  (defthm pbfr-depends-on-cdr
    (implies (not (pbfr-list-depends-on k p x))
             (not (pbfr-list-depends-on k p (cdr x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))


(define s-endp ((v true-listp))
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
  :short "Like @(see logcdr) for signed bvecs."
  :long "<p>See @(see bvec).  For a signed bit vector, the final bit is the
sign bit, which we must implicitly extend out to infinity.</p>"
  :inline t
  ;; MBE just for a simpler logical definition
  (let ((v (llist-fix v)))
    (if (atom (cdr v))
        ;; No more bits, so don't CDR the vector any more.
        v
      (cdr v)))
  ///
  (defthm pbfr-list-depends-on-scdr
    (implies (not (pbfr-list-depends-on k p x))
             (not (pbfr-list-depends-on k p (scdr x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))

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
    :rule-classes ((:rewrite :backchain-limit-lst 0))))



(define first/rest/end ((x true-listp))
  :short "Deconstruct a signed bit vector."
  :enabled t
  (declare (xargs :guard t
                  :guard-hints ('(:in-theory (enable scdr s-endp)))))
  (mbe :logic (mv (car x) (scdr x) (s-endp x))
       :exec (cond ((atom x)       (mv nil x t))
                   ((atom (cdr x)) (mv (car x) x t))
                   (t              (mv (car x) (cdr x) nil)))))


(define bool->sign (x)
  :short "Interpret a sign bit as an integer: true &rarr; -1, false &rarr; 0."
  :enabled t
  (if x -1 0))


(define bfr-list->s ((x   true-listp "BFR list to interpret as a signed number.")
                     (env "Environment to evaluate the BFRs under."))
  :short "Signed interpretation of a BFR list under some environment."
  :enabled t ;; bozo for backwards compatibility
  (b* (((mv first rest end) (first/rest/end x)))
    (if end
        ;; Infinitely extend the final bit
        (bool->sign (bfr-eval first env))
      (logcons (acl2::bool->bit (bfr-eval first env))
               (bfr-list->s rest env))))
  ///
  (defthm bfr-list->s-of-list-fix
    (equal (bfr-list->s (acl2::list-fix x) env)
           (bfr-list->s x env)))

  (defthm bfr-list->s-when-s-endp
    (implies (s-endp x)
             (equal (bfr-list->s x env)
                    (bool->sign (bfr-eval (car x) env))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthmd bfr-list->s-of-scdr
    (equal (bfr-list->s (scdr x) env)
           (logcdr (bfr-list->s x env))))

  (defthm logcdr-of-bfr-list->s
    (equal (logcdr (bfr-list->s x env))
           (bfr-list->s (scdr x) env)))

  (defthm logcar-of-bfr-list->s
    (equal (logcar (bfr-list->s x env))
           (acl2::bool->bit (bfr-eval (car x) env))))

  (defthm bfr-list->s-of-set-non-dep
    (implies (and (not (pbfr-list-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-list->s x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-list->s x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))


(define bfr-snorm ((v true-listp))
  :returns (vv true-listp :rule-classes :type-prescription)
  (if (atom v) '(nil) (llist-fix v))
  ///
  (defthm s-endp-of-bfr-snorm
    (equal (s-endp (bfr-snorm v))
           (s-endp v))
    :hints(("Goal" :in-theory (enable s-endp bfr-snorm))))

  (defthm scdr-of-bfr-snorm
    (equal (scdr (bfr-snorm v))
           (bfr-snorm (scdr v)))
    :hints(("Goal" :in-theory (enable scdr bfr-snorm))))

  (defthm car-of-bfr-snorm
    (equal (car (bfr-snorm v))
           (car v))
    :hints(("Goal" :in-theory (enable bfr-snorm))))

  (defthm bfr-list->s-of-bfr-snorm
    (equal (bfr-list->s (bfr-snorm v) env)
           (bfr-list->s v env))
    :hints(("Goal" :in-theory (e/d (bfr-list->s)
                                   (bfr-snorm)))))

  (defthm bfr-snorm-of-list-fix
    (equal (bfr-snorm (list-fix x)) (bfr-snorm x))))

(define bfr-scons (b (v true-listp))
  :short "Like @(see logcons) for signed bvecs."
  :returns (s true-listp :rule-classes :type-prescription)
  (if (atom v)
      (if b (list b nil) '(nil))
    (if (and (atom (cdr v))
             (hons-equal (car v) b))
        (llist-fix v)
      (cons b (llist-fix v))))
  ///

  (defthm scdr-of-bfr-scons
    (equal (scdr (bfr-scons b v))
           (bfr-snorm v))
    :hints(("Goal" :in-theory (enable bfr-snorm bfr-scons scdr))))

  (defthm s-endp-of-bfr-scons
    (equal (s-endp (bfr-scons b v))
           (and (s-endp v)
                (hqual b (car v))))
    :hints(("Goal" :in-theory (enable s-endp bfr-scons))))

  (defthm car-of-bfr-scons
    (equal (car (bfr-scons b v))
           b)
    :hints(("Goal" :in-theory (enable bfr-scons))))

  (defthm bfr-list->s-of-bfr-scons
    (equal (bfr-list->s (bfr-scons b x) env)
           (logcons (acl2::bool->bit (bfr-eval b env))
                    (bfr-list->s x env)))
    :hints(("Goal" ;:in-theory (enable bfr-scons scdr s-endp)
            :in-theory (e/d (bfr-list->s)
                            (bfr-scons))
            :expand ((bfr-list->s (bfr-scons b x) env))
            :do-not-induct t)))

  (defthm pbfr-list-depends-on-of-scons
    (implies (and (not (pbfr-depends-on k p b))
                  (not (pbfr-list-depends-on k p x)))
             (not (pbfr-list-depends-on k p (bfr-scons b x))))
    :hints(("Goal" :in-theory (enable bfr-scons pbfr-list-depends-on))))

  (defthm bfr-scons-of-list-fix
    (equal (bfr-scons b (list-fix v)) (bfr-scons b v))))


(define bfr-sterm (b)
  :short "Promote a single BFR into a signed, one-bit bvec, i.e., the resulting
value under @(see bfr-list->s) is either 0 or -1, depending on the
environment."
  (list b)
  ///
  (defthm s-endp-of-bfr-sterm
    (equal (s-endp (bfr-sterm b)) t)
    :hints(("Goal" :in-theory (enable s-endp))))

  (defthm scdr-of-bfr-sterm
    (equal (scdr (bfr-sterm b))
           (bfr-sterm b))
    :hints(("Goal" :in-theory (enable scdr))))

  (defthm car-of-bfr-sterm
    (equal (car (bfr-sterm b))
           b))

  (defthm bfr-list->s-of-bfr-sterm
    (equal (bfr-list->s (bfr-sterm b) env)
           (bool->sign (bfr-eval b env)))
    :hints(("Goal" :in-theory (e/d (bfr-list->s)
                                   (bfr-sterm)))))

  (defthm pbfr-list-depends-on-of-bfr-sterm
    (equal (pbfr-list-depends-on k p (bfr-sterm b))
           (pbfr-depends-on k p b))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on bfr-sterm)))))



(define i2v (n)
  ;; BOZO consider stronger guard
  ;; BOZO consider renaming N to I
  :short "Convert an integer into a corresponding signed bvec (with constant bits)."
  :measure (integer-length n)
  :hints(("Goal" :in-theory (enable acl2::integer-length**)))
  :enabled t ;; BOZO for backwards compatibility
  (cond ((eql 0 (ifix n)) '(nil))
        ((eql n -1) '(t))
        (t (bfr-scons (equal (logcar n) 1) (i2v (logcdr n)))))
  ///
  ;; (defthm true-listp-of-i2v
  ;;   (true-listp (i2v n))
  ;;   :rule-classes :type-prescription)

  (defthm bfr-list->s-of-i2v
    (equal (bfr-list->s (i2v n) env)
           (ifix n))
    :hints(("Goal" :in-theory (enable bfr-list->s))))

  (defthm pbfr-list-depends-on-of-i2v
    (not (pbfr-list-depends-on k p (i2v n)))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on i2v)))))



(define bfr-list->u ((x   "BFR List to interpret as an unsigned number.")
                     (env "Environment to evaluate the BFRs under."))
  :short "Unsigned interpretation of a BFR list under some environment."
  :enabled t ;; bozo for backwards compatibility
  (if (atom x)
      0
    (logcons (acl2::bool->bit (bfr-eval (car x) env))
             (bfr-list->u (cdr x) env)))
  ///
  (defthm bfr-list->u-of-list-fix
    (equal (bfr-list->u (acl2::list-fix x) env)
           (bfr-list->u x env)))

  (defthm bfr-list->u-type
    (natp (bfr-list->u x env))
    :rule-classes :type-prescription)

  (in-theory (disable (:t bfr-list->u)))

  (defthm bfr-list->u-of-set-non-dep
    (implies (and (not (pbfr-list-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-list->u x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-list->u x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))


(define bfr-ucons (b (x true-listp))
  :short "Like @(see logcons) for unsigned bvecs."
  :returns (new-x true-listp :rule-classes :type-prescription)
  (if (and (atom x) (not b))
      nil
    (cons b (llist-fix x)))
  ///

  (defthm bfr-list->u-of-bfr-ucons
    (equal (bfr-list->u (bfr-ucons b x) env)
           (logcons (acl2::bool->bit (bfr-eval b env))
                    (bfr-list->u x env)))
    :hints(("Goal" :in-theory (enable bfr-list->u))))

  (defthm pbfr-list-depends-on-of-bfr-ucons
    (implies (and (not (pbfr-depends-on k p b))
                  (not (pbfr-list-depends-on k p x)))
             (not (pbfr-list-depends-on k p (bfr-ucons b x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))

  (defthm bfr-ucons-of-list-fix
    (equal (bfr-ucons b (list-fix x))
           (bfr-ucons b x))))


(define n2v (n)
  ;; BOZO Consider stronger guard
  :short "Convert a natural into a corresponding unsigned bvec (with constant bits)."
  :enabled t ;; BOZO for backwards compatibility
  (if (eql (nfix n) 0)
      nil
    (bfr-ucons (equal 1 (logcar n))
               (n2v (logcdr n))))
  ///
  (defthm true-listp-of-n2v
    (true-listp (n2v n))
    :rule-classes :type-prescription)

  (defthm bfr-list->u-of-n2v
    (equal (bfr-list->u (n2v n) env)
           (nfix n))
    :hints(("Goal" :in-theory (enable bfr-list->u))))

  (defthm pbfr-list-depends-on-of-n2v
    (not (pbfr-list-depends-on k p  (n2v n)))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on n2v)))))



(define v2i ((v true-listp))
  ;; BOZO it would be natural to express bfr-list->s as a function that produced
  ;; a list of booleans, which we then interpreted using v2i
  :short "Convert a (pure constant) signed bvec into an integer."
  :verify-guards nil
  :enabled t ;; BOZO for backwards compatibility
  (mbe :logic
       (if (s-endp v)
           (bool->sign (car v))
         (logcons (acl2::bool->bit (car v))
                  (v2i (scdr v))))
       :exec
       (if (atom v)
           0
         (if (atom (cdr v))
             (if (car v) -1 0)
           (logcons (acl2::bool->bit (car v))
                    (v2i (cdr v))))))
  ///
  (verify-guards v2i
    :hints(("goal" :in-theory (enable logcons s-endp scdr
                                      acl2::bool->bit))))

  (defthm v2i-of-bfr-eval-list
    (equal (v2i (bfr-eval-list x env))
           (bfr-list->s x env))
    :hints(("Goal" :induct (bfr-list->s x env)
            :expand ((bfr-eval-list x env))
            :in-theory (enable s-endp scdr default-car bfr-list->s))))

  (defthm v2i-of-i2v
    (equal (v2i (i2v x))
           (ifix x))
    :hints(("Goal" :in-theory (enable bfr-scons s-endp scdr i2v)))))


(define v2n ((v true-listp))
  :short "Convert an unsigned bvec into the corresponding natural."
  :enabled t ;; BOZO for backwards compatibility
  (if (atom v)
      0
    (logcons (acl2::bool->bit (car v))
             (v2n (cdr v))))
  ///
  (defthm v2n-of-bfr-eval-list
    (equal (v2n (bfr-eval-list x env))
           (bfr-list->u x env))
    :hints(("Goal" :in-theory (enable bfr-list->u))))

  (defthm v2n-of-n2v
    (equal (v2n (n2v x))
           (nfix x))
    :hints(("Goal" :in-theory (enable bfr-ucons
                                      n2v)))))





(defcong bfr-env-equiv equal (bfr-list->s x env) 2)
(defcong bfr-env-equiv equal (bfr-list->u x env) 2)
