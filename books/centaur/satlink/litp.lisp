; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; litp.lisp -- Definition of CNF Literals, Clauses (lit-listp's), and Formulas
; (lit-list-listp's).

(in-package "SATLINK")
(include-book "varp")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(set-tau-auto-mode nil)

(define litp (x)
  :parents (cnf)
  :short "Representation of a literal (a Boolean variable or its negation)."

  :long "<p>Think of a <b>LITERAL</b> as an abstract data type that can either
represent a Boolean variable or its negation.  More concretely, you can think
of a literal as an structure with two fields:</p>

<ul>
<li>@('var'), a variable, represented as an @(see varp), and</li>
<li>@('neg'), a bit that says whether the variable is negated or not,
represented as a @(see bitp).</li>
</ul>

<p>In the implementation, we use an efficient natural-number encoding rather
than some kind of cons structure: @('neg') is the bottom bit of the literal,
and @('var') is the remaining bits.  (This trick exploits the representation of
identifiers as natural numbers.)</p>"

  (natp x)

  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (bool booleanp :rule-classes :tau-system))


(local (in-theory (enable litp)))


(define to-lit ((nat natp))
  :parents (litp)
  :short "Raw constructor for literals."
  :long "<p>This exposes the underlying representation of literals.  You
should generally use @(see make-lit) instead.</p>"

  (lnfix nat)

  :inline t
  :returns (lit litp :rule-classes (:rewrite :tau-system)))


(define lit-val ((lit litp))
  :parents (litp)
  :short "Raw value of a literal."
  :long "<p>This exposes the underlying representation of literals.  You should
generally use @(see lit->index) and @(see lit->neg) instead.</p>"

  (lnfix lit)

  :inline t
  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (nat natp :rule-classes (:rewrite :tau-system)))

(local (in-theory (enable to-lit lit-val)))


(define lit-equiv ((x litp) (y litp))
  :parents (litp)
  :short "Basic equivalence relation for literals."
  :enabled t

  (int= (lit-val x) (lit-val y))

  ///

  (defequiv lit-equiv)

  ;; BOZO ugly event name stuff works around defcong name stupidity and
  ;; incompatibility with defcongs for to-lit in the aignet package.
  (defcong lit-equiv equal (lit-val x) 1
    :event-name lit-equiv-implies-equal-lit-val-1)

  (defcong nat-equiv equal (to-lit x) 1
    :event-name nat-equiv-implies-equal-to-lit-1))


(define lit-fix ((x litp))
  :parents (litp)
  :short "Basic fixing function for literals."

  (to-lit (lit-val x))

  :inline t
  :returns (x-fix litp)

  ///

  (defcong lit-equiv equal (lit-fix x) 1
    :event-name lit-equiv-implies-equal-lit-fix-1)

  (defthm lit-fix-of-lit
    (implies (litp x)
             (equal (lit-fix x) x)))

  (defthm lit-equiv-of-lit-fix
    (lit-equiv (lit-fix lit) lit)))

(local (in-theory (enable lit-fix)))


(defsection lit-raw-theorems
  :parents (litp)
  :short "Basic theorems about raw literal functions like @(see to-lit) and
@(see lit-val)."

  (defthm lit-val-of-to-lit
    (equal (lit-val (to-lit x))
           (nfix x)))

  (defthm lit-equiv-of-to-lit-of-lit-val
    (lit-equiv (to-lit (lit-val lit)) lit))

  (defthm equal-of-to-lit-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (to-lit$inline ,x) ,y)
                       mfc state))
             (equal (equal (to-lit x) y)
                    (and (litp y)
                         (equal (nfix x) (lit-val y))))))

  (defthm equal-of-lit-fix-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (lit-fix$inline ,x) ,y)
                       mfc state))
             (equal (equal (lit-fix x) y)
                    (and (litp y)
                         (equal (lit-val x) (lit-val y))))))

  (defthm equal-of-to-lit-backchain
    (implies (and (litp y)
                  (equal (nfix x) (lit-val y)))
             (equal (equal (to-lit x) y) t))
    :hints (("goal" :use equal-of-to-lit-hyp)))

  (defthm equal-of-lit-fix-backchain
    (implies (and (litp y)
                  (equal (lit-val x) (lit-val y)))
             (equal (equal (lit-fix x) y) t))
    :hints (("goal" :use equal-of-to-lit-hyp)))

  (in-theory (disable litp to-lit lit-val))

  (defthm equal-lit-val-forward-to-lit-equiv
    (implies (and (equal (lit-val x) y)
                  (syntaxp (not (and (consp y)
                                     (or (eq (car y) 'lit-val)
                                         (eq (car y) 'nfix))))))
             (lit-equiv x (to-lit y)))
    :rule-classes :forward-chaining)

  (defthm equal-lit-val-nfix-forward-to-lit-equiv
    (implies (equal (lit-val x) (nfix y))
             (lit-equiv x (to-lit y)))
    :rule-classes :forward-chaining)

  (defthm equal-lit-val-forward-to-lit-equiv-both
    (implies (equal (lit-val x) (lit-val y))
             (lit-equiv x y))
    :rule-classes :forward-chaining)

  (defthm to-lit-of-lit-val
    (equal (to-lit (lit-val x))
           (lit-fix x))))



(local (in-theory (disable litp
                           to-lit
                           lit-val
                           lit-fix)))


(local (in-theory (enable* acl2::ihsext-recursive-redefs
                           acl2::ihsext-bounds-thms
                           nfix natp)))


(define lit->var ((lit litp))
  :parents (litp)
  :short "Access the @('var') component of a literal."

  (make-var (ash (the (integer 0 *) (lit-val lit))
                 -1))

  :inline t
  ;; BOZO type-prescription doesn't make sense unless we strengthen
  ;; the compound-recognizer rule for varp?
  :returns (var varp :rule-classes (:rewrite :type-prescription))

  ///
  (defcong lit-equiv equal (lit->var lit) 1))


(define lit->neg ((lit litp))
  :parents (litp)
  :short "Access the @('neg') bit of a literal."

  (the bit (logand 1 (the (integer 0 *) (lit-val lit))))

  :inline t
  :returns (neg bitp)

  ///

  (defthm natp-of-lit->neg
    ;; You might think this is unnecessary because ACL2 should infer it.  That's
    ;; true here, but when we include this file in other books that don't know
    ;; about LOGAND we lose it.  So, we make it explicit.
    (natp (lit->neg lit))
    :rule-classes (:type-prescription :tau-system))

  (in-theory (disable (:t lit->neg)))

  (defthm lit->neg-bound
    (<= (lit->neg lit) 1)
    :rule-classes :linear)

  (defcong lit-equiv equal (lit->neg lit) 1))


(acl2::def-b*-decomp lit
                     (var . lit->var)
                     (neg . lit->neg))


(define make-lit ((var varp) (neg bitp))
  :parents (litp)
  :short "Construct a literal with the given @('var') and @('neg')."

  (to-lit (the (integer 0 *)
            (logior (the (integer 0 *)
                      (ash (the (integer 0 *) (var->index var)) 1))
                    (the bit (lbfix neg)))))

  :inline t
  ;; BOZO type-prescription doesn't make sense unless we strenghten
  ;; the compound-recognizer rule for litp?
  :returns (lit litp :rule-classes (:rewrite :type-prescription))
  :prepwork ((local (in-theory (enable lit->var lit->neg))))
  ///
  (defcong var-equiv equal (make-lit var neg) 1)
  (defcong bit-equiv equal (make-lit var neg) 2)

  (defthm lit->var-of-make-lit
    (equal (lit->var (make-lit var neg))
           (var-fix var)))

  (defthm lit->neg-of-make-lit
    (equal (lit->neg (make-lit var neg))
           (bfix neg)))

  (defthm make-lit->varentity
    (equal (make-lit (lit->var lit)
                     (lit->neg lit))
           (lit-fix lit))
    :hints(("Goal" :in-theory (disable bitops::logior$))))

  (local (defthm equal-of-make-lit-lemma
           (implies (and (varp var) (bitp neg))
                    (equal (equal a (make-lit var neg))
                           (and (litp a)
                                (equal (var->index (lit->var a)) (var->index var))
                                (equal (lit->neg a) neg))))
           :hints(("Goal" :in-theory (disable make-lit
                                              make-lit->varentity
                                              lit->var lit->neg)
                   :use ((:instance make-lit->varentity (lit a)))))
           :rule-classes nil))

  (defthmd equal-of-make-lit
    (equal (equal a (make-lit var neg))
           (and (litp a)
                (equal (var->index (lit->var a)) (var->index var))
                (equal (lit->neg a) (bfix neg))))
    :hints(("Goal" :use ((:instance equal-of-make-lit-lemma
                          (var (var-fix var)) (neg (bfix neg))))
            :in-theory (disable lit->var lit->neg)))))


(local (in-theory (e/d (bitops::logxor**)
                       (bitops::logior$ bitops::logxor$))))


(define lit-negate ((lit litp))
  :parents (litp)
  :short "Efficiently negate a literal."
  :enabled t
  :inline t
  (mbe :logic (b* ((var (lit->var lit))
                   (neg (lit->neg lit)))
                (make-lit var (b-not neg)))
       :exec (to-lit
              (the (integer 0 *)
                (logxor (the (integer 0 *) (lit-val lit))
                        1))))

  :guard-hints(("Goal" :in-theory (enable make-lit lit->var lit->neg))))



(define lit-negate-cond ((lit litp) (c bitp))
  :parents (litp)
  :short "Efficiently negate a literal."
  :long "<p>When @('c') is 1, we negate @('lit').  Otherwise, when @('c') is 0,
we return @('lit') unchanged.</p>"
  :enabled t
  :inline t

  (mbe :logic (b* ((var (lit->var lit))
                   (neg (b-xor (lit->neg lit) c)))
                (make-lit var neg))
       :exec (to-lit (the (integer 0 *)
                       (logxor (the (integer 0 *) (lit-val lit))
                               (the bit c)))))

  :guard-hints(("Goal" :in-theory (enable make-lit lit->var lit->neg)))

  ///

  (defthmd lit-negate-cond-correct
    (implies (and (litp lit)
                  (bitp c))
             (equal (lit-negate-cond lit c)
                    (if (= c 1)
                        (lit-negate lit)
                      lit)))
    :hints(("Goal" :in-theory (enable b-xor equal-of-make-lit)))))


(define lit-listp (x)
  :parents (litp)
  :short "Recognize a list of literals."

  (if (atom x)
      (eq x nil)
    (and (litp (car x))
         (lit-listp (cdr x))))

  ///
  (defthm lit-listp-when-atom
    (implies (atom x)
             (equal (lit-listp x)
                    (not x))))

  (defthm lit-listp-of-cons
    (equal (lit-listp (cons a x))
           (and (litp a)
                (lit-listp x))))

  (defthm true-listp-when-lit-listp
    (implies (lit-listp x)
             (true-listp x))
    :rule-classes :compound-recognizer))


(define lit-list-listp (x)
  :parents (litp)
  :short "Recognize a list of @(see lit-listp)s."

  (if (atom x)
      (eq x nil)
    (and (lit-listp (car x))
         (lit-list-listp (cdr x))))

  ///
  (defthm lit-list-listp-when-atom
    (implies (atom x)
             (equal (lit-list-listp x)
                    (not x))))

  (defthm lit-list-listp-of-cons
    (equal (lit-list-listp (cons a x))
           (and (lit-listp a)
                (lit-list-listp x))))

  (defthm true-listp-when-lit-list-listp
    (implies (lit-list-listp x)
             (true-listp x))
    :rule-classes :compound-recognizer))


(defsection lit->index
  :parents (litp)
  :short "Shorthand for @('(var->index (lit->var x))')."
  :long "@(def lit->index)"

  (defmacro lit->index (x)
    `(var->index (lit->var ,x))))

