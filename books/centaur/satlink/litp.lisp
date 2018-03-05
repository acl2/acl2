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
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable nfix)))
(set-tau-auto-mode nil)

(local (std::add-default-post-define-hook :fix))

(define litp (x)
  :parents (cnf)
  :short "Representation of a literal (a Boolean variable or its negation)."

  :long "<p>Think of a <b>LITERAL</b> as an abstract data type that can either
represent a Boolean variable or its negation.  More concretely, you can think
of a literal as an structure with two fields:</p>

<ul>
<li>@('var'), a variable, represented as a natural number, and</li>
<li>@('neg'), a bit that says whether the variable is negated or not,
represented as a @(see bitp).</li>
</ul>

<p>In the implementation, we use an efficient natural-number encoding rather
than some kind of cons structure: @('neg') is the bottom bit of the literal,
and @('var') is the remaining bits.  (This trick exploits the representation of
identifiers as natural numbers.)</p>"

  (natp x)

  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (bool booleanp :rule-classes :tau-system)
  ///
  (defthm litp-compound-recognizer
    (equal (litp x) (natp x))
    :rule-classes :compound-recognizer))


(local (in-theory (enable litp)))




(define lit-fix ((x litp))
  :parents (litp)
  :short "Basic fixing function for literals."
  :guard-hints (("goal" :in-theory (enable litp)))
  (lnfix x)

  :inline t
  :returns (x-fix litp :rule-classes :type-prescription)

  ///

  (defthm lit-fix-of-lit
    (implies (litp x)
             (equal (lit-fix x) x))))


(define lit-equiv ((x litp) (y litp))
  :parents (litp)
  :short "Basic equivalence relation for literals."
  :enabled t
  (int= (lit-fix x) (lit-fix y))

  ///

  (defequiv lit-equiv)
  
  (local (in-theory (enable lit-fix)))

  (defcong lit-equiv equal (lit-fix x) 1
    :event-name lit-equiv-implies-equal-lit-fix-1)

  (defthm lit-equiv-of-lit-fix
    (lit-equiv (lit-fix lit) lit))

  (fty::deffixtype lit :pred litp :fix lit-fix :equiv lit-equiv
    :forward t))

(local (in-theory (enable lit-fix lit-equiv)))


;; (define to-lit ((nat natp))
;;   :parents (litp)
;;   :short "Raw constructor for literals."
;;   :long "<p>This exposes the underlying representation of literals.  You
;; should generally use @(see make-lit) instead.</p>"

;;   (lnfix nat)

;;   :inline t
;;   :returns (lit litp :rule-classes (:rewrite :tau-system)))


;; (define lit-val ((lit litp))
;;   :parents (litp)
;;   :short "Raw value of a literal."
;;   :long "<p>This exposes the underlying representation of literals.  You should
;; generally use @(see lit->index) and @(see lit->neg) instead.</p>"

;;   (lnfix lit)

;;   :inline t
;;   ;; Not :type-prescription, ACL2 infers that automatically
;;   :returns (nat natp :rule-classes (:rewrite :tau-system)))

;; (local (in-theory (enable to-lit lit-val)))


;; (defsection lit-raw-theorems
;;   :parents (litp)
;;   :short "Basic theorems about raw literal functions like @(see to-lit) and
;; @(see lit-val)."

;;   (defthm lit-val-of-to-lit
;;     (equal (lit-val (to-lit x))
;;            (nfix x)))

;;   (defthm lit-equiv-of-to-lit-of-lit-val
;;     (lit-equiv (to-lit (lit-val lit)) lit))

;;   (defthm equal-of-to-lit-hyp
;;     (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
;;                            `(equal (to-lit$inline ,x) ,y)
;;                            mfc state)
;;                           (acl2::rewriting-negative-literal-fn
;;                            `(equal ,y (to-lit$inline ,x))
;;                            mfc state)))
;;              (equal (equal (to-lit x) y)
;;                     (and (litp y)
;;                          (equal (nfix x) (lit-val y))))))

;;   (defthm equal-of-to-lit-backchain
;;     (implies (and (litp y)
;;                   (equal (nfix x) (lit-val y)))
;;              (equal (equal (to-lit x) y) t))
;;     :hints (("goal" :use equal-of-to-lit-hyp)))

;;   (defthm equal-lit-val-forward-to-lit-equiv
;;     (implies (and (equal (lit-val x) y)
;;                   (syntaxp (not (and (consp y)
;;                                      (or (eq (car y) 'lit-val)
;;                                          (eq (car y) 'nfix))))))
;;              (lit-equiv x (to-lit y)))
;;     :rule-classes :forward-chaining)

;;   (defthm equal-lit-val-nfix-forward-to-lit-equiv
;;     (implies (equal (lit-val x) (nfix y))
;;              (lit-equiv x (to-lit y)))
;;     :rule-classes :forward-chaining)

;;   ;; (defthm equal-lit-val-forward-to-lit-equiv-both
;;   ;;   (implies (equal (lit-val x) (lit-val y))
;;   ;;            (lit-equiv x y))
;;   ;;   :rule-classes :forward-chaining)

;;   (defthm equal-of-lit-vals-is-lit-equiv
;;     (equal (equal (lit-val x) (lit-val y))
;;            (lit-equiv x y)))

;;   (defthm to-lit-of-lit-val
;;     (equal (to-lit (lit-val x))
;;            (lit-fix x)))

;;   (in-theory (disable litp to-lit lit-val)))



(local (in-theory (disable litp
                           ;; to-lit
                           ;; lit-val
                           lit-fix)))


(local (in-theory (enable* acl2::ihsext-recursive-redefs
                           acl2::ihsext-bounds-thms)))


(define lit->var ((lit litp))
  :parents (litp)
  :short "Access the @('var') component of a literal."

  (ash (the (integer 0 *) (lit-fix lit))
       -1)

  :inline t
  ;; BOZO type-prescription doesn't make sense unless we strengthen
  ;; the compound-recognizer rule for varp?
  :returns (var varp :rule-classes (:rewrite :type-prescription))

  ///
  (defthmd lit-fix-bound-by-lit->var
    (<= (lit-fix x) (+ 1 (* 2 (lit->var x))))
    :hints(("Goal" :in-theory (enable lit-fix acl2::logcons)
            :use ((:instance bitops::logcons-destruct
                   (x x)))))
    :rule-classes :linear))

(define lit->var^ ((lit litp :type (unsigned-byte 32)))
  :parents (lit->var)
  :short "Same as @(see lit->var), but with a type declaration that the input is 32 bits unsigned."
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable lit->var)))
  (mbe :logic (lit->var lit)
       :exec (the (unsigned-byte 31)
                  (ash (the (unsigned-byte 32) lit) -1))))


(define lit->neg ((lit litp))
  :parents (litp)
  :short "Access the @('neg') bit of a literal."

  (the bit (logand 1 (the (integer 0 *) (lit-fix lit))))

  :inline t
  :returns (neg bitp :rule-classes (:rewrite :type-prescription))

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
    :rule-classes :linear))

(define lit->neg^ ((lit litp :type (unsigned-byte 32)))
  :parents (lit->neg)
  :short "Same as @(see lit->neg), but with a type declaration that the input is 32 bits unsigned."
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable lit->neg)))
  (mbe :logic (lit->neg lit)
       :exec (the bit (logand 1 (the (unsigned-byte 32) lit)))))



;; (acl2::def-b*-decomp lit
;;                      (var . lit->var)
;;                      (neg . lit->neg))


(define make-lit ((var varp :type (integer 0 *)) (neg bitp :type bit))
  :split-types t
  :parents (litp)
  :short "Construct a literal with the given @('var') and @('neg')."

  (the (integer 0 *)
       (logior (the (integer 0 *)
                    (ash (the (integer 0 *) (var-fix var)) 1))
               (the bit (lbfix neg))))

  :inline t
  ;; BOZO type-prescription doesn't make sense unless we strenghten
  ;; the compound-recognizer rule for litp?
  :returns (lit litp :rule-classes (:rewrite :type-prescription))
  :prepwork ((local (in-theory (enable lit->var lit->neg))))
  ///
  (fty::deffixequiv make-lit)

  (defthm lit->var-of-make-lit
    (equal (lit->var (make-lit var neg))
           (var-fix var)))

  (defthm lit->neg-of-make-lit
    (equal (lit->neg (make-lit var neg))
           (bfix neg)))

  (defthm make-lit-identity
    (equal (make-lit (lit->var lit)
                     (lit->neg lit))
           (lit-fix lit))
    :hints(("Goal" :in-theory (disable bitops::logior$))))

  ;; (local (defthm equal-of-make-lit-lemma
  ;;          (implies (and (varp var) (bitp neg))
  ;;                   (equal (equal a (make-lit var neg))
  ;;                          (and (litp a)
  ;;                               (equal (lit->var a) (var-fix var))
  ;;                               (equal (lit->neg a) neg))))
  ;;          :hints(("Goal" :in-theory (disable make-lit
  ;;                                             make-lit-identity
  ;;                                             lit->var lit->neg)
  ;;                  :use ((:instance make-lit-identity (lit a)))))
  ;;          :rule-classes nil))

  (defthmd equal-of-make-lit
    (equal (equal a (make-lit var neg))
           (and (litp a)
                (equal (lit->var a) (var-fix var))
                (equal (lit->neg a) (bfix neg))))))

(define make-lit^ ((var varp :type (unsigned-byte 31)) (neg bitp :type bit))
  :split-types t
  :guard (unsigned-byte-p 31 var)
  :parents (make-lit)
  :short "Same as @(see make-lit), but with a type declaration that the input variable is 31 bits unsigned."
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable make-lit)))
  (mbe :logic (make-lit var neg)
       :exec (the (unsigned-byte 32)
                  (logior (the (unsigned-byte 32)
                               (ash (the (unsigned-byte 31) var) 1))
                          (the bit neg)))))

(defthm equal-of-lit->var-equal-hyp
  (implies (and (syntaxp (acl2::rewriting-negative-literal-fn
                          `(equal (lit->var$inline ,x) (lit->var$inline ,y))
                          mfc state))
                (equal (lit->neg x) (lit->neg y)))
           (equal (equal (lit->var x) (lit->var y))
                  (equal (lit-fix x) (lit-fix y))))
  :hints (("goal" :use ((:instance lit->var$inline-of-lit-fix-lit
                         (lit y))
                        (:instance lit->var$inline-of-lit-fix-lit
                         (lit x))
                        (:instance make-lit-identity
                         (lit y))
                        (:instance make-lit-identity
                         (lit x)))
           :in-theory (e/d () (lit->var$inline-of-lit-fix-lit
                               lit->var$inline-lit-equiv-congruence-on-lit
                               make-lit-identity)))))

(defthm equal-of-lit-fix-forward1
  (implies (equal (lit-fix x) y)
           (lit-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-of-lit-fix-forward2
  (implies (equal y (lit-fix x))
           (lit-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-of-lit-fix-forward-both
  (implies (equal (lit-fix x) (lit-fix y))
           (lit-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-of-lit-fix-backchain
  (implies (and (syntaxp (not (or (acl2::rewriting-negative-literal-fn
                                   `(equal (lit-fix$inline ,x) ,y)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,y (lit-fix$inline ,x))
                                   mfc state))))
                (litp y)
                (equal (lit->var x) (lit->var y))
                (equal (lit->neg x) (lit->neg y)))
           (equal (equal (lit-fix x) y) t)))

(defthm equal-of-lit->var-implies-lit-equiv
  (implies (and (equal (lit->var x) (lit->var y))
                (equal (lit->neg x) (lit->neg y)))
           (lit-equiv x y))
  :rule-classes :forward-chaining)


(local (in-theory (e/d (bitops::logxor**)
                       (bitops::logior$ bitops::logxor$))))


(define lit-negate ((lit litp :type (integer 0 *)))
  :split-types t
  :parents (litp)
  :short "Efficiently negate a literal."
  :inline t
  :returns (new-lit litp)
  (mbe :logic (b* ((var (lit->var lit))
                   (neg (lit->neg lit)))
                (make-lit var (b-not neg)))
       :exec (the (integer 0 *)
                  (logxor (the (integer 0 *) lit)
                          1)))

  :guard-hints(("Goal" :in-theory (enable make-lit lit->var lit->neg)))
  ///
  (defret lit->var-of-lit-negate
    (equal (lit->var new-lit) (lit->var lit)))

  (defret lit->neg-of-lit-negate
    (equal (lit->neg new-lit) (b-not (lit->neg lit))))

  (defthm lit-negate-of-make-lit
    (equal (lit-negate (make-lit var neg))
           (make-lit var (b-not neg))))

  (defthm lit-negate-of-lit-negate
    (equal (lit-negate (lit-negate x))
           (lit-fix x))
    :hints(("Goal" :in-theory (disable b-not))))

  (defthm b-not-not-equal
    (not (equal (b-not x) x))
    :hints(("Goal" :in-theory (enable b-not))))

  (defthm lit-negate-not-equal-when-vars-mismatch
    (implies (not (equal (lit->var x) (lit->var y)))
             (not (equal (lit-negate x) y))))

  (defthm lit-negate-not-equal-when-neg-matches
    (implies (equal (lit->neg x) (lit->neg y))
             (not (equal (lit-negate x) y))))

  ;; (defthm equal-of-lit-negate-hyp
  ;;   (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
  ;;                          `(equal (lit-negate$inline ,x) ,y) mfc state)
  ;;                         (acl2::rewriting-negative-literal-fn
  ;;                          `(equal ,y (lit-negate$inline ,x)) mfc state)))
  ;;            (equal (equal (lit-negate x) y)
  ;;                   (and (litp y)
  ;;                        (equal (lit->var x) (lit->var y))
  ;;                        (equal (lit->neg x) (b-not (lit->neg y))))))
  ;;   :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  (defthm equal-of-lit-negate-backchain
    (implies (and (syntaxp (not (or (acl2::rewriting-negative-literal-fn
                                   `(equal (lit-negate$inline ,x) ,y)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,y (lit-negate$inline ,x))
                                   mfc state))))
                  (litp y)
                  (equal (lit->var x) (lit->var y))
                  (equal (lit->neg x) (b-not (lit->neg y))))
             (equal (equal (lit-negate x) y) t))
    :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  (local (defthm not-equal-of-bits
           (implies (and (syntaxp (acl2::rewriting-positive-literal-fn
                                   `(equal ,x ,y) mfc state))
                         (bitp x) (bitp y))
                    (equal (equal x y)
                           (not (equal x (b-not y)))))
           :hints(("Goal" :in-theory (enable bitp)))))

  (defthm equal-of-lit->var-negated-hyp
    (implies (and (syntaxp (acl2::rewriting-negative-literal-fn
                            `(equal (lit->var$inline ,x) (lit->var$inline ,y))
                            mfc state))
                  (not (equal (lit->neg x) (lit->neg y))))
             (equal (equal (lit->var x) (lit->var y))
                    (equal (lit-fix x) (lit-negate y))))
    :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  (defthm equal-of-lit-negate-component-rewrites
    (implies (equal (lit-negate x) (lit-fix y))
             (and (equal (lit->var y) (lit->var x))
                  (equal (lit->neg y) (b-not (lit->neg x)))))
    :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  ;; BOZO move to bitops or something
  (defthm equal-of-b-not-cancel
    (equal (equal (b-not x) (b-not y))
           (bit-equiv x y))
    :hints(("Goal" :in-theory (enable b-not))))

  (defthm equal-of-lit-negate-cancel
    (equal (equal (lit-negate x) (lit-negate y))
           (equal (lit-fix x) (lit-fix y)))
    :hints(("Goal" :in-theory (enable equal-of-make-lit)))))

(define lit-negate^ ((lit litp :type (unsigned-byte 32)))
  :parents (lit-negate)
  :short "Same as @(see lit-negate), but with a type declaration that the input is 32 bits unsigned."
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable lit-negate make-lit lit->var lit->neg)))
  (mbe :logic (lit-negate lit)
       :exec (the (unsigned-byte 32)
                  (logxor 1 (the (unsigned-byte 32) lit)))))





(define lit-negate-cond ((lit litp :type (integer 0 *)) (c bitp :type bit))
  :split-types t
  :parents (litp)
  :short "Efficiently negate a literal."
  :long "<p>When @('c') is 1, we negate @('lit').  Otherwise, when @('c') is 0,
we return @('lit') unchanged.</p>"
  :inline t
  :returns (new-lit litp)
  (mbe :logic (b* ((var (lit->var lit))
                   (neg (b-xor (lit->neg lit) c)))
                (make-lit var neg))
       :exec (the (integer 0 *)
                  (logxor (the (integer 0 *) lit)
                          (the bit c))))

  :guard-hints(("Goal" :in-theory (enable make-lit lit->var lit->neg)))

  ///

  (defret lit->var-of-lit-negate-cond
    (equal (lit->var new-lit) (lit->var lit)))

  (defret lit->neg-of-lit-negate-cond
    (equal (lit->neg new-lit) (b-xor c (lit->neg lit))))

  (defthm lit-negate-cond-of-make-lit
    (equal (lit-negate-cond (make-lit var neg) c)
           (make-lit var (b-xor c neg))))

  (defthm lit-negate-cond-not-equal-when-vars-mismatch
    (implies (not (equal (lit->var x) (lit->var y)))
             (not (equal (lit-negate-cond x c) y))))

  (local (defthm b-xor-b-xor
           (equal (b-xor c (b-xor c x)) (bfix x))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (defthm lit-negate-cond-not-equal-when-neg-mismatches
    (implies (not (equal (lit->neg x) (b-xor c (lit->neg y))))
             (not (equal (lit-negate-cond x c) y))))

  ;; (defthm equal-of-lit-negate-cond-hyp
  ;;   (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
  ;;                          `(equal (lit-negate-cond$inline ,x ,c) ,y) mfc state)
  ;;                         (acl2::rewriting-negative-literal-fn
  ;;                          `(equal ,y (lit-negate-cond$inline ,x ,c)) mfc state)))
  ;;            (equal (equal (lit-negate-cond x c) y)
  ;;                   (and (litp y)
  ;;                        (equal (lit->var x) (lit->var y))
  ;;                        (equal (lit->neg x) (b-xor c (lit->neg y))))))
  ;;   :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  (defthm equal-of-lit-negate-cond-component-rewrites
    (implies (equal (lit-negate-cond x c) (lit-fix y))
             (and (equal (lit->var y) (lit->var x))
                  (equal (lit->neg y) (b-xor c (lit->neg x)))))
    :hints(("Goal" :in-theory (enable equal-of-make-lit))))

  (defthm equal-of-lit-negate-cond-backchain
    (implies (and (syntaxp (not (or (acl2::rewriting-negative-literal-fn
                                     `(equal (lit-negate-cond$inline ,x ,c) ,y)
                                     mfc state)
                                    (acl2::rewriting-negative-literal-fn
                                     `(equal ,y (lit-negate-cond$inline ,x ,c))
                                     mfc state))))
                  (litp y)
                  (equal (lit->var x) (lit->var y))
                  (equal (lit->neg x) (b-xor c (lit->neg y))))
             (equal (equal (lit-negate-cond x c) y) t))
    :hints(("Goal" :in-theory (enable equal-of-make-lit)))))

(define lit-negate-cond^ ((lit litp :type (unsigned-byte 32))
                          (neg bitp :type bit))
  :split-types t
  :guard (unsigned-byte-p 32 lit)
  :parents (lit-negate-cond)
  :short "Same as @(see lit-negate-cond), but with a type declaration that the input literal is 32 bits unsigned."
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable lit-negate-cond make-lit lit->var lit->neg)))
  (mbe :logic (lit-negate-cond lit neg)
       :exec (the (unsigned-byte 32)
                  (logxor neg (the (unsigned-byte 32) lit)))))


(define lit-abs ((lit litp :type (integer 0 *)))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable make-lit lit->var)))
  (mbe :logic (make-lit (lit->var lit) 0)
       :exec (logand -2 (the (integer 0 *) lit))))


(define lit-abs^ ((lit litp :type (unsigned-byte 32)))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable make-lit lit->var)))
  (mbe :logic (lit-abs lit)
       :exec (logand -2 (the (unsigned-byte 32) lit))))







(fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
  :parents (litp)
  :short "List of literals")

(fty::deflist lit-list-list :pred lit-list-listp :elt-type lit-list :true-listp t
  :parents (litp)
  :short "List of @(see lit-list)s")


