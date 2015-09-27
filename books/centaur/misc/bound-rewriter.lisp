


(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :System)
(include-book "clause-processors/unify-subst" :dir :System)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)
(include-book "std/util/defaggrify-defrec" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


;; Linearly traverse an arithmetic comparison term and replace positive
;; occurrences with lower bounds and negative occurrences with upper bounds.

;; Terminology: If we are trying to prove the inequality
;; (< A B) or (<= A B),
;; then we can soundly [not necessarily completely] replace A by its upper
;; bound and/or B by its lower bound.  We say A is a negative occurrence and B
;; is a positive occcurrence.  If this inequality occurs in a hyp, then the
;; roles of A and B are switched.

;; Arithmetic operators +, *, -, / have simple rules:

;; If (+ A B) occurs positively then A and B are both positive occurrences, and
;; similarly for negative.
;; If (- A) occurs positively then this A is a negative occurrence, and vice versa.
;; If (* A B) occurs positively, then:
;;   - if A is known nonnegative, then B is a positive occurrence
;;   - if A is known nonpositive, then B is a negative occurrence
;; and symmetrically for B and for negative occurrences.
;; If (/ A) occurs positively, then A is a negative occurrence, and vice versa.



(defevaluator-fast boundrw-ev boundrw-ev-lst
  ;; required for meta-extract:
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   
   (cons a b) ;; required for unify

   ;; required for sublis-var
   (acl2-numberp x)
   (binary-* x y)
   (binary-+ x y)
   (unary-- x)
   (unary-/ x)
   (< x y)
   (car x)
   (cdr x)
   (char-code x)
   (characterp x)
   (code-char x)
   (complex x y)
   (complex-rationalp x)
   (coerce x y)
   (cons x y)
   (consp x)
   (denominator x)
   (equal x y)
   (imagpart x)
   (integerp x)
   (intern-in-package-of-symbol x y)
   (numerator x)
   (rationalp x)
   (realpart x)
   (stringp x)
   (symbol-name x)
   (symbol-package-name x)
   (symbolp x)
   (if x y z)
   (not x)

   (< a b)
   (binary-+ a b)
   (unary-- a)
   (binary-* a b)
   (unary-/ a)

   (hide a))
  :namedp t)

(def-meta-extract boundrw-ev boundrw-ev-lst)
(def-unify boundrw-ev boundrw-ev-alist)

(defthm boundrw-ev-of-sublis-var
  (implies (and (pseudo-termp x)
                (not (assoc nil alist)))
           (equal (boundrw-ev (sublis-var alist x) a)
                  (boundrw-ev x (append (boundrw-ev-alist alist a) a))))
  :hints (("goal" :use ((:functional-instance eval-of-sublis-var
                         (cterm-ev boundrw-ev)
                         (cterm-ev-lst boundrw-ev-lst)
                         (cterm-ev-alist boundrw-ev-alist))))
          (and stable-under-simplificationp
               '(:in-theory (enable boundrw-ev-of-fncall-args)))))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

;; defined everywhere
(local (defthm assoc-nonnil-of-append
         (implies x
                  (equal (assoc x (append a b))
                         (or (assoc x a) (assoc x b))))))

(defthm-simple-term-vars-flag
  (defthm boundrw-ev-of-append-substs
    (implies (and (all-keys-bound (simple-term-vars x) a)
                  (pseudo-termp x))
             (equal (boundrw-ev x (append a b))
                    (boundrw-ev x a)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((simple-term-vars x))))
            (and stable-under-simplificationp
                 '(:expand ((pseudo-termp x))
                   :in-theory (enable boundrw-ev-of-fncall-args))))
    :flag simple-term-vars)
  (defthm boundrw-ev-lst-of-append-substs
    (implies (and (all-keys-bound (simple-term-vars-lst x) a)
                  (pseudo-term-listp x))
             (equal (boundrw-ev-lst x (append a b))
                    (boundrw-ev-lst x a)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((simple-term-vars-lst x)))))
    :flag simple-term-vars-lst))

  


(local (in-theory (disable sublis-var)))

(std::defalist pseudo-term-map-p (x)
  :key (pseudo-termp x) :val (pseudo-termp x)
  :keyp-of-nil t :valp-of-nil t)

(set-state-ok t)

;; Check whether a term's sign is known.  Returns :nonnegative, :nonpositive, or nil.
(define ts-check-sign ((x pseudo-termp)
                       mfc state)

  :returns (category symbolp)
  (b* ((ts (mfc-ts x mfc state :forcep nil))
       ((unless (integerp ts)) nil))
    (cond ((eql 0 (logand (lognot (logior *ts-positive-integer*
                                          *ts-positive-ratio*
                                          *ts-zero*))
                          ts))
           ;; Its typeset can't be anything other than a positive integer,
           ;; positive rational, or zero.  So it's nonnegative.
           :nonnegative)
          ((eql 0 (logand (lognot (logior *ts-negative-integer*
                                          *ts-negative-ratio*
                                          *ts-zero*))
                          ts))
           :nonpositive)
          (t nil)))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))
  
  (defret ts-check-sign-nonnegative-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonnegative)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= 0 val)
                    (equal (< 0 val)
                           (not (equal val 0))))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))

  (defret ts-check-sign-nonpositive-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonpositive)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= val 0)
                    (equal (< val 0)
                           (not (equal val 0))))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))

  (defthm ts-check-sign-nonnil-casesplit
    (implies (rewriting-negative-literal `(ts-check-sign ,x ,m ,s))
             (let ((category (ts-check-sign x m s)))
               (iff category
                    (or (equal category :nonpositive)
                        (equal category :nonnegative)))))))


(define ts-check-sign-strict ((x pseudo-termp)
                              mfc state)

  :returns (category symbolp)
  (b* ((ts (mfc-ts x mfc state :forcep nil))
       ((unless (integerp ts)) nil))
    (cond ((eql 0 (logand (lognot (logior *ts-positive-integer*
                                          *ts-positive-ratio*))
                          ts))
           ;; Its typeset can't be anything other than a positive integer,
           ;; positive rational, or zero.  So it's nonnegative.
           :positive)
          ((eql 0 (logand (lognot (logior *ts-negative-integer*
                                          *ts-negative-ratio*))
                          ts))
           :negative)
          (t nil)))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))
  
  (defret ts-check-sign-strict-positive-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :positive)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (< 0 val))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))

  (defret ts-check-sign-strict-negative-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :negative)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (< val 0))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))


  (defthm ts-check-sign-strict-nonnil-casesplit
    (implies (rewriting-negative-literal `(ts-check-sign-strict ,x ,m ,s))
             (let ((category (ts-check-sign-strict x m s)))
               (iff category
                    (or (equal category :positive)
                        (equal category :negative)))))))


(define ts-check-nonzero ((x pseudo-termp)
                       mfc state)

  :returns (nonzerop)
  (b* ((ts (mfc-ts x mfc state :forcep nil)))
    (and (integerp ts)
         (eql 0 (logand (logior *ts-zero*
                                (lognot (logior *ts-positive-integer*
                                                *ts-positive-ratio*
                                                *ts-negative-integer*
                                                *ts-negative-ratio*)))
                        ts))))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))
  
  (defret ts-check-sign-nonzero-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and nonzerop
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (not (equal 0 val)))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning))))

(define ts-check-rational ((x pseudo-termp)
                       mfc state)

  :returns (rationalp)
  (b* ((ts (mfc-ts x mfc state :forcep nil)))
    (and (integerp ts)
         (eql 0 (logand (lognot (logior *ts-positive-integer*
                                        *ts-positive-ratio*
                                        *ts-negative-integer*
                                        *ts-negative-ratio*
                                        *ts-zero*))
                        ts))))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))
  
  (defret ts-check-sign-rational-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and rationalp
                    (boundrw-ev-meta-extract-contextual-facts a))
               (rationalp val)))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning))))




(local
 (defthmd mult-both-sides-preserves-<=
   (implies (and ;; (rationalp x)
                 ;; (rationalp y)
                 (rationalp c)
                 (<= x y)
                 (<= 0 c))
            (<= (* c x) (* c y)))
   :hints (("goal" :nonlinearp t))))

(local
 (defthmd mult-both-sides-preserves-<
   (implies (and ;; (rationalp x)
                 ;; (rationalp y)
                 (rationalp c)
                 (< x y)
                 (< 0 c))
            (< (* c x) (* c y)))
   :hints (("goal" :nonlinearp t))))

(defthm assoc-in-boundrw-ev-alist
  (implies k
           (equal (assoc k (boundrw-ev-alist x a))
                  (and (assoc k x)
                       (cons k (boundrw-ev (cdr (assoc k x)) a))))))

(defthm all-keys-bound-in-boundrw-ev-alist
  (implies (not (member nil keys))
           (equal (all-keys-bound keys (boundrw-ev-alist x a))
                  (all-keys-bound keys x)))
  :hints(("Goal" :in-theory (enable all-keys-bound))))

(defthm all-keys-bound-when-subsetp
  (implies (and (subsetp x y)
                (all-keys-bound y z))
           (all-keys-bound x z))
  :hints(("Goal" :in-theory (enable subsetp all-keys-bound))))


(defthmd boundrw-dummy-rewrite
  (implies (= a b)
           (equal (< a b) nil)))

(define boundrw-apply-bound ((x pseudo-termp)
                             (direction booleanp)
                             (bound-alist pseudo-term-map-p)
                             mfc state)
  :returns (new-x pseudo-termp :hyp (and (pseudo-termp x)
                                         (pseudo-term-map-p bound-alist)))
  (b* (((when (atom bound-alist)) x)
       ((unless (mbt (consp (car bound-alist))))
        (boundrw-apply-bound x direction (cdr bound-alist) mfc state))
       ((cons lhs rhs) (car bound-alist))
       ((mv unify-ok subst) (simple-one-way-unify lhs x nil))
       (vars-ok (and unify-ok (subsetp-eq (simple-term-vars rhs) (simple-term-vars lhs))))
       ((unless vars-ok)
        (boundrw-apply-bound x direction (cdr bound-alist) mfc state))
       ;; Check that the substitution is ok using relieve-hyp.
       (bound-ok
        (mfc-relieve-hyp
         (if direction
             ;; rhs is upper bound
             `(not (< ,rhs ,lhs))
           ;; rhs is lower bound
           `(not (< ,lhs ,rhs)))
         subst '(:rewrite boundrw-dummy-rewrite) '(< fake term) 1 mfc state
         :forcep nil))
       ((when bound-ok)
        (cw "~x0: relieve-hyp~%" x)
        (substitute-into-term rhs subst))
       (new-x (substitute-into-term rhs subst))
       (bound-ok (mfc-ap
                  ;; term to contradict:
                  (if direction
                      ;; new-x is upper bound
                      `(< ,new-x ,x)
                    ;; new-x is lower bound
                    `(< ,x ,new-x))
                  mfc state
                  :forcep nil))
       ((when bound-ok)
        (cw "~x0: ap~%" x)
        new-x))
    (boundrw-apply-bound x direction (cdr bound-alist) mfc state))
  ///
  (defret boundrw-apply-bound-correct
    (implies (and (boundrw-ev-meta-extract-contextual-facts a)
                  (pseudo-termp x)
                  (pseudo-term-map-p bound-alist))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev new-x a)))
                  (implies (not direction)
                           (<= (boundrw-ev new-x a) (boundrw-ev x a)))))))
  

(define boundrw-rewrite ((x pseudo-termp)
                         (direction booleanp)
                         (bound-alist pseudo-term-map-p)
                         (negative-bound-alist pseudo-term-map-p)
                         &key (mfc 'mfc) (state 'state))
  :irrelevant-formals-ok t
  :verify-guards nil
  :returns (new-x pseudo-termp
                  :hyp (and (pseudo-termp x)
                            (pseudo-term-map-p bound-alist)
                            (pseudo-term-map-p negative-bound-alist)))
  (cond ((atom x) (boundrw-apply-bound x direction bound-alist mfc state))
        ((quotep x) x)
        (t
         (case-match x
           (('binary-+ a b) (list 'binary-+
                                  (boundrw-rewrite a direction bound-alist negative-bound-alist)
                                  (boundrw-rewrite b direction bound-alist negative-bound-alist)))

           (('unary-- a) (list 'unary--
                               (boundrw-rewrite a (not direction) negative-bound-alist bound-alist)))
           (('unary-/ a)
            (b* ((a-sign (ts-check-sign-strict a mfc state))
                 ((unless a-sign) x)
                 (b (boundrw-rewrite a (not direction) negative-bound-alist bound-alist))
                 ((when (or (and (eq a-sign :positive) (not direction))
                            (and (eq a-sign :negative) direction)))
                  ;; a is positive and b is greater or equal, or a is negative
                  ;; and b is less or equal, just by correctness of this
                  ;; function.
                  (if (ts-check-rational b mfc state)
                      `(unary-/ ,b)
                    x))
                 (b-sign (ts-check-sign-strict b mfc state)))
              (if (eq a-sign b-sign)
                  `(unary-/ ,b)
                x)))

           (('binary-* a b)
            ;; First rewrite a based on b's type, then rewrite b based on a's
            ;; type, then if necessary, go back and look at a again.
            (b* (((unless (and (ts-check-rational a mfc state)
                               (ts-check-rational b mfc state)))
                  x)
                 (b-type (ts-check-sign b mfc state))
                 (new-a (if b-type
                            (b* (((mv a-dir a-bound-alist a-negative-bound-alist)
                                  (if (eq b-type :nonnegative)
                                      (mv direction bound-alist negative-bound-alist)
                                    (mv (not direction) negative-bound-alist bound-alist)))
                                 (res
                                  (boundrw-rewrite a a-dir a-bound-alist a-negative-bound-alist)))
                              (if (ts-check-rational res mfc state)
                                  res
                                a))
                          a))
                 (a-type (ts-check-sign new-a mfc state))
                 (new-b (if a-type
                            (b* (((mv b-dir b-bound-alist b-negative-bound-alist)
                                  (if (eq a-type :nonnegative)
                                      (mv direction bound-alist negative-bound-alist)
                                    (mv (not direction) negative-bound-alist bound-alist)))
                                 (res (boundrw-rewrite b b-dir b-bound-alist b-negative-bound-alist)))
                              (if (ts-check-rational res mfc state)
                                  res
                                b))
                          b))
                 ((when (or b-type (not a-type)))
                  `(binary-* ,new-a ,new-b))
                 (b-type (ts-check-sign new-b mfc state))
                 (new-a (if b-type
                            (b* (((mv a-dir a-bound-alist a-negative-bound-alist)
                                  (if (eq b-type :nonnegative)
                                      (mv direction bound-alist negative-bound-alist)
                                    (mv (not direction) negative-bound-alist bound-alist)))
                                 (res
                                  (boundrw-rewrite a a-dir a-bound-alist a-negative-bound-alist)))
                              (if (ts-check-rational res mfc state)
                                  res
                                a))
                          a)))
              `(binary-* ,new-a ,new-b)))

           (& (boundrw-apply-bound x direction bound-alist mfc state)))))
  ///
  (verify-guards+ boundrw-rewrite)

  (local (defthm reciprocal-antimonotonic-pos
           (implies (and (case-split (< 0 a))
                         (<= a b)
                         (rationalp a)
                         (rationalp b))
                    (<= (/ b) (/ a)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))


  
  (local (defthm reciprocal-antimonotonic-neg
           (implies (and (case-split (< b 0))
                         (<= a b)
                         (rationalp a)
                         (rationalp b))
                    (<= (/ b) (/ a)))
           :hints (("goal" :use ((:instance mult-both-sides-preserves-<
                                  (x (/ a)) (y (/ b))
                                  (c (* a b)))))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))


  (local (defthm mult-monotonic-pos
         (implies (and (rationalp a)
                       (<= 0 a)
                       (<= b c))
                  (<= (* a b) (* a c)))
         :hints (("goal" :nonlinearp t))))

  (local (defthm mult-monotonic-neg
           (implies (and (rationalp a)
                         (<= a 0)
                         (<= b c))
                    (<= (* a c) (* a b)))
           :hints (("goal" :nonlinearp t))))

  ;; Each of these covers a case where we replace a with c, then b with d.
  (local (defthm mult-monotonic-pos-pos-upper
           (implies (and (<= 0 b)
                         (<= a c)
                         (<= 0 c)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-pos-pos-lower
           (implies (and (<= 0 b)
                         (<= c a)
                         (<= 0 c)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-pos-neg-upper
           (implies (and (<= 0 b)
                         (<= a c)
                         (<= c 0)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-pos-neg-lower
           (implies (and (<= 0 b)
                         (<= c a)
                         (<= c 0)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-neg-pos-upper
           (implies (and (<= b 0)
                         (<= c a)
                         (<= 0 c)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-neg-pos-lower
           (implies (and (<= b 0)
                         (<= a c)
                         (<= 0 c)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-neg-neg-upper
           (implies (and (<= b 0)
                         (<= c a)
                         (<= c 0)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-neg-neg-lower
           (implies (and (<= b 0)
                         (<= a c)
                         (<= c 0)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defret boundrw-rewrite-correct
    (b* ((old (boundrw-ev x a))
         (new (boundrw-ev new-x a)))
      (implies (and (pseudo-termp x)
                    (pseudo-term-map-p bound-alist)
                    (pseudo-term-map-p negative-bound-alist)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (implies direction
                             (<= old new))
                    (implies (not direction)
                             (<= new old)))))
    :hints (("goal" :induct t
             :in-theory (disable COMMUTATIVITY-OF-*)))
    :rule-classes (:rewrite :linear)))


(local (defthm boundrw-ev-of-hide
         (equal (boundrw-ev `(hide ,x) a)
                (boundrw-ev x a))
         :hints (("goal" :expand ((:free (x) (hide x)))))))

(std::defaggrify-defrec rewrite-constant)
(std::defaggrify-defrec metafunction-context)

(local (in-theory (disable metafunction-context->ancestors
                           metafunction-context->rcnst
                           rewrite-constant->current-literal
                           weak-metafunction-context-p
                           weak-rewrite-constant-p)))

(define bound-rewrite-metafn ((x pseudo-termp) mfc state)
  :returns (new-x)
  (b* (((unless (and (consp x) (eq (car x) '<)))
        (cw "Bound-rewrite: applied to wrong term: ~x0~%" x)
        x)
       ((unless (and (weak-metafunction-context-p mfc)
                     (weak-rewrite-constant-p
                      (metafunction-context->rcnst mfc))))
        (cw "Bound-rewrite: malformed mfc/rnst?~%")
        x)
       ((when (metafunction-context->ancestors mfc)) ;; don't use this for backchaining
        ;; this is supposed to happen so don't print a warning
        x)
       (curr-lit (rewrite-constant->current-literal
                  (metafunction-context->rcnst mfc)))
       ((unless (and (consp curr-lit)
                     (equal (cdr curr-lit) x)))
        ;; this is supposed to happen so don't print a warning
        x)
       (hyp-p (car curr-lit))
       ;; OK, now we've established that we're rewriting a clause literal and
       ;; if hyp-p, it's negated, otherwise not.

       ;; (< a b) can be replaced in a clause by
       ;; (or (hide (< a b))
       ;;     (< au bl))
       ;; where au is an upper bound for a, bl is a lower bound for b.
       ;; This equals (< a b) because (< au bl) implies (< a b).

       ;; (not (< a b)) can be replaced in a clause by
       ;; (not (and (hide (< a b))
       ;;           (< al bu)))
       ;; This is equal because (< a b) implies (< al bu).
       ((unless (and (boundp-global 'boundrw-upper-bounds state)
                     (boundp-global 'boundrw-lower-bounds state)))
        (cw "Bound-rewrite: Bounds lists don't exist~%")
        x)
       (upper-bounds (@ boundrw-upper-bounds))
       (lower-bounds (@ boundrw-lower-bounds))
       ((unless (or (consp upper-bounds) (consp lower-bounds)))
        (cw "Bound-rewrite: Bounds lists are empty~%")
        x)
       ((unless (and (pseudo-term-map-p upper-bounds)
                     (pseudo-term-map-p lower-bounds)))
        (cw "Bound-rewrite: Bounds lists are not both pseudo-term-map-ps.~%")
        x)
       
       ((list a b) (cdr x))
       (new-a (if hyp-p
                  ;; (not (< a b)) case -- replace a by lower bound
                  (boundrw-rewrite a nil lower-bounds upper-bounds)
                ;; (< a b) case -- replace a by upper bound
                (boundrw-rewrite a t upper-bounds lower-bounds)))
       (new-b (if hyp-p
                  ;; (not (< a b)) case -- replace b by upper bound
                  (boundrw-rewrite b t upper-bounds lower-bounds)
                ;; (< a b) case -- replace b by lower bound
                (boundrw-rewrite b nil lower-bounds upper-bounds)))

       ((when (and (equal new-a a) (equal new-b b)))
        ;; failed to do any replacement, stick with current term
        x))
    (if hyp-p
        ;; (not (< a b)) -- use AND
        `(if (hide ,x)
             (< ,new-a ,new-b)
           'nil)
      ;; (< a b) -- use OR
      `(if (hide ,x)
           (hide ,x)
         (< ,new-a ,new-b))))
  ///
  (defthmd bound-rewrite
    (implies (and (pseudo-termp x)
                  (alistp a)
                  (boundrw-ev-meta-extract-contextual-facts a))
             (equal (boundrw-ev x a)
                    (boundrw-ev (bound-rewrite-metafn x mfc state) a)))
    :rule-classes ((:meta :trigger-fns (<)))))
             

(define boundrw-translate-substs
  ((substs "A list of inequalities, each either the form @('(<= lhs rhs)'), @('(<
            lhs rhs)'), @('(>= lhs rhs)'), or @('(> lhs rhs)'). These are used
            as substitution rules for contexts in which @('lhs') may be replaced
            by its upper or lower bound.")
   state)
  :mode :program
  :returns (mv (upper-bounds)
               (lower-bounds))
  (b* (((when (atom substs)) (mv nil nil))
       ((mv rest-upper rest-lower)
        (boundrw-translate-substs (cdr substs) state))
       (subst (car substs)))
    (case-match subst
      ((cmp lhs rhs)
       (b* (((unless (member cmp '(< <= > >=)))
             (raise "Boundrw-hint: Malformed comparison in substitutions: ~x0~%" subst)
             (mv nil nil))
            ((mv errp lhs) (translate-cmp lhs t nil nil 'boundrw-hint (w state)
                                          (default-state-vars t)))
            ((when errp) (er hard? errp "~@0~%" lhs) (mv nil nil))
            ((mv errp rhs) (translate-cmp rhs t nil nil 'boundrw-hint (w state)
                                          (default-state-vars t)))
            ((when errp) (er hard? errp "~@0~%" rhs) (mv nil nil)))
         (if (member cmp '(< <=))
             (mv (cons (cons lhs rhs) rest-upper) rest-lower)
           (mv rest-upper (cons (cons lhs rhs) rest-lower)))))
      (& (prog2$ (raise "Boundrw-hint: Malformed comparison in substitutions: ~x0~%" subst)
                 (mv nil nil))))))
       

       
(define try-bound-rw-fn (substs
                         in-theory
                         wait-til-stablep
                         stablep
                         state)
  :mode :program
  (b* (((unless (or (not wait-til-stablep) stablep))
        (value nil))
       ((mv upper-bounds lower-bounds) (boundrw-translate-substs substs state))
       (state (f-put-global 'boundrw-upper-bounds upper-bounds state))
       (state (f-put-global 'boundrw-lower-bounds lower-bounds state)))
    (value `(:in-theory (cons 'bound-rewrite ,in-theory)))))

(defmacro try-bound-rw (substs
                        &key
                        (in-theory '(enable))
                        (wait-til-stablep 't)
                        (stablep 'stable-under-simplificationp)
                        (state 'state))
  `(try-bound-rw-fn ',substs ',in-theory ,wait-til-stablep ,stablep ,state))


(local
 (progn
   (defstub a () nil)
   (defstub b () nil)
   (defstub c () nil)
   (defstub d () nil)

   (in-theory (disable <-*-left-cancel
                       <-*-right-cancel
                       commutativity-of-*
                       (tau-system)))

   (defthm mult-monotonic-neg-pos-lower-foo
     (implies (and (<= (b) 0)
                   (<= (a) (c))
                   (<= 0   (c))
                   (<= (d) (b))
                   (rationalp (a))
                   (rationalp (b))
                   (rationalp (c))
                   (rationalp (d)))
              (<= (* (c) (d)) (* (a) (b))))
     :hints ((try-bound-rw '((<= (a) (c))
                            (<= (d) (b))))))))




#||

dead code
(define boundrw-alist-okp ((alist pseudo-term-map-p)
                           (direction booleanp)
                           a)
  ;; Each key of alist is a term and each value is that term's bound.
  ;; If direction is T, then they are upper bounds, and if NIL, lower bounds.
  :returns (ok)
  (b* (((when (atom alist)) t)
       ((unless (mbt (consp (car alist))))
        (boundrw-alist-okp (cdr alist) direction a))
       ((cons key val) (car alist))
       (kv (boundrw-ev key a))
       (vv (boundrw-ev val a)))
    (and (rationalp kv)
         (rationalp vv)
         (if direction
             (<= kv vv)
           (<= vv kv))
         (boundrw-alist-okp (cdr alist) direction a)))
  ///
  (defret boundrw-alist-ok-correct
    (implies (and ok
                  (hons-assoc-equal x alist))
             (let ((bound (cdr (hons-assoc-equal x alist))))
               (and (rationalp (boundrw-ev bound a))
                    (implies direction
                             (not (< (boundrw-ev bound a)
                                     (boundrw-ev x a))))
                    (implies (not direction)
                             (not (< (boundrw-ev x a)
                                     (boundrw-ev bound a))))))))

  (defcong iff equal (boundrw-alist-okp alist direction a) 2))

||#
