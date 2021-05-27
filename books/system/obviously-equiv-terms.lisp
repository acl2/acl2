

(in-package "ACL2")

(include-book "tools/flag" :dir :System)
(include-book "std/util/defines" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :Dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(local (in-theory (disable subcor-var-is-sublis-var1
                           subcor-var-lst-is-sublis-var1-lst
                           subcor-var1-in-terms-of-cdr-assoc)))

(defines term-depth
  :flag-local nil
  (define term-depth ((x pseudo-termp))
    :returns (count posp :rule-classes :type-prescription)
    (cond ((variablep x) 1)
          ((fquotep x) 1)
          (t (b* ((fn (ffn-symb x)))
               (+ 1
                  (max (term-list-depth (fargs x))
                       (if (consp fn)
                           (term-depth (lambda-body fn))
                         0)))))))
  (define term-list-depth ((x pseudo-term-listp))
    :returns (count posp :rule-classes :type-prescription)
    (if (Atom x)
        1
      (max (term-depth (car x))
           (term-list-depth (cdr x)))))
  ///
  (defthm term-depth-of-cons-term
    (<= (term-depth (cons-term fn args))
        (term-depth (cons fn args)))
    :hints (("Goal" :Expand ((:free (fn args) (term-depth (cons fn args))))
             :in-theory (enable cons-term)))
    :rule-classes :linear)

  (defthm term-depth-of-subcor-var1-of-var
    (implies (and (symbol-listp terms)
                  (atom x))
             (equal (term-depth (subcor-var1 vars terms x))
                    1))
    :hints(("Goal" :in-theory (enable subcor-var1)
            :induct t
            :expand ((term-depth x)
                     (term-depth (Car terms))))))

  (defthm-term-depth-flag
    (defthm term-depth-of-subcor-var
      (implies (symbol-listp terms)
               (<= (term-depth (subcor-var vars terms x))
                   (term-depth x)))
      :flag term-depth
      :hints ('(:expand ((term-depth x)
                         (:free (args) (term-depth (cons (car x) args)))))
              (and stable-under-simplificationp
                   '(:use ((:instance term-depth-of-cons-term
                            (fn (car x))
                            (args (subcor-var-lst vars terms (fargs x)))))
                     :in-theory (disable term-depth-of-cons-term))))
      :rule-classes :linear)
    (defthm term-list-depth-of-subcor-var-lst
      (implies (symbol-listp terms)
               (<= (term-list-depth (subcor-var-lst vars terms x))
                   (term-list-depth x)))
      :flag term-list-depth
      :hints ('(:expand ((term-list-depth x)
                         (:free (a b) (term-list-depth (cons a b))))))
      :rule-classes :linear))

  (defthm term-depth-gt-args
    (implies (and (consp x)
                  (not (equal (car x) 'quote)))
             (< (term-list-depth (cdr x))
                (term-depth x)))
    :hints (("goal" :expand ((term-depth x))))
    :rule-classes :linear)

  (defthm term-depth-gt-lambda-body
    (implies (and (consp x)
                  (consp (car x)))
             (< (term-depth (caddar x))
                (term-depth x)))
    :hints (("goal" :expand ((term-depth x))))
    :rule-classes :linear)

  (defthm term-list-depth-gte-car
    (<= (term-depth (car x)) (term-list-depth x))
    :hints (("goal" :expand ((term-list-depth x))))
    :rule-classes :linear)

  (defthm term-list-depth-gte-cdr
    (<= (term-list-depth (cdr x)) (term-list-depth x))
    :hints (("goal" :expand ((term-list-depth x))))
    :rule-classes :linear))



;; (defines term-count
;;   (define term-count ((x pseudo-termp))
;;     :returns (count posp :rule-classes :type-prescription)
;;     (cond ((variablep x) 1)
;;           ((fquotep x) 1)
;;           (t (b* ((fn (ffn-symb x)))
;;                (+ 1
;;                   (term-list-count (fargs x))
;;                   (if (consp fn)
;;                       (term-count (lambda-body fn))
;;                     0))))))
;;   (define term-list-count ((x pseudo-term-listp))
;;     :returns (count posp :rule-classes :type-prescription)
;;     (if (Atom x)
;;         1
;;       (+ (term-count (car x))
;;          (term-list-count (cdr x)))))
;;   ///
;;   (defthm term-count-of-cons-term
;;     (<= (term-count (cons-term fn args))
;;         (term-count (cons fn args)))
;;     :hints (("Goal" :Expand ((:free (fn args) (term-count (cons fn args))))))
;;     :rule-classes :linear)

;;   (defthm term-count-of-subcor-var1-of-var
;;     (implies (and (symbol-listp terms)
;;                   (atom x))
;;              (equal (term-count (subcor-var1 vars terms x))
;;                     1))
;;     :hints(("Goal" :in-theory (enable subcor-var1)
;;             :induct t
;;             :expand ((term-count x)
;;                      (term-count (Car terms))))))

;;   (defthm-term-count-flag
;;     (defthm term-count-of-subcor-var
;;       (implies (symbol-listp terms)
;;                (<= (term-count (subcor-var vars terms x))
;;                    (term-count x)))
;;       :flag term-count
;;       :hints ('(:expand ((term-count x)
;;                          (:free (args) (term-count (cons (car x) args))))))
;;       :rule-classes :linear)
;;     (defthm term-list-count-of-subcor-var-lst
;;       (implies (symbol-listp terms)
;;                (<= (term-list-count (subcor-var-lst vars terms x))
;;                    (term-list-count x)))
;;       :flag term-list-count
;;       :hints ('(:expand ((term-list-count x)
;;                          (:free (a b) (term-list-count (cons a b))))))
;;       :rule-classes :linear))

;;   (defthm term-count-gt-args
;;     (implies (and (consp x)
;;                   (not (equal (car x) 'quote)))
;;              (< (term-list-count (cdr x))
;;                 (term-count x)))
;;     :hints (("goal" :expand ((term-count x))))
;;     :rule-classes :linear)

;;   (defthm term-count-gt-lambda-body
;;     (implies (and (consp x)
;;                   (consp (car x)))
;;              (< (term-count (caddar x))
;;                 (term-count x)))
;;     :hints (("goal" :expand ((term-count x))))
;;     :rule-classes :linear)

;;   (defthm term-list-count-gte-car
;;     (<= (term-count (car x)) (term-list-count x))
;;     :hints (("goal" :expand ((term-list-count x))))
;;     :rule-classes :linear)

;;   (defthm term-list-count-gt-car
;;     (implies (consp x)
;;              (< (term-count (car x)) (term-list-count x)))
;;     :hints (("goal" :expand ((term-list-count x))))
;;     :rule-classes :linear)

;;   (defthm term-list-count-gte-cdr
;;     (<= (term-list-count (cdr x)) (term-list-count x))
;;     :hints (("goal" :expand ((term-list-count x))))
;;     :rule-classes :linear)

;;   (defthm term-list-count-gt-cdr
;;     (implies (consp x)
;;              (< (term-list-count (cdr x)) (term-list-count x)))
;;     :hints (("goal" :expand ((term-list-count x))))
;;     :rule-classes :linear))

(local (defthm position-equal-ac-under-iff
         (implies n
                  (iff (position-equal-ac x y n)
                       (member x y)))))

#||
;; Matt -- A couple of bugs in obviously-equiv-terms:

;; the following condition isn't sufficient:
                  ((OR (FQUOTEP X) (FQUOTEP Y))
                   (AND IFF-FLG
                        (EQUAL (EQUAL X *NIL*)
                               (EQUAL Y *NIL*))))
;; e.g., x is 'a and y is (foo).


;; The current definition of obviously-equal-lambda-args can sometimes
;; cause an assertion violation.  E.g.:
:trans (let ((z z) (x x)) (declare (ignore z)) (cons x nil))

((LAMBDA (Z X) (CONS X 'NIL))
 (HIDE Z)
 X)

:trans (let ((x x) (y y)) (declare (ignore y)) (cons x nil))

((LAMBDA (X Y) (CONS X 'NIL))
 X (HIDE Y))


(obviously-equiv-terms '((LAMBDA (Z X) (CONS X 'NIL))
 (HIDE Z)
 X)
'((LAMBDA (X Y) (CONS X 'NIL))
  X (HIDE Y)) nil)

;; The assertion in obviously-equal-lambda-args holds if x-formals-tail is a
;; subset of y-formals.  The call of obviously-equal-lambda-args is guarded by
;; a call of obviously-equiv-terms on the lambda bodies of those formals, which
;; maybe implies that the set of free variables are equivalent, but in the
;; above case not all the formals are actually free variables of the lambda
;; bodies.

||#


;; (defun l-obviously-equal-lambda-args (x-formals-tail x-args-tail y-formals
;;                                                      y-args)
;;   (declare (xargs :measure (len x-formals-tail)
;;                   :guard (and (symbol-listp x-formals-tail)
;;                               (pseudo-term-listp x-args-tail)
;;                               (symbol-listp y-formals)
;;                               (pseudo-term-listp y-args))))

;; ; We know that y-formals is a permutation of x-formals.  We recur through
;; ; x-formals and x-args, checking that correspond arguments are equal.

;;   (cond ((endp x-formals-tail) t)
;;         (t (let ((posn (position-eq (car x-formals-tail) y-formals)))
;;              (and posn
;;                   (equal (car x-args-tail)
;;                          (nth posn y-args))
;;                   (l-obviously-equal-lambda-args (cdr x-formals-tail)
;;                                                  (cdr x-args-tail)
;;                                                  y-formals y-args))))))


(verify-termination obviously-equal-lambda-args)


;; Note: this is the same as obviously-equiv-terms/obviously-equiv-terms-lst
;; except for the occurrence of mbt.  Matt might add that to the definition in
;; which case we can replace this with:
;; (verify-termination
;;  (obviously-equiv-terms
;;   (declare (xargs :measure (two-nats-measure (max (term-depth x) (term-depth y)) 0)
;;                   :verify-guards nil)))
;;  (obviously-equiv-terms-lst
;;   (declare (xargs :measure (two-nats-measure (max (term-list-depth x) (term-list-depth y)) (len x))))))
;; and then replace all occurrences of l-obviously-equiv with obviously-equiv below.

(mutual-recursion

 (defun l-obviously-equiv-terms (x y iff-flg)
   (declare (xargs :measure (two-nats-measure
                             (max (term-depth x)
                                  (term-depth y))
                             0)
                   :hints (("goal" :do-not-induct t))
                   :measure-debug t
                   ;; :ruler-extenders :all
                   :guard (and (pseudo-termp x)
                               (pseudo-termp y))
                   :verify-guards nil))

; Warning: It is desirable to keep this reasonably in sync with untranslate1,
; specifically, giving similar attention in both to functions like implies,
; iff, and not, which depend only on the propositional equivalence class of
; each argument.

; Here we code a restricted version of equivalence of x and y, for use in
; chk-defabsstobj-method-lemmas or other places where we expect this to be
; sufficient.  The only requirement is that if (l-obviously-equiv-terms x y
; iff-flg), then (equal x y) a theorem (in every theory extending the
; ground-zero theory) unless iff-flg is true, in which case (iff x y) is a
; theorem.

   (or (equal x y) ; common case
       (cond ((or (variablep x)
                  (variablep y))
              nil)
             ((or (fquotep x)
                  (fquotep y))
              (and iff-flg
                   (fquotep x)
                   (fquotep y)
                   (unquote x)
                   (unquote y)))
             ((flambda-applicationp x)
              (and (flambda-applicationp y)

; There are (at least) two ways that x and y can be l-obviously equivalent.

; (1) The arguments agree, and their lambdas (function symbols) are equivalent
;     but have different formals and correspondingly different bodies, for
;     example:
;       ((lambda (x y) (cons x y)) '3 '4)
;       ((lambda (u v) (cons u v)) '3 '4)

; (2) The formals in the lambdas have been permuted and the arguments have been
;     correspondingly permuted, and the bodies of the lambdas are the same, for
;     example:
;       ((lambda (x y) (cons x y)) '3 '4)
;       ((lambda (y x) (cons x y)) '4 '3)

; Of course the function symbols of x and y can be equal, which fits into both
; (1) and (2).  And the discrepancies of (1) and (2) can happen together, as in
; the following example:
;       ((lambda (x y) (cons x y)) '3 '4)
;       ((lambda (u v) (cons v u)) '4 '3)

; But it is more complicated to handle this combination in full generality, so
; we content ourselves with (1) and (2).

                   (let ((x-fn (ffn-symb x))
                         (y-fn (ffn-symb y))
                         (x-args (fargs x))
                         (y-args (fargs y)))
                     (cond
                      ((equal x-fn y-fn) ; simple case
                       (l-obviously-equiv-terms-lst x-args y-args))
                      (t
                       (let ((x-formals (lambda-formals x-fn))
                             (x-body (lambda-body x-fn))
                             (y-formals (lambda-formals y-fn))
                             (y-body (lambda-body y-fn)))
                         (and (mbt (symbol-listp y-formals))
                              (eql (length x-formals) (length y-formals))
                              (or

; (1) -- see above

                               (and (l-obviously-equiv-terms
                                     (subcor-var x-formals y-formals x-body)
                                     y-body
                                     iff-flg)
                                    (l-obviously-equiv-terms-lst x-args y-args))

; (2) -- see above

                               (and (l-obviously-equiv-terms
                                     x-body y-body iff-flg)
                                    (obviously-equal-lambda-args
                                     x-formals (fargs x)
                                     y-formals (fargs y)))))))))))
             ((not (eq (ffn-symb x) (ffn-symb y)))
              nil)
             ((member-eq (ffn-symb x) '(implies iff))
              (and (l-obviously-equiv-terms (fargn x 1) (fargn y 1) t)
                   (l-obviously-equiv-terms (fargn x 2) (fargn y 2) t)))
             ((eq (ffn-symb x) 'not)
              (l-obviously-equiv-terms (fargn x 1) (fargn y 1) t))
             ((eq (ffn-symb x) 'if)
              (and (l-obviously-equiv-terms (fargn x 1) (fargn y 1) t)
                   (l-obviously-equiv-terms (fargn x 3) (fargn y 3) iff-flg)
                   (or (l-obviously-equiv-terms (fargn x 2) (fargn y 2) iff-flg)

; Handle case that a term is of the form (or u v).

                       (and iff-flg
                            (cond ((equal (fargn x 2) *t*)
                                   (l-obviously-equiv-terms
                                    (fargn y 2) (fargn y 1) t))
                                  ((equal (fargn y 2) *t*)
                                   (l-obviously-equiv-terms
                                    (fargn x 2) (fargn x 1) t))
                                  (t nil))))))
             (t (and (equal (length (fargs x))
                            (length (fargs y)))
                     (l-obviously-equiv-terms-lst (fargs x) (fargs y)))))))

 (defun l-obviously-equiv-terms-lst (x y)
   (declare (xargs :measure (two-nats-measure
                             (max (term-list-depth x)
                                  (term-list-depth y))
                             (len x))
                   :guard (and (pseudo-term-listp x)
                               (pseudo-term-listp y))))

; X and y are true-lists of the same length.

   (cond ((endp x) t)
         (t (and (l-obviously-equiv-terms (car x) (car y) nil)
                 (l-obviously-equiv-terms-lst (cdr x) (cdr y))))))


 )




(flag::make-flag l-obviously-equiv-terms-flag
                 l-obviously-equiv-terms
                 :flag-mapping
                 ((l-obviously-equiv-terms term)
                  (l-obviously-equiv-terms-lst list))
                 :hints (("goal" :do-not-induct t)))

(defsection l-obviously-equiv-terms-guards
  (local (include-book "meta/pseudo-termp-lemmas" :dir :system))
  (local (defthm pseudo-term-listp-when-symbol-listp
           (implies (symbol-listp x)
                    (pseudo-term-listp x))))

  (defthm subcor-var1-pseudo-termp
    (implies (and (pseudo-term-listp terms)
                  (pseudo-termp x))
             (pseudo-termp (subcor-var1 vars terms x))))

  ;; (defthm pseudo-termp-of-cons-term
  ;;   (implies (and (symbolp fn)
  ;;                 (not (eq fn 'quote))
  ;;                 (pseudo-term-listp args))
  ;;            (pseudo-termp (cons-term fn args)))
  ;;   :hints(("Goal" :in-theory (enable cons-term))))

  (defthm pseudo-termp-of-cons-term-car-x
    (implies (and (consp x)
                  (not (eq (car x) 'quote))
                  (pseudo-termp x)
                  (equal (len (cdr x)) (len args))
                  (pseudo-term-listp args))
             (pseudo-termp (cons-term (car x) args)))
    :hints(("Goal" :in-theory (enable cons-term)
            :expand ((pseudo-termp x)))))

  (defthm len-of-subcor-var-lst
    (equal (len (subcor-var-lst vars terms x))
           (len x))
    :hints (("goal" :induct (len x)
             :in-theory (enable subcor-var-lst))))

  (defthm-term-depth-flag subcor-var-pseudo-termp
    (defthm subcor-var-pseudo-termp
      (implies (and (pseudo-termp x)
                    (pseudo-term-listp terms))
               (pseudo-termp (subcor-var vars terms x)))
      :flag term-depth)
    (defthm subcor-var-lst-pseudo-termp
      (implies (and (pseudo-term-listp x)
                    (pseudo-term-listp terms))
               (pseudo-term-listp (subcor-var-lst vars terms x)))
      :flag term-list-depth))

  (verify-guards l-obviously-equiv-terms))


(include-book "std/lists/index-of" :dir :system)

(defthm position-equal-ac-elim
  (implies (acl2-numberp n)
           (equal (position-equal-ac k x n)
                  (and (index-of k x)
                       (+ n (index-of k x)))))
  :hints(("Goal" :in-theory (enable index-of position-equal-ac))))

(defthm assoc-in-pairlis$
  (equal (assoc v (pairlis$ vars terms))
         (and (member v vars)
              (cons v (nth (index-of v vars) terms))))
  :hints(("Goal" :in-theory (enable index-of nth))))

(defthm hons-assoc-in-pairlis$
  (equal (hons-assoc-equal v (pairlis$ vars terms))
         (and (member v vars)
              (cons v (nth (index-of v vars) terms))))
  :hints(("Goal" :in-theory (enable index-of nth))))

(defthm acl2-numberp-of-index-of
  (iff (acl2-numberp (index-of v x))
       (index-of v x))
  :hints(("Goal" :in-theory (enable index-of))))

(defthm obviously-equal-lambda-args-implies
  (implies (and (obviously-equal-lambda-args x-formals-tail x-args-tail
                                               y-formals y-args)
                (symbol-listp y-formals)
                (member v x-formals-tail))
           (and (member v y-formals)
                (equal (nth (index-of v y-formals) y-args)
                       (nth (index-of v x-formals-tail) x-args-tail))))
  :hints(("Goal" :in-theory (enable nth index-of))))

(defun set-equiv-by-len-ind (x y)
  (if (atom x)
      y
    (set-equiv-by-len-ind (cdr x) (remove (car x) y))))

(include-book "std/lists/sets" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)

(defthm len-of-remove-weak
  (<= (len (remove k x)) (len x))
  :rule-classes :linear)
(defthm len-of-remove-strong
  (implies (member k x)
           (< (len (remove k x)) (len x)))
  :rule-classes :linear)

(defthm set-equiv-by-len-lemma
  (implies (and (subsetp x y)
                (no-duplicatesp x)
                (>= (len x) (len y))
                (member v y))
           (member v x))
  :hints (("goal" :induct (set-equiv-by-len-ind x y)
           :in-theory (enable member subsetp no-duplicatesp))))

(defthm obviously-equal-lambda-args-implies-subsetp
  (implies (and (obviously-equal-lambda-args x-formals-tail x-args-tail
                                               y-formals y-args)
                (symbol-listp y-formals))
           (subsetp x-formals-tail y-formals))
  :hints ((set-reasoning)))



(defthm obviously-equal-lambda-args-implies-set-equiv
  (implies (and (obviously-equal-lambda-args x-formals x-args
                                               y-formals y-args)
                (no-duplicatesp x-formals)
                (symbol-listp y-formals)
                (equal (len x-formals) (len y-formals)))
           (set-equiv x-formals y-formals))
  :hints ((set-reasoning)
          (and stable-under-simplificationp
               '(:use ((:instance set-equiv-by-len-lemma
                        (v k0) (x x-formals) (y y-formals)))
                 :in-theory (disable set-equiv-by-len-lemma)
                 :do-not-induct t))))


(defevaluator-fast obv-ev obv-ev-lst
  ((acl2-numberp x)
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
   (iff x y)
   (implies x y)
   (typespec-check ts x))
  :namedp t)

(defun obv-ev-alist (x a)
  (if (atom x)
      nil
    (cons (cons (caar x) (obv-ev (cdar x) a))
          (obv-ev-alist (cdr x) a))))

(defthm lookup-in-obv-ev-alist
  (implies k
           (equal (assoc k (obv-ev-alist x a))
                  (and (assoc k x)
                       (cons k (obv-ev (cdr (assoc k x)) a))))))

(defthm assoc-of-append-when-alistp-x
  (implies (alistp x)
           (equal (assoc k (append x y))
                  (or (assoc k x)
                      (assoc k y)))))

(defthm alistp-of-obv-ev-alist
  (alistp (obv-ev-alist x a)))

(def-functional-instance
  obv-ev-cons-term-correct
  cterm-ev-cons-term-correct
  ((cterm-ev obv-ev)
   (cterm-ev-lst obv-ev-lst))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable obv-ev-of-fncall-args)))))

(def-functional-instance
  obv-ev-of-sublis-var
  eval-of-sublis-var
  ((cterm-ev obv-ev)
   (cterm-ev-lst obv-ev-lst)
   (cterm-ev-alist obv-ev-alist))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable obv-ev-of-fncall-args)))))

(def-functional-instance
  obv-ev-lst-of-pairlis
  ev-lst-of-pairlis
  ((mextract-ev obv-ev)
   (mextract-ev-lst obv-ev-lst))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable obv-ev-of-fncall-args)))))

;; (defthm subcor-var1-equals
;;   (equal (subcor-var1 vars terms x)
;;          (let ((look (assoc x (pairlis$ vars terms))))
;;            (if look (cdr look) x))))

(defthm obv-ev-of-subcor-var1
  (implies (and (symbolp x) x)
           (equal (obv-ev (subcor-var1 vars terms x) a)
                  (obv-ev x (append (pairlis$ vars (obv-ev-lst terms a)) a))))
  :hints(("Goal" :in-theory (enable subcor-var1))))

(defines no-nils-pseudo-termp
  (define no-nils-pseudo-termp ((x pseudo-termp))
    (cond ((atom x) x)
          ((fquotep x) t)
          (t (and (no-nils-pseudo-term-listp (cdr x))
                  (or (atom (car x))
                      (no-nils-pseudo-termp (caddr (car x))))))))
  (define no-nils-pseudo-term-listp ((x pseudo-term-listp))
    (if (atom x)
        t
      (and (no-nils-pseudo-termp (car x))
           (no-nils-pseudo-term-listp (cdr x))))))


(defthm-term-depth-flag
  (defthm obv-ev-of-subcor-var
    (implies (and (pseudo-termp x)
                  (no-nils-pseudo-termp x))
             (equal (obv-ev (subcor-var vars terms x) a)
                    (obv-ev x (append (pairlis$ vars (obv-ev-lst terms a)) a))))
    :hints ('(:expand ((subcor-var vars terms x)
                       (no-nils-pseudo-termp x))
              :in-theory (enable obv-ev-of-fncall-args)))
    :flag term-depth)
  (defthm obv-ev-lst-of-subcor-var-lst
    (implies (and (pseudo-term-listp x)
                  (no-nils-pseudo-term-listp x))
             (equal (obv-ev-lst (subcor-var-lst vars terms x) a)
                    (obv-ev-lst x (append (pairlis$ vars (obv-ev-lst terms a)) a))))
    :hints ('(:expand ((subcor-var-lst vars terms x)
                       (no-nils-pseudo-term-listp x))
              :in-theory (enable obv-ev-of-fncall-args)))
    :flag term-list-depth))

(defthm hons-assoc-equal-of-append
  (equal (hons-assoc-equal x (append y z))
         (or (hons-assoc-equal x y)
             (hons-assoc-equal x z))))

;; (defthm-term-depth-flag
;;   (defthm obv-ev-of-subcor-var
;;     (implies (and (pseudo-termp x))
;;              (equal (obv-ev (subcor-var vars terms x) a)
;;                     (obv-ev x (append (pairlis$ vars (obv-ev-lst terms a)) a))))
;;     :hints ('(:expand ((subcor-var vars terms x)
;;                        ;; (no-nils-pseudo-termp x)
;;                        )
;;               :in-theory (enable obv-ev-of-fncall-args)))
;;     :flag term-depth)
;;   (defthm obv-ev-lst-of-subcor-var-lst
;;     (implies (and (pseudo-term-listp x))
;;              (equal (obv-ev-lst (subcor-var-lst vars terms x) a)
;;                     (obv-ev-lst x (append (pairlis$ vars (obv-ev-lst terms a)) a))))
;;     :hints ('(:expand ((subcor-var-lst vars terms x)
;;                        ;; (no-nils-pseudo-term-listp x)
;;                        )
;;               :in-theory (enable obv-ev-of-fncall-args)))
;;     :flag term-list-depth))

(defthm nth-of-obv-ev-lst
  (equal (nth n (obv-ev-lst x a))
         (obv-ev (nth n x) a))
  :hints(("Goal" :in-theory (enable nth))))

(include-book "std/alists/alist-equiv" :dir :System)
(defthm obviously-equal-lambda-args-implies-alist-equiv
  (implies (and (obviously-equal-lambda-args x-formals x-args
                                               y-formals y-args)
                (no-duplicatesp x-formals)
                (symbol-listp y-formals)
                (equal (len x-formals) (len y-formals)))
           (equal (alist-equiv (pairlis$ x-formals (obv-ev-lst x-args a))
                               (pairlis$ y-formals (obv-ev-lst y-args a)))
                  t))
  :hints (("goal" :in-theory (e/d (alist-equiv-iff-agree-on-bad-guy)
                                  (obviously-equal-lambda-args-implies-set-equiv))
           :use obviously-equal-lambda-args-implies-set-equiv
           :do-not-induct t)))

(defthm assoc-equal-when-key
  (implies k
           (equal (assoc-equal k x)
                  (hons-assoc-equal k x))))

(defthm-term-depth-flag
  (defthm alist-equiv-congruence-on-obv-ev
    (implies (and (alist-equiv a b)
                  (pseudo-termp x))
             (equal (equal (obv-ev x a)
                           (obv-ev x b))
                    t))
    :hints ('(:in-theory (enable obv-ev-of-fncall-args)))
    :flag term-depth)
  (defthm alist-equiv-congruence-on-obv-ev-lst
    (implies (and (alist-equiv a b)
                  (pseudo-term-listp x))
             (equal (equal (obv-ev-lst x a)
                           (obv-ev-lst x b))
                    t))
    :flag term-list-depth))


(defthm eval-with-obviously-equal-lambda-args
  (implies (and (obviously-equal-lambda-args x-formals x-args
                                               y-formals y-args)
                (no-duplicatesp x-formals)
                (symbol-listp y-formals)
                (equal (len x-formals) (len y-formals))
                (pseudo-termp term))
           (equal (obv-ev term (pairlis$ x-formals (obv-ev-lst x-args a)))
                  (obv-ev term (pairlis$ y-formals (obv-ev-lst y-args a)))))
  :hints (("goal" :do-not-induct t)))


(defthm-term-depth-flag
  (defthm termp-implies-no-nils-pseudo-termp
    (implies (termp x w)
             (no-nils-pseudo-termp x))
    :hints ('(:expand ((termp x w)
                       (no-nils-pseudo-termp x))))
    :flag term-depth)
  (defthm term-listp-implies-pseudo-termp
    (implies (term-listp x w)
             (no-nils-pseudo-term-listp x))
    :hints ('(:expand ((term-listp x w)
                       (no-nils-pseudo-term-listp x))))
    :flag term-list-depth))

(defthm termp-of-cons-term
  (implies (and (termp x w)
                (consp x)
                (not (Eq (car x) 'quote))
                (term-listp args w)
                (equal (len args) (len (cdr x))))
           (termp (cons-term (car x) args) w))
  :hints(("Goal" :in-theory (enable cons-term)
          :expand ((termp x w))
          :do-not-induct t)))


(defthm-term-depth-flag
  (defthm termp-of-subcor-var
    (implies (and (termp x w)
                  (term-listp terms w)
                  (eql (len terms) (len vars)))
             (termp (subcor-var vars terms x) w))
    :hints ('(:expand ((termp x w)
                       (subcor-var vars terms x))))
    :flag term-depth)
  (defthm term-listp-of-subcor-var
    (implies (and (term-listp x w)
                  (term-listp terms w)
                  (eql (len terms) (len vars)))
             (term-listp (subcor-var-lst vars terms x) w))
    :hints ('(:expand ((term-listp x w)
                       (subcor-var-lst vars terms x))))
    :flag term-list-depth))

(defsection all-vars-redef
  (local (flag::make-flag all-vars1-flag all-vars1))

  (local (defun-sk all-vars1-accumulator-cond (term)
           (forall acc
                   (implies (syntaxp (not (equal acc ''nil)))
                            (set-equiv (all-vars1 term acc)
                                       (append acc
                                               (all-vars1 term nil)))))
           :rewrite :direct))
  (local (defun-sk all-vars1-lst-accumulator-cond (lst)
           (forall acc
                   (implies (syntaxp (not (equal acc ''nil)))
                            (set-equiv (all-vars1-lst lst acc)
                                       (append acc (all-vars1-lst lst nil)))))
           :rewrite :direct))

  (local
   (defthm-all-vars1-flag
     (defthm all-vars1-accumulator-elim-lemma
       (all-vars1-accumulator-cond term)
       :hints ('(:expand ((all-vars1-accumulator-cond term)
                          (:free (acc) (all-vars1 term acc)))))
       :flag all-vars1)
     (defthm all-vars1-lst-accumulator-elim-lemma
       (all-vars1-lst-accumulator-cond lst)
       :hints ('(:expand ((all-vars1-lst-accumulator-cond lst)
                          (:free (acc) (all-vars1 lst acc)))))
       :flag all-vars1-lst)))

  (defthm all-vars1-accumulator-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (set-equiv (all-vars1 term acc)
                        (append acc
                                (all-vars1 term nil)))))

  (defthm all-vars1-lst-accumulator-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (set-equiv (all-vars1-lst lst acc)
                        (append acc (all-vars1-lst lst nil)))))

  (defun all-vars-lst (lst)
    (if (atom lst)
        nil
      (append (all-vars (car lst))
              (all-vars-lst (cdr lst)))))

  (local (defthm all-vars1-lst-is-all-vars-lst
           (set-equiv (all-vars1-lst lst nil)
                      (all-vars-lst lst))
           :hints(("Goal" :in-theory (enable all-vars)))))

  (defthm all-vars-redef
    (set-equiv (all-vars term)
               (cond ((variablep term) (list term))
                     ((fquotep term) nil)
                     (t (all-vars-lst (cdr term)))))
    :hints(("Goal" :in-theory (enable all-vars)
            :expand ((all-vars1 term nil))))
    :rule-classes
    ((:definition
      :clique (all-vars all-vars-lst)
      :controller-alist ((all-vars t)
                         (all-vars-lst t))))))

(local (in-theory (disable all-vars)))

(defthm-term-depth-flag
  (defthm obv-ev-of-append-pairlis-when-vars-subset-of-first
    (implies (and (pseudo-termp x)
                  (no-nils-pseudo-termp x)
                  (subsetp (all-vars x) vars1))
             (equal (obv-ev x (append (pairlis$ vars1 vals1) rest))
                    (obv-ev x (pairlis$ vars1 vals1))))
    :hints ('(:expand ((pseudo-termp x)
                       (no-nils-pseudo-termp x)
                       (:with all-vars-redef (all-vars x)))
              :in-theory (enable obv-ev-of-fncall-args)))
    :flag term-depth)
  (defthm obv-ev-lst-of-append-pairlis-when-vars-subset-of-first
    (implies (and (pseudo-term-listp x)
                  (no-nils-pseudo-term-listp x)
                  (subsetp (all-vars-lst x) vars1))
             (equal (obv-ev-lst x (append (pairlis$ vars1 vals1) rest))
                    (obv-ev-lst x (pairlis$ vars1 vals1))))
    :hints ('(:expand ((pseudo-term-listp x)
                       (no-nils-pseudo-term-listp x)
                       (all-vars-lst x))))
    :flag term-list-depth))


(defthm term-listp-when-arglistp1
  (implies (arglistp1 x)
           (term-listp x w))
  :hints(("Goal" :in-theory (enable arglistp1)
          :induct (Arglistp1 x)
          :expand ((termp (car x) w)
                   (term-listp x w)))))

(local (in-theory (disable termp)))
(defsection termp-lemmas
  (local (in-theory (enable termp)))
  (defthm term-listp-of-args
    (implies (and (termp x w)
                  (consp x)
                  (not (eq (car x) 'quote)))
             (term-listp (cdr x) w)))

  (defthm termp-of-args-when-ternary
    (implies (and (termp x w)
                  (consp x)
                  (not (eq (car x) 'quote))
                  (not (consp (car x)))
                  (equal (arity (car x) w) 3))
             (and (termp (cadr x) w)
                  (termp (caddr x) w)
                  (termp (cadddr x) w))))

  (defthm termp-of-args-when-binary
    (implies (and (termp x w)
                  (consp x)
                  (not (eq (car x) 'quote))
                  (not (consp (car x)))
                  (equal (arity (car x) w) 2))
             (and (termp (cadr x) w)
                  (termp (caddr x) w))))

  (defthm termp-of-args-when-unary
    (implies (and (termp x w)
                  (consp x)
                  (not (eq (car x) 'quote))
                  (not (consp (car x)))
                  (equal (arity (car x) w) 1))
             (and (termp (cadr x) w))))

  (defthm termp-when-quote
    (implies (and (equal (car x) 'quote)
                  (consp (cdr x))
                  (null (cddr x)))
             (termp x w)))

  (local (defthm symbol-listp-when-arglistp1
           (implies (arglistp1 x)
                    (symbol-listp x))))

  (local (defthm member-nil-when-arglistp1
           (implies (arglistp1 x)
                    (not (member nil x)))))

  (local (defthm not-set-difference-implies-subset
           (implies (not (set-difference$ x y))
                    (subsetp x y))
           :hints(("Goal" :in-theory (enable set-difference$
                                             subsetp)))))

  (defthm termp-when-lambda
    (implies (and (termp x w)
                  (consp (car x)))
             (and (termp (caddr (car x)) w)
                  (pseudo-termp (caddr (car x)))
                  (no-nils-pseudo-termp (caddr (car x)))
                  (term-listp (cadr (car x)) w)
                  (equal (len (cadr (car x)))
                         (len (cdr x)))
                  (symbol-listp (cadr (car x)))
                  (not (member nil (cadr (car x))))
                  (not (stringp (cadr (car x))))
                  (no-duplicatesp (cadr (car x)))
                  (term-listp (cdr x) w)
                  (subsetp (all-vars (caddr (car x)))
                           (cadr (car x))))))

  (defthm termp-args-same-length-when-same-function
    (implies (and (termp x w) (termp y w)
                  (consp x) (consp y)
                  (not (equal (car x) 'quote))
                  (equal (car x) (car y)))
             (equal (equal (len (cdr x))
                           (len (cdr y)))
                    t))))

(local (defthm length-is-len
         (implies (not (stringp x))
                  (equal (length x) (len x)))))

(local (defthm len-equal-0
         (equal (equal 0 (len x))
                (atom x))))

(local (defthm len-cdr-equal
         (implies (equal (len x) (len y))
                  (equal (equal (len (cdr x)) (len (cdr y))) t))))

(local (in-theory (disable length
                           subcor-var
                           len)))

(defun iff* (x y) (iff x y))
(defequiv iff*)
(defrefinement iff* iff)
(defrefinement iff iff*)
(in-theory (disable iff* take))

;; (defsection obv-ev-lst-of-pairlis$
;;   (local (defun lemma-ind (vars n)
;;            (declare (xargs :measure (nfix (- (len vars) (nfix n)))))
;;            (if (<= (len vars) (nfix n))
;;                (list n)
;;              (lemma-ind vars (+ 1 (nfix n))))))

;;   (local (defthm nthcdr-gte-len
;;            (implies (and (<= (len x) (nfix n))
;;                          (symbol-listp x))
;;                     (equal (nthcdr n x) nil))
;;            :hints(("Goal" :in-theory (enable len)))))

;;   (local (defthm obv-ev-lst-of-cons-non-member
;;            (implies (and (not (member v x))
;;                          (symbol-listp x))
;;                     (equal (obv-ev-lst x (cons (cons v val) a))
;;                            (obv-ev-lst x a)))))
;;   (local (defthm obv-ev-lst-of-pairlis$-lemma
;;            (implies (and (equal (len vars) (len vals))
;;                          (symbol-listp vars)
;;                          (no-duplicatesp vars)
;;                          (not (member nil vars))
;;                          (true-listp vals))
;;                     (equal (obv-ev-lst (nthcdr n vars)
;;                                        (pairlis$ vars vals))
;;                            (nthcdr n vals)))
;;            :hints(("Goal" :in-theory (enable arglistp1)
;;                    :induct (lemma-ind vars n)
;;                    :expand ((:free (x) (nthcdr 1 x))
;;                             (:free (x) (nthcdr (+ 1 n) x))))))))

(include-book "std/lists/take" :dir :system)

(defthm take-of-equal-to-len
  (implies (equal n (len x))
           (equal (take n x)
                  (list-fix x))))

(defthm len-of-obv-ev-lst
  (equal (len (obv-ev-lst x a))
         (len x))
  :hints(("Goal" :in-theory (enable len))))

(defthm true-listp-of-obv-ev-lst
  (true-listp (obv-ev-lst x a))
  :hints (("goal" :induct (len x)
           :in-theory (enable len)))
  :rule-classes :type-prescription)




(defines l-obviously-equiv-alist
  :flag-local nil
  (define l-obviously-equiv-alist (x y iff-flg a)
    :measure (two-nats-measure
              (max (term-depth x)
                   (term-depth y))
              0)
    :hints (("goal" :do-not-induct t
             :in-theory (enable len)))
    :verify-guards nil

    (cond ((or (variablep x)
               (variablep y))
           a)
          ((or (fquotep x)
               (fquotep y))
           (and iff-flg a))
          ((flambda-applicationp x)
           (and (flambda-applicationp y)

                (let ((x-fn (ffn-symb x))
                      (y-fn (ffn-symb y))
                      (x-args (fargs x))
                      (y-args (fargs y)))
                  (cond
                   ((equal x-fn y-fn) ; simple case
                    (l-obviously-equiv-alist-lst x-args y-args a))
                   (t
                    (let ((x-formals (lambda-formals x-fn))
                          (x-body (lambda-body x-fn))
                          (y-formals (lambda-formals y-fn))
                          (y-body (lambda-body y-fn)))
                      (and (mbt (symbol-listp y-formals))
                           (eql (length x-formals) (length y-formals))
                           (list

; (1) -- see above

                            (list (l-obviously-equiv-alist
                                   (subcor-var x-formals y-formals x-body)
                                   y-body
                                   iff-flg
                                   (pairlis$ y-formals
                                             (obv-ev-lst y-args a)))
                                  (l-obviously-equiv-alist-lst
                                   x-args y-args a))

; (2) -- see above

                            (l-obviously-equiv-alist
                             x-body y-body iff-flg
                             (pairlis$ x-formals
                                       (obv-ev-lst x-args a)))))))))))
          ((not (eq (ffn-symb x) (ffn-symb y)))
           nil)
          ((member-eq (ffn-symb x) '(implies iff))
           (list (l-obviously-equiv-alist (fargn x 1) (fargn y 1) t a)
                 (l-obviously-equiv-alist (fargn x 2) (fargn y 2) t a)))
          ((eq (ffn-symb x) 'not)
           (l-obviously-equiv-alist (fargn x 1) (fargn y 1) t a))
          ((eq (ffn-symb x) 'if)
           (list (l-obviously-equiv-alist (fargn x 1) (fargn y 1) t a)
                 (l-obviously-equiv-alist (fargn x 3) (fargn y 3) iff-flg a)
                 (l-obviously-equiv-alist (fargn x 2) (fargn y 2) iff-flg a)

; Handle case that a term is of the form (or u v).

                 (cond ((equal (fargn x 2) *t*)
                        (l-obviously-equiv-alist
                         (fargn y 2) (fargn y 1) t a))
                       ((equal (fargn y 2) *t*)
                        (l-obviously-equiv-alist
                         (fargn x 2) (fargn x 1) t a))
                       (t nil))))
          (t (and (equal (length (fargs x))
                         (length (fargs y)))
                  (l-obviously-equiv-alist-lst (fargs x) (fargs y) a)))))

 (define l-obviously-equiv-alist-lst (x y a)
   :measure (two-nats-measure
             (max (term-list-depth x)
                  (term-list-depth y))
             (len x))

; X and y are true-lists of the same length.

   (cond ((endp x) t)
         (t (list (l-obviously-equiv-alist (car x) (car y) nil a)
                  (l-obviously-equiv-alist-lst (cdr x) (cdr y) a)))))
 ///

 (local (defthm not-stringp-cdr-when-pseudo-termp
          (implies (and (pseudo-termp y)
                        (consp y)
                        (not (eq (car y) 'quote)))
                   (not (stringp (cdr y))))
          :hints(("Goal" :in-theory (enable pseudo-termp)))))

 (local (defthm true-listp-when-arglistp1
          (implies (arglistp1 x)
                   (true-listp x))
          :rule-classes :compound-recognizer))

 (local (in-theory (disable l-obviously-equiv-terms
                            l-obviously-equiv-terms-lst
                            pseudo-termp pseudo-term-listp
                            pseudo-termp-opener
                            default-car default-cdr
                            no-duplicatesp
                            arglistp1
                            all-vars1)))

 (defthm-l-obviously-equiv-alist-flag l-obviously-equiv-terms-equal-implies-iff
  (Defthm l-obviously-equiv-terms-equal-implies-iff
    (implies (and (equal (arity 'if w) 3)
                  (equal (arity 'implies w) 2)
                  (equal (arity 'iff w) 2)
                  (termp x w)
                  (termp y w))
             (implies (l-obviously-equiv-terms x y nil)
                      (l-obviously-equiv-terms x y t)))
    :hints ('(:expand ((:free (iff-flg) (l-obviously-equiv-terms x y iff-flg))
                       (:free (x iff-flg) (l-obviously-equiv-terms x x iff-flg))
                       (termp x w)
                       (termp y w)
                       (term-listp (cdr x) w)
                       (term-listp (cdr y) w)
                       (term-listp (cddr x) w)
                       (term-listp (cddr y) w)
                       (term-listp (cdddr x) w)
                       (term-listp (cdddr y) w))
              :do-not-induct t
              :in-theory (enable obv-ev-of-fncall-args
                                 default-car default-cdr)))
    :flag l-obviously-equiv-alist)
  :skip-others t)


 (defthm-l-obviously-equiv-alist-flag l-obviously-equiv-terms-correct
  (defthm l-obviously-equiv-terms-correct
    (implies (and (equal (arity 'if w) 3)
                  (equal (arity 'implies w) 2)
                  (equal (arity 'iff w) 2)
                  (equal (arity 'not w) 1)
                  (termp x w)
                  (termp y w))
             (and (implies (l-obviously-equiv-terms x y t)
                           (iff* (obv-ev x a)
                                 (obv-ev y a)))
                  (implies (l-obviously-equiv-terms x y nil)
                           (equal (obv-ev x a)
                                  (obv-ev y a)))))
    :hints ('(:expand ((:free (iff-flg) (l-obviously-equiv-terms x y iff-flg))
                       ;; (termp x w)
                       ;; (termp y w)
                       )
              :do-not-induct t
              :in-theory (enable obv-ev-of-fncall-args)))
    :flag l-obviously-equiv-alist)
  (defthm l-obviously-equiv-terms-lst-correct
    (implies (and (term-listp x w)
                  (term-listp y w)
                  (equal (arity 'if w) 3)
                  (equal (arity 'implies w) 2)
                  (equal (arity 'iff w) 2)
                  (equal (arity 'not w) 1)
                  (equal (len x) (len y)))
             (implies (l-obviously-equiv-terms-lst x y)
                      (equal (obv-ev-lst x a)
                             (obv-ev-lst y a))))
    :hints ('(:expand ((:free () (l-obviously-equiv-terms-lst x y))
                       (term-listp x w)
                       (term-listp y w))))
    :flag l-obviously-equiv-alist-lst)))
