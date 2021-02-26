(in-package "SMT")
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")
;; (include-book "term-rectify")
;; (include-book "term-projection")
(set-state-ok t)

(defalist rational-integer-alist
  :key-type rationalp
  :val-type integerp
  :pred rational-integer-alistp
  :true-listp t)

(define rational-integer-cons-p ((x t))
  (and (consp x)
       (rationalp (car x))
       (integerp (cdr x))))

(easy-fix rational-integer-cons (cons 0 0))

(defoption maybe-integerp integerp :pred maybe-integerp)

(defoption maybe-rational-integer-consp rational-integer-cons-p
  :pred maybe-rational-integer-consp)

(deflist rational-list
  :elt-type rationalp
  :true-listp t)

(defthm integerp-implies-maybe-integerp
  (implies (integerp x) (maybe-integerp x)))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defthm rational-integer-cons-p-implies-maybe-rational-integer-consp
  (implies (rational-integer-cons-p x) (maybe-rational-integer-consp x)))

(defun supertype ()
  `((integerp . (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                   :formals '(x)
                                   :thm 'integerp-implies-rationalp)
                 ,(make-type-tuple :type 'integerp :neighbour-type
                                   'maybe-integerp
                                   :formals '(x)
                                   :thm 'integerp-implies-maybe-integerp)))
    (rationalp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (rational-integer-cons-p . (,(make-type-tuple :type 'rational-integer-cons-p
                                                  :neighbour-type
                                                  'maybe-rational-integer-consp
                                                  :formals '(x)
                                                  :thm
                                                  'rational-integer-cons-p-implies-maybe-rational-integer-consp)))
    (rational-integer-alistp . nil)
    (maybe-integerp . nil)
    (maybe-rational-integer-consp . nil)
    (rational-list-p . nil)
    ))

(defthm maybe-integerp-can-be-integerp
  (implies (and (maybe-integerp x) x)
           (integerp x)))

(defthm maybe-rational-integer-consp-can-be-rational-integer-cons-p
  (implies (and (maybe-rational-integer-consp x) x)
           (rational-integer-cons-p x)))

(defun subtype ()
  `((rationalp . nil)
    (maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type
                                         'integerp
                                         :formals '(x)
                                         :thm 'maybe-integerp-can-be-integerp)))
    (integerp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (maybe-rational-integer-consp . (,(make-type-tuple :type 'maybe-rational-integer-consp
                                                       :neighbour-type
                                                       'rational-integer-cons-p
                                                       :formals '(x)
                                                       :thm
                                                       'maybe-rational-integer-consp-can-be-rational-integer-cons-p)))
    (rational-integer-alistp . nil)
    (rational-integer-cons-p . nil)
    (rational-list-p . nil)
    ))

(defthm return-of-assoc-equal
  (implies (and (rationalp y)
                (rational-integer-alistp x))
           (maybe-rational-integer-consp (assoc-equal y x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr-maybe
  (implies (maybe-rational-integer-consp x)
           (maybe-integerp (cdr x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr
  (implies (rational-integer-cons-p x)
           (integerp (cdr x)))
  :hints (("Goal" :in-theory (enable rational-integer-cons-p))))

(defthm return-of-not
  (implies (booleanp x)
           (booleanp (not x))))

(defthm return-of-car-rlistp
  (implies (and (rational-list-p x) x)
           (rationalp (car x))))

(defthm return-of-cdr-rlistp
  (implies (rational-list-p x)
           (rational-list-p (cdr x))))

(defthm return-of-cons
  (implies (and (rationalp x)
                (rational-list-p y))
           (and (rational-list-p (cons x y))
                (cons x y))))

(defthm return-of-<
  (implies (and (rationalp x)
                (rationalp y))
           (booleanp (< x y))))

(defthm return-of-binary-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-binary-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-* x y))))

(defthm return-of-binary-+-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-unary--
  (implies (integerp x)
           (integerp (unary-- x))))

(defthm return-of-unary---rationalp
  (implies (rationalp x)
           (rationalp (unary-- x))))

(defthm return-of-rational-integer-alistp
  (booleanp (rational-integer-alistp x)))

(defthm return-of-rational-list-p
  (booleanp (rational-list-p x)))

(defthm return-of-rationalp
  (booleanp (rationalp x)))

(defthm return-of-integerp
  (booleanp (integerp x)))

(defthm return-of-acons
  (implies (and (rationalp x)
                (integerp y)
                (rational-integer-alistp z))
           (rational-integer-alistp (acons x y z))))

(defun rational-list-car (x)
  (if (consp x) (car x) (rfix x)))

(defthm replace-of-car
  (implies (and (rational-list-p x) x)
           (equal (car x) (rational-list-car x))))

(defun rational-list-cons (x y)
  (cons x y))

(defthm replace-of-cons
  (equal (cons x y) (rational-list-cons x y)))

;; assoc-equal: rational-integer-alistp -> maybe-rational-integer-consp
;; cdr: maybe-rational-integer-consp -> maybe-integerp &
;;      rational-integer-consp -> integerp
;; <: integerp integerp -> booleanp
;; binary-+: integerp integerp -> integerp
;; unary--: integerp -> integerp
(defun functions ()
  `((acons . (,(make-return-spec
                :formals '(x y z)
                :returns-thm 'return-of-acons)))
    (assoc-equal . (,(make-return-spec
                      :formals '(y x)
                      :returns-thm 'return-of-assoc-equal)))
    (car . (,(make-return-spec
              :formals '(x)
              :returns-thm 'return-of-car-rlistp
              :replace-thm 'replace-of-car)))
    (cdr . (,(make-return-spec
              :formals '(x)
              :returns-thm 'return-of-cdr-maybe)
            ,(make-return-spec
              :formals '(x)
              :returns-thm 'return-of-cdr)
            ,(make-return-spec
              :formals '(x)
              :returns-thm 'return-of-cdr-rlistp)))
    (cons . (,(make-return-spec
               :formals '(x y)
               :returns-thm 'return-of-cons
               :replace-thm 'replace-of-cons)))
    (< . (,(make-return-spec
            :formals '(x y)
            :returns-thm 'return-of-<)))
    (binary-+ . (,(make-return-spec
                   :formals '(x y)
                   :returns-thm 'return-of-binary-+)
                 ,(make-return-spec
                   :formals '(x y)
                   :returns-thm 'return-of-binary-+-rationalp)))
    (binary-* . (,(make-return-spec
                   :formals '(x y)
                   :returns-thm 'return-of-binary-*)))
    (unary-- . (,(make-return-spec
                  :formals '(x)
                  :returns-thm 'return-of-unary--)
                ,(make-return-spec
                  :formals '(x)
                  :returns-thm 'return-of-unary---rationalp)))
    (not . (,(make-return-spec
              :formals '(x)
              :returns-thm 'return-of-not)))
    (rational-integer-alistp . (,(make-return-spec
                                  :formals '(x)
                                  :returns-thm
                                  'return-of-rational-integer-alistp)))
    (rational-list-p . (,(make-return-spec
                          :formals '(x)
                          :returns-thm 'return-of-rational-list-p)))
    (rationalp . (,(make-return-spec
                    :formals '(x)
                    :returns-thm 'return-of-rationalp)))
    (integerp . (,(make-return-spec
                   :formals '(x)
                   :returns-thm 'return-of-integerp)))))

(defun symbol-nil () nil)
(defun boolean-nil () nil)
(defun rational-integer-alist-nil () nil)
(defun maybe-integer-nil () nil)
(defun maybe-rational-integer-cons-nil () nil)
(defun rational-list-nil () nil)

(defun nil-alst ()
  '((symbolp . symbol-nil)
    (booleanp . boolean-nil)
    (rational-integer-alistp . rational-integer-alist-nil)
    (maybe-integerp . maybe-integer-nil)
    (maybe-rational-integer-consp . maybe-rational-integer-cons-nil)
    (rational-list-p . rational-list-nil)))

;; (defthm alist-to-array-equiv-of-rational-integer-alist
;;   (implies (and (rational-integer-alistp a)
;;                 (equal b (rational-integer-alist-to-array a)))
;;            (alist-array-equiv a b)))

(defun alist ()
  nil
  ;; `((rational-integer-alistp
  ;;    . ,(make-a2a-info :a2a-fn 'rational-integer-alist-to-array
  ;;                      :formals '(a b)
  ;;                      :thm 'alist-to-array-equiv-of-rational-integer-alist)))
  )

;; (defthm assoc-equal-of-rational-integer-alist
;;   (implies (and (rational-integer-alistp al)
;;                 (rational-integer-arrayp ar)
;;                 (alist-array-equiv al ar)
;;                 (rationalp k))
;;            (and (alist-array-equiv (assoc-equal k al)
;;                                    (rational-integer-assoc-equal k ))
;;                 ())))

(defun aa-map ()
  nil
  ;; `((assoc-equal
  ;;    . ,(make-equiv :formal-map '((al . al) (ar . ar) (k . k))
  ;;                   :thm assoc-equal-of-rational-integer-alist))
  ;;   (rational-integer-alistp
  ;;    . ,(make-equiv :formal-map '((al . al) (ar . ar))
  ;;                   :thm rational-integer-alistp-of-rational-integer-alist)))
  )

(defun options ()
  (b* ((supertype (supertype))
       (subtype (subtype))
       (functions (functions))
       (nil-alst (nil-alst)))
    (make-type-options
     :supertype supertype
     :subtype subtype
     :functions functions
     :nil-alst nil-alst
     :alist nil
     :aa-map nil)))

(defun term ()
  '(if (if (rational-integer-alistp al)
           (if (rationalp r1)
               (assoc-equal r1 al)
             'nil)
         'nil)
       (< (binary-+ (cdr (assoc-equal r1 al))
                    (unary-- (cdr (assoc-equal r1 al))))
          '2)
     't))

(defun term2 ()
  '(if (if (rational-integer-alistp al)
           (if (rationalp r1)
               (assoc-equal r1 al)
             'nil)
         'nil)
       (< (binary-+ (cdr (assoc-equal r1 al))
                    (unary-- (cdr (assoc-equal r1 al))))
          '2)
     't))

(defun term3 ()
  '(if (if (integerp x)
           (if (rationalp y)
               (if (< '0 y) (< x '0) 'nil)
             'nil)
         'nil)
       (< '0 (binary-+ y (unary-- x)))
     't))

(defun term4 ()
  '(if (if (rational-integer-alistp x)
           (if (integerp y)
               (assoc-equal y (acons '1 '2 x))
             'nil)
         'nil)
       (< '0 (cdr (assoc-equal y (acons '1 '2 x))))
     't))

(defun term5 ()
  '(if (if (rational-list-p l1)
           (if (integerp i1)
               l1
             'nil)
         'nil)
       (< (binary-+ (car (cons i1 l1))
                    (unary-- i1))
          '2)
     't))

(type-judgement (term) ''t (options) (all-vars (term)) state)
(type-judgement (term2) ''t (options) (all-vars (term2)) state)
(type-judgement (term3) ''t (options) (all-vars (term3)) state)
(type-judgement (term4) ''t (options) (all-vars (term4)) state)
(type-judgement (term5) ''t (options) (all-vars (term5)) state)

;; ------------------------------------------------------

(good-typed-term-p
 (make-typed-term
  :term (term)
  :path-cond ''t
  :judgements (type-judgement (term) ''t (options) (all-vars (term)) state))
 (options))

(good-typed-term-p
 (make-typed-term
  :term (term2)
  :path-cond ''t
  :judgements (type-judgement (term2) ''t (options) (all-vars (term2)) state))
 (options))

(good-typed-term-p
 (make-typed-term
  :term (term3)
  :path-cond ''t
  :judgements (type-judgement (term3) ''t (options) (all-vars (term3)) state))
 (options))

(good-typed-term-p
 (make-typed-term
  :term (term4)
  :path-cond ''t
  :judgements (type-judgement (term4) ''t (options) (all-vars (term4)) state))
 (options))

(good-typed-term-p
 (make-typed-term
  :term (term5)
  :path-cond ''t
  :judgements (type-judgement (term5) ''t (options) (all-vars (term5)) state))
 (options))

;; ------------------------------------------------------
(unify-type
 (make-typed-term
  :term (term)
  :path-cond ''t
  :judgements (type-judgement (term) ''t (options) (all-vars (term)) state))
 ''t
 (options)
 (all-vars (term))
 state)

(unify-type
 (make-typed-term
  :term (term2)
  :path-cond ''t
  :judgements (type-judgement (term2) ''t (options) (all-vars (term2)) state))
 ''t
 (options)
 (all-vars (term2))
 state)

(unify-type
 (make-typed-term
  :term (term3)
  :path-cond ''t
  :judgements (type-judgement (term3) ''t (options) (all-vars (term3)) state))
 ''t
 (options)
 (all-vars (term3))
 state)

(unify-type
 (make-typed-term
  :term (term4)
  :path-cond ''t
  :judgements (type-judgement (term4) ''t (options) (all-vars (term4)) state))
 ''t
 (options)
 (all-vars (term4))
 state)

(unify-type
 (make-typed-term
  :term (term5)
  :path-cond ''t
  :judgements (type-judgement (term5) ''t (options) (all-vars (term5)) state))
 ''t
 (options)
 (all-vars (term5))
 state)

stop
;; ------------------------------------------------------------------

(term-rectify
 (unify-type (make-typed-term :term (term)
                              :path-cond ''t
                              :judgements (type-judgement (term) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

(term-rectify
 (unify-type (make-typed-term :term (term2)
                              :path-cond ''t
                              :judgements (type-judgement (term2) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

(term-rectify
 (unify-type (make-typed-term :term (term3)
                              :path-cond ''t
                              :judgements (type-judgement (term3) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

(term-rectify
 (unify-type (make-typed-term :term (term4)
                              :path-cond ''t
                              :judgements (type-judgement (term4) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

(term-rectify
 (unify-type (make-typed-term :term (term5)
                              :path-cond ''t
                              :judgements (type-judgement (term5) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

(term-rectify
 (unify-type (make-typed-term :term (term6)
                              :path-cond ''t
                              :judgements (type-judgement (term6) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 (options)
 state)

;; --------------------------------------------------
;; test
(defun test ()
  '(if (integerp x)
       (not (< (binary-* x x) '0))
     't))

(type-judgement (test) ''t (options) state)
(unify-type (make-typed-term :term (test)
                             :path-cond ''t
                             :judgements (type-judgement (test) ''t (options)
                                                         state))
            ''t
            (options)
            state)

;; --------------------------------------------------
;; test term projection


(term-projection
 (unify-type (make-typed-term :term (term)
                              :path-cond ''t
                              :judgements (type-judgement (term) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 ''t
 ''t
 (all-vars (typed-term->term
            (unify-type (make-typed-term :term (term)
                                         :path-cond ''t
                                         :judgements (type-judgement (term) ''t (options)
                                                                     state))
                        ''t
                        (options)
                        state)))
 (options)
 state)
