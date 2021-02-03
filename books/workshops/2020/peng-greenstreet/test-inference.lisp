;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (January 13th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")
(include-book "term-rectify")
(set-state-ok t)

(fty::defalist rational-integer-alist
               :key-type rationalp
               :val-type integerp
               :pred rational-integer-alistp
               :true-listp t)

(define rational-integer-cons-p ((x t))
  (and (consp x)
       (rationalp (car x))
       (integerp (cdr x))))

(easy-fix rational-integer-cons (cons 0 0))

(fty::defoption maybe-rational-integer-consp rational-integer-cons-p
                :pred maybe-rational-integer-consp)

(defun supertype ()
  `((integerp . (rationalp maybe-integerp$inline))
    (rationalp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (rational-integer-cons-p . (maybe-rational-integer-consp))
    (rational-integer-alistp . nil)
    (maybe-integerp$inline . nil)
    (maybe-rational-integer-consp . nil)
    (rational-listp . nil)
    ))

(defun subtype ()
  `((rationalp . (integerp))
    (maybe-integerp$inline . (integerp))
    (integerp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (maybe-rational-integer-consp . (rational-integer-cons-p))
    (rational-integer-alistp . nil)
    (rational-integer-cons-p . nil)
    (rational-listp . nil)
    ))

(defthm integerp-implies-maybe-integerp$inline
  (implies (integerp x) (maybe-integerp$inline x)))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defthm rational-integer-cons-p-implies-maybe-rational-integer-consp
  (implies (rational-integer-cons-p x) (maybe-rational-integer-consp x)))

(defun supertype-thm ()
  `((,(make-type-tuple :type 'integerp :neighbour-type 'maybe-integerp$inline) .
     integerp-implies-maybe-integerp$inline)
    (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp) .
     integerp-implies-rationalp)
    (,(make-type-tuple :type 'rational-integer-cons-p
                       :neighbour-type 'maybe-rational-integer-consp) .
                       rational-integer-cons-p-implies-maybe-rational-integer-consp)))

(defthm maybe-integerp$inline-can-be-integerp
  (implies (and (maybe-integerp$inline x) x)
           (integerp x)))

(defthm maybe-rational-integer-consp-can-be-rational-integer-cons-p
  (implies (and (maybe-rational-integer-consp x) x)
           (rational-integer-cons-p x)))

(defun subtype-thm ()
  `((,(make-type-tuple :type 'maybe-integerp$inline :neighbour-type 'integerp) .
     maybe-integerp$inline-can-be-integerp)
    (,(make-type-tuple :type 'maybe-rational-integer-consp
                       :neighbour-type 'rational-integer-cons-p) .
                       maybe-rational-integer-consp-can-be-rational-integer-cons-p)))

(defthm return-of-assoc-equal
  (implies (and (rationalp y)
                (rational-integer-alistp x))
           (maybe-rational-integer-consp (assoc-equal y x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr-maybe
  (implies (maybe-rational-integer-consp x)
           (maybe-integerp$inline (cdr x)))
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
  (implies (and (rational-listp x) x)
           (rationalp (car x))))

(defthm return-of-cdr-rlistp
  (implies (rational-listp x)
           (rational-listp (cdr x))))

(defthm return-of-cons
  (implies (and (rationalp x)
                (rational-listp y))
           (and (rational-listp (cons x y))
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

(defthm return-of-rational-listp
  (booleanp (rational-listp x)))

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

(defun rational-list-cons (x y)
  (cons x y))

(defthm replace-of-car
  (implies (and (rational-listp x) x)
           (equal (car x) (rational-list-car x))))

(defthm replace-of-cons
  (equal (cons x y) (rational-list-cons x y)))

;; assoc-equal: rational-integer-alistp -> maybe-rational-integer-consp
;; cdr: maybe-rational-integer-consp -> maybe-integerp$inline &
;;      rational-integer-consp -> integerp
;; <: integerp integerp -> booleanp
;; binary-+: integerp integerp -> integerp
;; unary--: integerp -> integerp
(defun functions ()
  `((acons
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((integerp
                               . ,(make-arg-decl-next
                                   :next `((rational-integer-alistp
                                            . ,(make-arg-decl-done
                                                :r
                                                (make-return-spec
                                                 :formals '(x y z)
                                                 :return-type 'rational-integer-alistp
                                                 :returns-thm 'return-of-acons))))))))))))
    (assoc-equal
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((rational-integer-alistp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(y x)
                                       :return-type 'maybe-rational-integer-consp
                                       :returns-thm
                                       'return-of-assoc-equal)))))))))
    (car
     . ,(make-arg-decl-next
         :next `((rational-listp
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'rationalp
                          :returns-thm 'return-of-car-rlistp
                          :replace-thm 'replace-of-car))))))
    (cdr
     . ,(make-arg-decl-next
         :next `((maybe-rational-integer-consp
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'maybe-integerp$inline
                          :returns-thm 'return-of-cdr-maybe)))
                 (rational-integer-cons-p
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'integerp
                          :returns-thm 'return-of-cdr)))
                 (rational-listp
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'rational-listp
                          :returns-thm 'return-of-cdr-rlistp))))))
    (cons
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((rational-listp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'rational-listp
                                       :returns-thm
                                       'return-of-cons
                                       :replace-thm 'replace-of-cons)))))))))
    (<
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((rationalp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'booleanp
                                       :returns-thm 'return-of-<)))))))))
    (binary-+
     . ,(make-arg-decl-next
         :next `((integerp
                  . ,(make-arg-decl-next
                      :next `((integerp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'integerp
                                       :returns-thm
                                       'return-of-binary-+))))))
                 (rationalp
                  . ,(make-arg-decl-next
                      :next `((rationalp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'rationalp
                                       :returns-thm
                                       'return-of-binary-+-rationalp)))))))))
    (binary-*
     . ,(make-arg-decl-next
         :next `((integerp
                  . ,(make-arg-decl-next
                      :next `((integerp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'integerp
                                       :returns-thm
                                       'return-of-binary-*)))))))))
    (unary-- . ,(make-arg-decl-next
                 :next `((integerp . ,(make-arg-decl-done
                                       :r (make-return-spec
                                           :formals '(x)
                                           :return-type 'integerp
                                           :returns-thm
                                           'return-of-unary--)))
                         (rationalp . ,(make-arg-decl-done
                                        :r (make-return-spec
                                            :formals '(x)
                                            :return-type 'rationalp
                                            :returns-thm
                                            'return-of-unary---rationalp))))))
    (not . ,(make-arg-decl-next
             :next `((booleanp . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x)
                                       :return-type 'booleanp
                                       :returns-thm
                                       'return-of-not))))))
    (rational-integer-alistp . ,(make-arg-decl-next
                                 :next `((t . ,(make-arg-decl-done
                                                :r (make-return-spec
                                                    :formals '(x)
                                                    :return-type 'booleanp
                                                    :returns-thm
                                                    'return-of-rational-integer-alistp))))))
    (rational-listp . ,(make-arg-decl-next
                        :next `((t . ,(make-arg-decl-done
                                       :r (make-return-spec
                                           :formals '(x)
                                           :return-type 'booleanp
                                           :returns-thm
                                           'return-of-rational-list-p))))))
    (rationalp . ,(make-arg-decl-next
                   :next `((t . ,(make-arg-decl-done
                                  :r (make-return-spec
                                      :formals '(x)
                                      :return-type 'booleanp
                                      :returns-thm
                                      'return-of-rationalp))))))
    (integerp . ,(make-arg-decl-next
                  :next `((t . ,(make-arg-decl-done
                                 :r (make-return-spec
                                     :formals '(x)
                                     :return-type 'booleanp
                                     :returns-thm
                                     'return-of-integerp))))))
    ))

(defun options ()
  (b* ((supertype (supertype))
       (supertype-thm (supertype-thm))
       (subtype (subtype))
       (subtype-thm (subtype-thm))
       (functions (functions)))
    (make-type-options
     :supertype supertype
     :supertype-thm supertype-thm
     :subtype subtype
     :subtype-thm subtype-thm
     :functions functions
     :alist nil
     :aa-map nil)))

;; ------------------------------------------------------
;; test cases

(defun term0 ()
  '(if (integerp x)
       (not (< (binary-* x x) '0))
     't))

(defun term1 ()
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
  '(if (if (rational-integer-alistp al)
           (rationalp r1)
         'nil)
       ((lambda (x y)
          (if (assoc-equal y x)
              (< (binary-+ (cdr (assoc-equal y x))
                           (unary-- (cdr (assoc-equal y x))))
                 '2)
            'nil))
        al r1)
     't))

(defun term6 ()
  '(if (if (rational-listp l1)
           (if (integerp i1)
               l1
             'nil)
         'nil)
       (< (binary-+ (car (cons i1 l1))
                    (unary-- i1))
          '2)
     't))

(value-triple (type-judgement (term0) ''t (options) state))
(value-triple (type-judgement (term1) ''t (options) state))
(value-triple (type-judgement (term2) ''t (options) state))
(value-triple (type-judgement (term3) ''t (options) state))
(value-triple (type-judgement (term4) ''t (options) state))
(value-triple (type-judgement (term5) ''t (options) state))
(value-triple (type-judgement (term6) ''t (options) state))

;; ------------------------------------------------------

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term0)
                   :path-cond ''t
                   :judgements (type-judgement (term0) ''t (options) state))
  (options))
 )

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term1)
                   :path-cond ''t
                   :judgements (type-judgement (term1) ''t (options) state))
  (options))
 )

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term2)
                   :path-cond ''t
                   :judgements (type-judgement (term2) ''t (options) state))
  (options))
 )

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term3)
                   :path-cond ''t
                   :judgements (type-judgement (term3) ''t (options) state))
  (options))
 )

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term4)
                   :path-cond ''t
                   :judgements (type-judgement (term4) ''t (options) state))
  (options))
 )

(value-triple
 (good-typed-term-p
  (make-typed-term :term (term5)
                   :path-cond ''t
                   :judgements (type-judgement (term5) ''t (options) state))
  (options))
 )

;; ------------------------------------------------------

(value-triple
 (unify-type (make-typed-term :term (term0)
                              :path-cond ''t
                              :judgements (type-judgement (term0) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

(value-triple
 (unify-type (make-typed-term :term (term1)
                              :path-cond ''t
                              :judgements (type-judgement (term1) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

(value-triple
 (unify-type (make-typed-term :term (term2)
                              :path-cond ''t
                              :judgements (type-judgement (term2) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

(value-triple
 (unify-type (make-typed-term :term (term3)
                              :path-cond ''t
                              :judgements (type-judgement (term3) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

(value-triple
 (unify-type (make-typed-term :term (term4)
                              :path-cond ''t
                              :judgements (type-judgement (term4) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

(value-triple
 (unify-type (make-typed-term :term (term5)
                              :path-cond ''t
                              :judgements (type-judgement (term5) ''t (options)
                                                          state))
             ''t
             (options)
             state)
 )

;; ------------------------------------------------------------------
(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term0)
                               :path-cond ''t
                               :judgements (type-judgement (term0) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term1)
                               :path-cond ''t
                               :judgements (type-judgement (term1) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term2)
                               :path-cond ''t
                               :judgements (type-judgement (term2) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term3)
                               :path-cond ''t
                               :judgements (type-judgement (term3) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term4)
                               :path-cond ''t
                               :judgements (type-judgement (term4) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term5)
                               :path-cond ''t
                               :judgements (type-judgement (term5) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )

(value-triple
 (term-rectify
  (unify-type (make-typed-term :term (term6)
                               :path-cond ''t
                               :judgements (type-judgement (term6) ''t (options)
                                                           state))
              ''t
              (options)
              state)
  (options)
  state)
 )
