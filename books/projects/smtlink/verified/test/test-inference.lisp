(in-package "SMT")
(include-book "../type-inference-bottomup")
(include-book "../type-inference-topdown")
;; (include-book "term-rectify")
;; (include-book "term-projection")

(ld "test-type-options.lisp")

(set-state-ok t)

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
