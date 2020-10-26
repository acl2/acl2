;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 16th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "hint-please")
(include-book "hint-interface")
(include-book "extractor")
(include-book "type-theorems")
(include-book "basics")
(include-book "term-substitution")

(set-state-ok t)
;; Type inference takes the clause from the add-hyp-cp clause-processor and
;; apply type inference to the clause.
;; It produces a new clause that replace the clause with functions that are
;; typed.
;; This type inference is verified to be sound.

;; -----------------------------------------------------------------
;;       Define evaluators

(acl2::defevaluator-fast ev-infer ev-infer-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z)
                          (binary-+ x y))
                         :namedp t)

(acl2::def-ev-theoremp ev-infer)
(acl2::def-meta-extract ev-infer ev-infer-lst)
(acl2::def-unify ev-infer ev-infer-alist)

;; -----------------------------------------------------------------
;;                  some helper functions
(define type-list-to-alist ((type-lst pseudo-term-listp)
                            (fixinfo smt-fixtype-info-p))
  :returns (type-alist pseudo-term-alistp
                       :hints (("Goal" :in-theory (enable type-decl-p))))
  (b* ((type-lst (pseudo-term-list-fix type-lst))
       ((unless (consp type-lst)) nil)
       ((cons first rest) type-lst)
       ((unless (type-decl-p first fixinfo))
        (er hard? 'type-inference=>type-list-to-alist
            "Need a type-decl-p: ~q0" first))
       ((list & term) first))
    (acons term first
           (type-list-to-alist rest fixinfo))))

(define type-alist-to-type-list ((type-alst pseudo-term-alistp))
  :measure (len (pseudo-term-alist-fix type-alst))
  :returns (type-lst pseudo-term-listp)
  (b* ((type-alst (pseudo-term-alist-fix type-alst))
       ((unless (consp type-alst)) nil)
       ((cons first rest) type-alst))
    (cons (cdr first)
          (type-alist-to-type-list rest))))

(define extend-var-alist-for-lambda ((var-alst pseudo-term-alistp)
                                     (formals symbol-listp)
                                     (types symbol-listp))
  :returns (type-alst pseudo-term-alistp)
  :measure (len (symbol-list-fix formals))
  (b* ((var-alst (pseudo-term-alist-fix var-alst))
       (formals (symbol-list-fix formals))
       (types (symbol-list-fix types))
       ((unless (and (consp formals) (consp types))) var-alst)
       ((cons first-formal rest-formals) formals)
       ((cons first-type rest-types) types))
    (acons first-formal
           `(,first-type ,first-formal)
           (extend-var-alist-for-lambda var-alst rest-formals rest-types))))

(skip-proofs
 (defthm correctness-of-smt-extract-0
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (not
                  (ev-infer
                   (conjoin
                    (mv-nth 0 (smt-extract (disjoin cl) fixinfo)))
                   a)))
            (ev-infer (disjoin cl) a))))

(skip-proofs
 (defthm correctness-of-smt-extract-1
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-infer
                  (mv-nth 1 (smt-extract (disjoin cl) fixinfo))
                  a))
            (ev-infer (disjoin cl) a))))

(skip-proofs
 (defthm correctness-of-type-list-to-alist
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp type-lst)
                 (alistp a))
            (equal (ev-infer-lst
                    (type-alist-to-type-list
                     (type-list-to-alist type-lst fixinfo))
                    a)
                   (ev-infer-lst type-lst a)))))

(skip-proofs
 (defthm correctness-of-smt-extract
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (not
                  (ev-infer
                   (conjoin
                    (type-alist-to-type-list
                     (type-list-to-alist
                      (mv-nth 0 (smt-extract (disjoin cl) fixinfo))
                      fixinfo)))
                   a)))
            (ev-infer (disjoin cl) a))))

;; -----------------------------------------------------------------

(defprod type-info
  ((typeterm pseudo-termp)
   (augterm pseudo-termp)))

(defalist pseudo-term-info-alist
  :key-type pseudo-term
  :val-type type-info
  :pred pseudo-term-info-alistp
  :true-listp t)

(local
 (defthm type-info-of-assoc-equal-of-pseudo-term-info-alistp
   (implies (and (pseudo-term-info-alistp type-alst)
                 (assoc-equal term type-alst))
            (type-info-p (cdr (assoc-equal term type-alst)))))
 )

(define typing-rules ()
  `((equal . equal-theorem)
    (< . <-theorem)

    ((binary-+ integerp integerp) . binary-+-of-integerp)
    ((binary-+ rationalp integerp) . binary-+-of-rational-integerp)
    ((binary-+ integerp rationalp) . binary-+-of-integer-rationalp)
    ((binary-+ rationalp rationalp) . binary-+-of-rationalp)

    ((unary-- integerp) . unary---of-integerp)
    ((unary-- rationalp) . unary---of-rationalp)

    ((binary-* integerp integerp) . binary-*-of-integerp)
    ((binary-* rationalp integerp) . binary-*-of-rational-integerp)
    ((binary-* integerp rationalp) . binary-*-of-integer-rationalp)
    ((binary-* rationalp rationalp) . binary-*-of-rationalp)

    ((unary-/ integerp) . unary-/-of-integerp)
    ((unary-/ rationalp) . unary-/-of-rationalp)

    (not . not-theorem)
    (if . if-theorem)
    (implies . implies-theorem)
    ))

;; TODO
(define list-type? ((x symbolp))
  :returns (ok booleanp)
  (or (equal x 'integer-listp) (equal x 'rational-listp)))

(define alist-type? ((x symbolp))
  :returns (ok booleanp)
  (or (equal x 'integer-integer-alistp)
      (equal x 'integer-rational-alistp)
      (equal x 'rational-integer-alistp)
      (equal x 'rational-rational-alistp)
      ))

(define maybe-consp-type? ((x symbolp))
  :returns (ok booleanp)
  (or (equal x 'maybe-integer-integer-consp)
      (equal x 'maybe-integer-rational-consp)
      (equal x 'maybe-rational-integer-consp)
      (equal x 'maybe-rational-rational-consp)))

(define option-type? ((x symbolp))
  :returns (ok booleanp)
  (or (equal x 'maybe-integerp)
      (equal x 'maybe-rationalp)
      (equal x 'maybe-integer-integer-consp)
      (equal x 'maybe-integer-rational-consp)
      (equal x 'maybe-rational-integer-consp)
      (equal x 'maybe-rational-rational-consp)))

(define cons-type? ((x symbolp))
  :returns (ok booleanp)
  (or (equal x 'integer-integer-consp)
      (equal x 'integer-rational-consp)
      (equal x 'rational-integer-consp)
      (equal x 'rational-rational-consp)))

(define kind-fn? ((x symbolp))
  :returns (ok booleanp)
  (b* ((str (symbol-name (symbol-fix x)))
       ((if (< (length str) 5)) nil))
    (not (null (search "-KIND" str)))))

;;
(define expected-types ()
  `((equal . (t t))
    (< . (t t))
    (binary-+ . (t t))
    (unary-- . (t))
    (binary-* . (t t))
    (unary-/ . (t))
    (not . (booleanp))
    (if . (booleanp t t))
    (implies . (booleanp booleanp))
    (car . (t))
    (cdr . (t))
    (acons . (t t t))
    (assoc-equal . (t t))
    )
  )

;; Very minimum subtyping
(define subtype-of ((type1 symbolp) (type2 symbolp))
  :returns (yes booleanp)
  (b* ((type1 (symbol-fix type1))
       (type2 (symbol-fix type2)))
    (cond ((equal type2 t) t)
          ((equal type1 type2) t)
          ((and (equal type1 'null) (equal type2 'booleanp)) t)
          ((and (equal type1 'null) (list-type? type2)) t)
          ((and (equal type1 'null) (alist-type? type2)) t)
          ((and (equal type1 'null) (option-type? type2)) t)
          ((and (equal type1 'integerp) (equal type2 'rationalp)) t)
          ((and (equal type1 'integerp) (equal type2 'realp)) t)
          ((and (equal type1 'rationalp) (equal type2 'realp)) t)
          ((and (equal type1 'integerp) (equal type2 'real/rationalp)) t)
          ((and (equal type1 'rationalp) (equal type2 'real/rationalp)) t)
          ((and (equal type1 'real/rationalp) (equal type2 'realp) ) t)
          (t nil))))

(define lu-bound ((type1 symbolp) (type2 symbolp))
  :returns (bound symbolp)
  (b* ((type1 (symbol-fix type1))
       (type2 (symbol-fix type2))
       ((if (subtype-of type1 type2))
        type2)
       ((if (subtype-of type2 type1))
        type1))
    (er hard? 'lu-bound
        "Type ~p0 and type ~p1 have no upper bound.~%" type1 type2)))

(define lu-bound-list ((type-lst symbol-listp))
  :returns (bound symbolp)
  :measure (len type-lst)
  (b* ((type-lst (symbol-list-fix type-lst))
       ((unless (consp type-lst))
        (er hard? 'type-inference
            "I don't know what to return for the least upper bound of no
             types.~%"))
       ((unless (consp (cdr type-lst)))
        (car type-lst)))
    (lu-bound (car type-lst) (lu-bound-list (cdr type-lst)))))

(define update-with-expected ((term pseudo-termp)
                              (type-alst pseudo-term-info-alistp)
                              (inferred symbolp)
                              (expected symbolp))
  :returns (new-alst pseudo-term-info-alistp)
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-info-alist-fix type-alst))
       (inferred (symbol-fix inferred))
       (expected (symbol-fix expected))
       ((unless (subtype-of inferred expected))
        (er hard? 'type-inference=>update-with-expected
            "Expected type ~p0 but ~p1 is of type ~p2~%"
            expected term inferred)))
    (acons term (make-type-info
                 :typeterm `(,inferred ,term)
                 :augterm term)
           type-alst)))

;; What constants are recognized
;; 1 2 3 ... integerp
;; 1/1 1/2 ... rationalp
;; 'test ... symbolp
;; nil t ... booleanp
;; These ones are not supported yet
;; '(1 2 3) ... integer-listp
;; '(1/1 1/2 ...) ... rational-listp
;; '(a b c) ... symbol-listp
;; '(t nil nil ...) ... boolean-listp
(define infer-constant ((term pseudo-termp)
                        (type-alst pseudo-term-info-alistp)
                        (conj-acc pseudo-termp)
                        (expected-type symbolp))
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (mv (new-term pseudo-termp)
               (new-conj pseudo-termp)
               (new-type-alst pseudo-term-info-alistp)
               (new-type symbolp))
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-info-alist-fix type-alst))
       (conj-acc (pseudo-term-fix conj-acc))
       ((if (acl2::variablep term)) (mv term conj-acc type-alst nil))
       ((unless (acl2::fquotep term)) (mv term conj-acc type-alst nil))
       (const (cadr term)))
    (cond ((integerp const)
           (mv term
               `(if (integerp ',const) ,conj-acc 'nil)
               (update-with-expected term type-alst 'integerp expected-type)
               'integerp))
          ((rationalp const)
           (mv term
               `(if (rationalp ',const) ,conj-acc 'nil)
               (update-with-expected term type-alst 'rationalp expected-type)
               'rationalp))
          ((null const)
           (mv term
               `(if (null ',const) ,conj-acc 'nil)
               (update-with-expected term type-alst 'null expected-type)
               'null))
          ((booleanp const)
           (mv term
               `(if (booleanp ',const) ,conj-acc 'nil)
               (update-with-expected term type-alst 'booleanp expected-type)
               'booleanp))
          ((symbolp const)
           (mv term
               `(if (symbolp ',const) ,conj-acc 'nil)
               (update-with-expected term type-alst 'symbolp expected-type)
               'symbolp))
          (t
           (mv (er hard? 'type-inference=>infer-constant "Type inference for ~
                constant term ~p0 is not supported yet. ~%" term)
               nil nil nil)))))

(define basic-expected ((fn symbolp))
  :returns (expected symbol-listp)
  (cdr (assoc-equal fn (expected-types))))

(define generate-expected ((len natp))
  :returns (expected boolean-listp)
  (if (zp len) nil (cons 't (generate-expected (1- len)))))

(define basic-fns ()
  '(equal < binary-+ unary-- binary-* unary-/ not if implies car cdr acons assoc-equal))

(define numerical-types ()
  '(integerp rationalp realp real/rationalp))

(define basic-fn-p ((fn symbolp))
  (member-equal fn (basic-fns)))

(define numerical-type-p ((tp symbolp))
  :returns (ok booleanp)
  (not (equal (member-equal tp (numerical-types)) nil)))

(define numerical-type-listp ((fn-lst symbol-listp))
  :returns (ok booleanp)
  :measure (len (symbol-list-fix fn-lst))
  (b* ((fn-lst (symbol-list-fix fn-lst))
       ((unless (consp fn-lst)) t)
       ((cons first rest) fn-lst))
    (and (numerical-type-p first)
         (numerical-type-listp rest))))

(defoption maybe-nat natp
  :pred maybe-natp)

(define get-type ((term pseudo-termp)
                  (type-alst pseudo-term-alistp))
  :returns (type symbolp)
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-alist-fix type-alst))
       (the-item (assoc-equal term type-alst))
       ((unless the-item)
        (er hard? 'type-inference=>get-type
            "The term hasn't been typed yet: ~q0" term))
       (type-term (cdr the-item))
       ((unless (and (consp type-term) (symbolp (car type-term))))
        (er hard? 'type-inference=>get-type
            "The typed term is not a type predicate: ~q0" type-term)))
    (car type-term)))

(define get-type-list ((term-lst pseudo-term-listp)
                       (type-alst pseudo-term-alistp))
  :returns (type-list symbol-listp)
  :measure (len (pseudo-term-list-fix term-lst))
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       ((unless (consp term-lst)) nil)
       ((cons first rest) term-lst)
       (first-type (get-type first type-alst))
       (rest-types (get-type-list rest type-alst)))
    (cons first-type rest-types))
  ///
  (more-returns
   (type-list (true-listp type-list)
              :name true-listp-of-type-list-of-get-type-list)))

(define get-type-term ((term pseudo-termp)
                       (type-alst pseudo-term-alistp))
  :returns (type pseudo-termp
                 :hints (("Goal" :in-theory (enable pseudo-term-alist-fix))))
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-alist-fix type-alst))
       (the-item (assoc-equal term type-alst))
       ((unless the-item)
        (er hard? 'type-inference=>get-type
            "The term hasn't been typed yet: ~q0" term)))
    (cdr the-item)))

(define get-type-term-list ((term-lst pseudo-term-listp)
                            (type-alst pseudo-term-alistp))
  :returns (type-list pseudo-term-listp)
  :measure (len (pseudo-term-list-fix term-lst))
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       ((unless (consp term-lst)) nil)
       ((cons first rest) term-lst)
       (first-type (get-type-term first type-alst))
       (rest-types (get-type-term-list rest type-alst)))
    (cons first-type rest-types))
  ///
  (more-returns
   (type-list (true-listp type-list)
              :name true-listp-of-type-list-of-get-type-term-list)))

(define add-suffix ((sym symbolp)
                    (suffix stringp))
  :returns (new-sym symbolp)
  (b* ((sym (symbol-fix sym))
       (sym-str (symbol-name sym))
       (new-str (concatenate 'string sym-str suffix)))
    (intern-in-package-of-symbol new-str sym)))

(define remove-suffix ((sym symbolp) (suffix stringp))
  :returns (new-sym symbolp)
  (b* ((sym (symbol-fix sym))
       (sym-str (symbol-name sym))
       ((unless (>= (length sym-str)
                    7))
        sym)
       (pos (str::search suffix sym-str))
       ((unless (and (rationalp pos)
                     (>= pos 0)
                     (<= pos (length sym-str))))
        sym))
    (intern-in-package-of-symbol
     (str::subseq sym-str 0 pos)
     sym)))

(verify-termination std::defguts-p)
(verify-termination std::defguts)
(verify-guards std::defguts)
(verify-termination std::defguts->raw-formals$inline)
(verify-guards std::defguts->raw-formals$inline)
(verify-termination std::defguts->returnspecs$inline)
(verify-guards std::defguts->returnspecs$inline)
(verify-termination std::returnspec-p)
(verify-termination std::returnspec->return-type$inline)
(verify-guards std::returnspec->return-type$inline)

(define get-define-guts-alist ((world plist-worldp))
  :returns (guts alistp)
  (b* ((tb (table-alist 'define world))
       ((unless (alistp tb))
        (prog2$ (er hard? 'type-inference=>get-define-guts-alist
                    "(table-alist 'define world) returned something that's not
                    an alist.~%")
                (std::make-defguts)))
       (guts-alist (cdr (assoc 'std::guts-alist tb)))
       ((unless (alistp guts-alist))
        (prog2$ (er hard? 'type-inference=>get-define-guts-alist
                    "~p0 is not a alistp.~%")
                (std::make-defguts))))
    guts-alist))

(define get-guards ((fn symbolp)
                    state)
  :returns (guards symbol-listp)
  :guard-hints
  (("Goal"
    :in-theory (disable consp-of-pseudo-lambdap
                        symbol-listp
                        assoc-equal
                        default-car
                        std::defguts-p
                        pseudo-termp)))
  (b* ((fn (remove-suffix fn "$INLINE"))
       (gut (assoc-equal fn (get-define-guts-alist (w state))))
       ((unless (and (consp gut) (std::defguts-p (cdr gut))))
        (er hard? 'type-inference=>get-guards
            "Can't find function ~p0 in the std::defguts table.~%" fn))
       ((unless (acl2::all->=-len (std::defguts->raw-formals (cdr gut)) 2))
        (er hard? 'type-inference=>get-guards
            "....~%" fn))
       (guards (strip-cadrs (std::defguts->raw-formals (cdr gut))))
       ((unless (symbol-listp guards))
        (er hard? 'type-inference=>get-guards
            "Guards of ~p0 is not a list of symbols ~p1~%" fn guards)))
    guards))

(define get-return ((fn symbolp)
                    (fixinfo smt-fixtype-info-p)
                    state)
  :returns (ret symbolp
                :hints
                (("Goal"
                  :in-theory (disable consp-of-pseudo-lambdap
                                      symbol-listp
                                      fgetprop
                                      pseudo-termp))))
  :guard-hints
  (("Goal"
    :in-theory (disable consp-of-pseudo-lambdap
                        symbol-listp
                        assoc-equal
                        default-car
                        std::defguts-p
                        pseudo-termp)))
  (b* ((fn (remove-suffix fn "$INLINE"))
       ((if (kind-fn? fn)) 'symbolp)
       (gut (assoc-equal fn (get-define-guts-alist (w state))))
       ((unless (and (consp gut) (std::defguts-p (cdr gut))))
        (er hard? 'type-inference=>get-return
            "Can't find function ~p0 in the std::defguts table.~%" fn))
       (returnspecs (std::defguts->returnspecs (cdr gut)))
       ((unless (and (consp returnspecs) (std::returnspec-p (car returnspecs))
                     (null (cdr returnspecs))))
        (er hard? 'type-inference=>get-return
            "Currently only functions that returns one argument is supported
                    ~p0~%" fn))
       (returnspec (std::returnspec->return-type (car returnspecs)))
       ((unless (and (pseudo-termp returnspec) (type-decl-p returnspec fixinfo)))
        (er hard? 'type-inference=>get-return
            "Return spec for ~p0 is not a type-decl-p ~p1.~%" fn returnspec)))
    (car returnspec)))

(define get-expected-types ((fn symbolp)
                            (state))
  :returns (expected-types symbol-listp)
  (b* ((fn (symbol-fix fn))
       ((if (basic-fn-p fn)) (basic-expected fn)))
    (get-guards fn state)))

(define calculate-bound ((bound pseudo-termp))
  `((bound (lu-bound-list ,bound))
    ((unless bound)
     (er hard? 'type-inference=>make-judgement
         "Type inference failed. Can't calculate ~
          the least upper bound of the types of arguments to: ~
          ~%~p0 : ~p1~%"
         `(,fn ,@actuals) ,bound))))

(define check-numerical ()
  `(((unless (numerical-type-listp types))
     (er hard? 'type-inference=>make-judgement
         "Inputs to ~p0 are required to be numerical
         types, but ~p1 are of typespec-check ~p2~%"
         `(,fn ,@actuals) actuals types))))

(define check-nargs ((nargs natp))
  `(((unless (equal (len actuals) ,nargs))
     (er hard? 'type-inference=>make-judgement
         "Number of arguments is violated. ~p0 takes ~p1 arguments but is fed
                     with ~p2.~%"
         `(,fn ,@actuals) ,nargs (len actuals)))))

(define judgement-fn ((nargs maybe-natp)
                      (get-type booleanp)
                      (bound pseudo-termp)
                      (numerical booleanp))
  (b* ((nargs (maybe-nat-fix nargs))
       (nargs-code (if nargs (check-nargs nargs) nil))
       (type-code (if get-type
                      '((types actuals-types))
                    nil))
       (numerical-code (if numerical (check-numerical) nil))
       (bound-code (if bound (calculate-bound bound) nil)))
    `(,@nargs-code
      ,@type-code
      ,@numerical-code
      ,@bound-code)))

(defmacro judgement (&key (nargs 'nil) (get-type 't)
                          (bound 'nil) (numerical 'nil) (returned 'nil))
  `(b* ,(judgement-fn nargs get-type bound numerical)
     ,returned))

;; TODO: I will change this function to extract the name of the elt-type from a
;; theorem instead of assuming the name convention later.
;; Probably use a table of user defined types from the smtlink hint.
(define elt-type-table ()
  '((integerp . integer-listp)
    (rationalp . rational-listp)))

(define list-type-table ()
  '((integer-listp . integerp)
    (rational-listp . rationalp)))

(define elt-type-of-list-type ((x symbolp))
  :returns (elt-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (list-type-table)))))

(define list-type-of-elt-type ((x symbolp))
  :returns (list-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (elt-type-table)))))

(define key-val-type-table ()
  '(((integerp integerp) . integer-integer-alistp)
    ((integerp rationalp) . integer-rational-alistp)
    ((rationalp integerp) . rational-integer-alistp)
    ((rationalp rationalp) . rational-rational-alistp)))

(define alist-type-of-key-table ()
  '((integer-integer-alistp . integerp)
    (integer-rational-alistp . integerp)
    (rational-integer-alistp . rationalp)
    (rational-rational-alistp . rationalp)))

(define alist-type-of-val-table ()
  '((integer-integer-alistp . integerp)
    (integer-rational-alistp . rationalp)
    (rational-integer-alistp . integerp)
    (rational-rational-alistp . rationalp)))

(define key-type-of-alist-type ((x symbolp))
  :returns (key-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (alist-type-of-key-table)))))

(define val-type-of-alist-type ((x symbolp))
  :returns (val-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (alist-type-of-val-table)))))

(define alist-type-of-key-val-type ((x symbol-listp))
  :returns (list-type symbolp)
  (b* ((x (symbol-list-fix x))
       ((unless (equal (len x) 2))
        (er hard? 'type-inference=>alist-type-of-key-val-type
            "x is not a symbol-list of length 2.~%"))
       ((if (or (equal (car x) 't) (equal (cadr x) 't))) 't))
    (cdr (assoc-equal x (key-val-type-table)))))

(define key-type-of-cons-table ()
  '((integer-integer-consp . integerp)
    (integer-rational-consp . integerp)
    (rational-integer-consp . rationalp)
    (rational-rational-consp . rationalp)))

(define key-type-of-cons-type ((x symbolp))
  :returns (key-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (key-type-of-cons-table)))))

(define cons-type-of-alist-table ()
  '((integer-integer-alistp . integer-integer-consp)
    (integer-rational-alistp . integer-rational-consp)
    (rational-integer-alistp . rational-integer-consp)
    (rational-rational-alistp . rational-rational-consp)))

(define cons-type-of-alist-type ((x symbolp))
  :returns (cons-type symbolp)
  (if (equal x 't)
      't
    (cdr (assoc-equal (symbol-fix x) (cons-type-of-alist-table)))))

(define maybe-of-cons-table ((x symbolp))
  :returns (maybe-type symbolp)
  (cdr (assoc-equal (symbol-fix x)
                    '((integer-integer-consp . maybe-integer-integer-consp)
                      (integer-rational-consp . maybe-integer-rational-consp)
                      (rational-integer-consp . maybe-rational-integer-consp)
                      (rational-rational-consp .
                                               maybe-rational-rational-consp)))))

;; special versions of cdr for consp
;; (cdr x) =>
;; (if x
;;     (maybe-integer-some (cdr (maybe-rational-integer-some-> x)))
;;   (maybe-integer-none))
(define cdr-of-maybe-consp ((x symbolp))
  :returns (maybe-type symbolp)
  (cdr (assoc-equal (symbol-fix x)
                    '((maybe-integer-integer-consp . maybe-integer-integer-cdr)
                      (maybe-integer-rational-consp . maybe-integer-rational-cdr)
                      (maybe-rational-integer-consp . maybe-rational-integer-cdr)
                      (maybe-rational-rational-consp .
                                                     maybe-rational-rational-cdr)))))

(define cdr-type-of-consp ((x symbolp))
  :returns (maybe-type symbolp)
  (cdr (assoc-equal (symbol-fix x)
                    '((integer-integer-consp . integerp)
                      (integer-rational-consp . rationalp)
                      (rational-integer-consp . integerp)
                      (rational-rational-consp . rationalp)))))

(define return-type-cdr-of-maybe-consp ((x symbolp))
  :returns (maybe-type symbolp)
  (cdr (assoc-equal (symbol-fix x)
                    '((maybe-integer-integer-cdr . maybe-integerp)
                      (maybe-integer-rational-cdr . maybe-rationalp)
                      (maybe-rational-integer-cdr . maybe-integerp)
                      (maybe-rational-rational-cdr . maybe-rationalp)))))

(define get-val-fn ((x symbolp))
  :returns (val-fn symbolp)
  (cdr (assoc-equal (symbol-fix x)
                    '((maybe-integerp . maybe-integer-some->val$inline)
                      (maybe-rationalp . maybe-rational-some->val$inline)
                      (maybe-integer-integer-consp . maybe-integer-integer-consp-some->val$inline)
                      (maybe-integer-rational-consp . maybe-integer-rational-consp-some->val$inline)
                      (maybe-rational-integer-consp . maybe-rational-integer-consp-some->val$inline)
                      (maybe-rational-rational-consp . maybe-rational-rational-consp-some->val$inline)))))

(define make-judgement ((fn symbolp)
                        (actuals pseudo-term-listp)
                        (actuals-types symbol-listp)
                        (fixinfo smt-fixtype-info-p)
                        state)
  :guard (not (equal fn 'quote))
  :returns (return-type symbolp)
  (b* ((fn (symbol-fix fn))
       (actuals-types (symbol-list-fix actuals-types))
       ((unless (mbt (not (equal fn 'quote)))) nil))
    (case-match fn
      ('equal (judgement :nargs 2 :bound types :numerical nil :returned 'booleanp))
      ('< (judgement :nargs 2 :bound types :numerical t :returned 'booleanp))
      ('binary-+ (judgement :nargs 2 :bound types :numerical t :returned bound))
      ('unary-- (judgement :nargs 1 :bound nil :numerical t :returned (car types)))
      ('binary-* (judgement :nargs 2 :bound types :numerical t :returned bound))
      ('unary-/ (judgement :nargs 1 :bound types :numerical t :returned bound))
      ('not (judgement :nargs 1 :get-type nil
                       :bound nil :numerical nil :returned 'booleanp))
      ;; ('if (judgement :nargs 3 :bound (cdr types) :numerical nil
      ;;                 :returned bound))
      ('implies (judgement :nargs 2 :get-type nil :bound nil :numerical nil
                           :returned 'booleanp))
      ('car (judgement :nargs 1 :bound nil :numerical nil
                       :returned (elt-type-of-list-type (car types))))
      (& (get-return fn fixinfo state))
      )))

(define cut-bound ((expected-type symbolp)
                   (type symbolp))
  :returns (bound symbolp)
  (b* ((type (symbol-fix type))
       (expected-type (symbol-fix expected-type))
       ((if (equal expected-type t)) type))
    (lu-bound expected-type type)))

(local
 (defthm pseudo-termp-of-lambda-conjunction
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-conj)
                 (pseudo-term-listp actuals)
                 (pseudo-termp actuals-conj)
                 (equal (len formals) (len actuals)))
            (pseudo-termp
             `(if ((lambda ,formals ,body-conj) ,@actuals)
                  ,actuals-conj
                'nil))))
 )

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-conj)
                 (pseudo-term-listp actuals)
                 (pseudo-termp actuals-conj)
                 (equal (len formals) (len actuals)))
            (pseudo-termp `((lambda ,formals ,body-conj) ,@actuals))))
 )

(local
 (defthm pseudo-termp-of-var-alst-item
   (implies (and (pseudo-term-alistp var-alst)
                 (consp (cdr (assoc-equal term var-alst)))
                 (pseudo-termp conj-acc))
            (pseudo-termp
             `(if ,(cdr (assoc-equal term var-alst)) ,conj-acc 'nil))))
 )

(defines infer-type
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal" :in-theory (disable symbolp-of-fn-call-of-pseudo-termp
                                      pseudo-term-listp-of-symbol-listp
                                      acl2::pseudo-termp-opener
                                      acl2::symbol-listp-when-not-consp
                                      acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                                      pseudo-term-alist-fix-when-pseudo-term-alistp
                                      assoc-equal
                                      default-car
                                      default-cdr
                                      consp-of-cdr-of-pseudo-lambdap
                                      acl2::true-listp-of-car-when-true-list-listp
                                      true-list-listp
                                      acl2::pseudo-lambda-listp-of-cdr-when-pseudo-lambda-listp
                                      acl2::symbol-listp-cdr-assoc-equal
                                      acl2::symbol-list-listp
                                      nil-of-assoc-equal-of-pseudo-term-alistp
                                      acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                      pseudo-term-alistp-when-not-consp
                                      consp-car-of-pseudo-term-alist-fix
                                      pseudo-termp-of-car-when-member-equal-of-pseudo-term-alistp
                                      member-equal
                                      pseudo-term-listp
                                      acl2::rational-listp-of-cdr-when-rational-listp
                                      acl2::integer-listp-of-cdr-when-integer-listp
                                      (:rewrite symbol-listp-of-car-when-symbol-list-listp)
                                      (:rewrite symbolp-of-caar-when-symbol-symbol-alistp)
                                      symbolp-of-caar-when-smtlink-hint-alist-p
                                      acl2::symbolp-of-caar-when-symbol-symbol-alistp
                                      symbolp-of-caar-when-symbol-prod-alist-p
                                      symbolp-of-caar-when-symbol-hint-pair-alist-p
                                      symbolp-of-caar-when-smt-fixtype-info-p
                                      acl2::rationalp-of-car-when-rational-listp
                                      acl2::integerp-of-car-when-integer-listp
                                      (:definition integer-listp)
                                      (:definition rational-listp)
                                      )))
  :returns-hints (("Goal"
                   :in-theory (disable (:definition len)
                                       type-decl-p-definition
                                       consp-when-member-equal-of-pseudo-term-info-alistp
                                       pseudo-termp-of-car-when-member-equal-of-pseudo-term-info-alistp
                                       symbolp-of-fn-call-of-pseudo-termp
                                       acl2::pseudo-lambdap-when-member-equal-of-pseudo-lambda-listp
                                       pseudo-term-listp-of-symbol-listp
                                       acl2::pseudo-termp-opener
                                       acl2::symbol-listp-when-not-consp
                                       acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                                       pseudo-term-alist-fix-when-pseudo-term-alistp
                                       assoc-equal
                                       default-car
                                       default-cdr
                                       consp-of-cdr-of-pseudo-lambdap
                                       acl2::true-listp-of-car-when-true-list-listp
                                       true-list-listp
                                       acl2::pseudo-lambda-listp-of-cdr-when-pseudo-lambda-listp
                                       acl2::symbol-listp-cdr-assoc-equal
                                       acl2::symbol-list-listp
                                       nil-of-assoc-equal-of-pseudo-term-alistp
                                       acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                       pseudo-term-alistp-when-not-consp
                                       consp-car-of-pseudo-term-alist-fix
                                       pseudo-termp-of-car-when-member-equal-of-pseudo-term-alistp
                                       member-equal
                                       pseudo-term-listp
                                       acl2::rational-listp-of-cdr-when-rational-listp
                                       acl2::integer-listp-of-cdr-when-integer-listp
                                       (:rewrite symbol-listp-of-car-when-symbol-list-listp)
                                       (:rewrite symbolp-of-caar-when-symbol-symbol-alistp)
                                       symbolp-of-caar-when-smtlink-hint-alist-p
                                       acl2::symbolp-of-caar-when-symbol-symbol-alistp
                                       symbolp-of-caar-when-symbol-prod-alist-p
                                       symbolp-of-caar-when-symbol-hint-pair-alist-p
                                       symbolp-of-caar-when-smt-fixtype-info-p
                                       pseudo-termp
                                       (:executable-counterpart symbolp)
                                       acl2::rationalp-of-car-when-rational-listp
                                       acl2::integerp-of-car-when-integer-listp
                                       (:definition integer-listp)
                                       (:definition rational-listp)
                                       )))

  ;; Type Inference for Cons
  ;; This is an algorithm that first goes top down passing along the type
  ;; information inferred from the element of car to the cdr. It tries
  ;; calculating the upper bound of the passed information with the inferred
  ;; information. It then goes bottom up passing along the upper bound as the
  ;; inferred type for the whole list.
  (define infer-cons ((fn symbolp)
                      (actuals pseudo-term-listp)
                      (var-alst pseudo-term-alistp)
                      (type-alst pseudo-term-info-alistp)
                      (conj-acc pseudo-termp)
                      (expected-type symbolp)
                      (fixinfo smt-fixtype-info-p)
                      (clock natp)
                      state)
    :guard (equal fn 'cons)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (equal fn 'cons)))
          (mv nil conj-acc type-alst nil))
         (expected-elt-type (elt-type-of-list-type expected-type))
         ((mv car-term car-conj car-type-alst car-type)
          (infer-type (car actuals) var-alst type-alst conj-acc t fixinfo clock
                      state))
         ;; Taking the upper bound of t with car-type will produce t, which is
         ;; not what we want. Therefore we are making a case for this special
         ;; occasion.
         (bound (cut-bound expected-elt-type car-type))
         (expected-lst-type (list-type-of-elt-type bound))
         ((mv cadr-term cadr-conj cadr-type-alst cadr-type)
          (infer-type (cadr actuals) var-alst car-type-alst car-conj
                      expected-lst-type fixinfo clock state))
         ;; If cadr is nil of type 'null, then the type for the list should be
         ;; the expected type, otherwise use cadr-type
         (return-type (if (equal cadr-type 'null) expected-lst-type cadr-type))
         (elt-type (elt-type-of-list-type return-type))
         ((unless (subtype-of car-type elt-type))
          (mv (er hard? 'type-inference=>infer-fncall-cons
                  "Can't cons a ~p0 onto a ~p1 in term ~p2~%"
                  car-type return-type `(,fn ,@actuals))
              nil nil nil))
         (new-term `(,fn ,car-term ,cadr-term)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,cadr-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 cadr-type-alst)
          return-type)))

  (define infer-acons ((fn symbolp)
                       (actuals pseudo-term-listp)
                       (var-alst pseudo-term-alistp)
                       (type-alst pseudo-term-info-alistp)
                       (conj-acc pseudo-termp)
                       (expected-type symbolp)
                       (fixinfo smt-fixtype-info-p)
                       (clock natp)
                       state)
    :guard (equal fn 'acons)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (equal fn 'acons)))
          (mv nil conj-acc type-alst nil))
         (expected-key-type (key-type-of-alist-type expected-type))
         (expected-val-type (val-type-of-alist-type expected-type))
         ((mv key-term key-conj key-type-alst key-type)
          (infer-type (car actuals) var-alst type-alst conj-acc t fixinfo clock
                      state))
         (key-bound (cut-bound expected-key-type key-type))
         ((mv val-term val-conj val-type-alst val-type)
          (infer-type (cadr actuals) var-alst key-type-alst key-conj t fixinfo
                      clock state))
         (val-bound (cut-bound expected-val-type val-type))
         (expected-alst-type
          (alist-type-of-key-val-type `(,key-bound ,val-bound)))
         ((mv alst-term alst-conj alst-type-alst alst-type)
          (infer-type (caddr actuals) var-alst val-type-alst val-conj
                      expected-alst-type fixinfo clock state))
         (return-type
          (if (equal alst-type 'null) expected-alst-type alst-type))
         (whole-key-type (key-type-of-alist-type return-type))
         (whole-val-type (val-type-of-alist-type return-type))
         ((unless (and (subtype-of key-type whole-key-type)
                       (subtype-of val-type whole-val-type)))
          (mv (er hard? 'type-inference=>infer-fncall-acons
                  "Can't acons a ~p0 with a ~p1 onto a ~p2 in term ~p3~%"
                  key-type val-type return-type `(,fn ,@actuals))
              nil nil nil))
         (new-term `(,fn ,key-term ,val-term ,alst-term)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,alst-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 alst-type-alst)
          return-type)))

  (define infer-assoc-equal ((fn symbolp)
                             (actuals pseudo-term-listp)
                             (var-alst pseudo-term-alistp)
                             (type-alst pseudo-term-info-alistp)
                             (conj-acc pseudo-termp)
                             (expected-type symbolp)
                             (fixinfo smt-fixtype-info-p)
                             (clock natp)
                             state)
    :guard (equal fn 'assoc-equal)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    :irrelevant-formals-ok t
    :ignore-ok t
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (equal fn 'assoc-equal)))
          (mv nil conj-acc type-alst nil))
         ((mv key-term key-conj key-type-alst key-type)
          (infer-type (car actuals) var-alst type-alst conj-acc t fixinfo clock
                      state))
         ((mv alst-term alst-conj alst-type-alst alst-type)
          (infer-type (cadr actuals) var-alst key-type-alst key-conj t fixinfo
                      clock state))
         (alst-key-type (key-type-of-alist-type alst-type))
         ((unless (subtype-of key-type alst-key-type))
          (mv (er hard? 'type-inference=>infer-fncall-assoc-equal
                  "Can't assoc-equal a ~p0 from a ~p1 in term ~p2~%"
                  key-type alst-type `(,fn ,@actuals))
              nil nil nil))
         (cons-type (cons-type-of-alist-type alst-type))
         (return-type (maybe-of-cons-table cons-type))
         (new-term `(,fn ,key-term ,alst-term)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,alst-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 alst-type-alst)
          return-type)))

  (define infer-cdr ((fn symbolp)
                     (actuals pseudo-term-listp)
                     (var-alst pseudo-term-alistp)
                     (type-alst pseudo-term-info-alistp)
                     (conj-acc pseudo-termp)
                     (expected-type symbolp)
                     (fixinfo smt-fixtype-info-p)
                     (clock natp)
                     state)
    :guard (equal fn 'cdr)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (equal fn 'cdr)))
          (mv nil conj-acc type-alst nil))
         ((mv car-term car-conj car-type-alst car-type)
          (infer-type (car actuals) var-alst type-alst conj-acc t fixinfo
                      clock state))
         ((if (list-type? car-type))
          (mv `(,fn ,car-term)
              `(if (,car-type (,fn ,car-term))
                   ,car-conj
                 'nil)
              (acons `(,fn ,car-term)
                     (make-type-info
                      :typeterm `(,car-type (,fn ,car-term))
                      :augterm `(,fn ,car-term))
                     car-type-alst)
              car-type))
         ((if (cons-type? car-type))
          (b* ((cdr-type (cdr-type-of-consp car-type)))
            (mv `(,fn ,car-term)
                `(if (,cdr-type (,fn ,car-term))
                     ,car-conj
                   'nil)
                (acons `(,fn ,car-term)
                       (make-type-info
                        :typeterm `(,cdr-type (,fn ,car-term))
                        :augterm `(,fn ,car-term))
                       car-type-alst)
                cdr-type)))
         ((unless (maybe-consp-type? car-type))
          (mv (er hard? 'type-inference=>infer-fncall-cdr
                  "The argument to cdr is of the wrong type. ~
                                  ~p0 in ~p1 is of type ~p2~%"
                  (car actuals) `(,fn ,@actuals)
                  car-type)
              nil nil nil))
         (cdr-fn (cdr-of-maybe-consp car-type))
         (new-term `(,cdr-fn ,car-term))
         (return-type (return-type-cdr-of-maybe-consp cdr-fn)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,car-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 car-type-alst)
          return-type)))

  (define infer-fn ((fn symbolp)
                    (actuals pseudo-term-listp)
                    (var-alst pseudo-term-alistp)
                    (type-alst pseudo-term-info-alistp)
                    (conj-acc pseudo-termp)
                    (expected-type symbolp)
                    (fixinfo smt-fixtype-info-p)
                    (clock natp)
                    state)
    :guard (not (equal fn 'quote))
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (not (equal fn 'quote))))
          (mv nil conj-acc type-alst nil))
         (expected-types (get-expected-types fn state))
         ((mv actuals-term actuals-conj actuals-type-alst
              actuals-types)
          (infer-type-list actuals var-alst type-alst conj-acc
                           expected-types fixinfo clock state))
         (return-type (make-judgement fn actuals actuals-types
                                      fixinfo state))
         ((unless (subtype-of return-type expected-type))
          (mv (er hard? 'type-inference=>infer-fncall
                  "Expected type ~p0 but ~p1 is of type ~p2~%"
                  expected-type `(,fn ,@actuals) return-type)
              nil nil nil))
         (new-term `(,fn ,@actuals-term)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,actuals-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 actuals-type-alst)
          return-type)))

  (define infer-if ((fn symbolp)
                    (actuals pseudo-term-listp)
                    (var-alst pseudo-term-alistp)
                    (type-alst pseudo-term-info-alistp)
                    (conj-acc pseudo-termp)
                    (expected-type symbolp)
                    (fixinfo smt-fixtype-info-p)
                    (clock natp)
                    state)
    :guard (equal fn 'if)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (clock (nfix clock))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (equal fn 'if)))
          (mv nil conj-acc type-alst nil))
         ((if (zp clock))
          (mv (er hard? 'type-inference=>infer-if
                  "Type inference runs out of clock.~%")
              nil nil nil))
         ((unless (equal (len actuals) 3))
          (mv (er hard? 'type-inference=>infer-if
              "Number of arguments is violated. ~p0 takes ~p1 arguments but is
                    given ~p2.~%" `(,fn ,@actuals) 3 (len actuals))
              nil nil nil))
         (expected-types (get-expected-types fn state))
         ;; infer the type for condition
         ((mv cond-term cond-conj cond-type-alst
              cond-type)
          (infer-type (car actuals) var-alst type-alst conj-acc
                      (car expected-types) fixinfo clock state))
         (new-then-else (if (option-type? cond-type)
                            (b* ((val-fn (get-val-fn cond-type))
                                 (subst `(,val-fn ,(car actuals)))
                                 (substed-then
                                  (term-substitution (cadr actuals) (car actuals)
                                                     subst)))
                              (cons substed-then (cddr actuals)))
                          (cdr actuals)))
         ((mv then-else-term then-else-conj then-else-type-alst
              then-else-types)
          (infer-type-list new-then-else var-alst cond-type-alst cond-conj
                           (cdr expected-types) fixinfo (1- clock) state))
         (return-type (lu-bound-list then-else-types))
         (new-term `(,fn ,cond-term ,@then-else-term))
         ((unless return-type)
          (mv (er hard? 'type-inference=>infer-if
                  "Type inference failed. can't calculate ~
          the least upper bound of the types of arguments to: ~
          ~%~p0 : ~p1~%"
                   new-term then-else-term)
              nil nil nil))
         ((unless (subtype-of return-type expected-type))
          (mv (er hard? 'type-inference=>infer-if
                  "Expected type ~p0 but ~p1 is of type ~p2~%"
                  expected-type new-term return-type)
              nil nil nil)))
      (mv new-term
          `(if (,return-type ,new-term)
               ,then-else-conj
             'nil)
          (acons new-term
                 (make-type-info
                  :typeterm `(,return-type ,new-term)
                  :augterm new-term)
                 then-else-type-alst)
          return-type)))

  (define infer-fncall ((fn symbolp)
                        (actuals pseudo-term-listp)
                        (var-alst pseudo-term-alistp)
                        (type-alst pseudo-term-info-alistp)
                        (conj-acc pseudo-termp)
                        (expected-type symbolp)
                        (fixinfo smt-fixtype-info-p)
                        (clock natp)
                        state)
    :guard (not (equal fn 'quote))
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix actuals)) 2)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (mbt (not (equal fn 'quote))))
          (mv nil conj-acc type-alst nil)))
      (cond ((equal fn 'cons) ;; cons
             (infer-cons fn actuals var-alst type-alst conj-acc
                         expected-type fixinfo clock state))
            ((equal fn 'acons) ;; acons
             (infer-acons fn actuals var-alst type-alst conj-acc
                          expected-type fixinfo clock state))
            ((equal fn 'assoc-equal) ;; assoc-equal
             (infer-assoc-equal fn actuals var-alst type-alst conj-acc
                                expected-type fixinfo clock state))
            ((equal fn 'cdr) ;; cdr
             (infer-cdr fn actuals var-alst type-alst conj-acc
                        expected-type fixinfo clock state))
            ((equal fn 'if) ;; if
             (infer-if fn actuals var-alst type-alst conj-acc
                       expected-type fixinfo clock state))
            (t ;; fncall
             (infer-fn fn actuals var-alst type-alst conj-acc
                       expected-type fixinfo clock state)))))

  (define infer-type ((term pseudo-termp)
                      (var-alst pseudo-term-alistp)
                      (type-alst pseudo-term-info-alistp)
                      (conj-acc pseudo-termp)
                      (expected-type symbolp)
                      (fixinfo smt-fixtype-info-p)
                      (clock natp)
                      state)
    :returns (mv (new-term pseudo-termp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type symbolp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-fix term)) 0)
    (b* ((term (pseudo-term-fix term))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         (item (assoc-equal term var-alst))
         ((if (and (consp (cdr item)) (symbolp (cadr item)) item))
          (mv term `(if ,(cdr item) ,conj-acc 'nil) type-alst (cadr item)))
         ((if (acl2::variablep term))
          (mv (er hard? 'type-inferece=>infer-type "Variable ~p0 isn't typed in the
                    environment.~%" term) nil nil nil))
         (item (assoc-equal term type-alst))
         ((if (and (consp item)
                   (consp (type-info->typeterm (cdr item)))
                   (symbolp (car (type-info->typeterm (cdr item))))))
          (mv (type-info->augterm (cdr item)) conj-acc
              type-alst (car (type-info->typeterm (cdr item)))))
         ((if (acl2::fquotep term))
          (infer-constant term type-alst conj-acc expected-type))
         ((cons fn actuals) term)
         ((if (pseudo-lambdap fn))
          (b* (((mv actuals-term actuals-conj actuals-type-alst actuals-types)
                (infer-type-list actuals var-alst type-alst conj-acc
                                 (generate-expected (len actuals)) fixinfo
                                 clock state))
               (formals (lambda-formals fn))
               ((unless (mbt (and (equal (len formals) (len actuals)))))
                (mv term conj-acc type-alst nil))
               ((unless (equal (len formals) (len actuals-term)))
                (mv (er hard? 'type-inference=>infer-type "This condition should be
                      proved using mbt. I can't prove it because of my
                      incompetence. But the fact that you triggered this
                      failure is a proof that this condition shouldn't be
                      proved in the first place. I guess I'm not a fool after
                      all.~%") nil nil nil))
               (body (lambda-body fn))
               (lambda-var-alst
                (extend-var-alist-for-lambda var-alst formals actuals-types))
               ((mv body-term body-conj & body-type)
                (infer-type body lambda-var-alst nil ''t expected-type fixinfo
                            clock state))
               (lambda-conj
                `(if ((lambda ,formals ,body-conj) ,@actuals)
                     ,actuals-conj
                   'nil))
               (lambda-term
                `((lambda ,formals ,body-term) ,@actuals-term)))
            (mv lambda-term
                lambda-conj
                (acons term (make-type-info
                             :typeterm `(,body-type ,term)
                             :augterm lambda-term)
                       actuals-type-alst)
                body-type))))
      (infer-fncall fn actuals var-alst type-alst conj-acc expected-type
                    fixinfo clock state)))

  (define infer-type-list ((term-lst pseudo-term-listp)
                           (var-alst pseudo-term-alistp)
                           (type-alst pseudo-term-info-alistp)
                           (conj-acc pseudo-termp)
                           (expected-type-lst symbol-listp)
                           (fixinfo smt-fixtype-info-p)
                           (clock natp)
                           state)
    :returns (mv (new-term-lst pseudo-term-listp)
                 (new-conj pseudo-termp)
                 (new-alst pseudo-term-info-alistp)
                 (new-type-lst symbol-listp))
    :measure (list (nfix clock) (acl2-count (pseudo-term-list-fix term-lst)) 0)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (var-alst (pseudo-term-alist-fix var-alst))
         (type-alst (pseudo-term-info-alist-fix type-alst))
         (conj-acc (pseudo-term-fix conj-acc))
         ((unless (consp term-lst)) (mv term-lst conj-acc type-alst nil))
         ((cons first rest) term-lst)
         ((cons first-expected rest-expected) expected-type-lst)
         ((mv first-term first-conj first-alst first-type)
          (infer-type first var-alst type-alst conj-acc first-expected fixinfo
                      clock state))
         (- (cw "first-conj: ~q0" first-conj))
         ((mv rest-terms rest-conj rest-alst rest-types)
          (infer-type-list rest var-alst first-alst first-conj rest-expected
                           fixinfo clock state))
         (- (cw "rest-conj: ~q0" rest-conj)))
      (mv (cons first-term rest-terms)
          rest-conj rest-alst (cons first-type rest-types))))
  )

(local
(defthm not-null-of-infer-type-list.new-type-lst
  (implies (not (consp (mv-nth 3
                               (infer-type-list actuals var-alst type-alst
                                                conj-acc expected-types
                                                fixinfo clock state))))
           (not (mv-nth 3
                        (infer-type-list actuals var-alst type-alst
                                         conj-acc expected-types
                                         fixinfo clock state))))
  :hints (("Goal"
           :use ((:instance acl2::true-listp-when-symbol-listp
                            (acl2::x (mv-nth 3
                                             (infer-type-list actuals var-alst type-alst
                                                              conj-acc expected-types
                                                              fixinfo clock state))))))))
)

(verify-guards infer-type
  :hints (("Goal" :in-theory (e/d (get-expected-types)
                                  (pseudo-termp
                                   acl2::pseudo-term-listp-of-cons)))))

(local
 (in-theory (enable pseudo-term-listp)))

(define infer-type-fn ((cl pseudo-term-listp)
                       (smtlink-hint t)
                       state)
  :returns (subgoal-lst pseudo-term-list-listp)
  :irrelevant-formals-ok t
  :ignore-ok t
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       ((mv type-hyp-lst untyped-theorem)
        (smt-extract (disjoin cl) h.types-info))
       (type-alist (type-list-to-alist type-hyp-lst h.types-info))
       (- (cw "type-alist: ~q0" type-alist))
       ((mv new-theorem new-conj new-hyp top-type)
        (infer-type untyped-theorem type-alist nil ''t t h.types-info
                    (acl2-count untyped-theorem) state))
       (- (cw "new-theorem: ~p0, type conj: ~p1, top-type: ~p2~%" new-theorem
              new-conj top-type))
       (new-cl `((implies ,new-conj ,new-theorem)))
       (next-cp (cdr (assoc-equal 'infer-type *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define infer-type-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* ((inferred-clause (infer-type-fn cl hints state)))
    (value inferred-clause)))

(local (in-theory (enable infer-type-cp infer-type-fn infer-type)))

(skip-proofs
 (defthm correctness-of-infer-type-cp
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-infer
                  (conjoin-clauses
                   (acl2::clauses-result
                    (infer-type-cp cl hint state)))
                  a))
            (ev-infer (disjoin cl) a))
   :rule-classes :clause-processor)
 )
