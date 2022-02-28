;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "type-refinement")
(include-book "type-equiv")
(include-book "type-list")
(include-book "type-str")
(include-book "type-fix")
(include-book "type-fty")
(include-book "kwargs")

(def::und weak-forward-chain-or (name n list term rule-classes hints)
  (declare (xargs :signature ((symbolp natp true-listp t true-listp t) true-listp)))
  (if (endp list) nil
    (append
     `((defthm ,(symbol-fns::suffix name '- n)
         (implies
          ,(car list)
          ,term)
         :hints ,hints
         :rule-classes (,@rule-classes))
       ,@(and rule-classes 
              `((local (in-theory (disable ,(symbol-fns::suffix name '- n)))))))
     (weak-forward-chain-or name (1+ n) (cdr list) term rule-classes hints))))
              
(def::und body-implies-term (term body)
  (declare (xargs :signature ((pseudo-termp pseudo-term-listp) pseudo-termp)))
  `(implies (and ,@body) ,term))

(def::und term-implies-body (term body)
  (declare (xargs :signature ((pseudo-termp pseudo-term-listp) pseudo-termp)))
  `(implies ,term (and ,@body)))

(def::und not-term-implies-not-body (nterm nbody)
  (declare (xargs :signature ((pseudo-termp pseudo-term-listp) pseudo-termp)))
  `(implies ,nterm (or ,@nbody)))

(def::und not-body-implies-not-term (nterm nbody)
  (declare (xargs :signature ((pseudo-termp pseudo-term-listp) pseudo-termp)))
  `(implies (or ,@nbody) ,nterm))

(defund true-pseudo-termp (x)
  (declare (type t x))
  (equal x acl2::*t*))

(defund false-pseudo-termp (x)
  (declare (type t x))
  (equal x acl2::*nil*))

(def::un drop-nots (neg term)
  (declare (xargs :signature ((t pseudo-termp) pseudo-termp)))
  (case-match term
    (('not arg)
     (drop-nots (not neg) arg))
    (('<= x y)
     (if (not neg) term
       `(< ,y ,x)))
    (&
     (if (not neg) term
       (cond
	((true-pseudo-termp term)  acl2::*nil*)
	((false-pseudo-termp term) acl2::*t*)
	(t `(not ,term)))))))

(def::und negate-term (term)
  (declare (xargs :signature ((pseudo-termp) pseudo-termp)))
  (drop-nots t term))

(def::un negate-term-list (list)
  (declare (xargs :signature ((pseudo-term-listp) pseudo-term-listp)))
  (if (endp list) nil
    (cons (negate-term (car list))
	  (negate-term-list (cdr list)))))

(def::und not- (x)
  (declare (xargs :signature ((t) symbolp)))
  (if x '|| 'not-))

;;
;; call pattern for conjunction:
;;
;; (common-rule-events 'joe 'and-t1-t2 '(and-t1-t2 x) '((t1 x) (t2 x)) t nil)
;;
;; call pattern for disjunction:
;;
;; (common-rule-events 'joe 'or-t1-t2 '(not (or-t1-t2 x)) '((not (t1 x)) (not (t2 x))) nil nil)
;;
;; :negative-rules      : rewrite rules to establish the negation of the predicate
;;                      (implies (not (and x y)) (not (and x y)))
;;                      (implies (and (not x) (not y)) (not (or x y)))
;;
;;                      recommended only if reasoning about negated predicates is
;;                      anticipated.
;;
;; :positive-rules      : rewrite rules to establish the positive of the predicate
;;                      (implies (and x y) (and x y))
;;                      (implies (or x y) (or x y))
;;
;;                      there is no good reason to disable positive type
;;                      rules unless perhaps the predicate is left enabled
;;
;; :rewrite             : enable rewriting to establish given elements of a conjunct
;; :type-prescription   : enable type-prescription rules to establish given elements of a conjunct
;;                      (implies (and x y) (and x y))
;;                      (implies (not (or x y)) (and (not x) (not y)))
;;
;; :tau-system          : enable tau reasoning for rewrite-like rules
;;
;; :forward-chain       : permit the use of forward-chaining
;;
;; :forward-chain-or    : forward chain disjunctions (not and) or (or)
;;                      (implies (not (and x y)) (or (not x) (not y)))
;;                      (implies (or x y)        (or x y))            
;;
;;                      this is recommended for disjunctions and for conjunctions when
;;                      negated predicates are anticipated, in which case :nneg = nil
;;
;; :forward-chain-and   : forward chain conjunctions (and) or (not or))
;;                      (implies (and x y) (and x y))
;;                      (implies (not (or x y)) (and (not x) (not y)))
;;
;;                      this is recommended for conjunctions and for disjunctions when
;;                      negated predicates are anticipated, in which ase :nneg = nil
;;
;; :forward-chain-cases : forward chain the individual cases of an 'or' hypothesis
;;                      (implies x (or x y))
;;                      (implies y (or x y))
;;                      (implies (not x) (not (and x y)))
;;                      (implies (not y) (not (and x y)))
;;
;;                      this isn't really recommented for most cases.
;;
;; :forward-chain-body  : trigger on the body to forward chain the predicate.
;;                      (implies (and x y) (and x y))
;;                      (implies (and (not x) (not y)) (not (or x y)))
;;
;;                      this isn't really recommended for most cases.
;;

(def::und common-rule-events (pkg base term body and kwargs)
  (declare (xargs :signature ((symbolp symbolp pseudo-termp pseudo-term-listp t kwargs-alistp) true-listp)))
  (b* (((&key prove-properties
              forward-chain
              rewrite
              type-prescription
              forward-chain-or
              forward-chain-and
              forward-chain-body
              forward-chain-cases
              tau-system
              negative-rules
              positive-rules
              prove-in-theory)
        kwargs)
       (nneg             (not negative-rules))
       (npos             (not positive-rules))
       ((mv nneg npos)   (if and (mv nneg npos) (mv npos nneg)))
       (term-implies     (symbol-fns::join-symbols pkg (not- and) base '-implies-body))
       (implies-term     (symbol-fns::join-symbols pkg (not- and) 'body-implies- base))
       (not-term-implies (symbol-fns::join-symbols pkg (not- (not and)) base '-implies- (not- (not and)) 'body))
       (implies-not-term (symbol-fns::join-symbols pkg (not- (not and)) 'body-implies- (not- (not and)) base))
       (nterm            (negate-term term))
       (nbody            (negate-term-list body))
       ;;
       (tclass1  `(:rewrite ,@(and rewrite type-prescription `(:type-prescription))
                            ,@(and rewrite tau-system `(:tau-system))
                            :forward-chaining))
       (theory1  `((local (in-theory (disable ,term-implies)))
                   ,@(and (not rewrite)
                          `((in-theory (disable (:rewrite ,term-implies)))))
                   ,@(and (or (not forward-chain) (not forward-chain-and))
                          `((in-theory (disable (:forward-chaining ,term-implies)))))
                   ))
       ;;
       (fclass1  `(:rewrite ,@(and type-prescription `(:type-prescription))
                            ,@(and (not npos) tau-system `(:tau-system))
                            :forward-chaining))
       (theory2  `((local (in-theory (disable ,implies-term)))
                   ,@(and npos
                          `((in-theory (disable (:rewrite ,implies-term)
                                                ,@(and type-prescription `((:type-prescription ,implies-term)))))))
                   ,@(and (or (not forward-chain) (not forward-chain-body))
                          `((in-theory (disable (:forward-chaining ,implies-term)))))
                   ))
       ;;
       (tclass2  `(:forward-chaining))
       (theory3  `((local (in-theory (disable ,not-term-implies)))
                   ,@(and (or (not forward-chain) (not forward-chain-or))
                          `((in-theory (disable (:forward-chaining ,not-term-implies)))))))
       ;;
       (fclass2  `(:rewrite
                   ,@(and type-prescription `(:type-prescription))
                   ,@(and (not nneg) tau-system `(:tau-system))))
       (theory4   `((local (in-theory (disable ,implies-not-term)))
                    ,@(and nneg
                           `((in-theory (disable (:rewrite ,implies-not-term)
                                                 ,@(and type-prescription `((:type-prescription ,implies-term)))))))
                    ))
       )
    (let ((hints nil))
      (let ((term-implies-thm     (named-rule term-implies     (term-implies-body term body)           tclass1 hints theory1))
	    (implies-term-thm     (named-rule implies-term     (body-implies-term term body)           fclass1 hints theory2))
            (not-term-implies-thm (named-rule not-term-implies (not-term-implies-not-body nterm nbody) tclass2 hints theory3))
	    (implies-not-term-thm (named-rule implies-not-term (not-body-implies-not-term nterm nbody) fclass2 hints theory4))
            (implies-not-term-fwd (weak-forward-chain-or implies-not-term 1 nbody nterm 
                                                         `(,@(and (not nneg) tau-system `(:tau-system))
                                                           ;;
                                                           ;; i don't know how strong :type-prescription is
                                                           ;; when faced with disjunctions in the hypothesis.
                                                           ;; for now, we will assume that it is weak and
                                                           ;; provide it with a set of individual rules.
                                                           ;;
                                                           ,@(and (not nneg) type-prescription `(:type-prescription))
                                                           ,@(and forward-chain-cases `(:forward-chaining)))
                                                         hints))
            )
	(and prove-properties
             `((encapsulate
                   ()
                 ,@(and prove-in-theory `((local (in-theory ,prove-in-theory))))
                 ,@term-implies-thm
                 ,@implies-term-thm
                 ,@not-term-implies-thm
                 ,@implies-not-term-thm
                 ,@implies-not-term-fwd
                 )))))))

;; (common-rule-events 'joe 'and-t1-t2 '(and-t1-t2 x) '((t1 x) (t2 x))                 t   (list :tau-system t :npos t :nneg t))
;; (common-rule-events 'joe 'or-t1-t2 '(not (or-t1-t2 x)) '((not (t1 x)) (not (t2 x))) nil (list :tau-system t :npos t :nneg t))

(defun predicate-type-specifier (x)
  (declare (type t x))
  (or (equal x :conjunction)
      (equal x :disjunction)))

(def::und rule-events (pkg base term body class kwargs)
;; nneg npos forward-chain-or forward-chain-body forward-chain-cases tau-system
  (declare (xargs :signature ((symbolp 
                               symbolp 
                               pseudo-termp 
                               pseudo-term-listp 
                               predicate-type-specifier 
                               kwargs-alistp)
                              true-listp)))
  (if (equal class :disjunction)
      (let ((nterm (negate-term term))
            (nbody (negate-term-list body)))
        (common-rule-events pkg base nterm nbody nil kwargs))
    (common-rule-events pkg base term body t kwargs)))

(defund ever-set (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (or (car list) (ever-set (cdr list)))))

(defund not-list (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (cons (not (car list))
          (not-list (cdr list)))))

(defun and-or-p (term)
  (declare (type t term))
  (case-match term
    (('and . args)  (pseudo-term-listp args))
    (('or . args)   (pseudo-term-listp args))
    (&              (pseudo-termp term))))

(def::un list-fix (x)
  (declare (xargs :signature ((t) true-listp)))
  (if (not (consp x)) nil
    (cons (car x) (list-fix (cdr x)))))

(def::und and-or-type (term)
  (declare (xargs :signature ((t) predicate-type-specifier)))
  (case-match term
    (('or . &)  :disjunction)
    (&          :conjunction)))
  
(def::und and-or-body (term)
  (declare (xargs :signature ((and-or-p) pseudo-term-listp)))
  (case-match term
    (('and . args)  args)
    (('or . args)   args)
    (&              (list term))))

(defun unary-function (x)
  (declare (type t x))
  (and (consp x)
       (symbolp (car x))
       (null (cdr x))))

;;
;; relational list
;;

;;
;; we should have a refinement map for each of our types.  technically
;; we should probably auto-generate the list rules for each type.
;;
;; (tx :executable t
;;     :list tx-list
;;     :extends (t1 t2)
;;     :refines (ta tb)
;;     )
;;
;; (tx-list :executable t
;;          :element tx
;;          :extends (t1-list t2-list)
;;          :refines (ta-list tb-list)
;;          )

;; our 

;; (implies (and (type-list-p list) (natp i) (< 0 i) (< i (len list))) (type-p (nth i list)))

;;
;; :body (or (equal x :a) (equal y :b))
;; :refines (symbol)
;;

;; we usually won't want to prove the refinements.
;; - when given a :body, :refines/:extends should just reflect that predicates in that body.
;;   -> ie: we don't prove the implication rules
;; - when given :or/:and, :refines/:extends should be redundant.
;;   -> the standard type rules should give us the desired implications
;;

(mutual-recursion
 (defun fix-weak-pseudo-term (term)
   (declare (type t term))
   (if (consp term)
       (cond
        ((equal (car term) 'quote) term)
        (t
         (cons (car term) (fix-weak-pseudo-term-list (cdr term)))))
     (if (symbolp term)
         term
       `(quote ,term))))
 (defun fix-weak-pseudo-term-list (args)
   (declare (type t args))
   (if (not (consp args)) nil
     (cons (fix-weak-pseudo-term (car args))
           (fix-weak-pseudo-term-list (cdr args)))))
 )

(defun make-body-from-type-name-list (type-name-list args fty-alist)
  (if (not (consp type-name-list)) nil
    (let* ((type-name (car type-name-list))
           (fty-entry (fty::get-entry type-name fty-alist))
           (type-p    (fty::get-key 'fty::pred fty-entry)))
      (cons (cons type-p args)
            (make-body-from-type-name-list (cdr type-name-list) args fty-alist)))))

;; (implies (and (t1) (t2)) (t3)) <- yes, :rewrite, :type-prescription
;;
;; (implies (t3) (and (t1) (t2))) <- uhh .. maybe not (?)

(defun make-predicate-body (define type args defn body and or fty-alist)
  (declare (ignorable type))
  (if (not define) (mv nil nil)
    (if (or defn body)
        (then
         (assert! (not (or and or)) ("you may bind no more than one of {:body :and :or} keywords")
                  :context 'def::type-predicate)
         (assert! (not (and defn body)) ("type ~x0 definition already exists, you may not specify a :body keyword" type)
                  :context 'def::type-predicate)
         (mv (not defn) (or defn body)))
      (else
       (assert! (or and or) ("type ~x0 is not currently defined; you must specify one of {:body :and :or} keywords" type)
                :context 'def::type-predicate)
       (assert! (not (and and or)) ("you may bind no more than one of {:and :or} keywords")
                :context 'def::type-predicate)
       (if and (mv t `(and ,@(make-body-from-type-name-list and args fty-alist)))
         (mv t `(or ,@(make-body-from-type-name-list or args fty-alist))))))))

(defun def-type-predicate (type-p args define refinement-events kwargs)
  (declare (xargs :mode :program))
  (b* (((&key prove-properties type-name guard non-executable doc body disable-type-p define-in-theory) kwargs)
       (kwargs (keep (def-type-property-keywords) kwargs))
       (body (fix-weak-pseudo-term body))
       (decl `(declare (type t ,@args) (xargs :normalize nil ,@(and guard `(:guard ,guard)))))
       (base (if define
                 type-p
               (symbol-fns::prefix 'deftype-properties- type-p)))
       (xbody (and-or-body body))
       (xtype (and-or-type body))
       (rules (rule-events base type-p `(,type-p ,@args) xbody xtype kwargs))
       (doc   (or doc
                  (and type-name (doc-string "predicate ~x0 recognizes objects of type ~x1" type-p type-name))
                  (doc-string "function ~x0 is a type predicate" type-p)))
       (body  (if (equal (and-or-type body) :conjunction)
                  `(and ,@xbody t)
                `(or ,@xbody nil)))
       )
    (if (or define prove-properties refinement-events)
        `(encapsulate
             ()
           ,@(and define
                  `((encapsulate
                        ()
                      ,@(and define-in-theory `((local (in-theory ,define-in-theory))))
                      (defun ,type-p ,args ,doc ,decl ,body)
                      )))
           ,@(and define non-executable `((in-theory (disable (,type-p)))))
           ,@(and define `((local (in-theory (union-theories
                                              '(,type-p)
                                              (theory 'acl2::minimal-theory))))))
           ,@rules
           ,@refinement-events
           ,@(and disable-type-p `((in-theory (disable ,type-p))))
           ,@(and non-executable `((in-theory (disable (,type-p)))))
           )
      `(progn))
    ))

(defun def-type-properties (type-p args body kwargs)
  (b* ((xbody (and-or-body body))
       (xtype (and-or-type body)))
    `(progn
       ,@(rule-events type-p type-p `(,type-p ,@args) xbody xtype kwargs)
       )))

(defun def-type-properties-wrapper (type-p args kwargs state)
  (declare (xargs :stobjs state
                  :mode :program)
           (ignorable args))
  (b* ((inline-type-p (safe-packn-pos (list type-p '$inline) type-p))
       (body (or (and (not (eq (getpropc type-p 'acl2::formals t) t))
                      (untranslate (getpropc type-p 'acl2::unnormalized-body) nil (w state)))
                 (and (not (eq (getpropc inline-type-p 'acl2::formals t) t))
                      (untranslate (getpropc inline-type-p 'acl2::unnormalized-body) nil (w state)))))
       (args (or (getpropc type-p 'acl2::formals nil)
                 (getpropc inline-type-p 'acl2::formals nil))))
    (def-type-properties type-p args body kwargs)))

(defmacro def::type-properties (name args &rest kvlist)
  (let ((kwargs (kwargs (def-type-property-keywords) kvlist)))
    `(make-event (def-type-properties-wrapper ',name ',args ',kwargs state))))

(defun def-type-predicate-wrapper (type-p args kwargs state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (((&key define-predicate body and or) kwargs)
       (inline-type-p (safe-packn-pos (list type-p '$inline) type-p))
       (defn (or (and (not (eq (getpropc type-p 'acl2::formals t) t))
                      (untranslate (getpropc type-p 'acl2::unnormalized-body) nil (w state)))
                 (and (not (eq (getpropc inline-type-p 'acl2::formals t) t))
                      (untranslate (getpropc inline-type-p 'acl2::unnormalized-body) nil (w state)))))
       (args (if (not defn) args
               (or (getpropc type-p 'acl2::formals nil)
                   (getpropc inline-type-p 'acl2::formals nil))))
       (body (fix-weak-pseudo-term body))
       (fty-alist (fty::get-fixtypes-alist (w state)))
       ((mv define body) (make-predicate-body define-predicate type-p args defn body and or fty-alist))
       (refinement-kwargs (keep (def-type-refinement-keywords) kwargs))
       (refinement-events (make-type-refinement-events type-p fty-alist refinement-kwargs))
       (kwargs (update kwargs :body body))
       )
    (with-guard-checking
     :all
     (def-type-predicate type-p args define refinement-events kwargs))))

(defmacro def::type-predicate (type-p args &rest kvlist)
  (let ((kwargs (kwargs (def-type-predicate-keywords) kvlist)))
    `(make-event (def-type-predicate-wrapper ',type-p ',args ',kwargs state))))

(defun def-type-fn (type-name kwargs)
  (declare (type symbol type-name)
           (type (satisfies kwargs-alistp) kwargs))
  (b* (((&key       (symbolp (type-p 'nil) (fix 'nil) (fix! 'nil) (equiv 'nil))) kwargs)
       ((&key       args non-executable fix-constants prefer-guarded type-list list-extends list-refines) kwargs)
       (type-p      (default-name type-p type-name '-p type-name))
       (type-equiv  (default-name equiv type-name '-equiv type-p))
       (type-fix!   (type-fix! fix! fix type-name type-p))
       (type-fix    (type-fix  fix type-name type-fix! type-p))
       (kwargs      (update kwargs
                            :type-p type-p
                            :fix type-fix
                            :fix! type-fix!
                            :equiv type-equiv)))
    `(encapsulate
         ()
       
       (def::type-predicate ,type-p ,args
         ,@(kvlist (keep (def-type-predicate-keywords) kwargs) )
         )
       
       (def::type-fix ,type-name
         ,@(kvlist (keep (def-type-fix-keywords) kwargs)
                   :non-executable non-executable)
         )
       
       (def::type-equiv ,type-name
         ,@(kvlist (keep (def-type-equiv-keywords) kwargs
                         :fix (if prefer-guarded type-fix type-fix!)
                         :guarded prefer-guarded
                         ))
         )
       
       (def::type-fty ,type-name
         :type-p ,type-p
         :fix    ,type-fix
         :fix!   ,type-fix!
         :equiv  ,type-equiv
         :fix-constants ,(and (not non-executable) fix-constants) ;; related to non-executable
         )
       
       (def::type-refinement ,type-name
         ,@(kvlist (keep (def-type-refinement-keywords) kwargs))
         )

       ,@(and type-list `((def::type-list ,type-name
                            ,@(kvlist (keep (def-type-list-keywords) kwargs
                                            :refines list-refines
                                            :extends list-extends
                                            )))))
       
       )))

(defun prefer-guarded (prefer-guarded type-fix type-fix! state)
  (declare (xargs :stobjs state :mode :program))
  (let ((undef-fix  (undefined-fn type-fix))
        (undef-fix! (undefined-fn type-fix!)))
    (if (iff undef-fix undef-fix!) prefer-guarded
      undef-fix!)))
  
(defun def-type-fn-wrapper (type-name kwargs state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((&key prefer-guarded fix fix!) kwargs)
       (prefer-guarded (prefer-guarded prefer-guarded fix fix! state))
       (kwargs (update kwargs :prefer-guarded prefer-guarded)))
    (with-guard-checking :all (def-type-fn type-name kwargs))))

(defmacro def::type (type-name args &rest kvlist)
  (b* ((kwargs (kwargs (def-type-keywords) kvlist))
       (kwargs (extend kwargs :args args)))
    `(make-event (def-type-fn-wrapper ',type-name ',kwargs state))))

#+joe
(def::type foo (x)
  ;;
  ;; type-p
  ;;
  :type-p integer-p
  :body (integerp x)
  :and (type1 type2)
  :or  (typeA typeB)
  :non-executable t
  :guard (type x)
  :negative-rules t
  ;;
  ;; type-fix
  ;;
  :type-fix foo-fix
  :fix-in-theory (enable )
  :witness 0
  ;;
  ;; type-equiv
  ;;
  :type-equiv foo-equiv
  :equality eql
  :reduce-equiv t
  :equal-fix-rule-classes :all
  :equiv-in-theory (enable )
  :refine-equiv-in-theory (e/d () ())
  ;;
  ;; type-refines
  ;;
  :type-refines (type1 type2)
  :type-extends (typeA typeB)
  :refine-type-in-theory (e/d () ())
  ;;
  ;; type-list
  ;;
  :type-list            type-list
  :type-list-p          type-list-p
  :type-list-fix        type-list-fix
  :type-list-equiv      type-list-equiv
  :type-list-refines    (true-list)
  :type-list-extends    (integer-list)
  :type-list-in-theory  (enable foo)
  )


#|

(defmacro def::type (name args &rest body)
  (def-type-fn name args body t nil nil))

(defmacro def::type+ (name args &rest body)
  (def-type-fn name args body t t nil))

(defmacro def::type-properties (name args &rest body)
  (def-type-fn name args body nil nil nil))

(defmacro def::type-properties+ (name args &rest body)
  (def-type-fn name args body nil t nil))

(local
(encapsulate
    ()

  (def::type singlep (x)
    (declare (type t x))
    (atom x))
  
  (def::type posnatp (x)
    (declare (xargs :type-witness 1)
             (type t x))
    (and (integerp x) (natp x) (< '0 x)))
  
  (def::type-properties posnatp (x)
    (declare (type t x))
    (and (integerp x) (natp x) (< '0 x)))

  (def::type+ choose (x)
    (declare (type t x))
    (or (symbolp x)
	(stringp x)
	(integerp x)))

  (def::type-properties+ choose (x)
    (declare (type t x))
    (or (symbolp x)
	(stringp x)
	(integerp x)))

  ))

(defmacro def::fty (name &key (pred 'nil) (fix 'nil) (equiv 'nil) (witness 'nil) (refines 'nil) (extends 'nil) (in-theory 'nil))
  ;;(let ((type-type-equiv (symbol-fns::suffix name '- equiv)))
  `(encapsulate
       ()
     ,@(deftype-fty pred name fix equiv ;; type-type-equiv
         witness refines extends in-theory)
     ))

(def::fty acl2::complex
  :type-p acl2::complex-rationalp
  :fix    acl2::complex-fix
  :equiv  acl2::complex-equiv
  :witness (complex 1 1)
  :refines (acl2::acl2-number))

(defun type-p (x)
  (declare (type t x))
  body)

(def::type-fix (x)
  (declare (xargs :signature ((t) type-p)))
  ..)

(def::type type (x)
  (declare (xargs :fix! type-fix))
  (type-p x))

|#
