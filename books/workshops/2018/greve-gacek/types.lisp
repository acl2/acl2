;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "centaur/fty/fixtype" :dir :system)

(def::und named-rule (name body rule-classes hints theory)
  (declare (xargs :signature ((symbolp pseudo-termp t t true-listp) true-listp)))
  `((defthm ,name ,body 
      :rule-classes ,rule-classes
      :hints ,hints)
    ,@theory))

(def::un named-rule-list (pkg base n list rule-classes hints theory)
  (declare (xargs :signature ((symbolp symbolp natp pseudo-term-listp t t true-listp) true-listp)))
  (if (endp list) nil
    (let ((name (symbol-fns::join-symbols pkg base '- n)))
      (append (named-rule name (car list) rule-classes hints theory)
	      (named-rule-list pkg base (1+ n) (cdr list) rule-classes hints theory)))))

(def::und weak-forward-chain-or (name n list term rule-classes hints)
  (declare (xargs :signature ((symbolp natp true-listp t true-listp t) true-listp)))
  (if (endp list) nil
    (cons `(defthm ,(symbol-fns::suffix name '- n)
             (implies
              ,(car list)
              ,term)
             :hints ,hints
             :rule-classes (,@rule-classes))
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
  (equal x *t*))

(defund false-pseudo-termp (x)
  (declare (type t x))
  (equal x *nil*))

(def::un drop-nots (neg term)
  (declare (xargs :signature ((t pseudo-termp) pseudo-termp)))
  (case-match term
    (('not arg)
     (drop-nots (not neg) arg))
    (&
     (if (not neg) term
       (cond
	((true-pseudo-termp term)  *nil*)
	((false-pseudo-termp term) *t*)
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

(def::und get-key (key body)
  (declare (xargs :signature ((symbolp true-listp) t)))
  (if (endp body) nil
    (if (endp (cdr body)) nil
      (if (equal (car body) key) (car (cdr body))
        (get-key key (cddr body))))))

(def::und common-rule-events (pkg base term body and xargs)
  (declare (xargs :signature ((symbolp symbolp pseudo-termp pseudo-term-listp t true-listp) true-listp)))
  (let* ((forward-chain-or      (get-key :forward-chain-or xargs))
         (forward-chain-body    (get-key :forward-chain-body xargs))
         (implies-term-forward-chaining (get-key :implies-term-forward-chaining xargs))
         (forward-chain-parent  (get-key :forward-chain-parent xargs))
         (tau-system            (get-key :tau-system xargs))
         (nneg                  (get-key (if and :nneg :npos) xargs))
         (npos                  (get-key (if and :npos :nneg) xargs))
         (tau-system       (and tau-system `(:tau-system)))
         (term-implies     (symbol-fns::join-symbols pkg (not- and) base '-implies-body))
         (implies-term     (symbol-fns::join-symbols pkg (not- and) 'body-implies- base))
         (not-term-implies (symbol-fns::join-symbols pkg (not- (not and)) base '-implies- (not- (not and)) 'body))
         (implies-not-term (symbol-fns::join-symbols pkg (not- (not and)) 'body-implies- (not- (not and)) base))
         (nterm            (negate-term term))
         (nbody            (negate-term-list body))
         (fclass1  `(,@tau-system :forward-chaining))
         (fclass2  `(:forward-chaining))
         ;;(trigger `(:trigger-terms (,@(if and body nbody))))
         (fw1      (and implies-term-forward-chaining `((:forward-chaining :backchain-limit-lst 0))))
         ;; For now this encodes "strong types" ..
         ;; You know, if you are going to do this you really should create several
         ;; different rules, each that can trigger on its own.
         ;;(fw2      (and forward-chain-or npos `((:forward-chaining ,@trigger :backchain-limit-lst 0))))
         (tclass1 `(,@tau-system :rewrite :type-prescription ,@fw1))
         ;; Don't widen that way ..
         ;; OK .. but how will we figure out conformance from a single instance?
         ;;
         ;; Now, consider the fact that rewriting is not applied to
         ;; forward chained results .. can we leverage that fact in
         ;; some way?  Perhaps we could rewrite back to 
         ;;
         ;; And we are only really pushing 
         ;;
         (tclass2 `(:rewrite :type-prescription));;  ,@fw2))
         (theory1 (and (not forward-chain-body) `((in-theory (disable ,term-implies)))))
         (theory2 (and npos `((in-theory (disable (:rewrite ,implies-term)     (:type-prescription ,implies-term))))))
         (theory3 (and nneg `((in-theory (disable (:rewrite ,implies-not-term) (:type-prescription ,implies-not-term))))))
         (theory4 (and (not forward-chain-or) `((in-theory (disable ,not-term-implies)))))
         )
    (let ((hints nil))
      (let ((term-implies-thm     (named-rule term-implies     (term-implies-body term body)           fclass1 hints theory1))
	    (implies-term-thm     (named-rule implies-term     (body-implies-term term body)           tclass1 hints theory2))
            (not-term-implies-thm (named-rule not-term-implies (not-term-implies-not-body nterm nbody) fclass2 hints theory4))
	    (implies-not-term-thm (named-rule implies-not-term (not-body-implies-not-term nterm nbody) tclass2 hints theory3))
            (implies-not-term-fwd (weak-forward-chain-or implies-not-term 1 nbody nterm 
                                                         `(,@tau-system
                                                           ,@(and forward-chain-parent `(:forward-chaining)))
                                                         hints))
            )
	(append
	 term-implies-thm
	 implies-term-thm
	 not-term-implies-thm
	 implies-not-term-thm
         implies-not-term-fwd
	 )))))

(defun predicate-type-specifier (x)
  (declare (type t x))
  (or (equal x :conjunction)
      (equal x :disjunction)))

(def::und rule-events (pkg base term body class xargs)
;; nneg npos forward-chain-or implies-term-forward-chaining forward-chain-parent tau-system
  (declare (xargs :signature ((symbolp 
                               symbolp 
                               pseudo-termp 
                               pseudo-term-listp 
                               predicate-type-specifier 
                               true-listp) 
                              true-listp)))
  (if (equal class :disjunction)
      (let ((nterm (negate-term term))
            (nbody (negate-term-list body)))
        (common-rule-events pkg base nterm nbody nil xargs))
    (common-rule-events pkg base term body t xargs)))

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

(defun deftype-fty (type-p type-name type-fix type-equiv type-type-equiv witness)
  (declare (type symbol type-p type-name type-fix type-equiv type-type-equiv))
  (let* ((type-witness                 (symbol-fns::suffix type-name '-witness))
         (type-p-type-witness          (symbol-fns::suffix type-p '- type-witness))
         (type-p-type-fix              (symbol-fns::suffix type-p '- type-fix))
         (type-fix-type-name           (symbol-fns::suffix type-fix '- type-name))
         (type-equiv-type-fix          (symbol-fns::suffix type-equiv '- type-fix))
         (equal-type-fix-to-type-equiv (symbol-fns::prefix 'equal- type-fix '-to- type-equiv))
         (type-equiv-to-equal          (symbol-fns::suffix type-equiv '-to-equal))
         (type-type-equiv-type-fix     (symbol-fns::suffix type-type-equiv '- type-fix))
         )
    
    `(
      (encapsulate
          ()
        (set-tau-auto-mode nil)
        (defun ,type-witness ()
          (declare (xargs :verify-guards t))
          ,witness)
        (set-tau-auto-mode t)
        (defthm ,type-p-type-witness
          (,type-p (,type-witness))
          :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((,type-witness)))))
        (in-theory (disable (:type-prescription ,type-witness) (,type-witness) ,type-witness))
        )
      (encapsulate
          ()
        (defun ,type-fix (x)
          (declare (type t x))
          (if (,type-p x) x (,type-witness)))
        (defthm ,type-p-type-fix
          (,type-p (,type-fix x))
          :rule-classes ((:forward-chaining :trigger-terms ((,type-fix x)))))
        (defthm ,type-fix-type-name
          (implies
           (,type-p x)
           (equal (,type-fix x) x)))
        (defun ,type-equiv (x y)
          (declare (type t x y))
          (equal (,type-fix x) (,type-fix y)))
        (defequiv ,type-equiv)
        (defcong ,type-equiv equal (,type-fix x) 1)
        (defthm ,type-equiv-type-fix
          (,type-equiv (,type-fix x) x))
        (defthm ,equal-type-fix-to-type-equiv
          (and (equal (equal (,type-fix x) y)
                      (and (,type-p y)
                           (,type-equiv x y)))
               (equal (equal y (,type-fix x))
                      (and (,type-p y)
                           (,type-equiv x y)))))
        (local (in-theory (disable ,equal-type-fix-to-type-equiv)))
        (defthmd ,type-equiv-to-equal
          (implies
           (and (,type-p x) (,type-p y))
           (iff (,type-equiv x y)
                (equal x y))))
        (defun ,type-type-equiv (x y)
          (declare (type t x y))
          (and (iff (,type-p x) (,type-p y))
               (,type-equiv x y)))
        (defequiv ,type-type-equiv)
        (defcong ,type-type-equiv equal (,type-p x) 1)
        (defrefinement ,type-type-equiv ,type-equiv)
        (defthm ,type-type-equiv-type-fix
          (and (iff (,type-type-equiv (,type-fix x) y)
                    (and (,type-p y)
                         (,type-equiv x y)))
               (iff (,type-type-equiv y (,type-fix x))
                    (and (,type-p y)
                         (,type-equiv x y)))))
        (in-theory (disable ,type-type-equiv))
        (in-theory (disable ,type-fix ,type-equiv))
        (theory-invariant (incompatible (:definition ,type-equiv)
                                        (:rewrite ,equal-type-fix-to-type-equiv)))
        (fty::deffixtype ,type-name
                         :pred   ,type-p
                         :fix    ,type-fix
                         :equiv  ,type-equiv
                         :define nil)
        ))))
     

(defun def-type-fn (name args body define nneg npos)
  (met ((doc decls xbody) (defun::decompose-defun-body body))
    (met ((type-fix decls) (defun::extract-xarg-key-from-decls :type-fix decls))
      (met ((type-equiv decls) (defun::extract-xarg-key-from-decls :type-equiv decls))
        (met ((type-type-equiv decls) (defun::extract-xarg-key-from-decls :type-type-equiv decls))
          (met ((type-name decls) (defun::extract-xarg-key-from-decls :type-name decls))
            (met ((witness decls) (defun::extract-xarg-key-from-decls :type-witness decls))
              (let* ((type-witness    (if witness         (car witness)          nil))
                     (type-name       (if type-name       (car type-name)        name))
                     (type-equiv      (if type-equiv      (car type-equiv)      (symbol-fns::suffix type-name '-equiv)))
                     (type-type-equiv (if type-type-equiv (car type-type-equiv) (symbol-fns::suffix type-name '-type-equiv)))
                     (type-fix        (if type-fix        (car type-fix)        (symbol-fns::suffix type-name '-fix))))
                (met ((implies-term-forward-chaining-hints decls) (defun::extract-xarg-key-from-decls :implies-term-forward-chaining decls))
                  (met ((forward-chain-or-hints decls) (defun::extract-xarg-key-from-decls :forward-chain-or decls))
                    (met ((forward-chain-body-hints decls) (defun::extract-xarg-key-from-decls :forward-chain-body decls))
                      (met ((forward-chain-parent-hints decls) (defun::extract-xarg-key-from-decls :forward-chain-parent decls))
                        (met ((nneg-hints decls) (defun::extract-xarg-key-from-decls :no-negative decls))
                          (met ((npos-hints decls) (defun::extract-xarg-key-from-decls :no-positive decls))
                            (met ((tau-hints decls) (defun::extract-xarg-key-from-decls :tau decls))
                              (let ((guard-flag (defun::get-xarg-keys-from-decls :guard decls)))
                                (let ((decls (if (not (and guard-flag (not (car guard-flag)))) (cons `(declare (type t ,@args)) decls)
                                               (met ((guard-flag decls) (defun::extract-xarg-key-from-decls :guard decls))
                                                 (declare (ignore guard-flag))
                                                 decls))))
                                  (let ((implies-term-forward-chaining (ever-set implies-term-forward-chaining-hints))
                                        (forward-chain-parent  (ever-set forward-chain-parent-hints))
                                        (nneg (or nneg (ever-set nneg-hints)))
                                        (npos (or npos (ever-set npos-hints)))
                                        (tau-system (ever-set tau-hints))
                                        ;; forward-chain-or defaults to 'true'
                                        (forward-chain-or   (not (ever-set (not-list forward-chain-or-hints))))
                                        ;; forward-chain-body defaults to 'true'
                                        (forward-chain-body (not (ever-set (not-list forward-chain-body-hints)))))
                                    (let ((xargs (list :nneg nneg
                                                       :npos npos
                                                       :implies-term-forward-chaining implies-term-forward-chaining
                                                       :forward-chain-parent forward-chain-parent
                                                       :tau-system tau-system
                                                       :forward-chain-or forward-chain-or
                                                       :forward-chain-body forward-chain-body
                                                       )))
                                        ;(let ((xbody (acl2::beta-reduce-pseudo-termp xbody)))
                                        ;(let ((xbody (expand-implies-term xbody)))
                                        ;(let ((xbody (defung::lift-ifs-term xbody)))
                                      (let ((base (if define name (symbol-fns::prefix 'deftype-properties- name))))
                                        (let ((rules (rule-events name base `(,name ,@args) (and-or-body xbody) (and-or-type xbody) xargs)))
                                          ;; Ensure that the type of the function is boolean ..
                                          (let ((body (if (equal (and-or-type xbody) :conjunction)
                                                          (defun::make-defun-body doc decls `(and ,xbody t)) 
                                                        (defun::make-defun-body doc decls `(or ,xbody nil)))))
                                            `(encapsulate
                                                 ()
                                               (encapsulate
                                                   ()
                                                 ,@(and define `((def::un ,name ,args ,@body)))
                                                 ,@(and define `((local (in-theory (union-theories
                                                                                    '(,name)
                                                                                    (theory 'acl2::minimal-theory))))))
                                                 ,@rules
                                                 ,@(and define `((in-theory (disable ,name))))
                                                 )
                                               ,@(and witness (deftype-fty name type-name type-fix type-equiv type-type-equiv type-witness))
                                               )
                                            ))))))))))))))))))))))
    
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
