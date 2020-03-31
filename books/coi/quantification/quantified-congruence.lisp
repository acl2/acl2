;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "QUANT")

(include-book "misc/beta-reduce" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "xdoc/top" :dir :system)

(defun beta-reduce-lambda-term (term)
  (declare (type (satisfies acl2::pseudo-termp) term))
  (if (acl2::lambda-expr-p term)
      (acl2::beta-reduce-lambda-expr term)
    term))

(encapsulate
    (
     ((relation * *) => *)
     ((relation-witness *) => *)
     )
  
  (local (defund relation (x y) (equal x y)))
  (local
   (defchoose relation-witness (a)
     (x)
     (relation a x)
     :strengthen t))

  (defthm strong-relation-witness
    (or (equal (relation-witness x)
               (relation-witness x1))
        (and (relation (relation-witness x) x)
             (not (relation (relation-witness x) x1)))
        (and (relation (relation-witness x1) x1)
             (not (relation (relation-witness x1) x))))
    :hints (("goal" :use relation-witness))
    :rule-classes nil)
  
  )

(defthm strong-relation-witness-property
  (or (equal (relation-witness x)
             (relation-witness x1))
      (and (relation (relation-witness x) x)
           (not (relation (relation-witness x) x1)))
      (and (relation (relation-witness x1) x1)
           (not (relation (relation-witness x1) x))))
  :rule-classes nil
  :hints (("Goal" :use strong-relation-witness)))

(encapsulate
    (
     ((relation-hyps *) => *)
     ((relation-equiv * *) => *)
     )
  
  (local (defun relation-hyps (x) (declare (ignore x)) nil))
  (local (defun relation-equiv (x y) (equal x y)))
  
  (defthm essential-congruence
    (implies
     (and
      (relation-hyps x)
      (relation-equiv x y))
     (iff (relation a x)
          (relation a y))))

  )

(defthm relation-witness-congruence
  (implies
   (and
    (relation-hyps x)
    (relation-equiv x y))
   (equal (relation-witness x)
          (relation-witness y)))
  :hints (("Goal" :use (:instance strong-relation-witness-property
                                  (x1 y)))))

(defun number-symbol (x base)
  (declare (type symbol x base))
  (intern-in-package-of-symbol
   (coerce
    (acl2::packn1 (list x 1))
    'string)
   base))

(defthm symbolp-number-symbol
  (implies
   (and (symbolp x) (symbolp base))
   (symbolp (number-symbol x base))))

(in-theory (disable number-symbol))

(local
 (defthm symbol-listp-implies-true-listp
   (implies
    (symbol-listp list)
    (true-listp list))
   :rule-classes (:forward-chaining)))

(defun number-symbol-list (list base)
  (declare (type (satisfies symbol-listp) list)
           (type symbol base))
  (if (not (consp list)) nil
    (cons (number-symbol (car list) base)
          (number-symbol-list (cdr list) base))))

(defthm symbol-listp-number-symbol-list
  (implies
   (and (symbol-listp x) (symbolp base))
   (symbol-listp (number-symbol-list x base))))

(defun make-binding-out-rec (args args1 index x x1)
  (declare (type integer index))
  (if (not (and (consp args) (consp args1))) nil
    (cons `(,(car args)  (nth ,index ,x))
    (cons `(,(car args1) (nth ,index ,x1))
          (make-binding-out-rec (cdr args) (cdr args1) (1+ index) x x1)))))

(defthm true-listp-make-binding-out-rec
  (true-listp (make-binding-out-rec args args1 index x x1)))

(defun make-binding-out (args args1 x x1)
  (declare (type (satisfies symbol-listp) args args1))
  (if (equal (len args) 1)
      `((,(nth 0 args)  ,x)
        (,(nth 0 args1) ,x1))
    (make-binding-out-rec args args1 0 x x1)))

(defthm true-listp-make-binding-out
  (true-listp (make-binding-out args args1 x x1)))

(in-theory (disable make-binding-out))

(defun make-binding-into (x x1 args args1)
  (declare (type (satisfies symbol-listp) args args1))
  (if (equal (len args) 1)
      `((,x  ,(nth 0 args))
        (,x1 ,(nth 0 args1)))
    `((,x  (list ,@args))
      (,x1 (list ,@args1)))))

(defthm true-listp-make-binding-into
  (true-listp (make-binding-into x x1 args args1)))

(in-theory (disable make-binding-into))

(defun lambda-term-p (term)
  (declare (type t term))
  (case-match term
    (('lambda a ('declare &) b) (and (symbol-listp a)
                                     (pseudo-termp b)))
    (('lambda a b) (and (symbol-listp a)
                        (pseudo-termp b)))
    (& nil)))

(defun into-args-rec (args index x)
  (declare (type integer index))
  (if (not (consp args)) nil
    (cons `(nth ,index ,x)
          (into-args-rec (cdr args) (1+ index) x))))

(defthm true-listp-into-args-rec
  (true-listp (into-args-rec args index x)))

(defun into-args (args x)
  (declare (type (satisfies symbol-listp) args))
  (if (equal (len args) 1)
      `(,x)
    (into-args-rec args 0 x)))

(defthm true-listp-into-args
  (true-listp (into-args args x)))

(in-theory (disable into-args))

(defthm open-nth
  (equal (nth a (cons b x))
         (if (zp a) b
           (nth (1- a) x))))

(defun good-congruence-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((congruence (car list)))
      (and (consp congruence)
           (symbolp (car congruence))
           (consp (cdr congruence))
           (symbolp (cadr congruence))
           (null (cddr congruence))
           (good-congruence-listp (cdr list))))))

(defthm good-congruence-listp-implies-alistp
  (implies
   (good-congruence-listp list)
   (alistp list))
  :rule-classes (:forward-chaining))

(defthm assoc-good-congruence-listp
  (implies
   (and
    (good-congruence-listp list)
    (assoc-equal key list))
   (and
    (consp (assoc-equal key list))
    (consp (cdr (assoc-equal key list)))
    (symbolp (cadr (assoc-equal key list)))))
  :rule-classes (:forward-chaining))
     
(defun symbol-pairlistp (pairlist)
  (declare (type t pairlist))
  (if (not (consp pairlist)) (null pairlist)
    (let ((entry (car pairlist)))
      (and (consp entry)
           (symbolp (car entry))
           (symbolp (cdr entry))
           (symbol-pairlistp (cdr pairlist))))))

(defthm symbol-pairlistp-pairlis$
  (implies
   (and
    (symbol-listp x)
    (symbol-listp y))
   (symbol-pairlistp (pairlis$ x y))))

(defun make-equiv-body (pairlist congruences)
  (declare (type (satisfies good-congruence-listp) congruences)
           (type (satisfies symbol-pairlistp) pairlist))
  (if (not (consp pairlist)) nil
    (let ((pair (car pairlist)))
      (let ((arg1 (car pair))
            (arg2 (cdr pair)))
        (let ((hit (assoc arg1 congruences)))
          (let ((equiv (if (not hit) `(equal ,arg1 ,arg2)
                         `(,(cadr hit) ,arg1 ,arg2))))
            (cons equiv (make-equiv-body (cdr pairlist) congruences))))))))

(defun make-binding (keys vals)
  (declare (type t keys vals))
  (if (not (and (consp keys) (consp vals))) nil
    (cons (list (car keys) (car vals))
          (make-binding (cdr keys) (cdr vals)))))

(defun make-congruences-rec (lemma fn n iff parg0 arg0 narg0 parg1 arg1 narg1 congruences)
  (declare (xargs :ruler-extenders :all)
           (type symbol fn iff arg0 arg1)
           (type integer n)
           (type (satisfies symbol-listp) parg0 parg1 narg0 narg1)
           (type (satisfies good-congruence-listp) congruences)
           )
  (let ((res (if (not (consp narg0)) nil
               (make-congruences-rec lemma fn (1+ n) iff
                                     (cons arg0 parg0) (car narg0) (cdr narg0)
                                     (cons arg1 parg1) (car narg1) (cdr narg1)
                                     congruences))))
    (let ((hit (assoc arg0 congruences)))
      (if (not hit) res
        (let ((equiv (cadr hit)))
          (let ((name (acl2::packn-pos (list equiv '- n '-implies- iff '- fn) fn)))
          (cons `(defthm ,name
                   (implies
                    (,equiv ,arg0 ,arg1)
                    (,iff (,fn ,@parg0 ,arg0 ,@narg0)
                          (,fn ,@parg0 ,arg1 ,@narg0)))
                   ,@(and lemma
                          `(:hints (("Goal" :use (:instance ,lemma
                                                            ,@(make-binding (append parg1 narg1)
                                                                            (append parg0 narg0)))))))
                   :rule-classes (:congruence))
                res)))))))

(defun make-congruences (lemma fn iff arg0 arg1 congruences)
  (declare (type symbol fn iff)
           (type (satisfies symbol-listp) arg0 arg1)
           (type (satisfies good-congruence-listp) congruences))
  (if (consp arg0) 
      (make-congruences-rec lemma fn 1 iff nil (car arg0) (cdr arg0) nil (car arg1) (cdr arg1) congruences)
    nil))

(defun all-congruences-apply-to-args (congruences args)
  (declare (type (satisfies good-congruence-listp) congruences)
           (type (satisfies symbol-listp) args))
  (if (not (consp congruences)) t
    (let ((congruence (car congruences)))
      (let ((name (car congruence)))
        (and (member-equal name args)
             (all-congruences-apply-to-args (cdr congruences) args))))))

(defun prove-quantified-congruence-fn (name a args args1 relation hyps congruences quantifier suffix iff hints)
  (declare (type symbol name a quantifier suffix)
           (type (satisfies symbol-listp) args)
           (type (satisfies symbol-listp) args1)
           (type (satisfies pseudo-termp) relation)
           (type (satisfies good-congruence-listp) congruences)
           (xargs :guard (and (or (not hyps) (pseudo-termp hyps))
                              (and congruences (not (equal congruences acl2::*nil*)))
                              (all-congruences-apply-to-args congruences args))))
  (let* (;(x                           (acl2::packn-pos (list "X") name))
         ;(y                           (acl2::packn-pos (list "Y") name))
         (hyps                        (if (not hyps) nil (if (equal hyps acl2::*nil*) nil hyps)))
         (iff                         (if iff 'iff 'equal))
         (relation-congruence         (acl2::add-suffix name (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (relation-witness            (acl2::add-suffix name "-WITNESS"))
         (relation-witness-congruence (acl2::add-suffix relation-witness   (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (relation-rule               (acl2::add-suffix relation-witness   "-STRENGTHEN"))
         (relation-witness-canary     (acl2::add-suffix relation-witness   "-CANARY"))
         (relation-raw                `(lambda (,a ,@args) ,relation))
         (relation                    (if (equal quantifier :exists) relation-raw `(lambda (,a ,@args) (not (,relation-raw ,a ,@args)))))
         (a1                          (acl2::packn-pos (list a 1) 'quant::prove-quantified-congruence-fn))
         (local-relation              (acl2::packn-pos (list name '-relation) 'quant::prove-quantified-congruence-fn))
         (local-definition            (acl2::packn-pos (list name '-definition) 'quant::prove-quantified-congruence-fn))
         (relation-equiv              (acl2::packn-pos (list name '-equiv) 'quant::prove-quantified-congruence-fn))
         (relation-hyps-x            `(lambda (x) ((lambda (,@args) (declare (ignorable ,@args)) ,(or hyps t)) ,@(into-args args 'x))))
         (relation-equiv-x           `(lambda (x y) (,relation-equiv ,@(into-args args 'x) ,@(into-args args 'y))))
         (relation-x                 `(lambda (a x) (,relation a ,@(into-args args 'x))))
         (relation-x-witness         `(lambda (x) (,relation-witness ,@(into-args args 'x))))
         )    
    `(encapsulate
         ()

       (local (in-theory (disable nth)))

       (local
        (defun ,local-relation (,a ,@args)
          (declare (ignorable ,@args))
          (,relation-raw ,a ,@args)))
       
       (local
        (encapsulate
            ()
          ,@(make-congruences nil local-relation iff (cons a args) (cons a1 args1) congruences)
          ))
       
       (local
        (defthm ,local-definition
          (equal (,name ,@args)
                 (,local-relation (,relation-witness ,@args) ,@args))
          :hints (("Goal" :in-theory (enable ,name)))))
       
       (local (in-theory (disable ,name ,local-relation ,local-definition)))

       (defun ,relation-equiv (,@args ,@args1)
         (and ,@(make-equiv-body (pairlis$ args args1) congruences)))
       
       (defthm ,relation-witness-canary
         (or (equal (,relation-witness ,@args)
                    (,relation-witness ,@args1))
             (and (,relation (,relation-witness ,@args) ,@args)
                  (not (,relation (,relation-witness ,@args) ,@args1)))
             (and (,relation (,relation-witness ,@args1) ,@args1)
                  (not (,relation (,relation-witness ,@args1) ,@args))))
         :rule-classes nil
         :hints (("Goal" :in-theory (append '((zp) open-nth) (theory 'minimal-theory))
                  :use (:functional-instance (:instance strong-relation-witness-property
                                                        ,@(make-binding-into 'x 'x1 args args1))
                                             (relation-hyps    ,relation-hyps-x)
                                             (relation-equiv   ,relation-equiv-x)
                                             (relation-witness ,relation-x-witness)
                                             (relation ,relation-x)
                                             ))
                 (and stable-under-simplificationp
                      '(:use (:instance ,relation-rule
                                        ,@(make-binding-out args args1 'x 'x1))))))
       
       (defthm ,relation-witness-congruence
         (implies
          (and
           ,(or hyps t)
           (,relation-equiv ,@args ,@args1))
          (equal (,relation-witness ,@args)
                 (,relation-witness ,@args1)))
         :rule-classes nil
         :hints (("Goal" :use (:functional-instance (:instance relation-witness-congruence
                                                               ,@(make-binding-into 'x 'y args args1))
                                                    (relation-hyps    ,relation-hyps-x)
                                                    (relation-equiv   ,relation-equiv-x)
                                                    (relation-witness ,relation-x-witness)
                                                    (relation         ,relation-x)))
                 ,@hints))
       
       (defthm ,relation-congruence
         (implies
          (and
           ,(or hyps t)
           (,relation-equiv ,@args ,@args1))
          (,iff (,name ,@args)
                (,name ,@args1)))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable ,local-definition)
                  :use ,relation-witness-congruence)
                 ,@hints))

       (local (in-theory (union-theories '(,relation-equiv) (theory 'acl2::minimal-theory))))

       ,@(and (not hyps) (make-congruences relation-witness-congruence relation-witness 'equal args args1 congruences))
       ,@(and (not hyps) (make-congruences relation-congruence name iff args args1 congruences))
       
       )))
     
(defun decompose-quantified-formula (expr)
  (declare (type t expr))
  (case-match expr
    ((`forall vars expr) (mv :forall vars expr))
    ((`exists vars expr) (mv :exists vars expr))
    (&                   (mv nil nil expr))))

(defun acl2::pseudo-translate-lambda (fn fn-args-lst wrld)
  (declare (xargs :mode :program))
  (if (symbolp fn) (mv t fn nil)
    (case-match fn
      (('lambda args &)
       (mv-let (flg term) (acl2::pseudo-translate `(,fn ,@args) fn-args-lst wrld)
         (case-match term
           ((('lambda formals body) . &)
            (mv flg `(lambda ,formals ,body) (nthcdr (len args) formals)))
           (& (mv nil fn nil)))))
      (& (mv nil fn nil)))))

(defmacro congruence (name args body &key (suffix '||) (hyps 'nil) (congruences 'nil) (iff 'nil) (hints 'nil))
  (mv-let (quantifier vars relation) (decompose-quantified-formula body)
    `(make-event
      (let ((name   ',name)
            (a      ',(car vars))
            (args   ',args)
            (hyps   ',hyps)
            (congruences ',congruences)
            (suffix ',suffix)
            (relation ',relation)
            (quantifier ',quantifier)
            (iff   ',iff)
            (hints ',hints)
            )
        (mv-let (flg relation) (acl2::pseudo-translate relation nil (w state))
          (declare (ignore flg))
          (mv-let (flg hyps) (acl2::pseudo-translate hyps nil (w state))
            (declare (ignore flg))
            (let ((args1 (acl2::generate-variable-lst-simple args (cons a args))))
              (prove-quantified-congruence-fn name a args args1 relation hyps congruences quantifier suffix iff hints))))))
    ))

(local
 (encapsulate
     ()

   (defun my-member (a x)
     (member a x))

   (defun-sk fred (z)
     (exists (a) (my-member a z))
     :strengthen t)

   (defun member-equalx (x y)
     (equal x y))

   (defequiv member-equalx)

   (defcong member-equalx iff (my-member a x) 2)

   (in-theory (disable my-member (my-member) member-equalx))

   (quant::congruence fred (z)
     (exists (a) (my-member a z))
     :congruences ((z member-equalx))
     ;; In some cases, the congruence may only be conditional.
     :hyps (true-listp z)
     ;; The quantified predicate may not be strictly Boolean
     ;; If that is so, set the :iff flag to t
     :iff t
     )

   ;; We don't actually get ACL2 congruence rules in this case
   ;; but we do get the following properties ..
   
   (defthmd fred-witness-congruence-result1
     (implies (and (true-listp z)
                   (member-equalx z z1))
              (equal (fred-witness z)
                     (fred-witness z1)))
     :hints (("goal" :use fred-witness-congruence)))
      
   (defthm fred-congruence-result2
     (implies (and (true-listp z)
                   (member-equalx z z1))
              (iff (fred z) (fred z1)))
     :hints (("goal" :use fred-congruence)))

   ))

(local
 (encapsulate
     ()

   (encapsulate
       (
        ((pred * * *) => *)
        ((pred-equiv * *) => *)
        )

     (local
      (defun pred-equiv (x y)
        (equal x y)))

     (defequiv pred-equiv)

     (local
      (defun pred (a x y)
        (declare (ignore a x y))
        t))
     
     (defcong pred-equiv equal (pred a x y) 2)
     
     )

   (local
    (encapsulate
        ()
     
     (local
      (encapsulate
          ()
        
        ;; Existentially quantified
        ;; The :strengthen t argument is required.
        (defun-sk quantified-pred (v z)
          (exists (a) (pred a v z))
          :strengthen t)
        
        (quant::congruence quantified-pred (v z)
          (exists (a) (pred a v z))
          :congruences ((v pred-equiv))
          )

        ;; The following congruences now follow naturally ..
        (defthmd test1
          (implies
           (pred-equiv v1 v2)
           (equal (quantified-pred-witness v1 z)
                  (quantified-pred-witness v2 z))))
        
        
        (defthmd test2
          (implies
           (pred-equiv v1 v2)
           (equal (quantified-pred v1 z)
                  (quantified-pred v2 z))))

        
       ))
     ))

   (local
    (encapsulate
        ()
     
     (local
      (encapsulate
          ()
               
        ;; Universally quantified
        ;; The :strengthen t argument is required.
        (defun-sk quantified-pred (v z)
          (forall (a) (pred a v z))
          :strengthen t)
        
        (quant::congruence quantified-pred (v z)
          (forall (a) (pred a v z))
          :congruences ((v pred-equiv)))
       
        ;; The following congruences now follow naturally ..
        (defthmd test1
          (implies
           (pred-equiv v1 v2)
           (equal (quantified-pred-witness v1 z)
                  (quantified-pred-witness v2 z))))
                  
                
        (defthmd test2
          (implies
           (pred-equiv v1 v2)
           (equal (quantified-pred v1 z)
                  (quantified-pred v2 z))))
                
        ))))
   
   ))


(acl2::defxdoc quant::congruence
  :short "A macro to prove congruence rules for quantified formulae and their associated witnesses"
  :parents (acl2::defun-sk)
  :long "<p> 
The @('quant::congruence') macro can be used to prove
@(tsee acl2::congruence) rules for quantified formulae and their associated
witnesses introduced using @(tsee acl2::defun-sk).  Note: this macro only
works for formula that are introduced with the :strengthen t keyword.
</p> 
<p>Usage:</p> @({
  (include-book \"coi/quantification/quantified-congruence\" :dir :system)
               
  ;; Given a predicate that satisfies some congruence
  (defcong pred-equiv equal (pred a x y) 2)

  ;; A quantified formula involving pred introduced using
  ;; defun-sk with the :strengthen t option.
  (defun-sk quantified-pred (v z)
    (forall (a) (pred a v z))
    :strengthen t)

  ;; We prove congruence rules relative to 'v'
  (quant::congruence quantified-pred (v z)
    (forall (a) (pred a v z))
    :congruences ((v pred-equiv)))
  
  ;; The following lemmas now follow directly ..
  (defthmd witness-congruence
    (implies
     (pred-equiv v1 v2)
     (equal (quantified-pred-witness v1 z)
            (quantified-pred-witness v2 z))))
            
          
  (defthmd quantified-congruence
    (implies
     (pred-equiv v1 v2)
     (equal (quantified-pred v1 z)
            (quantified-pred v2 z))))
                
 })

")
