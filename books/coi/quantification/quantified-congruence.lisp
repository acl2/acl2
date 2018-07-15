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
     ((relation-hyps * *) => *)
     )
  
  (local (defun relation-hyps (x y) (equal x y)))
  
  (defthm essential-congruence
    (implies
     (relation-hyps x y)
     (iff (relation a x)
          (relation a y))))

  )

(defthm relation-witness-congruence
  (implies
   (relation-hyps x y)
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

(defun prove-quantified-congruence-fn (name a args relation hyps free quantifier suffix iff rule-classes hints)
  (declare (type symbol name a quantifier suffix)
           (type (satisfies symbol-listp) args free)
           (type (satisfies pseudo-termp) relation)
           (xargs :guard (or (symbolp hyps) (lambda-term-p hyps))))
  (let* ((relation-congruence         (acl2::add-suffix name (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (relation-witness            (acl2::add-suffix name "-WITNESS"))
         (relation-witness-congruence (acl2::add-suffix relation-witness   (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (relation-rule               (acl2::add-suffix relation-witness   "-STRENGTHEN"))
         (relation-witness-canary     (acl2::add-suffix relation-witness   "-CANARY"))
         (relation                    `(lambda (,a ,@args) ,relation))
         (relation                    (if (equal quantifier :exists) relation `(not (,relation ,@args))))
         (args1                       (number-symbol-list args name))
         (hyps-x                      `(lambda (x y) (,hyps ,@(into-args args 'x) ,@(into-args args 'y) ,@free)))
         (hyps                        (with-guard-checking :none (ec-call (beta-reduce-lambda-term `(,hyps ,@args ,@args1 ,@free)))))
         (relation-x                  `(lambda (a x) (,relation a ,@(into-args args 'x))))
         (relation-x-witness          `(lambda (x) (,relation-witness ,@(into-args args 'x))))
         )
    `(encapsulate
         ()
       
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
                                             (relation ,relation-x)
                                             (relation-witness ,relation-x-witness)))
                 (and stable-under-simplificationp
                      '(:use (:instance ,relation-rule
                                        ,@(make-binding-out args args1 'x 'x1))))))
       
       (defthm ,relation-witness-congruence
         (implies
          ,hyps
          ,(let ((eq `(equal (,relation-witness ,@args)
                             (,relation-witness ,@args1))))
             (if iff `(iff ,eq t) eq)))
         :rule-classes ,rule-classes
         :hints (("Goal" :use (:functional-instance (:instance relation-witness-congruence
                                                               ,@(make-binding-into 'x 'y args args1))
                                                    (relation-hyps    ,hyps-x)
                                                    (relation-witness ,relation-x-witness)
                                                    (relation         ,relation-x)))
                 ,@hints))
       
       (defthm ,relation-congruence
         (implies
          ,hyps
          ,(let ((eq `(iff (,name ,@args)
                           (,name ,@args1))))
             (if iff `(iff ,eq t) eq)))
         :rule-classes ,rule-classes
         :hints (("Goal" :in-theory (e/d (,name) (,@(and rule-classes `(,relation-witness-congruence))))
                  :use ,relation-witness-congruence)
                 ,@hints))
       
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

(defmacro congruence (name args body &key (suffix '||) (hyps '(lambda (x y) t)) (iff 'nil) (rule-classes 'nil) (hints 'nil))
  (mv-let (quantifier vars relation) (decompose-quantified-formula body)
    `(make-event
      (let ((name   ',name)
            (a      ',(car vars))
            (args   ',args)
            (hyps   ',hyps)
            (suffix ',suffix)
            (relation ',relation)
            (quantifier ',quantifier)
            (rule-classes ',rule-classes)
            (iff   ',iff)
            (hints ',hints)
            )
        (mv-let (flg relation) (acl2::pseudo-translate relation nil (w state))
          (declare (ignore flg))
          (mv-let (flg hyps free) (acl2::pseudo-translate-lambda hyps nil (w state))
            (declare (ignore flg))
            (prove-quantified-congruence-fn name a args relation hyps free quantifier suffix iff rule-classes hints))))
      )))

(local
 (encapsulate
     ()

   (defun-sk fred (z)
     (exists (a) (member a z))
     :strengthen t)

   (defun member-equalx (x y)
     (equal x y))

   (defequiv member-equalx)

   (defcong member-equalx iff (member-equal a x) 2)

   (in-theory (disable member-equalx))

   (congruence fred (z)
     (exists (a) (member a z))
     :hyps member-equalx
     :rule-classes (:congruence)
     )

   ))



(local
 (encapsulate
     ()

   (defun-sk bread (v z)
     (exists (a) (member a (cons v z)))
     :strengthen t)

   (congruence bread (v z)
     (exists (a) (member a (cons v z)))
     :hyps (lambda (v1 z1 v2 z2) (and (equal v1 v2)
                                      (equal z1 z2)))
     )

   ))
