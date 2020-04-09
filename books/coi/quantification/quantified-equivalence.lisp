;;
;; Copyright (C) 2020, David Greve
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;;

;; The quant::equiv macro introduced in this book can be used to prove
;; that a universally quantified formula satisfies the properties of a
;; parameterized equivalence relation.

(in-package "QUANT")

(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "centaur/misc/beta-reduce-full" :dir :system)

(defun pseudo-term-fix-key (key term)
  (declare (type t term))
  (cond
   (key
    (if (not (consp term)) nil
      (cons (pseudo-term-fix-key nil (car term))
            (pseudo-term-fix-key key (cdr term)))))
   (t
    (cond
     ((symbolp term) term)
     ((not (consp term)) `(quote ,term))
     ((equal (car term) 'quote)
      (if (consp (cdr term)) `(quote ,(cadr term))
        nil))
     ((symbolp (car term))
      (cons (car term)
            (pseudo-term-fix-key t (cdr term))))
     ;; ((lambda (x) body) actuals)
     ((and (consp (car term))
           (let ((actuals (cdr term)))
             ;; (lambda (x) body)
             (and
              (consp (cdar term))
              ;; ((x) body)
              (let ((formals (car (cdar term))))
                (and (symbol-listp formals)
                     (equal (len formals) (len actuals))))))
           (consp (cddar term))
           ;; (body)
           )
      (cons `(lambda ,(car (cdar term)) ,(pseudo-term-fix-key nil (car (cddar term))))
            (pseudo-term-fix-key t (cdr term))))
     (t nil)))))

(defthm len-pseudo-term-fix-key-t
  (equal (len (pseudo-term-fix-key t term))
         (len term)))

(defthmd pseudo-termp-key-pseudo-term-fix-key
  (acl2::pseudo-termp-key key (pseudo-term-fix-key key term)))

(defthm pseudo-termp-pseudo-term-fix-key-nil
  (pseudo-termp (pseudo-term-fix-key nil term))
  :hints (("Goal" :use (:instance pseudo-termp-key-pseudo-term-fix-key
                                  (key nil))))
  :rule-classes (:type-prescription))
  
(defun beta-reduce-lambda-term-full (term)
  (declare (type t term))
  (let ((term (pseudo-term-fix-key nil term)))
    (acl2::beta-reduce-full term)))

(encapsulate
    (
     ((equiv-predicate * * * *) => *)
     )
  
 (local
  (defun equiv-predicate (a x y n)
    (declare (ignore a n))
    (equal x y)))

 (defthm equiv-predicate-booleanp
   (booleanp (equiv-predicate a x y n)))

 (defthm equiv-predicate-identity
   (equiv-predicate a x x n))

 (defthm equiv-predicate-symmetric
   (equal (equiv-predicate a x y n)
          (equiv-predicate a y x n)))

 (defthm equiv-predicate-transitive
   (implies (and (equiv-predicate a x y n)
                 (equiv-predicate a y z n))
            (equiv-predicate a x z n)))

 )

(defthm equiv-predicate-canary
  (list
   (equiv-predicate a x y n)
   )
  :rule-classes nil)

(defchoose equiv-predicate-witness (a) (x y n)
  (not (equiv-predicate a x y n)))

(defthm forall-equiv-predicate-witness
  (implies
   (equiv-predicate (equiv-predicate-witness x y n) x y n)
   (equiv-predicate a x y n))
  :hints (("Goal" :use equiv-predicate-witness)))

(defun equiv-predicate-quantified (x y n)
  (equiv-predicate (equiv-predicate-witness x y n) x y n))

(defthm quantified-equiv-predicate-canary
  (list
   (equiv-predicate a x y n)
   (equiv-predicate-witness x y n)
   (equiv-predicate-quantified x y n)
   )
  :rule-classes nil)

(defthm equiv-predicate-quantified-booleanp
  (booleanp (equiv-predicate-quantified x y n)))

(defthm equiv-predicate-quantified-identity
  (equiv-predicate-quantified x x n))

(defthm equiv-predicate-quantified-symmetric
  (implies
   (equiv-predicate-quantified x y n)
   (equiv-predicate-quantified y x n)))

(defthm equiv-predicate-quantified-transitive
  (implies (and (equiv-predicate-quantified x y n)
                (equiv-predicate-quantified y z n))
           (equiv-predicate-quantified x z n))
  :hints (("Goal" :in-theory (disable forall-equiv-predicate-witness)
           :use ((:instance forall-equiv-predicate-witness
                            (a (EQUIV-PREDICATE-WITNESS X Z N))
                            (x x)
                            (y y))
                 (:instance forall-equiv-predicate-witness
                            (a (EQUIV-PREDICATE-WITNESS X Z N))
                            (x y)
                            (y z))
                 ))))

(defun macro-cons (x y)
  (declare (type t x))
  `(cons ,x ,y))

(defun macro-quote (x)
  (declare (type t x))
  `(quote ,x))

(mutual-recursion

 (defun macroize-args (args)
   (declare (xargs :guard (pseudo-term-listp args)))
   (if (not (consp args)) nil
     (macro-cons (macroize (car args))
                 (macroize-args (cdr args)))))

 (defun macroize (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (consp term)
       (cond
        ((equal (car term) 'quote)
         (macro-quote term))
        (t 
         (macro-cons (macro-quote (car term))
                     (macroize-args (cdr term)))))
     term))

 )

(defun unbound (x)
  (declare (type t x))
  (or (not x) (equal x acl2::*nil*)))
      
(defun subset (x y)
  (declare (xargs :guard (and (symbol-listp x)
                              (symbol-listp y))))
  (if (not (consp x)) t
    (and (member (car x) y)
         (subset (cdr x) y))))

(defun perm (x y)
  (declare (xargs :guard (and (symbol-listp x)
                              (symbol-listp y))))
  (and (subset x y)
       (subset y x)))

(defun subs (alist list)
  (declare (type (satisfies alistp) alist))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (let ((hit (assoc-equal entry alist)))
        (if hit (cons (cdr hit)
                      (subs alist (cdr list)))
          (cons (car list) (subs alist (cdr list))))))))

(defun into-args-rec (args index x)
  (declare (type integer index))
  (if (not (consp args)) nil
    (cons `(nth ,index ,x)
          (into-args-rec (cdr args) (1+ index) x))))

(defthm true-listp-into-args-rec
  (true-listp (into-args-rec args index x)))

;; Note: this differs from the version in
;; quantified-congruence (!) .. not sure
;; why the added complexity there?
(defun into-args (args x)
  (declare (type (satisfies symbol-listp) args))
  (into-args-rec args 0 x))

(defthm true-listp-into-args
  (true-listp (into-args args x)))

(in-theory (disable into-args))

(local
 (defthm alistp-pairlis$
   (alistp (PAIRLIS$ x y))))

(local
 (defthm alistp-append
   (implies
    (and (alistp x) (alistp y))
    (alistp (append x y)))))

(local
 (defthm symbol-listp-append
   (implies
    (and (symbol-listp x) (symbol-listp y))
    (symbol-listp (append x y)))))

(defun duplicate (n expr)
  (declare (type (integer 0 *) n))
  (if (zp n) nil
    (cons expr (duplicate (1- n) expr))))

(defun quantified-equiv-fn (name vars args parms formals equiv-predicate quantifier)
  (declare (type symbol name)
           (type (satisfies symbol-listp) vars args parms formals)
           (type (satisfies pseudo-termp) equiv-predicate)
           (ignorable quantifier)
           (xargs :guard (and (equal quantifier :forall)
                              (equal (len args) 2)
                              (or (unbound formals) (perm formals (append args parms))))))
  (let* ((formals (if (unbound formals) (append args parms) formals))
         (parms  (if (unbound parms) nil parms))
         (x (nth 0 args))
         (y (nth 1 args))
         (equiv-predicate-booleanp   (acl2::packn-pos (list name '-booleanp) name))
         (equiv-predicate-identity   (acl2::packn-pos (list name '-identity) name))
         (equiv-predicate-symmetric  (acl2::packn-pos (list name '-symmetric) name))
         (equiv-predicate-transitive (acl2::packn-pos (list name '-transitive) name))
         (equiv-predicate-witness    (acl2::packn-pos (list name '-witness) name))
         (pformals       (append vars formals))
         (equiv-predicate      `(lambda ,pformals ,equiv-predicate))
         (pformals-x     (subs `((,x . x)
                                 (,y . y)
                                 ,@(pairlis$ vars (into-args vars 'a))
                                 ,@(pairlis$ parms (into-args parms 'n)))
                               pformals))
         (formals-x      (subs `((,x . x)
                                 (,y . y)
                                 ,@(pairlis$ parms (into-args parms 'n)))
                               formals))
         (n-x                    `(list ,@parms))
         ;(a-x                    `(list ,@vars))
         (equiv-predicate-x            `(lambda (a x y n) ,(beta-reduce-lambda-term-full `((lambda (a x y n) (,equiv-predicate ,@pformals-x)) a x y n))))
         (equiv-predicate-witness-x    `(lambda (x y n) (list ,@(duplicate (len vars) `(,equiv-predicate-witness ,@formals-x)))))
         (equiv-predicate-quantified-x `(lambda (x y n) (,name ,@formals-x)))
         (finst `((equiv-predicate            ,equiv-predicate-x)
                  (equiv-predicate-witness    ,equiv-predicate-witness-x)
                  (equiv-predicate-quantified ,equiv-predicate-quantified-x)))
         (inst  `(;(a ,a-x)
                  (n ,n-x)
                  (x ,x)
                  (y ,y)))
         )
    `(encapsulate
         ()

       (local (in-theory (disable nth)))
       (local (in-theory (enable ,name)))
       
       (local
        (defthm predicate-canary
          t
          :rule-classes nil
          :otf-flg t
          :hints (("Goal" :use (:functional-instance equiv-predicate-canary
                                                     ,@finst)))))

       (local
        (defthm quantified-predicate-canary
          t
          :rule-classes nil
          :otf-flg t
          :hints (("Goal" :use (:functional-instance quantified-equiv-predicate-canary
                                                     ,@finst)))))

       (defthm ,equiv-predicate-booleanp
         (booleanp (,name ,@formals))
         :hints (("Goal" :use (:functional-instance (:instance equiv-predicate-quantified-booleanp
                                                               ,@inst
                                                               )
                                                    ,@finst))))
    
       (defthm ,equiv-predicate-identity
         (,name ,@(subs `((,y . ,x)) formals))
         :hints (("Goal" :use (:functional-instance (:instance equiv-predicate-quantified-identity
                                                               ,@(remove-assoc 'y inst))
                                                    ,@finst))))
       
       (defthm ,equiv-predicate-symmetric
         (implies
          (,name ,@formals)
          (,name ,@(subs `((,x . ,y) (,y . ,x)) formals)))
         :hints (("Goal" :use (:functional-instance (:instance equiv-predicate-quantified-symmetric
                                                               ,@inst
                                                               )
                                                    ,@finst))))
       
       (defthm ,equiv-predicate-transitive
         (implies (and (,name ,@formals)
                       (,name ,@(subs `((,x . ,y) (,y . z)) formals)))
                  (,name ,@(subs `((,y . z)) formals)))
         :hints (("Goal" :use (:functional-instance (:instance equiv-predicate-quantified-transitive
                                                               ,@inst
                                                               )
                                                    ,@finst))))

       ,@(and (unbound parms) `((defequiv ,name)))
       
       )))

(defun decompose-quantified-formula (expr)
  (declare (type t expr))
  (case-match expr
    ((`forall vars expr) (mv :forall vars expr))
    ((`exists vars expr) (mv :exists vars expr))
    (&                   (mv nil nil expr))))

(defmacro equiv (name args parms body &key (formals 'nil))
  (mv-let (quantifier vars equiv-predicate) (decompose-quantified-formula body)
    `(make-event
      (let ((name   ',name)
            (vars   ',vars)
            (args   ',args)
            (parms  ',parms)
            (formals   ',formals)
            (equiv-predicate ',equiv-predicate)
            (quantifier ',quantifier))
        (mv-let (flg equiv-predicate) (acl2::pseudo-translate equiv-predicate nil (w state))
          (declare (ignore flg))
          (quantified-equiv-fn name vars args parms formals equiv-predicate quantifier))))))

(local
 (encapsulate
     ()

   (defun foo-pred (x k a y n b)
     (declare (ignore k a n b))
     (equal x y))
   
   (defun-sk foo (x k y n)
     (forall (a b) (foo-pred x k a y n b)))
   
   (quant::equiv foo (x y) (k n)
     (forall (a b) (foo-pred x k a y n b))
     :formals (x k y n))

   (in-theory (disable foo))
   
   (defthm equivalance-relation-properties
     (and
      (booleanp (foo x k y n))
      (foo x k x n)
      (implies
       (foo x k y n)
       (foo y k x n))
      (implies
       (and
        (foo x k y n)
        (foo y k z n))
       (foo x k z n))))

   ))
   
(acl2::defxdoc quant::equiv
  :short "A macro to prove that a universally quantified formula is a paramaterized equivalence relation"
  :parents (defun-sk defequiv)
  :long "<p> 
The @('quant::equiv') macro can be used to prove that a universally
quantified formula satisfies the properties of a parameterized
equivalence relation.  This macro is similar in nature to @(tsee
def-universal-equiv) except that parameterized equivalences are
supported.  If no paramaters are specified, however, we prove that the
quantified formula is in fact a standard @(tsee equivalence) relation.
</p> 
<p>Usage:</p> @({
  (include-book \"coi/quantification/quantified-equivalence\" :dir :system)
               
  (defun foo-pred (x k a y n b)
    (declare (ignore k a n b))
    (equal x y))

  (defun-sk foo (x k y n)
    (forall (a b) (foo-pred x k a y n b)))

  ;; The first argument is the name of the quantified formula.
  ;; The first argument list specifies the \"equivalent\" arguments
  ;; The second argument list specifies the parameters
  (quant::equiv foo (x y) (k n)
    ;; Repeat the body from the defun-sk event
    (forall (a b) (foo-pred x k a y n b))
    ;; Since the formals to the actual quantified formula 
    ;; are not (x y k n) as we would otherwise assume from
    ;; the arguments above we must specifify the actual
    ;; order of the formal arguments.
    :formals (x k y n))

  (in-theory (disable foo))

  ;; This now proves automatically
  (defthm equivalance-relation-properties
     (and
      (booleanp (foo x k y n))
      (foo x k x n)
      (implies
       (foo x k y n)
       (foo y k x n))
      (implies
       (and
        (foo x k y n)
        (foo y k z n))
       (foo x k z n))))

})
")
