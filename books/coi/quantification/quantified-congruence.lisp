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
(include-book "quantified-equivalence")

(defstub quantification-key-witness () nil)

(encapsulate
    (
     ((congruent-predicate * *) => *)
     ((congruent-predicate-witness *) => *)
     ((universally-quantified) => *)
     )
  (local (defun universally-quantified ()
           (quantification-key-witness)))
  (local (defund congruent-predicate (x y) (equal x y)))
  (local
   (defun-sk forall-predicate (x)
     (forall (a) (congruent-predicate a x))
     :strengthen t))
  (local
   (defun-sk exists-predicate (x)
     (exists (a) (congruent-predicate a x))
     :strengthen t))
  (local
   (defun congruent-predicate-witness (x)
     (if (universally-quantified) (forall-predicate-witness x)
       (exists-predicate-witness x))))
  
  (defthm existential-constraint
    (implies
     (not (universally-quantified))
     (and (implies (congruent-predicate a x)
                   (congruent-predicate (congruent-predicate-witness x) x))
          (or (equal (congruent-predicate-witness x)
                     (congruent-predicate-witness x1))
              (let ((a (congruent-predicate-witness x)))
                   (and (congruent-predicate a x)
                        (not (let ((x x1))
                                  (congruent-predicate a x)))))
              (let ((a (congruent-predicate-witness x1)))
                   (and (let ((x x1)) (congruent-predicate a x))
                        (not (congruent-predicate a x)))))))
    :hints (("goal" :use (exists-predicate-suff
                          exists-predicate-witness-strengthen))))

  (defthm universal-constratint
    (implies
     (universally-quantified)
     (and (implies (not (congruent-predicate a x))
                   (not (congruent-predicate (congruent-predicate-witness x) x)))
          (or (equal (congruent-predicate-witness x)
                     (congruent-predicate-witness x1))
              (let ((a (congruent-predicate-witness x)))
                   (and (not (congruent-predicate a x))
                        (not (let ((x x1))
                                  (not (congruent-predicate a x))))))
              (let ((a (congruent-predicate-witness x1)))
                   (and (let ((x x1))
                             (not (congruent-predicate a x)))
                        (not (not (congruent-predicate a x))))))))
    :hints (("goal" :use (forall-predicate-necc
                          forall-predicate-witness-strengthen))))
  
  )

(defun iff-equiv (x y)
  (iff x y))

(defequiv iff-equiv)

(encapsulate
    (
     ((congruent-predicate-hyps *) => *)
     ((congruent-predicate-relation * *) => *)
     ((congruent-predicate-equiv * *) => *)
     )
  
  (local (defun congruent-predicate-hyps (x) (declare (ignore x)) nil))
  (local (defun congruent-predicate-relation (x y) (declare (ignore x y)) nil))
  (local (defun congruent-predicate-equiv (x y) (equal x y)))
  
  (defthm essential-congruence
    (implies
     (and
      (congruent-predicate-hyps x)
      (congruent-predicate-relation x y)
      (congruent-predicate-equiv x y))
     (iff-equiv (congruent-predicate a x)
                (congruent-predicate a y))))

  )

(defthm congruent-predicate-witness-congruence
  (implies
   (and
    (congruent-predicate-hyps x)
    (congruent-predicate-relation x y)
    (congruent-predicate-equiv x y))
   (equal (congruent-predicate-witness x)
          (congruent-predicate-witness y)))
  :hints (("Goal" :use ((:instance existential-constraint
                                   (x1 y))
                        (:instance universal-constratint
                                   (x1 y))
                        (:instance essential-congruence
                                   (a (congruent-predicate-witness x)))
                        (:instance essential-congruence
                                   (a (congruent-predicate-witness y)))))))

(defun congruent-predicate-quantified (x)
  (congruent-predicate (congruent-predicate-witness x) x))

(defthm congruent-predicate-congruence
  (implies
   (and
    (congruent-predicate-hyps x)
    (congruent-predicate-relation x y)
    (congruent-predicate-equiv x y))
   (iff (congruent-predicate-quantified x)
        (congruent-predicate-quantified y)))
  :hints (("Subgoal 1" :use (:instance essential-congruence
                                       (a (congruent-predicate-witness y))))
          ("subgoal 2" :use (:instance essential-congruence
                                       (a (congruent-predicate-witness y))))))

(defthm congruent-predicate-canary
  (list
   (CONGRUENT-PREDICATE-QUANTIFIED X)
   (CONGRUENT-PREDICATE-HYPS X)
   (CONGRUENT-PREDICATE-RELATION X Y)
   (CONGRUENT-PREDICATE-EQUIV X Y)
   (CONGRUENT-PREDICATE-WITNESS X)
   (CONGRUENT-PREDICATE A X)
   (UNIVERSALLY-QUANTIFIED)
   )
  :rule-classes nil)

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
  (make-binding-out-rec args args1 0 x x1))

(defthm true-listp-make-binding-out
  (true-listp (make-binding-out args args1 x x1)))

(in-theory (disable make-binding-out))

(defun make-binding-into (x x1 args args1)
  (declare (type (satisfies symbol-listp) args args1))
  `((,x  (list ,@args))
    (,x1 (list ,@args1))))

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
    (& (symbolp term))))

(defun into-args-rec (args index x)
  (declare (type integer index))
  (if (not (consp args)) nil
    (cons `(nth ,index ,x)
          (into-args-rec (cdr args) (1+ index) x))))

(defthm true-listp-into-args-rec
  (true-listp (into-args-rec args index x)))

(defun into-args (args x)
  (declare (type (satisfies symbol-listp) args))
  (into-args-rec args 0 x))

(defun make-mv-rec (n index term)
  (declare (type (integer 0 *) n index))
  (if (zp n) nil
    (cons `(mv-nth ,index ,term)
          (make-mv-rec (1- n) (1+ index) term))))

(defthm true-listp-make-mv-rec
  (true-listp (make-mv-rec args index x)))

(defun make-mv (n term)
  (declare (type (integer 0 *) n))
  (if (equal n 1)
      (list term)
    (make-mv-rec n 0 term)))

(defthm true-listp-make-mv
  (true-listp (make-mv args x)))

(in-theory (disable make-mv))

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

(defun tcons (a list)
  (declare (type t list))
  (if (not (consp list)) (list a)
    (cons (car list) (tcons a (cdr list)))))

(defun make-congruences-rec (lemma fn name n iff vars parg0 arg0 narg0 parg1 arg1 narg1 congruences hyps relation suffix)
  (declare (xargs :ruler-extenders :all)
           (type symbol name iff arg0 arg1 suffix)
           (type integer n)
           (type (satisfies symbol-listp) vars parg0 parg1 narg0 narg1)
           (type (satisfies good-congruence-listp) congruences)
           )
  (let ((events (if (not (consp narg0)) nil
                  (make-congruences-rec lemma fn name (1+ n) iff vars
                                        (tcons arg0 parg0) (car narg0) (cdr narg0)
                                        (tcons arg1 parg1) (car narg1) (cdr narg1)
                                        congruences hyps relation suffix))))
    (let ((hit (assoc arg0 congruences)))
      (if (not hit) events
        (let ((equiv (cadr hit)))
          (let ((name (acl2::packn-pos (list equiv '- n '-implies- iff '- name suffix) name)))
            (cons `(defthm ,name
                     (implies
                      ,(if (and (not hyps) (not relation)) `(,equiv ,arg0 ,arg1)
                         `(and
                           ,(or hyps t)
                           ,(if relation (beta-reduce-lambda-term-full `(,relation ,@parg0 ,arg0 ,@narg0 ,@parg0 ,arg1 ,@narg0)) t)
                           (,equiv ,arg0 ,arg1)))
                      ,(if (or hyps relation)
                           `(iff (,iff ,(beta-reduce-lambda-term-full `(,fn ,@vars ,@parg0 ,arg0 ,@narg0))
                                       ,(beta-reduce-lambda-term-full `(,fn ,@vars ,@parg0 ,arg1 ,@narg0))) t)
                         `(,iff ,(beta-reduce-lambda-term-full `(,fn ,@vars ,@parg0 ,arg0 ,@narg0))
                                ,(beta-reduce-lambda-term-full `(,fn ,@vars ,@parg0 ,arg1 ,@narg0)))))
                     ,@(and lemma
                            `(:hints (("Goal" :use (:instance ,lemma
                                                              ,@(make-binding (append parg1 narg1)
                                                                              (append parg0 narg0)))))))
                     ,@(and (not hyps) (not relation) `(:rule-classes (:congruence))))
                  events)))))))

(local (in-theory (disable mv-nth)))

(defthm true-listp-make-congruences-rec
  (true-listp (make-congruences-rec lemma fn name n iff vars parg0 arg0 narg0 parg1 arg1 narg1 congruences hyps relation suffix)))

(defun make-congruences (lemma fn name iff vars arg0 arg1 congruences hyps relation suffix)
  (declare (type symbol name iff suffix)
           (type (satisfies symbol-listp) vars arg0 arg1)
           (type (satisfies good-congruence-listp) congruences))
  (if (consp arg0) 
      (make-congruences-rec lemma fn name 1 iff vars nil (car arg0) (cdr arg0) nil (car arg1) (cdr arg1) congruences hyps relation suffix)
    nil))

(defthm true-listp-make-congruences
  (true-listp (make-congruences lemma fn name iff vars arg0 arg1 congruences hyps relation suffix)))

(in-theory (disable make-congruences))

(defun make-witness-congruences-rec (vars n lemma fn arg0 arg1 congruences hyps relation suffix)
  (declare (type integer n)
           (type symbol fn suffix)
           (type (satisfies symbol-listp) arg0 arg1)
           (type (satisfies good-congruence-listp) congruences)
           (xargs :guard-debug t))
  (if (not (consp vars)) nil
    (let ((name (acl2::packn-pos (list 'mv-nth- n '- fn) fn)))
      (let ((fn0 `(lambda (,@arg0) (mv-nth ,n (,fn ,@arg0)))))
        (let ((events (make-congruences lemma fn0 name 'equal nil arg0 arg1 congruences hyps relation suffix)))
          (append events (make-witness-congruences-rec (cdr vars) (1+ n) lemma fn arg0 arg1 congruences hyps relation suffix)))))))

(defthm true-listp-make-witness-congruences-rec
  (true-listp (make-witness-congruences-rec vars n lemma fn arg0 arg1 congruences hyps relation suffix)))

(defun make-witness-congruences (vars lemma fn arg0 arg1 congruences hyps relation suffix)
  (declare (type symbol fn suffix)
           (type (satisfies symbol-listp) arg0 arg1)
           (type (satisfies good-congruence-listp) congruences))
  (if (and (consp vars) (null (cdr vars)))
      (make-congruences lemma fn fn 'equal nil arg0 arg1 congruences hyps relation suffix)
    (make-witness-congruences-rec vars 0 lemma fn arg0 arg1 congruences hyps relation suffix)))

(defthm true-listp-make-witness-congruences
  (true-listp (make-witness-congruences vars lemma fn arg0 arg1 congruences hyps relation suffix)))

(in-theory (disable make-witness-congruences))

(defun all-congruences-apply-to-args (congruences args)
  (declare (type (satisfies good-congruence-listp) congruences)
           (type (satisfies symbol-listp) args))
  (if (not (consp congruences)) t
    (let ((congruence (car congruences)))
      (let ((name (car congruence)))
        (and (member-equal name args)
             (all-congruences-apply-to-args (cdr congruences) args))))))

(local (in-theory (disable acl2::packn-pos make-congruences add-suffix lambda-term-p pseudo-termp string-append)))

(defun soft-alist (list)
  (declare (type (satisfies alistp) list))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (cons (list (car entry) (cdr entry))
            (soft-alist (cdr list))))))

(defun all-equal-rec (x y)
  (declare (type t x y))
  (if (not (and (consp x) (consp y))) nil
    (cons `(equal ,(car x) ,(car y))
          (all-equal-rec (cdr x) (cdr y)))))

(defthm true-listp-all-equal-rec
  (true-listp (all-equal-rec x y)))

(defun all-equal (x y)
  (declare (type t x y))
  (if (and (consp x) (null (cdr x))
           (consp y) (null (cdr y)))
      `(equal ,(car x) ,(car y))
    `(and ,@(all-equal-rec x y))))

(in-theory (disable all-equal))

(defun prove-quantified-congruence-fn (name vars args args1 congruent-predicate hyps relation congruences quantifier suffix iff hints)
  (declare (ignorable quantifier)
           (type symbol name quantifier suffix)
           (type (satisfies symbol-listp) vars args)
           (type (satisfies symbol-listp) args1)
           (type (satisfies pseudo-termp) congruent-predicate)
           (type (satisfies good-congruence-listp) congruences)
           (xargs :guard-debug t
                  :guard (and (or (not hyps) (pseudo-termp hyps))
                              (all-congruences-apply-to-args congruences args)
                              (or (not relation) (equal relation acl2::*nil*) (lambda-term-p relation)))))
  (let* (;(x                           (acl2::packn-pos (list "X") name))
         ;(y                           (acl2::packn-pos (list "Y") name))
         (hyps                         (if (not hyps) nil (if (equal hyps acl2::*nil*) nil hyps)))
         (relation                     (if (not relation) nil (if (equal relation acl2::*nil*) nil relation)))
         (relation-hyp                 (if (not relation) acl2::*t* (beta-reduce-lambda-term-full `(,relation ,@args ,@args1))))
         (iff                          (if iff 'iff 'equal))
         (suffix                       (if (equal suffix '||) suffix (acl2::packn-pos (list "-" suffix) suffix)))
         (congruent-predicate-congruence         (acl2::add-suffix name (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (congruent-predicate-witness            (acl2::add-suffix name "-WITNESS"))
         (congruent-predicate-lemma              (if (equal quantifier :exists) (acl2::add-suffix name "-SUFF") (acl2::add-suffix name "-NECC")))
         (congruent-predicate-witness-congruence (acl2::add-suffix congruent-predicate-witness   (concatenate 'acl2::string "-CONGRUENCE" (symbol-name suffix))))
         (congruent-predicate-rule               (acl2::add-suffix congruent-predicate-witness   "-STRENGTHEN"))
         ;;(congruent-predicate-witness-canary     (acl2::add-suffix congruent-predicate-witness   "-CANARY"))
         (congruent-predicate-raw                `(lambda (,@vars ,@args) ,(beta-reduce-lambda-term-full congruent-predicate)))
         ;(congruent-predicate                    (if (equal quantifier :exists) congruent-predicate-raw `(lambda (,@vars ,@args) (not (,congruent-predicate-raw ,@vars ,@args)))))
         ;(a1                                     (acl2::packn-pos (list a 1) 'quant::prove-quantified-congruence-fn))
         (local-congruent-predicate              (acl2::packn-pos (list name '-congruent-predicate) 'quant::prove-quantified-congruence-fn))
         (local-definition                       (acl2::packn-pos (list name '-definition) 'quant::prove-quantified-congruence-fn))
         (congruent-predicate-equiv              (acl2::packn-pos (list name '-equiv suffix) 'quant::prove-quantified-congruence-fn))
         (congruent-predicate-quantified-x      `(lambda (x) (,name ,@(into-args args 'x))))
         (congruent-predicate-hyps-x            `(lambda (x) ,(beta-reduce-lambda-term-full `((lambda (,@args) ,(or hyps acl2::*t*)) ,@(into-args args 'x)))))
         (congruent-predicate-relation-x        `(lambda (x y) ,(beta-reduce-lambda-term-full (if relation `(,relation ,@(into-args args 'x) ,@(into-args args 'y)) t))))
         (congruent-predicate-equiv-x           `(lambda (x y) (,congruent-predicate-equiv ,@(into-args args 'x) ,@(into-args args 'y))))
         (congruent-predicate-x                 `(lambda (a x) (,local-congruent-predicate ,@(into-args vars 'a) ,@(into-args args 'x))))
         (congruent-predicate-x-witness         `(lambda (x) (list ,@(make-mv (len vars) `(,congruent-predicate-witness ,@(into-args args 'x))))))
         (finst `((congruent-predicate-hyps       ,congruent-predicate-hyps-x)
                  (congruent-predicate-relation   ,congruent-predicate-relation-x)
                  (congruent-predicate-equiv      ,congruent-predicate-equiv-x)
                  (congruent-predicate-witness    ,congruent-predicate-x-witness)
                  (congruent-predicate            ,congruent-predicate-x)
                  (congruent-predicate-quantified ,congruent-predicate-quantified-x)
                  (universally-quantified         (lambda () ,(if (equal quantifier :exists) nil t)))))
         )
    
      `(encapsulate
           ()
         
         (local (in-theory (disable nth)))
         
         (local
          (defun ,local-congruent-predicate (,@vars ,@args)
            (declare (ignorable ,@vars ,@args))
            ,(beta-reduce-lambda-term-full `(,congruent-predicate-raw ,@vars ,@args))))

         (defun ,congruent-predicate-equiv (,@args ,@args1)
           (and ,@(make-equiv-body (pairlis$ args args1) congruences)))

         (local
          (defthm big-bang-congruence
            (implies
             (and
              ,(or hyps t)
              ,relation-hyp
              (,congruent-predicate-equiv ,@args ,@args1))
             (iff (iff-equiv (,local-congruent-predicate ,@vars ,@args)
                             (,local-congruent-predicate ,@vars ,@args1))
                  t))))
        
         ;; I honestly don't know if this helps .. what if we simply did the big-bang version?
         ;; (let ((events (make-congruences nil local-congruent-predicate local-congruent-predicate 'iff-equiv vars args args1 congruences hyps relation suffix)))
         ;;   (and events `((local
         ;;                  (encapsulate
         ;;                      ()
         ;;                    ,@events
         ;;                    )))))
         
         (local
          (defthm ,local-definition
            (equal (,name ,@args)
                   ;; We will need to duplicate the witness here for multiple vars ..
                   (,local-congruent-predicate ,@(make-mv (len vars) `(,congruent-predicate-witness ,@args)) ,@args))
            :hints (("Goal" :in-theory (enable ,name)))))
         
         (local (in-theory (disable iff-equiv ,name ,local-congruent-predicate ,local-definition)))
         
         (local
          (defthm congruent-predicate-witness-canary
            t
            :rule-classes nil
            :hints (("Goal" :use (:functional-instance congruent-predicate-canary
                                                       ,@finst
                                                       ))
                    (and stable-under-simplificationp
                         '(:in-theory (disable ,congruent-predicate-lemma)
                                      :use ((:instance ,congruent-predicate-rule
                                                       ,@(make-binding-out args args1 'x 'x1))
                                            (:instance ,congruent-predicate-lemma
                                                       ,@(soft-alist (pairlis$ vars (into-args vars 'a)))
                                                       ,@(soft-alist (pairlis$ args (into-args args 'x)))))))
                    (and stable-under-simplificationp
                         '(:in-theory (enable ,local-definition)))
                    (and stable-under-simplificationp
                         '(:in-theory (enable ,local-congruent-predicate)))
                    )))
                             
         (defthm ,congruent-predicate-witness-congruence
           (implies
            (and
             ,(or hyps t)
             ,relation-hyp
             (,congruent-predicate-equiv ,@args ,@args1))
            ,(all-equal (make-mv (len vars) `(,congruent-predicate-witness ,@args))
                        (make-mv (len vars) `(,congruent-predicate-witness ,@args1))))
           :rule-classes nil
           :hints (("Goal" :do-not-induct t
                    :use (:functional-instance (:instance congruent-predicate-witness-congruence
                                                          ,@(make-binding-into 'x 'y args args1))
                                               ,@finst))
                   ,@hints))
         
         (defthm ,congruent-predicate-congruence
           (implies
            (and
             ,(or hyps t)
             ,relation-hyp
             (,congruent-predicate-equiv ,@args ,@args1))
            (,iff (,name ,@args)
                  (,name ,@args1)))
           :rule-classes nil
           :hints (("Goal" :do-not-induct t
                    :use (:functional-instance (:instance congruent-predicate-congruence
                                                          ,@(make-binding-into 'x 'y args args1))
                                               ,@finst
                                               ))
                   ,@hints))
         
         (local (in-theory (union-theories '(,congruent-predicate-equiv) (theory 'acl2::minimal-theory))))
         
         (local (in-theory (disable ,name)))
         
         ,@(make-witness-congruences vars congruent-predicate-witness-congruence congruent-predicate-witness args args1 congruences hyps relation suffix)
         
         ,@(make-congruences congruent-predicate-congruence name name iff nil args args1 congruences hyps relation suffix)
                  
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

(defmacro congruence (name args body &key (suffix '||) (hyps 'nil) (relation 'nil) (congruences 'nil) (iff 'nil) (hints 'nil))
  (mv-let (quantifier vars congruent-predicate) (decompose-quantified-formula body)
    `(make-event
      (let ((name   ',name)
            (vars   ',vars)
            (args   ',args)
            (hyps   ',hyps)
            (relation ',relation)
            (congruences ',congruences)
            (suffix ',suffix)
            (congruent-predicate ',congruent-predicate)
            (quantifier ',quantifier)
            (iff   ',iff)
            (hints ',hints)
            )
        (mv-let (flg congruent-predicate) (acl2::pseudo-translate congruent-predicate nil (w state))
          (declare (ignore flg))
          (mv-let (flg hyps) (acl2::pseudo-translate hyps nil (w state))
            (declare (ignore flg))
            (let ((args1 (acl2::generate-variable-lst-simple args (append vars args))))
              (prove-quantified-congruence-fn name vars args args1 congruent-predicate hyps relation congruences quantifier suffix iff hints))))))
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

   (defun similar (x y)
     (declare (ignore x y))
     t)

   (defequiv member-equalx)

   (defcong member-equalx iff (my-member a x) 2)

   (in-theory (disable my-member (my-member) member-equalx))

   (quant::congruence fred (z)
     (exists (a) (my-member a z))
     :congruences ((z member-equalx))
     ;; In some cases, the congruence may only be conditional.
     :hyps (true-listp z)
     ;; Or there may be additional relations that must hold
     :relation (lambda (x y) (similar x y))
     ;; The quantified predicate may not be strictly Boolean
     ;; If that is so, set the :iff flag to t
     :iff t
     )

   ;; We don't actually get ACL2 congruence rules in this case
   ;; but we do get the following properties ..
   
   (defthmd fred-witness-congruence-result1
     (implies (and (true-listp z)
                   (similar z z1)
                   (member-equalx z z1))
              (equal (fred-witness z)
                     (fred-witness z1)))
     :hints (("goal" :use fred-witness-congruence)))
      
   (defthm fred-congruence-result2
     (implies (and (true-listp z)
                   (similar z z1)
                   (member-equalx z z1))
              (iff (fred z) (fred z1)))
     :hints (("goal" :use fred-congruence)))

   ))

(local
 (encapsulate
     ()

   (encapsulate
       (
        ((deuce * * *) => *)
        ((deuce-equiv * *) => *)
        )

     (local
      (defun deuce-equiv (x y)
        (equal x y)))

     (defequiv deuce-equiv)

     (local
      (defun deuce (a b x)
        (declare (ignore a b x))
        t))

     (defthm booleanp-deuce
       (booleanp (deuce a b x))
       :rule-classes (:type-prescription))

     (defcong deuce-equiv equal (deuce a b x) 3)
     
     )

   (encapsulate
       ()
     
     ;; We now support multiple quantified variables
     (defun-sk existentially-quantified-deuce (z)
       (exists (a b) (deuce a b z))
       :strengthen t)
     
     (quant::congruence existentially-quantified-deuce (z)
       (exists (a b) (deuce a b z))
       :congruences ((z deuce-equiv))
       )
     
     )

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

     (defthm booleanp-pred
       (booleanp (pred a x y))
       :rule-classes (:type-prescription))

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
        (defun-sk existentially-quantified-pred (v z)
          (exists (a) (pred a v z))
          :strengthen t)
        
        (quant::congruence existentially-quantified-pred (v z)
          (exists (a) (pred a v z))
          :congruences ((v pred-equiv))
          )

        ;; The following congruences now follow naturally ..
        (defthmd test1
          (implies
           (pred-equiv v1 v2)
           (equal (existentially-quantified-pred-witness v1 z)
                  (existentially-quantified-pred-witness v2 z))))
        
        
        (defthmd test2
          (implies
           (pred-equiv v1 v2)
           (equal (existentially-quantified-pred v1 z)
                  (existentially-quantified-pred v2 z))))

        
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
        (defun-sk universally-quantified-pred (v z)
          (forall (a) (pred a v z))
          :strengthen t)
        
        (quant::congruence universally-quantified-pred (v z)
          (forall (a) (pred a v z))
          :iff t
          :congruences ((v pred-equiv)))
       
        ;; The following congruences now follow naturally ..
        (defthmd test1
          (implies
           (pred-equiv v1 v2)
           (equal (universally-quantified-pred-witness v1 z)
                  (universally-quantified-pred-witness v2 z))))
                  
                
        (defthmd test2
          (implies
           (pred-equiv v1 v2)
           (equal (universally-quantified-pred v1 z)
                  (universally-quantified-pred v2 z))))
                
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
