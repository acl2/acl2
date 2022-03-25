;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")

(include-book "type-refinement")
(include-book "pick-a-point")

(defun len-len-induction (x y)
  (if (and (consp x) (consp y))
      (len-len-induction (cdr x) (cdr y))
    (list x y)))

(defun len-equiv (x y)
  (equal (len x)
         (len y)))

(defequiv len-equiv)
(defcong len-equiv equal (consp x) 1)
(defcong len-equiv len-equiv (cons a x) 2)
(defcong len-equiv len-equiv (cdr x) 1)
(defcong len-equiv equal (len x) 1)

(defun get-key? (key alist)
  (declare (type (satisfies alistp) alist))
  (let ((hit (assoc-equal key alist)))
    (if (not (consp hit)) nil
      (cdr hit))))

(defun def-type-list-fn (type fty-alist kwargs)
  (b* (((&rest kwargs &key list-name listp list-equiv list-fix list-fix!) kwargs)
       ((&key refines-type-in-theory refines-equiv-in-theory) kwargs)
       (entry (fty::get-entry type fty-alist))
       (equiv       (fty::get-key 'fty::equiv entry))
       (type-fix    (fty::get-key 'fty::fix   entry))
       (type-fix!   (fty::get-key 'fty::fix!  entry))
       (list-name   (default-name list-name  type '-list  type))
       (list-p      (default-name listp      type '-listp list-name))
       (list-equiv  (default-name list-equiv list-name '-equiv list-p))
       (list-fix!   (default-name list-fix!  list-name '-fix!  list-p))
       (list-fix    (type-fix list-fix list-name list-fix! list-p))
       ;;(fty-alist   (acons 'len `((fty::pred . len-p)   (fty::fix . acl2::len) (fty::equiv . len-equiv)) fty-alist))
       ;;(fty-alist   (acons name `((fty::pred . ,name-p) (fty::fix . ,list-fix) (fty::equiv . ,list-equiv)) fty-alist)))
       )
      `(encapsulate
           ()

       (fty::deflist ,list-name
                     :pred ,list-p
                     :elt-type ,type
                     :true-listp t
                     )

       (in-theory (enable ,list-fix))

       (defthm ,(safe-packn-pos (list 'open- list-fix) type)
         (implies
          (consp x)
          (equal (,list-fix x)
                 (cons (,type-fix (car x))
                       (,list-fix (cdr x)))))
         :rule-classes ((:rewrite :backchain-limit-lst 0)))

       (defun ,list-fix! (x)
         (declare (type t x))
         (if (not (consp x)) nil
           (cons (,type-fix! (car x))
                 (,list-fix! (cdr x)))))

       (defthm ,(safe-packn-pos (list list-fix! '-to- list-fix) list-p)
         (equal (,list-fix! x)
                (,list-fix  x)))

       (in-theory (disable ,list-fix!))
       
       (fty::add-fix! ,list-name :fix! ,list-fix!)

       (defthm ,(safe-packn-pos (list 'open- list-equiv) list-p)
         (equal (,list-equiv x y)
                (if (not (consp x)) (not (consp y))
                  (if (not (consp y)) nil
                    (and (,equiv (car x) (car y))
                         (,list-equiv (cdr x) (cdr y))))))
         :rule-classes (:definition))

       ;;
       ;; Ideally we would also provide existential equality
       ;;
       
       (in-theory (disable ,list-equiv))

       (defthm ,(safe-packn-pos (list list-equiv '-induction) list-p)
         t
         :rule-classes ((:induction
                         :pattern (,list-equiv x y)
                         :scheme (len-len-induction x y))))

       (defcong ,list-equiv ,equiv (nth i x) 2
         :hints (("Goal" :in-theory (enable nth))))

       (def::pick-a-point
         :type-fix ,type-fix
         :list-equiv ,list-equiv
         )

       ;; len-equiv says that length of two lists are equal,
       ;; irregardless of their content.
       ;;
       ;; list-equiv extends len-equiv
       ,(refinement-proof-events-fn list-p
                                    list-p list-equiv list-fix
                                    'acl2::any-p 'len-equiv 'acl2::len
                                    'equal nil
                                    refines-type-in-theory
                                    refines-equiv-in-theory
                                    nil)
       
       ;; True-list-equiv says that two lists are otherwise 'equal' if
       ;; you discount the final (cdr).
       ;;
       ;; list-equiv refines true-list-equiv
       ;;
       ;; I think this is (finally) a standard refinement ..
       ;;
       ,@(and nil
              (list
               (refinement-proof-events-fn list-p
                                           'acl2::any-p 'acl2::list-equiv 'acl2::true-list-fix
                                           list-p list-equiv list-fix
                                           'equal nil 
                                           nil
                                           (extend-in-theory '(acl2::list-equiv acl2::true-list-fix) nil refines-equiv-in-theory)
                                           nil)))
       
       (in-theory (enable ,list-p))

       (def::type-refinement ,list-name
         ,@(kvlist (keep (type-refinement-keywords) kwargs)))
              
       )))

(set-state-ok t)

(defun def-type-list-fn-wrapper (type kwargs state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let ((fty-alist (fty::get-fixtypes-alist (w state))))
    (def-type-list-fn type fty-alist kwargs)))

(defmacro def::type-list (type &rest kvlist)
  (let ((kwargs (kwargs (def-type-list-keywords) kvlist)))
    `(make-event (def-type-list-fn-wrapper
                   ',type
                   ',kwargs
                   state))))

(local
 (encapsulate
     ()
   
   (fty::deflist nat-list
                 :elt-type acl2::nat
                 :true-listp t)
   
   (fty::add-fix! acl2::int :fix! ifix)
   
   ;; DAG: It would be really nice if ACL2 didn't do this ..
   ;;
   ;; ACL2 Error in ( DEFTHM LIST-EQUIV-INT-LIST-EQUIV-REFINEMENT ...): 
   ;; ACL2::LIST-EQUIV is already known to be a refinement of 
   ;; INT-LIST-EQUIV$INLINE.  See :DOC refinement.
   
   (def::type-list acl2::int
     :list-name  int-list
     :listp      int-listp
     :list-fix   int-list-fix
     :list-fix!  int-list-fix!
     :list-equiv int-list-equiv
     ;;:refines (acl2::true-list)
     :extends (nat-list)
     :refines-equiv-in-theory (enable true-list-fix)
     ;;:refine-list-equiv nil
     )
   
   ))

