;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "type-fty")
(include-book "kwargs")

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

(encapsulate
    (
     ((extended-type-fix *) => *)
     ((extended-type-equiv * *) => *)
     ((refined-type-fix *) => *)
     ((refined-type-equiv * *) => *)
     ((xequiv * *) => *)
     )

  (local
   (encapsulate
       ()
     (defun refined-type-fix (x)
       (if (integerp x) x 0))
     (defun extended-type-fix (x)
       (if (integerp x) x 0))
     (defun xequiv (x y)
       (equal x y))
     (defun refined-type-equiv (x y)
       (equal (refined-type-fix x)
              (refined-type-fix y)))
     (defun extended-type-equiv (x y)
       (equal (extended-type-fix x)
              (extended-type-fix y)))
     ))

  (defequiv extended-type-equiv)
  (defequiv refined-type-equiv)
  (defequiv xequiv)
  
  (defthmd xequiv-refined-type-fix-extended-type-fix
    (implies
     (syntaxp (symbolp x))
     (xequiv (refined-type-fix x)
             (refined-type-fix (extended-type-fix x)))))

  (defthmd refined-type-equiv-definition
    (equal (refined-type-equiv x y)
           (xequiv (refined-type-fix x)
                   (refined-type-fix y))))
  
  (defthmd extended-type-equiv-definition
    (equal (extended-type-equiv x y)
           (xequiv (extended-type-fix x)
                   (extended-type-fix y))))
  
  (defcong xequiv xequiv (refined-type-fix x) 1)
  
  )

(defthm canary-lemma
  (list
   (extended-type-fix x)
   (extended-type-equiv x y)
   (refined-type-fix x)
   (refined-type-equiv x y)
   (xequiv x y)
   )
  :rule-classes nil)

(defthm extended-type-equiv-xequiv-refined-type-fix-congruence
  (implies
   (extended-type-equiv x y)
   (xequiv (refined-type-fix x)
           (refined-type-fix y)))
  :rule-classes :congruence
  :hints (("goal" :in-theory (enable extended-type-equiv-definition
                                     xequiv-refined-type-fix-extended-type-fix))))

(defthm extended-type-equiv-refined-type-equiv-refinement
  (implies (extended-type-equiv x y)
           (refined-type-equiv x y))
  :rule-classes nil
  :hints (("goal" :in-theory (enable refined-type-equiv-definition))))

#+joe
(defthm refined-type-equiv-extended-type-fix
  (refined-type-equiv (extended-type-fix x) x)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable xequiv-refined-type-fix-extended-type-fix
                                     refined-TYPE-EQUIV-definition))))

(defun extend-in-theory (elist dlist in-theory)
  (declare (type t elist))
  (let ((elist (acl2::list-fix elist))
        (dlist (acl2::list-fix dlist)))
    (case-match in-theory
      (('acl2::enable . eset)   `(acl2::e/d (,@elist ,@(acl2::list-fix eset)) ,dlist))
      (('acl2::disable . dset)  `(acl2::e/d ,elist (,@dlist ,@(acl2::list-fix dset))))
      (('acl2::e/d eset dset)   `(acl2::e/d (,@elist ,@(acl2::list-fix eset)) (,@dlist ,@(acl2::list-fix dset))))
      ('nil                     `(acl2::e/d ,elist ,dlist))
      (&                        `(set-difference-theories (append ',elist ,in-theory)
                                                          ',dlist)))))

(def::und type-refinement-events (pkg rtype-p etype-p xargs)
  (declare (xargs :signature ((symbolp symbolp symbolp kwargs-alistp) true-listp)))
  (b* (((&key negative-rules positive-rules rewrite type-prescription forward-chain tau-system) xargs)
       (nneg      (not negative-rules))
       (npos      (not positive-rules))
       (tau       tau-system)
       (t-thm     (safe-packn-pos (list rtype-p '-refines- etype-p) pkg))
       (t-class   `(:rewrite
                    ,@(and rewrite type-prescription `(:type-prescription))
                    ,@(and forward-chain `(:forward-chaining))
                    ,@(and tau (not npos) `(:tau-system))))
       (t-theory  `((local (in-theory (disable ,t-thm)))
                    ,@(and (not rewrite) `((in-theory (disable (:rewrite ,t-thm)))))
                    ,@(and npos `((in-theory (disable ,t-thm))))
                    ))
       (n-thm     (safe-packn-pos (list 'not- etype-p '-refines- 'not- rtype-p) pkg))
       (n-class   `(:rewrite
                    ,@(and rewrite type-prescription `(:type-prescription))
                    ,@(and forward-chain `(:forward-chaining))
                    ,@(and tau (not nneg) `(:tau-system))))
       (n-theory  `((local (in-theory (disable ,n-thm)))
                    ,@(and (not rewrite) `((in-theory (disable (:rewrite ,n-thm)))))
                    ,@(and nneg `((in-theory (disable ,n-thm))))
                    ))
       )
    (append
     (named-rule t-thm `(implies      (,rtype-p x)      (,etype-p x))   t-class nil t-theory)
     (named-rule n-thm `(implies (not (,etype-p x)) (not (,rtype-p x))) n-class nil n-theory)
     )))

(def::un all-type-refinement-events (pkg xtype-p is-refinement type-list fty-alist xargs)
  (declare (xargs :signature ((symbolp symbolp booleanp symbol-listp alistp kwargs-alistp) true-listp)))
  (if (not (consp type-list)) nil
    (let* ((type-name (car type-list))
           (fty-entry (fty::get-entry type-name fty-alist))
           (type-p    (acl2::symbol-fix (fty::get-key 'fty::pred fty-entry))))
      (mv-let (rtype-p etype-p) (if is-refinement (mv xtype-p type-p) (mv type-p xtype-p))
        (append (type-refinement-events pkg rtype-p etype-p xargs)
                (all-type-refinement-events pkg xtype-p is-refinement (cdr type-list) fty-alist xargs))))))

(def::und make-type-refinement-events (type-p fty-alist kwargs)
  (declare (xargs :signature ((symbolp alistp kwargs-alistp) true-listp)))
  (b* ((kwargs (check-keywords (def-type-refinement-keywords) kwargs))
       ((&key (symbol-listp (extends 'nil) (refines 'nil)) refines-type-in-theory) kwargs))
    (and
     (or extends refines)
     `((encapsulate
           ()
         ,@(and refines-type-in-theory `((local (in-theory ,refines-type-in-theory))))
         ,@(all-type-refinement-events type-p type-p t   refines fty-alist kwargs)
         ,@(all-type-refinement-events type-p type-p nil extends fty-alist kwargs)
         )))))

(defun refinement-proof-events-fn (witness
                                   extended-type-p extended-type-equiv extended-type-fix
                                   refined-type-p refined-type-equiv refined-type-fix
                                   xequiv lemma refines-type-in-theory refines-equiv-in-theory xargs)
  ;;(declare (ignore witness))
  (let* ((xequiv-refined-type-fix-extended-type-fix
          (safe-packn-pos (list xequiv '- refined-type-fix '- extended-type-fix) 'canary-lemma))
         (refined-type-equiv-definition
          (safe-packn-pos (list refined-type-equiv '-definition) 'canary-lemma))
         (extended-type-equiv-definition
          (safe-packn-pos (list extended-type-equiv '-definition) 'canary-lemma))
         (xequiv-is-an-equivalence
          (safe-packn-pos (list xequiv '-is-an-equivalence) 'canary-lemma))
         )
  `(encapsulate
       ()

     ;; ((RType-p x) => (EType-p x)) => ((Eequivx y) => (Requivx y))
     
     ,@(and lemma
            `((encapsulate
                  ()
                ,(and refines-type-in-theory `((local (in-theory ,refines-type-in-theory))))
                ,@(type-refinement-events witness refined-type-p extended-type-p xargs)
                )))
          
     ,@(and refines-equiv-in-theory `((local (in-theory ,refines-equiv-in-theory))))
     
     (local
      (encapsulate
          ()
        
        (local
         (defthm equal-type-implies-type
           (implies
            (and
             (equal x y)
             (or (,refined-type-p x) (,refined-type-p y)))
            (and
             (,refined-type-p y)
             (,refined-type-p x)))))
        
        (defthmd ,xequiv-refined-type-fix-extended-type-fix
          (,xequiv (,refined-type-fix (,extended-type-fix x))
                   (,refined-type-fix x)))
      
        (defthmd ,refined-type-equiv-definition
          (equal (,refined-type-equiv x y)
                 (,xequiv (,refined-type-fix x)
                          (,refined-type-fix y)))
          :hints ((and stable-under-simplificationp
                       '(:in-theory (enable ,refined-type-equiv
                                            ,refined-type-fix)))))
              
        (defthmd ,extended-type-equiv-definition
          (equal (,extended-type-equiv x y)
                 (,xequiv (,extended-type-fix x)
                          (,extended-type-fix y)))
          :hints ((and stable-under-simplificationp
                       '(:in-theory (enable ,extended-type-equiv
                                            ,extended-type-fix)))))
                
        (defthm ,xequiv-is-an-equivalence
          (and (booleanp (,xequiv x y))
               (iff (,xequiv x x) t)
               (implies (,xequiv x y) (iff (,xequiv y x) t))
               (implies (and (,xequiv x y) (,xequiv y z))
                        (iff (,xequiv x z) t))))
        
        ))

     (local (in-theory (theory 'acl2::minimal-theory)))

     (local
      (defthm canary-lemma-instance
        (list
         (,extended-type-fix x)
         (,extended-type-equiv x y)
         (,refined-type-fix x)
         (,refined-type-equiv x y)
         (,xequiv x y)
         )
        :hints (("Goal" :in-theory (enable ,xequiv-is-an-equivalence
                                           ,xequiv-refined-type-fix-extended-type-fix
                                           ,refined-type-equiv-definition
                                           ,extended-type-equiv-definition)
                 :use (:functional-instance canary-lemma
                                            (extended-type-fix   ,extended-type-fix)
                                            (extended-type-equiv ,extended-type-equiv)
                                            (refined-type-fix    ,refined-type-fix)
                                            (refined-type-equiv  ,refined-type-equiv)
                                            (xequiv              ,xequiv)
                                            )))))
      
     (defthm ,(safe-packn-pos (list extended-type-equiv '- xequiv '- refined-type-fix '-congruence) witness)
       (implies
        (,extended-type-equiv x y)
        (,xequiv (,refined-type-fix x)
                 (,refined-type-fix y)))
       :rule-classes :congruence
       :hints (("Goal" :use (:functional-instance extended-type-equiv-xequiv-refined-type-fix-congruence
                                                  (extended-type-fix   ,extended-type-fix)
                                                  (extended-type-equiv ,extended-type-equiv)
                                                  (refined-type-fix    ,refined-type-fix)
                                                  (refined-type-equiv  ,refined-type-equiv)
                                                  (xequiv              ,xequiv)
                                                  ))))
     
     (defthm ,(safe-packn-pos (list extended-type-equiv '- refined-type-equiv '-refinement) witness)
       (implies
        (,extended-type-equiv x y)
        (,refined-type-equiv x y))
       :rule-classes :refinement
       :hints (("Goal" :use (:functional-instance extended-type-equiv-refined-type-equiv-refinement
                                                  (extended-type-fix   ,extended-type-fix)
                                                  (extended-type-equiv ,extended-type-equiv)
                                                  (refined-type-fix    ,refined-type-fix)
                                                  (refined-type-equiv  ,refined-type-equiv)
                                                  (xequiv              ,xequiv)
                                                  ))))
     
     #+joe
     (defthm ,(safe-packn-pos (list refined-type-equiv '- extended-type-fix) witness)
       (,refined-type-equiv (,extended-type-fix x) x)
       :hints (("Goal" :in-theory (use (:functional-instance refined-type-equiv-extended-type-fix
                                                             (extended-type-fix   ,extended-type-fix)
                                                             (extended-type-equiv ,extended-type-equiv)
                                                             (refined-type-fix    ,refined-type-fix)
                                                             (refined-type-equiv  ,refined-type-equiv)
                                                             (xequiv              ,xequiv)
                                                             )))))
          
     )))

(defun refinement-proof-events (extended-type refined-type xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist witness xargs)
  ;(declare (ignore witness))
  (let* ((entry (fty::get-entry extended-type fty-alist))
         (extended-type-p     (fty::get-key 'fty::pred  entry))
         (extended-type-equiv (fty::get-key 'fty::equiv entry))
         (extended-type-fix   (fty::get-key 'fty::fix   entry))
         (entry (fty::get-entry refined-type fty-alist))
         (refined-type-p     (fty::get-key 'fty::pred  entry))
         (refined-type-equiv (fty::get-key 'fty::equiv entry))
         (refined-type-fix   (fty::get-key 'fty::fix   entry)))
    (refinement-proof-events-fn witness
                                extended-type-p extended-type-equiv extended-type-fix
                                refined-type-p refined-type-equiv refined-type-fix
                                xequiv lemma refines-type-in-theory refines-equiv-in-theory xargs)))

(defun base-refines-all (rtype etype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)
  (if (not (consp etype-list)) nil
    (let ((events (refinement-proof-events (car etype-list) rtype xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist rtype xargs)))
      (cons events
            (base-refines-all rtype (cdr etype-list) xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)))))

(defun all-refine-base (etype rtype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)
  (if (not (consp rtype-list)) nil
    (let ((events (refinement-proof-events etype (car rtype-list) xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist etype xargs)))
      (cons events
            (all-refine-base etype (cdr rtype-list) xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)))))

(defun def-refinement-fn (base-type rtype-list etype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)
  (if (or rtype-list etype-list)
      `(encapsulate
           ()
         ,@(all-refine-base base-type etype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)
         ,@(base-refines-all base-type rtype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)
         )
    `(progn)))

(set-state-ok t)

(defun def-refinement-fn-wrapper (base-type rtype-list etype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory xargs state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let ((fty-alist (fty::get-fixtypes-alist (w state))))
    (def-refinement-fn base-type rtype-list etype-list xequiv lemma refines-type-in-theory refines-equiv-in-theory fty-alist xargs)))

(defmacro def::type-refinement (base-type &rest kvlist)
  (b* ((kwargs (kwargs (def-type-refinement-keywords) kvlist))
       ((&rest kwargs &key refines extends xequiv type-refinement-lemma refines-type-in-theory refines-equiv-in-theory) kwargs)
       )
    `(make-event (def-refinement-fn-wrapper ',base-type ',refines ',extends ',xequiv ',type-refinement-lemma ',refines-type-in-theory ',refines-equiv-in-theory  ',kwargs state))))

(encapsulate
    ()

  (local
   (def::type-refinement acl2::int
     :refines (acl2::acl2-number)
     :extends (acl2::nat)
     )
   )

  ;; Note that you get this "for free" when you
  ;; prove the refinement.
  (local
   (defthm fix-equiv-ifix
     (acl2::int-equiv (acl2::fix x) x)))
  
  )

(def::type-refinement acl2::rational
  :refines (acl2::acl2-number))

(def::type-refinement acl2::int
  :refines (acl2::rational))

(def::type-refinement acl2::nat
  :refines (acl2::int))

(def::type-refinement acl2::pos
  :refines (acl2::nat)
  :refines-equiv-in-theory (enable acl2::pos-fix))

(def::type-refinement acl2::bit
  :refines (acl2::nat))

#+joe
(defun def-type-str-refinement (pred args guard fields body)
  `(encapsulate
       ()
     
     (defun ,str-fix ,args
       )
     
     ))


;; I'm not sure how list refinement differs from standard
;; type refinement (?)

;;
;; (defun def-type-list-refinement-fn (base-type refines extends lemma in-theory fty-alist xargs)
;;   (let ((extended-type (if refines base-type extends))
;;         (refined-type  (if refines refines   base-type)))
;;     (refinement-proof-events extended-type refined-type 'equal lemma in-theory fty-alist base-type xargs)))

;; (defun def-type-list-refinement-fn-wrapper (base-type refines extends lemma in-theory xargs state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (let ((fty-alist (fty::get-fixtypes-alist (w state))))
;;     (def-type-list-refinement-fn base-type refines extends lemma in-theory fty-alist xargs)))
    
;; (defmacro def::type-list-refinement (base-type &key (refines 'nil) (extends 'nil) (in-theory 'nil)
;;                                                (type-refinement-lemma 't) 
;;                                                (negative-rules     'nil)
;;                                                (positive-rules     't)
;;                                                (rewrite            'nil)
;;                                                (forward-chain      't)
;;                                                (type-prescription  'nil)
;;                                                (tau-system         't))
;;   (declare (xargs :guard (not (iff refines extends))))
;;   (let ((xargs (list :nneg (not negated-rules)
;;                      :npos (not positive-rules)
;;                      :rewrite rewrite
;;                      :forward-chain forward-chain
;;                      :type-prescription type-prescription
;;                      :tau-system tau-system
;;                      )))
;;     `(make-event (def-type-list-refinement-fn-wrapper ',base-type ',refines ',extends ',type-refinement-lemma ',in-theory ',xargs state))))

;; #+joe
;; (def::type-list-refinement base
;;   :refines Rtype1
;;   ;;:extends Etype2
;;   :type-refinement-lemma t
;;   :in-theory nil
;;   )

