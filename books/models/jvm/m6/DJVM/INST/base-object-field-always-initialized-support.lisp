(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
;; (include-book "base-consistent-state.lisp")


(acl2::set-verify-guards-eagerness 0)

;;; Wed Jul 20 15:51:38 2005
;;; copied from GETFIELD.lisp
;;;
;;; Not sure what needs to be disabled to make it go fasters. 
;;;

;;;
;;; The difficulty seems to be lying in the way of we assert properties
;;;
;;; We assert properties of an artifact not in the way that it will be used. 
;;; but in the way how it is constructured. 
;;; 
;;; We could have something that help hides how the internal data structure is
;;; constructured.
;;; 
;;; we would want to assert properties in form of "iterator", "enumerator"!!
;;;  

;; (defun fields-jvp (classname jvp)
;;   (binding classname jvp))

(local (in-theory (disable isClassTerm consistent-object
                           java-visible-portion
                           fields deref2 rREF isArrayType
                           class-exists? super binding bound?)))


(defthm consistent-fields-init-state-implied-by-jvp
  (implies (and (consistent-jvp-init-state jvp cl hp-init)
                (consistent-jvp obj-typ jvp cl hp)
                (binding classname jvp))
           (consistent-fields-init-state
            (binding classname jvp)
            (fields (class-by-name classname cl))
            hp-init))
  :hints (("Goal" :in-theory (enable binding class-by-name)
           :do-not '(generalize))))


;; Warnings:  Free and Non-rec
;; Time:  98.83 seconds (prove: 98.68, print: 0.12, other: 0.03)
;;  CONSISTENT-FIELDS-INIT-STATE-IMPLIED-BY-JVP
;;
;; Wed Jul 20 15:51:18 2005 

;; Summary
;; Form:  ( DEFTHM CONSISTENT-FIELDS-INIT-STATE-IMPLIED-BY-JVP ...)
;; Rules: ((:DEFINITION ALISTP)
;;         (:DEFINITION ASSOC-EQUAL)
;;         (:DEFINITION BINDING)
;;         (:DEFINITION CLASS-EXISTS?)
;;         (:DEFINITION CONSISTENT-IMMEDIDATE-INSTANCE)
;;         (:DEFINITION CONSISTENT-IMMEDIDATE-INSTANCE-INIT-STATE)
;;         (:DEFINITION CONSISTENT-JVP)
;;         (:DEFINITION CONSISTENT-JVP-INIT-STATE)
;;         (:DEFINITION ENDP)
;;         (:DEFINITION FIELDS)
;;         (:DEFINITION LEN)
;;         (:DEFINITION NOT)
;;         (:DEFINITION SUPER)
;;         (:DEFINITION WFF-IMMEDIATE-INSTANCE)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART <)
;;         (:EXECUTABLE-COUNTERPART ALISTP)
;;         (:EXECUTABLE-COUNTERPART BINARY-+)
;;         (:EXECUTABLE-COUNTERPART CDR)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART LEN)
;;         (:EXECUTABLE-COUNTERPART NOT)
;;         (:EXECUTABLE-COUNTERPART STRINGP)
;;         (:FAKE-RUNE-FOR-LINEAR NIL)
;;         (:FAKE-RUNE-FOR-TYPE-SET NIL)
;;         (:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
;;         (:INDUCTION ALISTP)
;;         (:INDUCTION ASSOC-EQUAL)
;;         (:INDUCTION CONSISTENT-JVP)
;;         (:INDUCTION CONSISTENT-JVP-INIT-STATE)
;;         (:INDUCTION LEN)
;;         (:TYPE-PRESCRIPTION ALISTP)
;;         (:TYPE-PRESCRIPTION CONSISTENT-FIELDS-INIT-STATE)
;;         (:TYPE-PRESCRIPTION ISCLASSTERM)
;;         (:TYPE-PRESCRIPTION LEN))
;; Warnings:  Free and Non-rec
;; Time:  98.83 seconds (prove: 98.68, print: 0.12, other: 0.03)
;;  CONSISTENT-FIELDS-INIT-STATE-IMPLIED-BY-JVP


;; Originally it takes only 2.7 seconds. 
;; Form:  ( DEFTHM CONSISTENT-FIELDS-INIT-STATE-IMPLIED-BY-JVP ...)
;; Rules: ((:DEFINITION ALISTP)
;;         (:DEFINITION ASSOC-EQUAL)
;;         (:DEFINITION BINDING)
;;         (:DEFINITION CONSISTENT-IMMEDIDATE-INSTANCE)
;;         (:DEFINITION CONSISTENT-IMMEDIDATE-INSTANCE-INIT-STATE)
;;         (:DEFINITION CONSISTENT-JVP)
;;         (:DEFINITION CONSISTENT-JVP-INIT-STATE)
;;         (:DEFINITION ENDP)
;;         (:DEFINITION FIELDS)
;;         (:DEFINITION LEN)
;;         (:DEFINITION NOT)
;;         (:DEFINITION WFF-IMMEDIATE-INSTANCE)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART <)
;;         (:EXECUTABLE-COUNTERPART ALISTP)
;;         (:EXECUTABLE-COUNTERPART BINARY-+)
;;         (:EXECUTABLE-COUNTERPART CDR)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART LEN)
;;         (:EXECUTABLE-COUNTERPART NOT)
;;         (:EXECUTABLE-COUNTERPART STRINGP)
;;         (:FAKE-RUNE-FOR-LINEAR NIL)
;;         (:FAKE-RUNE-FOR-TYPE-SET NIL)
;;         (:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
;;         (:INDUCTION ALISTP)
;;         (:INDUCTION ASSOC-EQUAL)
;;         (:INDUCTION CONSISTENT-JVP)
;;         (:INDUCTION CONSISTENT-JVP-INIT-STATE)
;;         (:INDUCTION LEN)
;;         (:TYPE-PRESCRIPTION ALISTP)
;;         (:TYPE-PRESCRIPTION CLASS-EXISTS?)
;;         (:TYPE-PRESCRIPTION CONSISTENT-FIELDS-INIT-STATE)
;;         (:TYPE-PRESCRIPTION LEN))
;; Warnings:  Free and Non-rec
;; Time:  2.70 seconds (prove: 2.58, print: 0.09, other: 0.03)
;;  CONSISTENT-FIELDS-INIT-STATE-IMPLIED-BY-JVP
;; DJVM !>



(defthm consistent-object-implies-consistent-jvp
  (implies (and (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (CONSISTENT-JVP (OBJ-TYPE OBJ) (JAVA-VISIBLE-PORTION OBJ) cl HP))
  :hints (("Goal" :in-theory (enable consistent-object))))

(in-theory (disable primitive-type? obj-type))

(defthm consistent-fields-init-state-implied-by
  (implies (and (consistent-object-init-state obj cl hp-init)
                (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj)))
                (binding classname (java-visible-portion obj)))
           (consistent-fields-init-state
            (binding classname (java-visible-portion obj))
            (fields (class-by-name classname cl))
            hp-init))
  :hints (("Goal" :in-theory (e/d ()
                                  (consistent-fields-init-state
                                   consistent-object
                                   isArrayType fields
                                   java-visible-portion))
           :restrict ((consistent-fields-init-state-implied-by-jvp
                       ((obj-typ (obj-type obj))
                        (hp hp)))))))





(defthm consistent-fields-init-state-not-primitive-type
  (implies (and (not (primitive-type? (get-field-type1 fieldname field-decls)))
                (binding fieldname fields)
                (not (equal (binding fieldname fields) -1))
                (consistent-fields-init-state fields field-decls
                                              hp-init))
           (not (bound? (binding fieldname fields)
                        hp-init)))
  :hints (("Goal" :in-theory (enable binding field-fieldname bound?))))


;; ;; (defthm object-field-is-always-initialized
;; ;;   (implies (and (not (primitive-type? 
;; ;;                       (get-field-type
;; ;;                        fieldclassname
;; ;;                        fieldname cl)))
;; ;;                 (not (isArrayType (obj-type (deref2 v (heap s)))))
;; ;;                 (m6-getfield fieldclassname fieldname (rREF v) s)
;; ;;                 (isClassTerm (class-by-name fieldclassname cl))
;; ;;                 (BINDING FIELDCLASSNAME (JAVA-VISIBLE-PORTION (DEREF2 V (HEAP S))))
;; ;;                 (not (equal (m6-getfield fieldclassname fieldname (rREF v) s) -1))
;; ;;                 (consistent-object-init-state 
;; ;;                  (deref2 v (heap s))
;; ;;                  cl hp-init)
;; ;;                 (consistent-object (deref2 v (heap s))
;; ;;                                    (heap s)
;; ;;                                    cl))
;; ;;            (not (bound? (m6-getfield fieldclassname
;; ;;                                      fieldname
;; ;;                                      (rREF v) s)
;; ;;                         hp-init)))
;; ;;   :hints (("Goal" :in-theory (e/d (m6-getfield) (fields))
;; ;;            :restrict ((consistent-fields-init-state-not-primitive-type
;; ;;                        ((field-decls (fields (class-by-name fieldclassname
;; ;;                                                             cl)))))
;; ;;                       (consistent-fields-init-state-implied-by
;; ;;                        ((hp (heap s))))))))
                                          
;;; (i-am-here) ;; Thu Jul 21 14:18:07 2005 

(local 
 (defthm binding-rREF-normalize
   (equal (binding (rREF v) hp)
          (deref2 v hp))
   :hints (("Goal" :in-theory (enable deref2)))))


(defthm object-field-is-always-initialized-lemma
  (implies (and (not (primitive-type? 
                      (get-field-type
                       fieldclassname
                       fieldname cl)))
                (not (isArrayType (obj-type (deref2 v (heap s)))))
                (m6-getfield fieldclassname fieldname (rREF v) s)
                (BINDING FIELDCLASSNAME (JAVA-VISIBLE-PORTION (DEREF2 V (HEAP S))))
                (not (equal (m6-getfield fieldclassname fieldname (rREF v) s) -1))
                (consistent-object-init-state 
                 (deref2 v (heap s))
                 cl hp-init)
                (consistent-object (deref2 v (heap s))
                                   (heap s)
                                   cl))
           (not (bound? (m6-getfield fieldclassname
                                     fieldname
                                     (rREF v) s)
                        hp-init)))
  :hints (("Goal" :in-theory (e/d (m6-getfield) (fields 
                                                 consistent-object-init-state
                                                 consistent-object))
           :restrict ((consistent-fields-init-state-not-primitive-type
                       ((field-decls (fields (class-by-name fieldclassname
                                                            cl)))))
                      (consistent-fields-init-state-implied-by
                       ((hp (heap s)))))
           :do-not-induct t)))



;; ;; ;;; this is expanded into this form with complicated

;;; we may simplify it be asserting that 
;;;
;;; hp-init does not contain nil as its key
;;; 
;;; and hp-init does not contain -1 as its key
;;;
;;; So we can prove get rid of the some hypothesis 
;;; btw relying on some pecularity of the our implementation that 
;;;
;;; (binding key db) returns nil, if key is not found. 
;;;
;;; Which is not a very good approach though. 
;;;
;;; We shall want to prove that when m6-get-field is called, 
;;; we know that the field will be found. etc.! 
;;;
;;; We do have our guard verification efforts!! 
;;; 

;;; Well this is what I am going to do!! 


(defthm not-binding-m6-get-field-nil
  (implies (NOT (BINDING FIELDCLASSNAME
                         (JAVA-VISIBLE-PORTION (BINDING (RREF V) (HEAP S)))))
           (equal  (m6-getfield fieldclassname 
                                fieldname (rREF v) s)
                   nil))
  :hints (("Goal" :in-theory (enable m6-getfield binding))))
                                


(defthm object-field-is-always-initialized
  (implies (and (case-split (not (primitive-type? 
                                  (get-field-type
                                   fieldclassname
                                   fieldname cl))))
                (not (isArrayType (obj-type (deref2 v (heap s)))))
                (not (bound? nil hp-init))
                (not (bound? -1 hp-init))
                (consistent-object-init-state 
                 (deref2 v (heap s))
                 cl hp-init)
                (consistent-object (deref2 v (heap s))
                                   (heap s)
                                   cl))
           (not (bound? (m6-getfield fieldclassname
                                     fieldname
                                     (rREF v) s)
                        hp-init)))
  :hints (("Goal" :in-theory (e/d () (fields m6-getfield))
           :cases ((binding fieldclassname (java-visible-portion (binding (rREF
                                                                           v)
                                                                          (heap
                                                                           s))))))
          ("Subgoal 1" :use object-field-is-always-initialized-lemma)))


;; (defthm object-field-is-always-initialized
;;   (implies (and (not (primitive-type? 
;;                       (get-field-type
;;                        fieldclassname
;;                        fieldname cl)))
;;                 (not (isArrayType (obj-type (deref2 v (heap s)))))
;;                 (not (bound? nil hp-init))
;;                 (not (bound? -1 hp-init))
;;                 (consistent-object-init-state 
;;                  (deref2 v (heap s))
;;                  cl hp-init)
;;                 (consistent-object (deref2 v (heap s))
;;                                    (heap s)
;;                                    cl))
;;            (not (bound? (m6-getfield fieldclassname
;;                                      fieldname
;;                                      (rREF v) s)
;;                         hp-init)))
;;   :hints (("Goal" :in-theory (e/d () (fields m6-getfield consistent-object-init-state))
;;            :cases ((binding fieldclassname (java-visible-portion (binding (rREF
;;                                                                            v)
;;                                                                           (heap
;;                                                                            s))))))
;;           ("Subgoal 1" :use object-field-is-always-initialized-lemma)))

