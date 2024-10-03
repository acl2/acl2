(in-package "DJVM")
(include-book "base-valid-type-s")
(include-book "../../BCV/bcv-functions")
(include-book "../../DJVM/consistent-state-to-sig-state")



;; (defthm 
;;   (CLASS-EXISTS? TYPE CL))
;; (BCV::GOOD-JAVA-TYPE (FIX-SIG TYPE)
;;                      CL)).

(defun wff-cl-x (cl)
  (if (endp cl) t
    (and (stringp (classname (car cl)))
         (wff-cl-x (cdr cl)))))


(local 
 (defthm stringp-class-exists-implies-good-java-type
   (implies (and (stringp name)
                 (class-exists? name cl))
            (bcv::good-java-type (fix-sig name) cl))
   :hints (("Goal" :do-not-induct t))))
           
(local 
 (defthm wff-cl-x-class-exists-implies-stringp
   (implies (and (class-exists? name cl)
                 (wff-cl-x cl))
            (stringp name))
   :rule-classes :forward-chaining))

;;;
;;; it appears that we need assertion about the cl does not contain array
;;; classes!! 
;;; 

(local 
 (defthm valid-type-s-implies-good-java-type-lemma
   (implies (and (wff-type-rep (fix-sig type))
                 (wff-cl-x cl)
                 (valid-type-s type cl mode))
            (bcv::good-java-type (fix-sig type) cl))
   :hints (("Goal" :in-theory (e/d (array-base-type 
                                    classname
                                    array-component-type) (class-exists?))
            :do-not '(generalize)))))



(local 
 (defthm fix-sig-normalize-type-rep-fix-id
   (implies (wff-type-rep type)
            (equal (fix-sig (normalize-type-rep type))
                   type))
   :hints (("Goal" :in-theory (enable wff-type-rep
                                      array-component-type
                                      isArrayType
                                      array-base-type
                                      fix-sig primitive-type?)))))


(defthm valid-type-s-implies-good-java-type
  (implies (and (wff-type-rep type)
                (wff-cl-x cl)
                (valid-type-s (normalize-type-rep type) cl mode))
           (bcv::good-java-type type cl))
  :hints (("Goal" :do-not-induct t
           :use ((:instance valid-type-s-implies-good-java-type-lemma
                            (type (normalize-type-rep type)))))))



(local 
 (defthm consistent-class-decls-implies-wff-cl-x
   (implies (consistent-class-decls cl1 cl hp)
            (wff-cl-x cl1))
   :rule-classes :forward-chaining))



(defthm consistent-state-implies-wff-cl-x
  (implies (consistent-state s)
           (wff-cl-x (instance-class-table s))))

;----------------------------------------------------------------------

(defthm valid-type-strong-implies-good-java-type-specific
  (implies (and (wff-type-rep type)
                (consistent-state s)
                (valid-type-strong (normalize-type-rep type) 
                                   (instance-class-table s)))
           (bcv::good-java-type type (instance-class-table s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable consistent-state valid-type-s))))




