(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")

(local (in-theory (e/d (isAssignableTo class-loaded? class-exists?)
                       (isClassTerm))))


(encapsulate () 
  (local (include-book "base-consistent-state-load-class"))
  (defthm resolveClassReference-preserve-consistency
    (implies (consistent-state s)
             (consistent-state (resolveClassReference any s)))))



(defthm class-table-is-loaded-from-implies-bound-bound
  (implies (and (class-table-is-loaded-from cl scl)
                (isClassTerm (class-by-name name cl))
                (stringp name))
           (car (class-by-name-s name scl))))

(defthm consistent-state-class-table-is-loaded-from
  (implies (consistent-state s)
           (class-table-is-loaded-from (instance-class-table s)
                                       (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable consistent-state))))



(local 
 (defthm consistent-class-decls-implies-stringp
   (implies (and (consistent-class-decls cl1 cl hp)
                 (wff-instance-class-table cl1)
                 (class-by-name name cl1))
            (stringp name))
   :hints (("Goal" :in-theory (enable consistent-class-decl)))
   :rule-classes :forward-chaining))


(defthm consistent-state-class-name-is-stringp
  (implies (and (class-by-name name (instance-class-table s))
                (consistent-state s))
           (stringp name))
  :rule-classes :forward-chaining)

(local 
 (defthm isClassTerm-implies-not-nil
   (implies (isClassTerm class-rep)
            class-rep)
   :hints (("Goal" :in-theory (enable isClassTerm)))
   :rule-classes :forward-chaining))


(defthm consistent-state-class-name-is-stringp-2
  (implies (and (isClassTerm (class-by-name name (instance-class-table s)))
                (consistent-state s))
           (stringp name))
  :rule-classes :forward-chaining)



(defthm isClassTerm-class-by-name-implies-bound?-static-class-table
  (implies (and (consistent-state s)
                (isClassTerm (class-by-name name (instance-class-table s))))
           (car (class-by-name-s name (env-class-table (env s)))))
  :hints (("Goal" :use ((:instance 
                         class-table-is-loaded-from-implies-bound-bound
                         (cl (instance-class-table s))
                         (scl (env-class-table (env s))))))))


(defthm if-found-in-static-class-table-then-mem-of-all-name-s
  (implies (car (class-by-name-s name scl))
           (mem name (all-class-names-s scl))))


(defthm isClassTerm-class-by-name-implies-bound?-static-class-table-g
  (implies (and (consistent-state s)
                (isClassTerm (class-by-name name (instance-class-table s)))
                (equal (env-class-table (env s)) scl))
           (car (class-by-name-s name scl))))


(defthm lemma-isSuperClass1-remain-isSupclass1-resolveClassReference
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (ISCLASSTERM
     (CLASS-BY-NAME TYP1
                    (INSTANCE-CLASS-TABLE (RESOLVECLASSREFERENCE ANY S)))))
   (MEM TYP1
        (ALL-CLASS-NAMES-S (ENV-CLASS-TABLE (ENV S)))))
  :hints (("Goal" :use ((:instance 
                         isClassTerm-class-by-name-implies-bound?-static-class-table-g
                         (s (resolveclassreference any s))
                         (name typ1)
                         (scl (env-class-table (env s))))))))


(defthm consistent-state-implies-isSuperClass1-invariant
  (implies (consistent-state s)
           (issuperclass1-invariant typ s)))

(local (in-theory (disable issuperclass1-invariant)))



(encapsulate () 
   (local (include-book "base-load-class-normalize-class-by-name"))
   (defthm class-by-name-no-change-after-resolveClassReference
     (implies (isClassTerm (class-by-name name (instance-class-table s)))
              (equal (class-by-name name (instance-class-table
                                          (resolveclassreference any s)))
                     (class-by-name name (instance-class-table s))))))




(defthm isSuperClass1-remain-isSupclass1-resolveClassReference
  (implies (and (car (isSuperClass1 typ1 typ2 s seen))
                (consistent-state s)
                (no-fatal-error? s)
                (no-fatal-error? (resolveclassreference any s)))
           (car (isSuperClass1 typ1 typ2 (resolveclassreference any s) seen)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (isSuperClass1)
                           (isSuperClass1-invariant)))))



(defthm implementInterface-x-remains-implementInterface-x-resolveClassReference
  (implies (and (car (IMPLEMENTINTERFACE-X from to s seen mode))
                (isClassTerm (class-by-name to (instance-class-table s)))
                (no-fatal-error? s)
                (no-fatal-error? (resolveclassreference any s))
                (consistent-state s))
           (car (implementinterface-x from to (resolveclassreference any s)
                                      seen mode)))
  :hints (("Goal" :do-not '(generalize))
          ("Subgoal *1/10" :expand (IMPLEMENTINTERFACE-X FROM TO S SEEN 0))))
           


(defthm consistent-state-if-bound-implies-isClassTerm
  (implies (and (wff-instance-class-table cl)
                (class-by-name name cl))
           (isClassTerm (class-by-name name cl)))
  :hints (("Goal" :in-theory (enable wff-class-rep isClassTerm))))

(defthm isInterface-implies-not-null
  (implies (isInterface class-rep)
           class-rep)
  :rule-classes :forward-chaining)


(defthm consistent-state-isInterface-implies-isClassTerm
  (implies (and (isInterface (class-by-name name (instance-class-table s)))
                (consistent-state s))
           (isClassTerm (class-by-name name (instance-class-table s)))))


(include-book "base-valid-type-s")



;; (defthm consistent-state-class-name-is-stringp
;;   (implies (and (class-by-name name (instance-class-table s))
;;                 (consistent-state s))
;;            (stringp name))
;;   :rule-classes :forward-chaining)



(defthm wff-array-type-not-stringp-f
  (implies (wff-array-type typ)
           (not (stringp typ)))
  :hints (("Goal" :in-theory (enable wff-array-type)))
  :rule-classes :forward-chaining)



(defthm consistent-state-wff-array-type-not-bound
  (implies (and (consistent-state s)
                (wff-array-type typ1))
           (not 
             (CLASS-BY-NAME typ1 (instance-class-table s))))
  :hints (("Goal" :use ((:instance consistent-state-class-name-is-stringp
                                   (name typ1))))))
  



(defthm valid-type-s-0-wff-array-type
  (implies (valid-type-s typ cl 0)
           (wff-array-type typ))
  :rule-classes :forward-chaining)



;; (defthm valid-type-s-0-not-stringp
;;   (implies (valid-type-s typ cl 0)
;;            (not (stringp typ)))
;;   :hints (("Goal" :expand (valid-type-s typ cl 0)
;;            :in-theory (enable wff-array-type))))



;; (defthm valid-type-s-0-not-stringp-f
;;   (implies (valid-type-s typ cl 0)
;;            (not (stringp typ)))
;;   :hints (("Goal" :expand (valid-type-s typ cl 0)
;;            :in-theory (enable wff-array-type)))
;;   :rule-classes :forward-chaining)


(defthm valid-type-s-not-class-by-name
  (implies (and (valid-type-s typ (instance-class-table s) 0)
                (consistent-state s))
           (not (class-by-name typ (instance-class-table s))))
  :hints (("Goal" 
           :use ((:instance consistent-state-class-name-is-stringp
                            (name typ))))))

(defthm consistent-state-valid-type-s-mode-0-not-interface-type
  (implies (and (consistent-state s)
                (valid-type-s typ1 (instance-class-table s) 0))
           (not 
            (ISINTERFACE
             (CLASS-BY-NAME TYP1
                            (INSTANCE-CLASS-TABLE (RESOLVECLASSREFERENCE ANY
                                                                         S))))))
  :hints (("Goal" 
           :use ((:instance resolveClassReference-preserve-consistency)))))
                            
  
(defthm consistent-state-array-type-not-isClassTerm
  (implies (and (consistent-state s)
                (array-type? typ))
           (not (class-by-name typ (instance-class-table s)))))



(defthm isAssignableTo-isAssignableTo-resolveClassReference-lemma
  (implies (and (car (isAssignableTo typ1 typ2 s))
                (valid-type-strong typ1 (instance-class-table s))
                (valid-type-strong typ2 (instance-class-table s))
                (consistent-state s)
                (no-fatal-error? s)
                (no-fatal-error? (resolveClassReference any s)))
           (car (isAssignableTo typ1 typ2 (resolveClassReference any s))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isSuperClass1
                               array-type?
                               implementinterface-x))))
                               


(encapsulate () 
  (local (include-book "base-fatal-errorflag-not-earsed"))
  (defthm not-no-fatal-error-preserved-resolveClassReference
    (implies (not (no-fatal-error? s))
             (not (no-fatal-error? (resolveClassReference any s))))))

;;; shall not be hard. 
;; ;;;
;; ;;; once have fatal-error, it will keep it. 
;; ;;;

;; we also proved a lemma to say if 
;; typ1 is a valid-type-strong,
;; then 
;; typ2 has to be a valid-type-strong,
;; otherwise
;; (car (isAssignableTo typ1 typ2 s)) is nil!! 
;;

;; (i-am-here) ;; Sat Jun 11 21:11:20 2005

(encapsulate () 
  (local (include-book "base-isAssignableTo-properties"))
  (defthm isAssignable-to-then-loaded
    (implies (and (car (isAssignableTo typ1 typ2 s))
                  (not (equal typ1 typ2))
                  (consistent-state s))
             (valid-type-strong typ2 (instance-class-table s)))
    :hints (("Goal" :do-not '(generalize)))))


(defthm isAssignableTo-valid-type-valid-type
  (implies (and (car (isAssignableTo typ1 typ2 s))
                (valid-type-strong typ1 (instance-class-table s))
                (consistent-state s))
           (valid-type-strong typ2 (instance-class-table s)))
  :hints (("Goal" :cases ((equal typ1 typ2)))))





(defthm isAssignableTo-isAssignableTo-resolveClassReference
  (implies (and (car (isAssignableTo typ1 typ2 s))
                (valid-type-strong typ1 (instance-class-table s))
                (consistent-state s)
                (no-fatal-error? (resolveClassReference any s)))
           (car (isAssignableTo typ1 typ2 (resolveClassReference any s))))
  :hints (("Goal" :do-not '(generalize)
           :cases ((no-fatal-error? s)))))


;;; we got rid of the valid-type-strong assertions on typ2 !!! 
;;; the theorem is easier to use!! 


                               


