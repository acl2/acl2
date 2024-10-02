(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")


(local (in-theory (disable isClassTerm)))


(defthm instance-class-table-load_cp_entry
  (equal (instance-class-table (mv-nth 1 (load_cp_entry any s)))
         (instance-class-table s)))

(defthm instance-class-table-load_cp_entries
  (equal (instance-class-table (mv-nth 1 (load_cp_entries cps s)))
         (instance-class-table s)))



(defthm isClassTerm-remains-isClassTerm-load_array2-lemma
  (implies (and (isClassTerm (class-by-name name cl))
                (isClassTerm class-rep))
           (isClassTerm (class-by-name name (cons class-rep cl)))))






(defthm class-by-name-no-change-after-load_class2-lemma
  (implies (and (class-exists? name s)
                (not (equal (classname class-rep) name)))
           (equal (class-by-name name (cons class-rep cl))
                  (class-by-name name cl))))



(defthm isClassTerm-remain-isClassTerm-load-class2
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (isClassTerm (class-by-name name 
                                       (instance-class-table 
                                        (load_class2 any s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (load_class2 add-instance-class-entry)
                           (make-runtime-class-rep)))))


(defthm class-by-name-no-change-after-load_class2
  (implies (and (isClassTerm (class-by-name name (instance-class-table s)))
                (not (isClassTerm (class-by-name any (instance-class-table s)))))
           (equal (class-by-name name (instance-class-table
                                       (load_class2 any s)))
                  (class-by-name name (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry)
                                  (make-runtime-class-rep)))))

;; Time:  34.13 seconds (prove: 33.76, print: 0.33, other: 0.04)
;;  CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2

;; not too good. but ok.

;;; this is stange 
;;; to prove this theorem, 
;;;
;;; we need to first prove an easier version which is 
;;;
;;; isClassTerm remains isClassTerm (first) 
;;;

;; (local 
;;  (defthm load_class_x-mode-1-expansion
;;    (equal (load_class_x any s seen 1)
;;           (IF
;;            (NOT (NO-FATAL-ERROR? S))
;;            S
;;           (if
;;            (not (load_class_2-inv any s seen))
;;            (fatalerror "load_class_2 violate internal inv"
;;                        s)
;;            (mv-let
;;             (def-found static-class-rep)
;;             (class-by-name-s
;;              any (external-class-table s))
;;             (declare (ignore def-found))
;;             (let ((interfaces (interfaces-s static-class-rep)))
;;                  (load_class_x interfaces
;;                                s (cons any seen)
;;                                0))))))
;;    :hints (("Goal" :in-theory (disable load_class_x)
;;             :expand (load_class_x any s seen 1)))))


(defthm isClassTerm-remain-isClassTerm-load-class-x
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (isClassTerm (class-by-name name (instance-class-table (load_class_x
                                                                   any s  seen mode)))))
  :hints (("Goal" :do-not '(generalize))))


(local 
 (encapsulate () 
   (local (include-book "base-loader-preserve-consistent-state"))
   (local (defthm not-loaded-notloaded-after-load-class-x-specific
            (implies (not (class-loaded? any s))
                     (NOT (CLASS-LOADED? ANY
                                         (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN '2)
                                                       SEEN '1))))))

   (defthm not-loaded-notloaded-after-load-class-x-specific-isClassTerm
     (implies (not (isClassTerm (class-by-name any (instance-class-table s))))
              (NOT (isClassTerm (class-by-name ANY (instance-class-table 
                                                    (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN '2)
                                                                  SEEN '1))))))
     :hints (("Goal" :use not-loaded-notloaded-after-load-class-x-specific
              :in-theory (e/d (class-loaded?) (isClassTerm)))))))
          

(defthm class-by-name-no-change-after-load_class_x
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (load_class_x any s seen mode)))
                  (class-by-name name (instance-class-table s))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-exists?
                            class-loaded?)
                           (no-fatal-error?)))))



(defthm class-by-name-no-change-after-load_array_class
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (load_array_class any s)))
                  (class-by-name name (instance-class-table s)))))


(defthm isClassTerm-remain-isClassTerm-load-array-class
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (isClassTerm (class-by-name name (instance-class-table (load_array_class
                                                                   any s)))))
  :hints (("Goal" :do-not '(generalize))))




(defthm class-by-name-no-change-after-resolveClassReference
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (resolveclassreference any s)))
                  (class-by-name name (instance-class-table s)))))



(defthm isClassTerm-remain-isClassTerm-resolveClassRefernece
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (isClassTerm (class-by-name name (instance-class-table
                                             (resolveclassreference any s)))))
  :hints (("Goal" :do-not '(generalize))))

  
(defthm class-by-name-no-change-after-getArrayClass
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (equal (class-by-name name (instance-class-table
                                       (getArrayClass any s)))
                  (class-by-name name (instance-class-table s)))))
  



(defthm isClassTerm-remain-isClassTerm-getArrayClass
  (implies (isClassTerm (class-by-name name (instance-class-table s)))
           (isClassTerm (class-by-name name (instance-class-table
                                             (getArrayClass any s)))))
  :hints (("Goal" :do-not '(generalize))))
