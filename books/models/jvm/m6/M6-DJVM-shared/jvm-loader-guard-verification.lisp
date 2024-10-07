(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader")
(include-book "../M6-DJVM-shared/jvm-dynamic-loading-property")

;;;; The goal to to prove that class loader is implemented correctly.  No guard
;;;; violation during execution is possible, if the top level guard is met. 

;;;; The essential thing is to prove that load_class of one class will perserve
;;;; the guard for operations that used to create another class. 

;;;; Since we already verified the guard of load_class2

; >V            (DEFUN
;                LOAD_CLASS2_GUARD (CLASSNAME S)
;                (MYLET*
;                 ((ENV (ENV S))
;                  (CLASS-TABLE (CLASS-TABLE S))
;                  (SCL (ENV-CLASS-TABLE ENV)))
;                 (AND
;                  (WFF-STATE S)
;                  (WFF-ENV ENV)
;                  (WFF-HEAP (HEAP S))
;                  (WFF-CLASS-TABLE CLASS-TABLE)
;                  (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD-STRONG S)
;                  (LOADER-INV S)
;                  (ALL-CORRECTLY-LOADED?
;                   (COLLECT-SUPERCLASSNAME CLASSNAME (EXTERNAL-CLASS-TABLE S))
;                   (INSTANCE-CLASS-TABLE S)
;                   (EXTERNAL-CLASS-TABLE S))
;                  (ALL-CORRECTLY-LOADED?
;                   (COLLECT-SUPERINTERFACE CLASSNAME (EXTERNAL-CLASS-TABLE S))
;                   (INSTANCE-CLASS-TABLE S)
;                   (EXTERNAL-CLASS-TABLE S))
;                  (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD-STRONG S)
;                  (WFF-STATIC-CLASS-TABLE SCL)
;                  (MV-LET
;                   (FOUND CLASS-DESC)
;                   (CLASS-BY-NAME-S CLASSNAME SCL)
;                   (MYLET*
;                    ((STATIC-CP (CONSTANTPOOL-S CLASS-DESC))
;                     (STATIC-FIELD-TABLE (FIELDS-S CLASS-DESC))
;                     (STATIC-METHOD-TABLE (METHODS-S CLASS-DESC)))
;                    (OR
;                     (NOT FOUND)
;                     (AND
;                        (WFF-CLASS-REP-STATIC CLASS-DESC)
;                        (LOAD_CP_ENTRIES_GUARD STATIC-CP S)
;                        (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
;                             "java.lang.Class" S)
;                        (WFF-FIELDS-S STATIC-FIELD-TABLE)
;                        (RUNTIME-METHOD-REP-GUARDS STATIC-METHOD-TABLE))))))))

;;;; We only need to verify the guard that load_class_x

;;;; load_class_x's guard is defined as load_class_x

(in-theory (disable loader-inv wff-env wff-class-table))


(defthm loader-inv-implies-wff-state
  (implies (loader-inv s)
           (wff-state s))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :type-prescription)


(defthm loader-inv-implies-wff-instance-class-table
  (implies (loader-inv s)
           (wff-instance-class-table (instance-class-table s)))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :type-prescription)


(defthm loader-inv-implies-wff-class-table
  (implies (loader-inv s)
           (wff-class-table (class-table s)))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :type-prescription)


(defthm loader-inv-implies-wff-env
  (implies (loader-inv s)
           (wff-env (env s)))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :type-prescription)

(defthm loader-inv-implies-wff-static-class-table
  (implies (loader-inv s)
           (wff-static-class-table-strong (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :forward-chaining)


(defthm loader-inv-equal
  (implies (and (loader-inv s)
                some-error)
           (loader-inv (MAKE-STATE (pc s)
                                 any_thread
                                 any_heap
                                 any_thread_table
                                 (class-table s)
                                 (ENV S)
                                 some-error
                                 any_aux)))
  :hints (("Goal" :in-theory (enable loader-inv))))

(defthm loader-inv-equal-specific
  (implies (loader-inv s)
           (LOADER-INV (MAKE-STATE (PC S)
                                   (CURRENT-THREAD S)
                                   (HEAP (LOAD_CLASS_X P1 S SEEN 3))
                                   (THREAD-TABLE S)
                                   (CLASS-TABLE (LOAD_CLASS_X P1 S SEEN 3))
                                   (ENV S)
                                   "class implements non interfaces"
                                   (NTH 8 (LOAD_CLASS_X P1 S SEEN 3)))))
  :hints (("Goal" :in-theory (enable loader-inv))))

;;; insert the file jvm-loader-property2 here!! 


(defthm isClassTerm-make-runtime-class-rep
  (isClassTerm (make-runtime-class-rep n super cps fs ms is sfs status afs itid cref)))
                


(defthm no-fatal-error-correctly-loaded-by-load_class2
  (implies (and (equal (env-class-table (env s)) env-cl)
                (no-fatal-error? (load_class2 p s)))
           (correctly-loaded? p (instance-class-table 
                                 (load_class2 p s))
                                 env-cl))
  :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry
                                               correctly-loaded?) 
                                  (wff-class-rep isClassTerm
                                   make-runtime-class-rep)))))


;; correctly loaded asserts that super/superinterfaces information matches with
;; that from the static class table! c.f. class-is-loaded-from 
;; 
;; Fri Jul  2 15:02:50 2004


;; (defthm correctly-loaded?-remain-correctly-loaded
;;   (implies (and (correctly-loaded? p (instance-class-table s)
;;                                    (external-class-table s))
;;                 (equal (external-class-table s) env-cl))
;;            (correctly-loaded? p (instance-class-table 
;;                                  (load_class_x p s seen mode))
;;                               env-cl))
;;   :hints (("Goal" :do-not '(generalize))))


(defthm no-fatal-error-correctly-loaded
  (implies (and (equal (env-class-table (env s)) env-cl)
                (not (class-loaded? p s))
                (no-fatal-error? (load_class_x p s seen 3)))
           (correctly-loaded? p (instance-class-table (load_class_x p s seen
                                                                    3))
                              env-cl))
  :hints (("Goal" :expand (load_class_x p s seen 3))))


(defthm loader-inv-loaded-class-are-correctly-loaded
  (implies (and (loader-inv s)
                (class-loaded? p s)
                (no-fatal-error? s)
                (equal (external-class-table s) env-cl))
           (correctly-loaded? p (instance-class-table s)
                              env-cl))
  :hints (("Goal" :in-theory (enable loader-inv))))

(defthm no-fatal-error-correctly-loaded-version
  (implies (and (loader-inv s)
                (equal (env-class-table (env s)) env-cl)
                (no-fatal-error? (load_class_x p s seen 3)))
           (correctly-loaded? p (instance-class-table (load_class_x p s seen
                                                                    3))
                              env-cl))
  :hints (("Goal" :cases ((class-loaded? p s)))))


;; (skip-proofs
;;  (defthm no-fatal-error-correctly-loaded-2
;;   (implies (and (loader-inv s)
;;                 (equal (env-class-table (env s)) env-cl)
;;                 (no-fatal-error? (load_class_x interfaces s seen 0)))
;;            (all-correctly-loaded? interfaces (instance-class-table 
;;                                               (load_class_x interfaces s seen 0))
;;                               env-cl))))


(defthm correctly-loaded-is-preserved-by-load_class2
  (implies (and (correctly-loaded? p (instance-class-table s) env-cl)
                (equal (external-class-table s) env-cl))
           (correctly-loaded? p (instance-class-table (load_class2 any s))
                              env-cl))
  :hints (("Goal" :in-theory (e/d (load_class2 correctly-loaded? 
                                               add-instance-class-entry) 
                                  (isClassTerm make-runtime-class-rep)))))


(defthm correctly-loaded-is-preserved-by-load_class_x
  (implies (and (correctly-loaded? p (instance-class-table s) env-cl)
                (equal (external-class-table s) env-cl))
           (correctly-loaded? p (instance-class-table (load_class_x any s seen mode))
                              env-cl)))


(defun all-correctly-loaded-induct (p s seen) 
  (if (endp p) (list p s seen)
    (all-correctly-loaded-induct (cdr p)
                                 (load_class_x (car p) s seen 3)
                                 seen)))


(defthm mem-x-then-correctly-loaded
  (implies (and (loader-inv s)
                (equal (external-class-table s) env-cl)
                (no-fatal-error? (load_class_x p s seen 0))
                (mem x p))
           (correctly-loaded? x
            (instance-class-table (load_class_x p s seen 0))
            env-cl))
  :hints (("Goal" :do-not '(generalize)
           :induct (all-correctly-loaded-induct p s seen))))
                              

(defthm no-fatal-error-all-correctly-loaded
  (implies (and (loader-inv s)
                (equal (env-class-table (env s)) env-cl)
                (subset px p)
                (no-fatal-error? (load_class_x p s seen 0)))
           (all-correctly-loaded? px  (instance-class-table 
                                       (load_class_x p s seen 0))
                                  env-cl))
  :hints (("Goal" :do-not '(generalize))))


(defthm no-fatal-error-all-correctly-loaded-specific
   (implies (and (loader-inv s)
                 (equal (env-class-table (env s)) env-cl)
                 (no-fatal-error? (load_class_x p s seen 0)))
            (all-correctly-loaded? p (instance-class-table 
                                      (load_class_x p s seen 0))
                                   env-cl))
   :hints (("Goal" :do-not '(generalize))))

;; (i-am-here) ;; Sun Nov  7 17:18:17 2004

(defthm loader-inv-fatal-error
  (implies (and (loader-inv s)
                any)
           (loader-inv (fatalerror any s))))

(defthm loader-inv-perserved-by-load_class_x_mode_0
  (implies (loader-inv s)
           (loader-inv (load_class_x p s seen 0)))
  :hints (("Goal" :induct (all-correctly-loaded-induct p s seen)
           :in-theory (disable fatalerror))))

(defthm loader-inv-perserved-by-load_class_x_mode_1
  (implies (loader-inv s)
           (loader-inv (load_class_x p s seen 1)))
  :hints (("Goal" :expand (load_class_x p s seen 1))))


(defthm loader-inv-perserved-by-load_class_x_mode_2
  (implies (loader-inv s)
           (loader-inv (load_class_x p s seen 2)))
  :hints (("Goal" :expand (load_class_x p s seen 2))))



(defthm loader-inv-invariant
  (implies (loader-inv s)
           (loader-inv (load_class_x p s seen mode)))
  :hints (("Goal" :cases ((equal mode 2) (equal mode 1) (equal mode 0) 
                          (equal mode 3)))))




(defthm wff-heap-load_class2
  (implies (wff-heap (heap s))
           (wff-heap (heap (load_class2 p s))))
  :hints (("Goal" :in-theory (enable wff-heap load_class2))))

(defthm wff-heap-load_class_x
  (implies (wff-heap (heap s))
           (wff-heap (heap (load_class_x p s seen mode)))))


(defthm loader-inv-implies-wff-instance-class-table-strong
  (implies (loader-inv s)
           (wff-instance-class-table-strong (instance-class-table s)))
  :hints (("Goal" :in-theory (enable loader-inv)))
  :rule-classes :type-prescription)



(defthm all-correctly-loaded?-app-list
  (implies (all-correctly-loaded? (app a b) cl env-cl)
           (all-correctly-loaded? a cl env-cl))
  :rule-classes :forward-chaining)

(defthm loader-inv-helper1-implies-all-correctly-loaded
  (implies (and (mem any (all-class-names l))
                (loader-inv-helper l cl env-cl))
           (all-correctly-loaded? (collect-superclassname1 any env-cl nil)
                                  cl env-cl))
  :hints (("Goal" :induct (loader-inv-helper l cl env-cl)
           :do-not '(generalize)
           :in-theory (enable collect-assignableToName))))



(defthm class-loaded-implies
  (implies (class-loaded? any s)
           (mem any (all-class-names (instance-class-table s))))
  :hints (("Goal" :in-theory (enable class-loaded?))))


(defthm loader-inv-implies
  (implies (and (loader-inv s)
                (no-fatal-error? s))
           (loader-inv-helper (instance-class-table s) 
                              (instance-class-table s)
                              (external-class-table s)))
  :hints (("Goal" :in-theory (enable loader-inv))))


(defthm loader-inv-loaded-class-implies-all-correctly-loaded
  (implies (and (class-loaded? any s)
                (no-fatal-error? s)
                (loader-inv s))
           (all-correctly-loaded? (collect-superclassname1 any 
                                                           (external-class-table s)
                                                           nil)
                                  (instance-class-table s)
                                  (external-class-table s)))
  :hints (("Goal" :in-theory (disable external-class-table)
           :restrict ((loader-inv-helper1-implies-all-correctly-loaded
                       ((l (instance-class-table s)))))
           :do-not '(generalize)
           :do-not-induct t)))



(defthm loader-inv-loaded-class-implies-all-correctly-loaded-generalized-lemma
  (implies (and (class-loaded? p s)
                (no-fatal-error? s)
                (loader-inv s)
                (equal (external-class-table s) env-cl))
           (all-correctly-loaded? (collect-superclassname1 p env-cl nil)
                                  (instance-class-table s)
                                  env-cl))
  :hints (("Goal" :in-theory (disable all-correctly-loaded?
                                      collect-superclassname1 external-class-table))))


(defthm subset-collect-superclass-list1-seen
  (implies (subset seen1 seen2)
           (subset (collect-superclassname1 p env-cl seen2)
                   (collect-superclassname1 p env-cl seen1))))

;;; proved before.

(defthm all-correctly-loaded-subset
  (implies (and (subset a b)
                (all-correctly-loaded? b cl env-cl))
           (all-correctly-loaded? a cl env-cl)))
;; also proved in jvm-dynamic-loading-property.lisp before 



(defthm loader-inv-loaded-class-implies-all-correctly-loaded-generalized
  (implies (and (class-loaded? p s)
                (no-fatal-error? s)
                (loader-inv s)
                (equal (external-class-table s) env-cl))
           (all-correctly-loaded? (collect-superclassname1 p env-cl seen)
                                  (instance-class-table s)
                                  env-cl))
  :hints (("Goal" :in-theory (disable all-correctly-loaded?
                                      collect-superclassname1
                                      external-class-table)
           :restrict ((all-correctly-loaded-subset
                       ((b (collect-superclassname1 p (external-class-table s)  nil))))))))


(defthm collect-superclassname1-equal
  (implies (and (mv-nth 0 (class-by-name-s classname env-cl))
                (not (mem classname seen)))
           (equal (cdr (collect-superclassname1 classname env-cl seen))
                  (collect-superclassname1 (super-s 
                                            (mv-nth 1 (class-by-name-s
                                                       classname env-cl)))
                                           env-cl
                                           (cons classname seen)))))


(defthm class-loaded-still-class-loaded?-load_class2
  (implies (class-loaded? x s)
           (class-loaded? x (load_class2 p s)))
  :hints (("Goal" :in-theory (e/d (load_class2 class-loaded?
                                   add-instance-class-entry)
                                  (isClassTerm make-runtime-class-rep)))))


(defthm class-loaded?-equal
  (implies (and (class-loaded? p s)
                some-error)
           (class-loaded? p (MAKE-STATE pc
                                 any_thread
                                 any_heap
                                 any_thread_table
                                 (class-table s)
                                 any-env
                                 some-error
                                 any_aux)))
  :hints (("Goal" :in-theory (enable class-loaded?))))


(defthm class-loaded-still-class-loaded?
  (implies (class-loaded? x s)
           (class-loaded? x (load_class_x p s seen mode)))
  :hints (("Goal" :do-not '(generalize))))


(defthm load_class2-loads
  (implies (no-fatal-error? (load_class2 p s))
           (class-loaded? p (load_class2 p s)))
  :hints (("Goal" :in-theory (e/d (class-loaded? load_class2 add-instance-class-entry)
                                  (isClassTerm make-runtime-class-rep)))))

(defthm loader-loads
  (implies (no-fatal-error? (load_class_x p s seen 3))
           (class-loaded? p (load_class_x p s seen 3)))
  :hints (("Goal" :expand (load_class_x p s seen 3))))



;;  (ALL-CORRECTLY-LOADED?
;;   (APP (INTERFACES-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
;;        (APP (COLLECT-INTERFACE-X-ENV
;;                  (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
;;                  ENV-CL (CONS CLASSNAME SEEN)
;;                  1)
;;             (COLLECT-INTERFACE-X-ENV
;;                  (INTERFACES-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
;;                  ENV-CL (CONS CLASSNAME SEEN)
;;                  2)))
;;   CL ENV-CL)).


(defthm subset-collect-interface-x-env-mode-1-collect-AssignableToName
  (subset (collect-interface-x-env p env-cl seen 1)
          (collect-assignabletoname p env-cl))
  :hints (("Goal" :in-theory (enable collect-assignabletoname))))


(defun all-assignable-to-name (p env-cl)
  (if (endp p) nil
    (app (collect-assignabletoname (car p) env-cl)
         (all-assignable-to-name (cdr p) env-cl))))


(defthm subset-collect-interface-x-env-mode-2-collect-AssignableToName
  (subset (collect-interface-x-env p env-cl seen 2)
          (all-assignable-to-name p env-cl)))



(defthm loader-inv-helper-implies-assignabletoname-loaded
  (implies (and (correctly-loaded? p cl env-cl)
                (loader-inv-helper cl cl env-cl))
           (all-correctly-loaded? (collect-assignabletoname p env-cl)
                                  cl env-cl)))


(defthm loader-inv-helper-implies-all-assignabletoname-loaded
  (implies (and (all-correctly-loaded? ps cl env-cl)
                (loader-inv-helper cl cl env-cl))
           (all-correctly-loaded? (all-assignable-to-name ps env-cl)
                                  cl env-cl)))

(defthm subset-relation-assignable
  (subset 
   (APP (COLLECT-INTERFACE-X-ENV
         (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
         ENV-CL (CONS CLASSNAME SEEN)
         1)
        (COLLECT-INTERFACE-X-ENV
         (INTERFACES-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
         ENV-CL (CONS CLASSNAME SEEN)
         2))
   (app (collect-assignabletoname  (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S
                                                       CLASSNAME ENV-CL))) env-cl)
        (all-assignable-to-name (interfaces-s (mv-nth 1 (class-by-name-s
                                                         classname env-cl))) env-cl))))

(defthm subset-relation-assignable-2
  (subset interfaces
          (all-assignable-to-name interfaces env-cl)))



(defthm subset-relation-assignable-specific
  (subset   (APP (INTERFACES-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
                 (APP (COLLECT-INTERFACE-X-ENV
                       (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
                       ENV-CL (CONS CLASSNAME SEEN)
                       1)
                      (COLLECT-INTERFACE-X-ENV
                       (INTERFACES-S (MV-NTH 1 (CLASS-BY-NAME-S CLASSNAME ENV-CL)))
                       ENV-CL (CONS CLASSNAME SEEN)
                       2)))
            (app (collect-assignabletoname  (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S
                                                                CLASSNAME ENV-CL))) env-cl)
                 (all-assignable-to-name (interfaces-s (mv-nth 1 (class-by-name-s
                                                                  classname env-cl))) env-cl))))




(defthm all-correct-loaded-implies-interfaces-correctly-loaded
  (implies (and (all-correctly-loaded? (interfaces-s  (mv-nth 1 (class-by-name-s
                                                                 classname env-cl)))
                                       cl
                                       env-cl)
                (correctly-loaded? (super-s (mv-nth 1 (class-by-name-s 
                                                       classname env-cl)))
                                   cl env-cl)
                (loader-inv-helper cl cl env-cl))
           (all-correctly-loaded? (cdr (collect-interface-x-env
                                        classname env-cl seen 1))
                                       cl env-cl))
  :hints (("Goal" :do-not-induct t
           :expand (collect-interface-x-env classname env-cl seen 1)
           :restrict ((all-correctly-loaded-subset
                       ((b (app (collect-assignabletoname  (SUPER-S (MV-NTH 1 (CLASS-BY-NAME-S
                                                                               CLASSNAME ENV-CL))) env-cl)
                                (all-assignable-to-name (interfaces-s (mv-nth 1 (class-by-name-s
                                                                                 classname env-cl))) env-cl)))))))))
        
(defthm loader-inv-implies-loader-helper
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (equal (external-class-table s) env-cl))
           (loader-inv-helper (instance-class-table s)
                              (instance-class-table s) 
                              env-cl))
  :hints (("Goal" :in-theory (enable loader-inv))))
 

(include-book "../M6-DJVM-shared/jvm-loader-guard-verification-support-load-cp-guard")


(defthm wff-instance-class-table-strong-bound
  (implies (and (class-by-name any cl)
                (wff-instance-class-table-strong cl))
           (wff-class-rep-strong (class-by-name any cl))))


(defthm wff-class-rep-strong-implies-wff-fields
  (implies (wff-class-rep-strong class-rep)
           (wff-class-fields (fields class-rep))))




(defthm loader-inv-loaded-build-immediate-data
  (implies (and (loader-inv s)
                (class-loaded? any s))
           (build-immediate-instance-data-guard any s))
  :hints (("Goal" :in-theory (e/d (class-loaded? loader-inv)
                                  (fields)))))
                
(defthm loader-inv-loaded-build-instance-data
  (implies (and (loader-inv s)
                (all-loaded? l s))
           (build-a-java-visible-instance-data-guard l s))
  :hints (("Goal" :in-theory (disable build-immediate-instance-data-guard))))


(defthm loader-inv-and-loaded-implies-all-loaded-specific
    (implies (and (loader-inv s)
                  (no-fatal-error? s)
                  (class-loaded? classname s))
             (all-loaded? (collect-superclassname1 classname
                                                   (env-class-table (env s)) nil)
                          s))
    :hints (("Goal" :use ((:instance
                           loader-inv-and-loaded-implies-all-loaded
                           (seen nil)))
             :in-theory (disable loader-inv-and-loaded-implies-all-loaded))))


(defthm loader-inv-loaded-ready-create-instance
  (implies (and (loader-inv s)
                (wff-heap (heap s))
                (no-fatal-error? s)
                (class-loaded? any s))
           (build-a-java-visible-instance-guard any s))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))



(defthm loader-inv-java-lang-Object-loaded-implies-load_cp_entry_guard
  (implies (and (loader-inv s)
                (wff-heap (heap s))
                (no-fatal-error? s)
                (wff-constant-pool-entry-s cp)
                (class-loaded? "java.lang.Object" s))
           (load_cp_entry_guard cp s)))

(defthm load_cp_entries_guard_loader-inv
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (wff-heap (heap s))
                (wff-constant-pool-s cps)
                (class-loaded? "java.lang.Object" s))
           (load_cp_entries_guard cps s)))



(defthm runtime-method-rep-guards-assertion-in-wff-class-table
  (implies (and (wff-static-class-table-strong env-cl)
                (mv-nth 0 (class-by-name-s p env-cl)))
           (runtime-method-rep-guards (methods-s (mv-nth 1 (class-by-name-s p env-cl))))))




(defthm if-loaded-then-well-formed
  (IMPLIES (AND (LOADER-INV S)
                (class-loaded? p s))
           (wff-class-rep (CLASS-BY-NAME p (INSTANCE-CLASS-TABLE S))))
  :hints (("Goal" :in-theory (enable loader-inv class-loaded?))))


(in-theory (disable wff-class-rep))



;; not necessary

(defthm wff-class-rep-MAKE-RUNTIME-CLASS-REP-generalize
  (implies (and (wff-class-rep-static class-desc)
                (integerp new-address)
                (true-listp dynamic-cp))
           (wff-class-rep (make-runtime-class-rep 
                           classname
                           (super-s class-desc)
                           dynamic-cp
                           (runtime-instance-fields-rep1 
                            (fields-s class-desc) classname)                    
                           (runtime-methods-rep1 
                            (methods-s class-desc) classname)
                           (interfaces-s class-desc)
                           (runtime-static-fields-rep1 
                            (fields-s class-desc) classname dynamic-cp)
                           any
                           (accessflags-s class-desc) 
                           -1            
                           new-address)))
  :hints (("Goal" :in-theory (enable  accessflags-s
                              wff-class-rep-static interfaces-s
                              make-runtime-class-rep wff-class-rep))))


(in-theory (disable fields-s accessflags-s))


(defthm wff-instance-class-table-preserved-load_class2
  (implies (and (wff-instance-class-table (instance-class-table s))
                (wff-static-class-table (external-class-table s)))
           (wff-instance-class-table (instance-class-table 
                                      (load_class2 p s))))
  :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry)
                                  (wff-class-rep make-runtime-class-rep)))))


(defthm wff-instance-class-table-preserved
  (implies (and (wff-instance-class-table (instance-class-table s))
                (wff-static-class-table (external-class-table s)))
           (wff-instance-class-table (instance-class-table (load_class_x p s seen mode)))))


(defthm wff-static-class-table-strong-implies-found-wff-fields-s
  (implies (and (mv-nth 0 (class-by-name-s p env-cl))
                (wff-static-class-table-strong env-cl))
           (wff-fields-s (fields-s (mv-nth 1 (class-by-name-s p env-cl))))))


(defthm wff-constant-pool-s-implied-by-wff-static-class-table-strong
  (implies (and (wff-static-class-table-strong env-cl)
                (mv-nth 0 (class-by-name-s p env-cl)))
           (wff-constant-pool-s (constantpool-s (mv-nth 1 (class-by-name-s p
                                                                           env-cl))))))


(in-theory (disable constantpool-s))


(verify-guards load_class_x
               :hints (("Goal" 
                        :in-theory (disable all-correctly-loaded?)
                        :expand 
                        ((load_class_x p s seen 2)
                         (LOAD_CLASS_X
                          P
                          (LOAD_CLASS_X
                           (SUPER-S (MV-NTH 1
                                            (CLASS-BY-NAME-S P (ENV-CLASS-TABLE (ENV S)))))
                           S (CONS P SEEN)
                           3)
                          SEEN 1)))))



(defthm loader-inv-set-current-thread
  (implies (loader-inv s)
           (loader-inv (state-set-current-thread any s))))

(defthm wff-state-state-set-thread
  (implies (wff-state s)
           (wff-state (state-set-current-thread any s)))
  :hints (("Goal" :in-theory (enable state-set-current-thread))))


(verify-guards load_class)

;----------------------------------------------------------------------


(local (in-theory (disable wff-array-class-table-rep
                           arrayClassLoaded?
                           make-array-type
                           array-type?
                           array-base-type
                           wff-class-rep instance-class-table)))

(defthm bound-implies-array-class-rep-wff
  (implies (and (ARRAY-CLASS-BY-NAME any acl)
                (WFF-ARRAY-CLASS-TABLE acl))
           (WFF-ARRAY-CLASS-TABLE-REP (ARRAY-CLASS-BY-NAME any acl))))


(defthm hack-1
  (IMPLIES (AND (TRUE-LISTP TYPE4)
                (EQUAL (LEN TYPE4) 0))
           (NOT TYPE4))
  :rule-classes nil)


(defthm list-cons-rewrite-hack
  (implies (and (true-listp type2)
                (consp type2)
                (equal (len type2) 1))
           (equal (CONS 'ARRAY TYPE2)
                  (list 'ARRAY (car type2))))
  :hints (("Goal" :do-not-induct t)
          ("Goal''" :use hack-1))
  :rule-classes nil)



(defthm array-loaded-implies-wff-array-class-rep
  (implies (and (Arrayclassloaded? (array-base-type type) s)
                (array-type? type)
                (wff-array-class-table (array-class-table s)))
           (wff-array-class-table-rep 
            (array-class-by-name type (array-class-table s))))
  :hints (("Goal" :in-theory (e/d (arrayclassloaded? make-array-type
                                                     array-type?
                                                     array-base-type)
                                  (bound-implies-array-class-rep-wff)))
          ("Subgoal 1" :use ((:instance  
                              bound-implies-array-class-rep-wff
                              (any (LIST 'ARRAY (CAR ACL2::TYPE2)))
                              (acl (array-class-table s)))
                             (:instance 
                              list-cons-rewrite-hack
                              (type2 acl2::type2))))))


(defthm class-loaded-implies-wff-class-rep
  (implies (and (wff-instance-class-table (instance-class-table s))
                (class-loaded? any s))
           (wff-class-rep (class-by-name any (instance-class-table s))))
  :hints (("Goal" :in-theory (enable class-loaded?))))

(verify-guards load_array_class2)


;----------------------------------------------------------------------
(defthm wff-state-load_array_class2
  (implies (wff-state s)
           (wff-state (load_array_class2 any s))))

(defthm wff-state-load_array_class
  (implies (wff-state s)
           (wff-state (load_array_class any s)))
  :hints (("Goal" :in-theory (disable load_array_class2))))

;----------------------------------------------------------------------

(defthm array-class-table-make-state-make-class-table
  (equal (array-class-table (make-state 
                             any_pc
                             any_th
                             any_heap
                             any_tt
                             (make-class-table any_cl
                                               some_acl)
                             any_env
                             any_ef
                             any_aux))
         some_acl)
  :hints (("Goal" :in-theory (enable array-class-table make-class-table))))


(local (in-theory (enable wff-array-class-table-rep
                           arrayClassLoaded?
                           make-array-type
                           array-type?
                           array-base-type
                           wff-class-rep instance-class-table)))



(defthm wff-array-class-table-load_array_class2
  (implies (wff-array-class-table (array-class-table s))
           (wff-array-class-table (array-class-table (load_array_class2 any s)))))

(defthm array-class-table-state-set-current-thread
  (equal (array-class-table (state-set-current-thread any s))
         (array-class-table s)))




(defthm array-class-table-equal 
  (equal (ARRAY-CLASS-TABLE
          (MAKE-STATE any_pc
                      any_th
                      any_hp
                      any_tt
                      (CLASS-TABLE S)
                      any_env
                      any_ef
                      any_aux))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable array-class-table))))


(defthm load_cp_entry_change_not_array_class_table
  (equal (array-class-table (mv-nth 1 (load_cp_entry any s)))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm load_cp_entries_change_not_array_class_table
  (equal (array-class-table (mv-nth 1 (load_cp_entries cps s)))
         (array-class-table s)))


(defthm load_class2_change_not_array_class_table
  (equal (array-class-table (load_class2 any s))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable load_class2))))


(defthm load_class_x_change_not_array_class_table
  (equal (array-class-table (load_class_x any s seen mode))
         (array-class-table s)))

(defthm wff-array-class-table-load_array_class
  (implies (wff-array-class-table (array-class-table s))
           (wff-array-class-table (array-class-table (load_array_class any
                                                                       s))))
  :hints (("Goal" :in-theory (disable load_array_class2 wff-array-class-table)
           :do-not '(generalize))))


(defthm wff-class-table-load_array_class2
  (implies (wff-class-table  (class-table s))
           (wff-class-table (class-table (load_array_class2 any s)))))

(defthm wff-class-table-load_class2
  (implies (wff-class-table  (class-table s))
           (wff-class-table (class-table (load_class2 any s)))))

(defthm wff-class-table-load_array_class
  (implies (wff-class-table  (class-table s))
           (wff-class-table (class-table (load_array_class any s))))
  :hints (("Goal" :in-theory (disable load_array_class2))))


(defthm wff-heap-load_array_class2
  (implies (wff-heap (heap s))
           (wff-heap (heap (load_array_class2 any s))))
  :hints (("Goal" :in-theory (enable wff-heap))))

(defthm wff-heap-load_array_class
  (implies (wff-heap (heap s))
           (wff-heap (heap (load_array_class any s))))
  :hints (("Goal" :in-theory (e/d ()
                                  (load_array_class2)))))


(defthm load_array_class2-array-class-loaded
  (ArrayClassLoaded? any (load_array_class2 any s)))


(defthm load_array_class-array-class-loaded
  (implies (no-fatal-error? (load_array_class any s))
           (ArrayClassLoaded? any (load_array_class any s)))
  :hints (("Goal" :in-theory (disable load_array_class2
                                      ArrayClassLoaded?))))

;; (defun base-types (type)
;;   (if (array-type? type)
;;       (cons type (base-types (array-base-type type)))
;;     (list type)))


(defthm load-a-base-type-will-not-load-a-type-load_class_x
  (equal (arrayclassloaded? base-type 
                            (load_class_x any s ss mode))
         (arrayclassloaded? base-type s)))


(defthm arrayClassloaded-state-set-current-thread
  (equal (arrayclassloaded? base-type 
                            (state-set-current-thread any s))
         (arrayclassloaded? base-type s)))



(defthm load-a-base-type-will-not-load-a-type-load_array_class2
  (implies (not (equal some-base-type base-type))
           (equal (arrayclassloaded? base-type 
                                     (load_array_class2 some-base-type  s))
                  (arrayclassloaded? base-type s))))


(defthm array-type?-array-base-type-less
  (implies (consp type)
           (< (acl2-count (array-base-type type))
              (acl2-count type)))
  :hints (("Goal'" :expand (nth 1 type)))
  :rule-classes :linear)


(defthm array-type?-consp
  (implies (array-type? type)
           (consp type))
  :rule-classes :forward-chaining)

;; (defthm not-mem-base-type-base-types
;;   (not (mem base-type (base-types (array-base-type base-type))))

(defthm mem-base-types
   (implies (mem x (base-types y))
            (<= (acl2-count x) 
                (acl2-count y)))
   :hints (("Goal" :induct (base-types y)))
   :rule-classes :linear)

;; (defun ordered (l)
;;   (if (endp l) t
;;     (if (endp (cdr l)) t
;;       (and (>  (acl2-count (car l))
;;                (acl2-count (cadr l)))
;;            (ordered (cdr l))))))

;; (defthm ordered-base-types
;;    (ordered (base-types s)))


(defthm mem-base-types-implies-not-equal
  (implies (and (mem some-base-type (base-types (array-base-type base-type)))
                (array-type? base-type))
           (not (equal some-base-type base-type)))
  :hints (("Goal" :use ((:instance mem-base-types
                                   (x some-base-type)
                                   (y base-type))
                        (:instance array-type?-array-base-type-less
                                   (type base-type))))))


(defthm mem-type-base-types
  (mem type (base-types type)))

(defthm mem-base-type-member
  (implies (and (mem some-base-type (base-types type))
                (array-type? some-base-type))
           (mem (array-base-type some-base-type) (base-types type)))
  :hints (("Goal" :in-theory (disable array-base-type
                                      array-type?))))
                                      

(defthm load-a-base-type-will-not-load-a-type
  (implies (and (array-type? base-type)
                (mem some-base-type (base-types (array-base-type base-type))))
           (equal (arrayclassloaded? base-type 
                                     (load_array_class some-base-type  s))
                  (arrayclassloaded? base-type s)))
  :hints (("Goal" :in-theory (disable load_array_class2 
                                      array-base-type
                                      arrayclassloaded?
                                      array-type?)
           :do-not '(generalize))))
                            

;; (defthm load_array_class2_wff_array_rep
;;   (wff-array-class-table-rep
;;    (array-class-by-name type
;;                         (array-class-table (load_array_class2 type s))))
;;   :hints (("Goal" :expand (load_array_class2 type s))))


;; (defthm load_array_class_wff_array_rep
;;   (implies (no-fatal-error? (load_array_class type s))
;;            (wff-array-class-table-rep
;;             (array-class-by-name type
;;                                  (array-class-table (load_array_class type
;;                                                                       s)))))
;;   :hints (("Goal" :in-theory (disable load_array_class2)
;;            :do-not '(generalize))))


(in-theory (disable instance-class-table))

(defthm wff-instance-class-table-perserved-by-load_array_class2
  (implies (wff-instance-class-table (instance-class-table s))
           (wff-instance-class-table (instance-class-table 
                                      (load_array_class2 any s)))))

(defthm wff-instance-class-table-perserved-by-state-set-current-thread
  (implies (wff-instance-class-table (instance-class-table s))
           (wff-instance-class-table (instance-class-table
                                      (state-set-current-thread any s)))))

(defthm wff-instance-class-table-perserved-by-load_array_class
   (implies (and (wff-instance-class-table (instance-class-table s))
                 (wff-static-class-table (external-class-table s)))
            (wff-instance-class-table (instance-class-table 
                                       (load_array_class any s))))
   :hints (("Goal" :in-theory (disable load_array_class2))))




;----------------------------------------------------------------------


(defthm class-table-load_cp_entry-no-change
  (equal (class-table (mv-nth 1 (load_cp_entry cp s)))
         (class-table s))
  :hints (("Goal" :in-theory (enable load_cp_entry))))


(defthm instance-class-table-load_cp_entry-no-change
  (equal (instance-class-table (mv-nth 1 (load_cp_entry cp s)))
         (instance-class-table  s))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm class-by-name-add-intstance-entry
  (equal (class-by-name any (add-instance-class-entry 
                             class-rep
                             cl))
         (if (equal any (classname class-rep))
             class-rep
           (class-by-name any cl)))
  :hints (("Goal" :in-theory (enable add-instance-class-entry))))
                                                     

(defthm class-by-name-equal-after-load_class2
  (implies (not (equal any anyx))
           (equal (class-by-name any (instance-class-table (load_class2 anyx s)))
                  (class-by-name any (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (load_class2) (make-runtime-class-rep)))))

;----------------------------------------------------------------------


(defun all-found? (names env-cl)
  (if (endp names) t
    (mv-let (found class-desc)
            (class-by-name-s (car names) env-cl)
            (declare (ignore class-desc))
            (and found
                 (all-found? (cdr names) env-cl)))))



(defthm all-correctly-loaded-implies-collect-superclass-list
  (implies (and (all-correctly-loaded? 
                 (collect-superclassname1 classname env-cl seen)
                 cl 
                 env-cl)
                (all-found? (all-class-names cl) env-cl))
           (equal (collect-superclass-list1 classname cl seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not '(fertilize)
           :in-theory (enable correctly-loaded?))))


(defthm correctly-loaded-is-preserved-by-load_class2-x
  (implies (and (correctly-loaded? any (instance-class-table s) 
                                   env-cl)
                (equal (external-class-table s) env-cl))
           (correctly-loaded? any (instance-class-table (load_class2 anyx s))
                              env-cl)))



(defthm all-correctly-loaded-is-preserved-by-load_class2
  (implies (and (all-correctly-loaded? anylist (instance-class-table s) 
                                   env-cl)
                (equal (external-class-table s) env-cl))
           (all-correctly-loaded? anylist (instance-class-table (load_class2 anyx s))
                                  env-cl)))

(defthm all-found?-all-found-after-load-class2
  (implies (and (all-found? (all-class-names (instance-class-table s)) env-cl)
                (mv-nth 0 (class-by-name-s any env-cl))
                (equal (external-class-table s) env-cl))
           (all-found? (all-class-names  (instance-class-table (load_class2 any
                                                                            s)))
                       env-cl))
  :hints (("Goal" :in-theory (enable load_class2 all-class-names 
                                     classname add-instance-class-entry))))





(defthm load_class2-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (mv-nth 0 (class-by-name-s any env-cl))
                ;; why I need this? 
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table (load_class2 any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable collect-superclassname1 all-correctly-loaded?
                               collect-superclass-list1
                               all-correctly-loaded-implies-collect-superclass-list
                               all-correctly-loaded-is-preserved-by-load_class2)
           :restrict ((all-correctly-loaded-implies-collect-superclass-list
                       ((env-cl env-cl))))
           :use ((:instance all-correctly-loaded-is-preserved-by-load_class2
                            (anylist (collect-superclassname1 classname
                                                                env-cl seen))
                            (anyx any))
                 (:instance
                  all-correctly-loaded-implies-collect-superclass-list
                  (cl (instance-class-table (load_class2 any s))))))))
;; this is really strange!! 



;; the following is not true!! 
;; suppose loader-inv is not hold, anyx is an unloaded super class of some
;; class 
;;
;;
;; (defthm not-on-super-chain-does-not-affect-collection
;;   (implies (and (not (mem anyx (collect-superclass-list1 any 
;;                                                          (instance-class-table s)
;;                                                          seen)))
;;                 ;; (not (mem anyx seen))
;;                 (consp (collect-superclass-list1 any (instance-class-table s) seen)))
;;            (equal (collect-superclass-list1 any (instance-class-table (load_class2 anyx s)) seen)
;;                   (collect-superclass-list1 any (instance-class-table s)
;;                                             seen)))
;;   :hints (("Goal" :in-theory (e/d (class-loaded?) (isClassTerm classname
;;                                                                classsuperclassname))
;;            :do-not '(generalize))
;;           ("Subgoal *1/4" :expand (COLLECT-SUPERCLASS-LIST1
;;            (CLASSSUPERCLASSNAME (CLASS-BY-NAME ANY (INSTANCE-CLASS-TABLE S)))
;;            (INSTANCE-CLASS-TABLE S)
;;            (CONS ANY SEEN)))))

                                                
;; (defthm not-on-super-chain-does-not-affect-collection
;;   (implies (and (equal (collect-superclass-list1 any (instance-class-table s) seen)
;;                        (collect-superclassname1 any (external-class-table s) seen))
;;                 (mv-nth 0 (class-by-name-s anyx (external-class-table s))))
;;            (equal (collect-superclass-list1 any (instance-class-table (load_class2 anyx s)) seen)
;;                   (collect-superclassname1 any (external-class-table s) seen))))


(defthm loader-inv-no-err-implies-loaded-class-super-loaded
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (equal (external-class-table s) env-cl)
                (class-loaded? any s))
           (all-correctly-loaded? (collect-superclassname1 any
                                                           env-cl seen)
                                  (instance-class-table s)
                                env-cl)))
;;
;; duplicated: loader-inv-loaded-class-implies-all-correctly-loaded-generalized
;;                                  

(defthm mem-name-collect-assignable
  (mem  n (collect-assignabletoname n env-cl)))

(defthm all-correctly-loaded?-correctly-loaded
  (implies (and (mem n l)
                (all-correctly-loaded? l cl env-cl))
           (correctly-loaded? n cl env-cl)))


(defthm correctly-loaded?-found
  (implies (correctly-loaded? n cl env-cl)
           (mv-nth 0 (class-by-name-s n env-cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))
  

(defthm loader-inv-helper1-implies-found
  (implies (loader-inv-helper1 class cl env-cl)
           (mv-nth 0 (class-by-name-s (classname class) env-cl)))
  :hints (("Goal" :restrict ((all-correctly-loaded?-correctly-loaded
                              ((l (collect-assignabletoname (classname class)
                                                            env-cl))
                               (n (classname class)))))
           :use ((:instance all-correctly-loaded?-correctly-loaded
                            (n (classname class))
                            (l (collect-assignabletoname (classname class) env-cl)))))))


;; some times. the rewrite rule are not so good. give use hints! 

;; no the mv-nth 0, not expecting it to fire in most cases!! 

(defthm load-inv-helper-implies-all-found?
  (implies (loader-inv-helper l cl env-cl)
           (all-found? (all-class-names l) env-cl))
  :hints (("Goal" :in-theory (disable loader-inv-helper1 mv-nth))))

(defthm loader-inv-no-err-implies-all-found?
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (equal (external-class-table s) env-cl))
           (all-found? (all-class-names (instance-class-table s))
                       env-cl))
  :hints (("Goal" :in-theory (enable loader-inv))))



;; (defthm collect-superclass-list1-does-not-change-load_class2
;;   (implies (and (loader-inv s)
;;                 (no-fatal-error? s)
;;                 (mv-nth 0 (class-by-name-s anyx (external-class-table s)))
;;                 (class-loaded? any s))
;;            (equal (collect-superclass-list1 any (instance-class-table (load_class2 anyx s)) seen)
;;                   (collect-superclassname1 any (external-class-table s)
;;                                            seen)))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (disable collect-superclass-list1 collect-superclassname1
;;                                ;;external-class-table
;;                                mv-nth)
;;            :restrict ((load_class2-do-not-change-collect-superclass-list
;;                        ((env-cl (env-class-table (env s)))))))))

;; ;;;
;; ;;; well this is not so useful!! because we can not guarantee the
;; ;;; no-fatal-error?
;; ;;;
;; ;;; We should stick with load class preserved all-correctly-loaded? of already
;; ;;; loaded classes
;; ;;;


;; (defthm load_class2-do-not-change-collect-superclass-list
;;   (implies (and (all-correctly-loaded? (collect-superclassname1 classname
;;                                                                 env-cl seen)
;;                                        (instance-class-table s)
;;                                        env-cl)
;;                 (mv-nth 0 (class-by-name-s any env-cl))
;;                 ;; why I need this? 
;;                 (equal (external-class-table s) env-cl)
;;                 (all-found? (all-class-names (instance-class-table s)) env-cl))
;;            (equal (collect-superclass-list1 classname (instance-class-table (load_class2 any s)) seen)
;;                   (collect-superclassname1 classname env-cl seen)))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (disable collect-superclassname1 all-correctly-loaded?
;;                                collect-superclass-list1
;;                                all-correctly-loaded-implies-collect-superclass-list
;;                                all-correctly-loaded-is-preserved-by-load_class2)
;;            :restrict ((all-correctly-loaded-implies-collect-superclass-list
;;                        ((env-cl env-cl))))
;;            :use ((:instance all-correctly-loaded-is-preserved-by-load_class2
;;                             (anylist (collect-superclassname1 classname
;;                                                                 env-cl seen))
;;                             (anyx any))
;;                  (:instance
;;                   all-correctly-loaded-implies-collect-superclass-list
;;                   (cl (instance-class-table (load_class2 any s))))))))

;;
;; and extend this to load_class_x and load_array_class2, load_array_class!! 
;;


(defthm load_class2-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (mv-nth 0 (class-by-name-s any env-cl))
                ;; why I need this? 
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table (load_class2 any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable collect-superclassname1 all-correctly-loaded?
                               collect-superclass-list1
                               all-correctly-loaded-implies-collect-superclass-list
                               all-correctly-loaded-is-preserved-by-load_class2)
           :restrict ((all-correctly-loaded-implies-collect-superclass-list
                       ((env-cl env-cl))))
           :use ((:instance all-correctly-loaded-is-preserved-by-load_class2
                            (anylist (collect-superclassname1 classname
                                                                env-cl seen))
                            (anyx any))
                 (:instance
                  all-correctly-loaded-implies-collect-superclass-list
                  (cl (instance-class-table (load_class2 any s))))))))



(defthm load_class2-do-not-change-collect-superclass-list-strong
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table (load_class2 any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable collect-superclassname1 all-correctly-loaded?
                               collect-superclass-list1 ;;external-class-table
                               all-correctly-loaded-implies-collect-superclass-list
                               all-correctly-loaded-is-preserved-by-load_class2)
           :cases ((mv-nth 0 (class-by-name-s any env-cl))))
          ("Subgoal 2" :expand (load_class2 any s)
           :use ((:instance
                  all-correctly-loaded-implies-collect-superclass-list
                  (cl (instance-class-table s))
                  (env-cl (external-class-table s)))))))


(defthm all-correctly-loaded-still-correctly-loaded
  (implies (and (all-correctly-loaded? l (instance-class-table s) env-cl)
                (equal (external-class-table s) env-cl))
           (all-correctly-loaded? l (instance-class-table (load_class_x any s
                                                                        seen
                                                                        mode))
                                  env-cl)))


(defthm all-found?-all-found-after-load-class2-strong
  (implies (and (all-found? (all-class-names (instance-class-table s)) env-cl)
                (equal (external-class-table s) env-cl))
           (all-found? (all-class-names  (instance-class-table (load_class2 any
                                                                            s)))
                       env-cl))
  :hints (("Goal" :cases ((mv-nth 0 (class-by-name-s any env-cl))))
          ("Subgoal 2" :expand (load_class2 any s))))


(defthm all-found?-still-all-found?
  (implies (and (all-found? (all-class-names (instance-class-table s)) env-cl)
                (equal (external-class-table s) env-cl))
           (all-found? (all-class-names  (instance-class-table (load_class_x
                                                                any s ss mode)))
                       env-cl)))



;; (defthm |Subgoal *1/6|
;;   (IMPLIES
;;    (AND
;;     (EQUAL
;;      (COLLECT-SUPERCLASS-LIST1
;;       CLASSNAME
;;       (INSTANCE-CLASS-TABLE (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SS 2)
;;                                           SS 1))
;;       SEEN)
;;      (COLLECT-SUPERCLASSNAME1 CLASSNAME (ENV-CLASS-TABLE (ENV S))
;;                               SEEN))
;;     (ALL-CORRECTLY-LOADED?
;;      (COLLECT-SUPERCLASSNAME1 CLASSNAME (ENV-CLASS-TABLE (ENV S))
;;                               SEEN)
;;      (INSTANCE-CLASS-TABLE S)
;;      (ENV-CLASS-TABLE (ENV S)))
;;     (ALL-FOUND? (ALL-CLASS-NAMES (INSTANCE-CLASS-TABLE S))
;;                 (ENV-CLASS-TABLE (ENV S))))
;;   (EQUAL (COLLECT-SUPERCLASS-LIST1
;;           CLASSNAME
;;           (INSTANCE-CLASS-TABLE
;;            (LOAD_CLASS2 ANY
;;                         (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SS 2)
;;                                       SS 1)))
;;           SEEN)
;;          (COLLECT-SUPERCLASSNAME1 CLASSNAME (ENV-CLASS-TABLE (ENV S))
;;                                   SEEN)))
;;   :hints (("Goal" :do-not-induct t
;;            :restrict ((load_class2-do-not-change-collect-superclass-list-strong
;;                        ((env-cl (env-class-table (env s)))))))))


(defthm load_class_x-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table
                                                       (load_class_x any s ss mode)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable collect-superclassname1 collect-superclass-list1
                               all-correctly-loaded?)
           :restrict ((load_class2-do-not-change-collect-superclass-list-strong
                       ((env-cl (env-class-table (env s))))))
                         ;;; special attention here!! 
           :induct (load_class_x any s ss mode))))




(defthm load_array_class2-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table
                                                       (load_array_class2 any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable collect-superclassname1 collect-superclass-list1
                               all-correctly-loaded?))))




(defthm load_array_class2-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table
                                                       (load_array_class2 any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable collect-superclassname1 collect-superclass-list1
                               all-correctly-loaded?))))



(defthm load_array_class-do-not-change-collect-superclass-list
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                env-cl seen)
                                       (instance-class-table s)
                                       env-cl)
                (equal (external-class-table s) env-cl)
                (all-found? (all-class-names (instance-class-table s)) env-cl))
           (equal (collect-superclass-list1 classname (instance-class-table
                                                       (load_array_class any s)) seen)
                  (collect-superclassname1 classname env-cl seen)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable collect-superclassname1 collect-superclass-list1
                               all-correctly-loaded?))))



(defthm load_array_class-do-not-change-collect-superclass-list-specific
  (implies (and (all-correctly-loaded? (collect-superclassname1 classname
                                                                (external-class-table s) seen)
                                       (instance-class-table s)
                                       (external-class-table s))
                (all-found? (all-class-names (instance-class-table s))
                            (external-class-table s)))
           (equal (collect-superclass-list1 classname (instance-class-table
                                                       (load_array_class any s)) seen)
                  (collect-superclassname1 classname (external-class-table s)  seen)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable collect-superclassname1 collect-superclass-list1
                               all-correctly-loaded?))))


(defthm env-no-change-load-array-class
  (equal (env (load_array_class any s))
         (env s)))

;; (defthm build-immediate-instance-data-guard-not-affected-by-load-class2
;;   (implies (and (build-immediate-instance-data-guard any s)
;;                 (wff-static-class-table (external-class-table s)))
;;            (build-immediate-instance-data-guard any (load_class2 anyx s)))
;;   :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry 
;;                                                fields
;;                                    build-immediate-instance-data-guard)
;;                                   (make-runtime-class-rep wff-class-rep)))))


;; (defthm build-immediate-instance-data-guard-not-affected-by-load-array
;;   (implies (build-immediate-instance-data-guard any s)
;;            (build-immediate-instance-data-guard any (load_array_class anyx s))))


;; proved in jvm-loader-guard-verification-support-load-cp-guard.cert!!
(defthm
  class-table-correct-extension-does-not-change-build-an-java-instance-data-guard
  (implies (and (build-a-java-visible-instance-data-guard classnames s)
                (all-loaded? classnames s)
                (loader-inv s))
           (build-a-java-visible-instance-data-guard
               classnames (load_class_x anyx s seen mode)))
  :hints (("Goal" :in-theory (disable load_class_x class-loaded?))))




; (skip-proofs 
;  (defthm loader-inv-and-loaded-implies-all-loaded
;    (implies (and (loader-inv s)
;                  (class-loaded? classname s))
;             (all-loaded? (COLLECT-SUPERCLASS-LIST1 classname
;                                                    (INSTANCE-CLASS-TABLE S)
;                                                    seen)
;                          s))))


(defthm loader-inv-and-loaded-implies-all-loaded
  (implies (and (loader-inv s)
                (class-loaded? classname s))
           (all-loaded? (COLLECT-SUPERCLASS-LIST1 classname
                                                  (INSTANCE-CLASS-TABLE S)
                                                  seen)
                          s)))


(defthm build-immediate-instance-data-guard-equal-1
   (implies (and (integerp int_pc)
                 (wff-class-table (class-table s))
                 (wff-state s))
            (equal (build-immediate-instance-data-guard
                    classname
                    (make-state 
                     int_pc any_thread wff_heap any_tt 
                     (make-class-table 
                      (instance-class-table s)
                      any_acl)
                     any_env
                     any_errorflag
                     any_aux))
                   (build-immediate-instance-data-guard
                    classname s)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable build-immediate-instance-data-guard))))


(defthm build-a-java-visible-instance-data-guard-equal-1
   (implies (and (integerp int_pc)
                 (wff-class-table (class-table s))
                 (wff-state s))
            (equal (build-a-java-visible-instance-data-guard
                    classnames
                    (make-state 
                     int_pc any_thread wff_heap any_tt 
                     (make-class-table 
                      (instance-class-table s)
                      any_acl)
                     any_env
                     any_errorflag
                     any_aux))
                   (build-a-java-visible-instance-data-guard  
                    classnames s)))
   :hints (("Goal" :do-not '(generalize))))

(defthm build-a-java-visible-instance-data-guard-equal-state-set-cur-thread
  (implies (wff-state s)
            (equal (build-a-java-visible-instance-data-guard
                    classnames
                    (state-set-current-thread any s))
                   (build-a-java-visible-instance-data-guard  
                    classnames s)))
   :hints (("Goal" :in-theory (enable state-set-current-thread))))


;; (defthm build-a-j
;;    (BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD
;;         CLASSNAMES
;;         (MAKE-STATE
;;              (PC S)
;;              (CURRENT-THREAD S)
;;              (BIND (LEN (HEAP S))
;;                    (LIST* 'OBJECT
;;                           '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
;;                                         "java.lang.Class")
;;                           (LIST 'SPECIFIC-INFO
;;                                 'ARRAY_CLASS
;;                                 (LIST 'ARRAY ANYX))
;;                           '((("java.lang.Class")
;;                              ("java.lang.Object"))))
;;                    (HEAP S))
;;              (THREAD-TABLE S)
;;              (MAKE-CLASS-TABLE
;;                   (INSTANCE-CLASS-TABLE S)
;;                   (CONS (LIST (LIST 'ARRAY ANYX)
;;                               '(ACCESSFLAGS *FINAL* *ABSTRACT* *ARRAY_CLASS*)
;;                               (LEN (HEAP S)))
;;                         (ARRAY-CLASS-TABLE S)))
;;              (ENV S)
;;              (ERROR-FLAG S)
;;              (NTH 8 S)))).


(defthm loader-inv-implies-acl2-numberp-pc
  (implies (loader-inv s)
           (integerp (pc s)))
  :hints (("Goal" :in-theory (enable loader-inv))))


(defthm
  class-table-correct-extension-does-not-change-build-an-java-instance-data-guard-load-array2
  (implies (and (build-a-java-visible-instance-data-guard classnames s)
                (all-loaded? classnames s)
                (loader-inv s))
           (build-a-java-visible-instance-data-guard
               classnames (load_array_class2 anyx s)))
  :hints (("Goal" :in-theory (disable load_class_x))))


(defthm all-loaded-state-set-current-thread
  (equal (all-loaded? l (state-set-current-thread any s))
         (all-loaded? l s)))


(defthm all-loaded-load-class-x
  (implies (all-loaded? l s)
           (all-loaded? l (load_class_x anyx s seen mode))))


(defthm all-loaded-equal-x
  (equal (all-loaded? l (MAKE-STATE (pc s)
                                    any_thread
                                    any_heap
                                    any_thread_table
                                    (make-class-table 
                                     (instance-class-table s)
                                     any_acl)
                                    (ENV S)
                                    (ERROR-FLAG S)
                                    any_aux))
         (all-loaded? l s))
  :hints (("Goal" :in-theory (enable class-loaded?))))



(defthm all-loaded-load-array-class2
  (implies (all-loaded? l s)
           (all-loaded? l (load_array_class2 anyx s)))
  :hints (("Goal" :in-theory (disable load_class_x))))


(defthm all-loaded-load-array-class
  (implies (all-loaded? l s)
           (all-loaded? l (load_array_class anyx s)))
  :hints (("Goal" :in-theory (disable load_array_class2))))



(defthm loader-inv-equal-x
  (implies (loader-inv s)
           (loader-inv (MAKE-STATE (pc s)
                                 any_thread
                                 any_heap
                                 any_thread_table
                                 (make-class-table 
                                  (instance-class-table s)
                                  any_acl)
                                 (ENV S)
                                 (ERROR-FLAG S)
                                 any_aux)))
  :hints (("Goal" :in-theory (enable loader-inv))))



(defthm loader-inv-load-array-class2
  (implies (loader-inv s)
           (loader-inv (load_array_class2 any s))))



(defthm loader-inv-load-array-class
  (implies (loader-inv s)
           (loader-inv (load_array_class any s)))
  :hints (("Goal" :in-theory (disable load_array_class2))))



(defthm
  class-table-correct-extension-does-not-change-build-an-java-instance-data-guard-load-array
  (implies (and (build-a-java-visible-instance-data-guard classnames s)
                (all-loaded? classnames s)
                (loader-inv s))
           (build-a-java-visible-instance-data-guard
               classnames (load_array_class anyx s)))
  :hints (("Goal" :in-theory (disable load_class_x load_array_class2))))


(defthm build-an-instance-guard-not-change-across-array-class-loading
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (class-loaded? any s))
           (build-a-java-visible-instance-guard any (load_array_class anyx s)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard)
                                  (load_array_class)))))





;----------------------------------------------------------------------

(defthm array-class-table-make-state
  (equal (array-class-table (make-state pc th hp tt 
                                        (make-class-table 
                                         cl
                                         acl)
                                        env ef aux))
         acl))


(defthm wff-array-class-table-rep-make-array-class-table-entry
  (wff-array-class-table-rep (make-array-class-table-entry 
                              type acess-flag addr)))

;; (defthm wff-array-class-table-rep-make-array-class-table-entry
;;   (wff-array-class-table-rep (make-array-class-table-entry 
;;                               type acess-flag addr)))

(defthm car-make-array-class-table-entry
  (equal (car (make-array-class-table-entry type acess-flag addr))
         (make-array-type type)))

(defthm wff-array-class-table-rep-load-array-class2
  (wff-array-class-table-rep (array-class-by-name 
                               (make-array-type type)
                               (array-class-table 
                                (load_array_class2 type s))))
  :hints (("Goal" :in-theory (disable wff-array-class-table-rep 
                                      make-array-class-table-entry))))



(defthm wff-array-class-table-rep-load-array-class-lemma
  (implies (and (no-fatal-error? (load_array_class type s))
                (not (arrayclassloaded? type s)))
           (wff-array-class-table-rep (array-class-by-name 
                                       (make-array-type type)
                                       (array-class-table 
                                        (load_array_class type s)))))
  :hints (("Goal" :in-theory (disable wff-array-class-table-rep 
                                      load_array_class2
                                      make-array-type
                                      primitive-type?
                                      make-array-class-table-entry)
           :do-not '(generalize))))


(defthm wff-array-class-table-rep-load-array-class
  (implies (and (no-fatal-error? (load_array_class type s))
                (wff-array-class-table (array-class-table s)))
           (wff-array-class-table-rep (array-class-by-name 
                                       (make-array-type type)
                                       (array-class-table 
                                        (load_array_class type s)))))
  :hints (("Goal" :in-theory (disable wff-array-class-table-rep 
                                      ;;arrayclassloaded?
                                      load_array_class2
                                      make-array-type
                                      primitive-type?
                                      make-array-class-table-entry)
           :do-not '(generalize)
          :cases ((arrayclassloaded? type s)))))


;----------------------------------------------------------------------


;(i-am-here) 

;; (skip-proofs 
;;  (defthm load_array_class_perserve_array_class_table-inv
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (no-fatal-error? (load_array_class any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class any s)))
;;             (load_array_class any s)))))


(defthm instance-class-table-update-trace
  (equal (instance-class-table (update-trace any s))
         (instance-class-table s)))

;; (defthm array-class-correctly-loaded-equal
;;   (equal (array-class-correctly-loaded? l 
;;              (make-state anypc anyth anyheap anytt
;;                          (make-class-table anycl
                                          
(defthm make-array-type-array-type
  (array-type? (make-array-type any)))


;; (defthm if-base-loaded-cons
;;   (IMPLIES
;;    (ARRAY-CLASS-TABLE-INV-HELPER (BASE-TYPES ANY) s)
;;    (ARRAY-CLASS-CORRECTLY-LOADED?
;;     (BASE-TYPES (MAKE-ARRAY-TYPE ANY))
;;     (MAKE-STATE
;;      anypc anyth anyheap anytt 
;;      (MAKE-CLASS-TABLE
;;       (instance-class-table s)
;;       (CONS (LIST (MAKE-ARRAY-TYPE ANY)
;;                   any-access-flag
;;                   (LEN (HEAP S)))
;;             (ARRAY-CLASS-TABLE S)))
;;      anyenv anyef anyaux))))


(defthm base-type-make-array-type-f
  (IMPLIES
   (ARRAY-CLASS-CORRECTLY-LOADED?
    (BASE-TYPES (MAKE-ARRAY-TYPE ANY)) s)
   (ARRAY-CLASS-CORRECTLY-LOADED? 
    (base-types any) s))
  :rule-classes :forward-chaining)



;; (defthm base-type-make-array-type
;;   (IMPLIES
;;    (ARRAY-CLASS-CORRECTLY-LOADED?
;;     (BASE-TYPES (MAKE-ARRAY-TYPE ANY)) s)
;;    (ARRAY-CLASS-CORRECTLY-LOADED? 
;;     (base-types any) s))
;;   :rule-classes nil)


(defthm once-correctly-loaded-correctly-loaded
  (IMPLIES
   (array-class-correctly-loaded? l s)
   (array-class-correctly-loaded? l 
    (MAKE-STATE
     anypc anyth anyheap anytt 
     (MAKE-CLASS-TABLE
      (instance-class-table s)
      (CONS (LIST (MAKE-ARRAY-TYPE ANY)
                  any-access-flag
                  (LEN (HEAP S)))
            (ARRAY-CLASS-TABLE S)))
     anyenv anyef anyaux)))
  :hints (("Goal" :in-theory (enable class-loaded?))))


(defthm once-correctly-loaded-correctly-loaded-corollary
  (IMPLIES
   (ARRAY-CLASS-TABLE-INV-HELPER l s)
   (ARRAY-CLASS-TABLE-INV-HELPER l 
    (MAKE-STATE
     anypc anyth anyheap anytt 
     (MAKE-CLASS-TABLE
      (instance-class-table s)
      (CONS (LIST (MAKE-ARRAY-TYPE ANY)
                  any-access-flag
                  (LEN (HEAP S)))
            (ARRAY-CLASS-TABLE S)))
     anyenv anyef anyaux)))
  :hints (("Goal" :in-theory (disable 
                              make-array-type
                              array-type? primitive-type? 
                              array-class-correctly-loaded?)
           :do-not '(generalize)))) 

(defthm base-types-make-type
  (equal (base-types (make-array-type any))
         (cons (make-array-type any) 
               (base-types any))))

(defthm equal-make-array-type-base-type-make-array-type
  (equal (MAKE-ARRAY-TYPE (ARRAY-BASE-TYPE (make-array-type any)))
         (make-array-type any)))


(defthm once-correctly-loaded-correctly-loaded-specific
  (IMPLIES
   (array-class-correctly-loaded? (base-types (array-base-type any)) s)
   (array-class-correctly-loaded? (base-types (array-base-type any))
    (MAKE-STATE
     anypc anyth anyheap anytt 
     (MAKE-CLASS-TABLE
      (instance-class-table s)
      (CONS (LIST (MAKE-ARRAY-TYPE ANY)
                  any-access-flag
                  (LEN (HEAP S)))
            (ARRAY-CLASS-TABLE S)))
     anyenv anyef anyaux)))
  :hints (("Goal" :in-theory (disable make-array-type))))


(defthm array-class-table-inv-helper-loaded-implies-correctly-loaded
  (implies (and (array-class-table-inv-helper (all-array-sigs l) s)
                (array-class-by-name (make-array-type any) l))
           (array-class-correctly-loaded? (base-types any) s))
  :hints (("Goal" :in-theory (disable array-type? primitive-type?
                                      make-array-type
                                      array-base-type)
           :do-not '(generalize))))

;;
;; the proof of this is a bit flaky. It needs quite a few inductions to
;; "extract" some facts about array-class-table-inv-helper!
;; Wed Aug  4 14:58:07 2004
;;

;; (i-am-here) 

;; Tue Mar 1 20:58:52 2005 The question: why we need the no-fatal-error?
;; assertion!!

(defthm load_array_class2_perserve_array_class_table-inv
  (implies (and (array-class-table-inv-helper 
                 (all-array-sigs (array-class-table s)) s)
                (array-type? any)
                (arrayclassloaded? (array-base-type any) s))
           (array-class-table-inv-helper 
            (all-array-sigs (array-class-table 
                             (load_array_class2 any s)))
            (load_array_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :do-not-induct t
           :in-theory (disable array-base-type make-array-type
                               gen-access-flags
                               array-type?))))
 

;; (defthm load_array_class2_perserve_array_class_table-inv
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (array-type? any)
;;                 (arrayclassloaded? (array-base-type any) s)
;;                 (no-fatal-error? (load_array_class2 any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class2 any s)))
;;             (load_array_class2 any s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :do-not-induct t
;;            :in-theory (disable array-base-type make-array-type
;;                                gen-access-flags
;;                                array-type?))))
 

;; (skip-proofs 
;;  (defthm load_array_class2_perserve_array_class_table-inv
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (array-type? any)
;;                 (arrayclassloaded? (array-base-type any) s)
;;                 (no-fatal-error? (load_array_class2 any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class2 any s)))
;;             (load_array_class2 any s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :do-not-induct t
;;            :in-theory (disable array-base-type make-array-type
;;                                gen-access-flags
;;                                array-type?)))))






;; (defthm load_array_class2_perserve_array_class_table-inv-x
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (not (array-type? any))
;;                 (not (primitive-type? any))
;;                 (no-fatal-error? (load_array_class2 any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class2 any s)))
;;             (load_array_class2 any s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :do-not-induct t
;;            :in-theory (e/d (class-loaded?)
;;                            (array-base-type make-array-type
;;                             array-type? primitive-type?                                           
;;                             gen-access-flags array-type?)))))


(defthm primitive-correctly-loaded
  (implies 
   (PRIMITIVE-TYPE? ANY)
   (ARRAY-CLASS-CORRECTLY-LOADED?
    (BASE-TYPES ANY)
    (MAKE-STATE
     anypc anyth anyheap anytt 
     (MAKE-CLASS-TABLE
      (instance-class-table s)
      (CONS (LIST (MAKE-ARRAY-TYPE ANY)
                  any-access-flag
                  (LEN (HEAP S)))
            (ARRAY-CLASS-TABLE S)))
     anyenv anyef anyaux))))



(defthm load_array_class2_perserve_array_class_table-inv-2
  (implies (and (array-class-table-inv-helper 
                 (all-array-sigs (array-class-table s)) s)
                (primitive-type? any))
           (array-class-table-inv-helper 
            (all-array-sigs (array-class-table 
                             (load_array_class2 any s)))
            (load_array_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :do-not-induct t
           :in-theory (disable primitive-type?
                               array-base-type make-array-type
                               gen-access-flags 
                               array-type?))))



;; (defthm load_array_class2_perserve_array_class_table-inv-2
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (primitive-type? any)
;;                 (no-fatal-error? (load_array_class2 any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class2 any s)))
;;             (load_array_class2 any s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :do-not-induct t
;;            :in-theory (disable primitive-type?
;;                                array-base-type make-array-type
;;                                gen-access-flags 
;;                                array-type?))))


(defthm class-type-correctly-loaded
  (implies 
   (and (not (array-type? any))
        (not (primitive-type? any))
        (class-loaded? any s))
   (ARRAY-CLASS-CORRECTLY-LOADED?
    (BASE-TYPES (MAKE-ARRAY-TYPE ANY))
    (MAKE-STATE
     anypc anyth anyheap anytt 
     (MAKE-CLASS-TABLE
      (instance-class-table s)
      (CONS (LIST (MAKE-ARRAY-TYPE ANY)
                  any-access-flag
                  (LEN (HEAP S)))
            (ARRAY-CLASS-TABLE S)))
     anyenv anyef anyaux)))
  :hints (("Goal" :in-theory (enable class-loaded?))))


(defthm load_array_class2_perserve_array_class_table-inv-3
  (implies (and (array-class-table-inv-helper 
                 (all-array-sigs (array-class-table s)) s)
                (not (primitive-type? any))
                (not (array-type? any))
                (class-loaded? any s))
                ;;(no-fatal-error? (load_array_class2 any s)))
           (array-class-table-inv-helper 
            (all-array-sigs (array-class-table 
                             (load_array_class2 any s)))
            (load_array_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable primitive-type?
                               array-base-type make-array-type
                               gen-access-flags 
                               array-type?))))


;; -- Tue Mar  1 21:02:46 2005 ----------

(defthm load_array_class2_perserve_array_class_table-inv-4
  (implies (and (jvm::array-class-table-inv-helper 
                 (jvm::all-array-sigs (array-class-table s)) s)
                (not (array-type? any))
                (class-loaded? any s))
           (jvm::array-class-table-inv-helper 
            (jvm::all-array-sigs (array-class-table 
                             (load_array_class2 any s)))
            (load_array_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :do-not-induct t
           :in-theory (e/d (load_array_class2)
                           (array-base-type make-array-type
                            gen-access-flags
                            array-type?)))))

;;; -----------------------------------

(defthm state-set-current-thread-not-change-correctly-loaded
  (equal (array-class-correctly-loaded? l (state-set-current-thread any s))
         (array-class-correctly-loaded? l s)))


(defthm state-set-current-thread-not-change-inv
  (equal (array-class-table-inv-helper l (state-set-current-thread any s))
         (array-class-table-inv-helper l s)))

(defthm load-class-does-affect-already-loaded-classes
  (implies (array-class-correctly-loaded? l s)
           (array-class-correctly-loaded? l (load_class_x any s seen mode))))


(defthm load-class-does-affect-already-loaded-classes-inv
  (implies (array-class-table-inv-helper l s)
           (array-class-table-inv-helper l (load_class_x any s seen mode))))

;(i-am-here) ;; Wed Aug  4 22:35:32 2004


(in-theory (disable array-base-type))


(defthm class-loaded-set-current-thread
  (equal (class-loaded? any (state-set-current-thread anyx s))
         (class-loaded? any s)))


(defthm load-class-load
  (implies (not (error-flag (load_class_x any s seen 3)))
           (class-loaded? any (load_class_x any s seen 3))))


(defthm array-class-by-name-implies-array-correctly-loaded
  (implies (and (array-class-table-inv-helper (all-array-sigs acl) s)
                (array-class-by-name any acl))
           (array-class-correctly-loaded? (base-types any) s)))


(defthm load-array-class-class-load
  (implies (not (error-flag (load_array_class any s)))
           (array-class-by-name (make-array-type any)
            (array-class-table (load_array_class any s)))))


(defthm load_array_class_perserve_array_class_table-inv
   (implies (and (array-class-table-inv-helper 
                  (all-array-sigs (array-class-table s)) s)
                 (no-fatal-error? (load_array_class any s))
                 (load_array_class_guard s))
            (array-class-table-inv-helper 
             (all-array-sigs (array-class-table 
                              (load_array_class any s)))
             (load_array_class any s)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (disable load_array_class2 primitive-type? 
                                array-type?))))

;; good. Thu Aug  5 12:21:01 2004

;;
;; (defthm array-class-correctly-loaded?-l-s
;;   (implies (and (mem x l)
;;                 (array-class-correctly-loaded? l s)
;;                 (array-type? x))
;;            (arrayclassloaded? (array-base-type x) s)))
;;


;; (defthm arrayclassloaded-implies-wff-array-class-table-rep
;;   (implies (and (wff-array-class-table (array-class-table s))
;;                 (arrayclassloaded? (array-base-type x) s))
;;            (wff-array-class-table-rep 
;;             (array-class-by-name (make-array-type (array-base-type x))
;;                                  (array-class-table s)))))

;; ;; (skip-proofs
;; ;;  (defthm arrayclassloaded-implies-wff-array-class-table-rep
;; ;;    (implies (and (wff-array-class-table (array-class-table s))
;; ;;                  (arrayclassloaded? (array-base-type x) s))
;; ;;             (wff-array-class-table-rep 
;; ;;              (array-class-by-name x 
;; ;;                                   (array-class-table s))))))

;; ;; (defthm lemma
;; ;;   (implies (and (array-class-correctly-loaded? (base-types (make-array-type
;; ;;                                                             base-type)) s)
;; ;;                 (a
           
;; ;;            (arrayclassloaded? (array-base-type base-type) s)))



;; ;;            (WFF-ARRAY-CLASS-TABLE-REP
            
;; ;;             (ARRAY-CLASS-BY-NAME
;; ;;              (ARRAY-BASE-TYPE BASE-TYPE)
;; ;;              (ARRAY-CLASS-TABLE s)))))


;; (skip-proofs 
;;  (defthm mem-x
;;    (MEM (CAR (BASE-TYPES (CAR (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S)))))
;;         (ALL-ARRAY-SIGS
;;          (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                               S))))))


;; (skip-proofs 
;;  (ARRAY-CLASS-CORRECTLY-LOADED?
;;   (ALL-ARRAY-SIGS
;;    (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                         S)))
;;   S))


;; (defthm load-array-class-class-load
;;   (implies (not (error-flag (load_array_class any s)))
;;            (array-class-by-name (make-array-type any)
;;             (array-class-table (load_array_class any s)))))

(defthm array-class-by-name-array-correctly-loaded
  (implies (and (array-class-table-inv-helper (all-array-sigs
                                               (array-class-table s)) s)
                (array-class-by-name any (array-class-table s)))
           (array-class-correctly-loaded? (base-types any) s)))

;(i-am-here)

(defthm wff-array-class-table-rep-if-found
  (implies (and (wff-array-class-table l)
                (array-class-by-name any l))
           (wff-array-class-table-rep (array-class-by-name any l))))


(defthm array-class-correctly-loaded-implies-base-class-loaded
  (implies (and (array-class-correctly-loaded? l s)
                (array-type? any)
                (mem any l))
           (array-class-by-name (make-array-type (array-base-type any)) 
                                (array-class-table s))))
  
(defthm true-listp-len-1-is-list-car
  (implies (and (true-listp l)
                (equal (len l) 1))
           (equal (list (car l)) l))
  :hints (("Goal" :do-not '(generalize))))


;; (defthm mem-any-base-types
;;    (implies (array-type? any)
;;             (mem any (base-types (make-array-type any)))))


(local (in-theory (enable array-base-type)))

(defthm make-array-type-array-base-type-is-identity-when-array-type?
  (implies (array-type? any)
           (equal (make-array-type (array-base-type any))
                  any)))


(defthm array-class-correctly-loaded-implies-base-class-loaded-general
  (implies (and (array-class-correctly-loaded? l s)
                (array-type? any)
                (mem any l))
           (array-class-by-name any
                                (array-class-table s))))





(defthm array-class-correctly-loaded-implies-base-class-loaded-general-specific
  (implies (and (array-class-correctly-loaded? (base-types any) s)
                (array-type? any)
                (array-type? (array-base-type any)))
           (array-class-by-name (array-base-type any)
                                (array-class-table s)))
  :hints (("Goal" :in-theory (disable array-base-type)
           :restrict
           ((array-class-correctly-loaded-implies-base-class-loaded-general
             ((l (base-types any))))))))


(defthm array-class-by-name-loaded-loaded
  (implies (and (array-class-table-inv-helper (all-array-sigs
                                               (array-class-table s))
                                              s)
                (array-type? any)
                (array-class-by-name any (array-class-table s))
                (array-type? (array-base-type any)))
           (array-class-by-name (array-base-type any)
                                (array-class-table s)))
  :hints (("Goal" :in-theory (disable array-base-type))))


;; (defthm load-array-class-class-load
;;   (implies (not (error-flag (load_array_class any s)))
;;            (array-class-by-name (make-array-type any)
;;             (array-class-table (load_array_class any s)))))



(defthm load-array-class-class-load-specific
  (implies (and (not (error-flag (load_array_class (array-base-type any) s)))
                (array-type? any))
           (array-class-by-name any
              (array-class-table (load_array_class (array-base-type any) s))))
  :hints (("Goal" :use ((:instance load-array-class-class-load
                                   (any (array-base-type any))))
           :in-theory (disable load_array_class array-base-type array-type?
                               make-array-type))))


(defthm |Subgoal 5.5|
  (IMPLIES
   (AND (LOADER-INV S)
        (WFF-HEAP (HEAP S))
        (CLASS-LOADED? "java.lang.Object" S)
        (CLASS-LOADED? "java.lang.Class" S)
        (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
        (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
        (WFF-ENV (ENV S))
        (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
                                      S)
        (NOT (ERROR-FLAG S))
        (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
        (ARRAY-TYPE? BASE-TYPE)
        (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
                                           S)))
        (ARRAY-TYPE? (ARRAY-BASE-TYPE BASE-TYPE)))
   (WFF-ARRAY-CLASS-TABLE-REP
    (ARRAY-CLASS-BY-NAME
     (ARRAY-BASE-TYPE BASE-TYPE)
     (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
                                          S)))))
  :hints (("Goal" :in-theory (disable make-array-type array-base-type
                                      array-class-table-inv-helper
                                      array-type? 
                                      wff-array-class-table-rep))))
                            
;; The proof is not clean at all. Twisting!! 
;;  
;; 
;; we proved a stronger result: load_array_class any results in
;; (make-array-type any) is loaded. 
;; 
;; we proved the inv on array-class-table is preserved. 
;;
;; we implicitly proved the wff-array-class-table is preserved
;;
;; We only need to show (array-base-type base-type) are also loaded!!
;; 
;; the cause of the difficult is our predicate of 
;;
;;    array-class-correctly-loaded?
;;
;; which skipped an intermediate concept, instend it asserts on any list
;;
;;    (array-class-correctly-loaded? l s)
;;
;; We could have a more recusive definition. instead of relying on base-types
;; to define the l we need. 
;;

;; (skip-proofs 
;;  (defthm |Subgoal 5.5|
;;    (IMPLIES
;;     (AND (LOADER-INV S)
;;          (WFF-HEAP (HEAP S))
;;          (CLASS-LOADED? "java.lang.Object" S)
;;          (CLASS-LOADED? "java.lang.Class" S)
;;          (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
;;          (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
;;          (WFF-ENV (ENV S))
;;          (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
;;                                        S)
;;          (NOT (ERROR-FLAG S))
;;          (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
;;          (ARRAY-TYPE? BASE-TYPE)
;;          (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                             S)))
;;          (ARRAY-TYPE? (ARRAY-BASE-TYPE BASE-TYPE)))
;;     (WFF-ARRAY-CLASS-TABLE-REP
;;      (ARRAY-CLASS-BY-NAME
;;       (ARRAY-BASE-TYPE BASE-TYPE)
;;       (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                            S)))))))


(defthm class-loaded-then-well-formed
  (implies (and (class-loaded? type s)
                (wff-instance-class-table (instance-class-table s)))
           (wff-class-rep (class-by-name type (instance-class-table s)))))



(defthm array-class-correctly-loaded?-mem-not-primitive-type-not-array-type
  (implies (and (mem any l)
                (not (primitive-type? any))
                (not (array-type? any))
                (array-class-correctly-loaded? l s))
           (class-loaded? any s))
  :hints (("Goal" :in-theory (disable array-type? primitive-type?))))
  

(defthm array-class-by-name-implies-array-correctly-loaded-when-inv-hold
  (implies (and (array-class-table-inv-helper (all-array-sigs
                                               (array-class-table s)) s)
                (array-class-by-name any (array-class-table s)))
           (array-class-correctly-loaded? (base-types any) s)))


(defthm array-type-implies-array-base-type-mem
  (implies (array-type? any)
           (mem (array-base-type any) (base-types any))))
                

(defthm
  array-class-table-inv-helper-implies-non-primitive-type-non-array-type-loaded
  (implies (and (array-class-table-inv-helper (all-array-sigs
                                               (array-class-table s)) s)
                (not (primitive-type? (array-base-type any)))
                (not (array-type? (array-base-type any)))
                (array-type? any)
                (array-class-by-name any (array-class-table s)))
           (class-loaded? (array-base-type any) s))
  :hints (("Goal" :in-theory (disable make-array-type array-base-type
                                      array-class-table-inv-helper
                                      primitive-type? array-type?)
           :restrict
           ((array-class-correctly-loaded?-mem-not-primitive-type-not-array-type
             ((l (base-types any))))))))




(defthm |Subgoal 5.3|
  (IMPLIES
    (AND (LOADER-INV S)
         (WFF-HEAP (HEAP S))
         (CLASS-LOADED? "java.lang.Object" S)
         (CLASS-LOADED? "java.lang.Class" S)
         (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
         (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
         (WFF-ENV (ENV S))
         (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
                                       S)
         (NOT (ERROR-FLAG S))
         (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
         (ARRAY-TYPE? BASE-TYPE)
         (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
                                            S)))
         (NOT (ARRAY-TYPE? (ARRAY-BASE-TYPE BASE-TYPE)))
         (NOT (PRIMITIVE-TYPE? (ARRAY-BASE-TYPE BASE-TYPE))))
    (WFF-CLASS-REP
     (CLASS-BY-NAME
      (ARRAY-BASE-TYPE BASE-TYPE)
      (INSTANCE-CLASS-TABLE (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
                                              s)))))
  :hints (("Goal" :in-theory (disable make-array-type array-base-type
                                      array-class-table-inv-helper
                                      array-type?  primitive-type?
                                      wff-class-rep ;;load_array_class
                                      wff-array-class-table-rep))))


;; Thu Aug  5 12:53:40 2004 this following is more meaningful lemma to prove. 

;; (defthm array-class-table-inv-loaded-means-base-type-loaded
;;   (implies (array-class-table-inv-helper l 





;; (defthm |Subgoal 5'|
;;   (IMPLIES
;;    (AND (LOADER-INV S)
;;          (WFF-HEAP (HEAP S))
;;          (CLASS-LOADED? "java.lang.Object" S)
;;          (CLASS-LOADED? "java.lang.Class" S)
;;          (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
;;          (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
;;          (WFF-ENV (ENV S))
;;          (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
;;                                        S)
;;          (NOT (ERROR-FLAG S))
;;          (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
;;          (ARRAY-TYPE? BASE-TYPE)
;;          (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                             S))))
;;     (LOAD_ARRAY_CLASS2-GUARD BASE-TYPE
;;                              (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                                S)))
;;   :hints (("Goal" :in-theory (disable ;;arrayclassloaded?
;;                                       array-type?
;;                                       make-array-type
;;                                       make-array-class-table-entry
;;                                       wff-array-class-table-rep
;;                                       wff-array-class-table
;;                                       primitive-type?
;;                                       ;;load_array_class2-guard
;;                                       ;;gen-access-flags-guard
;;                                       class-loaded?
;;                                       wff-class-rep
;;                                       ;;load_array_class2-guard
;;                                       array-base-type
;;           ("Subgoal 1" :expand (load_array_class (array-base-type base-type) s))))
           



(verify-guards load_array_class
               :hints (("Goal" :in-theory (disable arrayclassloaded?
                                                   array-type?
                                                   make-array-class-table-entry
                                                   wff-array-class-table-rep
                                                   wff-array-class-table
                                                   primitive-type?
                                                   ;;load_array_class2-guard
                                                   ;;gen-access-flags-guard
                                                   class-loaded?
                                                   wff-class-rep
                                                   ;;load_array_class2-guard
                                                   array-base-type))))




;; ;; (local (in-theory (disable instance-class-table
;; ;;                            wff-class-table
;; ;;                            array-class-table)))
                        


;; ;; (defthm loader-inv-perserved-by-load_array_class2
;; ;;   (implies (loader-inv s)
;; ;;            (loader-inv (load_array_class2 any s))))



;; ;; ;;   :hints (("Goal" :in-theory (e/d (loader-inv)
;; ;; ;;                                   (instance-class-table 
;; ;; ;;                                    wff-class-table
;; ;; ;;                                    wff-array-class-table
;; ;; ;;                                    array-class-table)))))


;; ;; (defthm loader-inv-perserved-by-load_array_class
;; ;;   (implies (loader-inv s)
;; ;;            (loader-inv (load_array_class any s)))
;; ;;   :hints (("Goal" :in-theory (disable load_array_class2))))





































;; ;; (defthm load_array_class_perserve_array_class_table-inv
;; ;;   (implies (and (array-class-table-inv-helper 
;; ;;                  (all-array-sigs (array-class-table s)) s)
;; ;;                 (no-fatal-error? (load_array_class any s)))
;; ;;            (array-class-table-inv-helper 
;; ;;             (all-array-sigs (array-class-table 
;; ;;                              (load_array_class any s)))
;; ;;             (load_array_class any s))))

;; (skip-proofs 
;;  (defthm load_array_class_perserve_array_class_table-inv
;;   (implies (and (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s)
;;                 (no-fatal-error? (load_array_class any s)))
;;            (array-class-table-inv-helper 
;;             (all-array-sigs (array-class-table 
;;                              (load_array_class any s)))
;;             (load_array_class any s)))))
                 


;; (defthm Arrayclassloaded?-implies-mem-all-sig-lemma
;;   (implies (array-class-by-name any acl)
;;            (mem any (all-array-sigs acl))))

;; (defthm Arrayclassloaded?-implies-mem-all-sig
;;   (implies (arrayclassloaded? any s)
;;            (mem (make-array-type any) (all-array-sigs (array-class-table s)))))
           
;; (defthm array-type-implies-array-base-make-array-type
;;   (implies (array-type? type)
;;            (equal (make-array-type (array-base-type type))
;;                   type))
;;   :hints (("Subgoal 1" :use (:instance 
;;                               list-cons-rewrite-hack
;;                               (type2 acl2::type2)))))


;; (defthm subset-base-types-all-array-sigs-lemma
;;    (implies (and (array-class-table-inv-helper l s)
;;                  (mem x l))
;;             (array-class-correctly-loaded? (base-types x) s)))


;; (defthm ArrayClassLoaded?-mem-l
;;   (implies (and (ArrayClassLoaded? (array-base-type any) s)
;;                 (array-type? any))
;;            (mem any (all-array-sigs (array-class-table s))))
;;   :hints (("Goal" :in-theory (disable array-base-type
;;                                       make-array-type
;;                                       array-type?))))
                


;;; array class loaded? use the base type for testing. 
;;; Fri Jul 30 22:04:37 2004

;; (defthm correctly-loaded?-implies-loaded
;;   (implies (and (mem x l)
;;                 (array-type? x)
;;                 (array-class-correctly-loaded? l s))
;;            (Arrayclassloaded? (array-base-type x) s)))

;;;
;;; give an array type, all super class are loaded!! 
;;;

;; (skip-proofs
;;  (defthm ArrayClassLoaded-all-correct-loaded
;;   (implies (and (ArrayClassLoaded? (array-base-type any) s)
;;                 (array-type? any)
;;                 (array-class-table-inv-helper 
;;                  (all-array-sigs (array-class-table s)) s))
;;            (array-class-table-inv-helper (base-types any) s))
;;   :hints (("Goal" :do-not '(generalize)


;;            :do-not-induct t))))


;; ;;            :in-theory (disable array-base-type
;; ;;                                ArrayClassLoaded?-mem-l
;; ;;                                array-class-table-inv-helper
;; ;;                                array-class-correctly-loaded?
;; ;;                                ArrayClassLoaded?
;; ;;                                make-array-type
;; ;;                                array-type?)
;; ;;            :use ((:instance subset-base-types-all-array-sigs-lemma
;; ;;                             (x any)
;; ;;                             (l (all-array-sigs (array-class-table s))))
;; ;;                  (:instance ArrayClassLoaded?-mem-l)))))



;; ;; (defthm load_array_class_perserve_array_class_table-inv
;; ;;   (implies (and (array-class-table-inv-helper 
;; ;;                  (all-array-sigs (array-class-table s)) s)
;; ;;                 (no-fatal-error? (load_array_class any s)))
;; ;;            (array-class-table-inv-helper 
;; ;;             (all-array-sigs (array-class-table 
;; ;;                              (load_array_class any s)))
;; ;;             (load_array_class any s))))

                

;; (skip-proofs 
;;  (defthm |Subgoal 5.22|
;;   (IMPLIES
;;   (AND (LOADER-INV S)
;;        (WFF-HEAP (HEAP S))
;;        (CLASS-LOADED? "java.lang.Object" S)
;;        (CLASS-LOADED? "java.lang.Class" S)
;;        (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
;;        (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
;;        (WFF-ENV (ENV S))
;;        (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
;;                                      S)
;;        (NOT (ERROR-FLAG S))
;;        (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
;;        (ARRAY-TYPE? BASE-TYPE)
;;        (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                           S)))
;;        (ARRAY-TYPE? (ARRAY-BASE-TYPE BASE-TYPE)))
;;   (ARRAY-CLASS-TABLE-INV-HELPER (BASE-TYPES (ARRAY-BASE-TYPE BASE-TYPE))
;;                                 (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                                   S)))))



;; (skip-proofs 
;;  (defthm |Subgoal 5.4|
;;    (IMPLIES
;;   (AND (LOADER-INV S)
;;        (WFF-HEAP (HEAP S))
;;        (CLASS-LOADED? "java.lang.Object" S)
;;        (CLASS-LOADED? "java.lang.Class" S)
;;        (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
;;        (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
;;        (WFF-ENV (ENV S))
;;        (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
;;                                      S)
;;        (NOT (ERROR-FLAG S))
;;        (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
;;        (ARRAY-TYPE? BASE-TYPE)
;;        (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                           S)))
;;        (PRIMITIVE-TYPE? (ARRAY-BASE-TYPE BASE-TYPE)))
;;   (ARRAY-CLASS-TABLE-INV-HELPER (BASE-TYPES (ARRAY-BASE-TYPE BASE-TYPE))
;;                                 (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                                   S)))))

;; (i-am-here)

;; (skip-proofs 
;;  (defthm base-type-class-type-loaded
;;    (implies (and (arrayclassloaded? any s)
;;                  (array-class-table-inv-helper (all-array-sigs
;;                                                 (array-class-table s)) s)
;;                  (not (primitive-type? any))
;;                  (not (array-type? any)))
;;             (class-loaded? any (instance-class-table s)))))
                 
;; (defthm load_array_class2_load_indeed
;;   (implies (no-fatal-error? (load_array_class any s))
;;            (Arrayclassloaded? (array-base-type any) (load_array_class2 any s))))

;; (skip-proofs 
;;  (defthm load_array_class_load_indeed
;;    (implies (no-fatal-error? (load_array_class any s))
;;             (Arrayclassloaded? (array-base-type any) (load_array_class any s)))))


;; (skip-proofs
;;  (defthm |Subgoal 5.8|
;;   (IMPLIES
;;     (AND (LOADER-INV S)
;;          (WFF-HEAP (HEAP S))
;;          (CLASS-LOADED? "java.lang.Object" S)
;;          (CLASS-LOADED? "java.lang.Class" S)
;;          (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S))
;;          (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
;;          (WFF-ENV (ENV S))
;;          (ARRAY-CLASS-TABLE-INV-HELPER (ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
;;                                        S)
;;          (NOT (ERROR-FLAG S))
;;          (NOT (ARRAYCLASSLOADED? BASE-TYPE S))
;;          (ARRAY-TYPE? BASE-TYPE)
;;          (NOT (ERROR-FLAG (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                                             S))))
;;     (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
;;          "java.lang.Class"
;;          (LOAD_ARRAY_CLASS (ARRAY-BASE-TYPE BASE-TYPE)
;;                            S)))))


;; (verify-guards load_array_class
;;                :hints (("Goal" :in-theory (disable arrayclassloaded?
;;                                                    array-type?
;;                                                    make-array-class-table-entry
;;                                                    wff-array-class-table-rep
;;                                                    wff-array-class-table
;;                                                    primitive-type?
;;                                                    ;;gen-access-flags-guard
;;                                                    class-loaded?
;;                                                    wff-class-rep
;;                                                    ;;load_array_class2-guard
;;                                                   array-base-type))))



;; ;----------------------------------------------------------------------


;; (verify-guards load_array_class2)


;; (defthm wff-class-table-load_array_class2
;;   (implies (wff-class-table  (class-table s))
;;            (wff-class-table (class-table (load_array_class2 any s)))))

;; (defthm wff-class-table-load_class2
;;   (implies (wff-class-table  (class-table s))
;;            (wff-class-table (class-table (load_class2 any s)))))

;; (defthm wff-class-table-load_array_class
;;   (implies (wff-class-table  (class-table s))
;;            (wff-class-table (class-table (load_array_class any s))))
;;   :hints (("Goal" :in-theory (disable load_array_class2))))



;; ;; (defthm loader-inv-loaded-ready-create-instance
;; ;;   (implies (and (loader-inv s)
;; ;;                 (wff-heap (heap s))
;; ;;                 (no-fatal-error? s)
;; ;;                 (class-loaded? any s))
;; ;;            (build-a-java-visible-instance-guard any s))
;; ;;   :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))
;; ;;
;; ;; this is a bit weak. 
;; ;; If a fatal error is caused by some other component of the JVM, this is still
;; ;; true. 
;; ;; Sun Jul  4 15:55:36 2004. But let me modify jvm-loader.lisp to check
;; ;; fatalError
;; ;;


;; ;; (defthm build-a-java-visible-instance-guard
;; ;;      (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
;; ;;           "java.lang.Class"
;; ;;           (LOAD_ARRAY_CLASS (NTH 1 (CONS 'ARRAY BASE-TYPE2))
;; ;;                             S))).

;; ;; Sun Jul  4 16:43:36 2004

;; ;(i-am-here)
;; ;;Mon Jul  5 18:38:39 2004


;; ;; (defthm collect-superclass-does-not-change-via-load_cp_entry
;; ;;   (implies (and (loader-inv s)
;; ;;                 (no-fatal-error? s)
;; ;;                 (class-loaded? any s))
;; ;;            (equal (collect-superclass-list1 any (instance-class-table (mv-nth 1
;; ;;                                                                               (load_cp_entry cp s))) seen)
;; ;;                   (collect-superclass-list1 any (instance-class-table  s) seen)))
;; ;;   :hints (("Goal" :in-theory (enable load_cp_entry))))


;; (defthm load_cp_entry_do_not_change_cl
;;   (equal (instance-class-table (mv-nth 1 (load_cp_entry cp s)))
;;          (instance-class-table  s))
;;   :hints (("Goal" :in-theory (enable load_cp_entry))))


;; (defthm load_cp_entries_do_not_change_cl
;;   (equal (instance-class-table (mv-nth 1 (load_cp_entries cps s)))
;;          (instance-class-table s)))


;; ;; (defthm correctly-loaded-not-changed-by-load-class
;; ;;   (implies (and (correctly-loaded? x (instance-class-table s) env-cl)
;; ;;                 (equal (external-class-table s) env-cl))
;; ;;            (correctly-loaded? x (load_class2 anyx 
                


;; ;; (skip-proofs 
;; ;;  (defthm all-correctly-loaded-implies-collect-superclass-list
;; ;;    (implies (and (all-correctly-loaded? 
;; ;;                   (collect-superclassname1 classname env-cl seen)
;; ;;                   cl 
;; ;;                   env-cl)
;; ;;                  (all-found? (all-class-names cl) env-cl))
;; ;;             (equal (collect-superclass-list1 classname cl seen)
;; ;;                    (collect-superclassname1 classname env-cl seen)))
;; ;;    :hints (("Goal" :do-not '(fertilize)
;; ;;             :in-theory (enable correctly-loaded?)))))



;; ;; (defthm collect-superclass-list1-add-class-rep
;; ;;   (implies (not (mem (classname class-rep) 
;; ;;                      (collect-superclass-list1 any cl seen)))

;; ;;            (equal (collect-superclass-list1 any (cons class-rep cl) seen)
;; ;;                   (collect-superclass-list1 any cl seen)))
;; ;;   :hints (("Goal" :do-not '(generalize))))


;; (skip-proofs 
;;  (defthm collect-superclass-does-not-change-load_class2
;;    (implies (and (equal (collect-superclass-list1 any 
;;                                                   (instance-class-table s)
;;                                                   seen)
;;                         (collect-superclassname1 any (external-class-table s)
;;                                                  seen))
;;                  (mv-nth 0 (class-by-name-s anyx (external-class-table s)))) 
;;             (equal (collect-superclass-list1 any (instance-class-table
;;                                                   (load_class2 anyx s)) seen)
;;                    (collect-superclassname1  any (external-class-table s) seen)))
;;    :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry)
;;                                    (make-runtime-class-rep wff-class-rep))
;;             :do-not '(generalize)
;;             :do-not-induct T
;;             :cases ((mem anyx (collect-superclassname1 any
;;                                                        (external-class-table s) seen)))))))
           


;; ;; some theorem that needs to be proved!! 
;; ;;
;; ;; my way of proving that superchain is equal was weak. relies on load_class2
;; ;; does not return an error state! (via, superclass matches with env)


;; (defthm collect-superclass-does-not-change-load_class
;;   (implies (and 
;;             (and (equal (collect-superclass-list1 any 
;;                                                   (instance-class-table s)
;;                                                   seen)
;;                         (collect-superclassname1 any (external-class-table s)
;;                                                  seen))
;;                  (class-loaded? any s)))
;;             (equal (collect-superclass-list1 any (instance-class-table
;;                                                   (load_class_x anyx s ss mode)) seen)
;;                    (collect-superclassname1 any (external-class-table s) seen)))
;;   :hints (("Goal" :do-not '(generalize fertilize)
;;            :in-theory (e/d ()(wff-class-rep wff-class-rep-strong 
;;                                             isClassTerm
;;                                             make-runtime-class-rep))
;;            :induct (load_class_x anyx s ss mode))))



;; ;; (defthm collect-superclass-list1-equal
;; ;;   (implies (equal (external-class-table s) some_env_cl)
;; ;;            (equal (collect-superclass-list1 any (make-state any_pc
;; ;;                                                             any_th
;; ;;                                                             any_hp
;; ;;                                                             any_th
;; ;;                                                             (make-class-table 
;; ;;                                                              (instance-class-table s)
;; ;;                                                              any_acl)
;; ;;                                                             some_env_cl
;; ;;                                                             any_ef
;; ;;                                                             any_aux) seen)
;; ;;                   (collect-superclass-list1 any s seen))))
                                                      

;; (skip-proofs 
;;  (defthm loader-inv-implies-two-class-table-match
;;    (implies (and (loader-inv s)
;;                  (no-fatal-error? s))
;;             (equal (collect-superclass-list1 classname (instance-class-table s) seen)
;;                    (collect-superclassname1 classname (external-class-table s) seen)))
;;    :hints (("Goal" :do-not '(fertilize)
;;             :in-theory (enable correctly-loaded?)))))


;; (skip-proofs 
;;  (defthm loader-inv-perserved-by-load_array_class2
;;    (implies (loader-inv s)
;;             (loader-inv (load_array_class2 any s)))))



;; ;;   :hints (("Goal" :in-theory (e/d (loader-inv)
;; ;;                                   (instance-class-table 
;; ;;                                    wff-class-table
;; ;;                                    wff-array-class-table
;; ;;                                    array-class-table)))))


;; (defthm loader-inv-perserved-by-load_array_class
;;   (implies (loader-inv s)
;;            (loader-inv (load_array_class any s)))
;;   :hints (("Goal" :in-theory (disable load_array_class2))))





;; (defthm collect-superclass-does-not-change-load_array-class2
;;    (implies (and ;;(loader-inv s)
;;                  ;;(no-fatal-error? s)
;;                  (equal (collect-superclass-list1 any (instance-class-table s)
;;                                                   seen)
;;                         (collect-superclassname1 any (external-class-table s) seen))
;;                  (class-loaded? any s))
;;             (equal (collect-superclass-list1 any (instance-class-table (load_array_class2 anyx s)) seen)
;;                    (collect-superclass-list1 any (instance-class-table s) seen)))
;;    :hints (("Goal" :in-theory (disable load_class))))

;; (defthm class-loaded?-state-set-current-thread
;;   (equal (class-loaded? x (state-set-current-thread any s))
;;          (class-loaded? x s)))
         


;; (defthm collect-superclass-does-not-change-load_array-class
;;    (implies (and ;;(loader-inv s)
;;                  (no-fatal-error? s)
;;                  (loader-inv s)
;;                  (equal (collect-superclass-list1 any (instance-class-table s)
;;                                                   seen)
;;                         (collect-superclassname1 any (external-class-table s) seen))
;;                  (class-loaded? any s))
;;             (equal (collect-superclass-list1 any (instance-class-table (load_array_class anyx s)) seen)
;;                    (collect-superclassname1 any (external-class-table s) seen)))
;;    :hints (("Goal" :in-theory (disable load_class_x class-loaded?
;;                                        collect-superclass-list1
;;                                        ;;load_array_class
;;                                        ;;external-class-table
;;                                        load_array_class2))))


;; (defthm instance-class-table-equal
;;   (equal (INSTANCE-CLASS-TABLE
;;           (MAKE-STATE any_pc
;;                       ANY_TH 
;;                       SOME_HP
;;                       any_tt
;;                       (MAKE-CLASS-TABLE (INSTANCE-CLASS-TABLE S)
;;                                         ANY_CL)
;;                       any_env
;;                       ANY_EF ANY_AUX))
;;          (instance-class-table s))
;;   :hints (("Goal" :in-theory (enable instance-class-table class-table))))

;; (defthm build-immediate-instance-data-guard-equal
;;   (implies (and (wff-state s)
;;                 (wff-heap some_hp)
;;                 (equal (env s) some_env_cl)
;;                 (build-immediate-instance-data-guard any s))
;;            (build-immediate-instance-data-guard
;;             any 
;;             (make-state (pc s)
;;                         any_th
;;                         some_hp
;;                         any_tt
;;                         (make-class-table 
;;                          (instance-class-table s)
;;                          any_cl)
;;                         some_env_cl
;;                         any_ef
;;                         any_aux)))
;;   :hints (("Goal" :in-theory (enable build-immediate-instance-data-guard))))

                                              
;; (defthm build-a-java-visible-instance-data-guard-equal
;;   (implies (and (wff-state s)
;;                 (wff-heap some_hp)
;;                 (equal (env s) some_env_cl)
;;                 (build-a-java-visible-instance-data-guard classnames s))
;;            (build-a-java-visible-instance-data-guard
;;             classnames
;;             (make-state (pc s)
;;                         any_th
;;                         some_hp
;;                         any_tt
;;                         (make-class-table 
;;                          (instance-class-table s)
;;                          any_cl)
;;                         some_env_cl
;;                         any_ef
;;                         any_aux))))


;; (defthm wff-heap-bind-heap
;;   (implies (wff-heap hp)
;;            (wff-heap (bind x y hp)))
;;   :hints (("Goal" :in-theory (enable wff-heap))))
           


;; (defthm build-a-java-visible-instance-guard-perserved-by-load_array_class2
;;   (implies (and (loader-inv s)
;;                 (no-fatal-error? s)
;;                 (wff-heap (heap s))
;;                 (class-loaded? any s)
;;                 (build-a-java-visible-instance-guard any s))
;;            (build-a-java-visible-instance-guard any (load_array_class2 anyx
;;                                                                        s)))
;;   :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))


;; (skip-proofs 
;;  (defthm build-a-java-visible-instance-guard-perserved-by-load_array_class
;;   (implies (and (loader-inv s)
;;                 (wff-heap (heap s))
;;                 (no-fatal-error? s)
;;                 (class-loaded? any s)
;;                 (build-a-java-visible-instance-guard any s))
;;            (build-a-java-visible-instance-guard any (load_array_class anyx s)))
;;   :hints (("Goal" :in-theory (e/d (state-set-current-thread) (load_array_class2))))))


;; (skip-proofs 
;;  (defthm build-a-java-visible-instance-guard-perserved-by-load_class_x
;;   (implies (and (loader-inv s)
;;                 (wff-heap (heap s))
;;                 (no-fatal-error? s)
;;                 (class-loaded? any s)
;;                 (build-a-java-visible-instance-guard any s))
;;            (build-a-java-visible-instance-guard any (load_class_x anyx s seen mode)))))



;; (defthm wff-heap-perserved-by-load_array_class2
;;   (implies (wff-heap (heap s))
;;            (wff-heap (heap (load_array_class2 any s))))
;;   :hints (("Goal" :in-theory (enable wff-heap))))

;; (defthm wff-heap-perserved-by-load_array_class
;;   (implies (wff-heap (heap s))
;;            (wff-heap (heap (load_array_class any s))))
;;   :hints (("Goal" :in-theory (disable load_array_class2))))


;; (in-theory (disable load_array_class2))


;; (skip-proofs 
;;  (defthm loader-base-class-will-not-load-the-current-class
;;    (implies (and (not (arrayclassloaded? any s))
;;                  (array-type? any))
;;             (not (arrayclassloaded? any 
;;                                     (load_array_class 
;;                                      (array-base-type any) s))))))
  


;; (skip-proofs 
;;  (defthm build-a-java-visible-instance-guard-set-currenth-thread
;;   (implies (wff-state s)
;;            (equal (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
;;                    any
;;                    (STATE-SET-CURRENT-THREAD th s))
;;                   (build-a-java-visible-instance-guard any
;;                    s)))
;;   :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard)))))
           


;; (skip-proofs 
;;  (defthm wff-array-class-table-loaded-implies-wff-rep
;;   (implies   (and (ARRAYCLASSLOADED? (ARRAY-BASE-TYPE BASE-TYPE) s)
;;                   (wff-array-class-table (array-class-table s)))
;;              (WFF-ARRAY-CLASS-TABLE-REP
;;               (ARRAY-CLASS-BY-NAME
;;                BASE-TYPE
;;                (ARRAY-CLASS-TABLE env-cl))))))

;; (defthm class-loaded-state-set-current-thread
;;   (equal (class-loaded? any (state-set-current-thread anyx s))
;;          (class-loaded? any s)))

;; (defthm array-class-loaded-state-set-current-thread
;;   (equal (ArrayClassLoaded? any (state-set-current-thread anyx s))
;;          (ArrayClassLoaded? any s)))


;; (defthm ArrayClassLoaded?-if-array-class-table-equal
;;   (implies (equal (array-class-table s2) (array-class-table s1))
;;            (equal (arrayclassloaded? any s2)
;;                   (arrayclassloaded? any s1))))

;; (defthm ArrayClassLoaded?-if-array-class-table-equal-specific
;;   (implies (equal (array-class-table (load_class_x anyx s1 seen mode)) (array-class-table s1))
;;            (equal (arrayclassloaded? any (load_class_x anyx s1 seen mode))
;;                   (arrayclassloaded? any s1))))

;; (verify-guards load_array_class
;;                :hints (("Goal" :in-theory (disable arrayclassloaded?
;;                                                    array-type?
;;                                                    make-array-class-table-entry
;;                                                    wff-array-class-table-rep
;;                                                    wff-array-class-table
;;                                                    ;;gen-access-flags-guard
;;                                                    ;;load_array_class2-guard
;;                                                   array-base-type))))





;; ;----------------------------------------------------------------------



;; (local (in-theory (disable instance-class-table
;;                            wff-class-table
;;                            array-class-table)))
                           


;; (defthm loader-inv-perserved-by-load_array_class2
;;   (implies (loader-inv s)
;;            (loader-inv (load_array_class2 any s))))



;; ;;   :hints (("Goal" :in-theory (e/d (loader-inv)
;; ;;                                   (instance-class-table 
;; ;;                                    wff-class-table
;; ;;                                    wff-array-class-table
;; ;;                                    array-class-table)))))


;; (defthm loader-inv-perserved-by-load_array_class
;;   (implies (loader-inv s)
;;            (loader-inv (load_array_class any s)))
;;   :hints (("Goal" :in-theory (disable load_array_class2))))


(verify-guards class-exists-externally?)
(verify-guards getClass)
(verify-guards getArrayClass11)
(verify-guards getArrayClass)


;; (defun getArrayClass11 (basetype S)
;;   (declare (xargs :guard (load_array_class_guard s)))
;;   (load_array_class basetype S))

;; (defun getArrayClass (basetype S)
;;   (declare (xargs :guard (load_array_class_guard s)))
;;   (if (ArrayClassLoaded? basetype s)
;;       s
;;     (load_array_class basetype S)))



(in-theory (disable MEM-BASE-TYPES-IMPLIES-NOT-EQUAL))