(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader-primitives")
(include-book "../M6-DJVM-shared/jvm-loader-constant-pool-primitives")
(include-book "../M6-DJVM-shared/jvm-loader-inv")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

;; (acl2::set-verify-guards-eagerness 0) ;; tmp implementation!! 
;;
;; Wed Mar 31 14:02:42 2004
;;
(acl2::set-verify-guards-eagerness 2)

; test whethter the instance class of classname is loaded. 
(defun class-loaded? (classname s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (isClassTerm (class-by-name classname (instance-class-table s))))

(defun ArrayClassLoaded1? (type l)
  (declare (xargs :guard (wff-array-class-table l)))
  (array-class-by-name type l))

(defun ArrayClassLoaded? (basetype s)
  "Return whether array of such a basetype has been loaded"
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-array-class-table (array-class-table s)))))
  (let ((al (array-class-table s)))
    (ArrayClassLoaded1? (make-array-type basetype) al)))

;; real loader
;;
;; this method load the class, it will be correct only when the superclasses
;; are loaded, or the class is java.lang.Object, java.lang.String,
;; java.lang.Class.
;;
;; According to the JVM spec, exception should be thrown.
;;
;; However in KVM, fatalError is thrown. Programs that relies on the exception
;; being thrown will terminate.
;; 
;; note 1: This file, we included a simplified loader, which doesn't throw exception. 
;; instead it throws a fatal exception, which means during loading no exception
;; will be thrown.  This is "faithful" to the KVM except KVM doesn't fatalError
;; in less cases, instead it mark ClASS_ERROR in a few cases.


;(i-am-here)

;;
;; this following function blindly load the class of name class-name
;;

(defun build-a-java-visible-instance-guard-strong (s)
  (and (wff-state s)
       (wff-class-table (class-table s))
       (wff-instance-class-table-strong (instance-class-table s))
       (wff-env (env s))
       (wff-static-class-table-strong (external-class-table s))
       (loader-inv s)
       (build-a-java-visible-instance-data-guard
        (all-class-names (instance-class-table s)) s)))

;;
;; build-a-java-visible-instance-data-guard asserts wff-fields. 
;; 

;(i-am-here)

(defun load_class2_guard (classname s)
  (mylet* ((env (env s))
           (class-table (class-table s))
           (scl (env-class-table env)))
    (and (wff-state s)
         (wff-env env)
         (wff-heap (heap s))
         (wff-class-table class-table)
         ;(build-a-java-visible-instance-guard-strong s)
         ;; this asserts every class decl in instance-class-table is well
         ;; formed (we can build data fields belong to those classes.
         ;; We also need to to assert that all the super classes are loaded!! 
         ;; but can we assert it here??
         ;; will I still be able to prove the property? I should. 
         ;; Wed Jun 23 18:38:17 2004
         
         ;; Add new assertions about all supers are loaded. 
         ;; Thu Jun 24 14:35:28 2004
         (loader-inv s)
         (all-correctly-loaded? 
          (cdr (collect-superclassname classname (external-class-table s)))
          (instance-class-table s)
          (external-class-table s))
         (all-correctly-loaded? 
          (cdr (collect-superinterface classname (external-class-table s)))
          (instance-class-table s)
          (external-class-table s))
         ;;
         ;; in load_class2, we only need to make sure java.lang.Object and
         ;; java.lang.Class are loaded. java.lang.String as well. 
         ;; 
         ;; Before we are allowed to call load_class2, we need to assert all
         ;; super are loaded!! 
         ;; added to assert that classname's super are loaded.
         ;; (build-a-java-visible-instance-guard-strong s)
         (wff-static-class-table scl)
         (mv-let (found class-desc)
                 (class-by-name-s classname scl)
                 (mylet* ((static-cp  (constantpool-s class-desc))
                          (static-field-table (fields-s class-desc))
                          (static-method-table (methods-s class-desc)))
                 (or (not found)
                     (and (wff-class-rep-static class-desc)
                          (load_CP_entries_guard static-cp s)
                          (build-a-java-visible-instance-guard "java.lang.Class" s)
                          (wff-fields-s static-field-table)
                          (runtime-method-rep-guards static-method-table))))))))


(in-theory (disable ;; load_CP_entries 
                    wff-class-rep-static
                    add-instance-class-entry classname-s 
                    make-runtime-class-rep make-class-table
                    array-class-table  wff-state wff-heap
                    build-a-java-visible-instance-guard
                    fields-s methods-s interfaces-s))

(defthm wff-heap-implies-alistp
  (implies (wff-heap hp)
           (alistp hp)))

(defthm wff-heap-implies-alistp-specific
  (implies (wff-heap (heap s))
           (alistp (heap (mv-nth 1 (load_CP_entries cps s)))))
  :hints (("Goal" :in-theory (disable load_CP_entries))))

;(i-am-here)

;; (i-am-here) ;; Sat Nov  6 15:39:57 2004

;; Sun Nov  7 16:02:30 2004

(defthm load-cp-entry-wff-constant-pool
  (implies (wff-constant-pool-entry-s cp)
           (wff-constant-pool-entry (car (load_cp_entry cp s)))))


(defthm load-cp-entries-wff-constant-pool
  (implies (wff-constant-pool-s cp)
           (wff-constant-pool (car (load_cp_entries cp s))))
  :hints (("Goal" :in-theory (disable wff-constant-pool-entry-s
                                      load_cp_entry
                                      wff-constant-pool-entry))))


(defthm wff-constant-pool-s-implied-by-wff-static-class-table
  (implies (and (wff-static-class-table-strong scl)
                (car (class-by-name-s classname scl)))
           (wff-constant-pool-s 
            (CDR (NTH 3
                      (MV-NTH 1
                              (CLASS-BY-NAME-S CLASSNAME scl)))))))


(defthm wff-constant-pool-s-implied-by-wff-static-class-table-constant-pool
  (implies (and (wff-static-class-table-strong scl)
                (car (class-by-name-s classname scl)))
           (wff-constant-pool-s 
            (constantpool-s 
                      (MV-NTH 1
                              (CLASS-BY-NAME-S CLASSNAME scl))))))

(defthm true-listp-load_cp_entries
  (true-listp (car (load_cp_entries cp s)))
  :hints (("Goal" :in-theory (disable load_cp_entry))))

(defthm len-equal-load-cpentries
  (equal (len (car (load_cp_entries cps s)))
         (len cps))
  :hints (("Goal" :in-theory (disable load_cp_entry))))


(defthm load_cp_entry-no-change-centry-type
  (equal (cpentry-type (car (load_cp_entry cp s)))
         (cpentry-type-s cp)))

(defthm load_cp_entry-no-change-centry-value
  (implies (primitive-type? (cpentry-type-s cp))
           (equal (cpentry-value (car (load_cp_entry cp s)))
                  (cpentry-value-s cp))))


;; (defthm cdr-load_cp_entires-is-load_cp_entries-cdr
;;   (equal (cdr (car (load_cp_entries cps s)))
;;          (car (load_cp_entries (cdr cps) s)))
;;   :hints (("Goal" :in-theory (disable load_cp_entry)
;;            :do-not '(generalize))))

;;;
;;; this is not true. because the different of heap object creation order!! 
;;;  


;; (defthm nth-i-load_cp_entries-is-load_cp_entry_nth
;;   (equal (nth i (car (load_cp_entries cps s)))
;;          (car (load_cp_entry (nth i cps) s)))
;;   :hints (("Goal" :in-theory (disable load_cp_entry)
;;            :do-not '(generalize))))




(defthm centry-type-no-change-load_cp_entries
  (equal (cpentry-type (nth i (car (load_cp_entries cps s))))
         (cpentry-type-s (nth i cps)))
  :hints (("Goal" :in-theory (disable load_cp_entry)
           :do-not '(generalize))
          ("Subgoal *1/2.2" :expand (LOAD_CP_ENTRY cps1 S))
          ("Subgoal *1/2.1" :expand (LOAD_CP_ENTRY (cons cps3 cps4) S))))


(defthm centry-value-no-change-load_cp_entries
  (implies (primitive-type? (cpentry-type-s (nth i cps)))
           (equal (cpentry-value (nth i (car (load_cp_entries cps s))))
                  (cpentry-value-s (nth i cps))))
  :hints (("Goal" :in-theory (disable 
                              cpentry-value-s
                              cpentry-value
                              load_cp_entry primitive-type?)
           :do-not '(generalize))
          ("Subgoal *1/2.2" :expand (LOAD_CP_ENTRY cps1 S))
          ("Subgoal *1/2.1" :expand (LOAD_CP_ENTRY (cons cps3 cps4) S))))



;; (i-am-here) ;; Wed Nov 10 20:50:15 2004

;; (i-am-here) ;; Thu Jan  5 19:10:13 2006

;; (i-am-here) ;; Thu Jan  5 20:48:00 2006

(defthm wff-static-cp-ok-s-implied-by-wff-static-class-table
  (implies (wff-static-cp-ok-s fields-s static-cp)
           (wff-static-cp-ok fields-s
                             (car (load_cp_entries static-cp s))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable load_cp_entry))))
                                                       
(defthm wff-static-class-table-strong-and-exists-implies-wff-static-cp-ok-s
  (implies (and (wff-static-class-table-strong scl)
                (car (class-by-name-s name scl)))
           (wff-static-cp-ok-s 
            (fields-s (mv-nth 1 (class-by-name-s name scl)))
            (constantpool-s (mv-nth 1 (class-by-name-s name scl))))))

;; (defthm  wff-static-class-table-strong-test
;;   (not (wff-static-class-table-strong scl)))

(defun load_class2 (classname s)
  (declare (xargs :guard (load_class2_guard classname s)
                  :guard-hints (("Goal" :in-theory (disable load_CP_entry constantpool-s)))))
  (let* ((scl (env-class-table (env s)))
         (dcl (instance-class-table s)))
         (mv-let 
          (def-found class-desc)
          (class-by-name-s classname scl)
          (if (not def-found)
              (fatalError "java.lang.ClassNotFoundException" s)
            (let  ((static-cp  (constantpool-s class-desc)))
              (mv-let 
               (dynamic-cp  new-state)  
               (load_CP static-cp  s)
               (mv-let (the-Class-object new-state2)
                       (build-an-instanceClass classname new-state)
                       (let* ((heap-with-strings (heap new-state2))
                              (new-address (alloc heap-with-strings))
                              (new-heap    (bind new-address the-Class-object
                                                 heap-with-strings)) 
                              ;; new heap
                              (runtime-class-rep 
                               (make-runtime-class-rep 
                                (classname-s class-desc)
                                (super-s class-desc)
                                dynamic-cp
                                (runtime-instance-fields-rep 
                                 (fields-s class-desc) classname)                    
                                (runtime-methods-rep 
                                 (methods-s class-desc) classname)
                                 (interfaces-s class-desc)
                                (runtime-static-fields-rep 
                                 (fields-s class-desc) classname dynamic-cp)
                                *class_loaded*  ;;   -- 2
                                (accessflags-s class-desc) 
                                -1            ;; indicate the non-init-thread
                                new-address)) ;; reference to ClassObject in the java heap
                              (new-dcl (add-instance-class-entry
                                              runtime-class-rep dcl))) 
                         ;; using cons instead of using bind.
                         (prog2$ (acl2::debug-print "class loading ~p0 complete! ~%" classname) 
                                 (update-trace new-address 
                                               (state-set-heap new-heap
                                                   (state-set-class-table
                                                    (make-class-table new-dcl 
                                                                      (array-class-table new-state2))
                                                    new-state2))))))))))))

;; modified to use primitives of state-set-heap
;; state-set-class-table to hide the fact of state is composed of 7-8 slots


;; (defstub loader-measure (* * *) => *)
;; --- start to prove the admissibility of the mutual recursion -
(defun load-class-x-guard (s seen)
  (and (wff-state s)
       (wff-env (env s))
       (wff-static-class-table 
        (env-class-table (env s)))
       (true-listp seen)))


(defun unloaded-class-count (s seen)
  (declare (xargs :guard (load-class-x-guard s seen)))
  (let ((cl (env-class-table (env s))))
    (+ 1 (len (set-diff (all-class-names-s cl) seen)))))


(defun loader-measure (stage s seen)
  (declare (xargs :guard (load-class-x-guard s seen)))
   (cons (cons (unloaded-class-count s seen) 0) stage))


(defun load_class_1-inv (classname s seen)
  (declare (xargs :guard (load-class-x-guard s seen)))
  (and (not (mem classname seen))
       (mem classname (all-class-names-s (env-class-table (env s))))))

(defun load_class_2-inv (classname s seen)
  (declare (xargs :guard (load-class-x-guard s seen)))
  (and (not (mem classname seen))
       (mem classname (all-class-names-s (env-class-table (env s))))))

(defun trivial-inv-env-do-not-change (s1 s2)
  (declare (xargs :guard (and (wff-state s1)
                              (wff-state s2))))
  (equal (env s1) (env s2)))



(in-theory (disable class-loaded? env env-class-table no-fatal-error? load_class2))


(defun induct-measure (p s seen mode)
  (declare (xargs :guard (load-class-x-guard s seen)))
  (cond ((equal mode 3) (loader-measure 3 s seen))
        ((equal mode 2) (loader-measure 2 s seen))
        ((equal mode 1) (loader-measure 1 s seen))
        ((equal mode 0) (loader-measure (+ 4 (len p)) s seen))
        (t 0)))


(acl2::set-verify-guards-eagerness 0) 

(defun load_class_x (p s seen mode)
  (declare (xargs :measure (induct-measure p s seen mode)
                  :guard (and (loader-inv s)
                              (wff-heap (heap s))
                              (class-loaded? "java.lang.Object" s)
                              (class-loaded? "java.lang.Class" s)
                              (true-listp seen))))
  ;; we may be able to write stronger guards 
  ;; but loader-inv is only necessary.
  (let ((classname p)
        (interfaces p))
  (if (not (no-fatal-error? s)) 
      s
    (cond ((equal mode 3) 
           (prog2$ (acl2::debug-print " load request ~p0 received!~%" classname)
                   (if (class-loaded? classname s)
                       (prog2$ (acl2::debug-print "class  ~p0 already loaded!~%" classname)
                               s)
                     (if (mem classname seen)
                         (fatalError "java.lang.ClassCircularityError" s);; ref to note 1
                       (mv-let 
                        (def-found class-desc)
                        (class-by-name-s classname (external-class-table s))
                        (declare (ignore class-desc))
                        (if (not def-found)
                            (fatalError "java.lang.ClassNotFoundException" s);; note 1
                          (let ((s1 (load_class_x classname s seen 2)))
                            (if (not (trivial-inv-env-do-not-change s1 s))
                                (fatalError "load_class_1 violate internal inv" s1)
                              (if (no-fatal-error? s1)
                                  (let ((s2 (load_class_x classname s1 seen 1)))
                                    (if (no-fatal-error? s2)
                                        (load_class2 classname s2)
                                      s2))
                                s1)))))))))
           ((equal mode 2)
            (if (not (load_class_1-inv classname s seen))
                (fatalError "load_class_1 violate internal inv" s)
              (mv-let 
               (def-found class-desc)
               (class-by-name-s classname (external-class-table s))
               (declare (ignore def-found))
               (let* ((supername (super-s class-desc))
                      (new-state (load_class_x supername s (cons classname seen) 3)))
                 new-state))))
           ((equal mode 1)
            (if (not (load_class_2-inv classname s seen))
                (fatalError "load_class_2 violate internal inv" s)
              (mv-let (def-found static-class-rep)
                      (class-by-name-s classname (external-class-table s))
                      (declare (ignore def-found))
                      (let ((interfaces (interfaces-s static-class-rep)))
                        (load_class_x interfaces s (cons classname seen) 0)))))
           ((equal mode 0)
            (if (not (consp interfaces))
                s
              ;; assuming no array  
              ;; doesn't check whether a class implments a class, instead of an
              ;; interfaces. ;; don't check access 
              (if (no-fatal-error? s)
                  (if (mem (car interfaces) seen)
                      (fatalError "interface circularity" s)
                    (if (class-loaded? (car interfaces) s)
                        (let ((class-rep (class-by-name (car interfaces)
                                                        (instance-class-table s))))
                          (if (not (isInterface class-rep))
                              (fatalError "here class implements non interfaces" s)
                            (load_class_x (cdr interfaces) s seen 0)))
                      (let* ((new-s (load_class_x (car interfaces) s seen 3))
                             (class-rep (class-by-name (car interfaces)
                                                       (instance-class-table new-s))))
                        (if (not (trivial-inv-env-do-not-change new-s s))
                            (fatalError "load_class_1 violate internal inv" new-s)
                          (if (no-fatal-error? new-s)
                              (if (not (isInterface class-rep))
                                  (fatalError "class implements non interfaces" new-s)
                                (load_class_x (cdr interfaces) new-s seen 0))
                            new-s)))))
                s)))
           (t s)))))

;;
;; move guard verification to the later Guard verification relies on a
;; load_class_x perserve certain invariant on the class-table!!  which is
;; not easy to do guard verification before the function is admitted!!
;; Tue Apr  6 20:55:22 2004
;;

;;
;; set the current thread to -1 to indicate the loading is done by JVM 
;; the obj created belongs to all threads. 
;;
(acl2::set-verify-guards-eagerness 2)

(defun load_class-guard (s)
  (and (loader-inv s)
       (wff-heap (heap s))
       (class-loaded? "java.lang.Object" s)
       (class-loaded? "java.lang.Class" s)))

;;(verify-guards load_class-guard)

(acl2::set-verify-guards-eagerness 0)

(defun load_class (classname s)
  (declare (xargs :guard (load_class-guard s)))
  (let ((th  (current-thread s))
        (s1  (state-set-current-thread -1 s)))
    (state-set-current-thread th (load_class_x classname s1 nil 3))))

(acl2::set-verify-guards-eagerness 2)
;; inferring the accessflags for array classes


(defun gen-access-flags-guard (base-type s)
  (and (wff-state s)
       (wff-class-table (class-table s))
       ;; why I need the following?? 
       (if (array-type? base-type)
           (and (wff-array-class-table (array-class-table s))
                (wff-array-class-table-rep 
                 (array-class-by-name base-type 
                                      (array-class-table s))))
         (if (primitive-type? base-type) t
           (and (wff-instance-class-table
                 (instance-class-table s))
                (wff-class-rep (class-by-name base-type 
                                              (instance-class-table s))))))))
                         
(defun gen-access-flags (base-type S);; assume the base-type is loaded
  (declare (xargs :guard (gen-access-flags-guard base-type s)
                  :guard-hints (("Goal" :in-theory (disable array-type?)))))
  (if (array-type? base-type)
      (let* ((array-class-rep 
              (array-class-by-name base-type
                                   (array-class-table S)))
             (access-flags  (array-access-flags array-class-rep)))
        (if (mem '*public* access-flags)
            (make-accessflags '(*final* *abstract* *array_class* *public*))
          (make-accessflags '(*final* *abstract* *array_class*))))
    (if (primitive-type? base-type)
        (make-accessflags '(*final* *abstract* *array_class* *public*))
      ;; has to be instance-class
      (let* ((instance-class-rep 
              (class-by-name base-type (instance-class-table S)))
             (access-flags (class-accessflags instance-class-rep)))
        (if (mem '*public* access-flags)
            (make-accessflags '(*final* *abstract* *array_class* *public*))
          (make-accessflags '(*final* *abstract* *array_class*)))))))

;;;; ACCESS TO THE ARRAY CLASS IS DEFINED BY CHECKING THE ACCESS TO THE BASE
;;;; TYPE!!

;; this load_array_clas2  doesn't test wether this (array base) type exist or
;; not.  always build an instanceClass object that represent the class.
;; simplify the getArrayClass
  
;; We assume that the base class is loaded already but (array base-class)
;; haven't be loaded.

;;
;; the shape of an entry in the array class table: 
;;
;;         (array-type access-flags the-class-obj-ref)
;;
;;
;;
;; (defun array-base-types (type)
;;   (if (array-type? type)
;;       (cons type (array-base-types (array-base-type type)))
;;     type))
;;
;; (defun all-array-class-loaded (



(defun base-types (type)
  (if (array-type? type)
      (cons type (base-types (array-base-type type)))
    (list type)))

(defun array-class-correctly-loaded? (types s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s))
                              (wff-array-class-table (array-class-table s)))))
  (if (not (consp types)) t
    (and (if (array-type? (car types))
             (ArrayClassLoaded? (array-base-type (car types)) s)
           (if (primitive-type? (car types)) t
             (class-loaded? (car types) s)))
         (array-class-correctly-loaded? (cdr types) s))))

                           
(defun array-class-table-inv-helper (l s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s))
                              (wff-array-class-table (array-class-table s)))))
  (if (not (consp l)) t
    (and (array-type? (car l))
         (array-class-correctly-loaded? (base-types (car l)) s)
         (array-class-table-inv-helper (cdr l) s))))




(defun all-array-sigs (l) 
  (declare (xargs :guard (wff-array-class-table l)))
  (if (not (consp l)) nil
    (cons (array-sig (car l))
          (all-array-sigs (cdr l)))))
      


(defun load_array_class2-guard (base-type s)
  (and (build-a-java-visible-instance-guard "java.lang.Class" s)
       (wff-state s)
       (wff-heap (heap s))
       (or (not (array-type? base-type))
           (gen-access-flags-guard (array-base-type base-type) s))
       (wff-class-table (class-table s))
       (wff-instance-class-table (instance-class-table s))
       (wff-array-class-table (array-class-table s))
       (not (ArrayClassLoaded? base-type s)) 
       (array-class-table-inv-helper (all-array-sigs (array-class-table s)) s)
       ;; only called when base-type is not loaded! 
       (if (array-type? base-type)
           (ArrayClassLoaded? (array-base-type base-type) s)
         ;; all base type must be loaded!! 
         (if (primitive-type? base-type)
             t
           (class-loaded? base-type s)))))



;; (defun load_array_class2-guard (base-type s)
;;   (and (build-a-java-visible-instance-guard "java.lang.Class" s)
;;        (wff-state s)
;;        (wff-heap (heap s))
;;        (or (not (array-type? base-type))
;;            (gen-access-flags-guard (array-base-type base-type) s))
;;        (wff-class-table (class-table s))
;;        (wff-instance-class-table (instance-class-table s))
;;        (wff-array-class-table (array-class-table s))
;;        (not (ArrayClassLoaded? base-type s)) 
;;        ;; only called when base-type is not loaded! 
;;        (if (array-type? base-type)
;;            (and (ArrayClassLoaded? (array-base-type base-type) s)
;;                 (array-class-table-inv-helper (base-types (array-base-type
;;                                                            base-type))
;;                                               s))
;;          ;; all base type must be loaded!! 
;;          (if (primitive-type? base-type)
;;              t
;;            (class-loaded? base-type s)))))


(acl2::set-verify-guards-eagerness 0)


(defun load_array_class2 (base-type S)
  (declare (xargs :guard (load_array_class2-guard base-type s)))
  (mv-let (array-class-rep-obj new-S)
          (build-instanceClassArrayClass base-type S)
          (let* ((heap (heap new-S))
                 (new-addr (alloc heap))
                 (new-heap (bind new-addr array-class-rep-obj heap))
                 (access-flags (gen-access-flags base-type S))
                 (array-class-rep 
                  (make-array-class-table-entry base-type access-flags new-addr))
                 (old-array-class-table (array-class-table S))
                 (new-array-class-table 
                  (add-array-class-table-entry array-class-rep
                                               old-array-class-table)))
            (state-set-array-class-table new-array-class-table
                                         (update-trace new-addr (state-set-heap
                                                                 new-heap
                                                                 new-s))))))


;;; this create a class-rep that reps `(array ,base-type)
;;;

;; what if the base class doesn't exist?  We can make the guard to say the base
;; type is loaded! So far it is not. FIXED! Tue Apr  6 21:12:39 2004

;;
;; this loader will load the base array class. (different from the original loader).
;;

;; (acl2::set-verify-guards-eagerness 2)
;; (defun all-array-sigs (l) 
;;   (declare (xargs :guard (wff-array-class-table l)))
;;   (if (not (consp l)) nil
;;     (cons (array-sig (car l))
;;           (all-array-sigs (cdr l)))))
      

(acl2::set-verify-guards-eagerness 2)
(defun load_array_class_guard (s)
  (and (load_class-guard s)
       (build-a-java-visible-instance-guard "java.lang.Class" s)
       (wff-array-class-table (array-class-table s))
       (wff-instance-class-table (instance-class-table s))
       (wff-env (env s))
       (wff-static-class-table (external-class-table s))
       (array-class-table-inv-helper (all-array-sigs (array-class-table s)) s)))


;(acl2::set-verify-guards-eagerness 0)

;(i-am-here)

(acl2::set-verify-guards-eagerness 0)

(defun load_array_class (base-type S)
  (declare (xargs :guard (load_array_class_guard s)))
  (if (not (no-fatal-error? s))
      s
    (if (ArrayClassLoaded? base-type S)
        s
      (if (array-type? base-type)
          (let ((s1  (load_array_class 
                      (array-base-type base-type) S)))
            (if (not (no-fatal-error? s1))
                s1
              (load_array_class2 base-type s1)))
        (if (primitive-type? base-type)
            (load_array_class2 base-type s)
          (if (class-loaded? base-type S)
              (load_array_class2 base-type S)
            (let ((s1 (load_class base-type s)))
              (if (not (no-fatal-error? s1))
                  s1
                (load_array_class2 base-type s1)))))))))

(acl2::set-verify-guards-eagerness 2)

;; (defun gen-access-flags-guard (base-type s)
;;   (and (wff-state s)
;;        (wff-class-table (class-table s))
;;        (if (array-type? base-type)
;;            (and (wff-array-class-table (array-class-table s))
;;                 (wff-array-class-table-rep 
;;                  (array-class-by-name base-type 
;;                                       (array-class-table s))))
;;          (if (primitive-type? base-type) t
;;            (and (wff-instance-class-table
;;                  (instance-class-table s))
;;                 (wff-class-rep (class-by-name base-type 
;;                                               (instance-class-table s))))))))

;;
;;
;; (defun primitive-types (primitive-types)
;;   (if (not (consp primitive-types)) t
;;     (and (primitive-type? (car primitive-types))
;;          (primitive-types (cdr primitive-types))))
;;
;;

(defun load_primitive_array_classes-guard (types s)
  (if (not (consp types)) t
    (and (load_array_class2-guard (car types) s)
         (load_primitive_array_classes-guard (cdr types) s))))
      

(acl2::set-verify-guards-eagerness 0)
(defun load_primitive_array_classes (primitive-types s)
  (declare (xargs :guard (load_primitive_array_classes-guard primitive-types s)))
  (if (not (consp primitive-types))
      s
    (load_primitive_array_classes (cdr primitive-types) 
                                  (load_array_class2 (car primitive-types) s))))


;-------------------------------

;; The interface that the other part of the system will use more often.

(defun getClass (classname s)
  (declare (xargs :guard (load_class-guard s)))
  (if (class-loaded? classname s)
      s
    (load_class classname s)))

(defun getArrayClass11 (basetype S)
  (declare (xargs :guard (load_array_class_guard s)))
  (load_array_class basetype S))

(defun getArrayClass (basetype S)
  (declare (xargs :guard (load_array_class_guard s)))
  (if (ArrayClassLoaded? basetype s)
      s
    (load_array_class basetype S)))

;------------------------------

(defun load-JavaSystemClasses (s) 
  (let* ((th (current-thread s))
         (s0 (state-set-current-thread -1 s))
         (s1 (load_class2 "java.lang.Object" s0))
         (s2 (load_class2 "java.lang.Class"  s1))
         (s3 (load_class2 "java.lang.String" s2))
         (s4 (load_primitive_array_classes *primitive-types* s3))
         (s5 (load_class "java.lang.System" s4))
         (s6 (load_class "java.lang.Thread" s5))
         (s7 (load_class "java.lang.Throwable" s6))
         (s8 (load_class "java.lang.Error" s7))
         (s9 (state-set-current-thread th s8)))
    s9))
;;; Wed Mar 31 21:53:47 2004. this may never guard verify because 
;;; load_class2 need a guard saying "java.lang.Object"  exists


(defun load_classes (nl s)
  (declare (xargs :guard (load_class-guard s)))
  (if (not (consp nl))
      s
    (load_class (car nl) 
                (load_classes (cdr nl) s))))


;------------ class loader property --------------------


(defun class-exists-externally? (from cl)
  (declare (xargs :guard (wff-static-class-table cl)))
  (mem from (all-class-names-s cl)))



(defthm fatalError-no-fatal-error?
  (implies (stringp msg)
           (not (no-fatal-error? (fatalError msg s))))
  :hints (("Goal" :in-theory (enable no-fatal-error?))))

(in-theory (disable instance-class-table isInterface super-s))

(defthm load_cp_entry_only_change_class_table_error_flag_heap
  (let ((s1 (mv-nth 1 (load_cp_entry cp s0))))
    (and    (equal (pc s1) (pc s0))
            (equal (current-thread s1) (current-thread s0))
            (equal (thread-table   s1) (thread-table s0))
            (equal (env            s1) (env          s0)))))

(in-theory (disable load_cp_entry))

;; these theorems are not good. Thu Jun 24 12:01:56 2004

(defthm load_cp_entries_only_change_class_table_error_flag_heap
  (let ((s1 (mv-nth 1 (load_cp_entries cps s0))))
    (and    (equal (pc s1) (pc s0))
            (equal (current-thread s1) (current-thread s0))
            (equal (thread-table   s1) (thread-table s0))
            (equal (env            s1) (env          s0)))))
    


(defthm load_class2_only_change_class_table_error_flag_heap
  (let ((s1 (load_class2 n s0)))
    (and    (equal (pc s1) (pc s0))
            (equal (current-thread s1) (current-thread s0))
            (equal (thread-table   s1) (thread-table s0))
            (equal (env            s1) (env          s0))))
  :hints (("Goal" :in-theory (enable load_class2))))


(defthm load_class_x_only_change_class_table_error_flag_heap
  (implies (or (equal mode 3)
               (equal mode 2)
               (equal mode 1)
               (equal mode 0))
           (let ((s1 (load_class_x p s0 seen mode)))
             (and    (equal (pc s1) (pc s0))
                     (equal (current-thread s1) (current-thread s0))
                     (equal (thread-table   s1) (thread-table s0))
                     (equal (env            s1) (env          s0))))))


;;  acl2 generates an good enough  induction hint.
;;  :hints (("Goal" :induct (loader-induct n_or_ifaces s0 seen mode))))

(defthm load_class_only_change_class_table_error_flag_heap
  (let ((s1 (load_class classname s0)))
    (and    (equal (pc s1) (pc s0))
            (equal (current-thread s1) (current-thread s0))
            (equal (thread-table   s1) (thread-table s0))
              (equal (env            s1) (env          s0))
              )));; need to find the measure for admit the load_class




;; where I need this? it's a nice property that worth proving though.
;; to admin is superclass

(defun classes-exists-externally? (ifaces cl)
  (if (endp ifaces)
      t
    (and (class-exists-externally? (car ifaces) cl)
         (classes-exists-externally? (cdr ifaces) cl))))




(in-theory (disable isInterface))




#|
;; this is not true 
(defthm no-fatal-error?-after-load-class-x-implies-class-exists-externally
  (and (implies (or (equal mode 1)
                    (equal mode 2)
                    (equal mode 3))
                (implies (no-fatal-error? (load_class_x p s seen mode))
                         (class-exists-externally? p (env-class-table (env s)))))
       (implies (equal mode 0)
                (implies (no-fatal-error? (load_class_x p s seen mode))
                         (classes-exists-externally? p (env-class-table (env s)))))))

|#


(defun all-not-loaded? (classes seen s)
  (if (endp classes)
      nil
    (and (not (class-loaded? (car classes) s))
         (all-not-loaded? (cdr classes) (cons (car classes) seen) 
                          (load_class_x (car classes) s seen 3)))))


(in-theory (disable fatalError))
;; this is true 
(defthm no-fatal-error?-after-load-class-x-implies-class-exists-externally
  (and (implies (or (equal mode 1)
                    (equal mode 2)
                    (equal mode 3))
                (implies (and (no-fatal-error? (load_class_x p s seen mode))
                              (not (class-loaded? p s)))
                         (class-exists-externally? p (env-class-table (env s)))))
       (implies (equal mode 0)
                (implies (and (no-fatal-error? (load_class_x p s seen mode))
                              (all-not-loaded? p seen s))
                         (classes-exists-externally? p (env-class-table (env s))))))
  :hints (("Goal" :induct (load_class_x p s seen mode))))

;; Sun Jun 20 01:57:34 2004


; >V d          (DEFUN MAKE-STATE
;                      (IP CUR JAVAHEAP THREAD-TABLE
;                          INTERNAL-CLASS-TABLE ENV ERROR-FLAG AUX)
;                      (LIST 'STATE
;                            IP CUR (CONS 'HEAP JAVAHEAP)
;                            (CONS 'THREAD-TABLE THREAD-TABLE)
;                            INTERNAL-CLASS-TABLE
;                            ENV ERROR-FLAG AUX))
; JVM !>

;(i-am-here)

;; (i-am-here) ;;; Fri Oct 29 17:50:48 2004
;;
;; modification to get assert heap-init-map

;; heap-init-map


(defun equiv-aux (aux1 aux2)
  (equal (heap-init-map aux1) 
         (heap-init-map aux2)))

(defequiv equiv-aux)

(defcong equiv-aux equal (heap-init-map aux) 1)
(defcong equiv-aux equiv-aux (aux-set-trace trace aux) 2)

(defthm equiv-aux-aux-set-any
  (equiv-aux (aux-set-trace any aux)
             aux))

;;; the equiv-aux is added?? !! 
;;; Fri Nov  5 13:43:01 2004

(defun equiv-state-except-thread-and-trace (s1 s2) 
  (and ;(equal (pc s1) (pc s2))
       ;(equal (thread-table s1) (thread-table s2))
       (equal (heap s1) (heap s2))
       (equal (class-table s1) (class-table s2))
       (equal (env s1) (env s2))
       (equal (error-flag s1) (error-flag s2))
       (equiv-aux (aux s1) (aux s2))))


(defequiv equiv-state-except-thread-and-trace)



(defun equiv-tuple-load (tuple1 tuple2)
  (and (equal (mv-nth 0 tuple1) 
              (mv-nth 0 tuple2))
       (equiv-state-except-thread-and-trace (mv-nth 1 tuple1)
                                            (mv-nth 1 tuple2))))

(defun slot1-tuple-load (tuple)
  (mv-nth 0 tuple))

(defun slot2-tuple-load (tuple)
  (mv-nth 1 tuple))

;(i-am-here)

(defequiv equiv-tuple-load)


(defcong equiv-state-except-thread-and-trace equiv-tuple-load 
  (load_cp_entry cp s) 2
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(local (defthm mv-to-slot 
         (and (equal (mv-nth 0 tuple)
                     (slot1-tuple-load tuple))
              (equal (mv-nth 1 tuple)
                     (slot2-tuple-load tuple)))))




(in-theory (disable slot2-tuple-load slot1-tuple-load)) 

(defcong equiv-tuple-load equiv-state-except-thread-and-trace
  (slot2-tuple-load tuple) 1)

(defcong equiv-tuple-load equal
  (slot1-tuple-load tuple) 1)

;(defcong equiv-state-except-thread-and-trace equal (pc s) 1)
;(defcong equiv-state-except-thread-and-trace equal (thread-table s) 1)
(defcong equiv-state-except-thread-and-trace equal (class-table s) 1)
(defcong equiv-state-except-thread-and-trace equal (heap s) 1)
(defcong equiv-state-except-thread-and-trace equal (error-flag s) 1)
(defcong equiv-state-except-thread-and-trace equal (env s) 1)
(defcong equiv-state-except-thread-and-trace equiv-aux (aux s) 1)

(in-theory (disable equiv-state-except-thread-and-trace equiv-aux aux-set-trace))

;; (skip-proofs 
;;  (defcong equiv-state-except-thread-and-trace equiv-tuple-load 
;;    (load_cp_entry cp s) 2
;;    :hints (("Goal" :in-theory (disable
;;    equiv-state-except-thread-and-trace)))))

;; (defcong equiv-state-except-thread-and-trace equiv-tuple-load 
;;   (load_cp_entry cp s) 2
;;   :hints (("Goal" :in-theory (disable equiv-state-except-thread-and-trace)))))



(defcong equiv-state-except-thread-and-trace equiv-tuple-load 
  (load_cp_entries cps s) 2
  :hints (("Goal" :in-theory (disable equiv-state-except-thread-and-trace))))


;(i-am-here)
(in-theory (disable equiv-tuple-load))

; >V d          (DEFUN MAKE-STATE
;                      (IP CUR JAVAHEAP THREAD-TABLE
;                          INTERNAL-CLASS-TABLE ENV ERROR-FLAG AUX)
;                      (LIST 'STATE
;                            IP CUR (CONS 'HEAP JAVAHEAP)
;                            (CONS 'THREAD-TABLE THREAD-TABLE)
;                            INTERNAL-CLASS-TABLE
;                            ENV ERROR-FLAG AUX))

;; may be need to write a marco to simulate the named fields

;; this is easily looping!! 

; (defthm equiv-state-except-thread-and-trace-make-state
;   (equiv-state-except-thread-and-trace 
;    (make-state pc
;                anyth1
;                hp
;                tt
;                cl
;                env
;                ef
;                anyaux1)
;    (make-state pc
;                anyth2
;                hp
;                tt
;                cl
;                env
;                ef
;                anyaux2))
;   :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace))))
               


(defthm equiv-state-except-thread-and-trace-make-state
  (implies (equiv-aux anyaux1 anyaux2)
           (equal (equiv-state-except-thread-and-trace 
                   (make-state anypc1
                               anyth1
                               hp
                               anytt1
                               cl
                               env
                               ef
                               anyaux1)
                   (make-state anypc2
                               anyth2
                               hp
                               anytt2
                               cl
                               env
                               ef
                               anyaux2)) t))
  :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace))))
               


;; Sun Jun 20 00:00:42 2004. We want to prove the following. We can prove
;; stronger properties. We will prove no-fatal-error earlier.
(defcong equiv-state-except-thread-and-trace
  equiv-state-except-thread-and-trace
  (fatalError any s) 2
  :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace
                                     fatalError))))



(defcong equiv-state-except-thread-and-trace equiv-tuple-load
  (build-an-instanceClass c s) 2
  :hints (("Goal" :in-theory (e/d (equiv-tuple-load slot1-tuple-load) 
                                  (mv-to-slot
                                   equiv-state-except-thread-and-trace)))))

;; (defcong equiv-state-except-thread-and-trace equiv-tuple-load
;;   (build-an-instanceClass c s) 2
;;   :hints (("Goal" :in-theory (e/d (equiv-tuple-load slot1-tuple-load) 
;;                                   (mv-to-slot
;;                                    equiv-state-except-thread-and-trace)))))


(defcong equiv-state-except-thread-and-trace equal 
  (instance-class-table s) 1
  :hints (("Goal" :in-theory (e/d (instance-class-table) ()))))

(defcong equiv-state-except-thread-and-trace equal 
  (array-class-table s) 1
  :hints (("Goal" :in-theory (e/d (array-class-table) ()))))


;; (defcong equiv-state-except-thread-and-trace equiv-tuple-load
;;     (load_cp_entry any s) 2
;;     :hints (("Goal" :in-theory (e/d (load_cp_entry) (equiv-aux heap-init-map)))))

;; (defthm equal-mv-nth-1-slot-2-is
;;   (equal (mv-nth 1 (load_cp_entries cps s))
;;          (slot2-tuple-load (load_cp_entries cps s)))
;;   :hints (("Goal" :in-theory (enable slot2-tuple-load))))

;; (defthm heap-init-map-aux-mv-nth-is
;;   (equal (heap-init-map (aux (mv-nth 1 (load_cp_entries any s))))
;;          (heap-init-map (aux (slot2-tuple-load (load_cp_entries any s))))))


(defthm equiv-aux-aux-set-trace-rewrite
  (and (equal (equiv-aux (aux-set-trace any aux1) aux2)
              (equiv-aux aux1 aux2))
       (equal (equiv-aux aux1 (aux-set-trace any aux2))
              (equiv-aux aux1 aux2))))

(in-theory (disable aux))


(defthm equiv-aux-equiv-state
  (implies (equiv-state-except-thread-and-trace s-equiv s)
           (equal (EQUIV-AUX
                   (AUX
                    (SLOT2-TUPLE-LOAD
                     (BUILD-AN-INSTANCECLASS
                      P
                      (SLOT2-TUPLE-LOAD
                       (LOAD_CP_ENTRIES
                        cps 
                        S)))))
                   (AUX
                    (SLOT2-TUPLE-LOAD
                     (BUILD-AN-INSTANCECLASS
                      P
                      (SLOT2-TUPLE-LOAD
                       (LOAD_CP_ENTRIES
                        cps
                        S-EQUIV)))))) t))
  :hints (("Goal" :in-theory (disable build-an-instanceclass))))

;;;
;;; Fri Oct 29 19:27:03 2004. 
;;;
;;; Backward chaining!! strange!! backward-chaing vs. cong reasoning.
;;;

(defcong equiv-state-except-thread-and-trace equiv-state-except-thread-and-trace
  (load_class2 p s) 2
  :hints (("Goal" :in-theory (e/d (load_class2)
                                  (build-an-instanceClass)))))

; (defthm fatalerror-equiv-state-state
;   (EQUIV-STATE-EXCEPT-THREAD-AND-TRACE
;    (FATALERROR any S) s)
;   :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace fatalerror))))

(defcong equiv-state-except-thread-and-trace equal 
  (no-fatal-error? s) 1
  :hints (("Goal" :in-theory (e/d (no-fatal-error?) ()))))


(defun load_class_x_induct (p s s-equiv seen mode)
  (declare (xargs :measure (induct-measure p s seen mode)
                  :guard (and (loader-inv s)
                              (loader-inv s-equiv))))
  (let ((classname p)
        (interfaces p))
  (if (not (no-fatal-error? s)) 
      s
    (cond ((equal mode 3) 
           (prog2$ (acl2::debug-print " load request ~p0 received!~%"
                                      classname)
                   (cond ((class-loaded? classname s)
                          (list p s s-equiv seen mode))
                         ((class-loaded? classname s-equiv)
                          (list p s s-equiv seen mode))
                         ((mem classname seen)
                          (list p s s-equiv seen mode))
                         (t (mv-let (def-found1 class-desc1)
                                    (class-by-name-s classname
                                                     (external-class-table s))
                                    (declare (ignore class-desc1))
                                    (mv-let (def-found2 class-desc2)
                                            (class-by-name-s classname 
                                                             (external-class-table s-equiv))
                                            (declare (ignore class-desc2))
                                            (cond ((not def-found1)
                                                   (list p s s-equiv seen
                                                         mode))
                                                  ((not def-found2)
                                                   (list p s s-equiv seen
                                                         mode))
                                                  (t (let ((s1 (load_class_x
                                                                classname s seen
                                                                2))
                                                           (s1-equiv (load_class_x
                                                                      classname
                                                                      s-equiv seen
                                                                      2)))
                                                       (cond ((not
                                                               (trivial-inv-env-do-not-change s1 s))
                                                              (load_class_x_induct 
                                                               classname s s-equiv
                                                               seen
                                                               2))
                                                             ((not
                                                               (trivial-inv-env-do-not-change s1-equiv s))
                                                              (load_class_x_induct
                                                               classname s s-equiv
                                                               seen 2))
                                                             (t 
                                                              (cond
                                                                ((not (no-fatal-error? s1))
                                                                 (load_class_x_induct
                                                                  classname s s-equiv
                                                                  seen 2))
                                                                ((not (no-fatal-error? s1-equiv))
                                                                 (load_class_x_induct
                                                                  classname s s-equiv
                                                                  seen 2))
                                                                (t 
                                                                 (list 
                                                                  (load_class_x_induct
                                                                   classname s s-equiv
                                                                   seen 2)
                                                                  (load_class_x_induct
                                                                   classname s1
                                                                   s1-equiv seen 1)))))))))))))))

          ((equal mode 2)
           (cond ((not (load_class_1-inv classname s seen))
                  (list p s s-equiv seen mode))
                 ((not (load_class_1-inv classname s-equiv seen))
                  (list p s s-equiv seen mode))
                 (t (mv-let (def-found1 class-desc1)
                            (class-by-name-s classname
                                             (external-class-table s))
                            (declare (ignore def-found1))
                            (mv-let (def-found2 class-desc2)
                                    (class-by-name-s classname 
                                                     (external-class-table s-equiv))
                                    (declare (ignore def-found2))
                                    (let ((supername1 (super-s class-desc1))
                                          (supername2 (super-s class-desc2)))
                                      (cond ((not (equal supername1 supername2))
                                             (list p s s-equiv seen mode))
                                            (t (load_class_x_induct supername1 s s-equiv
                                                                    (cons classname
                                                                          seen)
                                                                    3)))))))))
          ((equal mode 1)
           (cond ((not (load_class_2-inv classname s seen))
                  (list p s s-equiv seen mode))
                 ((not (load_class_2-inv classname s-equiv seen))
                  (list p s s-equiv seen mode))
                 (t (mv-let (def-found1 class-desc1)
                            (class-by-name-s classname
                                             (external-class-table s))
                            (declare (ignore def-found1))
                            (mv-let (def-found2 class-desc2)
                                    (class-by-name-s classname 
                                                     (external-class-table s-equiv))
                                    (declare (ignore def-found2))
                                    (let ((interfaces1 (interfaces-s class-desc1))
                                          (interfaces2 (interfaces-s class-desc2)))
                                      (cond ((not (equal interfaces2 interfaces1))
                                             (list p s s-equiv seen mode))
                                            (t 
                                             (load_class_x_induct interfaces1 s s-equiv 
                                                                  (cons classname seen) 0)))))))))
          ((equal mode 0)
           (cond ((not (consp interfaces))
                  (list p s s-equiv seen mode))
                 ((not (no-fatal-error? s))
                  (list p s s-equiv seen mode))
                 ((not (no-fatal-error? s-equiv))
                  (list p s s-equiv seen mode))
                 (t (cond ((mem (car interfaces) seen)
                           (list p s s-equiv seen mode))
                          ((and (class-loaded? (car interfaces) s)
                                (class-loaded? (car interfaces) s-equiv))
                           ;; I could add test of whether isInterface class-rep
                           ;; Sun Jun 20 18:07:50 2004
                           (load_class_x_induct (cdr interfaces) s s-equiv seen
                                                0))
                          ((and (not (class-loaded? (car interfaces) s))
                                (not (class-loaded? (car interfaces) s-equiv)))
                           (let ((new-s (load_class_x (car interfaces) s seen 3))
                                 (new-s-equiv (load_class_x (car interfaces)
                                                            s-equiv seen 3)))
                             (cond ((not (trivial-inv-env-do-not-change new-s
                                                                        s))
                                    (load_class_x_induct (car interfaces) 
                                                         s s-equiv 
                                                         seen 3))
                                   ((not (trivial-inv-env-do-not-change
                                          new-s-equiv s-equiv))
                                    (load_class_x_induct (car interfaces) 
                                                         s s-equiv 
                                                         seen 3))
                                   (t (cond ((not (no-fatal-error? new-s))
                                             (load_class_x_induct (car interfaces) 
                                                                  s s-equiv 
                                                                  seen 3))
                                            ((not (no-fatal-error? new-s-equiv))
                                             (load_class_x_induct (car interfaces) 
                                                                  s s-equiv 
                                                                  seen 3))
                                            (t (list (load_class_x_induct (car
                                                                           interfaces)
                                                                          s
                                                                          s-equiv
                                                                          seen
                                                                          3)
                                                     (load_class_x_induct (cdr
                                                                           interfaces)
                                                                          new-s
                                                                          new-s-equiv 
                                                                          seen
                                                                          0))))))))))))
           (t s)))))


(defcong equiv-state-except-thread-and-trace equal (class-loaded? p s) 2
  :hints (("Goal" :in-theory (enable class-loaded?))))
  

(defcong equiv-state-except-thread-and-trace equiv-state-except-thread-and-trace
  (load_class_x p s seen mode) 2
  :hints (("Goal" :do-not '(generalize fertilize)
           :induct (load_class_x_induct p s s-equiv seen mode))))

; (skip-proofs 
;  (defthm error-flag-set-thread-load_class_x
;    (equal (error-flag (load_class_x p (state-set-current-thread th s) 
;                                     seen mode))
;           (error-flag (load_class_x p s seen mode)))
;    :hints (("Goal" :do-not '(generalize)
;             :in-theory (disable state-set-current-thread)))))

(defthm equiv-state-except-thread-and-trace-set-current-thread
  (equiv-state-except-thread-and-trace (state-set-current-thread th s)
                                       s)
  :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace))))

(in-theory (disable state-set-current-thread))

(defthm no-fatal-error-set-thread-load_class_x
  (equal (no-fatal-error? (load_class_x p (state-set-current-thread th s) 
                                        seen mode))
         (no-fatal-error? (load_class_x p s seen mode))))


(defthm no-fatal-error?-after-load-implies-class-exists-externally
  (implies (and (no-fatal-error? (load_class fromClass s))
                (not (class-loaded? fromClass s)))
           (class-exists-externally? fromClass 
                                     (env-class-table (env s))))
  :hints (("Goal"  
           :in-theory (disable load_class_x state-set-current-thread
                       no-fatal-error?-after-load-class-x-implies-class-exists-externally
                       class-exists-externally?)
           :use 
           ((:instance
             no-fatal-error?-after-load-class-x-implies-class-exists-externally
             (mode 3) (p fromClass) (seen nil))))))
  
;;; 


;----------------------------------------------------------------------
;;;
;;; properties for 
;;;

(acl2::set-verify-guards-eagerness 2)

(local (in-theory (disable mv-to-slot)))

(defthm wff-state-load_class2
  (implies (wff-state s)
           (wff-state (load_class2 classname s)))
  :hints (("Goal" :in-theory (e/d (load_class2 fatalError) (load_cp_entry)))))


(defthm wff-state-load_class_x
  (implies (wff-state s)
           (wff-state (load_class_x p s seen mode)))
  :hints (("Goal" :in-theory (e/d (fatalError) ()))))


;; (defthm load_class_guard-strong-l-implies-wff-statici-class-rep
;;   (implies (and (load_class2_guard-strong1 l s)
;;                 (mv-let (found class-desc)
;;                         (class-by-name-s classname l)
;;                         (declare (ignore class-desc))
;;                         found))
;;            (wff-class-rep-static class-desc))

(defthm wff-static-class-table-found-implies-wff-static-class-rep
  (mv-let (found class-desc)
          (class-by-name-s classname l)
          (implies (and (wff-static-class-table l)
                        found)
                   (wff-class-rep-static class-desc))))

(defthm wff-static-class-table-member-all-names-implies
  (mv-let (found class-desc)
          (class-by-name-s p l)
          (declare (ignore found))
  (implies (and (mem p (all-class-names-s l))
                (wff-static-class-table l))
           (wff-class-rep-static class-desc))))






