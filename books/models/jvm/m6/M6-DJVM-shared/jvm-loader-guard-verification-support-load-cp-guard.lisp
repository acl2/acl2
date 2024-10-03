(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader")
(include-book "../M6-DJVM-shared/jvm-dynamic-loading-property")

(local (encapsulate ()

     (defun wff-class-table-state (s)
       (wff-class-table (class-table s)))

     (defun wff-heap-state (s)
       (wff-heap (heap s)))

     ;;
     ;; we define a equiv relation, we know most operation will preserve, except 
     ;; the extension to the instance-class-table. 
     ;;

     (defun equiv-state-instance-class-table (s1 s2)
       (and (equal (wff-state s1) (wff-state s2))
            (equal (wff-class-table-state s1) (wff-class-table-state s2))
            (equal (wff-heap-state s1) (wff-heap-state s2))
            (equal (env s1) (env s2))
            (equal (loader-inv s1) (loader-inv s2))
            (equal (instance-class-table s1)
                   (instance-class-table s2))))


     (defequiv equiv-state-instance-class-table
       :hints (("Goal" :in-theory (e/d () (wff-heap wff-state wff-class-table)))))

     (defcong equiv-state-instance-class-table equal (instance-class-table s) 1)
     (defcong equiv-state-instance-class-table equal (env s) 1)
     (defcong equiv-state-instance-class-table equal (wff-state s) 1)
     (defcong equiv-state-instance-class-table equal (wff-class-table-state s) 1)
     (defcong equiv-state-instance-class-table equal (wff-heap-state s) 1)
     (defcong equiv-state-instance-class-table equal (loader-inv s) 1)

     (in-theory (disable equiv-state-instance-class-table))


     (local 
      (defthm wff-class-table-class-table-norm
        (equal (wff-class-table (class-table s))
               (wff-class-table-state s))))

     (in-theory (disable wff-class-table-state))


     (local 
      (defthm wff-heap-heap-norm
        (equal (wff-heap (heap s))
               (wff-heap-state s))))

     (in-theory (disable wff-heap-state))


     ;;
     ;; we define another equiv on pairs that we know load_cp_entry will return. 
     ;;
     ;; (maybe we should use local)

     (defun equiv-two-tuple (t1 t2)
       (and (equal (mv-nth 0 t1) (mv-nth 0 t2))
            (equiv-state-instance-class-table (mv-nth 1 t1) (mv-nth 1 t2))))


     (defequiv equiv-two-tuple)

     (defun slot1 (tuple)
       (mv-nth 0 tuple))

     (defun slot2 (tuple)
       (mv-nth 1 tuple))


     (defcong equiv-two-tuple equal (slot1 tuple) 1)
     (defcong equiv-two-tuple equiv-state-instance-class-table (slot2 tuple) 1)

     (in-theory (disable equiv-two-tuple))


     ;----------------------------------------------------------------------
     ;
     ; (defthm load_cp_entry_guard_preserved_by_load_class
     ;   (implies (and (load_cp_entry_guard any s)
     ;                 (loader-inv s))
     ;            (load_cp_entry_guard cp (load_class anyx s))))

     ; shall we try more systematic way? (enable state-set *** )

     (in-theory (enable state-set-current-thread class-loaded?))
     (in-theory (disable accessflags-s constantpool-s aux loader-inv wff-class-rep
                         wff-class-table wff-env))

     (defthm class-loaded-load_class_x_3
       (implies (class-loaded? x s)
                (equal (load_class_x x s seen 3)
                       s)))

     (defcong equiv-state-instance-class-table
       equal (build-immediate-instance-data-guard any s) 2)
     (in-theory (disable build-immediate-instance-data-guard))


     (defcong equiv-state-instance-class-table
       equal (build-a-java-visible-instance-data-guard any s) 2
       :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))



     (defthm wff-state-equiv-state-instance-class-table
       (implies (and (wff-state s1) 
                     (equiv-state-instance-class-table s2 s1)
                     (syntaxp (> (acl2-count s2)
                                 (acl2-count s1))))
                (equal (build-a-java-visible-instance-guard any s2)
                       (build-a-java-visible-instance-guard any s1)))
       :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard)
                                       (equiv-state-instance-class-table)))))

     (defthm equiv-state-instance-class-table-if-wff
       (mylet* ((ns (MAKE-STATE (PC S)
                                (CURRENT-THREAD S)
                                (HEAP S)
                                (THREAD-TABLE S)
                                (CLASS-TABLE S)
                                (ENV S)
                                (ERROR-FLAG S)
                                (AUX S))))
       (implies (wff-state s)
                (equiv-state-instance-class-table ns s)))
       :hints (("Goal" :in-theory (e/d (equiv-state-instance-class-table 
                                        loader-inv wff-class-table-state
                                        wff-heap-state)
                                       (wff-class-table-class-table-norm
                                        wff-heap-heap-norm)))))


     (defthm equiv-state-instance-class-table-if-wff-specific
       (mylet* ((ns (MAKE-STATE (PC S)
                                (CURRENT-THREAD S)
                                (HEAP S)
                                (THREAD-TABLE S)
                                (CLASS-TABLE S)
                                (ENV S)
                                (ERROR-FLAG S)
                                (AUX S))))
       (implies (wff-state s)
                (equal (equiv-state-instance-class-table ns s) t)))
       :hints (("Goal" :in-theory (e/d (equiv-state-instance-class-table 
                                        loader-inv wff-class-table-state
                                        wff-heap-state)
                                       (wff-class-table-class-table-norm
                                        wff-heap-heap-norm)))))


     ;;;        
     ;;; proved the case where "class_loaded?" is true.
     ;;;

     ; (defthm load_cp_entry_guard_preserved_by_load_class
     ;    (implies (and (load_cp_entry_guard cp s)
     ;                  (wff-state s)
     ;                  (loader-inv s))
     ;             (load_cp_entry_guard cp (load_class anyx s)))
     ;    :hints (("Goal" :in-theory (e/d () (loader-inv))
     ;             :restrict ((wff-state-equiv-state-instance-class-table
     ;                         ((s1 s))))
     ;             :cases ((not (class-loaded? anyx s))))))

     ;;;
     ;;; now we need to deal with more difficult part. where class table changes! 
     ;;;
     ;(i-am-here)

     ; (defthm equiv-state-instance-class-table-if-wff-specific-2
     ;   (mylet* ((ns (MAKE-STATE pc 
     ;                            any
     ;                            hp
     ;                            (THREAD-TABLE S)
     ;                            (CLASS-TABLE S)
     ;                            (ENV S)
     ;                            (ERROR-FLAG S)
     ;                            (AUX S))))
     ;   (implies (wff-state s)
     ;            (equal (equiv-state-instance-class-table ns s) t)))
     ;   :hints (("Goal" :in-theory (e/d (equiv-state-instance-class-table 
     ;                                    loader-inv wff-class-table-state
     ;                                    wff-heap-state)
     ;                                   (wff-class-table-class-table-norm
     ;                                    wff-heap-heap-norm)))))


                             
     (defthm wff-heap-state-load_cp_entry
       (implies (wff-heap (heap s))
                (wff-heap (heap (mv-nth 1 (load_cp_entry cp s)))))
       :hints (("Goal" :in-theory (e/d (load_cp_entry wff-heap)
                                       (wff-heap-heap-norm)))))

     (defthm wff-heap-state-load_cp_entries
       (implies (wff-heap (heap s))
                (wff-heap (heap (mv-nth 1 (load_cp_entries cps s)))))
       :hints (("Goal" :in-theory (e/d () (wff-heap-heap-norm)))))

     (defthm wff-heap-bind
       (implies (wff-heap hp)
                (wff-heap (bind x v hp)))
       :hints (("Goal" :in-theory (enable wff-heap))))
                


     (defthm wff-heap-state-load_class2
       (implies (wff-heap (heap s))
                (wff-heap (heap (load_class2 any s))))
       :hints (("Goal" :in-theory (e/d (wff-heap-state load_class2)
                                       (wff-heap-heap-norm)))))


     (defthm wff-heap-state-load_class_x
       (implies (wff-heap-state s)
                (wff-heap-state (load_class_x any s seen mode)))
       :hints (("Goal" :in-theory (e/d (wff-heap-state)
                                       (wff-heap-heap-norm)))))

     (defthm wff-heap-state-implies-wff-heap
       (equal (wff-heap-state 
               (MAKE-STATE anypc 
                           anythread
                           (heap s)
                           anytt
                           anycl
                           anyenv
                           anyef
                           anyaux))
              (wff-heap-state s))
       :hints (("Goal" :in-theory (e/d (wff-heap-state)
                                       (wff-heap-heap-norm)))))

     ;; now we have proved simple assertions of in the load_cp_entry_guard
     ;; 
     ;; We need to deal with build-a-java-visible-instance-guard.
     ;;
     ;; The current approach is leaving update enabled. So the state is always of
     ;; form make-state ....  We chose to enable build-a-java-visible-instance-guard
     ;; so that the proof naturally reveals the dependency on class-table.

     ;; 
             

     (defthm wff-class-table-state-load_class2
       (implies (wff-class-table (class-table s))
                (wff-class-table (class-table (load_class2 any s))))
       :hints (("Goal" :in-theory (e/d (load_class2)
                                       (wff-class-table-class-table-norm)))))

     (defthm wff-class-table-state-load_class_x
       (implies (wff-class-table-state s)
                (wff-class-table-state (load_class_x any s seen mode)))
       :hints (("Goal" :in-theory (e/d (wff-class-table-state)
                                       (wff-class-table-class-table-norm)))))




     (defthm wff-class-table-implies-wff-class-table
       (equal (wff-class-table-state  
               (MAKE-STATE anypc 
                           anythread
                           anyheap
                           anytt
                           (class-table s)
                           anyenv
                           anyef
                           anyaux))
              (wff-class-table-state s))
       :hints (("Goal" :in-theory (e/d (wff-class-table-state)
                                       (wff-class-table-class-table-norm)))))


     (defthm wff-instance-class-table-implies-wff-instance-class-table
       (equal (wff-instance-class-table
               (instance-class-table
                (MAKE-STATE anypc 
                            anythread
                            anyheap
                            anytt
                            (class-table s)
                            anyenv
                            anyef
                            anyaux)))
              (wff-instance-class-table (instance-class-table s))))


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



     (defthm wff-instance-class-table-add-instance-class-rep
       (implies (and (wff-instance-class-table cl)
                     (wff-class-rep class))
                (wff-instance-class-table (add-instance-class-entry class cl)))
       :hints (("Goal" :in-theory (enable wff-instance-class-table 
                                          add-instance-class-entry))))


     (defthm wff-instance-class-table-preserved-by-load_class_x2-weak
       (implies (and (wff-instance-class-table (instance-class-table s))
                     (wff-static-class-table (external-class-table s)))
                (wff-instance-class-table (instance-class-table (load_class2 any
                                                                             s))))
       :hints (("Goal" :in-theory (e/d (load_class2)
                                       (make-runtime-class-rep)))))


     (defthm wff-instance-class-table-preserved-by-load_class_x-weak
       (implies (and (wff-instance-class-table (instance-class-table s))
                     (wff-static-class-table (external-class-table s)))
                (wff-instance-class-table (instance-class-table (load_class_x any s seen mode)))))



     ;; from jvm-loader.lisp we have: 
     ;
     ; (defcong equiv-state-except-thread-and-trace equiv-state-except-thread-and-trace
     ;   (load_class_x p s seen mode) 2
     ;   :hints (("Goal" :do-not '(generalize fertilize)
     ;            :induct (load_class_x_induct p s s-equiv seen mode))))
     ;

     ;; (i-am-here) ;; Sun Nov  7 17:57:15 2004

     ;; Fri Nov  5 13:41:44 2004

     ;; (defthm equiv-state-instance-class-table-make-thread
     ;;   (equiv-state-instance-class-table
     ;;    (MAKE-STATE any_pc
     ;;                any_thread
     ;;                (HEAP S)
     ;;                any_thread_table
     ;;                (CLASS-TABLE S)
     ;;                (ENV S)
     ;;                (ERROR-FLAG S)
     ;;                any_aux)
     ;;    s)
     ;;   :hints (("Goal" :in-theory (enable equiv-state-instance-class-table equiv-aux))))

     ;;;   
     ;;; add the extra assertion, make the following fails.
     ;;; 
     ;;; Fri Nov  5 13:44:41 2004
     ;;;


     (defun equiv-state-except-thread-and-trace2 (s1 s2) 
       (and ;(equal (pc s1) (pc s2))
            ;(equal (thread-table s1) (thread-table s2))
            (equal (heap s1) (heap s2))
            (equal (class-table s1) (class-table s2))
            (equal (env s1) (env s2))
            (equal (error-flag s1) (error-flag s2))))


     (defequiv equiv-state-except-thread-and-trace2)


     (defun equiv-tuple-load2 (tuple1 tuple2)
       (and (equal (mv-nth 0 tuple1) 
                   (mv-nth 0 tuple2))
            (equiv-state-except-thread-and-trace2 (mv-nth 1 tuple1)
                                                  (mv-nth 1 tuple2))))

     ;; (defun slot1-tuple-load (tuple)
     ;;   (mv-nth 0 tuple))

     ;; (defun slot2-tuple-load (tuple)
     ;;   (mv-nth 1 tuple))

     ;; ;(i-am-here)

     (defequiv equiv-tuple-load2)


     (defcong equiv-state-except-thread-and-trace2 equiv-tuple-load2
       (load_cp_entry cp s) 2
       :hints (("Goal" :in-theory (enable load_cp_entry))))


     (local (defthm mv-to-slot 
              (and (equal (mv-nth 0 tuple)
                          (slot1-tuple-load tuple))
                   (equal (mv-nth 1 tuple)
                          (slot2-tuple-load tuple)))
              :hints (("Goal" :in-theory (enable slot2-tuple-load
                                                 slot1-tuple-load)))))




     (in-theory (disable slot2-tuple-load slot1-tuple-load)) 

     (defcong equiv-tuple-load2 equiv-state-except-thread-and-trace2
       (slot2-tuple-load tuple) 1)

     (defcong equiv-tuple-load2 equal
       (slot1-tuple-load tuple) 1)

     (defcong equiv-state-except-thread-and-trace2 equal (class-table s) 1)
     (defcong equiv-state-except-thread-and-trace2 equal (heap s) 1)
     (defcong equiv-state-except-thread-and-trace2 equal (error-flag s) 1)
     (defcong equiv-state-except-thread-and-trace2 equal (env s) 1)

     (in-theory (disable equiv-state-except-thread-and-trace2))




     (defcong equiv-state-except-thread-and-trace2 equiv-tuple-load2 
       (load_cp_entries cps s) 2
       :hints (("Goal" :in-theory (disable equiv-state-except-thread-and-trace2))))


     ;(i-am-here)
     (in-theory (disable equiv-tuple-load2))

     (defthm equiv-state-except-thread-and-trace2-make-state
       (equal (equiv-state-except-thread-and-trace2 
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
                           anyaux2)) t)
       :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace2))))
                    


     (defcong equiv-state-except-thread-and-trace2
       equiv-state-except-thread-and-trace2
       (fatalError any s) 2
       :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace2
                                          fatalError))))



     (defcong equiv-state-except-thread-and-trace2 equiv-tuple-load2
       (build-an-instanceClass c s) 2
       :hints (("Goal" :in-theory (e/d (equiv-tuple-load2 slot1-tuple-load) 
                                       (mv-to-slot
                                        equiv-state-except-thread-and-trace2)))))

     (defcong equiv-state-except-thread-and-trace2 equal 
       (instance-class-table s) 1
       :hints (("Goal" :in-theory (e/d (instance-class-table) ()))))

     (defcong equiv-state-except-thread-and-trace2 equal 
       (array-class-table s) 1
       :hints (("Goal" :in-theory (e/d (array-class-table) ()))))


     (defcong equiv-state-except-thread-and-trace2 equiv-state-except-thread-and-trace2
       (load_class2 p s) 2
       :hints (("Goal" :in-theory (e/d (load_class2)
                                       (build-an-instanceClass)))))

     ; (defthm fatalerror-equiv-state-state
     ;   (EQUIV-STATE-EXCEPT-THREAD-AND-TRACE
     ;    (FATALERROR any S) s)
     ;   :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace fatalerror))))

     (defcong equiv-state-except-thread-and-trace2 equal 
       (no-fatal-error? s) 1
       :hints (("Goal" :in-theory (e/d (no-fatal-error?) ()))))


     (defcong equiv-state-except-thread-and-trace2 equal (class-loaded? p s) 2
       :hints (("Goal" :in-theory (enable class-loaded?))))
       

     (defcong equiv-state-except-thread-and-trace2 equiv-state-except-thread-and-trace2
       (load_class_x p s seen mode) 2
       :hints (("Goal" :do-not '(generalize fertilize)
                :induct (load_class_x_induct p s s-equiv seen mode))))


     (defthm equiv-state-except-thread-and-trace2-make-state-case
       (equiv-state-except-thread-and-trace2
        (MAKE-STATE any_pc
                    any_thread
                    (HEAP S)
                    any_thread_table
                    (CLASS-TABLE S)
                    (ENV S)
                    (ERROR-FLAG S)
                    any_aux)
        s)
       :hints (("Goal" :in-theory (enable equiv-state-except-thread-and-trace2))))


     ;;(skip-proofs 
     (defthm change-current-thread-does-not-change-class-table
        ;; what really care about is the relation between classes!!
        (equal (INSTANCE-CLASS-TABLE (LOAD_CLASS_X ANYX
                                                   (MAKE-STATE any_pc
                                                               any_thread
                                                               (HEAP S)
                                                               any_thread_table
                                                               (CLASS-TABLE S)
                                                               (ENV S)
                                                               (ERROR-FLAG S)
                                                               any_aux)
                                                   seen mode))
               (INSTANCE-CLASS-TABLE (LOAD_CLASS_X ANYX s seen mode)))
        :hints (("Goal" :in-theory (disable load_class_x))))


     ;; this is not quite true. if we do not have some extra assertions on 
     ;; instance-class-table 

     (defun all-found? (names env-cl)
       (if (endp names) t
         (mv-let (found class-desc)
                 (class-by-name-s (car names) env-cl)
                 (declare (ignore class-desc))
                 (and found
                      (all-found? (cdr names) env-cl)))))

     ; (defthm not-nil-collect-super-implies-bounded?
     ;   (implies (and (collect-superclass-list1 classname cl seen)
     ;                 (wff-instance-class-table cl))
     ;            (mem classname (collect-superclass-list1 classname cl seen))))
       
     (local (in-theory (disable mv-to-slot)))

     (defthm not-found-in-env-cl-not-class-term
       (implies (and (not (car (class-by-name-s classname env-cl)))
                     (all-found? (all-class-names cl) env-cl))
                (not (class-by-name classname cl))))


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
                (mem any (all-class-names (instance-class-table s)))))

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
                                       
     (defthm loader-inv-helper-implies-all-found?
       (implies (loader-inv-helper l cl env-cl)
                (all-found? (all-class-names l) env-cl))
       :hints (("Goal" :do-not '(generalize fertilize)
                :in-theory (enable collect-assignableToName
                                   correctly-loaded?))))


     (defthm loaded-in-a-loader-inv-state-superchain-is-fixed
       (implies (and (class-loaded? any s)
                     (no-fatal-error? s)
                     (loader-inv s))
                (equal (collect-superclass-list1 any (instance-class-table s) nil)
                       (collect-superclassname1 any (external-class-table s) nil)))
       :hints (("Goal" :restrict
                ((all-correctly-loaded-implies-collect-superclass-list
                  ((env-cl (external-class-table s))))
                 (loader-inv-helper-implies-all-found?
                  ((cl (instance-class-table s)))))
                :do-not-induct t
                :in-theory (disable external-class-table))))

     ;;; Wed Jun 30 14:14:43 2004. HERE: this is good. However, this is not the way
     ;;; to do prove the following: loading some other class does not affect 
     ;;; the collect-superclassname1. 
     ;;;
     ;;; We will show even there is a fatal error, we can still prove that property.
     ;;; (Do we need such a strong theorem?)
     ;;; Wed Jun 30 14:17:50 2004
     ;;;
     ;;; Maybe we can get away with adding no-fatal-error assertions everywhere.  In
     ;;; our current implementation, we know this fatal error during class loading
     ;;; will not corrupt the existing classes, which may not be always true.
     ;;; 
     ;;;

     (defthm collect-superclassname1-does-not-change
       (mylet* ((ns (load_class_x anyx s ss mode)))
               (equal (external-class-table ns)
                      (external-class-table s))))
               

     (defthm class-loaded?-is-perserved
       (implies (class-loaded? any s)
                (class-loaded? any (load_class2 anyx s)))
       :hints (("Goal" :in-theory (enable load_class2 add-instance-class-entry))))


     (defthm class-loaded-make-state-equal
       (equal (class-loaded? any (make-state any_pc 
                                             any_th
                                             any_hp
                                             any_thread_table
                                             (class-table s)
                                             any_env
                                             any_ef
                                             any_aux))
              (class-loaded? any s)))

     (defthm class-loaded?-is-perserved-by-load_class_x
       (implies (class-loaded? any s)
                (class-loaded? any (load_class_x anyx s ss mode)))
       :hints (("Goal" :in-theory (disable class-loaded?))))


     (defthm once-loaded-superchain-does-not-change
       (implies (and (class-loaded? any s)
                     (no-fatal-error? s)
                     (no-fatal-error? (load_class_x anyx s ss 3))
                     (loader-inv s))
                (equal (collect-superclass-list1 any 
                                                 (instance-class-table
                                                  (load_class_x anyx s ss 3)) nil)
                       (collect-superclass-list1 any 
                                                 (instance-class-table s)
                                                 nil)))
       :hints (("Goal" :do-not-induct t
                :in-theory (disable external-class-table no-fatal-error? class-loaded?))))

     ;;
     ;; only care about the mode 3. which corresponds to load_class
     ;;


     ;; Superclass chain does not change because of loading!!
     ;
     ;
     ; (defthm once-loaded-superchain-does-not-change
     ;   (implies (and (class-loaded? any s)
     ;                 (no-fatal-error? s)
     ;                 (no-fatal-error? (load_class_x anyx s ss mode))
     ;                 (loader-inv s))
     ;            (equal (collect-superclass-list1 any 
     ;                                             (instance-class-table
     ;                                              (load_class_x anyx s ss mode)) nil)
     ;                   (collect-superclass-list1 any 
     ;                                             (instance-class-table s)
     ;                                             nil)))
     ;   :hints (("Goal" :do-not-induct t
     ;            :in-theory (disable external-class-table no-fatal-error? class-loaded?))))

     ;; important lemma.
     ;;

     ; >V d          (DEFUN
     ;                BUILD-IMMEDIATE-INSTANCE-DATA-GUARD
     ;                (CLASS-NAME S)
     ;                (AND
     ;                 (WFF-STATE S)
     ;                 (WFF-CLASS-TABLE (CLASS-TABLE S))
     ;                 (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE S))
     ;                 (WFF-CLASS-REP
     ;                      (CLASS-BY-NAME CLASS-NAME (INSTANCE-CLASS-TABLE S)))
     ;                 (WFF-CLASS-FIELDS
     ;                  (FIELDS
     ;                       (CLASS-BY-NAME CLASS-NAME (INSTANCE-CLASS-TABLE S))))))


     (defun build-immediate-instance-data-guard-alternative (class-name cl)
       (and (wff-class-rep (class-by-name class-name cl))
            (wff-class-fields (fields (class-by-name class-name cl)))))

     (defthm build-immediate-instance-data-guard-alternative-extension
       (implies (and (build-immediate-instance-data-guard-alternative classname cl)
                     (not (equal (classname new-class) classname)))
                (build-immediate-instance-data-guard-alternative classname
                                                                 (add-instance-class-entry 
                                                                   new-class cl)))
       :hints (("Goal" :in-theory (enable add-instance-class-entry))))

     (defthm build-immediate-instance-data-guard-implied-by
       (implies (and (build-immediate-instance-data-guard-alternative classname 
                                                                      (instance-class-table s))
                     (wff-state s)
                     (wff-instance-class-table (instance-class-table s))
                     (wff-class-table (class-table s)))
                (build-immediate-instance-data-guard classname s))
       :hints (("Goal" :in-theory (enable build-immediate-instance-data-guard))))

     ;;; For proving the following 
     ; (skip-proofs
     ;  (defthm
     ;    build-immediate-instance-data-guard-alternative-perserved-by-load_class_x
     ;    (implies (and (build-immediate-instance-data-guard-alternative any
     ;                                                                   (instance-class-table s))
     ;                  (class-loaded? any s)
     ;                  (loader-inv s))
     ;             (build-immediate-instance-data-guard-alternative any
     ;                                                              (instance-class-table 
     ;                                                               (load_class_x
     ;                                                                anyx s seen mode))))))

     ;; we need class-by-name is not changed! 

     (defthm class-by-name-load_class2
       (implies (not (equal any anyx))
                (equal (class-by-name any (instance-class-table (load_class2 anyx s)))
                       (class-by-name any (instance-class-table s))))
       :hints (("Goal" :in-theory (enable load_class2 add-instance-class-entry 
                                          classname))))
               


     (defthm load_class_does_not_change_loaded_class
       (implies (class-loaded? any s)
                (equal (class-by-name any (instance-class-table 
                                           (load_class_x anyx s seen mode)))
                       (class-by-name any (instance-class-table s))))
       :hints (("Goal" :do-not '(fertilize generalize))
               ("Subgoal *1/8" :cases ((equal any anyx)))))


     (defthm
       build-immediate-instance-data-guard-alternative-perserved-by-load_class_x
       (implies (and (build-immediate-instance-data-guard-alternative any
                                                                      (instance-class-table s))
                     (class-loaded? any s)
                     (loader-inv s))
                (build-immediate-instance-data-guard-alternative any
                                                                 (instance-class-table 
                                                                  (load_class_x
                                                                   anyx s seen mode)))))
       
     (defthm build-immediate-instance-data-guard-implies-alternative
       (implies (build-immediate-instance-data-guard name s)
                (build-immediate-instance-data-guard-alternative name
                                                                 (instance-class-table s)))
       :hints (("Goal" :in-theory (enable build-immediate-instance-data-guard)))
       :rule-classes :forward-chaining)


     (defthm build-immediate-instance-data-guard-implies-alternative-b
       (implies (build-immediate-instance-data-guard name s)
                (build-immediate-instance-data-guard-alternative name
                                                                 (instance-class-table s)))
       :hints (("Goal" :in-theory (enable build-immediate-instance-data-guard))))

     ;;; updated for ACL2 2.8 --> 2.9 ;;Fri Oct  8 15:17:44 2004




     (defthm loadr-inv-implies-wff-static-class-table
       (implies (loader-inv s)
                (wff-static-class-table (env-class-table (env s))))
       :hints (("Goal" :in-theory (enable loader-inv))))


     (defthm
       class-table-correct-extension-does-not-change-build-immedimate-data-guard
       (implies (and (build-immediate-instance-data-guard classname s)
                     (class-loaded? classname s)
                     (loader-inv s))
                (build-immediate-instance-data-guard
                    classname (load_class_x anyx s seen mode)))
       :hints (("Goal" :in-theory (disable load_class_x class-loaded? 
                                           build-immediate-instance-data-guard-alternative)
                :expand (build-immediate-instance-data-guard classname s))))

     (defun all-loaded? (classnames s)
       (if (endp classnames) t
         (and (class-loaded? (car classnames) s)
              (all-loaded? (cdr classnames) s))))


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

     ;; strange Wed Jun 30 15:00:42 2004. It proves by induction.

     ;; Wed Jun 30 15:02:09 2004


     ; (skip-proofs
     ;  (defthm build-a-java-visible-instance-data-guard-equal
     ;    (implies (integerp int_pc)
     ;             (equal (build-a-java-visible-instance-data-guard
     ;                     classnames
     ;                     (make-state 
     ;                      int_pc any_thread wff_heap any_tt 
     ;                      (class-table s)
     ;                      any_env
     ;                      any_errorflag
     ;                      any_aux))
     ;                    (build-a-java-visible-instance-data-guard  
     ;                     classnames s)))))

     (defthm build-immediate-instance-data-guard-equal
        (implies (and (integerp int_pc)
                      (wff-state s))
                 (equal (build-immediate-instance-data-guard
                         classname
                         (make-state 
                          int_pc any_thread wff_heap any_tt 
                          (class-table s)
                          any_env
                          any_errorflag
                          any_aux))
                        (build-immediate-instance-data-guard
                         classname s)))
        :hints (("Goal" :do-not '(generalize)
                 :in-theory (enable build-immediate-instance-data-guard))))


     (defthm build-a-java-visible-instance-data-guard-equal
        (implies (and (integerp int_pc)
                      (wff-state s))
                 (equal (build-a-java-visible-instance-data-guard
                         classnames
                         (make-state 
                          int_pc any_thread wff_heap any_tt 
                          (class-table s)
                          any_env
                          any_errorflag
                          any_aux))
                        (build-a-java-visible-instance-data-guard  
                         classnames s)))
        :hints (("Goal" :do-not '(generalize))))
               
     (defthm loader-inv-and-loaded-implies-all-loaded-generalize
       (implies (and (loader-inv s)
                     (equal (instance-class-table s) cl)
                     (class-loaded? classname s))
                (all-loaded? (COLLECT-SUPERCLASS-LIST1 classname
                                                       cl
                                                       seen)
                             s))
       :hints (("Goal" :in-theory (disable all-loaded? class-loaded?))))

     (defthm wff-state-implies-integerp-pc
       (implies (wff-state s)
                (integerp (pc s)))
       :rule-classes :type-prescription
       :hints (("Goal" :in-theory (enable wff-state pc))))

     (defthm loader-inv-equal
       (implies (loader-inv s)
                (loader-inv (MAKE-STATE (pc s)
                                      any_thread
                                      any_heap
                                      any_thread_table
                                      (CLASS-TABLE S)
                                      (ENV S)
                                      (ERROR-FLAG S)
                                      any_aux)))
       :hints (("Goal" :in-theory (enable loader-inv))))



     (defthm load_cp_entry_guard_preserved_by_load_class
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class anyx s))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class anyx s)))
        :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard) (loader-inv))
                 :restrict ((wff-state-equiv-state-instance-class-table
                             ((s1 s))))
                 :cases ((not (class-loaded? anyx s))))))



     (defthm load_cp_entries_guard_preserved_by_load_class
        (implies (and (load_cp_entries_guard cps s)
                      (wff-state s)
                      (no-fatal-error? (load_class anyx s))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entries_guard cps (load_class anyx s)))
        :hints (("Goal" :in-theory (disable load_class no-fatal-error?
                                            load_cp_entry_guard
                                            loader-inv class-loaded?))))


     (defthm load_cp_entry_guard_preserved_by_load_class_x_mode_3
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen 3))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class_x anyx s seen 3)))
        :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard) (loader-inv))
                 :restrict ((wff-state-equiv-state-instance-class-table
                             ((s1 s))))
                 :cases ((not (class-loaded? anyx s))))))



     (defthm load_cp_entry_guard_preserved_by_load_class_x_mode_2
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen 2))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class_x anyx s seen 2)))
        :hints (("Goal" :expand (load_class_x anyx s seen 2))))


     (defun mode-0-loaded-induct (p s seen) 
       (if (endp p) (list p s seen)
         (mode-0-loaded-induct (cdr p)
                               (load_class_x (car p) s seen 3)
                               seen)))

     (defthm load_cp_entry_guard_preserved_by_load_class_x_mode_0
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen 0))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class_x anyx s seen 0)))
        :hints (("Goal" :in-theory (disable load_cp_entry_guard)
                 :induct (mode-0-loaded-induct anyx s seen))))


     (defthm load_cp_entry_guard_preserved_by_load_class_x_mode_1
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen 1))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class_x anyx s seen 1)))
        :hints (("Goal" :in-theory (disable load_cp_entry_guard)
                 :expand (load_class_x anyx s seen 1))))
                 

     (defthm load_cp_entry_guard_preserved_by_load_class_x
        (implies (and (load_cp_entry_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen mode))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entry_guard cp (load_class_x anyx s seen mode)))
        :hints (("Goal" :do-not-induct t
                 :cases ((equal mode 3) (equal mode 2) (equal mode 1) (equal mode
                                                                             0)))))

     (defthm load_cp_entries_guard_preserved_by_load_class_x
        (implies (and (load_cp_entries_guard cp s)
                      (wff-state s)
                      (no-fatal-error? (load_class_x anyx s seen mode))
                      (class-loaded? "java.lang.Object" s)
                      (loader-inv s))
                 (load_cp_entries_guard cp (load_class_x anyx s seen mode)))
        :hints (("Goal"  :in-theory (disable load_class_x wff-state
                                             no-fatal-error?
                                             load_cp_entry_guard class-loaded?))))
))          

(defthm load_cp_entry_guard_preserved_by_load_class
   (implies (and (load_cp_entry_guard cp s)
                 (wff-state s)
                 (no-fatal-error? (load_class anyx s))
                 (class-loaded? "java.lang.Object" s)
                 (loader-inv s))
            (load_cp_entry_guard cp (load_class anyx s)))
   :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard) (loader-inv))
            :restrict ((wff-state-equiv-state-instance-class-table
                        ((s1 s))))
            :cases ((not (class-loaded? anyx s))))))


(defthm load_cp_entries_guard_preserved_by_load_class
   (implies (and (load_cp_entries_guard cps s)
                 (wff-state s)
                 (no-fatal-error? (load_class anyx s))
                 (class-loaded? "java.lang.Object" s)
                 (loader-inv s))
            (load_cp_entries_guard cps (load_class anyx s)))
   :hints (("Goal" :in-theory (disable load_class no-fatal-error?
                                       load_cp_entry_guard
                                       loader-inv class-loaded?))))


(defthm load_cp_entry_guard_preserved_by_load_class_x
   (implies (and (load_cp_entry_guard cp s)
                 (wff-state s)
                 (no-fatal-error? (load_class_x anyx s seen mode))
                 (class-loaded? "java.lang.Object" s)
                 (loader-inv s))
            (load_cp_entry_guard cp (load_class_x anyx s seen mode)))
   :hints (("Goal" :do-not-induct t
            :cases ((equal mode 3) (equal mode 2) (equal mode 1) (equal mode
                                                                        0)))))

(defthm load_cp_entries_guard_preserved_by_load_class_x
   (implies (and (load_cp_entries_guard cp s)
                 (wff-state s)
                 (no-fatal-error? (load_class_x anyx s seen mode))
                 (class-loaded? "java.lang.Object" s)
                 (loader-inv s))
            (load_cp_entries_guard cp (load_class_x anyx s seen mode)))
   :hints (("Goal"  :in-theory (disable load_class_x wff-state
                                        no-fatal-error?
                                        load_cp_entry_guard class-loaded?))))
  

(defthm loaded-in-a-loader-inv-state-superchain-is-fixed
  (implies (and (class-loaded? any s)
                (no-fatal-error? s)
                (loader-inv s))
           (equal (collect-superclass-list1 any (instance-class-table s) nil)
                  (collect-superclassname1 any (external-class-table s) nil)))
  :hints (("Goal" :restrict
           ((all-correctly-loaded-implies-collect-superclass-list
             ((env-cl (external-class-table s))))
            (loader-inv-helper-implies-all-found?
             ((cl (instance-class-table s)))))
           :do-not-induct t
           :in-theory (disable external-class-table))))


(defun all-loaded? (classnames s)
  (if (endp classnames) t
    (and (class-loaded? (car classnames) s)
         (all-loaded? (cdr classnames) s))))


(defthm loader-inv-and-loaded-implies-all-loaded
    (implies (and (loader-inv s)
                  (class-loaded? classname s))
             (all-loaded? (COLLECT-SUPERCLASS-LIST1 classname
                                                    (INSTANCE-CLASS-TABLE S)
                                                    seen)
                          s)))


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
 

