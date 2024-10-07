(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-type-value")
(include-book "../M6-DJVM-shared/jvm-object-manipulation-primitives")
(include-book "../M6-DJVM-shared/jvm-thread")
(include-book "../M6-DJVM-shared/jvm-thread-primitives")
(include-book "../M6-DJVM-shared/jvm-linker")
(include-book "../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../M6-DJVM-shared/jvm-monitor-primitives")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-obj")


(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)


;; primitives to manipulate exceptions
;; 1. find the appropriate exception handler
;; 2. find the error message contained in the exception.


;; Thu Apr  8 19:39:17 2004
;;
;; Only called from the JVM when current-thread is -1 which I will assert when
;; current-thread is -1, no thread is thrown!!
;; 

(acl2::set-verify-guards-eagerness 2)

(defun ERROR_THROW (i s)
  (declare (xargs :guard t))
  ;; I could assert consistent-state in consistent-state.  however that is not
  ;; defined, yet!  Thu Apr 8 19:41:49 2004. the same problem as with
  ;; jvm-loader One could combine guard verification with
  ;; consistency-perserving. 
  (declare (ignore i))
  s)


(defun wff-exception-hander (handler)
  (and (consp handler)
       (true-listp handler)
       (equal (car handler) 'handler)
       (equal (len handler) 5)
       (integerp (nth 1 handler)) 
       (integerp (nth 2 handler))
       (integerp (nth 3 handler))
       (wff-type-rep (nth 4 handler))))
       


(defun handler-start (handler)
  (declare (xargs :guard (wff-exception-hander handler)))
  (nth 1 handler))

(defun handler-end (handler)
  (declare (xargs :guard (wff-exception-hander handler)))
  (nth 2 handler))

(defun handler-entry-point (handler)
  (declare (xargs :guard (wff-exception-hander handler)))
  (nth 3 handler))

;;;
;;; DJVM will check the entry point at right position in an instruction stream.
;;; need to assert this as part of consistent-state Thu Apr 8 19:55:39 2004
;;;

(defun handler-exception-type (handler)
  (declare (xargs :guard (wff-exception-hander handler)))
  (normalize-type-rep (nth 4 handler)))

(include-book "../M6-DJVM-shared/jvm-exceptions-guard-verification-1")

(defun correct-java-lang-String-class (s)
  (and (wff-state s)
       (wff-class-table (class-table s))
       (wff-instance-class-table (instance-class-table s))       
       (equal (class-by-name "java.lang.String" (instance-class-table s))
              (runtime-java-lang-String))))
       

;; (defthm correct-java-lang-String-class-implies-field-access-to
;;   (implies (and (correct-java-lang-String-class s)
;;                 (bound? str-ref (heap s)))
;;            (field-access-guard "java.lang.String" "value" str-ref s)))
  
;;;
;;; this above is not true, we really need to know the OBJECT is
;;; consistent-object.
;;;
;;; HOWEVER consistent-object has not be defined yet!! 
;;;
;;;
;;; thus the guard is quite complicated
;;;

(defun JavaString-to-ACL2-str-guard (str-ref s)
  (and (wff-state s)
       (wff-heap (heap s))
       (bound? str-ref (heap s))
       (correct-java-lang-String-class s)
       (field-access-guard "java.lang.String" "value"  str-ref s)
       (field-access-guard "java.lang.String" "offset" str-ref s)
       (field-access-guard "java.lang.String" "count" str-ref s)
       (mylet* ((array-ref (m6-getfield "java.lang.String" "value" str-ref s))
                (array-obj (deref array-ref (heap s)))
                (array-data (array-data array-obj))
                (start (m6-getfield "java.lang.String" "offset" str-ref s))
                (len   (m6-getfield "java.lang.String" "offset" str-ref s))
                (codes (sub-list array-data start len)))
               (or (equal array-ref -1)
                   (and (bound? array-ref (heap s))
                        (wff-internal-array array-obj)
                        (integerp start)
                        (integerp len)
                        (<= 0 start)
                        (<= 0 len)
                        (< (+ start len) (array-bound array-obj))
                        (chars-numsp codes))))))
                        
           
;; The guard is complicated but easy to establish!!
;;
;; ACL2 should be more intelliegent to figure out the minimum guard!! 

(acl2::set-verify-guards-eagerness 0)

(defun JavaString-to-ACL2-str (str-ref s)
  (declare (xargs :guard (JavaString-to-ACL2-str-guard str-ref s)))
  (mylet* ((array-ref (m6-getfield "java.lang.String" "value"  str-ref s))
           (start     (m6-getfield "java.lang.String" "offset" str-ref s))
           (len       (m6-getfield "java.lang.String" "count"  str-ref s))
           (array-obj (deref array-ref (heap s)))
           (array-data (array-data array-obj))
           (codes      (sub-list array-data start len)))
          (if (equal array-ref -1)
              ""
            (make-acl2-string (code-to-chars codes)))))


(defun throw-exception2 (obj-ref s)
  (prog2$ (acl2::cw "uncaught exception ~p0!~%Stop current-thread ~p1~%"
                    obj-ref (current-thread s))
          (stopThread s)))


(defun find-handler (handlers exception-type ip-offset s)
  (let ((handler (car handlers)))
    (if (endp handlers)
        (mv nil s)
      (let* ((start (handler-start handler))
             (end   (handler-end   handler))
             (type  (handler-exception-type handler))
             (s1    (resolveClassReference type s))) ;; this can raise fatal error
        (if (not (no-fatal-error? s1))  ;; pass the fatal error on.
            (mv nil s1)
          (if (or (< ip-offset start)
                  (> ip-offset end))
              (find-handler (cdr handlers) exception-type ip-offset s)
            (mv-let (assignable s2)
                    (isAssignableTo exception-type type s1)
                    (if assignable
                        (mv handler s2)
                      (find-handler (cdr handlers) exception-type ip-offset s2)))))))))
      



(defun getExceptionMessage (obj-ref s)
  (let* ((obj (deref obj-ref s))
         (specific-info (specific-info obj))
         (msg-ref  (specific-info-throwable-instance-message specific-info)))
    msg-ref))
    



;--- primitives for dealing with monitors, exception handling need that. ---
;
;    according to JVM spec, if monitorExit is called in an incorrect state
;    the an exception need to be raised. however in KVM implementation, this is
;    not the case. In MonitorExit no exception is thrown, instead a variable is
;    used to record what kind of exception is thrown.
;
;---

;; it refers to many helper functions, such as obj-monitor-by-ref, 
;; which is defined jvm-monitors.

;; (mv * * *)
(defun monitorExit (obj-ref s)
  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (if (not (equal (owner monitor) (current-thread s)))
        (mv 'MonitorStatusError  "IllegalMonitorStateException" s)
      (let* ((new-monitor (monitor-set-depth (- (depth monitor) 1)
                                             monitor))
             (new-state (update-obj-monitor obj-ref new-monitor s)))
        (if (equal (depth new-monitor) 0)
            (mv 'MonitorStatusRelease nil (removeMonitorWait obj-ref new-state))
          (mv 'MonitorStatusOwn nil new-state))))))



;; Mon Dec 29 15:44:53 2003

;; (defun wff-thread-strong1 (thread)
;;   (and (wff-thread thread)
;;        (consp (thread-call-stack thread))))

;; (defun wff-thread-table-strong1 (tt)
;;   (if (endp tt)
;;       t
;;     (and (wff-thread-strong1 (car tt))
;;          (wff-thread-table-strong1 (cdr tt)))))


(defun call-stack-depth (s)
  (let ((tid (current-thread s)))
    (if (equal tid -1)
        1
      (if (not (wff-thread-table (thread-table s)))
          1
      (let ((thd (thread-by-id tid (thread-table s))))
        (if (not (current-thread-exists? s))
            1
          (let ((call-stack (thread-call-stack thd)))
            (+ (len call-stack) 2))))))))


(defun locked-stage (s)
  (let* ((curframe (current-frame s))
         (sync-obj-ref (sync-obj-ref curframe)))
    (if (equal sync-obj-ref -1)
        1
      2)))


(defun exception-measure (stage s)
  (cons (cons (cons (call-stack-depth s) 0)
        (locked-stage s))
        stage))



(defthm build-java-visible-instance-data-only-change-heap
  (mv-let (obj s1)
          (build-a-java-visible-instance-data classnames s0)
          (declare (ignore obj))
  (and    (equal (pc s1) (pc s0))
          (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
          (equal (thread-table   s1) (thread-table s0))
          (equal (class-table    s1) (class-table  s0))
          (equal (env            s1) (env          s0))
          (equal (error-flag     s1) (error-flag   s0))
          )))


(in-theory (disable env))
(defthm instantiate-only-change-heap
  (mv-let (obj s1)
          (instantiate classname s0)
          (declare (ignore obj))
  (and    (equal (pc s1) (pc s0))
          (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
          (equal (thread-table   s1) (thread-table s0))
          (equal (class-table    s1) (class-table  s0))
          (equal (env            s1) (env          s0))
          (equal (error-flag     s1) (error-flag   s0))
          )))
    
(in-theory (disable instantiate))


(defthm current-thread-pushFrame0
  (equal (current-thread (pushFrame0 anyFrame s))
         (current-thread s)))


(defthm current-thread-popFrame
  (equal (current-thread (popFrame s))
         (current-thread s)))

(in-theory (disable make-thread))


(defthm wff-thread-make-thread 
  (wff-thread (make-thread id 
                           saved-pc 
                           cs
                           status
                           m-ref
                           mdepth
                           thread-ref))
  :hints (("Goal" :in-theory (enable wff-thread make-thread))))




(defthm wff-thread-table-is-preserved-by-pushFrame
  (implies (wff-thread-table (thread-table s))
           (wff-thread-table (thread-table (pushFrame0 anyFrame s)))))


(defthm wff-thread-table-is-preserved-by-popFrame
  (implies (wff-thread-table (thread-table s))
           (wff-thread-table (thread-table (popFrame s)))))

(defthm wff-thread-table-thread-id
  (implies (thread-by-id id tt)
           (equal (thread-id (thread-by-id id tt))
                  id)))


(defthm thread-exists?-implies-thread-exists?
  (implies (and (thread-by-id id tt)
                (equal (thread-id new-thread) id))
           (equal (thread-by-id id (replace-thread-table-entry (thread-by-id id tt)
                                                               new-thread tt))
                  new-thread)))

(defthm thread-id-thread
  (implies (not thread)
           (not (thread-id thread))))


;; the problem is that id could be nil!! 

(defthm thread-exists?-implies-thread-exists?-2
  (implies (thread-by-id id tt)
           (thread-by-id id (replace-thread-table-entry 
                             (thread-by-id id tt)
                             (make-thread id pc cs s m md obj) tt))))


(in-theory (enable pushFrame0 popFrame))


(defthm thread-call-stack-pushFrame 
  (implies (and (thread-by-id (current-thread s) (thread-table s))
                (wff-thread-table (thread-table s))
                (equal (current-thread s) id))
           (equal (thread-call-stack 
                   (thread-by-id id
                                 (thread-table (pushFrame0 anyFrame s))))
                  (cons anyFrame (thread-call-stack (thread-by-id (current-thread s)
                                                                  (thread-table s)))))))


(defthm thread-call-stack-popFrame 
  (implies (and (thread-by-id (current-thread s) (thread-table s))
                (wff-thread-table (thread-table s))
                (equal (current-thread s) id))
           (equal (thread-call-stack 
                   (thread-by-id id
                                 (thread-table (popFrame s))))
                  (cdr (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))))


(defthm thread-exists?-implies-thread-exists?-3
  (implies (and (thread-by-id (current-thread s) (thread-table s))
                (wff-thread-table (thread-table s))
                (equal (current-thread s) id))
           (thread-by-id id (thread-table 
                             (pushFrame0 anyFrame s)))))

(defthm thread-exists?-implies-thread-exists?-4
  (implies (and (thread-by-id (current-thread s) (thread-table s))
                (wff-thread-table (thread-table s))
                (equal (current-thread s) id))
           (thread-by-id id (thread-table (popFrame s)))))



(in-theory (disable popFrame pushFrame0))

(defthm call-stack-depth-property
   (let* ((tid (current-thread s))
          (thd (thread-by-id tid (thread-table s)))
          (cs  (thread-call-stack thd)))
     (and (implies (equal tid -1) 
                   (equal (call-stack-depth s) 1))
          (implies (and (not (equal tid -1))
                        (not (current-thread-exists? s)))
                   (equal (call-stack-depth s) 1))
          (implies (and  (not (endp cs))
                         (not (equal tid -1)) ;; this is really annoying
                         (wff-thread-table (thread-table s))
                         (current-thread-exists? s))
                   (equal (call-stack-depth (pushFrame0 anyFrame 
                                                        (popFrame s)))
                          (call-stack-depth s)))
          (implies (and (not (endp cs))
                        (not (equal tid -1))
                        (wff-thread-table (thread-table s))
                        (current-thread-exists? s))
                   (equal (call-stack-depth (popFrame s))
                          (- (call-stack-depth s) 1)))
          (implies (and (endp cs)
                        (not (equal tid -1))
                        (wff-thread-table (thread-table s))
                        (current-thread-exists? s))
                   (equal (call-stack-depth s)
                          2)))))


;-----------------------
;
#| moved to jvm-loader.lisp
;; ----- start to prove load_class_only_change_class_table_error_flag_heap
|#

(in-theory (disable env))
 
(defthm getClass_only_change_class_table_error_flag_heap
  (let ((s1 (getClass classname s0)))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
             (equal (thread-table   s1) (thread-table s0))
             (equal (env            s1) (env          s0))
            ))) ;; need to find the measure for admit the load_class
                ;; functions.


;; has free variable in it.

;; --- end of proving load_class_only_change
(in-theory (disable getClass))


;; --- start to prove find-handler does not change state ---

(in-theory (enable fatalError))
(defthm isSuperClass1-only-change-class-table-error-flag-heap
   (mv-let (assignable s1)
           (isSuperClass1 t1 t2 s0 seen)
           (declare (ignore assignable))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))
(in-theory (disable isSuperClass1))

;; 


(defthm isAssignableTo-only-change-class-table-error-flag-heap
   (mv-let (assignable s1)
           (isAssignableTo t1 t2 s0)
           (declare (ignore assignable))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))



(in-theory (disable isAssignableTo))


 ;; --- start to prove resolveClassReference -----




(defthm load_array_class2-only-change-class-table-error-flag-heap
   (let ((s1 (load_array_class2 base-type s0)))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))
  ;; --- end of proving resolveClassReference ---- 
(in-theory (disable load_array_class2))



(defthm load_array_class-only-change-class-table-error-flag-heap
   (let ((s1 (load_array_class base-type s0)))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))
  ;; --- end of proving resolveClassReference ---- 
(in-theory (disable load_array_class))





(defthm resolveClassReference-only-change-class-table-error-flag-heap
   (let ((s1 (resolveClassReference classname s0)))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))
  ;; --- end of proving resolveClassReference ---- 
(in-theory (disable resolveClassReference))



(defthm find_handler__only_change_class_table_error_flag_heap
   (mv-let (handler s1)
           (find-handler handlers exception-type ip-offset s0)
           (declare (ignore handler))
     (and    (equal (pc s1) (pc s0))
             (equal (current-thread s1) (current-thread s0))
          ;; (equal (heap s1) (heap s0))
             (equal (thread-table   s1) (thread-table s0))
          ;; (equal (class-table    s1) (class-table  s0))
             (equal (env            s1) (env          s0))
          ;; (equal (error-flag     s1) (error-flag   s0))
            )))
  ;; has free variable in it.

;;----- end of proving find-handler does not change state
(in-theory (disable find-handler))

;;;; Mon Dec 29 23:17:03 2003 chose not to talk about current-thread-exists?
;;;; only talk about thread-by-id ....
;;;; but keep the following!! 

(defthm current-thread-exists-equal-2
  (let ((s1 (make-state pc  (current-thread s0) hp (thread-table s0) cl env ef aux)))
    (equal (current-thread-exists? s1)
           (current-thread-exists? s0)))
  :hints (("Goal" :in-theory (enable current-thread-exists?))))



(defthm current-thread-exists?-getClass-not-changed
  (equal (current-thread-exists? (getClass classname s0))
         (current-thread-exists? s0))
  :hints (("Goal" :in-theory (enable current-thread-exists?))))



(defthm current-thread-exists?-find-handler-not-changed
  (mv-let (handler s1)
           (find-handler handlers exception-type ip-offset s0)
           (declare (ignore handler))
  (equal (current-thread-exists? s1)
         (current-thread-exists? s0)))
  :hints (("Goal" :in-theory (enable current-thread-exists?))))



(defthm call-stack-depth-exists-equal-2
  (let ((s1 (make-state pc  (current-thread s0) hp (thread-table s0) cl env ef aux)))
    (equal (call-stack-depth s1)
           (call-stack-depth s0)))
  :hints (("Goal" :in-theory (enable call-stack-depth))))


(defthm call-stack-depth-getClass-not-changed
  (equal (call-stack-depth (getClass classname s0))
         (call-stack-depth  s0))
  :hints (("Goal" :in-theory (enable call-stack-depth))))


(defthm call-stack-depth-find-handler-not-changed
  (mv-let (handler s1)
           (find-handler handlers exception-type ip-offset s0)
           (declare (ignore handler))
  (equal (call-stack-depth s1)
         (call-stack-depth  s0)))
  :hints (("Goal" :in-theory (enable call-stack-depth))))
  

(defthm current-frame-equal-2
  (let ((s1 (make-state pc  (current-thread s0) hp (thread-table s0) cl env ef aux)))
    (equal (current-frame s1)
           (current-frame s0))))


(defthm current-frame-getClass-not-changed
  (equal (current-frame (getClass classname s0))
         (current-frame s0)))

(defthm current-frame-find-handler-not-changed
  (mv-let (handler s1)
          (find-handler handlers exception-type ip-offset s0)
          (declare (ignore handler))
  (equal (current-frame s1)
         (current-frame s0)))
  :hints (("Goal" :in-theory (enable current-frame))))
  



;; this are used for talking about the sync-obj-ref 

(in-theory (enable current-frame))
(defthm current-frame-pushFrame0-simplify-to
  (implies (and (wff-thread-table (thread-table anyS))
                (current-thread-exists? anyS))
           (equal (current-frame (pushFrame0 anyFrame anyS))
                  anyFrame)))
                         
(in-theory (disable current-frame))

;;----

(defthm update-obj-monitor-preserve-wff-thread-table-thread-exist-current-th
  (let ((s1 (update-obj-monitor obj-ref m s0)))
    (and (equal (wff-thread-table (thread-table s1))
                (wff-thread-table (thread-table s0)))
         (iff   (current-thread-exists? s1)
                (current-thread-exists? s0))
         (equal (call-stack-depth s1)
                (call-stack-depth s0))
         (equal (consp (thread-call-stack (thread-by-id x (thread-table s1))))
                (consp (thread-call-stack (thread-by-id x (thread-table s0)))))
         (equal (current-thread s1) 
                (current-thread s0)))))

(in-theory (disable update-obj-monitor))


(defthm thread-by-id-replace-thread-table-entry-not-equal-equal
  (implies (and (not (equal (thread-id old) x))
                (not (equal (thread-id new) x)))
  (equal (thread-by-id x 
            (replace-thread-table-entry old
                                        new 
                                        tt))
         (thread-by-id x tt))))

;; (defthm thread-by-id-replace-thread-table-entry-thread-exists?
;;   (implies (and (not (equal (thread-id old) x))
;;                 (not (equal (thread-id new) x)))
;;   (equal (thread-exists? x
;;             (replace-thread-table-entry old
;;                                         new 
;;                                         tt))
;;          (thread-exists? x tt)))
;;   :hints (("Goal" :in-theory (enable thread-exists?))))

          

;; (defthm current-thread-exists-replace-thread-table-entry
;;   (let* ((th (current-thread s0))
;;          (tt (thread-table s0))
;;          (s1 (make-state pc th hp
;;                          (replace-thread-table-entry 
;;                           (thread-by-id id tt)
;;                           (make-thread id anySavePC anyCallStack anyState
;;                                       anyMonitorRef anyMonitorDepth
;;                                       anyThreadRef)
;;                           tt)
;;                         cl env ef aux)))
;;     (implies (and (not (equal th id))
;;                   (wff-thread-table-strong1 tt)
;;                   (thread-exists? id tt))
;;              (equal (current-thread-exists? s1)
;;                     (current-thread-exists? s0))))
;;   :hints (("Goal" :in-theory (enable current-thread-exists?))))



(defthm resume-thread-preserve-wff-thread-table-thread-exist-current-th
  (let ((s1 (resumeThread id s0)))
    (and (equal (wff-thread-table (thread-table s1))
                (wff-thread-table (thread-table s0)))
         (iff   (current-thread-exists? s1)
                (current-thread-exists? s0))
         (equal (call-stack-depth s1)
                (call-stack-depth s0))
         (equal (consp (thread-call-stack (thread-by-id x (thread-table s1))))
                (consp (thread-call-stack (thread-by-id x (thread-table s0)))))
         (equal (current-thread s1) 
                (current-thread s0))))
  :hints (("Goal" :cases ((equal x id)))))


(in-theory (disable resumeThread))


(in-theory (disable make-monitor dequeue-h OBJ-MONITOR-BY-REF mqueue))

(defthm removeMonitorWait-preserve-wff-thread-table-thread-exist-current-th
  (let ((s1 (removeMonitorWait obj-ref s0)))
    (and (equal (wff-thread-table (thread-table s1))
                (wff-thread-table (thread-table s0)))
         (iff   (current-thread-exists? s1)
                (current-thread-exists? s0))
         (equal (call-stack-depth s1)
                (call-stack-depth s0))
         (equal (consp (thread-call-stack (thread-by-id x (thread-table s1))))
                (consp (thread-call-stack (thread-by-id x (thread-table s0)))))
         (equal (current-thread s1) 
                (current-thread s0))))
  :hints (("Goal" :cases ((equal x (DEQUEUE-H (MQUEUE (OBJ-MONITOR-BY-REF OBJ-REF S0))))))))


(in-theory (disable removeMonitorWait))



(defthm monitorExit-preserve-wff-thread-table-thread-exist-current-th
   (mv-let (status exception-type s1)
           (monitorExit any-obj-ref s0)
           (declare (ignore status exception-type))
           (and (equal (wff-thread-table (thread-table s1))
                       (wff-thread-table (thread-table s0)))
                (iff   (current-thread-exists? s1)
                       (current-thread-exists? s0))
                (equal (call-stack-depth s1)
                       (call-stack-depth s0))
                (equal (consp (thread-call-stack (thread-by-id x (thread-table s1))))
                       (consp (thread-call-stack (thread-by-id x (thread-table s0)))))
                (equal (current-thread s1) 
                       (current-thread s0)))))


(in-theory (disable monitorExit))


;; (defthm wff-call-frame-make-frame
;;   (wff-call-frame (make-frame rpc os lc mp sf)))

;;; not true. in the current Mon Dec 29 23:28:55 2003 wff-call-frame we also
;;; assert wff-formed method-ptr

(in-theory (disable make-frame return-pc operand-stack locals method-ptr sync-obj-ref))


(defthm sync-obj-ref-frame-set-sync
  (equal (sync-obj-ref (frame-set-sync-obj-ref x frame))
         x))

(in-theory (disable frame-set-sync-obj-ref))


(defthm lemma-admission 
  (implies (and  (WFF-THREAD-TABLE (THREAD-TABLE S))
                 (NOT (EQUAL (current-thread s) -1))
                 (CURRENT-THREAD-EXISTS? S)
                 (CONSP (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                            (THREAD-TABLE S)))))
           (EQUAL
            (CALL-STACK-DEPTH
             (PUSHFRAME0
              (FRAME-SET-SYNC-OBJ-REF -1 (CURRENT-FRAME S))
              (POPFRAME (MV-NTH 2
                                (MONITOREXIT (SYNC-OBJ-REF (CURRENT-FRAME S))
                                             S)))))
            (CALL-STACK-DEPTH S)))
  :hints (("Goal" :in-theory (disable call-stack-depth))))





(defmacro m6assert (s cond msg &rest action)
  `(if (not ,cond)
       (fatalError ,msg ,s)
     ,@action))


(defmacro m6assert2 (s cond msg &rest action)
  `(if (not ,cond)
       (mv nil (fatalError ,msg ,s))
           ,@action))


(defun invariant-exception-handling-1 (s)
  (and (wff-thread-table (thread-table s))
       (current-thread-exists? s)
       (not (equal (current-thread s) -1))
       (not (endp (thread-call-stack (thread-by-id (current-thread s)
                                                   (thread-table s)))))))


(defun invariant-exception-handling-2 (s)
  (and (wff-thread-table (thread-table s))
       (current-thread-exists? s)
       (not (equal (current-thread s) -1))))




;; however this invariant is not true when we allow unwinding across the custom
;; code.
(defun release-lock-invariant (s1 s0)
  (and (equal (wff-thread-table (thread-table s1))
              (wff-thread-table (thread-table s0)))
       (iff   (current-thread-exists? s1)
              (current-thread-exists? s0))
       (equal (call-stack-depth s1)
              (call-stack-depth s0))
       (equal (consp (thread-call-stack (thread-by-id (current-thread s1) (thread-table s1))))
              (consp (thread-call-stack (thread-by-id (current-thread s0) (thread-table s0)))))
       (equal (current-thread s1) 
              (current-thread s0))))









(in-theory (disable call-stack-depth))

(in-theory (disable  method-code code-handlers instance-class-table
                     DEREF-METHOD current-method-ptr))


(defthm current-frame-pushFrame0-thread-exists
  (implies (and  (current-thread-exists? s)
                 (wff-thread-table (thread-table s)))
           (equal (current-frame (pushFrame0 frame s))
                  frame))
  :hints (("Goal" :in-theory (enable pushFrame0 current-frame current-thread-exists?))))

(defthm current-thread-exists?-pushFrame
  (implies (and (current-thread-exists? s)
                (wff-thread-table (thread-table s)))
           (current-thread-exists? (pushFrame0 any s)))
  :hints (("Goal" :in-theory (enable pushFrame0 current-thread-exists?))))

(defthm current-thread-exists?-popFrame
  (implies (and (current-thread-exists? s)
                (wff-thread-table (thread-table s)))
           (current-thread-exists? (popFrame s)))
  :hints (("Goal" :in-theory (enable popFrame current-thread-exists?))))




(in-theory (enable frame-set-sync-obj-ref))
(in-theory (disable current-thread-exists?))





(acl2::mutual-recursion  
 (defun release-lock-on-sync-obj (s)
  (declare (xargs :measure (exception-measure 1 s)))
  ;; guard section. 
  (m6assert2 s (invariant-exception-handling-1 s) 
             "release-lock-on-sync-obj violates invariante" 
             (let* ((current-frame (current-frame s))
                    (sync-obj-ref (sync-obj-ref current-frame)))
               (if (equal sync-obj-ref -1)
                   (mv nil s)
                 (mv-let (status exception-type s1)
                         (monitorExit sync-obj-ref s)
                         (if (equal status 'MonitorStatusError)
                             (mv t (raise-exception exception-type 
                                                    (pushFrame0 
                                                     (frame-set-sync-obj-ref -1 current-frame)
                                                     (popFrame s1))))
                           (mv nil s1)))))))
                 

;; in cldc there is no finally block. preverify have removed the jsr
;; instruction by copying the finally block to the both normal execution path
;; and exception execution path. 

(defun throw-exception1 (obj-ref s) 
  (declare (xargs :measure (exception-measure 2 s)))
  (m6assert s (invariant-exception-handling-2 s) 
            "throw-exception invariant violated"
  (let* ((tid (current-thread s))
         (curthread (thread-by-id tid (thread-table s)))
         (call-stack (thread-call-stack curthread)))
    (if (endp call-stack) ;; no more call frames, uncaught exception.
        (throw-exception2 obj-ref s)
      (let* ((method-ptr (current-method-ptr s))
             (cur-method (deref-method method-ptr 
                                       (instance-class-table s)))
             (exception-type (obj-type (deref obj-ref (heap s))))
             (ip-offset  (pc s))
             (handlers   (code-handlers (method-code cur-method))))
        (if (equal handlers nil)
            (if (equal method-ptr (RunCustomCode-Method-ptr))
                ;; handle exception if exception is raised within a internal
                ;; function call. define a way how to propogate the exception
                ;; across the custom-code. (custom code may call many java
                ;; mehtods and the java method may raise exception and not
                ;; catching them.
                
                ;; trival implementation now, not  clear at all to myself now. 

                (prog2$ 
                 (acl2::debug-print
                          "trying to unwind past a customcode callframe!~%Stack Trace:~p0~%~%"
                           (thread-call-stack (thread-by-id (current-thread s) (thread-table s))))
                 (fatalError "trying to unwind past a customcode --not implemented yet" s))

              (mv-let (return-directly s1)
                      (release-lock-on-sync-obj  s);; strange?? 
                      (m6assert s1 (release-lock-invariant s1 s) 
                                "should always be true release-lock-invariant"
                                (if return-directly 
                                    s1
                                  ;; BEFORE we can pop frame, we need to release the monitor if necessary. 
                                  (throw-exception1 obj-ref (popFrame s1))))))
          (mv-let (thehandler s1)
                  (find-handler handlers exception-type ip-offset s)
                  (prog2$ (acl2::debug-print 
                           "exception ~p0 is thrown~% find handler ~p1 in current frame!~%" 
                           exception-type thehandler)
                  (if (not (no-fatal-error? s1))
                      s1
                    (if (not (equal  theHandler nil))
                      ;; fake a frame and call exception handler.
                      (let* ((old-frame (current-frame s1))
                             (new-frame (frame-set-operand-stack
                                         (list obj-ref)
                                         old-frame)))
                        (mv-let (return-directly s2)
                                (release-lock-on-sync-obj s1)
                                (m6assert s1 (release-lock-invariant s2 s1) 
                                          "should always be true release-lock-invariant"
                                          (if (not (no-fatal-error? s2))
                                              s2
                                            (if return-directly 
                                                s2
                                              (state-set-pc (handler-entry-point theHandler)
                                                            (pushFrame0 new-frame 
                                                                        (popFrame s2))))))))
                      
                      (mv-let (return-directly s2)
                              (release-lock-on-sync-obj s1)
                              (m6assert s1 (release-lock-invariant s2 s1) 
                                        "should always be true release-lock-invariant"
                              (if (not (no-fatal-error? s2))
                                  s2
                                (if return-directly 
                                    s2
                                  (throw-exception1 obj-ref 
                                                    (popFrame s2))))))))))))))))
                
                
;; precondition is obj-ref is always a throwable_instance.      

(defun throw-exception (obj-ref s)
  (declare (xargs :measure (exception-measure 3 s)))
  (let* ((current-thread (current-thread s)))
    (if (equal current-thread -1)
        (let ((msg-str-ref (getExceptionMessage obj-ref s)))
          (if (equal msg-str-ref -1)
              (ERROR_THROW -1 s)
            (fatalError (JavaString-to-ACL2-str msg-str-ref s) s)))
      (throw-exception1 obj-ref s)))) ;; unroll call frames and fake call frames
                                   ;; to handle exception?
       

         
;; the assumption is that "java.lang.Throwable" is loaded.
(defun raise-exception1 (classname s)
  (declare (xargs :measure (exception-measure 4 s)))
  (mv-let (new-addr s1)
          (new-instance classname s)
          (throw-exception new-addr s1)))

;;
;; in our implementation no-fatal-error? will ensure the class is loaded. 
;; we will prove this property. 
;; class not found will be a fatalError.
;; 

(defun raise-exception (classname s)
  (declare (xargs :measure (exception-measure 5 s)))
  (let ((s1 (getClass classname s)))
    (if (no-fatal-error? s1)
        (raise-exception1 classname s1)
      (alertUser 
       "raise-excecption: fatalError ocurred in getClass, can't find exception class indicated." 
       s1)))))























