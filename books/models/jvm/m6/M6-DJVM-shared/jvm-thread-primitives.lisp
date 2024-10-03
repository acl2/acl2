(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-thread")

(acl2::set-verify-guards-eagerness 0)
;; still need to deai with this guard verification sometime. Wed Dec 24
;; 23:41:30 2003

;;;
;;; Tue Jan 13 15:01:05 2004 NOT NOW: currently I am focusing on define a
;;; consistent-state. the guard of consistent-state must be T.
;;;
;;; We plan to use consistent-state as the guard of INSTRUCTIONS!!
;;; 
;;; By showing guard are not violated, we also show more. (guard verify!)
;;; 

;##### this few are primitives tmp inplementation

(defun signalTimeToReschedule (s) 
  s)

(defun dismantleThread (tid s)
  (declare (ignore tid))
  s)


;***************************
;; Resume thread 

;; invariant 
(defun resumeThread-inv (id s)
  (and (wff-thread-table (thread-table s))
       (thread-exists? id (thread-table s))))



(defun resumeThread (id s) 
  (let* ((old-thread-table (thread-table s))
         (old-thread       (thread-by-id id old-thread-table))
         (old-thread-state (thread-state old-thread)))
    (if (not (resumeThread-inv id s))
        (fatalError "resumeThread violate internal invariant" s)
      (if (not (mem 'thread_suspended old-thread-state))
          (fatalError "try to resume a thread that is not suspended before" s) 
        (let* ((new-thread-state '(thread_active)) ;; remove all previous flags.
               (new-thread (thread-set-state new-thread-state old-thread))
               (new-thread-table 
                (replace-thread-table-entry old-thread new-thread
                                            old-thread-table))
               (new-state (state-set-thread-table new-thread-table s)))
          (if (equal (current-thread s) id)
              ;; resuming itself?? 
              (fatalError "attempting to resuming itself" s)
            new-state))))))
        ;; we don't have a RunableThread queue, instead we run according to a
        ;; external schedule. A thread_active flag is good enough.
        ;; shall we? we can always search through the thread table to find
        ;; which threads are active, thus runable.  

;; let's treat error happened at this stage, as internal m6 implementation
;; error.  someone calls start(), or resume(), the code there should check if
;; that thread is resumable or not and throw appropriate exception. We can't
;; rely on this resumeThread to throw appropriate exception.


(defun storeExecutionEnvironment (s)
  (let* ((tid        (current-thread s))
         (old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (new-thread (thread-set-saved-pc (pc s)
                                          old-thread))
         ;; in our representation only pc need to be saved
         (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                       old-thread-table)))
    (state-set-thread-table new-thread-table s)))

(defun loadExecutionEnvironment (tid s)
  (let* ((thread-table (thread-table s))
         (thread (thread-by-id tid thread-table))
         ;; only need to restore the pc value
         (pc     (thread-saved-pc thread)))
    (state-set-current-thread tid (state-set-pc pc s))))


(defun suspendThread1 (s)
  (let* ((tid        (current-thread s))
         (old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (new-thread (set-thread-state-flag 'JVM::thread_suspended  old-thread))
         (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                       old-thread-table)))
    (state-set-current-thread -1 (state-set-thread-table new-thread-table s))))


;; in our representation of thread, 
(defun suspendThread (s) ;; always gsuspends the current running thread.
  (let* ((tid        (current-thread s))
         (old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (old-thread-state (thread-state old-thread)))
    (if (not (mem 'JVM::thread_suspended old-thread-state))
        (suspendThread1 (signalTimeToReschedule  
                         (storeExecutionEnvironment s)))
                          
      (suspendThread1 s))))

(defun startThread (tid s)
  (let* ((old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (new-thread (thread-set-state '(JVM::thread_suspended) old-thread))
         (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                       old-thread-table)))
    (state-set-thread-table new-thread-table s)))
         
(defun stopThread (s)
  (let* ((tid (current-thread s))
         (old-thread-table (thread-table s))
         (old-thread (thread-by-id tid old-thread-table))
         (new-thread (thread-set-state '(thread_dead) old-thread))
         (new-thread-table (replace-thread-table-entry old-thread new-thread
                                                       old-thread-table))
         (s1  (suspendThread s))
         (s2  (state-set-thread-table new-thread-table s1))
         ;;(s3  (state-set-current-thread -1 s2))
         ;;(s3  (state-set-current-thread -1 s2))
         (s3  (dismantleThread tid s2)))
    s3))

               
                                                       
    


