(in-package "M6")
(include-book "../M6/m6-state")
(include-book "../M6/m6-class-table")
(include-book "../M6/m6-verifier")
(include-book "../M6/m6-frame-manipulation-primitives")
(include-book "../M6/m6-linker")
(include-book "../M6/m6-monitor-failure-as-fatalError")

;; assume class is loaded 
;;
;; need to hijack the class initialization of java.lang.System? 
;; or make every method in it Native??
;; thus no complicated initialization .
;; chose to latter. easier.
;;
;; need to dealing with IO, add more entry into the ENV
;; 
(defun initializeClass1 (classname s)
  (let ((class-rep (class-by-name classname (instance-class-table s))))
    (if (class-rep-in-error-state? class-rep) ;; loading error may exists, 
        s  ;; loading error should set the flag to be class_error.
      (if (not (class-rep-verified? class-rep))
          (let ((new-state (verify-class class-rep s)))
            (if (not (no-fatal-error? new-state))
                new-state
              ;; fake a call to Class.runCustomCode to invoke runClinit
              (let* ((s1 (pushFrame (RunCustomCode-method-ptr) nil new-state))
                     (s2 (pushStack (make-callback-func-ptr '*runClinit*) s1))
                     (s3 (pushStack 1 s2)))
                s3)))
        (let* ((s1 (pushFrame (RunCustomCode-method-ptr) nil s))
               (s2 (pushStack (make-callback-func-ptr '*runClinit*) s1))
               (s3 (pushStack classname s2))
               (s4 (pushStack 1 s3)))
          s4)))))


;; if anything went wrong with load_class, class-rep should be in an
;; error-state.
(defun initializeClass (classname s)
  (if (class-loaded? classname s)
      (initializeClass1 classname s)
    (initializeClass1 classname (load_class classname s))))


(defun runClinit6 (classname s)
  (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 6)
  (let* ((s1 (setClassInitialThread classname -1 s));; indicate no thread is
                                                    ;; initializing the object
        (s2 (setClassStatus classname 'class_ready s1)))
    (mv-let  (mstatus s3)
             (classMonitorNotifyX classname 'ALL s2)
             (declare (ignore mstatus))
             (mv-let (monitorStatus exception-name s4)
                     (classMonitorExitX classname s3)
                     (declare (ignore monitorStatus exception-name))
                     (popFrame s4))))))  ;; KVM doesn't implement this correctly.

;; popFrame. 

;; If exception is thrown, then it is not handled as described in the JVM
;; specification 2.17.5 (10-11) but the class will be in an error state, we
;; will detect it through this.


(defun set-clinit-stage (th stage s)
  (let ((cid (current-thread s)))
    (state-set-current-thread 
       cid 
       (pushStack stage (popStack (state-set-current-thread th s))))))                  

;; "don't" means that "we chose not to" 

;; don't implement the short cut, always grab the monitor.
(defun runClinit5 (classname s)
  (let ((cid (current-thread s)))
    (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 5)
            (mv-let (mstatus new-s)
                    (classMonitorEnterX classname s)
                    (if (not (equal mstatus 'JVM::MonitorStatusOwn))
                        (set-clinit-stage cid 6 new-s)
                      (runClinit6 classname new-s))))))

;; don't deal with resource limitations.

(defun runClinit4 (classname s)
  (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 4)
  (let* ((clinitMethod-ptr (clinitMethod-ptr classname))
         (thisMethod       (getSpecialMethod clinitMethod-ptr s)))
    (if (not (equal thisMethod nil))
        (pushFrame clinitMethod-ptr nil 
                   (set-clinit-stage (current-thread s) 5 s))
      ;; assuming no stack overflow while pushing frame
      (runClinit5 classname s))))) ;; fall through



(defun runClinit3 (classname s)
  (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 3)
   (let ((class-rep (class-by-name classname (instance-class-table s)))
         (cid (current-thread s)))
     (if (not (isInterface class-rep))
         (if (and (super-exists class-rep)
                  (not (class-initialized? (super class-rep) s)))
             (initializeClass (super class-rep) 
                              (set-clinit-stage cid 4 s))
           (runClinit4 classname s))
       (runClinit4 classname s)))))
       

;; in state 2 we always have monitor.
;; invariant current-thread has the monitor.


(defun runClinit2 (classname s)
  (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 2)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (initThread (init-thread-id class-rep))
         (cid (current-thread s)))
    (cond ((and (not (equal initThread -1))
                (not (equal initThread (current-thread s))))
           (let ((new-s (classMonitorWaitX classname s)))
                 ;; yield the monitor and wait, when return has monitor again.
             (set-clinit-stage cid 2 new-s)))
          ((or (equal initThread (current-thread s))
               (class-initialized? classname s))
           (mv-let (mstatus exception-name new-state)
                   (classMonitorExitX classname s)
                   (declare (ignore mstatus exception-name))
                   (popFrame new-state)))
          ((class-rep-in-error-state? class-rep)
           (fatalError "bad-class-state" s))
          (t (let ((s-start-init (setClassInitialThread classname
                                                        (current-thread s) s)))
               (mv-let (mstatus exception-name s-new)
                       (classMonitorExitX classname s-start-init)
                       (declare (ignore mstatus exception-name))
                       (runClinit3 classname s-new))))))))


(defun runClinit1 (classname s)
  (let ((cid (current-thread s)))
    (prog2$ (acl2::debug-print "Class initialization in stage ~p0~%" 1)
            (mv-let (mstatus new-s)
                    (classMonitorEnterX classname s)
                    (if (not (equal mstatus 'MonitorStatusOwn))
                        (set-clinit-stage cid 2 s)
                      (runClinit2 classname new-s))))))



(defun runClinit (s) ;; put up top element to see which stage it is in.
  (let ((st (topStack s))
        (classname (secondStack s)))
    (cond ((equal st  1) (runClinit1 classname s))
          ((equal st 2)  (runClinit2 classname s))
          ((equal st 3)  (runClinit3 classname s))
          ((equal st 4)  (runClinit4 classname s))
          ((equal st 5)  (runClinit5 classname s))
          ((equal st 6)  (runClinit5 classname s))
          (t (fatalError "static-initializer-failed" s)))))







