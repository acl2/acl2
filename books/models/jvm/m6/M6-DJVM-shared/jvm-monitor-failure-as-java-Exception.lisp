(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-monitor-primitives")
(include-book "../M6-DJVM-shared/jvm-obj")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-exceptions")

;; (mv * *)
(defun monitorNotify (obj-ref notifymode s)
  (let* ((old-heap (heap s))
         (old-obj (deref obj-ref old-heap))
         (old-common-info (common-info old-obj))
         (old-monitor (monitor old-common-info))
         (owner       (owner old-monitor)))
    (if (not (equal owner (current-thread s))) ;; not owner by current
        (mv 'MonitorStatusError (raise-exception "java.lang.IllegalMonitorStateException" s))
      (mv 'MonitorStatusOwn (removeCondvarWait obj-ref notifymode s)))))

;; (mv * *)
(defun classMonitorNotify (classname notifymode s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (monitorNotify class-ref notifymode s))) ;; 2 values status bit, return state.


#|
;; (mv * * *)
(defun monitorExit (obj-ref s)
  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (if (not (equal (owner monitor) (current-thread s)))
        (mv 'MonitorStatusError  "java.lang.IllegalMonitorStateException" s)
      (let* ((new-monitor (monitor-set-depth (- (depth monitor) 1)
                                             monitor))
             (new-state (update-obj-monitor obj-ref new-monitor s)))
        (if (equal (depth new-monitor) 0)
            (mv 'MonitorStatusRelease nil (removeMonitorWait obj-ref new-state))
          (mv 'MonitorStatusOwn nil new-state))))))

;; already defined in jvm-exceptions.lisp
|#          

;; (mv * * *)
(defun classMonitorExit (classname s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (monitorExit class-ref s))) ;; monitor exit return status bit, exception
                                ;; name, state three items. 

;; (mv * *)
(defun monitorEnter (obj-ref s)
  (prog2$ (acl2::debug-print "try entering monitor for obj ~p0~%" obj-ref)

  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (cond ((equal (owner monitor) -1) ;; not owner
           (let ((new-monitor 
                  (monitor-set-depth 1 (monitor-set-owner (current-thread s)
                                                          monitor))))
             (mv 'MonitorStatusOwn
                 (update-obj-monitor obj-ref new-monitor s))))
          ((equal (owner monitor) (current-thread s))
           (let ((new-monitor 
                  (monitor-set-depth (+ (depth monitor) 1) monitor)))
             (mv 'MonitorStatusOwn
                 (update-obj-monitor obj-ref new-monitor s))))
          (t (let* ((old-thread-table (thread-table s))
                    (old-thread (thread-by-id (current-thread s)
                                              old-thread-table))
                    (new-thread (thread-set-mdepth 1 old-thread))
                    (new-thread-table (replace-thread-table-entry old-thread
                                                                  new-thread
                                                                  old-thread-table))
                    (new-state (state-set-thread-table new-thread-table s)))
	    (mv 'MonitorStatusWaiting
                (suspendThread (addMonitorWait (current-thread s) obj-ref
                                               new-state)))))))))
  

(defun classMonitorEnter (classname s)
  (prog2$ (acl2::debug-print "try entering monitor associated with class ~p0~%" classname)
          (let* ((class-rep (class-by-name classname (instance-class-table s)))
                 (class-ref (class-ref class-rep)))
            (monitorEnter class-ref s))))
  
;; Since we didn't implemented timed alarm.
;; we couldn't implement alarm... july 13 2002

;; (mv * *)


(defun monitorWait1 (obj-ref s)
  (mv 'MonitorStatusWaiting 
      (suspendThread (addCondvarWait obj-ref (current-thread s) s))))
  


(defun monitorWait (obj-ref duration s)
  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (if (not (equal (owner monitor) (current-thread s)))
        (mv 'MonitorStatusError 
            (raise-exception "java.lang.IllegalMonitorStateException" s))
      (if (> duration 0)
          (monitorWait1 obj-ref (registerAlarm (current-thread s) duration 'monitorWaitAlarm))
        ;; register a call back function, when alarm is on, call the call back function.
        (monitorWait1 obj-ref s)))))



;; don't care the monitor status error
(defun classMonitorWait (classname s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (mv-let (mstatus new-s)
            (monitorWait class-ref 0 s)
            (declare (ignore mstatus))
            new-s)))





