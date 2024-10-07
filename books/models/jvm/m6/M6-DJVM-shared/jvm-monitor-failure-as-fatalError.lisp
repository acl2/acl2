(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-obj")
(include-book "../M6-DJVM-shared/jvm-monitor-primitives")
(include-book "../M6-DJVM-shared/jvm-state")


;; (mv * *)
(defun monitorNotifyX (obj-ref notifymode s)
  (let* ((old-heap (heap s))
         (old-obj (deref obj-ref old-heap))
         (old-common-info (common-info old-obj))
         (old-monitor (monitor old-common-info))
         (owner       (owner old-monitor)))
    (if (not (equal owner (current-thread s))) ;; not owner by current
        (mv 'MonitorStatusError (fatalError
                                 "java.lang.IllegalMonitorStateException" s))
      (mv 'MonitorStatusOwn (removeCondvarWait obj-ref notifymode s)))))


;; (mv * *)
(defun classMonitorNotifyX (classname notifymode s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (monitorNotifyX class-ref notifymode s))) ;; 2 values status bit, return state.


;; (mv * * *)
(defun monitorExitX (obj-ref s)
  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (if (not (equal (owner monitor) (current-thread s)))
        (mv 'MonitorStatusError  "java.lang.IllegalMonitorStateException" s)
      (let* ((new-monitor (monitor-set-depth (- (depth monitor) 1)
                                             monitor))
             (new-state (update-obj-monitor obj-ref new-monitor s)))
        (if (equal (depth new-monitor) 0)
            (mv 'MonitorStatusRelease nil (removeMonitorWait obj-ref new-state))
          (mv 'MonitorStatusOwn nil new-state))))))
          

;; (mv * * *)
(defun classMonitorExitX (classname s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (monitorExitX class-ref s))) ;; monitor exit return status bit, exception
                                ;; name, state three items. 


;; (mv * *)
(defun monitorEnterX (obj-ref s)
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
  

  
(defun classMonitorEnterX (classname s)
  (prog2$ (acl2::debug-print "try entering monitor associated with class ~p0~%" classname)
          (let* ((class-rep (class-by-name classname (instance-class-table s)))
                 (class-ref (class-ref class-rep)))
            (monitorEnterX class-ref s))))
  
         
                          

;; we couldn't implement alarm... july 13 2002

;; (mv * *)


(defun monitorWait1X (obj-ref s)
  (mv 'MonitorStatusWaiting 
      (suspendThread (addCondvarWait obj-ref (current-thread s) s))))
  


(defun monitorWaitX (obj-ref duration s)
  (let ((monitor (obj-monitor-by-ref obj-ref s)))
    (if (not (equal (owner monitor) (current-thread s)))
        (mv 'MonitorStatusError 
            (fatalError "java.lang.IllegalMonitorStateException" s))
      (if (> duration 0)
          (monitorWait1X obj-ref (registerAlarm (current-thread s) duration 'monitorWaitAlarm))
        ;; register a call back function, when alarm is on, call the call back function.
        (monitorWait1X obj-ref s)))))


;; * 
;; don't care the monitor status error
(defun classMonitorWaitX (classname s)
  (let* ((class-rep (class-by-name classname (instance-class-table s)))
         (class-ref (class-ref class-rep)))
    (mv-let (mstatus new-s)
            (monitorWaitX class-ref 0 s)
            (declare (ignore mstatus))
            new-s)))






