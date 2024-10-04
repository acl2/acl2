(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-obj")
(include-book "../M6-DJVM-shared/jvm-thread")
(include-book "../M6-DJVM-shared/jvm-thread-primitives")


;; temp implementation
;; have implement the clock..
(defun removePendingAlarm (waiter s)
  (declare (ignore waiter))
  s)


(defun registerAlarm (waiter duration s)
  (declare (ignore waiter duration))
  s)

;###



;; lookup the waiting queue of the monitor associated with this class
;; remove those thread from the queue, set thread state back to active. 
;;
;; in our model monitor always exists, 
;; while the ready queue of the system doesn't really exist.
;; 
;; in principle we could maintain all the monitors in a separate list but here
;; we keep the monitor fields in the heap object themselfs.  so any
;; modification of the monitor, in ACL2 we need to create an new object and
;; bind the new object to the same address.


;; isn't it an invariant that all the thread on the mqueue has depth 1?
;; no, it is not true. Because a thread can relinquish the lock on monitor when
;; it start waiting on the conditional variable (cqueue). 

(defun dequeue-h (queue)
  (car queue))
(defun dequeue-r (queue)
  (cdr queue))

(defun obj-monitor-by-ref (obj-ref s)
  (obj-monitor (deref obj-ref (heap s))))

(defun update-obj-monitor (obj-ref m s)
  (let* ((old-heap (heap s))
         (old-obj  (deref obj-ref old-heap))
         (old-common-info (common-info old-obj))
         (new-common-info (common-info-set-monitor m old-common-info))
         (new-obj (obj-set-common-info new-common-info old-obj))
         (new-heap (bind obj-ref new-obj old-heap)))
    (state-set-heap new-heap 
                    s)))

(defun removeMonitorWait-inv (waiter-id s)
  (and (thread-exists? waiter-id (thread-table s))
       (not (equal waiter-id (current-thread s)))
       (wff-thread-table (thread-table s))))




(defun removeMonitorWait (obj-ref s)
  (let* ((m   (obj-monitor-by-ref obj-ref s))
         (mqueue (mqueue m)))
    (if (endp mqueue)
        (let ((new-m (make-monitor -1 ;; no one want
                                   0 
                                   nil
                                   (cqueue m))))
          ;; however some one may be waiting for the condtional variable.
              (update-obj-monitor obj-ref new-m s))
      (let* ((waiter-id (dequeue-h mqueue))
             (old-thread-table (thread-table s))
             (old-thread  (thread-by-id waiter-id old-thread-table))
             (new-m  (make-monitor waiter-id
                                   (thread-mdepth old-thread)
                                   (dequeue-r mqueue)
                                   (cqueue m)))
             (new-thread (thread-set-mref -1  ;; release the monitor
                            (thread-set-mdepth 0 old-thread)))
             (new-thread-table 
                (replace-thread-table-entry old-thread new-thread
                                            old-thread-table)))
        (if (not (removeMonitorWait-inv waiter-id s))
            (fatalError "removeMonitorWait-inv violated" s)
        (update-obj-monitor obj-ref new-m
                            (resumeThread waiter-id (state-set-thread-table new-thread-table s))))))))

;; notice here we didn't really change the monitor that is in the heap.
;; we need to rely on the the caller to take the new monitor returned and set
;; update the monitor fields of the corresponding object.
;; this is internal method. user interface is monitorNotify, ...


;; I didn't see any reason to keep track which monitor the thread is waiting
;; on. except for debug purpose or garbarge collection.
;; why ??? 
;; it is used for timer call back ....

(defun add-to-queue-end (item queue)
  (app queue (list item)))

(defun addMonitorWait (waiter obj-ref s)
  (mylet* ((monitor (obj-monitor-by-ref obj-ref s))
         (old-thread-table (thread-table s))
         (old-thread  (thread-by-id waiter old-thread-table))
         (mqueue      (mqueue monitor))
         (new-mqueue  (add-to-queue-end waiter mqueue))
         (new-thread  (thread-set-mref obj-ref 
                       (set-thread-state-flag 'thread_monitor_wait old-thread)))
         (new-monitor (monitor-set-mqueue new-mqueue monitor))
         (new-thread-table (replace-thread-table-entry 
                            old-thread new-thread old-thread-table))
         (new-state (update-obj-monitor obj-ref new-monitor 
                                        (state-set-thread-table new-thread-table s))))
    (if (equal (owner new-monitor) -1) ;; nobody is holding the thread
        (removeMonitorWait obj-ref  new-state)
      new-state)))


(defun removeCondvarWait2 (waiter obj-ref s)
  (addMonitorWait waiter obj-ref
                  (removePendingAlarm waiter s)))
    
(defun removeCondvarWait1 (queue obj-ref s)
  (if (endp queue)
      (let* ((monitor (obj-monitor-by-ref obj-ref s))
             (new-monitor (monitor-set-cqueue nil monitor))
             (new-state (update-obj-monitor obj-ref new-monitor s)))
        new-state)
    (removeCondvarWait1 (cdr queue) obj-ref
                        (removeCondvarWait2 (car queue) obj-ref s))))


(defun removeCondvarWait (obj-ref notifymode s)
  (let* ((monitor (obj-monitor-by-ref obj-ref s))
         (cqueue  (cqueue monitor)))
    (if (endp cqueue)
        s
      (if (not (equal notifymode 'ALL))
          (let* ((new-monitor 
                  (monitor-set-cqueue (dequeue-r cqueue) monitor))
                 (new-state (update-obj-monitor obj-ref new-monitor s)))
               (removeCondvarWait2 (dequeue-h cqueue) obj-ref new-state))
        (removeCondvarWait1 cqueue obj-ref s)))))


         
                          

(defun addCondvarWait (obj-ref tid s)
  (let* ((monitor (obj-monitor-by-ref obj-ref s))
         (owner   (owner monitor))
         (cqueue  (cqueue monitor)))
    (if (not (equal tid owner))
        (fatalError "bad-call-to-addCondVarWait" s);
      (let* ((new-monitor (monitor-set-cqueue 
                            (add-to-queue-end tid cqueue)
                            monitor))
             (old-thread-table (thread-table s))
             (old-thread (thread-by-id tid old-thread-table))
             (new-thread (thread-set-mdepth (depth monitor)
                                            (set-thread-state-flag 
                                             'thread_convar_wait
                                             (thread-set-mref obj-ref
                                                              old-thread))))
             (new-thread-table (replace-thread-table-entry old-thread
                                                           new-thread
                                                           old-thread-table))
             (new-state (state-set-thread-table new-thread-table 
                              (update-obj-monitor  obj-ref new-monitor s))))
        (removeMonitorWait obj-ref new-state)))))
             
             
             

