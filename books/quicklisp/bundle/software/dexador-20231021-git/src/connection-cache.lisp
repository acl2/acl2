(in-package :cl-user)
(defpackage dexador.connection-cache
  (:use :cl)
  (:import-from :bordeaux-threads
                :make-lock
                :with-lock-held)
  (:export :*connection-pool*
   :*use-connection-pool*
           :*max-active-connections*
           :make-connection-pool
           :steal-connection
           :push-connection
           :clear-connection-pool))
(in-package :dexador.connection-cache)

(defvar *use-connection-pool* t)
(defvar *max-active-connections* 8
  "Allowed number of active connections to all hosts.  If you change this,
  then call (make-new-connection-pool).")

(defstruct lru-pool-elt
  (prev nil :type (or null lru-pool-elt))
  (next nil :type (or null lru-pool-elt))
  (elt nil :type t)
  (key nil :type t)
  (eviction-callback nil :type (or null function)))

;; An LRU-POOL can have multiple entries for the same key
(defstruct lru-pool
  (lock #+thread-support (bt2:make-lock :name "connection pool lock")
        #-thread-support nil)
  (hash-table nil :type (or null hash-table)) ;; hash table entries are lists of elements
  (head nil :type (or null lru-pool-elt)) ;; most recently used is here and it's a doubly-linked-list
  (tail nil :type (or null lru-pool-elt)) ;; least recently used is here
  (num-elts 0 :type fixnum)
  (max-elts 8 :type fixnum))

(defun make-connection-pool (&optional (max-active-connections *max-active-connections*))
  (make-lru-pool :hash-table (make-hash-table :test 'equal) :max-elts max-active-connections))

(defvar *connection-pool* nil)

(defun make-new-connection-pool (&optional (max-active-connections *max-active-connections*))
  (clear-connection-pool)
  (setf *connection-pool* (make-connection-pool max-active-connections)))

(defun get-from-lru-pool (lru-pool key)
  "Takes an element from the LRU-POOL matching KEY.  Must be called with LRU-POOL-LOCK held.
   The element is removed from the pool."
  (let* ((hash-table (lru-pool-hash-table lru-pool))
         (possible-elts (gethash key (lru-pool-hash-table lru-pool))))
    (when possible-elts
      (let ((remaining-elts (cdr possible-elts)))
        (if remaining-elts
            (setf (gethash key hash-table) remaining-elts)
            (remhash key hash-table)))
      (let ((elt (car possible-elts)))
        (let ((prev (lru-pool-elt-prev elt))
              (next (lru-pool-elt-next elt)))
          (if prev
              (setf (lru-pool-elt-next prev) next)
              (setf (lru-pool-head lru-pool) next))
          (if next
              (setf (lru-pool-elt-prev next) prev)
              (setf (lru-pool-tail lru-pool) prev)))
        (decf (lru-pool-num-elts lru-pool))
        (lru-pool-elt-elt elt)))))

(defun evict-tail (lru-pool)
  "Removes the least recently used element of the LRU-POOL and returns
    (values evicted-element eviction-callback t) if there was
   an element to remove, otherwise nil.  Must be called with LRU-POOL-LOCK held.

   Outside the LRU-POOL-LOCK you must call the returned EVICTION-CALLBACK with the EVICTED-ELEMENT."
  ;; slightly different from get-from-lru-pool because we want to get rid of the
  ;; actual oldest element (one could in principle call get-from-lru-pool on
  ;; (lru-pool-elt-key (lru-pool-tail lru-pool)) if you didn't care
  (let* ((tail (lru-pool-tail lru-pool)))
    (when tail
      (let ((prev (lru-pool-elt-prev tail)))
        (if prev
            (setf (lru-pool-elt-next prev) nil)
            (setf (lru-pool-head lru-pool) nil))
        (setf (lru-pool-tail lru-pool) prev)
        (let* ((hash-table (lru-pool-hash-table lru-pool))
               (key (lru-pool-elt-key tail))
               (remaining (delete tail (gethash key hash-table))))
          (if remaining
              (setf (gethash key hash-table) remaining)
              (remhash key hash-table))))
      (decf (lru-pool-num-elts lru-pool))
      (values (lru-pool-elt-elt tail) (lru-pool-elt-eviction-callback tail) t))))

(defun add-to-lru-pool (lru-pool key elt eviction-callback)
  "Adds ELT to an LRU-POOL with potentially non-unique KEY, potentially evicting another element to
   make room.  EVICTION-CALLBACK will be called with one parameter ELT, when ELT is evicted from the
   LRU-POOL.  ADD-TO-LRU-POOL must be called with LRU-POOL-LOCK held.

   If an element was evicted to make space, returns (values evicted-elt eviction-callback t)
   otherwise nil.  The EVICTION-CALLBACK should take one parameter, the evicted element."
  (declare (type lru-pool lru-pool))
  (let* ((old-head (lru-pool-head lru-pool))
         (lru-pool-elt (make-lru-pool-elt :prev nil :next old-head :elt elt :key key :eviction-callback eviction-callback))
         (hash-table (lru-pool-hash-table lru-pool)))
    (setf (lru-pool-head lru-pool) lru-pool-elt)
    (push lru-pool-elt (gethash key hash-table))
    (when old-head
      (setf (lru-pool-elt-prev old-head) lru-pool-elt))
    (unless (lru-pool-tail lru-pool)
      (setf (lru-pool-tail lru-pool) lru-pool-elt))
    (when (> (incf (lru-pool-num-elts lru-pool)) (lru-pool-max-elts lru-pool))
      (evict-tail lru-pool))))

(defmethod print-object ((obj lru-pool-elt) str) ;; avoid printing loops
  (print-unreadable-object (obj str :type "LRU-POOL-ELT")
    (format str "~A NEXT ~A" (lru-pool-elt-key obj) (lru-pool-elt-next obj))))

(defmethod print-object ((obj lru-pool) str) ;; avoid printing loops
  (print-unreadable-object (obj str :type "LRU-POOL")
    (let (objs)
      (loop with lru-pool-elt = (lru-pool-head obj)
            while lru-pool-elt
            do (push (list (lru-pool-elt-key lru-pool-elt) (lru-pool-elt-elt lru-pool-elt)) objs)
            do (setf lru-pool-elt (lru-pool-elt-next lru-pool-elt)))
      (if objs
          (format str "~A/~A elts~%~{ ~{~A~^: ~}~^~%~}" (lru-pool-num-elts obj) (lru-pool-max-elts obj) objs)
          (format str "empty")))))

(defmacro with-lock (lock &body body)
  (declare (ignorable lock))
  #+thread-support `(bt2:with-lock-held (,lock)
                      ,@body)
  #-thread-support `(progn ,@body))

(defun push-connection (host-port stream &optional eviction-callback)
  "Add STREAM back to connection pool with key HOST-PORT.  EVICTION-CALLBACK
   must be a function of a single parameter, and will be called with STREAM
   if the HOST-PORT/SOCKET pair is evicted from the connection pool."
  (when *use-connection-pool*
    (let ((pool *connection-pool*))
      (multiple-value-bind (evicted-elt eviction-callback)
          (with-lock (lru-pool-lock pool)
            (add-to-lru-pool pool host-port stream eviction-callback))
        (and eviction-callback (funcall eviction-callback evicted-elt))
        (values)))))

(defun steal-connection (host-port)
  "Return the STREAM associated with key HOST-PORT"
  (when *use-connection-pool*
    (let ((pool *connection-pool*))
      (with-lock (lru-pool-lock pool)
        (get-from-lru-pool pool host-port)))))

(defun clear-connection-pool ()
  "Remove all elements from the connection pool, calling their eviction-callbacks."
  (when *use-connection-pool*
    (let ((pool *connection-pool*)
          evicted-element eviction-callback element-was-evicted)
      (when pool
        (loop for count from 0
              do (setf (values evicted-element eviction-callback element-was-evicted)
                       (with-lock (lru-pool-lock pool)
                         (evict-tail pool)))
              do (when eviction-callback (funcall eviction-callback evicted-element))
              while element-was-evicted)))))

(make-new-connection-pool)
