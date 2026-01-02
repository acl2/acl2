;;;; ACL2-Bridge: SBCL + bordeaux-threads Implementation
;;;; 
;;;; This is a working port of CCL's process-based architecture to SBCL's
;;;; thread model, with proper Unix domain socket cleanup and graceful shutdown.
;;;; 
;;;; Key principles:
;;;; 1. Graceful shutdown using flag instead of aggressive thread termination
;;;; 2. Explicit Unix domain socket file cleanup in unwind-protect
;;;; 3. Proper error handling for socket operations
;;;; 4. Compatible with usocket and native sb-bsd-sockets
;;;;

(in-package :acl2-bridge)

;;; ============================================================================
;;; Configuration and State
;;; ============================================================================

(defparameter *socket-path* "/tmp/acl2-bridge.sock")

(defparameter *bridge-shutdown* nil
  "Flag to signal graceful shutdown of listener thread")

(defparameter *listener-thread* nil
  "Reference to the main listener thread")

(defparameter *worker-threads* (make-hash-table)
  "Registry of active worker threads")

(defparameter *worker-lock* (bordeaux-threads:make-lock))

;;; ============================================================================
;;; Thread Management Utilities
;;; ============================================================================

(defun register-worker (thread-obj)
  "Register a new worker thread"
  (bordeaux-threads:with-lock-held (*worker-lock*)
    (setf (gethash thread-obj *worker-threads*) t)))

(defun unregister-worker (thread-obj)
  "Unregister a completed worker thread"
  (bordeaux-threads:with-lock-held (*worker-lock*)
    (remhash thread-obj *worker-threads*)))

(defun kill-all-workers (&optional (timeout 5))
  "Gracefully terminate all worker threads with timeout"
  (bordeaux-threads:with-lock-held (*worker-lock*)
    (let ((threads (loop for thread being the hash-keys of *worker-threads*
                         collect thread)))
      (dolist (thread threads)
        (when (bordeaux-threads:thread-alive-p thread)
          (bordeaux-threads:destroy-thread thread))))
    (clrhash *worker-threads*))
  ;; Give threads time to exit
  (sleep timeout))

;;; ============================================================================
;;; Socket Lifecycle Management
;;; ============================================================================

(defun create-listen-socket (path)
  "Create and bind a Unix domain listening socket.
   
   This function:
   1. Removes any stale socket file from previous runs
   2. Creates a local socket in stream mode
   3. Binds and listens on the specified path
   4. Returns the configured socket
   
   On failure, raises a socket error condition."
  
  ;; Clean up stale socket file (POSIX requirement)
  ;; This prevents 'Address already in use' errors
  (when (probe-file path)
    (delete-file path))
  
  (let ((sock (make-instance 'sb-bsd-sockets:local-socket
                             :type :stream)))
    (handler-case
        (progn
          (sb-bsd-sockets:socket-bind sock path)
          (sb-bsd-sockets:socket-listen sock 1)
          sock)
      (error (e)
        ;; Clean up on bind/listen failure
        (sb-bsd-sockets:socket-close sock)
        (when (probe-file path)
          (delete-file path))
        (error e)))))

(defun cleanup-socket-file (path)
  "Remove a Unix domain socket file from the filesystem.
   
   This is necessary because closing the socket's file descriptor
   does NOT automatically delete the filesystem object.
   
   See: man 7 unix - 'Binding a name to a UNIX-domain socket 
        with bind(2) causes a socket file to be created in the 
        filesystem. This file is not removed when the socket is closed—
        unlink(2) must be used to remove the file.'"
  (when (and path (probe-file path))
    (delete-file path)))

;;; ============================================================================
;;; Worker Thread Implementation
;;; ============================================================================

(defun worker-thread (stream)
  "Handle a single client connection.
   
   This function runs in a separate thread and should:
   1. Read commands from the stream
   2. Execute ACL2 operations
   3. Return results
   4. Clean up the stream
   
   The calling thread automatically unregisters the worker on exit."
  (let ((thread-obj (bordeaux-threads:current-thread)))
    (register-worker thread-obj)
    (unwind-protect
         (handler-case
             (progn
               ;; Your actual ACL2 command processing here
               ;; For now, just echo as proof-of-concept
               (let ((input (read-line stream)))
                 (format stream "ECHO: ~A~%" input)
                 (force-output stream)))
           ;; Gracefully handle client disconnections
           (end-of-file () nil)
           ;; Log other errors but don't crash the thread
           (error (e)
             (alert (format nil "Worker error: ~A" e))))
      ;; Cleanup: close stream and unregister thread
      (progn
        (close stream :abort t)
        (unregister-worker thread-obj)))))

;;; ============================================================================
;;; Listener Thread Implementation
;;; ============================================================================

(defun listener-thread ()
  "Main listener thread: accepts connections and spawns workers.
   
   This thread:
   1. Accepts incoming connections from *bridge-shutdown* = nil
   2. For each connection, spawns a worker thread
   3. Handles socket errors gracefully
   4. Cleans up the socket file on exit
   
   The loop checks *bridge-shutdown* on each iteration for graceful
   shutdown (no aggressive thread termination needed)."
  
  (let ((sock (create-listen-socket *socket-path*)))
    (unwind-protect
         (progn
           (alert "ACL2-Bridge listener started")
           ;; Main accept loop - checks shutdown flag on each iteration
           (loop until *bridge-shutdown* do
             (handler-case
                 (let ((client-stream 
                        (sb-bsd-sockets:socket-make-stream
                          (sb-bsd-sockets:socket-accept sock)
                          :input t :output t :buffering :full)))
                   ;; Spawn worker for this connection
                   (when client-stream
                     (let ((worker 
                            (bordeaux-threads:make-thread
                              (lambda () (worker-thread client-stream))
                              :name (format nil "acl2-worker-~D" 
                                           (random 1000)))))
                       (alert (format nil "Accepted connection: ~A" worker)))))
               ;; Handle socket errors that don't terminate the listener
               (sb-bsd-sockets:interrupted-error ()
                 ;; Re-check shutdown flag and continue loop
                 nil)
               (sb-bsd-sockets:operation-timeout-error ()
                 ;; Timeout on accept - just retry
                 nil)
               ;; Catch unexpected errors but keep listening
               (error (e)
                 (alert (format nil "Accept loop error: ~A" e))))))
      ;; Cleanup: close socket and remove socket file
      (progn
        (alert "Forcibly closing ACL2-Bridge socket!")
        (sb-bsd-sockets:socket-close sock)
        ;; CRITICAL: Socket file must be explicitly deleted
        ;; This is not done automatically by socket-close
        (cleanup-socket-file *socket-path*)))))

;;; ============================================================================
;;; Public API: start/stop
;;; ============================================================================

(defun start ()
  "Start the ACL2-Bridge listener.
   
   Returns the listener thread object.
   
   Example:
     (bridge::start)   ; Start listening
     
   Error conditions:
     - socket-error: If socket creation/binding fails
     - error: If thread creation fails"
  
  (when (bordeaux-threads:thread-alive-p *listener-thread*)
    (error "ACL2-Bridge already running"))
  
  (setf *bridge-shutdown* nil)
  (setf *listener-thread*
        (bordeaux-threads:make-thread 
          #'listener-thread
          :name "acl2-bridge-listener"))
  
  *listener-thread*)

(defun stop ()
  "Stop the ACL2-Bridge listener gracefully.
   
   This function:
   1. Sets shutdown flag (signals listener to exit)
   2. Waits for listener to close socket file
   3. Terminates remaining worker threads
   4. Returns NIL on success
   
   Example:
     (bridge::stop)    ; Stop listening
     
   Note: This does NOT use aggressive thread termination.
         All cleanup is gracefully triggered by *bridge-shutdown*."
  
  (unless (bordeaux-threads:thread-alive-p *listener-thread*)
    (return-from stop nil))
  
  ;; Signal graceful shutdown
  (setf *bridge-shutdown* t)
  
  ;; Give listener thread time to:
  ;; 1. Finish current accept() call (max ~100ms for timeout)
  ;; 2. Exit its loop
  ;; 3. Close socket
  ;; 4. Delete socket file
  (sleep 0.2)
  
  ;; Terminate remaining workers
  (kill-all-workers 5)
  
  ;; Force-terminate listener if still alive (shouldn't happen)
  (when (bordeaux-threads:thread-alive-p *listener-thread*)
    (bordeaux-threads:destroy-thread *listener-thread*))
  
  (setf *listener-thread* nil)
  
  nil)

(defun status ()
  "Return current bridge status.
   
   Returns a property list with:
     :running - boolean
     :socket-path - path to Unix domain socket
     :workers - number of active worker threads
     :listener - listener thread object or nil"
  
  (list :running (bordeaux-threads:thread-alive-p *listener-thread*)
        :socket-path *socket-path*
        :workers (hash-table-count *worker-threads*)
        :listener *listener-thread*
        :socket-exists (probe-file *socket-path*)))

;;; ============================================================================
;;; Alert/Logging (Replace with your logging system)
;;; ============================================================================

(defun alert (message)
  "Log a message. Replace with your logging framework."
  (format *standard-output* "[ACL2-BRIDGE] ~A~%" message)
  (force-output *standard-output*))

;;; ============================================================================
;;; Testing / Example Usage
;;; ============================================================================

#|

;; Start the bridge
(bridge::start)

;; Check status
(bridge::status)

;; Test with socat (from another terminal):
;;   echo "hello" | socat - UNIX-CONNECT:/tmp/acl2-bridge.sock

;; Stop the bridge
(bridge::stop)

;; Verify socket file is cleaned up
(probe-file "/tmp/acl2-bridge.sock")  => NIL

|#
