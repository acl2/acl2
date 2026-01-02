;;; bridge-sbcl.lisp - SBCL port of centaur/bridge/bridge-raw.lsp
;;;
;;; This is a direct adaptation of the original CCL-only bridge code.
;;; CCL-specific calls are replaced with SBCL/portable equivalents.

(in-package "BRIDGE")

;;; ============================================================================
;;; CCL Compatibility Layer for SBCL
;;; ============================================================================

;;; Threading primitives (using bordeaux-threads)
(defmacro ccl-make-lock (name)
  `(bt:make-lock ,name))

(defmacro ccl-with-lock-grabbed ((lock) &body body)
  `(bt:with-lock-held (,lock) ,@body))

(defun ccl-try-lock (lock)
  (bt:acquire-lock lock nil))

(defun ccl-release-lock (lock)
  (bt:release-lock lock))

(defun ccl-make-semaphore ()
  (bt:make-semaphore))

(defun ccl-wait-on-semaphore (sem)
  (bt:wait-on-semaphore sem))

(defun ccl-signal-semaphore (sem)
  (bt:signal-semaphore sem))

(defun ccl-process-name (thread)
  (bt:thread-name thread))

(defun ccl-current-process ()
  (bt:current-thread))

(defun ccl-all-processes ()
  (bt:all-threads))

(defun ccl-process-kill (thread)
  (bt:destroy-thread thread))

(defun ccl-process-interrupt (thread function)
  (bt:interrupt-thread thread function))

(defmacro ccl-without-interrupts (&body body)
  `(sb-sys:without-interrupts ,@body))

(defun ccl-getenv (name)
  (uiop:getenv name))

;;; Socket primitives (using usocket for TCP, sb-bsd-sockets for Unix)
(defun ccl-make-socket-tcp (port)
  (usocket:socket-listen "0.0.0.0" port :reuse-address t :element-type 'character))

(defun ccl-make-socket-unix (path)
  "Create a Unix domain socket at PATH."
  ;; Use SBCL's native sb-bsd-sockets for Unix sockets
  (format *error-output* "~&[ccl-make-socket-unix] requiring sb-bsd-sockets~%")
  (force-output *error-output*)
  (require :sb-bsd-sockets)
  (format *error-output* "~&[ccl-make-socket-unix] creating local-socket instance~%")
  (force-output *error-output*)
  (handler-case
      (let ((socket (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
        (format *error-output* "~&[ccl-make-socket-unix] socket instance created~%")
        (force-output *error-output*)
        ;; Remove existing socket file if present
        (when (probe-file path)
          (format *error-output* "~&[ccl-make-socket-unix] removing existing socket~%")
          (force-output *error-output*)
          (delete-file path))
        (format *error-output* "~&[ccl-make-socket-unix] binding to ~A~%" path)
        (force-output *error-output*)
        (sb-bsd-sockets:socket-bind socket path)
        (format *error-output* "~&[ccl-make-socket-unix] listening~%")
        (force-output *error-output*)
        (sb-bsd-sockets:socket-listen socket 5)
        (format *error-output* "~&[ccl-make-socket-unix] done, file exists: ~A~%" (probe-file path))
        (force-output *error-output*)
        socket)
    (error (e)
      (format *error-output* "~&[ccl-make-socket-unix] ERROR: ~A~%" e)
      (force-output *error-output*)
      (error e))))

(defun ccl-accept-connection (server-socket)
  "Accept a connection and return a bidirectional stream."
  (format *error-output* "~&[ccl-accept-connection] called with ~A~%" (type-of server-socket))
  (force-output *error-output*)
  (etypecase server-socket
    (usocket:stream-server-usocket
     (let ((client (usocket:socket-accept server-socket)))
       (usocket:socket-stream client)))
    (sb-bsd-sockets:local-socket
     (format *error-output* "~&[ccl-accept-connection] calling socket-accept...~%")
     (force-output *error-output*)
     (let ((client-socket (sb-bsd-sockets:socket-accept server-socket)))
       (format *error-output* "~&[ccl-accept-connection] got client socket~%")
       (force-output *error-output*)
       (sb-bsd-sockets:socket-make-stream client-socket
                                          :input t :output t
                                          :element-type 'character
                                          :buffering :full)))))

(defun ccl-close-socket (socket &key abort)
  (etypecase socket
    (usocket:usocket
     (usocket:socket-close socket))
    (sb-bsd-sockets:socket
     (sb-bsd-sockets:socket-close socket))
    (stream
     (close socket :abort abort))))

;;; Process/thread creation
(defun ccl-process-run-function (options function &rest args)
  (let ((name (if (listp options) (getf options :name) options)))
    (bt:make-thread (lambda () (apply function args)) :name name)))

;;; ============================================================================
;;; Gray Streams for Bridge Output
;;; ============================================================================

(defclass bridge-ostream (trivial-gray-streams:fundamental-character-output-stream)
  ((stream :initarg :stream :accessor bridge-ostream-stream)
   (name   :initarg :name   :accessor bridge-ostream-name)))

(defmethod trivial-gray-streams:stream-write-char ((stream bridge-ostream) char)
  (ccl-without-interrupts
    (send-message "STDOUT" (string char) (bridge-ostream-stream stream)))
  char)

(defmethod trivial-gray-streams:stream-write-string ((stream bridge-ostream) string &optional start end)
  (let* ((start (or start 0))
         (end (or end (length string)))
         (substr (if (and (= start 0) (= end (length string)))
                     string
                     (subseq string start end))))
    (when (> (length substr) 0)
      (ccl-without-interrupts
        (send-message "STDOUT" substr (bridge-ostream-stream stream)))))
  string)

(defmethod trivial-gray-streams:stream-line-column ((stream bridge-ostream))
  nil)

(defmethod trivial-gray-streams:stream-force-output ((stream bridge-ostream))
  (force-output (bridge-ostream-stream stream)))

(defmethod trivial-gray-streams:stream-finish-output ((stream bridge-ostream))
  (finish-output (bridge-ostream-stream stream)))

;;; ============================================================================
;;; Bridge Protocol - Message Format
;;; ============================================================================

(defvar bridge-default-port 55433)

;; NOTE: *standard-co* is an ACL2 variable that must be imported from ACL2,
;; not redefined. We use acl2::*standard-co* directly.

(defvar *bridge-debug* nil)

(defun bridge-debug (msg &rest args)
  (when *bridge-debug*
    (apply #'format t msg args)))

(defun bridge-alert (msg &rest args)
  (apply #'format t msg args))

(defun send-message (type content stream)
  "Send: TYPE LEN\\nCONTENT\\n"
  (ccl-without-interrupts
    (write-string type stream)
    (write-char #\Space stream)
    (write-string (write-to-string (length content)) stream)
    (write-char #\Newline stream)
    (write-string content stream)
    (write-char #\Newline stream)
    (force-output stream)))

(defun read-command (stream)
  "Read a command, return (values type content) or (values nil nil) on EOF."
  (let ((line (read-line stream nil nil)))
    (unless line
      (return-from read-command (values nil nil)))
    (let* ((space (position #\Space line))
           (type (subseq line 0 space))
           (len (parse-integer line :start (1+ space))))
      (let ((content (make-string len)))
        (read-sequence content stream)
        (read-char stream nil nil)  ; consume newline
        (values (intern (string-upcase type) "KEYWORD") content)))))

;;; ============================================================================
;;; Worker Thread - Command Processing
;;; ============================================================================

(defun worker-write-return (type results stream)
  "Encode and send return value based on command type."
  (let ((content
          (case type
            (:lisp    (write-to-string (first results)))
            (:lisp_mv (write-to-string results))
            (:json    (bridge::to-json (first results)))
            (:json_mv (bridge::to-json results))
            (t        (write-to-string (first results))))))
    (send-message "RETURN" content stream)))

(defun worker-do-work (stream)
  "Process one command. Returns T to continue, NIL to exit."
  (send-message "READY" "" stream)
  (multiple-value-bind (type content) (read-command stream)
    (unless type
      (bridge-debug "Client disconnected.~%")
      (return-from worker-do-work nil))
    (bridge-debug "Got command: ~a ~a~%" type content)
    (handler-case
        (let* ((form (read-from-string content))
               (results (multiple-value-list
                         (eval `(let ((state acl2::*the-live-state*))
                                  (declare (ignorable state))
                                  ,form)))))
          (worker-write-return type results stream))
      (error (condition)
        (bridge-debug "Error: ~a~%" condition)
        (send-message "ERROR" (format nil "~a" condition) stream))))
  t)

;;; ============================================================================
;;; ACL2 Output Channel Binding
;;; ============================================================================

(defmacro with-acl2-channels-bound (channel &rest forms)
  `(progv
       (list (acl2::global-symbol 'acl2::proofs-co)
             (acl2::global-symbol 'acl2::standard-co)
             (acl2::global-symbol 'acl2::trace-co))
       (list ,channel ,channel ,channel)
     (progn . ,forms)))

(defmacro with-output-to (stream &rest forms)
  (let ((channel (gensym)))
    `(let* ((,channel (gensym)))
       (setf (get ,channel acl2::*open-output-channel-type-key*) :character)
       (setf (get ,channel acl2::*open-output-channel-key*) ,stream)
       (unwind-protect
           (let ((*standard-output* ,stream)
                 (*trace-output*    ,stream)
                 (*debug-io*        ,stream)
                 (*error-output*    ,stream)
                 (acl2::*standard-co*     ,channel))
             (with-acl2-channels-bound ,channel . ,forms))
         (setf (get ,channel acl2::*open-output-channel-key*) nil)
         (setf (get ,channel acl2::*open-output-channel-type-key*) nil)))))

;;; ============================================================================
;;; Worker Thread Entry Point
;;; ============================================================================

(defun worker-thread (stream)
  (handler-case
      (let ((acl2::*default-hs* (acl2::hl-hspace-init))
            (*package* (find-package "ACL2"))
            (ostream (make-instance 'bridge-ostream
                                    :stream stream
                                    :name "STDOUT")))
        (with-output-to ostream
          (send-message "ACL2_BRIDGE_HELLO" (ccl-process-name (ccl-current-process)) stream)
          (loop while (worker-do-work stream))
          (close stream)))
    (error (condition)
      (bridge-alert "Uncaught error in worker thread: ~a~%" condition)
      (ignore-errors (close stream :abort t)))))

;;; ============================================================================
;;; Listener Thread
;;; ============================================================================

(defvar *worker-counter* 0)

(defun listener-thread (server-socket)
  (format t "; ACL2 Bridge: Listener thread starting.~%")
  (unwind-protect
      (loop do
        (let* ((client-stream (ccl-accept-connection server-socket))
               (worker-name (format nil "bridge-worker-~a" (incf *worker-counter*))))
          (bridge-debug "Got connection.~%")
          (ccl-process-run-function (list :name worker-name)
                                    'worker-thread client-stream)))
    (progn
      (bridge-alert "Forcibly closing ACL2-Bridge socket!")
      (ccl-close-socket server-socket :abort t)))
  (format t "; ACL2 Bridge: Listener thread exiting~%"))

;;; ============================================================================
;;; Main Thread Support (for memoization, hons sharing)
;;; ============================================================================

(defvar *main-thread-lock* (ccl-make-lock "*main-thread-lock*"))
(defvar *main-thread-work* nil)
(defvar *main-thread-ready* (ccl-make-semaphore))

(defun main-thread-loop ()
  "Run the main thread work loop. This should be called from the main ACL2 thread
   after starting any background servers (HTTP, Bridge, etc.).
   Worker threads delegate heavy ACL2 operations here via execute-in-main-thread."
  (setf *main-thread-running* t)
  (format t "; Main thread loop starting (thread: ~A)~%" (bt:current-thread))
  (unwind-protect
      (loop do
        (bridge-debug "Main thread waiting for work.~%")
        (ccl-wait-on-semaphore *main-thread-ready*)
        (bridge-debug "Main thread got work.~%")
        (let ((work *main-thread-work*))
          (setq *main-thread-work* nil)
          (when work (funcall work))))
    (setf *main-thread-running* nil)
    (format t "; Main thread loop exiting~%")))

(defvar *no-main-thread* nil
  "When T, in-main-thread just executes forms directly.")

(defmacro in-main-thread-aux (&rest forms)
  (let ((done         (gensym))
        (retvals      (gensym))
        (errval       (gensym))
        (finished     (gensym))
        (saved-stdout (gensym))
        (saved-stdco  (gensym))
        (work         (gensym)))
    `(let* ((,done         (ccl-make-semaphore))
            (,retvals      nil)
            (,finished     nil)
            (,errval       nil)
            (,saved-stdout *standard-output*)
            (,saved-stdco  acl2::*standard-co*)
            (,work
             (lambda ()
               (bridge-debug "Main thread is doing its work.~%")
               (let* ((*standard-output* ,saved-stdout)
                      (*trace-output*    ,saved-stdout)
                      (*debug-io*        ,saved-stdout)
                      (*error-output*    ,saved-stdout)
                      (acl2::*standard-co*     ,saved-stdco))
                 (with-acl2-channels-bound ,saved-stdco
                   (block try-to-run-it
                     (unwind-protect
                         (handler-case
                             (progn
                               (setq ,retvals (multiple-value-list (progn . ,forms)))
                               (setq ,finished t)
                               (bridge-debug "Main thread computed its return values.~%"))
                           (error (condition)
                             (bridge-debug "Main thread trapping error for worker.~%")
                             (setq ,errval condition)
                             (setq ,finished t)))
                       (unless ,finished 
                         (setq ,errval (make-condition 'simple-error
                                                       :format-control "Unexpected non-local exit.")))
                       (return-from try-to-run-it nil)))
                   (ccl-signal-semaphore ,done)
                   (bridge-debug "Main thread is all done.~%"))))))
       (bridge-debug "Installing work for main thread.~%")
       (setq *main-thread-work* ,work)
       (ccl-signal-semaphore *main-thread-ready*)
       (bridge-debug "Waiting for main thread to finish.~%")
       (ccl-wait-on-semaphore ,done)
       (when ,errval
         (bridge-debug "Got error from the main thread.~%")
         (error ,errval))
       (bridge-debug "Got good values from the main thread.~%")
       (values-list ,retvals))))

(defun run-in-main-thread-raw (irrelevant-variable-for-return-last form)
  (declare (ignore irrelevant-variable-for-return-last))
  (if *no-main-thread*
      (eval form)
      (ccl-with-lock-grabbed (*main-thread-lock*)
        (bridge-debug "Got the lock, now in main thread.~%")
        (eval `(in-main-thread-aux ,form)))))

(defun try-to-run-in-main-thread-raw (irrelevant-variable-for-return-last form)
  (declare (ignore irrelevant-variable-for-return-last))
  (cond (*no-main-thread*
         (eval form))
        ((not (ccl-try-lock *main-thread-lock*))
         (bridge-debug "The main thread is busy, giving up.~%")
         (error "The main thread is busy."))
        (t
         (unwind-protect
             (progn
               (bridge-debug "Main thread wasn't busy, so it's my turn.~%")
               (eval `(in-main-thread-aux ,form)))
           (bridge-debug "Releasing lock on main thread.~%")
           (ccl-release-lock *main-thread-lock*)))))

;;; ---------------------------------------------------------------------------
;;; Public API for Main Thread Execution
;;; ---------------------------------------------------------------------------

(defun execute-in-main-thread (thunk)
  "Execute THUNK (a zero-argument function) in the main ACL2 thread.
   This is safe for operations like include-book that require the main thread.
   Returns the result of THUNK, or signals any error that occurred.
   
   If *no-main-thread* is true, just calls THUNK directly."
  (if *no-main-thread*
      (funcall thunk)
      (ccl-with-lock-grabbed (*main-thread-lock*)
        (bridge-debug "Got the lock, delegating to main thread.~%")
        (let* ((done (ccl-make-semaphore))
               (retvals nil)
               (errval nil)
               (finished nil))
          ;; Install the work
          (setq *main-thread-work*
                (lambda ()
                  (bridge-debug "Main thread executing work.~%")
                  (handler-case
                      (progn
                        (setq retvals (multiple-value-list (funcall thunk)))
                        (setq finished t))
                    (error (condition)
                      (bridge-debug "Main thread caught error: ~A~%" condition)
                      (setq errval condition)
                      (setq finished t)))
                  (unless finished
                    (setq errval (make-condition 'simple-error
                                                 :format-control "Unexpected non-local exit.")))
                  (ccl-signal-semaphore done)))
          ;; Signal main thread
          (ccl-signal-semaphore *main-thread-ready*)
          ;; Wait for completion
          (bridge-debug "Waiting for main thread...~%")
          (ccl-wait-on-semaphore done)
          ;; Return result or signal error
          (when errval
            (bridge-debug "Re-signaling error from main thread.~%")
            (error errval))
          (bridge-debug "Got result from main thread.~%")
          (values-list retvals)))))

(defvar *main-thread-running* nil
  "True when main-thread-loop is running.")

;;; ============================================================================
;;; Public API
;;; ============================================================================

(defun start-fn (socket-name-or-port-number stack-size tstack-size vstack-size)
  (declare (ignore stack-size tstack-size vstack-size))
  (unless socket-name-or-port-number
    (setq socket-name-or-port-number bridge-default-port))
  (format t "Starting ACL2 Bridge on ~a, ~a~%"
          (or (ccl-getenv "HOSTNAME") "localhost")
          socket-name-or-port-number)
  (let ((sock (cond ((integerp socket-name-or-port-number)
                     (ccl-make-socket-tcp socket-name-or-port-number))
                    ((stringp socket-name-or-port-number)
                     (ccl-make-socket-unix socket-name-or-port-number))
                    (t
                     (error "Expected port number or socket path, got ~s"
                            socket-name-or-port-number)))))
    (ccl-process-run-function (list :name "bridge-listener")
                              'listener-thread sock))
  ;; Enter the main thread loop (blocks forever)
  (main-thread-loop)
  nil)

(defun stop ()
  (format t "; bridge::stop: Current threads: ~a~%" (ccl-all-processes))
  (dolist (thread (ccl-all-processes))
    (when (and (bt:thread-name thread)
               (or (search "bridge-listener" (bt:thread-name thread))
                   (search "bridge-worker" (bt:thread-name thread))))
      (format t "Killing ~a~%" thread)
      (ignore-errors (ccl-process-kill thread))))
  (sleep 2)
  (format t "; bridge::stop done.~%"))
