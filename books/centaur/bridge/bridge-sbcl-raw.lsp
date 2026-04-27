; ACL2 Bridge -- SBCL Port
; Copyright (C) 2012 Centaur Technology
; Copyright (C) 2026 (SBCL port)
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; SBCL port based on bridge-raw.lsp

(in-package "BRIDGE")

(defun sleep$ (n)
  (sleep n))

(defconstant bridge-default-port 55433)

(defmacro debug (msg &rest args)
  nil
  ;; For hacking on the bridge, uncomment this to watch what's happening.
  ;; `(format *terminal-io*
  ;;         (concatenate 'string "Bridge: ~a: " ,msg)
  ;;         (bordeaux-threads:thread-name (bordeaux-threads:current-thread))
  ;;         . ,args)
  )

(defmacro alert (msg &rest args)
  ;; This is only used for bridge messages that are unusual.
  `(format *terminal-io*
           (concatenate 'string "Bridge: ~a: " ,msg)
           (bordeaux-threads:thread-name (bordeaux-threads:current-thread))
           . ,args))

; Writing Messages -----------------------------------------------------------

; We write an output stream class for wrapping up ordinary printed output
; (e.g., from things like FORMAT, CW, etc.) into messages.  This lets us send
; all output to the client in a uniform way.

(defun send-message (type content stream)
  ;; Basic routine for sending strings as messages.  This gets used for error
  ;; messages and sending results (after encoding them as json), but not for
  ;; output.
  (declare (type string type content))
  (debug "Send plain message on ~a: ~a~%" type content)
  (sb-sys:without-interrupts (write-string type stream)
                             (write-char #\Space stream)
                             (prin1 (length content) stream)
                             (write-char #\Newline stream)
                             (write-string content stream)
                             (write-char #\Newline stream)))

(defclass bridge-ostream (trivial-gray-streams:fundamental-character-output-stream)
  ;; Special output stream that gets used to distinguish different kinds of
  ;; output channels

  (;; NAME is the name that we want to use for every message we print to this
   ;; stream.  This lets us say, e.g., that a message is for standard output,
   ;; or for the comment window, or for other kinds of output streams.
   (name   :initarg :name :reader name-of)

   ;; STREAM is the actual output stream to the client.  Typically it is shared
   ;; by many bridge-ostreams that are all also writing to the client.  Note
   ;; that there's no locking here, we only expect each client to have a single
   ;; thread interacting with it.
   (stream :initarg :stream :reader stream-of)))

;; Note: stream-element-type and close are standard CL functions, not
;; trivial-gray-streams generics.  We don't need to specialize them here
;; since the default behavior delegates to the underlying stream appropriately.

(defmethod trivial-gray-streams:stream-line-column ((self bridge-ostream))
  nil)

(defmethod trivial-gray-streams:stream-finish-output ((self bridge-ostream))
  (finish-output (stream-of self)))

(defmethod trivial-gray-streams:stream-force-output ((self bridge-ostream))
  (force-output (stream-of self)))

(defmethod trivial-gray-streams:stream-write-char ((self bridge-ostream) c)
  (let ((stream (stream-of self)))
    (debug "Send char message on ~a: ~a~%" (name-of self) (if (eql c #\Newline) "[Newline]" c))
    (sb-sys:without-interrupts
     (write-string (name-of self) stream)
     (write-char #\Space stream)
     (write-char #\1 stream)
     (write-char #\Newline stream)
     (write-char c stream)
     (write-char #\Newline stream))))

(defun ugly-string-length-computation (str start end)
  ;; Compute actual length to write, handling optional END parameter.
  (let ((end (or end (length str))))
    (- end start)))

(defmethod trivial-gray-streams:stream-write-string ((self bridge-ostream) str &optional (start 0) end)
  (let ((stream (stream-of self))
        (n      (ugly-string-length-computation str start end)))
    (debug "Send str message on ~a: ~a~%" (name-of self) (subseq str start end))
    (sb-sys:without-interrupts
     (write-string (name-of self) stream)
     (write-char #\Space stream)
     (prin1 n stream)
     (write-char #\Newline stream)
     (write-string str stream :start start :end end)
     (write-char #\Newline stream))))



; Here's an example of what the above accomplishes:
;
; We can wrap up the standard output stream in multiple bridge-ostreams.  We
; can then print to these streams using ordinary functions like write-string,
; write-char, format, etc., and it automatically wraps everything up into
; messages and does the necessary multiplexing.
;
; Note for multithreading: we don't currently do anything to lock writes.  If
; you have multiple Lisp threads printing to the same bridge-ostream, it's
; going to cause probelms.

#||

(let ((stream (make-instance 'bridge-ostream
                             :stream *standard-output*
                             :name "STDOUT"
                             ))
      (stream2 (make-instance 'bridge-ostream
                              :stream *standard-output*
                              :name "STDERR")))
  (write-string "Hello" stream)
  (write-string "Hello" stream2)
  (write-char #\a stream)
  (write-string "World" stream)
  (force-output stream)
  (write-char #\Newline stream)
  (format stream "This is a ~a message with~% ~15:D with args."
          (cons 1 2) 130120110)
  (finish-output stream))

||#



; Reading Commands ------------------------------------------------------------

(defparameter eof
  ;; Special constant to denote end of file
  (cons :eof :eof))

(defun substring-number-p (str &key (start '0) end)
  (declare (string str)
           (fixnum start))
  (let ((end (or end (length str))))
    (declare (fixnum end))
    (loop for i fixnum from start below end do
          (let ((c (char str i)))
            (unless (and (char<= #\0 c)
                         (char<= c #\9))
              (return-from substring-number-p nil))))
    (< start end)))

(assert (substring-number-p "1"))
(assert (substring-number-p "12"))
(assert (substring-number-p "331"))
(assert (not (substring-number-p "")))
(assert (not (substring-number-p "12 ")))
(assert (not (substring-number-p " 12")))

(defund identifier-p (str &key (start '0) end)
  ;; START must be a valid index for STR.
  (declare (string str)
           (fixnum start))
  (let ((end (or end (length str))))
    (declare (fixnum end))
    (let ((c (char str start)))
      (unless (and (char<= #\A c) (char<= c #\Z))
        ;; First char must be uppercase alpha
        (return-from identifier-p nil))
      ;; Rest must be uppercase alpha, numeric, or underscore
      (loop for i fixnum from (+ 1 start) below end do
            (let ((c (char str i)))
              (unless (or (eql c #\_)
                          (and (char<= #\A c) (char<= c #\Z))
                          (and (char<= #\0 c) (char<= c #\9)))
                (return-from identifier-p nil))))
      t)))

(assert (identifier-p "F"))
(assert (identifier-p "FOO"))
(assert (identifier-p "FOO_12"))
(assert (identifier-p "F1_AB"))
(assert (not (identifier-p "f")))
(assert (not (identifier-p " ")))
(assert (not (identifier-p "FAB ")))
(assert (not (identifier-p "Fa")))

(defun parse-header (header)
  (declare (type string header))
  (let ((space (position #\Space header)))
    (unless space
      (return-from parse-header (values nil nil)))
    (let ((type (subseq header 0 space)))
      (unless (identifier-p type)
        (return-from parse-header (values nil nil)))
      (let ((len (and (substring-number-p header :start (+ 1 space))
                      (parse-integer header :start (+ 1 space)))))
        (if len
            (values type len)
          (values nil nil))))))

; Some examples:

(assert (equal (multiple-value-list (parse-header "CMD 150"))  (list "CMD" 150)))
(assert (equal (multiple-value-list (parse-header "CMD 0"))    (list "CMD" 0)))
(assert (equal (multiple-value-list (parse-header "CMD 1234")) (list "CMD" 1234)))
(assert (equal (multiple-value-list (parse-header "FOO"))      (list nil nil)))
(assert (equal (multiple-value-list (parse-header "CMD 123 ")) (list nil nil)))
(assert (equal (multiple-value-list (parse-header "CMD"))      (list nil nil)))
(assert (equal (multiple-value-list (parse-header "CMD "))     (list nil nil)))

(defun string-to-sexpr (str)
  (multiple-value-bind (sexpr pos)
      (read-from-string str)
    (let ((next (read-from-string str nil eof :start pos)))
      (unless (eq next eof)
        (error "Found more than one sexpr in command content:~%String was: ~a~%" str)))
    sexpr))

(assert (equal (string-to-sexpr "(+ 1 2)") '(+ 1 2)))
(assert (equal (string-to-sexpr "(+ 1 2) ") '(+ 1 2)))
(assert (equal (string-to-sexpr " (+ 1 2) ") '(+ 1 2)))
(assert (equal (string-to-sexpr " (+ #x10 2) ") '(+ 16 2)))

(defun read-command (stream)
  ;; Returns (values type sexpr) or (values eof eof)
  (let ((header (read-line stream nil eof nil)))
    (debug "Read header: ~a~%" header)
    (if (eq header eof)
        (values eof eof)
      (multiple-value-bind (type len)
          (parse-header header)
        (unless type
          (error "Invalid command: expected valid header but found ~a.~%" header))
        (let* ((content (make-string len))
               (nread   (read-sequence content stream))
               (newline nil))
        (declare (dynamic-extent content))
        (debug "Read content: ~a~%" content)
        (unless (= nread len)
          (error "Invalid command, expected ~a characters of content but found ~a.~%
                  Header was ~a~%Content was ~a"
                 len nread header (subseq content 0 nread)))
        (setq newline (read-char stream))
        (unless (eql newline #\Newline)
          (error "Invalid command, expected newline after content but found ~a.~%
                  Header was ~a~%Content was ~a"
                 newline header content))
        (values (intern type "KEYWORD") (string-to-sexpr content)))))))

(defun test-read-command (input expected-type expected-sexpr)
  (let ((stream (make-string-input-stream input)))
    (multiple-value-bind (type sexpr)
        (read-command stream)
      (and (or (equal type expected-type)
               (error "type not right: found ~a, expected ~a" type expected-type))
           (or (equal sexpr expected-sexpr)
               (error "sexpr not right: found ~a, expected ~a" sexpr expected-sexpr))))))

(assert (test-read-command "" eof eof))

(assert (test-read-command "CMD 3
abc
" :cmd 'abc))

(assert (test-read-command "CMD 8
 (+ 1 2)
" :cmd '(+ 1 2)))



; Worker Threads --------------------------------------------------------------

(defun worker-write-return (type ret-list stream)
  (case type
    (:lisp    (send-message "RETURN" (prin1-to-string (car ret-list)) stream))
    (:lisp_mv (send-message "RETURN" (prin1-to-string ret-list) stream))
    (:json    (send-message "RETURN" (json-encode (car ret-list)) stream))
    (:json_mv (send-message "RETURN" (json-encode ret-list) stream))
    (otherwise
     (alert "Unsupported command type: ~a~%" type)
     (error "Unsupported command type: ~a~%" type))))

(defun worker-do-work (stream)
  ;; Returns true when we want to do more work, nil when we're ready to be all
  ;; done.
  (debug "Starting work loop~%")
  (send-message "READY" "" stream)
  (force-output stream)
  (multiple-value-bind
      (type cmd)
      (handler-case (read-command stream)
                    (error (condition)
                           (alert "Error during read-command:~%~a~%" condition)
                           (send-message "ERROR"
                                         (format nil "Error during read-command:~%~a~%" condition)
                                         stream)
                           (clear-input stream)
                           (return-from worker-do-work t)))

    (when (eq type eof)
      ;; EOF means client is all done, stop processing commands.
      (debug "Found EOF, worker quitting.~%")
      (return-from worker-do-work nil))

    (debug "Ready to execute: ~a: ~a~%" type cmd)

    ;; Try to do the command.  This can fail for any number of reasons.  We
    ;; always want to keep going, whether there's an error or not.
    (let ((ret (handler-case
                (multiple-value-list
                 (eval
                  ;; As a convenience, bind STATE so that commands can use it without having
                  ;; to bind it.  This is nice in that it lets a macro such as
                  ;;   (FOO-MAC X Y Z) == `(FOO-MAC-FN ,X ,Y ,Z STATE)
                  ;; be used from commands directly and still hide the state.  It's probably
                  ;; not worth doing this for other stobjs, but STATE is so common that maybe
                  ;; it's worthwhile to do it.
                  `(let ((acl2::state acl2::*the-live-state*))
                     (declare (ignorable acl2::state))
                     ,cmd)))
                (error (condition)
                       (alert "Error executing command ~a:~%~a~%" cmd condition)
                       (send-message "ERROR"
                                     (format nil "Error executing command ~a:~%~a~%" cmd condition)
                                     stream)
                       (return-from worker-do-work t)))))

      (debug "Done executing command: ~a~%" ret)
      
      ;; Check shutdown flag BEFORE writing return value.
      ;; If stop() was called, the client has disconnected after sending
      ;; the stop command, so writing the return would cause broken pipe.
      ;; This is the hunchentoot pattern: check shutdown before I/O.
      (when *bridge-shutdown*
        (debug "Shutdown requested, exiting worker without writing return.~%")
        (return-from worker-do-work nil))
      
      (handler-case
       (worker-write-return type ret stream)
       (error (condition)
              (alert "Error writing return value: ~a~%" condition)
              (send-message "ERROR"
                            (format nil "Error writing return value:~%~a~%" condition)
                            stream)
              (return-from worker-do-work t)))

      t)))


; Worker Output Setup.
;
; The goal here is to get printing to FMT, CW, etc., routed through the
; client's output stream.
;
; Binding *STANDARD-OUTPUT* is easy.
;
; Binding *STANDARD-CO* is slightly trickier.  The value of *STANDARD-CO* is
; just a symbol, e.g., ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0, and
; functions like PRINC$ use GET-OUTPUT-STREAM-FROM-CHANNEL to look up the
; associated stream.  So, to fit into this scheme, we need to bind
; *STANDARD-CO* to a new symbol that is associated with our particular stream.
;
; Unfortunately, aside from *standard-co*, there are also several state globals
; that ACL2 uses to do printing.  These include standard-co (again), proofs-co
; and trace-co.
;
; The way these work is really complicated.  Basically if you do (global-symbol
; 'proofs-co), you'll get a symbol like ACL2_GLOBAL_ACL2::PROOFS-CO.  Even
; though this symbol doesn't have *s around its name, it's a special, and
; whatever value it's bound to is the name of the actual channel (not stream)
; to use.  After some poking around I found you can use PROGV to bind these.
; What a mess!

(defmacro with-acl2-channels-bound (channel &rest forms)
  `(progv
       (list (acl2::global-symbol 'acl2::proofs-co)
             (acl2::global-symbol 'acl2::standard-co)
             (acl2::global-symbol 'acl2::trace-co))
       (list ,channel ,channel ,channel)
     (progn . ,forms)))

(defmacro with-output-to (stream &rest forms)
  (let ((channel (gensym)))
    `(let* ((,channel        (gensym)))
       (setf (get ,channel acl2::*open-output-channel-type-key*) :character)
       (setf (get ,channel acl2::*open-output-channel-key*) ,stream)
       (unwind-protect
           (let ((*standard-output* ,stream)
                 (*trace-output*    ,stream)
                 (*debug-io*        ,stream)
                 (*error-output*    ,stream)
                 (*standard-co*     ,channel))
             (with-acl2-channels-bound ,channel . ,forms))
         ;; Invalidate the symbol's stream so the garbage collector can
         ;; reclaim the stream.
         (setf (get ,channel acl2::*open-output-channel-key*) nil)
         (setf (get ,channel acl2::*open-output-channel-type-key*) nil)))))

;; Basic test of this:
(assert (equal (let ((test (make-string-output-stream)))
                  (with-output-to test
                                  (format t "This is a format test~%")
                                  (cw "This is a cw test")
                                  (fmt "This is a proof output test"
                                       nil (acl2::proofs-co acl2::*the-live-state*)
                                       acl2::*the-live-state* nil)
                                  (fmt "This is a standard-co test"
                                       nil (acl2::standard-co acl2::*the-live-state*)
                                       acl2::*the-live-state* nil)
                                  (fmt "This is a trace-co test"
                                       nil (f-get-global 'acl2::trace-co acl2::*the-live-state*)
                                       acl2::*the-live-state* nil))
                  (get-output-stream-string test))
                "This is a format test
This is a cw test
This is a proof output test
This is a standard-co test
This is a trace-co test"))

(defun worker-thread (stream)
  (format t "Starting worker thread~%")
  (handler-case
   (let ((acl2::*default-hs* (acl2::hl-hspace-init))
         (*package*          (find-package "ACL2"))
         (ostream            (make-instance 'bridge-ostream
                                            :stream stream
                                            :name "STDOUT")))
     (with-output-to ostream
                     (send-message "ACL2_BRIDGE_HELLO"
                                   (bordeaux-threads:thread-name (bordeaux-threads:current-thread))
                                   stream)
                     (loop while (worker-do-work stream))
                     (close stream)))
   (error (condition)
          (alert "Uncaught error in worker thread: ~a~%" condition)
          (ignore-errors (close stream :abort t)))))



; Bridge Listener and Worker Thread Creation ----------------------------------

; The listener thread waits for and handles new connections.  To keep things
; simple, I don't implement any kind of thread-recycling; I just create a new
; worker thread to handle each incoming connection.

; Note: On SBCL, we cannot set per-thread stack sizes like CCL supports.
; The *worker-stack-size*, *worker-vstack-size*, and *worker-tstack-size*
; variables are kept for API compatibility but are ignored.

(defvar *worker-stack-size*)
(defvar *worker-vstack-size*)
(defvar *worker-tstack-size*)

;; Track socket path for cleanup. Unix domain socket files must be explicitly
;; deleted - socket-close does NOT remove them (standard POSIX behavior).
(defvar *bridge-socket-path* nil)

;; Shutdown flag for graceful listener termination.
;; SBCL's destroy-thread is unreliable - use this flag instead.
(defvar *bridge-shutdown* nil)

; Socket handling: we need to support both TCP (via usocket) and Unix domain
; sockets (via sb-bsd-sockets). We use etypecase dispatch to handle both.

(defun make-socket-tcp (port)
  "Create a TCP server socket on PORT."
  (usocket:socket-listen "0.0.0.0" port
                         :reuse-address t
                         :element-type 'character))

(defun make-socket-unix (path)
  "Create a Unix domain socket at PATH.
   Removes any stale socket file from previous runs before binding."
  (require :sb-bsd-sockets)
  (let ((socket (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
    ;; Clean up stale socket file from previous runs
    (when (probe-file path)
      (delete-file path))
    (sb-bsd-sockets:socket-bind socket path)
    (sb-bsd-sockets:socket-listen socket 5)
    ;; Use blocking mode - we'll wake it with a dummy connection on shutdown
    socket))

(defun accept-connection (server-socket)
  "Accept a connection and return a bidirectional character stream."
  (etypecase server-socket
    (usocket:stream-server-usocket
     (let ((client (usocket:socket-accept server-socket :element-type 'character)))
       (usocket:socket-stream client)))
    (sb-bsd-sockets:local-socket
     (let ((client-socket (sb-bsd-sockets:socket-accept server-socket)))
       (when client-socket
         (sb-bsd-sockets:socket-make-stream client-socket
                                            :input t
                                            :output t
                                            :element-type 'character
                                            :buffering :full))))))

(defun close-socket (socket &key abort)
  "Close a socket (server or client)."
  (etypecase socket
    (usocket:usocket
     (usocket:socket-close socket))
    (sb-bsd-sockets:socket
     (sb-bsd-sockets:socket-close socket))
    (stream
     (close socket :abort abort))))

(defun listener-thread (sock)
  (format t "; ACL2 Bridge: Listener started~%")
  (unwind-protect
      ;; Main accept loop - blocking accept, woken by dummy connection on shutdown
      (loop for n from 0 do
            (handler-case
                (let ((stream (accept-connection sock)))
                  (cond
                    ;; Check shutdown AFTER accept returns (woken by dummy connection)
                    (*bridge-shutdown*
                     (when stream (ignore-errors (close stream :abort t)))
                     (return))
                    ;; Got a real connection - spawn worker
                    (stream
                     (let ((worker-name (cl-user::format nil "bridge-worker-~a" n)))
                       (bordeaux-threads:make-thread (lambda () (worker-thread stream))
                                                     :name worker-name)))))
              (sb-bsd-sockets:interrupted-error () nil)
              (error (e)
                (unless *bridge-shutdown*
                  (format t "; ACL2 Bridge: Listener error: ~a~%" e)))))
    ;; Cleanup: close the socket handle only. Socket FILE cleanup happens in stop().
    (ignore-errors (close-socket sock :abort t))))




; Access to the Main Thread ---------------------------------------------------

; The special macros (IN-MAIN-THREAD ...) and (TRY-IN-MAIN-THREAD ...) can be
; used to execute forms in the main thread (the "initial" thread).
;
; This is a huge hack.  It lets us use the main thread as the authoritative
; hons space.  And it lets us get around the fact that the memoize code is just
; not at all thread safe, and you can't even try to run a memoized computation
; from another thread.

(defvar *main-thread-lock* (bordeaux-threads:make-lock "main-thread-lock"))
(defvar *main-thread-work* nil)
(defvar *main-thread-ready* (bt-semaphore:make-semaphore))

(defun main-thread-loop ()
  (loop until *bridge-shutdown* do
        ;; I don't do any sort of error checking here because, by construction,
        ;; the work that gets added by IN-MAIN-THREAD-AUX should properly send
        ;; any errors out to the worker thread.
        (debug "Main thread waiting for work.~%")
        (bt-semaphore:wait-on-semaphore *main-thread-ready*)
        (debug "Main thread got work.~%")
        (unless *bridge-shutdown*
          (let ((work *main-thread-work*))
            (setq *main-thread-work* nil)
            (when work (funcall work))))))

; Setting up the work is very subtle.  To a first approximation, we just want
; to tell the main thread to execute
;
;  (lambda () (progn forms))
;
; But this isn't quite enough.  For one, the main thread has its own binding of
; *standard-out* and *standard-co*, so we'll need to make sure the lambda
; rebinds these (and any other specials we end up wanting.  Also, we want to
; pass the return values and any exceptions back on to the caller, which gets
; messy with multiple-values, etc.

;; This is no good:
;; (catch 'foo
;;   (handler-case
;;    (throw 'foo 3)
;;    (condition (foo) (format t "Got it ~a" foo))))

;; This works:
;; (catch 'foo
;;   (progn
;;     (block bar
;;       (unwind-protect
;;           (throw 'foo 3)
;;         (return-from bar nil)))
;;     (format t "Did what I want!")))


(defmacro in-main-thread-aux (&rest forms)
  ;; Assumes we have the lock, i.e., the exclusive right to tell the main
  ;; thread what to do.
  (let ((done         (gensym))
        (retvals      (gensym))
        (errval       (gensym))
        (finished     (gensym))
        (saved-stdout (gensym))
        (saved-stdco  (gensym))
        (work         (gensym)))
    `(let* ((,done         (bt-semaphore:make-semaphore))
            (,retvals      nil)
            (,finished     nil)
            (,errval       nil)
            (,saved-stdout *standard-output*)
            (,saved-stdco  *standard-co*)
            (,work
             (lambda ()
               (debug "Main thread is doing its work.~%")
               ;; This is what gets executed in the main thread:
               (let* ((*standard-output* ,saved-stdout)
                      (*trace-output*    ,saved-stdout)
                      (*debug-io*        ,saved-stdout)
                      (*error-output*    ,saved-stdout)
                      (*standard-co*     ,saved-stdco))
                 (with-acl2-channels-bound ,saved-stdco

                   (block try-to-run-it
                     (unwind-protect
                         (handler-case
                          (progn
                            (setq ,retvals (multiple-value-list (progn . ,forms)))
                            (setq ,finished t)
                            (debug "Main thread computed its return values.~%"))
                          (error (condition)
                                 (debug "Main thread trapping error for worker.~%")
                                 (setq ,errval condition)
                                 (setq ,finished t)))
                       ;; Things like THROW can get past the handler-case, but not
                       ;; past the unwind-protect.  Arrrgh...
                       (debug "Main thread computation had non-local exit.~%")
                       (unless ,finished (setq ,errval
                                               (make-condition
                                                'simple-error
                                                :format-control "Unexpected non-local exit.")))
                       (return-from try-to-run-it nil)))

                   (debug "Main thread waking up the worker.~%")
                   (bt-semaphore:signal-semaphore ,done)
                   (debug "Main thread is all done.~%"))))))
       (debug "Installing work for main thread.~%")
       (setq *main-thread-work* ,work)                        ;; Install work for main to find
       (bt-semaphore:signal-semaphore *main-thread-ready*)     ;; Tell main work is there for him
       (debug "Waiting for main thread to finish.~%")
       (bt-semaphore:wait-on-semaphore ,done)                  ;; Wait until main is done
       (when ,errval
         (debug "Got error from the main thread.~%")
         (error ,errval))               ;; Transparently propagate errors
       (debug "Got good values from the main thread.~%")
       (values-list ,retvals))))


(defvar *no-main-thread*
  ;; Gross hack to be able to turn off the main thread for interactive
  ;; scripting modes.  If this is set to T, the main-thread stuff is all just
  ;; turned into progns.
  nil)

(defmacro run-in-main-thread-raw (irrelevant-variable-for-return-last form)
  (declare (ignore irrelevant-variable-for-return-last))
  ;; BOZO this probably isn't quite right w.r.t. values-list, our-multiple-values-bind, etc. nonsense
  ;; But it seems to work on SBCL, at least.
  `(if *no-main-thread*
       ,form
     (bordeaux-threads:with-lock-held
      (*main-thread-lock*)
      (debug "Got the lock, now in main thread.~%")
      (in-main-thread-aux ,form))))

(defmacro try-to-run-in-main-thread-raw (irrelevant-variable-for-return-last form)
  (declare (ignore irrelevant-variable-for-return-last))
  ;; BOZO this probably isn't quite right w.r.t. values-list, our-multiple-values-bind, etc. nonsense
  ;; But it seems to work on SBCL, at least.
  `(cond (*no-main-thread*
          ,form)
         ((not (bordeaux-threads:acquire-lock *main-thread-lock* nil))
          (progn
            (debug "The main thread is busy, giving up.~%")
            (error "The main thread is busy.")))
         (t
          (unwind-protect
              ;; For the lock we just grabbed.
              (progn
                (debug "Main thread wasn't busy, so it's my turn.~%")
                (in-main-thread-aux ,form))
            (debug "Releasing lock on main thread.~%")
            (bordeaux-threads:release-lock *main-thread-lock*)))))


(defun start-fn (socket-name-or-port-number
                 stack-size
                 tstack-size
                 vstack-size)
  ;; Note: stack-size, tstack-size, vstack-size are CCL-specific and ignored on SBCL
  (when (or (/= stack-size  (* 16 (expt 2 20)))
            (/= tstack-size (* 16 (expt 2 20)))
            (/= vstack-size (* 16 (expt 2 20))))
    (format t "; Warning: stack size parameters are CCL-specific and ignored on SBCL.~%"))
  (debug "Setting stack sizes (ignored on SBCL): ~d, ~d, ~d~%" stack-size tstack-size vstack-size)
  ;; Reset shutdown flag from any previous session
  (setq *bridge-shutdown* nil)
  (setq *worker-stack-size* stack-size)
  (setq *worker-vstack-size* tstack-size)
  (setq *worker-tstack-size* vstack-size)
  (unless socket-name-or-port-number
    (setq socket-name-or-port-number bridge-default-port))
  (format t "Starting ACL2 Bridge on ~a, ~a~%"
          (or (sb-ext:posix-getenv "HOSTNAME") "localhost")
          socket-name-or-port-number)
  ;; Track socket path for cleanup (only for Unix domain sockets)
  (setq *bridge-socket-path* (and (stringp socket-name-or-port-number)
                                   socket-name-or-port-number))
  (let ((sock (cond ((natp socket-name-or-port-number)
                     (make-socket-tcp socket-name-or-port-number))
                    ((stringp socket-name-or-port-number)
                     (make-socket-unix socket-name-or-port-number))
                    (t
                     (er hard? 'start-fn "Expected socket-name-or-port-number ~
                                          to be a string (for a socket name) ~
                                          or a natural number (for a tcp/ip ~
                                          port), but found ~x0."
                         socket-name-or-port-number)))))
    (debug "Sock is ~a~%" sock)
    (bordeaux-threads:make-thread (lambda () (listener-thread sock))
                                  :name "bridge-listener"))
  (main-thread-loop)
  nil)


; Interruption Stuff ---------------------------------------------------------
; This is a work in progress.  Probably not ready for production.

(defun find-process (name)
  (loop for p in (bordeaux-threads:all-threads) do
        (if (equal (bordeaux-threads:thread-name p) name)
            (return-from find-process p)
          nil)))

(defun interrupt (name)
  (let ((process (bridge::find-process name)))
    (unless process
      (format *terminal-io* "~a: Can't interrupt ~a, process not found.\n" 
              (bordeaux-threads:thread-name (bordeaux-threads:current-thread))
              name)
      (return-from interrupt nil))
    (bordeaux-threads:interrupt-thread process
                                       (lambda () (error "bridge interrupt")))))


(defun kill-workers ()
  (let ((current (bordeaux-threads:current-thread)))
    (loop for p in (bordeaux-threads:all-threads) do
          (when (and (str::strprefixp "bridge-worker-" (bordeaux-threads:thread-name p))
                     (not (eq p current)))
            (format t "Killing ~a~%" p)
            (bordeaux-threads:destroy-thread p)))))

(defun wake-listener-for-shutdown ()
  "Make a dummy connection to wake up the blocking accept in listener thread.
   This is the hunchentoot pattern for graceful shutdown."
  (when *bridge-socket-path*
    (ignore-errors
      (let ((sock (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
        (unwind-protect
            (sb-bsd-sockets:socket-connect sock *bridge-socket-path*)
          (ignore-errors (sb-bsd-sockets:socket-close sock)))))))

(defun stop ()
  ;; Signal shutdown
  (setq *bridge-shutdown* t)
  
  ;; Wake the listener's blocking accept with a dummy connection
  (wake-listener-for-shutdown)
  
  ;; Wait for listener to exit
  (let ((listener (find-process "bridge-listener")))
    (when listener
      (loop for i from 0 below 30
            while (bordeaux-threads:thread-alive-p listener)
            do (sleep 0.1))
      (when (bordeaux-threads:thread-alive-p listener)
        (bordeaux-threads:destroy-thread listener))))
  
  ;; Don't kill workers here - the worker calling stop() would kill itself
  ;; mid-operation. Workers will exit naturally when their clients disconnect.
  
  ;; Delete the socket file
  (when *bridge-socket-path*
    (ignore-errors (delete-file *bridge-socket-path*))
    (setq *bridge-socket-path* nil))
  
  ;; Wake main-thread-loop so it can exit
  (bt-semaphore:signal-semaphore *main-thread-ready*))
