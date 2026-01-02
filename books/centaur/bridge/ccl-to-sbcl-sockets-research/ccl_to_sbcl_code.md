# CCL vs SBCL: Exact Code Differences for ACL2-Bridge Port

This document shows side-by-side comparisons of how to port CCL-specific code to SBCL.

---

## 1. Basic Thread Spawning

### CCL (Original)
```lisp
(defun listener-thread (sock)
  (loop for n from 0 do
    (let* ((stream (ccl::accept-connection sock)))
      (ccl::process-run-function ... 'worker-thread stream))))

;; Somewhere else:
(ccl::process-run-function "bridge-listener" nil #'listener-thread sock)
```

### SBCL (Correct Port)
```lisp
(defun listener-thread ()
  (let ((sock (create-listen-socket *socket-path*)))
    (unwind-protect
         (loop until *bridge-shutdown* do
           (handler-case
               (let ((stream (sb-bsd-sockets:socket-make-stream
                              (sb-bsd-sockets:socket-accept sock)
                              :input t :output t)))
                 (when stream
                   (bordeaux-threads:make-thread
                     (lambda () (worker-thread stream))
                     :name (format nil "acl2-worker-~A" (random 1000)))))
             (sb-bsd-sockets:interrupted-error () nil)))
      (sb-bsd-sockets:socket-close sock)
      (cleanup-socket-file *socket-path*))))

;; To start:
(bordeaux-threads:make-thread #'listener-thread :name "acl2-bridge-listener")
```

**Key Differences**:
- CCL: Uses `ccl::process-run-function` which handles thread naming and setup
- SBCL: Must manually call `bordeaux-threads:make-thread` with explicit name
- CCL: `ccl::accept-connection` blocks until connection arrives
- SBCL: `sb-bsd-sockets:socket-accept` + `socket-make-stream` (two-step)
- SBCL: Must explicitly check `*bridge-shutdown*` flag for graceful exit

---

## 2. Thread Termination

### CCL (Original) — Works Reliably
```lisp
(defun stop ()
  (let ((listener (ccl::find-process "bridge-listener")))
    (when listener
      (ccl::process-kill listener)))    ; <-- Synchronous, guarantees cleanup
  (kill-workers)
  (sleep 2))
```

### SBCL (WRONG - Do NOT Do This)
```lisp
(defun stop ()
  (let ((listener (find-thread-by-name "bridge-listener")))
    (when listener
      (bordeaux-threads:destroy-thread listener)))  ; <-- PROBLEMATIC!
  (kill-workers)
  (sleep 2))

;; PROBLEM: unwind-protect fires immediately, but socket file NOT deleted
;; Result: Next start() fails with "Address already in use"
```

### SBCL (CORRECT - Graceful Shutdown)
```lisp
(defun stop ()
  ;; Signal graceful shutdown - listener loop will check this
  (setf *bridge-shutdown* t)
  
  ;; Give listener thread time to:
  ;; 1. Exit its accept() call
  ;; 2. Run its unwind-protect cleanup
  ;; 3. Close socket
  ;; 4. Delete socket file
  (sleep 0.2)
  
  ;; Kill worker threads
  (kill-all-workers)
  
  ;; If listener is still alive, force termination (should rarely happen)
  (when (bordeaux-threads:thread-alive-p *listener-thread*)
    (bordeaux-threads:destroy-thread *listener-thread*))
  
  nil)
```

**Critical Difference**: 
- CCL: `process-kill` is **synchronous** and **reliable**; cleanup is guaranteed
- SBCL: `destroy-thread` is **asynchronous** and **unreliable**; use **graceful shutdown flag instead**

---

## 3. Socket Creation and Binding

### CCL (Original)
```lisp
(let* ((sock (ccl:make-socket :address-family :file
                              :type :stream
                              :name socket-path)))
  ;; Automatically binds to socket-path
  (ccl::accept-connection sock))
```

### SBCL (Equivalent)
```lisp
(let ((sock (make-instance 'sb-bsd-sockets:local-socket
                           :type :stream)))
  ;; Must manually bind
  (sb-bsd-sockets:socket-bind sock socket-path)
  ;; Must manually listen
  (sb-bsd-sockets:socket-listen sock 1)
  
  ;; Accept connection
  (sb-bsd-sockets:socket-accept sock))
```

**Key Difference**: SBCL requires explicit three-step process (create → bind → listen).

---

## 4. Socket File Cleanup (The Hidden Issue)

### CCL (Original)
```lisp
;; When CCL closes a socket:
(close sock)  ; or (ccl:close sock :abort t)

;; Socket file cleanup is NOT automatic, but CCL's process-kill
;; happens synchronously so cleanup code can delete it:
(defun listener-cleanup ()
  (unwind-protect
       (loop ...)
    (progn
      (close sock)
      ;; Socket file cleanup happens here, synchronously
      (delete-file socket-path))))
```

### SBCL (REQUIRED - Explicit Cleanup)
```lisp
;; When SBCL closes a socket:
(sb-bsd-sockets:socket-close sock)  ; Closes FD but NOT filesystem file!

;; You MUST explicitly delete the socket file:
(defun cleanup-socket-file (path)
  (when (probe-file path)
    (delete-file path)))

;; In unwind-protect:
(unwind-protect
     (loop ...)
  (progn
    (sb-bsd-sockets:socket-close sock)
    ;; MUST do this - socket-close doesn't!
    (cleanup-socket-file *socket-path*)))
```

**Why This Matters**: 
- Unix domain sockets create **filesystem files**
- Closing the file descriptor doesn't delete the file
- You must call `unlink()` (Lisp: `delete-file`) explicitly
- This is standard POSIX behavior, not a bug

### Evidence: What Happens Without Cleanup

```lisp
;; First run:
(bridge::start)   ; Socket file created: /tmp/acl2-bridge.sock
(bridge::stop)    ; Socket file LEFT BEHIND

;; Second run:
(bridge::start)   ; ERROR: Address already in use!
                  ;  ← Because /tmp/acl2-bridge.sock still exists

;; Solution: Delete it first (or implement cleanup in stop())
(delete-file "/tmp/acl2-bridge.sock")
(bridge::start)   ; ✓ Works now
```

---

## 5. Socket Acceptance and Stream Creation

### CCL (Original)
```lisp
(let* ((stream (ccl::accept-connection sock)))
  ;; stream is immediately usable for I/O
  (read-line stream))
```

### SBCL (Two-Step)
```lisp
(let* ((connected-socket (sb-bsd-sockets:socket-accept sock))
       (stream (sb-bsd-sockets:socket-make-stream connected-socket
                 :input t :output t :buffering :full)))
  ;; stream is now usable for I/O
  (read-line stream))
```

---

## 6. Error Handling

### CCL (Original) — Aggressive Approach
```lisp
(handler-case
    (loop do
      (let ((stream (ccl::accept-connection sock)))
        (ccl::process-run-function 'worker stream)))
  (error (e)
    (format t "Fatal error: ~A~%" e)
    (return)))  ; Exit on any error
```

### SBCL (Correct) — Resilient Approach
```lisp
(loop until *bridge-shutdown* do
  (handler-case
      (let ((stream (sb-bsd-sockets:socket-make-stream
                      (sb-bsd-sockets:socket-accept sock)
                      :input t :output t)))
        (when stream
          (bordeaux-threads:make-thread 
            (lambda () (worker-thread stream)))))
    ;; Interrupted accept (timeout, signal) — just continue
    (sb-bsd-sockets:interrupted-error ()
      nil)
    ;; Timeout on accept — just retry
    (sb-bsd-sockets:operation-timeout-error ()
      nil)
    ;; Unexpected error — log but continue listening
    (error (e)
      (format t "Accept error: ~A (continuing)~%" e))))
```

**Difference**: SBCL listener should be **resilient** — individual connection errors shouldn't crash the listener.

---

## 7. Thread Registry (New Required Pattern for SBCL)

### CCL (Original)
```lisp
;; CCL's process model makes it easy to find/manage processes
(ccl::find-process "bridge-listener")
(ccl::all-processes)
```

### SBCL (Must Implement Manually)
```lisp
;; You need explicit thread tracking
(defvar *worker-threads* (make-hash-table))
(defvar *worker-lock* (bordeaux-threads:make-lock))

(defun register-worker (thread-obj)
  (bordeaux-threads:with-lock-held (*worker-lock*)
    (setf (gethash thread-obj *worker-threads*) t)))

(defun kill-all-workers ()
  (bordeaux-threads:with-lock-held (*worker-lock*)
    (dolist (thread (loop for t being the hash-keys of *worker-threads*
                          collect t))
      (when (bordeaux-threads:thread-alive-p thread)
        (bordeaux-threads:destroy-thread thread))))
  (sleep 0.5))

;; Usage in worker-thread:
(let ((thread-obj (bordeaux-threads:current-thread)))
  (register-worker thread-obj)
  (unwind-protect
       (your-work)
    (unregister-worker thread-obj)))
```

---

## 8. Complete Comparison: Full start/stop Lifecycle

### CCL Version
```lisp
;;; CCL: Process-based, built-in process management

(defvar *listener-process* nil)
(defvar *socket-path* "/tmp/acl2-bridge.sock")

(defun start-listener ()
  (setf *listener-process*
        (ccl:process-run-function "bridge-listener" nil
                                 #'listener-thread)))

(defun listener-thread ()
  (let ((sock (ccl:make-socket :address-family :file
                               :type :stream
                               :name *socket-path*)))
    (unwind-protect
         (loop do
           (let ((stream (ccl::accept-connection sock)))
             (ccl::process-run-function 'worker-thread stream)))
      (close sock))))

(defun stop-listener ()
  (ccl::process-kill *listener-process*)
  (setf *listener-process* nil))
```

**CCL Strengths**:
- ✓ Process-kill is synchronous and reliable
- ✓ Built-in process naming and discovery
- ✓ Cleaner API overall

---

### SBCL Version
```lisp
;;; SBCL: Thread-based, requires explicit management

(defvar *bridge-shutdown* nil)
(defvar *listener-thread* nil)
(defvar *worker-threads* (make-hash-table))
(defvar *socket-path* "/tmp/acl2-bridge.sock")

(defun start-listener ()
  (setf *bridge-shutdown* nil)
  (setf *listener-thread*
        (bordeaux-threads:make-thread #'listener-thread
                                      :name "bridge-listener")))

(defun listener-thread ()
  (let ((sock (create-listen-socket *socket-path*)))
    (unwind-protect
         (loop until *bridge-shutdown* do
           (handler-case
               (let ((stream (sb-bsd-sockets:socket-make-stream
                              (sb-bsd-sockets:socket-accept sock)
                              :input t :output t)))
                 (when stream
                   (let ((worker (bordeaux-threads:make-thread
                                   (lambda () (worker-thread stream)))))
                     (register-worker worker))))
             (sb-bsd-sockets:interrupted-error () nil)
             (error (e) (format t "Error: ~A~%" e))))
      (progn
        (sb-bsd-sockets:socket-close sock)
        (cleanup-socket-file *socket-path*)))))

(defun stop-listener ()
  (setf *bridge-shutdown* t)
  (sleep 0.2)
  (kill-all-workers)
  (when (bordeaux-threads:thread-alive-p *listener-thread*)
    (bordeaux-threads:destroy-thread *listener-thread*))
  (setf *listener-thread* nil))

(defun create-listen-socket (path)
  (when (probe-file path) (delete-file path))
  (let ((sock (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
    (sb-bsd-sockets:socket-bind sock path)
    (sb-bsd-sockets:socket-listen sock 1)
    sock))

(defun cleanup-socket-file (path)
  (when (probe-file path) (delete-file path)))

(defun register-worker (thread)
  (setf (gethash thread *worker-threads*) t))

(defun kill-all-workers ()
  (loop for thread being the hash-keys of *worker-threads*
        do (when (bordeaux-threads:thread-alive-p thread)
             (bordeaux-threads:destroy-thread thread)))
  (sleep 0.5)
  (clrhash *worker-threads*))
```

**SBCL Differences**:
- ✗ Must manually manage shutdown flag
- ✗ Must manually track worker threads
- ✗ Must explicitly clean up socket files
- ✗ Error handling must be more robust
- ✓ Actually more portable across Lisp implementations

---

## Migration Checklist

When porting from CCL to SBCL:

- [ ] Replace `ccl::process-run-function` with `bordeaux-threads:make-thread`
- [ ] Replace `ccl:find-process` / `ccl:all-processes` with manual thread registry
- [ ] Replace `ccl:process-kill` with graceful shutdown flag pattern
- [ ] Add explicit socket file cleanup in `unwind-protect`
- [ ] Add error handling to listener loop (handle interrupts gracefully)
- [ ] Test that socket file is deleted on every `stop()` call
- [ ] Test that multiple start/stop cycles work without "Address in use" errors
- [ ] Verify all worker threads are cleaned up before next start

---

## Testing: Verify the Fix

```bash
# Terminal 1: Start Lisp
sbcl --load "your-bridge.lisp"
CL-USER> (bridge::start)
[ACL2-BRIDGE] ACL2-Bridge listener started

# Terminal 2: Test connection
$ ls -la /tmp/acl2-bridge.sock
-rw-------  1 user  group  0 Jan  1 12:34 /tmp/acl2-bridge.sock
$ echo "test" | socat - UNIX-CONNECT:/tmp/acl2-bridge.sock

# Terminal 1: Stop
CL-USER> (bridge::stop)
[ACL2-BRIDGE] Forcibly closing ACL2-Bridge socket!

# Terminal 2: Verify cleanup
$ ls -la /tmp/acl2-bridge.sock
ls: /tmp/acl2-bridge.sock: No such file or directory    ✓ Correct!

# Terminal 1: Restart (should work without errors)
CL-USER> (bridge::start)
[ACL2-BRIDGE] ACL2-Bridge listener started       ✓ Works!
```

This verifies that socket file cleanup is working correctly.
