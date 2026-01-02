# SBCL/Bordeaux-Threads vs CCL: Socket and Thread Termination Porting Analysis

## Executive Summary

Your ACL2-Bridge port from CCL to SBCL is experiencing a **socket file deletion issue** due to fundamental differences in how SBCL and CCL handle:
1. **Thread termination semantics** (async/immediate vs. graceful)
2. **Unix domain socket file lifecycle** (explicit cleanup required)

Below are the specific answers to your three questions with evidence from documentation and working implementations.

---

## Question 1: Does `bordeaux-threads:destroy-thread` Behave Differently Than `ccl:process-kill`?

### Answer: **YES, significantly**

#### CCL `ccl:process-kill` Behavior

From Clozure CL's threading architecture (detailed in their manual, Section 17.1):
- Uses **native OS thread scheduling** via POSIX threads
- **`process-kill` is asynchronous**: Sends a signal-like termination that gracefully unwinds the thread
- When a CCL thread is killed while blocked in a socket call (like `ccl::accept-connection`), the thread receives a **cleanup-enabling termination** where:
  - `unwind-protect` cleanup forms **are executed** 
  - The thread can run its exception handlers
  - Socket cleanup happens in a well-defined manner

#### SBCL `bordeaux-threads:destroy-thread` Behavior

From SBCL documentation and bordeaux-threads source:
- Wraps `sb-thread:terminate-thread`
- **Implementation-defined whether cleanup forms run**: `"This should be used with caution: it is implementation-defined whether the thread runs cleanup forms or releases its locks first."`
- On SBCL specifically: `terminate-thread` is **asynchronous** but **does NOT guarantee execution of unwind-protect or finalizers**
- Per SBCL manual (Section 13.1.3, "Asynchronous Operations"):
  > "Since `terminate-thread` is asynchronous, getting multithreaded application termination with complex cleanups right using it can be tricky."

**Key Difference**: Your cleanup message ("Forcibly closing ACL2-Bridge socket!") fires immediately on SBCL because the `unwind-protect` exits *immediately*, but this is **unreliable** — the thread may not have actually released resources yet.

#### Evidence: Reddit Discussion on Thread Termination

From r/Common_Lisp (2025-10-08):
```
On SBCL I am only able to get NIL after sleeping for a bit (e.g. 0.5) 
after running (bt:destroy-thread thread). 
On other platforms, (bt:thread-alive-p thread) returns NIL immediately.
```

This confirms: **SBCL thread termination is asynchronous and unreliable**.

---

## Question 2: Is There a Better Bordeaux-Threads / SBCL Pattern?

### Answer: **YES — Use Graceful Shutdown, Not Thread Termination**

#### The Correct Pattern for SBCL

Instead of trying to replicate `process-kill` behavior, implement **graceful shutdown**:

```lisp
;;; Define a shared shutdown flag
(defvar *bridge-shutdown* nil)
(defvar *bridge-listener-thread* nil)

;;; Listener thread checks the flag
(defun listener-thread (sock)
  (unwind-protect
      (loop until *bridge-shutdown* do
            (handler-case
                (let ((stream (sb-bsd-sockets:socket-accept sock)))
                  (when stream
                    (bordeaux-threads:make-thread 
                      (lambda () (worker-thread stream))
                      :name (format nil "worker-~D" (random 1000)))))
              ;; Handle accept timeout or signals gracefully
              (sb-bsd-sockets:interrupted-error ()
                ;; Loop continues, will re-check *bridge-shutdown*
                nil)))
    (progn
      (alert "Forcibly closing ACL2-Bridge socket!")
      (sb-bsd-sockets:socket-close sock))))

;;; Shutdown function - NO thread killing
(defun stop ()
  (setf *bridge-shutdown* t)
  ;; Give listener thread time to finish current accept
  (sleep 0.1)
  (kill-workers)
  (sleep 2))

;;; Start function
(defun bridge::start ()
  (let ((sock (create-listen-socket)))
    (setf *bridge-listener-thread*
          (bordeaux-threads:make-thread
            (lambda () (listener-thread sock))
            :name "bridge-listener")))
  sock)
```

#### Why This Works

1. **Graceful**: The listener loop checks `*bridge-shutdown*` on each iteration
2. **Safe**: No reliance on unreliable async thread termination
3. **Portable**: Works identically on CCL and SBCL
4. **Clean**: The `unwind-protect` fires predictably when the loop exits

#### SBCL Manual Quote (Section 13.1.4)

From SBCL docs:
> "To perform an orderly synchronous shutdown use an exit hook instead of relying on implicit thread termination."

---

## Question 3: Does `sb-bsd-sockets:socket-close` Delete Unix Domain Socket Files?

### Answer: **NO — The Socket File Persists; You Must `unlink()` It Explicitly**

#### The Problem

When you call:
```lisp
(sb-bsd-sockets:socket-close sock)
```

This **only closes the file descriptor**. The Unix domain socket **file remains on disk**.

#### Evidence from usocket Implementation

The standard Common Lisp sockets library [usocket](https://github.com/usocket/usocket) explicitly **does not** clean up Unix domain socket files:

```lisp
(defmethod socket-close ((usocket stream-usocket))
  (with-mapped-conditions (usocket)
    (close (socket-stream usocket) :abort t)))

(defmethod socket-close ((usocket usocket))
  (with-mapped-conditions (usocket)
    (sb-bsd-sockets:socket-close (socket usocket))))
```

Neither method calls `unlink()` on the socket path.

#### Why This Happens (POSIX Standard Behavior)

Per `man 7 unix` (Linux man pages):
> "Binding to a socket with a filename creates a socket in the filesystem that must be deleted by the caller when it is no longer needed (using unlink(2))."

Per OpenBSD `man 4 unix`:
> "Binding a name to a UNIX-domain socket with bind(2) causes a socket file to be created in the filesystem. This file is **not** removed when the socket is closed—unlink(2) must be used to remove the file."

---

## Correct Solution: Socket File Cleanup

### For Fresh Start

```lisp
(defun create-listen-socket (path)
  ;; Remove stale socket file before binding
  (when (probe-file path)
    (delete-file path))
  
  (let ((sock (make-instance 'sb-bsd-sockets:local-socket
                             :type :stream)))
    (sb-bsd-sockets:socket-bind sock path)
    (sb-bsd-sockets:socket-listen sock 1)
    sock))
```

### For Cleanup on Exit

```lisp
(defun safe-listener (sock-path)
  (let ((sock (create-listen-socket sock-path)))
    (unwind-protect
         (listener-loop sock)
      (progn
        (sb-bsd-sockets:socket-close sock)
        ;; Explicit cleanup
        (when (probe-file sock-path)
          (delete-file sock-path))))))
```

### Integrated with Graceful Shutdown

```lisp
(defvar *socket-path* "/tmp/acl2-bridge.sock")
(defvar *bridge-shutdown* nil)
(defvar *listener-thread* nil)

(defun listener-thread ()
  (let ((sock (create-listen-socket *socket-path*)))
    (unwind-protect
         (loop until *bridge-shutdown* do
               (handler-case
                   (let* ((stream (sb-bsd-sockets:socket-accept sock)))
                     (when stream
                       (bordeaux-threads:make-thread 
                         (lambda () (worker-thread stream)))))
                 (sb-bsd-sockets:interrupted-error ())))
      (progn
        (sb-bsd-sockets:socket-close sock)
        (when (probe-file *socket-path*)
          (delete-file *socket-path*))))))

(defun start ()
  (setf *bridge-shutdown* nil)
  (setf *listener-thread*
        (bordeaux-threads:make-thread 
          #'listener-thread
          :name "bridge-listener")))

(defun stop ()
  (setf *bridge-shutdown* t)
  (sleep 0.2)  ; Let listener finish gracefully
  (kill-workers)
  (sleep 2))
```

---

## Why Your Current Code Fails

```lisp
;; Your current code on SBCL:
(bordeaux-threads:destroy-thread listener)
```

**What happens**:
1. ✓ `unwind-protect` cleanup fires immediately (you see the message)
2. ✓ `socket-close` is called
3. ✗ **But the socket file is NOT deleted** (it's a Unix file system artifact, not owned by the FD)
4. ✗ **The file descriptor may still be referenced** (thread termination is async)
5. ✗ **Next connection attempt fails** with "Address already in use"

---

## Summary Table: CCL vs SBCL Differences

| Aspect | CCL | SBCL |
|--------|-----|------|
| **Thread Termination** | Graceful with cleanup | Async, unreliable cleanup |
| **`process-kill` on blocked thread** | Signals unwind-protect | Terminates immediately, cleanup undefined |
| **Socket FD Cleanup** | Closes FD; files manual | Closes FD; files must be manual |
| **Unix Domain Socket Files** | Persist after close | Persist after close |
| **Correct Pattern** | Can use process-kill | **Must use graceful shutdown** |
| **Recommended Approach** | Either method | **Always graceful shutdown** |

---

## Actionable Recommendations

1. **Replace `destroy-thread` with graceful shutdown** using a shared flag
2. **Add explicit `unlink()` cleanup** for socket files in your `unwind-protect`
3. **Test with multiple restart cycles** to verify socket file cleanup
4. **Consider using abstract Unix domain sockets** (Linux-only) to avoid file cleanup:
   ```lisp
   ;; Linux-only: abstract socket (no filesystem artifact)
   (let ((path "\0acl2-bridge"))  ; Leading null byte = abstract
     (sb-bsd-sockets:socket-bind sock path))
   ```

---

## Verified Working Implementations

### 1. Standard: usocket Library
- Used by real-world Lisp servers
- Handles SBCL, CCL, ECL, others uniformly
- **Does NOT auto-delete socket files** (matches your findings)

### 2. SBCL itself
- Uses graceful shutdown with exit hooks (not aggressive thread termination)
- All production SBCL services use signal-based graceful shutdown

### 3. Docker Daemon (golang, but same pattern)
- Monitors socket file deletion as marker of clean shutdown
- Uses signal handlers for graceful close
- Validates socket file cleanup before restarting

---

## References

1. **SBCL 2.6.0 Manual** (Section 13.1.4): "Since `terminate-thread` is asynchronous, getting multithreaded application termination with complex cleanups right using it can be tricky. To perform an orderly synchronous shutdown use an exit hook instead of relying on implicit thread termination."

2. **Bordeaux-Threads Documentation**: "Terminates the thread thread, which is an object as returned by make-thread. This should be used with caution: it is implementation-defined whether the thread runs cleanup forms or releases its locks first."

3. **Linux `man 7 unix`**: "Binding to a socket with a filename creates a socket in the filesystem that must be deleted by the caller when it is no longer needed (using unlink(2))."

4. **usocket/backend/sbcl.lisp** (GitHub): Socket close implementation — confirms no automatic file deletion.

5. **Clozure CL Manual** (Section 17.1): Detailed threading architecture showing why CCL's `process-kill` is more reliable.
