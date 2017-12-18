; Shellpool - Interface from Common Lisp to External Programs
; Copyright (C) 2014-2015 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

; utils.lisp -- just some utility functions

(let ((sem   (bt-sem:make-semaphore))
      (lock  (bt:make-lock))
      (queue nil))

  (defun msg (msg &rest args)
    "Like format, but safe for printing messages from multiple threads."
    (bt:with-lock-held (lock)
                       (push (cons msg args) queue))
    (bt-sem:signal-semaphore sem))

  (bt:make-thread
   ;; Start up a thread to process MSG calls.
   (lambda ()
     (loop do
           (unless (bt-sem:wait-on-semaphore sem)
             (error "Failed to get the print semaphore."))
           (let ((pair nil))
             (bt:with-lock-held (lock)
                                (setq pair (pop queue)))
             (let ((msg (car pair))
                   (args (cdr pair)))
               (eval `(format t ,msg . ,args))
               (force-output)))))))

(msg "Test message.~%")
(sleep 0.2)

(defun ezrun (cmd)
  "Run a program, ensure it exits with status 0 and prints nothing to stderr,
   and return its stdout output as a string list."
  (let* ((stdout nil)
         (stderr nil)
         (shellpool:*debug* nil)
         (each-line (lambda (line type)
                      (case type
                        (:stdout (push line stdout))
                        (:stderr (push line stderr))
                        (otherwise (error "Bad type ~s for line ~s~%" type line)))))
         (status (shellpool:run cmd :each-line each-line))
         (stdout (nreverse stdout))
         (stderr (nreverse stderr)))
    (when stderr
      (error "Error running ~s: Got lines on stderr: ~s" cmd stderr))
    (when (not (equal status 0))
      (error "Error running ~s: non-zero exit status ~s" cmd status))
    stdout))

(defun list-processes ()
  "Try to get a list of all processes that are currently running.  Used in
   interruption tests."
  ;; BOZO is this conditional needed?
  #+freebsd
  (ezrun "ps ax -o pid,gid,ppid,pgid,command")
  #-freebsd
  ;; This works on at least: Linux, Windows with Cygwin, OpenBSD, Darwin
  (ezrun "ps ax"))

(defun has-process (name)
  "Check if a process is running."
  (let ((all-processes (list-processes)))
    (loop for entry in all-processes do
          (when (shellpool::strpos name entry)
            (format t "Has-process: found match for ~s: ~s~%" name entry)
            (return-from has-process t)))
    (format t "Has-process: no matches for ~s.~%" name)
    nil))

(msg "Testing out has-process.~%")
(sleep 0.2)

;(setq shellpool:*debug* t)

(unless (has-process "bash")
  (error "Doesn't seem like has-process is working right: no bash shells are running."))

(when (has-process "lollipops-dancing-on-my-elbows.exe")
  (error "Doesn't seem like has-process is working right: unlikely process exists."))

(setq shellpool:*debug* nil)
(msg "Has-process seems ok.~%")
(sleep 0.2)
