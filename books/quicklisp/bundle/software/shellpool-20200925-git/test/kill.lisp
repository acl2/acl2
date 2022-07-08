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

; kill.lisp -- tests of killing shellpool processes
;
; I originally wrote this test using two threads, where a RUNNER thread
; executed the task and a CHECKER thread would interrupt the RUNNER by using
; BT:INTERRUPT-THREAD to make it throw a tag.  That worked fine in CCL and
; SBCL, but in Allegro it seems that you are not allowed to cause a non-local
; exit from a thread when you interrupt it, so this did not work at all.
;
; To avoid this, I rewrote the test to be more "cooperative", so that the
; RUNNER thread will throw its own tag when the CHECKER thread was ready.
; Still I wasn't able to get the tests to pass on Allegro, ABCL, and Lispworks,
; and I suspected that multithreading problems were muddying the waters.
;
; I eventually realized I could make the test completely single-threaded,
; (albeit using two shells: one to run the actual program and another to check
; whether programs are running, e.g., see HAS-PROCESS in utils.lisp).
;
; The flow of the test is as follows.  There is only one thread.  The current
; state of the thread is recorded in ST.
;
;     Prepare to catch a SIMULATED-INTERRUPT tag.
;     Invoke the subprogram using shellpool:run.
;
;     Control now enters our each-line callback:
;        Ignore the subprogram's output until we see the ready line.
;        Once we see the ready line:
;           ensure that the subprogram is running (using has-process)
;           throw the SIMULATED-INTERRUPT tag
;
;     This triggers the shellpool kill mechanism and returns control to the
;     top-level DO-TEST function.  (The callback cannot be called any more.)
;
;     Now we simply need to:
;
;      - Ensure that we caught the SIMULATED-INTERRUPT tag instead of getting a
;        normal exit.
;
;      - Ensure that the subprogram got killed as desired (using has-process)
;
;      - Ensure that this all happened within our time bound.

(defparameter *my-interrupt* (cons 'my 'interrupt))

(defun do-test (&key cmd      ; Command to run
                     subname  ; Name of the subprocess that must be killed
                     ready-fn ; Function to determine if it's time to kill
                     max-time ; Time bound in seconds
                     )
  (when (has-process subname)
    (error "Looks like ~s is running already, won't be able to test killing correctly."
           subname))
  (let* ((start-time (get-internal-real-time))
         (step       :start)
         (each-line  (lambda (line type)
                       (declare (ignore type))
                       (format t " - [[Each-Line Got: ~s]]~%" line)
                       (unless (eq step :start)
                         ;; We should never get here because we should have thrown.
                         (error "Thought each-line would have thrown by now."))
                       (cond ((funcall ready-fn line)
                              (format t " - Found ready line.  Ensure ~s is running.~%" subname)
                              (sleep 0.2)
                              (unless (has-process subname)
                                (error "Doesn't seem like ~s got started." subname))
                              (format t " - Looks like ~s is indeed alive (hooray)~%" subname)
                              (setq step :throw)
                              (throw 'simulated-interrupt *my-interrupt*))
                             (t
                              (format t " - Not the ready line, ignoring it.~%")))))
         (result (catch 'simulated-interrupt
                   (progn (format t " - Starting test.~%")
                          (shellpool:run cmd :each-line each-line)))))
    (unless (eq result *my-interrupt*)
      (error "Command exited with result ~s instead of an interrupt." result))
    (sleep .5)
    (when (has-process subname)
      (error "Doesn't seem like ~s got killed." subname))
    (format t " - Program seems sufficiently dead.~%")
    ;; ;; Try to verify that all of the above happened very fast, i.e., we
    ;; ;; didn't just sit around waiting for the command to exit.
    (let* ((end-time (get-internal-real-time))
           (elapsed  (coerce (- end-time start-time) 'float))
           (limit    (* max-time internal-time-units-per-second)))
      (format t " - Test took in ~s seconds.~%" (/ elapsed internal-time-units-per-second))
      (unless (< elapsed limit)
        (error "Seems like that took too long.")))
    (format t "~%")))

(shellpool:start) ;; need a second shell.

; (setq shellpool:*debug* t)

;; Basic check: can we kill the main process that gets launched?  We run this a
;; few times to try to make sure our killing stuff works more than once.
(loop for i from 1 to 5 do
      (format t "*** Starting basic sleep test ~s.~%" i)
      (do-test :cmd "./sleep.pl 15"

               :subname
               ;; For whatever reason, Cygwin's PS command doesn't show this as
               ;; "sleep.pl" but rather shows it as "/usr/bin/perl", so we'll
               ;; look for that process name on Windows.
               #-windows "sleep.pl"
               #+windows "perl"

               :ready-fn (lambda (line)
                           (if (equal line "Sleeping for 15 more seconds.")
                               (progn
                                 (format t " --- Ready to kill.~%")
                                 t)
                             nil))
               :max-time 10))

;; Check of whether we can kill subprocesses that our command launches.
(loop for i from 1 to 5 do
      (format t "*** Starting sleepN test ~s.~%" i)
      (do-test :cmd "./sleepN.sh 15 5"
               :subname
               #-windows "sleep.pl"
               #+windows "perl"
               :ready-fn (lambda (line)
                           (if (equal line "Waiting for sleep.pl processes to finish.")
                               (progn
                                (format t " --- Ready to kill.~%")
                                t)
                             nil))
               :max-time 10))

;; Check whether we can kill off a "bad" process that ignores various kill signals.
(loop for i from 1 to 5 do
      (format t "*** Starting badsleep test ~s.~%" i)
      (do-test :cmd "./badsleep.pl 15"
               :subname
               #-windows "badsleep.pl"
               #+windows "perl"
               :ready-fn (lambda (line)
                           (if (equal line "Sleeping for 15 more seconds.")
                               (progn
                                 (format t " --- Ready to kill.~%")
                                 t)
                             nil))
               :max-time 10))

;; And similarly for a process that launches "bad" processes.
(loop for i from 1 to 5 do
      (format t "*** Starting badsleepN test ~s.~%" i)
      (do-test :cmd "./badsleepN.sh 15 5"
               :subname
               #-windows "badsleep.pl"
               #+windows "perl"
               :ready-fn (lambda (line)
                           (if (equal line "Waiting for badsleep.pl processes to finish.")
                               (progn
                                 (format t " --- Ready to kill.~%")
                                 t)
                             nil))
               :max-time 10))


