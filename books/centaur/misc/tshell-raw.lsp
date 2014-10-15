; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Tshell
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; NOTE: This file requires that str/strprefixp has been loaded.

(defvar *tshell-debug*
  ;; Change this to T for verbose debugging information.
  nil)

(defmacro tshell-debug (&rest args)
  `(when *tshell-debug* (format t ,@args)))


; We look for certain strings to know when the program's output ends.  This is
; gross, but in practice it should work.

(defvar *tshell-exit-line*   "HORRIBLE_STRING_TO_DETECT_END_OF_TSHELL_COMMAND")
(defvar *tshell-status-line* "HORRIBLE_STRING_TO_DETECT_TSHELL_EXIT_STATUS")
(defvar *tshell-pid-line*    "TSHELL_PID")


; We actually use two bash processes.  *tshell* runs the programs.
; *tshell-killer* is only used to kill programs that *tshell* is running.

; Bug fix 2013-09-17: these were formerly uninitialized defvars, but Matt
; pointed out that tshell-ensure is assuming they are initialized, so set
; them to nil.

(defvar *tshell* nil)
(defvar *tshell-killer* nil)

; I added another bash process for background jobs.  This seems easier than
; running them with *tshell*.

(defvar *tshell-bg* nil)


(defun tshell-stop ()
  ;; Stops any tshell processes that are running.

  #-(and Clozure (not mswindows))
  ;; BOZO maybe eventually add support for other Lisps
  nil

  #+(and Clozure (not mswindows))
  (progn (ignore-errors
           (when *tshell*
             (tshell-debug "TSHELL-STOP: stopping *tshell*~%")
             (ccl::signal-external-process *tshell* 9)
             (setq *tshell* nil)))
         (ignore-errors
           (when *tshell-killer*
             (tshell-debug "TSHELL-STOP: stopping *tshell-killer*~%")
             (ccl::signal-external-process *tshell-killer* 9)
             (setq *tshell-killer* nil)))
         (ignore-errors
           (when *tshell-bg*
             (tshell-debug "TSHELL-STOP: stopping *tshell-bg*~%")
             (ccl::signal-external-process *tshell-bg* 9)
             (setq *tshell-bg* nil)))
         nil))

(defun tshell-start ()
  ;; Stops any tshell processes and starts new ones.

  #-(and Clozure (not mswindows))
  ;; BOZO maybe eventually add support for other Lisps
  nil

  #+(and Clozure (not mswindows))
  (progn (tshell-debug "TSHELL-START: killing old processes~%")
         (tshell-stop)
         (tshell-debug "TSHELL-START: starting *tshell*~%")
         (setf *tshell* (ccl::run-program "/bin/bash" nil
                                          :wait nil
                                          :input :stream
                                          :output :stream
                                          :error :stream))
         (tshell-debug "TSHELL-START: starting *tshell-killer*~%")
         (setf *tshell-killer* (ccl::run-program "/bin/bash" nil
                                                 :wait nil
                                                 :input :stream
                                                 :output :stream
                                                 :error :stream))
         (tshell-debug "TSHELL-START: starting *tshell-bg*~%")
         (setf *tshell-bg* (ccl::run-program "/bin/bash" nil
                                             :wait nil
                                             :input :stream
                                             :output nil
                                             :error nil))
         nil))

(defun tshell-check ()
  #-(and Clozure (not mswindows))
  t
  #+(and Clozure (not mswindows))
  (and (ccl::external-process-p *tshell*)
       (ccl::external-process-p *tshell-killer*)
       (ccl::external-process-p *tshell-bg*)
       (eq (ccl::external-process-status *tshell*) :running)
       (eq (ccl::external-process-status *tshell-killer*) :running)
       (eq (ccl::external-process-status *tshell-bg*) :running)))

(defun tshell-ensure ()
  ;; Stops any tshell processes and starts new ones.
  #-(and Clozure (not mswindows))
  ;; BOZO eventually add support for other Lisps
  nil
  #+(and Clozure (not mswindows))
  (unless (tshell-check)
    (tshell-debug "TSHELL-START: starting *tshell*~%")
    (setf *tshell* (ccl::run-program "/bin/bash" nil
                                     :wait nil
                                     :input :stream
                                     :output :stream
                                     :error :stream))
    (tshell-debug "TSHELL-START: starting *tshell-killer*~%")
    (setf *tshell-killer* (ccl::run-program "/bin/bash" nil
                                            :wait nil
                                            :input :stream
                                            :output :stream
                                            :error :stream))
    (tshell-debug "TSHELL-START: starting *tshell-bg*~%")
    (setf *tshell-bg* (ccl::run-program "/bin/bash" nil
                                        :wait nil
                                        :input :stream
                                        :output nil
                                        :error nil)))
  nil)

(defun tshell-parse-status-line (line)
  ;; Returns (PREFIX STATUS)
  ;; If it's an exit line, PREFIX is anything that was printed before the
  ;; exit message stuff (which can happen when the command doesn't print a
  ;; newline at the end of its output), and STATUS is an integer that gives
  ;; the exit status code.
  ;; If it's not an exit line, PREFIX and STATUS are both NIL.
  (let ((pos (str::strpos *tshell-status-line* line)))
    (if (not pos)
        (values nil nil)
      (progn
        (tshell-debug "Found status line: ~a~%" line)
        (let ((prefix (subseq line 0 pos))
              (suffix (subseq line (+ 1 (length *tshell-status-line*) pos))))
          (multiple-value-bind (val next-pos)
              (parse-integer suffix)
            (declare (ignore next-pos))
            (values prefix val)))))))

(defun tshell-parse-pid-line (line)
  ;; Given a line like TSHELL_PID 1234, we return 1234.
  (tshell-debug "Parsing PID line: ~a~%" line)
  (unless (str::strprefixp *tshell-pid-line* line)
    (error "TSHELL error: bad pid line: ~a." line))
  (multiple-value-bind (val pos)
      (parse-integer (subseq line (+ 1 (length *tshell-pid-line*))))
    (declare (ignore pos))
    val))

#+(and Clozure (not mswindows))
(defun tshell-kill (pid)
  ;; Use the tshell-killer process to try to kill process PID.
  (tshell-debug "TSHELL-KILL: killing ~a.~%" pid)
  (let* ((killer-in (ccl::external-process-input-stream *tshell-killer*)))

; Wow, this is tricky.  Want to kill not only the process, but all processes
; that it spawns.  To do this:
;   1. First look up the process's parent, i.e., the bash that is running
;      inside of *tshell*.
;   2. Find all processes with *tshell* as their parent, removing *tshell*
;      itself.
;   3. Kill everything found in 2.

    (format killer-in "PARENT=`ps -o pgrp ~a | tail -1`~%" pid)
    (format killer-in "NOT_PARENT=`pgrep -g $PARENT | grep -v $PARENT`~%")
    (format killer-in "kill -9 $NOT_PARENT~%")
    (force-output killer-in)))

(defun tshell-echo (line buf stream)

; This is how tshell prints output from the sub-program using :print t.
;
; We originally put this in a separate function so that it can be redefined.
; Now there's no reason to do that because you can give a custom argument to
; :print.  But your function should be signature-compatible with tshell-echo.
;
; Note: Redefined in transistor/equiv-check (Centaur internal), so don't change
; it unless you update that, too.
;
; We could probably make this more general.  At least it's better than it was
; before.

  (declare (ignorable buf))
  (write-line line stream)
  (force-output stream))

(defun tshell-echo-alldone (stream)
  (declare (ignorable stream))

; Called by tshell after all the output has been printed with tshell-echo, in
; case tshell-echo wants to not print newlines right away.  BOZO this doesn't
; really fit into our output filtering scheme.  Fortunately it isn't being used
; by anything anymore.  (It was used as part of the original AIGPU to implement
; some carriage-return hacks, but that's all deprecated now.)

  nil)

(defun tshell-call-fn (cmd print save)
  ;; See the documentation in tshell.lisp.

  (unless (tshell-check)
    (error "Invalid *tshell*, *tshell-killer*, or *tshell-bg* -- did you call (tshell-start)?"))

  #-(and Clozure (not mswindows))
  (error "Oops, TSHELL isn't implemented for this Lisp.")

  #+(and Clozure (not mswindows))
  (let* ((tshell-in     (ccl::external-process-input-stream *tshell*))
         (tshell-out    (ccl::external-process-output-stream *tshell*))
         (tshell-err    (ccl::external-process-error-stream *tshell*))
         (pid           0)
         (exit-status   1)
         (line          nil)
         (stdout-exit   nil)
         (stderr-exit   nil)
         (buf           nil)
         (print         (if (eq print t) 'tshell-echo print))
         (stream        (get-output-stream-from-channel *standard-co*))


; To run a command, we basically tell our bash shell to execute:
;
;    (cmd < /dev/null 2>&1 ; echo EXIT_STATUS $?) &
;    echo TSHELL_PID $! 1>&2
;    wait
;    echo END_STRING
;    echo END_STRING 1>&2
;
; The EXIT_STATUS printing must be associated with CMD, so that waiting and
; such will work.
;
; The TSHELL_PID line lets us read the PID for the child process on the first
; line of stderr, and hence we can kill it if we are interrupted.  It will
; actually hold the PID for the subshell containing both the command and echo
; statement.
;
; The horrible strings we print are used to determine when we've reached the
; end of the output associated with this command.  Of course, there's no
; guarantee that the program itself doesn't emit these strings, but in practice
; it won't happen.

         (nl  (coerce (list #\Newline) 'string))
         (cmd (concatenate 'string
              "(" cmd " < /dev/null 2>&1 ; echo " *tshell-status-line* " $? ) &" nl
               "echo " *tshell-pid-line* " $! 1>&2" nl
               "wait" nl
               "echo " *tshell-exit-line* nl
               "echo " *tshell-exit-line* " 1>&2" nl)))

    (tshell-debug "TSHELL_RUN~%~a~%" cmd)

    (write-line cmd tshell-in)
    (finish-output tshell-in)

    (setq pid (tshell-parse-pid-line (read-line tshell-err)))

    (tshell-debug "PID is ~a.~%" pid)

    (unwind-protect

        (progn
          ;; Read command output until we find the exit line.
          (loop do
                (block continue
                  (setq line (read-line tshell-out))
                  (tshell-debug "** raw tshell stdout line: ~a~%" line)

                  (multiple-value-bind
                      (prefix code)
                      (tshell-parse-status-line line)
                    (tshell-debug "** attempt to parse exit status: prefix=~a, code=~a~%"
                                  prefix code)
                    (when code
                      (tshell-debug "TSHELL_STATUS is ~a.~%" code)
                      (setq exit-status code)

                      ;; Gah, so totally gross -- keep in sync with 'line'
                      ;; handling below
                      (unless (equal prefix "")
                        (when print
                          (funcall print prefix buf stream))
                        (when save
                          (push prefix buf)))
                      (return-from continue)))

                  (when (equal line *tshell-exit-line*)
                    (tshell-debug "TSHELL_EXIT on STDOUT~%")
                    (setq stdout-exit t)
                    (loop-finish))

                  ;; Keep in sync with 'prefix' handling above
                  (when print
                    (funcall print line buf stream))
                  (when save
                    (push line buf))))

          ;; Read stderr until we find the exit line.
          (loop do
                (setq line (read-line tshell-err))
                (tshell-debug "** raw tshell stderr line: ~a~%" line)
                (when (equal line *tshell-exit-line*)
                  (tshell-debug "TSHELL_EXIT on STDERR: ~a~%" line)
                  (setq stderr-exit t)
                  (loop-finish))
                (tshell-debug "TSHELL_ERR: ~a.~%" line)))

      (progn
        ;; Cleanup in case of interrupts.
        (when (not stdout-exit)
          (format t "~%; Note: tshell shutting down process ~a.~%" pid)
          (tshell-kill pid)
          (loop do
                (setq line (read-line tshell-out))
                (when (str::strsuffixp *tshell-exit-line* line)
                  ;; We used to try to match *tshell-exit-line* exactly, but
                  ;; then we found that if we interrupt while the program has
                  ;; printed partial output, we can end up with a situation
                  ;; like:
                  ;;     <partial output>HORRIBLE_STRING_TO_DETECT_WHATEVER
                  ;; So now we are more permissive.  We don't try to capture
                  ;; the <partial output> because we're just skipping these
                  ;; lines anyway.
                  (tshell-debug "TSHELL_RECOVER: TSHELL_EXIT on STDOUT.~%")
                  (tshell-debug "stdout line: ~s, suffixp: ~a~%"
                                line (str::strsuffixp *tshell-exit-line* line))
                  (loop-finish))
                (tshell-debug "TSHELL_RECOVER stdout: Skip ~a.~%" line)))

        (when (not stderr-exit)
          (loop do
                (setq line (read-line tshell-err))
                (when (str::strsuffixp *tshell-exit-line* line)
                  (tshell-debug "TSHELL_RECOVER: TSHELL_EXIT on STDERR.~%")
                  (tshell-debug "stderr line: ~s, suffixp: ~a~%"
                                line (str::strsuffixp *tshell-exit-line* line))
                  (loop-finish))
                (tshell-debug "TSHELL_RECOVER stderr: Skip ~a on stderr.~%" line)))))

    (tshell-debug "TSHELL_RUN done.~%")
    (tshell-echo-alldone stream)

    (values (and stdout-exit stderr-exit)
            exit-status
            (nreverse buf))))


(defun tshell-run-background (cmd)
  (unless (tshell-check)
    (error "Invalid *tshell*, *tshell-killer*, or *tshell-bg* -- did you call (tshell-start)?"))

  #-(and Clozure (not mswindows))
  (error "Oops, TSHELL isn't implemented on this Lisp.")

  #+(and Clozure (not mswindows))
  (let* ((tshell-bg-in (ccl::external-process-input-stream *tshell*))
         (nl  (coerce (list #\Newline) 'string))
         (cmd (concatenate 'string "(" cmd ") &" nl)))
    (tshell-debug "TSHELL_BG~%~a~%" cmd)
    (write-line cmd tshell-bg-in)
    (finish-output tshell-bg-in))

  nil)


#|

;; everything works with no status

(include-book "str/strprefixp" :dir :system)
:q
(load "tshell-raw.lsp")
(in-package "AIGPU")

(setq *tshell-debug* t)
(tshell-start)
(tshell "echo hello")
(tshell "./run_aigpu.sh mul35.aigpu")
(tshell "echo hello")

|#
