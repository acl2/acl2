; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Tshell
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; NOTE: This file requires that str/strprefixp has been loaded.

(defparameter *tshell-debug*
  ;; Change this to T for verbose debugging information.
  nil)

(defmacro tshell-debug (&rest args)
  `(when *tshell-debug* (format t ,@args)))


; We look for certain strings to know when the program's output ends.  This is
; gross, but in practice it should work.

(defparameter *tshell-exit-line*   "HORRIBLE_STRING_TO_DETECT_END_OF_TSHELL_COMMAND")
(defparameter *tshell-status-line* "HORRIBLE_STRING_TO_DETECT_TSHELL_EXIT_STATUS")
(defparameter *tshell-pid-line*    "TSHELL_PID")


; We actually use two bash processes.  *tshell* runs the programs.
; *tshell-killer* is only used to kill programs that *tshell* is running.

(defvar *tshell*)
(defvar *tshell-killer*)

; I added another bash process for background jobs.  This seems easier than
; running them with *tshell*.

(defvar *tshell-bg*)


(defun tshell-stop ()
  ;; Stops any tshell processes that are running.

  #-Clozure
  ;; BOZO maybe eventually add support for other Lisps
  nil

  #+Clozure
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

  #-Clozure
  ;; BOZO maybe eventually add support for other Lisps
  nil

  #+Clozure
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
  #-Clozure
  t
  #+Clozure
  (and (ccl::external-process-p *tshell*)
       (ccl::external-process-p *tshell-killer*)
       (ccl::external-process-p *tshell-bg*)
       (eq (ccl::external-process-status *tshell*) :running)
       (eq (ccl::external-process-status *tshell-killer*) :running)
       (eq (ccl::external-process-status *tshell-bg*) :running)))

(defun tshell-ensure ()
  ;; Stops any tshell processes and starts new ones.
  #-Clozure
  ;; BOZO eventually add support for other Lisps
  nil
  #+Clozure
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
  ;; If it's an exit line, parse the status and return it as an
  ;; integer. Otherwise, return nil.
  (if (str::strprefixp *tshell-status-line* line)
      (multiple-value-bind (val pos)
          (parse-integer (subseq line (+ 1 (length *tshell-status-line*))))
        (declare (ignore pos))
        val)
    nil))

(defun tshell-parse-pid-line (line)
  ;; Given a line like TSHELL_PID 1234, we return 1234.
  (unless (str::strprefixp *tshell-pid-line* line)
    (error "TSHELL error: bad pid line: ~a." line))
  (multiple-value-bind (val pos)
      (parse-integer (subseq line (+ 1 (length *tshell-pid-line*))))
    (declare (ignore pos))
    val))

#+Clozure
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

; Called by tshell to echo output from the sub-program.  We put this in its own
; function so that it can be redefined.  The buf is the previous lines from
; this invocation of the program, in reverse order.

  (declare (ignorable buf))
  (write-line line stream)
  (force-output stream))

(defun tshell-echo-alldone (stream)
  (declare (ignorable stream))

; Called by tshell after all the output has been printed with tshell-echo, in
; case tshell-echo wants to not print newlines right away

  nil)



(defun tshell-call-fn (cmd print save)
  ;; See the documentation in tshell.lisp.

  (unless (tshell-check)
    (error "Invalid *tshell*, *tshell-killer*, or *tshell-bg* -- did you call (tshell-start)?"))

  #-Clozure
  (error "Oops, TSHELL isn't implemented for this Lisp.")

  #+Clozure
  (let* ((tshell-in     (ccl::external-process-input-stream *tshell*))
         (tshell-out    (ccl::external-process-output-stream *tshell*))
         (tshell-err    (ccl::external-process-error-stream *tshell*))
         (pid           0)
         (exit-status   1)
         (line          nil)
         (code          nil)
         (stdout-exit   nil)
         (stderr-exit   nil)
         (buf           nil)
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
;               cmd " < /dev/null 2>&1 & " nl
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
              (setq line (read-line tshell-out))
              (setq code (tshell-parse-status-line line))
              (cond ((equal line *tshell-exit-line*)
                     (progn
                       (tshell-debug "TSHELL_EXIT on STDOUT~%")
                       (setq stdout-exit t)
                       (loop-finish)))
                    (code
                     (progn
                       (tshell-debug "TSHELL_STATUS is ~a.~%" code)
                       (setq exit-status code)))
                    (t
                     (progn
                       (when print
                         (tshell-echo line buf stream))
                       (when save
                         (push line buf))))))

          ;; Read stderr until we find the exit line.
          (loop do
                (setq line (read-line tshell-err))
                (when (equal line *tshell-exit-line*)
                  (tshell-debug "TSHELL_EXIT on STDERR~%")
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
                (when (equal line *tshell-exit-line*)
                  (tshell-debug "TSHELL_RECOVER: TSHELL_EXIT on STDOUT.~%")
                  (loop-finish))
                (tshell-debug "TSHELL_RECOVER: Skip ~a.~%" line)))

        (when (not stderr-exit)
          (loop do
                (setq line (read-line tshell-err))
                (when (equal line *tshell-exit-line*)
                  (tshell-debug "TSHELL_RECOVER: TSHELL_EXIT on STDERR.~%")
                  (loop-finish))
                (tshell-debug "TSHELL_RECOVER: Skip ~a on stderr.~%" line)))))

    (tshell-debug "TSHELL_RUN done.~%")
    (tshell-echo-alldone stream)

    (values (and stdout-exit stderr-exit)
            exit-status
            (nreverse buf))))


(defun tshell-run-background (cmd)
  (unless (tshell-check)
    (error "Invalid *tshell*, *tshell-killer*, or *tshell-bg* -- did you call (tshell-start)?"))

  #-Clozure
  (error "Oops, TSHELL isn't implemented on this Lisp.")

  #+Clozure
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
