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

(in-package :shellpool)


; ----------------------------------------------------------------------------
; Simple Utilities

(defvar *debug* nil
  "Change to T for verbose debugging messages.")

(defmacro debug-msg (&rest args)
  "Like (format t ...) but only prints if debugging is enabled."
  `(when *debug*
     (format t "Shellpool: ")
     (format t ,@args)
     (finish-output)))

(defmacro define-constant (name value &optional doc)
  `(defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)
     ,@(when doc (list doc))))

(define-constant nl
  (coerce (list #\Newline) 'string)
  "Newline as a string.  Convenient in string concatenations as a way to insert
   newlines without having to ruin your indenting.")

(defun strprefixp-impl (x y xn yn xlen ylen)
  (declare (type string x y)
           (type fixnum xn yn xlen ylen))
  (cond ((eql xn xlen)
         t)
        ((eql yn ylen)
         nil)
        ((eql (char x xn) (char y yn))
         (strprefixp-impl x y
                          (the fixnum (+ xn 1))
                          (the fixnum (+ yn 1))
                          xlen ylen))
        (t
         nil)))

(defun strprefixp (x y)
  "Determines if the string X comes at the start of the string Y.
   Example:  (strprefixp \"foo\" \"foobar\") is true."
  (declare (type string x y))
  (strprefixp-impl x y 0 0 (length x) (length y)))

(defun strsuffixp (x y)
  "Determines if the string X comes at the end of the string Y.
   Example: (strsuffixp \"bar\" \"foobar\") is true."
  (declare (type string x y))
  (let* ((xlen (length x))
         (ylen (length y)))
    (and (<= xlen ylen)
         (strprefixp-impl x y 0 (- ylen xlen) xlen ylen))))

(defun strpos-fast (x y n xlen ylen)
  (declare (type string x y)
           (type fixnum n xlen ylen))
  (cond ((strprefixp-impl x y 0 n xlen ylen)
         n)
        ((eql n ylen)
         nil)
        (t
         (strpos-fast x y (the fixnum (+ 1 n)) xlen ylen))))

(defun strpos (x y)
  "Determines the position of the first occurrence of the substring X in the
   string Y, or returns NIL if there is no such occurrence."
  (declare (type string x y))
  (strpos-fast x y 0 (length x) (length y)))


; ----------------------------------------------------------------------------
; Glue


#+(or allegro lispworks)
(defstruct bashprocess
  (stdin)
  (stdout)
  (stderr))

(defun make-bash ()
  (let ((bash #+windows "bash.exe"
              #-windows "bash")
        ;; For Windows, invoking Bash with "-o igncr" seems to basically solve
        ;; a bunch of errors due to carriage-return end of line stuff.
        ;; (Without this shellpool wasn't working at all.)
        (args #+windows (list "-o" "igncr")
              #-windows nil))
    #+ccl
    (ccl:run-program bash args
                     :wait   nil
                     :input  :stream
                     :output :stream
                     :error  :stream
                     :sharing :external)
    #+sbcl
    (sb-ext:run-program bash args
                        :search t
                        :wait nil
                        :input :stream
                        :output :stream
                        :error :stream)
    #+cmucl
    (extensions:run-program bash args
                            :wait nil
                            :input :stream
                            :output :stream
                            :error :stream)
    #+allegro
    (multiple-value-bind (stdin stdout stderr pid)
        (excl:run-shell-command bash
                                ;; BOZO somewhere to put args?
                                :wait nil
                                :input :stream
                                :output :stream
                                :error-output :stream
                                :separate-streams t)
      (declare (ignore pid))
      (make-bashprocess :stdin stdin
                        :stdout stdout
                        :stderr stderr))
    #+lispworks
    ;; This doesn't seem to work at all.
    (multiple-value-bind (stdio stderr pid)
        (system:run-shell-command bash
                                  ;; BOZO somewhere to put args?
                                  :wait nil
                                  :input :stream
                                  :output :stream
                                  :error-output :stream)
      (declare (ignore pid))
      (make-bashprocess :stdin stdio
                        :stdout stdio
                        :stderr stderr))

    #+abcl
    (system:run-program bash args :wait nil)

    ;; CLISP and ECL each have run-program commands, which look mostly similar
    ;; to that of many of these other Lisps, but they don't seem to provide any
    ;; stderr handling, so our current code won't work with them.
    ;;
    ;; It might be possible to rework things so that we don't rely on stderr,
    ;; but this would especially make PID detection trickier, see the notes
    ;; below where we create the temporary file.
    ))

(defun bash-in (sh)
  #+ccl     (ccl:external-process-input-stream sh)
  #+sbcl    (sb-ext:process-input sh)
  #+cmucl   (extensions:process-input sh)
  #+(or allegro lispworks) (bashprocess-stdin sh)
  #+abcl    (system:process-input sh)
  )

(defun bash-out (sh)
  #+ccl     (ccl:external-process-output-stream sh)
  #+sbcl    (sb-ext:process-output sh)
  #+cmucl   (extensions:process-output sh)
  #+(or allegro lispworks) (bashprocess-stdout sh)
  #+abcl    (system:process-output sh)
  )

(defun bash-err (sh)
  #+ccl     (ccl:external-process-error-stream sh)
  #+sbcl    (sb-ext:process-error sh)
  #+cmucl   (extensions:process-error sh)
  #+(or allegro lispworks) (bashprocess-stderr sh)
  #+abcl    (system:process-error sh)
  )

(defun bash-alive-p (sh)
  #+ccl       t ;; BOZO implement me
  #+sbcl      (sb-ext:process-alive-p sh)
  #+cmucl     t ;; BOZO implement me
  #+allegro
  (and (open-stream-p (bashprocess-stdin sh))
       (open-stream-p (bashprocess-stdout sh))
       (open-stream-p (bashprocess-stderr sh)))
  #+lispworks t ;; BOZO implement me
  #+abcl      (system:process-alive-p sh)
  )


; ----------------------------------------------------------------------------
; State

(defstruct runner
  ;; A single runner thread.

  ;; ERR is signaled only when the runner shell unexpectedly dies.  A runner
  ;; that gets flagged with an ERR does not get added back into the state.
  (err)

  ;; SH is the main shell (a Lisp process or bashprocess object, depending on
  ;; the lisp).
  (sh))

(defstruct state

  ;; LOCK is a lock that protects access to the state itself.  See the fields
  ;; below for when the lock must be acquired.
  (lock)

  ;; AUX is a dedicated bash process that is used to:
  ;;   - send kill signals to subsidiary processes to support interrupts,
  ;;   - launch background commands using run&
  ;;
  ;; Note that we only need a single AUX shell to be able to kill any number
  ;; of running processes.  Similarly, since background processes are of a
  ;; "fire and forget" nature, i.e., we invoke commands like "firefox &", we
  ;; think a single background shell should suffice.
  ;;
  ;; Locking convention: the LOCK must be held while using the AUX shell.  We
  ;; expect uses of AUX to take very little time (it just sends a "kill" signal
  ;; to some other process or launches background programs).
  (aux)

  ;; SEM is a semaphore that governs access to the RUNNERS.  Invariant: the
  ;; count of the semaphore should always agree exactly with (LENGTH RUNNERS).
  ;; See WITH-RUNNER, which properly waits for the next free runner.
  (sem)

  ;; RUNNERS are an ordinary list of RUNNERs that are available for running
  ;; foreground shell commands with RUN.  Invariant: Every runner is always OK,
  ;; i.e., there are no runners marked with ERR.
  (runners)

  ;; TOTAL is the total number of shells that have been started.  It can exceed
  ;; (length runners) because, whereas shells are taken out of the list of
  ;; runners by WITH-RUNNER, total is mainly intended for use in ENSURE and is
  ;; (typically) not changed merely because a shell is in use.  (We may
  ;; decrease it if a shell dies unexpectedly.)
  ;;
  ;; Locking convention: the LOCK must be held while you inspect/access total.
  (total))

(defparameter *state*
  (make-state :lock       (bt:make-lock "shellpool state lock")
              :aux        nil
              :sem        (bt-sem:make-semaphore)
              :runners    nil
              :total      0))

(defmacro with-state-lock (&rest forms)
  `(bt:with-lock-held ((state-lock *state*))
                      . ,forms))

(defmacro with-runner (name &rest forms)
  `(let ((,name nil))
     (unwind-protect
         (progn
           (with-state-lock
             ;; This isn't a perfect defense against all shells dying, but in
             ;; practice it should be pretty good.
             (when (eql (state-total *state*) 0)
               (error "No shells are available.")))
           (unless (bt-sem:wait-on-semaphore (state-sem *state*))
             (error "Failed to acquire runner"))
           (with-state-lock
             (unless (consp (state-runners *state*))
               ;; Should never happen.  The number of free runners
               ;; should always agree with the value of the
               ;; semaphore.
               (error "Our turn to go, but no runners are available?"))
             (setq ,name (pop (state-runners *state*))))
           (unless (bash-alive-p (runner-sh ,name))
             (debug-msg "Shellpool: with-runner failing because bash is dead!~%")
             (setf (runner-err ,name) t)
             (error "Shellpool runner is dead."))
           ,@forms)
       ;; Clean up by putting the runner back.
       (with-state-lock
         (cond ((runner-err runner)
                (debug-msg "Not reinstalling runner due to error.~%")
                ;; In this very unusual case, decrease the total number of
                ;; shells since one has died.
                (setf (state-total *state*)
                      (max 0 (- (state-total *state*) 1))))
               (t
                (push ,name (state-runners *state*))
                (bt-sem:signal-semaphore (state-sem *state*))))))))

(define-constant +exit-line+   "SHELLPOOL_EXIT")
(define-constant +status-line+ "SHELLPOOL_STATUS")
(define-constant +pid-line+    "SHELLPOOL_PID")
(define-constant +death-line+  "SHELLPOOL_UNEXPECTED_DEATH")

(define-constant +allkids+
  ;; Bash script to recursively collect the children of a process.
  ;;  - Works on Linux and FreeBSD at least.
  ;;  - For Windows this also seems to work, with some caveats:
  ;;     * needs the procps cygwin package installed
  ;;     * may NOT work for native windows processes (instead of
  ;;       cygwin processes?)
  ;;
  ;; If you need to port this to some other OS, some useful commands
  ;; that we used when developing it on FreeBSD/Linux were:
  ;;
  ;;   $ ./sleepN.sh 1234 4 > foo.out &
  ;;        - creates some perl processes under our shell for 1234 seconds
  ;;   $ ps ax -o pid,gid,ppid,pgid,command
  ;;        - lets us see their PIDs, etc.
  ;;   $ ... hack together an allkids function and test it on $$ ...
  ;;
  ;; When I ported this to OpenBSD 5.6, I noticed that shellpool would
  ;; reliably fail the kill tests, issuing 'shell is corrupted' messages
  ;; such as this:
  ;;    Shellpool: Shell is corrupted: "+Sleeping for 14 more seconds."
  ;;
  ;; Thinking about this, I realized that my original implementation of allkids
  ;; was simply returning the PID for the process and all of its transitive
  ;; children in some arbitrary order.  Supposing that the 'kill' command
  ;; simply walks over them and kills them one by one, this would give no
  ;; guarantee that the children are killed before the parent.  That could lead
  ;; to the kind of corruption message above: the parent could be killed early,
  ;; causing shellpool's 'wait' command to think it's time for the exit line;
  ;; meanwhile the subprocesses could continue to print messages before being
  ;; killed.  These messages could thus arrive after the exit line, corrupting
  ;; the shell.
  ;;
  ;; To avoid this, allkids now takes a two arguments.  Think of it as
  ;; allkids(pid, printp), where printp becomes true on any recursive call but
  ;; is originally false.  In other words, allkids no longer prints out the PID
  ;; of the parent process, but only prints the PIDs only of the (transitive)
  ;; children.  This way, we can kill just the children first, and the parents
  ;; later.

  "function allkids() {
     if [ ! -z \"$2\" ]
     then
         echo $1
     fi
     local children=`pgrep -P $1`
     if [ -z \"$children\" ]
     then
         return;
     else
         for child in $children
         do
             allkids $child 1
         done
     fi
  }")

(defun add-runners (n)
  ;; Assumes the state lock is held.
  (let ((state *state*))
    (loop for i from 1 to n do
          (let* ((sh    (make-bash))
                 (sh-in (bash-in sh)))
            ;; Try to make sure that if the shell itself is killed, we get a
            ;; chance to see that it has died.  This isn't a guarantee, of
            ;; course: the shell could always get killed with -9 and we'll
            ;; never have a chance to see it go.
            (format sh-in "trap \"echo ~s; echo ~s 1>&2; exit\" SIGHUP SIGINT SIGTERM~%"
                    +death-line+ +death-line+)
            (push (make-runner :err nil :sh sh)
                  (state-runners state))))
    (incf (state-total state) n)
    (bt-sem:signal-semaphore (state-sem state) n)))

(defparameter *max-shells* 1000
  "Purely a safety valve.  We'll cause an error if you try to start more than
   this many shells at once, since that would probably cause problems on your
   system.  We make this a parameter so you can reconfigure it if you really
   need to create so many shells.")

(defun start (&optional (n '1))
  "Start some number of shells and ensure that the aux shell is running."
  (check-type n unsigned-byte)
  (debug-msg "START: ~s~%" n)
  (with-state-lock
    (when (>= (+ n (state-total *state*)) *max-shells*)
      (error "Too many shells.  Trying to start ~s shells, which would push ~
              the total number of shells to ~s.  If you really want to do ~
              this, adjust shellpool:*max-shells*." n (+ n (state-total *state*))))
    (unless (state-aux *state*)
      (debug-msg "START: starting aux shell~%")
      (let* ((aux    (make-bash))
             (aux-in (bash-in aux)))
        (write-line +allkids+ aux-in)
        (setf (state-aux *state*) aux)))
    (add-runners n)
    nil))

(defun ensure (&optional (n '1))
  "Ensure that at least n shells are running, starting up shells if needed."
  (check-type n unsigned-byte)
  (let* ((current-total (with-state-lock (state-total *state*))))
    (debug-msg "ENSURE: currently have ~s shells, want ~s.~%" current-total n)
    (when (<= current-total n)
      (start (- n current-total))))
  nil)

(defun parse-pid-line (line)
  ;; Given a line like SHELLPOOL_PID 1234, we return 1234.
  (debug-msg "Parsing PID line: ~s~%" line)
  (unless (strprefixp +pid-line+ line)
    (error "Shellpool error: bad pid line: ~s." line))
  (multiple-value-bind (val pos)
      (parse-integer (subseq line (+ 1 (length +pid-line+))))
    (declare (ignore pos))
    val))

(defun kill (pid)
  ;; Use the aux shell to try to kill process PID.
  (debug-msg "KILL: killing ~s.~%" pid)
  (with-state-lock
    (let* ((aux    (state-aux *state*))
           (aux-in (bash-in aux)))
      (unless (bash-alive-p aux)
        (error "Shellpool error: aux shell died?"))

      ;; Killing is a bit trickier than just sending a kill signal to the
      ;; target PID, because the PID can spawn children.  See +allkids+ above.

      ;; We arrange so that the aux shell starts with the allkids function
      ;; defined.  We can then be sure to kill all the children that your
      ;; process has created.

      ;; Kill all children:
      (format aux-in "kill -9 $(allkids ~s)~%" pid)

      ;; Kill the parent last.  See the comments in +allkids+ above.
      (format aux-in "kill -9 ~s~%" pid)

      ;; Use finish-output, not force-output, because we want to be very sure
      ;; this gets run.
      (finish-output aux-in)

      (unless (bash-alive-p aux)
        (error "Shellpool error: aux shell died?")))))

(defun default-each-line (line type)
  (declare (type string line))
  (debug-msg "Default streaming line (type ~s): ~s ~%" type line)
  (case type
    (:stdout
     (write-line line)
     (force-output))
    (:stderr
     (write-line line *error-output*)
     (force-output *error-output*))
    (otherwise
     (error "Unexpected line type ~s" type))))


(defmacro with-file-to-be-deleted (filename &rest forms)
  `(unwind-protect
       (progn . ,forms)
     (delete-file ,filename)))


(defun make-run-command-string (filename)
  ;; Extremely tricky and carefully crafted bash code follows.
  ;;
  ;; The core of this was originally the following:
  ;;
  ;;  0.     set -o pipefail
  ;;  1.     ((bash cmd.sh < /dev/null | sed -u 's/^/+/') 3>&1 1>&2 2>&3 | sed -u 's/^/-/') 2>&1
  ;;
  ;; What's going on here?
  ;;
  ;;   - The SED commands and output redirection are grabbing the output from
  ;;     cmd.sh and modifying it so that:
  ;;          every stdout line gets prefixed by +
  ;;          every stderr line gets prefixed by -
  ;;          the resulting lines are merged together and printed to stdout
  ;;          the use of "-u" prevents sed from adding extra buffering
  ;;
  ;;     This is wonderful and allows us to
  ;;       (1) distinguish the stderr/stdout lines from one another (obviously),
  ;;       (2) distinguish the command output from other stuff (needed in a moment),
  ;;       (3) get stdout/stderr together, interleaved, as they are produced.
  ;;
  ;;   - Normally this use of sed would ruin the exit code from cmd.sh.
  ;;     However, the pipefail option corrects for this, and sets things up so
  ;;     that if cmd.sh exits with a failure, we'll get this failure as the
  ;;     exit status for the whole pipeline.
  ;;
  ;; We extend this core with some additional stuff for being able to extract
  ;; the exit code and PID of the command.  Here is the real solution:
  ;;
  ;;  0.   set -o pipefail                        # As above, and doesn't bother anything below
  ;;  1.   ( <core 1> ; printf "\nEXIT $?\n") &   # Run in background (so we can get PID), print exit status
  ;;  2.   echo PID $! 1>&2                       # Print the PID to stderr.
  ;;  3.   wait                                   # Wait for the command to finish
  ;;  4.   echo ""                                # Make sure we get a newline at end of stdout
  ;;  5.   echo "" 1>&2                           # Make sure we get a newline at end of stderr
  ;;  6.   echo END                               # Print end-of-command to stdout
  ;;  7.   echo END 1>&2                          # Print end-of-command to stderr
  ;;
  ;; The main trick here is to run the command in the background and then to
  ;; wait for it.  We do this so that (line 2) we can print out the PID
  ;; associated with the subshell we're launching.  Notice that something
  ;; subtle helps to make this safe: all output from Line 1 goes to stdout, but
  ;; we print the PID to stderr.  Accordingly, when reading output in Lisp, we
  ;; can be sure that the first line of stderr is going to be the PID line,
  ;; even if the command prints immediately to stderr.
  ;;
  ;; The printf command in line 1 deserves some attention.  Note that we add a
  ;; newline before printing the exit message.  This is because the command
  ;; could exit after printing some non newline-terminated text, e.g., suppose
  ;; the user wants to run a command like "echo -n hello".  By printing the
  ;; newline, we're sure that our EXIT message will occur on its own line.
  ;; This makes it possible to reliably parse it without any restrictions on
  ;; what core might print.
  ;;
  ;; The end strings are needed to determine when we've reached the end of the
  ;; output associated with this command.
  ;;
  ;; Portability tweak.
  ;;
  ;; When I ported this to PC-BSD, I found that the SED command there did not
  ;; have the -u (unbuffered) option.  Fortunately our use of SED is quite
  ;; minimal and, it turns out, we can emulate it entirely within BASH, as with
  ;; just some simple functions, i.e.,
  ;;
  ;; add_plus() { local line; while read line; do echo "+$line"; done }
  ;; add_minus() { local line; while read line; do echo "-$line"; done }
  ;;
  ;; Then our core can become:
  ;;
  ;;  ((bash cmd.sh < /dev/null | add_plus) 3>&1 1>&2 2>&3 | add_minus) 2>&1
  ;;
  ;; This is almost exactly what we'll use, except that we will prefix our
  ;; functions with shellpool_ to reduce the chance of collision with the
  ;; user's scripts.
  ;;
  ;; Bug fix for version 0.0.3.
  ;;
  ;; The above definitions of add_plus and add_minus don't work when the script
  ;; doesn't print a newline on its last line of output.  See
  ;; https://stackoverflow.com/questions/4165135 for some background.  After
  ;; tinkering with it, I came up with this patched version, which notices when
  ;; the last line has content and prints it as if it were a normal line.
  ;;
  ;; add_plus() {
  ;;     local line;
  ;;     local eof;
  ;;     eof=""
  ;;     while [ -z "$eof" ]
  ;;     do
  ;;        read line || eof=1
  ;;        if [ -z "$eof" ]
  ;;        then
  ;;            # No EOF so this is a normal line, just echo it.
  ;;            echo "+$line";
  ;;        elif [ ! -z "$line" ]
  ;;        then
  ;;            # Found EOF and there is content, so echo it.
  ;;            echo "+$line";
  ;;        fi
  ;;     done
  ;; }
  (concatenate 'string
               "set -o pipefail

shellpool_add_plus() {
    local line;
    local eof;
    eof=\"\"
    while [ -z \"$eof\" ]
    do
	read line || eof=1
	if [ -z \"$eof\" ]
	then
	    echo \"+$line\";
	elif [ ! -z \"$line\" ]
	then
	    echo \"+$line\";
	fi
    done
}

shellpool_add_minus() {
    local line;
    local eof;
    eof=\"\"
    while [ -z \"$eof\" ]
    do
	read line || eof=1
	if [ -z \"$eof\" ]
	then
	    echo \"-$line\";
	elif [ ! -z \"$line\" ]
	then
	    echo \"-$line\";
	fi
    done
}
"
               "(((bash " filename
               " < /dev/null | shellpool_add_plus) 3>&1 1>&2 2>&3 | shellpool_add_minus) 2>&1"
               " ; printf \"\\n" +status-line+ " $?\\\n\" ) &" nl
               "echo " +pid-line+ " $! 1>&2" nl
               "wait" nl
               "echo " +exit-line+ nl
               "echo " +exit-line+ " 1>&2" nl))


(defun run (script &key (each-line #'default-each-line))
  (check-type script string)
  (check-type each-line function)
  (debug-msg "Going into run.~%")

  (with-runner runner
    (debug-msg "Got with-runner~%")
    (let* ((sh            (runner-sh runner))
           (bash-in       (bash-in sh))
           (bash-out      (bash-out sh))
           (bash-err      (bash-err sh))
           (pid           nil)
           (exit-status   nil)
           (line          nil)
           (stdout-exit   nil)
           (stderr-exit   nil)
           (tempfile
            (cl-fad:with-output-to-temporary-file
             (stream :template "shellpool-%.tmp")
             ;; Notes:
             ;;
             ;;  - We don't need a #!/???/bash line.  We will invoke the script
             ;;    with "bash tempfile" instead.  This avoids needing chmod and
             ;;    avoids needing to know where bash lives.
             ;;
             ;;  - I once tried to put the printing of the PID line here, but
             ;;    that didn't work so well because the stdout+stderr output
             ;;    from this temporary script gets interleaved in an
             ;;    unpredictable way, so if the user's command immediately
             ;;    prints a message, then it can come first, before even our
             ;;    PID line.  To avoid this, we do the PID capture outside the
             ;;    command on STDERR, which the user's command has no way to
             ;;    influence.

             ;; BOZO -- test me -- I think we probably don't need to do this.
             ;; (write-line "trap \"kill -- -$BASHPID\" SIGINT SIGTERM" stream)
             (write-line script stream))))
      (with-file-to-be-deleted tempfile

        (let ((cmd (make-run-command-string (namestring tempfile))))

          (debug-msg "Temp path is ~s~%" (namestring tempfile))
          (debug-msg "<Bash Commands>~%~s~%</Bash Commands>~%" cmd)

          (write-line "echo ping" bash-in)
          (finish-output bash-in)
          (let ((line (read-line bash-out)))
            (unless (equal line "ping")
              (setf (runner-err runner) t)
              (error "Shellpool: Shell is corrupted: ~s~%" line)))

          ;; Use finish-output, not force-output, because we want to be very
          ;; sure this gets run.
          (write-line cmd bash-in)
          (finish-output bash-in)

          (setq pid (parse-pid-line (read-line bash-err)))

          (debug-msg "PID is ~s.~%" pid)

          (unwind-protect

              (progn
                ;; Read command output until we find the exit line.
                (loop do
                      (setq line (read-line bash-out))
                      (debug-msg "** Output line: ~s~%" line)
                      (cond ((equal line "")
                             (debug-msg "Ignoring blank line.~%"))
                            ((equal line +exit-line+)
                             (debug-msg "Exit line, done reading STDOUT.~%")
                             (setq stdout-exit t)
                             (loop-finish))
                            ((eql (char line 0) #\+)
                             (debug-msg "Stdout line, invoking callback.~%")
                             (funcall each-line (subseq line 1 nil) :stdout))
                            ((eql (char line 0) #\-)
                             (debug-msg "Stderr line, invoking callback.~%")
                             (funcall each-line (subseq line 1 nil) :stderr))
                            ((strprefixp +status-line+ line)
                             (debug-msg "Exit status line: ~s~%" line)
                             (setq exit-status
                                   (parse-integer line :start (+ 1 (length +status-line+)))))
                            ((equal line +death-line+)
                             (debug-msg "Unexpected death line.  Signaling error.~%")
                             (setf (runner-err runner) t)
                             (error "Shellpool: Shell died unexpectedly!~%"))
                            (t
                             (error "Unexpected line ~s~%" line))))

                ;; Read stderr until we find the exit line.
                (loop do
                      (setq line (read-line bash-err))
                      (debug-msg "** Stderr line: ~s~%" line)
                      (cond ((equal line "")
                             (debug-msg "Ignoring blank line.~%"))
                            ((equal line +exit-line+)
                             (debug-msg "Exit line, done reading STDERR.~%")
                             (setq stderr-exit t)
                             (loop-finish))
                            ((equal line +death-line+)
                             (debug-msg "Unexpected death line.  Signaling error.~%")
                             (setf (runner-err runner) t)
                             (error "Shellpool: Shell died unexpectedly!~%"))
                            (t
                             (error "Unexpected line ~s~%" line)))))

            (progn
              ;; Cleanup in case of interrupts.
              (unless (and stdout-exit stderr-exit)
                (debug-msg "Shutting down process ~s.~%" pid)
                (kill pid)
                (debug-msg "Done shutting down ~s.~%" pid))

              (debug-msg "In unwind-protect, alive is: ~s~%"
                         (bash-alive-p (runner-sh runner)))

              (when (and (not stdout-exit)
                         (not (runner-err runner)))
                (loop do
                      (setq line (read-line bash-out))
                      (cond ((strsuffixp +exit-line+ line)
                             ;; We used to try to match +exit-line+ exactly, but
                             ;; then we found that if we interrupt while the program has
                             ;; printed partial output, we can end up with a situation
                             ;; like:
                             ;;     <partial output>HORRIBLE_STRING_TO_DETECT_WHATEVER
                             ;; So now we are more permissive.  We don't try to capture
                             ;; the <partial output> because we're just skipping these
                             ;; lines anyway.
                             (debug-msg "Recovery: Got EXIT on STDOUT.~%")
                             (debug-msg "Stdout line: ~s, suffixp: ~s~%"
                                        line (strsuffixp +exit-line+ line))
                             (loop-finish))
                            ((equal line +death-line+)
                             (debug-msg "Unexpected death line.  Signaling error.~%")
                             (setf (runner-err runner) t)
                             (loop-finish))
                            (t
                             (debug-msg "Recovery: Stdout: Skip ~s.~%" line)))))

              (when (and (not stderr-exit)
                         (not (runner-err runner)))
                (loop do
                      (setq line (read-line bash-err))
                      (cond ((strsuffixp +exit-line+ line)
                             (debug-msg "Recovery: Got EXIT on STDERR.~%")
                             (debug-msg "stderr line: ~s, suffixp: ~s~%"
                                        line (strsuffixp +exit-line+ line))
                             (loop-finish))
                            ((equal line +death-line+)
                             (debug-msg "Unexpected death line.  Signaling error.~%")
                             (setf (runner-err runner) t)
                             (loop-finish))
                            (t
                             (debug-msg "Recovery: Stderr: Skip ~s.~%" line))))))))

        (debug-msg "RUN done.~%")

        (unless (integerp exit-status)
          (error "Somehow didn't get the exit status?"))

        (unless (and stdout-exit stderr-exit)
          (error "Somehow didn't exit?"))

        exit-status))))

(defun run& (script)
  (check-type script string)
  (debug-msg "Going into run&.~%")

  ;; What we want to do seems very simple:
  ;;
  ;;   1. Create a temporary file and write the script into it.
  ;;   2. Run the script with `bash temp.sh &` (well, modulo some io
  ;;      redirection to prevent any reading/printing).
  ;;   3. Delete the temporary file.
  ;;
  ;; Unfortunately there is a tricky race condition here: how do we make sure
  ;; that the `bash temp.sh &` command will read the script before we delete
  ;; it?  Some approaches that won't work include:
  ;;
  ;;   1. Use something like (with-file-to-be-deleted tempfile ...) to have
  ;;      Lisp delete it.  This doesn't work because there's no guarantee that
  ;;      bash will even be started before Lisp gets a chance to unlink the
  ;;      file.
  ;;
  ;;   2. Issue separate shell commands, e.g.,
  ;;
  ;;        bash temp.sh &
  ;;        rm temp.sh
  ;;
  ;;      This is perhaps even less likely to work than having Lisp delete
  ;;      the temp.sh file.
  ;;
  ;; A solution that probably would work would be to do something like this:
  ;;
  ;;      (bash temp.sh ; rm temp.sh) &
  ;;
  ;; I think this should be robust against any failures in temp.sh, and the
  ;; only reason it would fail would be if the bash itself got killed somehow.
  ;; However, note that this approach does have the disadvantage that the
  ;; temporary script will continue to exist for as long as temp.sh is running.
  ;;
  ;; Given that, I think it's arguably most elegant to have the script simply
  ;; delete itself.  Since the bash process executing the script will
  ;; necessarily have a file handle open to the script, the unlink can happen
  ;; immediately but the inode shouldn't get freed until the script exits.

  (let ((tempfile
         (cl-fad:with-output-to-temporary-file
          (stream :template "shellpool-%.tmp")

          ;; We don't need a #!/???/bash line.  We will invoke the script with
          ;; "bash tempfile" instead.  This avoids needing chmod and avoids
          ;; needing to know where bash lives.

          ;; Step 1: delete yourself.  (See above comments)
          (write-line "rm -- \"$0\"" stream)

          ;; Step 2: do what the user said.
          (write-line script stream))))

    (with-state-lock
      (let* ((aux    (state-aux *state*))
             (aux-in (if (not aux)
                         (error "No shells are available.")
                       (bash-in aux)))
             (filename (namestring tempfile))

             ;; The use of disown here is intended to allow the background job
             ;; to persist even if the Lisp process and/or its corresponding
             ;; Bash shells are destroyed.
             (cmd      (concatenate 'string
                                    "(bash " filename " < /dev/null 2>&1 > /dev/null) &
disown -h $!
")))
        (debug-msg "BG: ~s~%" cmd)
        (write-line cmd aux-in)
        (finish-output aux-in)
        )))
  nil)
