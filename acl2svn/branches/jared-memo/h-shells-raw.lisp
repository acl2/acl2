;; BOZO copyright stuff.

; h-shells-raw.lisp
;
; Functions for interacting with subsidiary CSH and SH processes.  Jared split
; this out of memoize-raw.lisp because it has nothing to do with memoization.
; However, the CSH subshell seems to be used a lot in the WATCH stuff.
;
; It would probably be best to work toward getting away from this stuff.  The
; TSHELL book from AIGPU is a more capable replacement that accomplishes the
; same thing but also lets you interrupt nicely, get exit codes, and control
; the printing from the subprocess.  So if we get WATCH set up so that it can
; go into a book, maybe we can just release TSHELL and have it use that
; instead.

(in-package "ACL2")

;;   CSH

;
; Here is a quite simple version of OPEN-GZIPPED-FILE that is fine to
; use in CCL for a few files, but perhaps not for thousands of files
; because FORK can take a serious amount of time for a big CCL job such
; as ACL2 since a copy is made by FORK of the entire job.
;
; (defun open-gzipped-file (name)
;    (ccl::external-process-output-stream
;      (ccl::run-program "gunzip" (list "-c"  name)
;                        :output :stream :wait nil)))
;
; To eliminate FORK as a source of such inefficiency, we provide the
; function CSH, which establishes a lasting subsidiary cshell process
; executing a 'read-and-execute one CSH line' loop.  It may be a good
; idea to call CSH very early, even before you need it, simply to get
; that process running when you can, i.e., when your image is small
; enough.

(defv *csh-process* nil

  "When not NIL, *CSH-PROCESS* has as its value the Lisp process
  object for an underlying csh process.")

(defv *csh-temporary-file-name* nil

  "When not NIL, *CSH-TEMPORARY-FILE-NAME* has as its value a stream
  via which an underlying csh process sends synchronizing info back to
  Lisp.")

#+Clozure
(defn1 csh-stop ()

  "(csh-stop) kills the subsidiary csh process if there is one."

  (ignore-errors
    (when (ccl::external-process-p *csh-process*)
      (ccl::signal-external-process *csh-process* 9)))
  (setq *csh-process* nil)
  (ignore-errors
    (when (and *csh-temporary-file-name*
               (probe-file *csh-temporary-file-name*))
      (delete-file *csh-temporary-file-name*)))
  (setq *csh-temporary-file-name* nil))

#+Clozure
(defv *csh-start-string*
  "set tm=`mktemp /tmp/acl2-csh-temp.XXXXXX`; echo $tm")

#+Clozure
(defn1 csh-start ()

  "(CSH-START) creates a subsidiary csh process.  CSH-START
  is called automatically by CSH."

  (csh-stop)
  (setq *csh-process*
    (ccl::run-program "/bin/csh" (list "-f")
                      :input :stream
                      :output :stream
                      :wait nil))
  (let ((is (ccl::external-process-input-stream *csh-process*)))
    (our-syntax
     (write-line *csh-start-string* is)
     (finish-output is)
     (setq *csh-temporary-file-name*
       (read-line
        (ccl::external-process-output-stream *csh-process*)
        nil
        :eof)) ; wait
     (cond ((ignore-errors
              (probe-file *csh-temporary-file-name*))
            *csh-temporary-file-name*)
           (t (error "csh-start: failed."))))))

(defn1 args-spaced (args)
  (cond ((atom args) "")
        ((and (atom (cdr args))
              (stringp (car args)))
         (car args))
        (t (with-output-to-string (s)
             (loop for tail on args do
                   (our-syntax
                    (princ (car tail) s)
                    (when (cdr tail) (write-char #\Space s))))))))

#+Clozure
(defun csh (&rest args)

  "CSH is a raw Lisp function.  Called with no arguments, (CSH)
  returns a status report on a process, which is created if necessary,
  and which, once created, is the value of the Lisp variable
  *CSH-PROCESS*.

  On each call to CSH, one csh shell command is executed.  Unless for
  some unusual reason the process is killed, the same process executes
  all the commands.  That is, to repeat, a new process is not created
  for each command, but the same csh process is used repeatedly.  This
  may significantly reduce the copying overhead of a call to FORK to
  create a new process under a big Lisp job, as the ACL2 function
  SYSTEM-CALL does on each call.

  (CSH :STREAM arg1 ... argn) executes a single csh command, namely,
  the string obtained by placing spaces between the strings, symbols,
  or numbers arg1 ... argn.  A stream of the command's standard output
  is returned as the value of CSH.  For example,

     (CSH :STREAM '|gunzip -c foo.gz|)

  returns an open input stream that contains the ungzipped contents of
  the file 'foo.gz'.

  If arg1 is not :STREAM, (CSH arg1 ... argn) executes one csh command
  exactly as in the :STREAM case, namely, the string obtained by
  placing spaces between the strings, symbols, or numbers arg1
  ... argn.  But the standard output of the command is printed into a
  string, which is returned as the value of CSH.  If the last
  character of that output is a newline, it is not included in the
  string returned.

  The standard output from the command is diverted through a unique
  /tmp file, whose name is the value of the variable
  *CSH-TEMPORARY-FILE-NAME*.

  If the command sends any output to error output, a Lisp ERROR is
  caused and the error output of the command is printed to Lisp's
  *STANDARD-OUTPUT*.

  Each single csh command fed to CSH should be only one line long, and
  should not involve any of the fancier csh characters such *, ~, !,
  =, |, <, >, &, \, {, }, single quote, semicolon, period, question
  mark, parentheses, square brackets, double quote, and backquote.
  Stick to alphanumeric characters, space, and hyphen if possible.
  Create a separate, small .csh file to do anything fancy involving
  csh and those punctuation characters.  See abc-iprove.csh for one
  example, which involves creating a temp file."

  ;; CSH is at least as dangerous as SYSCALL, so would need a
  ;; trust-tag if made into an ACL2 command.

  ;; Implementation note: For CSH to work, the csh shell command
  ;; 'echo' with no arguments must 'flush' its output, in addition to
  ;; printing a newline, or in Lisp terminology, 'echo' must
  ;; 'finish-output'.  We believe 'echo' does that, but we have not
  ;; tracked down where it officially says so.  If 'echo' does not
  ;; flush its output, then the READ-CHAR below may wait forever.
  ;; Probably, adding a 'sync' command would guarantee the flushing.

  (with-standard-io-syntax
   (pushnew 'csh-stop ccl::*save-exit-functions*)
   (unless (ccl::external-process-p *csh-process*) (csh-start))
   (prog*
    ((p *csh-process*)
     (command (if (eq (car args) :stream) (cdr args) args))
     (is (ccl::external-process-input-stream p))
     (os (ccl::external-process-output-stream p))
     (x nil))

    (unless args
      (return
       (list :status (ccl::external-process-status p)
             :process p
             :input-stream (ccl::external-process-input-stream p)
             :output-stream (ccl::external-process-output-stream p)
             :temp-file-name *csh-temporary-file-name*)))

    ;; It seems so peculiar to 'print' to an 'input' here, but input
    ;; and output are opposite on the other end.

    (write-string (args-spaced command) is)
    (write-line " > $tm < /dev/null ; echo" is)
    (finish-output is)
    (setq x (read-char os nil :eof))

    ;; If necessary, READ-CHAR will wait.

    (unless (and (eql x #\Newline) (null (listen os)))
      (loop while (characterp x) do
            (write-char x *error-output*)
            (force-output *error-output*)
            (setq x (read-char-no-hang os nil :eof)))
      (csh-stop)
      (error "CSH: ~a." args))
    (return
     (cond
      ((eq :stream (car args)) (open *csh-temporary-file-name*))
      (t (with-open-file (o *csh-temporary-file-name*)
           (with-output-to-string
             (s)
             (loop while
                   (and (not (eq :eof (setq x (read-char
                                               o nil :eof))))
                        (or (not (eql x #\Newline))
                            (not (eq :eof (peek-char
                                           nil o nil :eof)))))
                   do (write-char x s))))))))))

(defv *sh-process* nil

  "When not NIL, *SH-PROCESS* has as its value the Lisp process
  object for an underlying sh process.")

(defv *sh-temporary-file-name* nil

  "When not NIL, *SH-TEMPORARY-FILE-NAME* has as it value a stream
  via which an underlying sh process sends synchronizing info back to
  Lisp.")

#+Clozure
(defn1 sh-stop ()

  "(sh-stop) kills the subsidiary sh process if there is one."

  (ignore-errors
    (when (ccl::external-process-p *sh-process*)
      (ccl::signal-external-process *sh-process* 9)))
  (setq *sh-process* nil)
  (ignore-errors
    (when (and *sh-temporary-file-name*
               (probe-file *sh-temporary-file-name*))
      (delete-file *sh-temporary-file-name*)))
  (setq *sh-temporary-file-name* nil))

#+Clozure
(defv *sh-start-string*
  "tm=`mktemp /tmp/acl2-sh-temp.XXXXXX`; echo $tm")

#+Clozure
(defn1 sh-start ()

  "(SH-START) creates a subsidiary sh process.  SH-START
  is called automatically by SH."

  (sh-stop)
  (setq *sh-process*
    (ccl::run-program "/bin/sh" nil
                      :input :stream
                      :output :stream
                      :wait nil))
  (let ((is (ccl::external-process-input-stream *sh-process*)))
    (our-syntax
     (write-line *sh-start-string* is)
     (finish-output is)
     (setq *sh-temporary-file-name*
       (read-line
        (ccl::external-process-output-stream *sh-process*)
        nil
        :eof)) ; wait
     (cond ((probe-file *sh-temporary-file-name*)
            *sh-temporary-file-name*)
           (t (error "sh-start: failed."))))))

#+Clozure
(defun sh (&rest args)

  "SH is a raw Lisp function.  (SH) returns a status report on a lower
  'sh' shell process, which is created if necessary, and which, once
  created, is the value of the Lisp variable *SH-PROCESS*.

  On each call to SH, one sh shell command is executed.  The same sh
  process executes all the commands.  That is, a new process is not
  created for each command, but the same sh process is used
  repeatedly.  This may significantly reduce the copying overhead
  incurred by a call to FORK to create a new process under a big Lisp
  job, as the ACL2 function SYSTEM-CALL might on each call.

  (SH :STREAM arg1 ... argn) executes a single sh command, namely,
  the string obtained by placing spaces between the strings, symbols,
  or numbers arg1 ... argn.  A stream of the command's standard output
  is returned as the value of SH.  For example,

     (SH :STREAM '|gunzip -c foo.gz|)

  returns an open input stream that contains the ungzipped contents of
  the file 'foo.gz'.

  If arg1 is not :STREAM, (SH arg1 ... argn) executes one sh command
  exactly as in the :STREAM case, namely, the string obtained by
  placing spaces between the strings, symbols, or numbers arg1
  ... argn.  But the standard output of the command is printed into a
  string, which is returned as the value of SH.  If the last character
  of that output is a newline, it is not included in the string
  returned.

  The standard output from the command is diverted through a unique
  /tmp file, whose name is the value of the variable
  *SH-TEMPORARY-FILE-NAME*.

  If the command sends any output to error output, a Lisp ERROR is
  caused and the error output of the command is printed to Lisp's
  *STANDARD-OUTPUT*.

  SH is almost identical to CSH.

  For the best of hacking luck, each single SH command fed to SH
  should be only one line long, and should not involve any of the
  fancier SH characters such *, ~, !, =, |, <, >, &, \, {, }, single
  quote, semicolon, period, question mark, parentheses, square
  brackets, double quote, and backquote.  Stick to alphanumeric
  characters, space, and hyphen if possible.  Create a separate, small
  .sh file to do anything fancy involving sh and such punctuation
  characters.  See abc-iprove.csh for one example, which involves
  creating a temp file."

  (with-standard-io-syntax
   (pushnew 'sh-stop ccl::*save-exit-functions*)
   (unless (ccl::external-process-p *sh-process*) (sh-start))
   (prog*
    ((p *sh-process*)
     (command (if (eq (car args) :stream) (cdr args) args))
     (is (ccl::external-process-input-stream p))
     (os (ccl::external-process-output-stream p))
     (x nil))

    (unless args
      (return
       (list :status (ccl::external-process-status p)
             :process p
             :input-stream (ccl::external-process-input-stream p)
             :output-stream (ccl::external-process-output-stream p)
             :temp-file-name *sh-temporary-file-name*)))

    ;; It seems so peculiar to 'print' to an 'input' here, but input
    ;; and output are opposite on the other end.

    (write-string (args-spaced command) is)
    (write-line " > $tm < /dev/null ; echo" is)
    (finish-output is)
    (setq x (read-char os nil :eof))

    ;; If necessary, READ-CHAR will wait.

    (unless (and (eql x #\Newline) (null (listen os)))
      (loop while (characterp x) do
            (write-char x *error-output*)
            (force-output *error-output*)
            (setq x (read-char-no-hang os nil :eof)))
      (sh-stop)
      (error "SH: ~a." args))
    (return
     (cond
      ((eq :stream (car args))
       (open *sh-temporary-file-name*))
      (t (with-open-file
           (o *sh-temporary-file-name*)
           (with-output-to-string
             (s)
             (loop while
                   (and (not (eq :eof (setq x (read-char
                                               o nil :eof))))
                        (or (not (eql x #\Newline))
                            (not (eq :eof (peek-char
                                           nil o nil :eof)))))
                   do (write-char x s))))))))))


