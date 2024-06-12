(in-package "ACL2")

(include-book "tshell")
;; (depends-on "tshell-unsound-raw.lsp")

(defsection tshell-call-unsound-fn1
  :parents (tshell tshell-call-unsound tshell-call-fn1)
  :short "Unsound variant of @(see tshell-call-fn1) which doesn't take @(see
state)."

  (partial-encapsulate
   (((tshell-call-unsound-fn1 * * *) => (mv * *)))
   nil ;; supporters
   (local (defun tshell-call-unsound-fn1 (x y z)
            (declare (ignorable x y z))
            (mv 0 nil)))

   (defthm return-type-of-tshell-call-unsound-fn1
     (b* (((mv status lines)
           (tshell-call-unsound-fn1 cmd print save)))
       (and (natp status)
            (string-listp lines))))))


(define tshell-call-unsound
  :parents (tshell tshell-call)
  :short "Unsound variant of @(see tshell-call) which doesn't take @(see state)."

  ((cmd stringp
        "This is the command to run.  It can actually be a full-blown shell script.
         It should not require any input from the user.")
   &key
   ((print symbolp
           "This says whether we should print the lines produced by @('cmd') as
           they are produced.  @('nil') means print nothing, @('t') means print
           everything, and any other symbol @('fn') means call the raw Lisp
           function @('fn') to do the printing.  Custom output functions are an
           advanced feature; see @('tshell-raw.lsp') for details.")
    't)

   ((save booleanp
          "This says whether we should capture the stdout/stderr lines produced
          by @('cmd') and return them as the @('lines') output.  If you aren't
          going to analyze the program's output, you might want to set this to
          @('nil') to cut down on memory usage.")
    't))

  :returns
  (mv (exit-status natp :rule-classes :type-prescription
                   "The exit code from the command.  Typically 0 means success
                    and any non-zero value means failure.  This is only
                    sensible if @('finishedp') is @('t').")

      (lines string-listp
             "The output from the command (from both standard output and
              standard error.)  Note that @('lines') will always just be
              @('nil') if you're using @(':save nil')."))

  :long "<p>This is equivalent to the old version of @(see tshell-call), before
it was made sound by adding state.</p>

<p>It is unsound because it is not functional; two executions with the same
arguments might yield different results.</p>

<p>See @(see tshell-call) for usage information.</p>"

  (progn$
   (cw "Warning: under-the-hood definition of ~s0 not installed?"
       __function__)
   (tshell-call-unsound-fn1 cmd print save)))


(defttag tshell-unsound)

(include-raw "tshell-unsound-raw.lsp")
