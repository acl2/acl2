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
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/define" :dir :system)
;; (include-book "std/strings/defs" :dir :system) ;; used in the raw code
(include-book "quicklisp/shellpool" :dir :system)
;; (depends-on "tshell-raw.lsp")

(defxdoc tshell
  :parents (interfacing-tools sys-call)
  :short "A fancy alternative to @(see sys-call) that features output streaming
and capture, exit-code capture, interruption, and better control over when
forking occurs."

  :long "<p><b>Tshell</b> is an ACL2 wrapper around the <a
href='https://github.com/jaredcdavis/shellpool/'>Shellpool</a> library for
Common Lisp, which is available via @(see quicklisp).  It allows you to run
external programs from within ACL2, and has many nice features for handling
output, etc.</p>

<p>Shellpool has its own <a
href='https://github.com/jaredcdavis/shellpool/blob/master/DOC.md'>API
documentation</a>, which you may find useful.</p>


<h3>Usage</h3>

<p>Note that Tshell requires @(see trust-tag)s because its implementation
requires some raw Lisp code.  The book to load is:</p>

@({
    (include-book \"centaur/misc/tshell\" :dir :system)
})

<p>After loading this book, the first step is then to launch one or more
shells, e.g.,</p>

@({
    (value-triple (tshell-ensure))
})

<p>This is a thin wrapper around @('shellpool:ensure').  It launches the
subsidiary bash shells that tshell/shellpool will use to run programs.  This
step requires forking ACL2 itself, so you typically want to do this early in
your ACL2 session, before you have allocated tons of memory.</p>

<p>After that, you can start launching programs using @(see tshell-call) or
@(see tshell-run-background).  For instance,</p>

@({
    ACL2 !>(tshell-call \"echo hello\")
    (tshell-call \"echo hello\")
    hello             ;; <-- output from subprogram, streamed
    (0 (\"hello\"))   ;; <-- exit code 0, output lines
})")


(define tshell-start (&optional ((n posp "How many shells to start.") '1))
  :parents (tshell)
  :short "Start additional shells for running sub-processes (forks ACL2)."
  :returns (nil)
  :long "<p>We usually instead use @(see tshell-ensure), which only starts up
new bash processes if they aren't already running.</p>

<p>If you want to use this in a book, you can wrap it in a @(see value-triple),
e.g.,</p>

@({ (value-triple (tshell-start)) })

<p>This is essentially just @('shellpool:start'); see the <a
href='https://github.com/jaredcdavis/shellpool/blob/master/DOC.md'>Shellpool
API documentation</a> for details.</p>"
  (declare (ignorable n))

  (cw "Warning: under-the-hood definition of ~s0 not installed?"
      __function__))


(define tshell-ensure (&optional ((n posp "How many shells to start.") '1))
  :parents (tshell)
  :short "Ensure that shells are available for running sub-processes (may fork ACL2)."
  :returns (nil)
  :long "<p>If you want to use this in a book, you can wrap it in a @(see
value-triple), e.g.,</p>

@({ (value-triple (tshell-ensure)) })

<p>It's also typically useful to put this before calls of @(see tshell-call) or
@(see tshell-run-background), to start up the shells if the user hadn't already
gotten them started earlier.</p>

<p>This is essentially just @('shellpool:ensure'); see the <a
href='https://github.com/jaredcdavis/shellpool/blob/master/DOC.md'>Shellpool
API documentation</a> for details.</p>"

  (declare (ignorable n))
  (cw "Warning: under-the-hood definition of ~s0 not installed?"
      __function__))


(defun tshell-useless-clauseproc (clause)
  (list clause))

(defsection tshell-call-fn1
  :parents (tshell)
  :short "Logical story for @(see tshell-call)."

  :long "<p>We use the @(':partial-theory') feature of @(see
define-trusted-clause-processor) to introduce a function, @('tshell-call-fn1'),
about which we assume nothing.</p>

<p>BOZO this probably isn't sound.  Don't we get the equality axioms for
tshell-call-fn1?  But those aren't necessarily satisfied by command-line
programs.  We should probably be using oracle reads instead, but then we'll
need to involve state.</p>"

  (partial-encapsulate
   (((tshell-call-fn1 * * *) => (mv * *)))
   nil ;; supporters
   (local (defun tshell-call-fn1 (x y z)
            (declare (ignorable x y z))
            (mv 0 nil)))

   (defthm return-type-of-tshell-call-fn1
     (b* (((mv status lines)
           (tshell-call-fn1 cmd print save)))
       (and (natp status)
            (string-listp lines))))))


(define tshell-call
  :parents (tshell)
  :short "Use tshell to run a sub-program and wait for it to finish.  (never
forks ACL2)."

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

  :long "<p>Before using @('tshell-call') you need to make sure that the bash
processes for tshell have been started; see @(see tshell-start) and @(see
tshell-ensure).</p>

<p>Note that @(':save') and @(':print') are independent from one-another; you
can print without saving, save without printing, save and print, or do neither
and just get the exit code.</p>"

  (progn$
   (cw "Warning: under-the-hood definition of ~s0 not installed?"
       __function__)
   (tshell-call-fn1 cmd print save)))

(define tshell-run-background
  :parents (tshell)
  :short "Use tshell to run a sub-program in the background; don't wait for it
to finish and don't get any output from it. (never forks ACL2)."

 ((cmd stringp "The command to give to the shell.  It had better be
                well-formed.  It can probably use input/output redirection
                without problems.  We're basically going to run: @('(cmd) &')."))
 :returns (nil)
 :ignore-ok t
 (cw "Warning: under-the-hood definition of ~s0 not installed?"
     __function__))

(defttag tshell)

(include-raw "tshell-raw.lsp")



