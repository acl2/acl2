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
(include-book "tools/include-raw" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "str/strprefixp" :dir :system) ;; used in the raw code
;; (depends-on "tshell-raw.lsp")

(defxdoc tshell
  :parents (interfacing-tools sys-call)
  :short "A fancy alternative to @(see sys-call) that features output streaming
and capture, exit-code capture, interruption, and better control over when
forking occurs. (CCL only)"

  :long "<p><b>Tshell</b> is an alternative to things like ACL2's @(see
sys-call) or Lisp-specific tools like CCL's @('run-program') that offers
some nice features:</p>

<ul>

<li><i>Output streaming and capture</i>.  You can (optionally) have the
program's output printed at runtime, but still (optionally) capture its output
as a strings list.  This makes it easy to show a user a long-running
sub-program's output as it's being created, but also parse and analyze the
program's output with your ACL2 code.</li>

<li><i>Exit code.</i> Yep, you get it.</li>

<li><i>Interruption.</i> Interrupts are handled gracefully.  After you
interrupt (e.g., Control C), you can @(':continue') to keep running the
program, or @(':q') to send the sub-program a KILL signal.</li>

<li><i>Forking.</i> Sub-programs are launched with a separate shell, so you can
avoid <a
href='http://en.wikipedia.org/wiki/Fork_%28operating_system%29'>forking</a>
your ACL2 image when you have dozens of GB allocated.  (Trying to do so
typically results in ACL2 being killed, despite the wonders of copy-on-write
pages.)</li>

<li><i>Background jobs.</i> You can optionally launch programs in the
background.  We use this, e.g., to launch waveform viewers which the user can
then interact with independently from ACL2.</li>

</ul>

<h3>Usage</h3>

<p>Note that Tshell requires a trust tag because its implementation requires
some raw Lisp code.  The book to load is:</p>

@({
 (include-book \"centaur/misc/tshell\" :dir :system)
})

<p>After loading this book, the first step is then to launch a tshell,
e.g.,</p>

@({
 (value-triple (tshell-ensure))
})

<p>This will launch the subsidiary bash shell that tshell will use to run
programs (actually three bash shells: one to launch programs, one to kill them,
and one for background jobs).  This step requires forking ACL2 itself, so you
typically want to do this early in your ACL2 session, before you have allocated
tons of memory.</p>

<p>After that, you can start launching programs using @(see tshell-call) or
@(see tshell-run-background).  For instance,</p>

@({
    ACL2 !>(tshell-call \"echo hello\")
    (tshell-call \"echo hello\")
    hello             ;; <-- output from subprogram, streamed
    (T 0 (\"hello\"))   ;; <-- finished ok, exit code 0, output lines
})")


(define tshell-stop ()
  :parents (tshell)
  :short "Stop any subsidiary bash processes that tshell is running."
  :returns (nil)
  :long "<p>You could call this when you're done using tshell.  We typically
don't bother, since the shells get closed when ACL2 exits anyway.</p>"

  (cw "Warning: under-the-hood definition of ~s0 not installed?"
      __function__))


(define tshell-start ()
  :parents (tshell)
  :short "Stop any subsidiary bash processes that tshell is running, then
start new ones. (always forks ACL2)"
  :returns (nil)
  :long "<p>We usually instead use @(see tshell-ensure), which only starts up
new bash processes if they aren't already running.</p>

<p>If you want to use this in a book, you can wrap it in a @(see value-triple),
e.g.,</p>

@({ (value-triple (tshell-start)) })"

  (cw "Warning: under-the-hood definition of ~s0 not installed?"
      __function__))


(define tshell-ensure ()
  :parents (tshell)
  :short "Starts up the subsidiary bash processes for tshell, but only if they
are not already running. (sometimes forks ACL2)"
  :returns (nil)
  :long "<p>If you want to use this in a book, you can wrap it in a @(see
value-triple), e.g.,</p>

@({ (value-triple (tshell-ensure)) })

<p>It's also typically useful to put this before calls of @(see tshell-call) or
@(see tshell-run-background), to start up the shells if the user hadn't already
gotten them started earlier.</p>"

  (cw "Warning: under-the-hood definition of ~s0 not installed?"
      __function__))



(defun tshell-useless-clauseproc (clause)
  (list clause))

(defttag tshell)

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

  (acl2::define-trusted-clause-processor
   tshell-useless-clauseproc
   (tshell-call-fn1)
   :partial-theory
   (encapsulate
     (((tshell-call-fn1 * * *) => (mv * * *)))

     (local (defun tshell-call-fn1 (x y z)
              (declare (ignorable x y z))
              (mv nil 0 nil)))

     (defthm return-type-of-tshell-call-fn1
       (b* (((mv finishedp status lines)
             (tshell-call-fn1 cmd print save)))
         (and (booleanp finishedp)
              (natp status)
              (string-listp lines)))))))

(define tshell-call
  :parents (tshell)
  :short "Use tshell to run a sub-program and wait for it to finish.  (never
forks ACL2)."

  ((cmd stringp
        "This should be an ordinary shell command that takes no input and does
         not attempt to do any I/O redirection.  It can have arguments, e.g.,
         you can write something like @('\"echo hello\"') here.  But it won't
         work to do something like @('\"echo < foo.txt\"').")
   &key

   ((print booleanp
           "This says whether we should print the lines produced by @('cmd') as
            they are produced.")
    't)

   ((save booleanp
          "This says whether we should capture the output lines produced by
           @('cmd') and return them as the @('lines') output.  If you aren't
           going to analyze the program's output, you might want to set this
           to @('nil') to cut down on memory usage.")
    't))

  :returns
  (mv (finishedp booleanp :rule-classes :type-prescription
                 "This will be @('t') if the command completed normally, or
                  @('nil') if the command was interrupted.")

      (exit-status natp :rule-classes :type-prescription
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

(include-raw "tshell-raw.lsp")



