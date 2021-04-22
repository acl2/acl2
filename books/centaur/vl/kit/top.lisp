; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "lint")
(include-book "shell")
(include-book "gather")
(include-book "zip")
(include-book "json")
(include-book "server")
(include-book "oslib/argv" :dir :system)
(include-book "centaur/misc/intern-debugging" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "centaur/nrev/fast" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

#||

; Fool the dependency scanner into certifying testing books as part
; of building top.cert

(include-book "../loader/lexer/tests")
(include-book "../loader/preprocessor/tests")
(include-book "../loader/parser/tests/top")

; Fool the dependency scanner into building additional books loaded
; in save.lsp
(include-book "oslib/top" :dir :system)

||#

(defconst *vl-generic-help*
  "VL Verilog Toolkit
Copyright (C) 2008-2016 Centaur Technology <http://www.centtech.com>

Usage: vl <command> [arguments]

Commands:

  help    Print this message, or get help on a particular VL command
  lint    Find potential bugs in a Verilog design
  gather  Collect Verilog files into a single file
  server  Start a VL web server for web-based module browsing
  shell   Interactive VL shell (for experts)
  zip     Save a .vlzip file for the VL web server

Use 'vl help <command>' for help on a specific command.
")

(make-event
 `(defsection kit
    :parents (vl)
    :short "A command-line program for using @(see VL) in basic ways."

    :long ,(cat "<p>The VL Toolkit (``kit'') is a standalone program that lets
you use various parts of VL from the command-line.  It currently includes:</p>

<ul>
<li>A Verilog/SystemVerilog linter, @(see vl-lint)</li>
<li>A server that powers a web-based module browser, @(see vl-server)</li>
<li>A shell for launching @(see acl2) with VL pre-loaded, @(see vl-shell)</li>
<li>Some miscellaneous commands.</li>
</ul>

<p>Note that the kit is intended to be a <b>convenient, but not complete</b>
way to use VL.  We generally intend VL to be a useful ACL2 library, not a
standalone program.  Most VL functions don't have any command-line
wrappers.</p>

<h3>Installation</h3>

<p>To build the kit, just run @('make vl') in the @('acl2/books') directory.
This should produce an executable at @('acl2/books/centaur/vl/bin/vl').</p>

<h3>Usage</h3>

<p>The top-level @('vl') program is really just a wrapper for several
sub-commands:</p>

@({" *vl-generic-help* " })

<h3>Extending the Kit</h3>

<p>If you develop your own VL functionality, you can create an extended kit
that knows how to run your additional commands.  See in particular @(see
vl-toolkit-other-command).</p>")))


(defsection vl-toolkit-help-message
  :parents (vl-help)
  :short "Look up the help message for a VL kit program."
  :long "<p>This is attachable so advanced users can add additional
commands.</p>

@(def *vl-help-messages*)
@(def vl-toolkit-help-message)"

  (defconst *vl-help-messages*
    (list (cons "help"   *vl-generic-help*)
          (cons "lint"   *vl-lint-help*)
          (cons "gather" *vl-gather-help*)
          (cons "server" *vl-server-help*)
          (cons "shell"  *vl-shell-help*)
          (cons "zip"    *vl-zip-help*)
          ))

  (encapsulate
    (((vl-toolkit-help-message *) => *
      :formals (command)
      :guard (stringp command)))
    (local (defun vl-toolkit-help-message (command)
             (declare (ignore command))
             nil))
    (defthm vl-toolkit-help-message-constraint
      (or (not (vl-toolkit-help-message command))
          (stringp (vl-toolkit-help-message command)))
      :rule-classes :type-prescription)))


(define vl-toolkit-help-message-default ((command stringp))
  :parents (vl-toolkit-help-message)
  :returns (help (or (not help)
                     (stringp help))
                 :rule-classes :type-prescription)
  (cdr (assoc-equal command *vl-help-messages*))
  ///
  (defattach vl-toolkit-help-message vl-toolkit-help-message-default))


(define vl-help ((args string-listp) &key (state 'state))
  :parents (vl-main)
  :short "Show help on how to use VL @(see kit) commands."
  :long "<p>This just implements the @('vl help') command.</p>"
  (b* (((unless (or (atom args)
                    (atom (cdr args))))
        (die "Usage: vl help <command>~%")
        state)
       (command (if (atom args)
                    "help"
                  (car args)))
       (help    (vl-toolkit-help-message command))
       ((unless help)
        (die "Unknown command ~s0." command)
        state))
    (vl-cw-ps-seq (vl-print help))
    state))


(defsection vl-toolkit-other-command
  :parents (vl-main)
  :short "Attachable handler for extending the VL @(see kit) with additional
commands."

  :long "<p>By default this just dies with an error message that says the
command is unknown.  But it is attachable, so advanced users can extend the
toolkit with their own commands.</p>

@(def vl-toolkit-other-command)"

  (encapsulate
    (((vl-toolkit-other-command * * state) => state
      :formals (command args state)
      :guard (and (stringp command)
                  (string-listp args)
                  (state-p1 state))))
    (local (defun vl-toolkit-other-command (command args state)
             (declare (ignore command args)
                      (xargs :stobjs state))
             state))))


(define vl-toolkit-other-command-default ((command stringp)
                                          (args string-listp)
                                          state)
  :parents (vl-toolkit-other-command)
  :ignore-ok t
  (progn$ (die "Unknown command ~s0.~%" command)
          state)
  ///
  (defattach vl-toolkit-other-command vl-toolkit-other-command-default))


(define vl-main (&key (state 'state))
  :parents (kit)
  :short "Top level entry point into the @(see kit).  This just handles the
command-line parsing and invokes the right sub-command for the @('vl')
executable."

  :long "<p>Note that the kit is extensible and it is relatively easy to add
new commands even without releasing your code.  See in particular @(see
vl-toolkit-other-command).</p>"

  (b* ((state
        ;; Since the VL executable is a non-interactive program, there's no
        ;; chance to enter a break loop if something crashes.  Printing a
        ;; backtrace before aborting, then, can be extremely useful.
        (set-debugger-enable :bt-break))
       (- (gc-verbose t))
       (- (acl2::tshell-ensure))
       ((mv argv state) (oslib::argv))

       ((unless (consp argv))
        (b* ((state (vl-help '("help"))))
          (exit-fail)
          state))

       ((cons cmd args) argv)

       ((when (or (equal cmd "help")
                  (equal cmd "-h")
                  (equal cmd "--help")))
        (b* ((state (vl-help args)))
          (exit-ok)
          state))

       ((when (equal cmd "lint"))
        (b* ((state (vl-lint-top args)))
          ;; hack to make interactive lint debugging work and not just exit
          (and (not (intersectp-equal '("--shell" "--post-shell") args))
               (exit-ok))
          state))

       ((when (equal cmd "gather"))
        (b* ((state (vl-gather-top args)))
          (exit-ok)
          state))

       ((when (equal cmd "zip"))
        (b* ((state (vl-zip-top args)))
          (exit-ok)
          state))

       ((when (equal cmd "json"))
        (b* ((state (vl-json-top args)))
          (exit-ok)
          state))

       ((when (equal cmd "server"))
        (b* ((state (vl-server-top args)))
          ;; Do not call exit here, same reason as 'shell'
          state))

       ((when (equal cmd "shell"))
        (b* ((state (vl-shell-top args)))
          ;; Do NOT exit here.  If you do, commands like :q quit entirely
          ;; instead of dropping you into raw Lisp.
          state))
       )

    (vl-toolkit-other-command cmd args state)))

