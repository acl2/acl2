; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "json")
(include-book "lint")
(include-book "model")
(include-book "shell")
(include-book "pp")
(include-book "gather")
(include-book "oslib/argv" :dir :system)
(include-book "centaur/esim/stv/stv2c/top" :dir :system)
(include-book "centaur/misc/intern-debugging" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "centaur/nrev/fast" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defconst *vl-generic-help*
  "VL Verilog Toolkit
Copyright (C) 2008-2013 Centaur Technology <http://www.centtech.com>

Usage: vl <command> [arguments]

Commands:

  help    Print this message, or get help on a particular VL command
  json    Convert Verilog designs into JSON files (for easy parsing)
  lint    Find potential bugs in a Verilog design
  model   Translate Verilog designs for the ACL2 theorem prover
  stv2c   Translate symbolic runs of Verilog designs into C++
  pp      Preprocess Verilog designs
  gather  Collect Verilog files into a single file
  shell   Interactive VL shell (for experts)

Use 'vl help <command>' for help on a specific command.
")

(make-event
 `(defsection kit
    :parents (vl)
    :short "A command-line program for using VL in basic ways."

    :long ,(cat "<p>@(see VL) is mainly an ACL2 library, and a lot of its
functionality and features are available only from within ACL2.  However, to
make VL more widely approachable, we have bundled up certain pieces of it into
a command line program, which we call the Kit.</p>

<p>The kit is ordinarily built by running @('make vl') in the @('acl2/books')
directory.  The source files are found in @('acl2/books/centaur/vl/kit') but
the resulting executable is put into @('acl2/books/centaur/vl/bin') and is
simply named @('vl').</p>

<p>This @('vl') program is really just a wrapper for several sub-commands:</p>

@({" *vl-generic-help* " })")))


(defsection vl-toolkit-help-message
  :parents (vl-help)
  :short "Look up the help message for a VL kit program."
  :long "<p>This is attachable so advanced users can add additional
commands.</p>

@(def *vl-help-messages*)
@(def vl-toolkit-help-message)"

  (defconst *vl-help-messages*
    (list (cons "help"   *vl-generic-help*)
          (cons "json"   *vl-json-help*)
          (cons "lint"   *vl-lint-help*)
          (cons "model"  *vl-model-help*)
          (cons "stv2c"  acl2::*stv2c-help*)
          (cons "pp"     *vl-pp-help*)
          (cons "gather" *vl-gather-help*)
          (cons "shell"  *vl-shell-help*)))

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
  :parents (kit)
  :short "The @('vl help') command."

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
  :parents (kit)
  :short "Handler for additional vl toolkit commands."

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
  (progn$
   (die "Unknown command ~s0.~%" command)
   state)
  ///
  (defattach vl-toolkit-other-command vl-toolkit-other-command-default))


(define vl-main (&key (state 'state))
  :parents (kit)
  :short "The top-level @('vl') meta-command."

  (b* ((state
        ;; Since the VL executable is a non-interactive program, there's no
        ;; chance to enter a break loop if something crashes.  Printing a
        ;; backtrace before aborting, then, can be extremely useful.
        (set-debugger-enable :bt))
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

       ((when (equal cmd "json"))
        (b* ((state (vl-json args)))
          (exit-ok)
          state))

       ((when (equal cmd "lint"))
        (b* ((state (vl-lint args)))
          (exit-ok)
          state))

       ((when (equal cmd "model"))
        (b* ((state (vl-model args)))
          (exit-ok)
          state))

       ((when (equal cmd "pp"))
        (b* ((state (vl-pp args)))
          (exit-ok)
          state))

       ((when (equal cmd "gather"))
        (b* ((state (vl-gather args)))
          (exit-ok)
          state))

       ((when (equal cmd "stv2c"))
        (b* ((state (acl2::stv2c args)))
          (exit-ok)
          state))

       ((when (equal cmd "shell"))
        (b* ((state (vl-shell args)))
          ;; Do NOT exit here.  If you do, commands like :q quit entirely
          ;; instead of dropping you into raw Lisp.
          state))
       )

    (vl-toolkit-other-command cmd args state)))

