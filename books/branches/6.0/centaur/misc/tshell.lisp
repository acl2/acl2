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


; TSHELL is an alternative to things like sys-call and run-program.  It is
; similar to the CSH and SH commands in hons-raw.lisp, and like CSH and SH it
; does not require a "fork" for every external program invocation.  Instead, we
; start up a single BASH process with (TSHELL-START) ahead of time, then use
; this process to issue every command.  Forking is often problematic when many
; gigabytes of memory are allocated, so the basic idea is to call TSHELL-START
; The basic idea is to call TSHELL-START early in the life of the Lisp image,
; before much memory allocation is done.
;
; Here are TSHELL's features that are not in CSH or SH:
;
;   (1) You can have the program's output printed at runtime, but still capture
;       its output as a list of strings.
;
;   (2) You can get the exit code from the program.
;
;   (3) If you interrupt, :continue will let you keep running the program, but
;       if you :q then a KILL signal will be sent.
;
; The third feature was particularly important to me for AIGPU, because we
; don't want some runaway AIGPU process on prime getting in the way and
; stopping us from doing other tautology checking.


; This file defines the ACL2 interface for tshell; see tshell-raw.lsp for the
; implementation.

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)
(include-book "str/strprefixp" :dir :system)

;; (depends-on "tshell-raw.lsp")

(defun tshell-start ()
  (declare (xargs :guard t))
  (cw "Warning: tshell-start not redefined."))

(defun tshell-stop ()
  (declare (xargs :guard t))
  (cw "Warning: tshell-stop not redefined."))

(defun tshell-ensure ()
  (declare (xargs :guard t))
  (cw "Warning: tshell-ensure not redefined."))

(defun tshell-run-background (cmd)
  (declare (xargs :guard t)
           (ignorable cmd))
  (cw "Warning: tshell-run-background not redefined."))

(defun tshell-useless-clauseproc (clause)
  (list clause))

(defttag tshell)

(acl2::define-trusted-clause-processor
  tshell-useless-clauseproc
  (tshell-call-fn1)
  :partial-theory
  (encapsulate
    (((tshell-call-fn1 * * *) => (mv * * *)))

    (local (defun tshell-call-fn1 (x y z)
             (declare (ignorable x y z))
             (mv nil nil nil)))))

(defun tshell-call-fn (cmd print save)
  (declare (xargs :guard t))
  (tshell-call-fn1 cmd print save))

(defmacro tshell-call (cmd &key (print 't) (save 't))
  `(tshell-call-fn ,cmd ,print ,save))

(acl2::include-raw "tshell-raw.lsp")

(acl2::progn!
 (set-raw-mode t)
 (defun tshell-call-fn (cmd print save)
   (tshell cmd :print print :save save)))
