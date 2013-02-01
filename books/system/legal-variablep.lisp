; legal-variablep.lisp -- admit and verify guards of legal-variablep, etc.
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")

(local (in-theory (disable member-equal)))
(verify-termination legal-variable-or-constant-namep)
(verify-termination legal-variablep)
(verify-termination arglistp1)
(verify-termination arglistp)
(verify-termination lambda-keywordp)
(verify-termination legal-constantp1)

(verify-guards legal-variable-or-constant-namep)
(verify-guards legal-variablep)
(verify-guards arglistp1)
(verify-guards arglistp)
(verify-guards lambda-keywordp)

;; bleh, someone else can prove the guards
(verify-termination find-first-bad-arg
                      (declare (xargs :verify-guards nil)))

(defthm symbolp-when-legal-variablep
  (implies (legal-variablep x)
           (and (symbolp x)
                (not (equal x t))
                (not (equal x nil))))
  :rule-classes :compound-recognizer)

; Since we're verifying these terminate, it seems reasonable to disable them here.

(in-theory (disable legal-variable-or-constant-namep
                    legal-variablep
                    arglistp1
                    arglistp
                    lambda-keywordp
                    legal-constantp1
                    find-first-bad-arg))
