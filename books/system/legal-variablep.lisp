; legal-variablep.lisp -- admit and verify guards of legal-variablep, etc.
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")

(local (in-theory (disable member-equal)))
(verify-termination legal-variable-or-constant-namep)
(verify-termination legal-variablep)
(verify-termination arglistp1)
(verify-termination arglistp)
(verify-termination lambda-keywordp)

(verify-guards legal-variable-or-constant-namep)
(verify-guards legal-variablep)
(verify-guards arglistp1)
(verify-guards arglistp)
(verify-guards lambda-keywordp)

(verify-termination legal-constantp ; and guards [added by Matt K.]
  (declare (xargs :verify-guards t)))

(verify-termination find-first-bad-arg ; See later in file for verify-guards.
                    (declare (xargs :verify-guards nil)))

(defthm symbolp-when-legal-variablep
  (implies (legal-variablep x)
           (and (symbolp x)
                (not (equal x t))
                (not (equal x nil))))
  :rule-classes :compound-recognizer)

(local (defthm find-first-bad-arg-lemma-lemma
         (implies (and (character-listp x)
                       (atom (cdr x))
                       (equal (car x) #\&))
                  (equal "&" (coerce x 'string)))
         :rule-classes nil))

(local (defthm find-first-bad-arg-lemma
         (implies (and (not (equal "&" s))
                       (equal (car (coerce s 'list)) #\&)
                       (stringp s))
                  (consp (cdr (coerce s 'list))))
         :hints (("Goal" :use ((:instance find-first-bad-arg-lemma-lemma
                                          (x (coerce s 'list))))))))

(verify-guards find-first-bad-arg
               :hints (("Goal" :in-theory (enable string< string<-l))))

; Since we're verifying these terminate, it seems reasonable to disable them here.

(in-theory (disable legal-variable-or-constant-namep
                    legal-variablep
                    arglistp1
                    arglistp
                    lambda-keywordp
                    legal-constantp1
                    find-first-bad-arg))
