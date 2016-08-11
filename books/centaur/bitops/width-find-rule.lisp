; Centaur Bitops Library
; Copyright (C) 2010-2016 Centaur Technology
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

; signed-byte-p.lisp
; Original author: Sol Swords <sswords@centtech.com>


(in-package "BITOPS")

(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "ihsext-basics")

(local (in-theory (disable unsigned-byte-p signed-byte-p)))

(defun check-width-rule (rule target-width lhs-term)
  (declare (xargs :mode :program))
  (b* (((acl2::rewrite-rule r) rule)
       ((unless (and (equal r.rhs acl2::*t*)
                     (consp (third r.lhs))))
        (mv nil nil))
       ((mv okp subst) (acl2::one-way-unify (third r.lhs) lhs-term))
       ((unless okp)
        (mv nil nil))
       (width (second r.lhs))
       (width (if (symbolp width)
                  (cdr (assoc width subst))
                width))
       ((unless (and (quotep width)
                     (< (unquote width) target-width)))
        (mv nil nil)))
    (mv width (and r.hyps t))))

(defun look-for-width-rule (rules target-width lhs-term)
  (declare (xargs :mode :program))
  ;; returns (mv width conditionalp)
  (b* (((when (atom rules)) (mv nil nil))
       ((mv width condp) (check-width-rule (car rules) target-width lhs-term))
       ((when (and width (not condp)))
        (mv width nil))
       ((mv width2 condp2) (look-for-width-rule (cdr rules) target-width lhs-term))
       ((when (and width2 (not condp2)))
        (mv width2 nil)))
    (mv (or width width2) t)))

(defun width-find-rule-bind-free (width-fn w x mfc state)
  (declare (ignore mfc)
           (xargs :mode :program
                  :stobjs state))
  (b* (((unless (quotep w)) nil)
       ((mv width &) (look-for-width-rule
                      (fgetprop width-fn 'acl2::lemmas nil (w state))
                      (unquote w) x)))
    (and width
         `((w2 . ,width)))))
    

(defthmd unsigned-byte-p-by-find-rule
  (implies (and (bind-free (width-find-rule-bind-free 'unsigned-byte-p w x mfc state) (w2))
                (natp w2)
                (natp w)
                (< w2 w)
                (unsigned-byte-p w2 x))
           (unsigned-byte-p w x)))

(defthmd signed-byte-p-by-find-rule
  (implies (and (bind-free (width-find-rule-bind-free 'signed-byte-p w x mfc state) (w2))
                (natp w2)
                (natp w)
                (< w2 w)
                (signed-byte-p w2 x))
           (signed-byte-p w x)))

;; test
(local
 (progn

   (define foo (x)
     :returns foo
     (if (unsigned-byte-p 10 x) x 10)
     ///
     (defret unsigned-byte-p-10-of-foo
       (unsigned-byte-p 10 foo)))

   (defthm unsigned-byte-p-50-of-foo
     (unsigned-byte-p 50 (foo x))
     :hints(("Goal" :in-theory (enable unsigned-byte-p-by-find-rule))))

   (define bar (x)
     :returns bar
     (if (signed-byte-p 10 x) x 10)
     ///
     (defret signed-byte-p-10-of-bar
       (signed-byte-p 10 bar)))

   (defthm signed-byte-p-50-of-bar
     (signed-byte-p 50 (bar x))
     :hints(("Goal" :in-theory (enable signed-byte-p-by-find-rule))))))
