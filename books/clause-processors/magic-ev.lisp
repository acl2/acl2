; Term evaluator based on magic-ev-fncall

; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(mutual-recursion
 (defun magic-ev (x alist state hard-errp aokp)
   (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-alistp alist))
                   :verify-guards nil
                   :stobjs state))
   (cond ((not x) (mv nil nil))
         ((atom x)
          (mv nil (cdr (assoc-eq x alist))))
         ((eq (car x) 'quote) (mv nil (cadr x)))
         ((consp (car x))
          (b* (((mv err args)
                (magic-ev-lst (cdr x) alist state hard-errp aokp))
               ((when err)
                (mv err args))
               (new-alist (pairlis$ (cadar x) args)))
            (magic-ev (caddar x) new-alist state hard-errp aokp)))
         ((eq (car x) 'if)
          (b* (((mv err test)
                (magic-ev (cadr x) alist state hard-errp aokp))
               ((when err) (mv err test)))
            (if test
                (if (equal (cadr x) (caddr x))
                    ;; OR -- don't re-evaluate the same term
                    (mv nil test)
                  (magic-ev (caddr x) alist state hard-errp aokp))
              (magic-ev (cadddr x) alist state hard-errp aokp))))
         (t (b* (((mv err args)
                  (magic-ev-lst (cdr x) alist state hard-errp aokp))
                 ((when err)
                  (mv err args)))
              (magic-ev-fncall (car x) args state hard-errp aokp)))))

 (defun magic-ev-lst (x alist state hard-errp aokp)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-alistp alist))
                   :stobjs state))
   (if (endp x)
       (mv nil nil)
     (b* (((mv err first) (magic-ev (car x) alist state hard-errp aokp))
          ((when err) (mv err first))
          ((mv err rest) (magic-ev-lst (cdr x) alist state hard-errp aokp))
          ((when err) (mv err rest)))
       (mv nil (cons first rest))))))

(defthm len-of-magic-ev-lst
  (b* (((mv err val)
        (magic-ev-lst x alist state hard-errp aokp)))
    (implies (not err)
             (equal (len val) (len x)))))

(defthm true-listp-magic-ev-lst
  (b* (((mv err val)
        (magic-ev-lst x alist state hard-errp aokp)))
    (implies (not err)
             (true-listp val)))
  :hints (("goal" :induct (len x)
           :expand ((magic-ev-lst x alist state hard-errp aokp)))))

(defthm symbol-alistp-pairlis
  (implies (symbol-listp keys)
           (symbol-alistp (pairlis$ keys vals))))

(verify-guards magic-ev
  :hints ((and stable-under-simplificationp
               '(:expand ((pseudo-termp x))))))


