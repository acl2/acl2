; Term evaluator based on magic-ev-fncall

; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "tools/bstar" :dir :system)

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
                (mv err nil))
               (new-alist (pairlis$ (cadar x) args)))
            (magic-ev (caddar x) new-alist state hard-errp aokp)))
         ((eq (car x) 'if)
          (b* (((mv err test)
                (magic-ev (cadr x) alist state hard-errp aokp))
               ((when err) (mv err nil)))
            (if test
                (magic-ev (caddr x) alist state hard-errp aokp)
              (magic-ev (cadddr x) alist state hard-errp aokp))))
         (t (b* (((mv err args)
                  (magic-ev-lst (cdr x) alist state hard-errp aokp))
                 ((when err)
                  (mv err nil)))
              (magic-ev-fncall (car x) args state hard-errp aokp)))))

 (defun magic-ev-lst (x alist state hard-errp aokp)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-alistp alist))
                   :stobjs state))
   (if (endp x)
       (mv nil nil)
     (b* (((mv err first) (magic-ev (car x) alist state hard-errp aokp))
          ((when err) (mv err nil))
          ((mv err rest) (magic-ev-lst (cdr x) alist state hard-errp aokp))
          ((when err) (mv err nil)))
       (mv nil (cons first rest))))))

(defthm len-of-magic-ev-lst
  (b* (((mv err val)
        (magic-ev-lst x alist state hard-errp aokp)))
    (implies (not err)
             (equal (len val) (len x)))))

(defthm true-listp-magic-ev-lst
  (true-listp (mv-nth 1 (magic-ev-lst x alist state hard-errp aokp)))
  :hints (("goal" :induct (len x))))

(defthm symbol-alistp-pairlis
  (implies (symbol-listp keys)
           (symbol-alistp (pairlis$ keys vals))))

(verify-guards magic-ev
  :hints ((and stable-under-simplificationp
               '(:expand ((pseudo-termp x))))))


