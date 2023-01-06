; Standard System Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Matt Kaufmann (matthew.j.kaufmann@gmail.com)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-theorem-no-simplify")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun foo (x)
   (if (consp x) (foo (cddr x)) x))
 (assert-equal (guard-theorem-no-simplify 'foo nil (w state) t t)
               '(if (not (consp x))
                    't
                  (if (consp (cdr x))
                      't
                    (equal (cdr x) 'nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun foo (x)
   (if (consp x) (foo (cddr x)) x))
 (assert-event
  (mv-let (erp val)
      (magic-ev-fncall 'guard-theorem-no-simplify
                       (list 'foo nil (w state) t t)
                       state t t)
    (and (null erp)
         (equal val
                '(if (not (consp x))
                     't
                   (if (consp (cdr x))
                       't
                     (equal (cdr x) 'nil))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (guard-theorem-no-simplify 'len nil (w state) t t)
              '(if (not (consp x))
                   't
                 (acl2-numberp (len (cdr x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (guard-theorem-no-simplify 'binary-+ nil (w state) t t)
              ''t)
