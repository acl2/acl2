; Centaur Miscellaneous Books
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; REMOVE-ASSOC-EQUAL is like DELETE-ASSOC-EQUAL, but removes all occurrences of
; the key from the alist instead of just removing the first occurrence.

; Modifications below to remove-assoc-xxx are from Matt K., 5/19/2014, to
; support changes in let-mbe that provide better guard-checking.

(defun-with-guard-check remove-assoc-eq-exec (x alist)
  (if (symbolp x)
      (alistp alist)
    (symbol-alistp alist))
  (cond ((endp alist) nil)
        ((eq x (car (car alist))) (remove-assoc-eq-exec x (cdr alist)))
        (t (cons (car alist)
                 (remove-assoc-eq-exec x (cdr alist))))))

(defun-with-guard-check remove-assoc-eql-exec (x alist)
  (if (eqlablep x)
      (alistp alist)
    (eqlable-alistp alist))
  (cond ((endp alist) nil)
        ((eql x (car (car alist))) (remove-assoc-eql-exec x (cdr alist)))
        (t (cons (car alist) (remove-assoc-eql-exec x (cdr alist))))))

(defun remove-assoc-equal (x alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((equal x (car (car alist))) (remove-assoc-equal x (cdr alist)))
        (t (cons (car alist) (remove-assoc-equal x (cdr alist))))))

(defmacro remove-assoc-eq (x lst)
  `(remove-assoc ,x ,lst :test 'eq))

(defthm remove-assoc-eq-exec-is-remove-assoc-equal
  (equal (remove-assoc-eq-exec x l)
         (remove-assoc-equal x l)))

(defthm remove-assoc-eql-exec-is-remove-assoc-equal
  (equal (remove-assoc-eql-exec x l)
         (remove-assoc-equal x l)))

(defmacro remove-assoc (x alist &key (test ''eql))
  (declare (xargs :guard (or (equal test ''eq)
                             (equal test ''eql)
                             (equal test ''equal))))
  (cond
   ((equal test ''eq)
    `(let-mbe ((x ,x) (alist ,alist))
              :logic (remove-assoc-equal x alist)
              :exec  (remove-assoc-eq-exec x alist)))
   ((equal test ''eql)
    `(let-mbe ((x ,x) (alist ,alist))
              :logic (remove-assoc-equal x alist)
              :exec  (remove-assoc-eql-exec x alist)))
   (t ; (equal test 'equal)
    `(remove-assoc-equal ,x ,alist))))

(defthm assoc-of-remove-assoc-split
  (equal (assoc j (remove-assoc k a))
         (if (equal j k)
             nil
           (assoc j a))))

