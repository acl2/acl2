; Copyright (C) 2012 Centaur Technology
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

;; A set of utility functions for finding or collecting certain subterms of a
;; term/clause.

;; Basic: find one occurrence of a call of a particular function.  Don't look
;; in lambda bodies.
(mutual-recursion
 (defun find-call (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((eq fn (car x)) x)
         (t (find-call-lst fn (cdr x)))))
 (defun find-call-lst (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (or (find-call fn (car x))
         (find-call-lst fn (cdr x))))))

;; Find all occurrences of a call of a particular function.
(mutual-recursion
 (defun find-calls (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((eq fn (car x))
          (cons x
                (find-calls-lst fn (cdr x))))
         (t (find-calls-lst fn (cdr x)))))
 (defun find-calls-lst (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (append (find-calls fn (car x))
             (find-calls-lst fn (cdr x))))))


;; Find all calls of several functions
(mutual-recursion
 (defun find-calls-of-fns (fns x)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((member (car x) fns)
          (cons x
                (find-calls-of-fns-lst fns (cdr x))))
         (t (find-calls-of-fns-lst fns (cdr x)))))
 (defun find-calls-of-fns-lst (fns x)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (append (find-calls-of-fns fns (car x))
             (find-calls-of-fns-lst fns (cdr x))))))
