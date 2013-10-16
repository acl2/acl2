; Centaur Miscellaneous Books
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; tuplep.lisp
;  - tuplep: recognizer for n-tuples
;  - tuple-listp: recognizer for n-tuple lists

(in-package "ACL2")

(defun tuplep (n x)
  ;; Note: we leave this enabled and allow it to expand.
  (declare (xargs :guard t))
  (and (true-listp x)
       (eql (mbe :logic (len x)
                 :exec (length x))
            n)))

(defund tuple-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (tuplep n (car x))
         (tuple-listp n (cdr x)))))

(defthm tuple-listp-when-atom
  (implies (atom x)
           (equal (tuple-listp n x)
                  (not x)))
  :hints(("Goal" :in-theory (enable tuple-listp))))

(defthm tuple-listp-of-cons
  (equal (tuple-listp n (cons a x))
         (and (tuplep n a)
              (tuple-listp n x)))
  :hints(("Goal" :in-theory (enable tuple-listp))))

(defthm tuple-listp-of-append
  (implies (and (tuple-listp n x)
                (tuple-listp n y))
           (tuple-listp n (append x y)))
  :hints(("Goal" :induct (len x))))
