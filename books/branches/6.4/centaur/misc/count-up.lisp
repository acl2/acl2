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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Provides a measure and efficient termination check
;; for functions that recur by counting up to a limit.

(defmacro count-up-meas (x max)
  `(nfix (- (nfix ,max) (nfix ,x))))

(defmacro count-up-guard (x max)
  `(let ((x ,x) (max ,max))
     (and (natp x) (natp max) (<= x max))))

(defmacro count-up-done (x max)
  `(mbe :logic (zp (- (nfix ,max) (nfix ,x)))
        :exec (= ,x ,max)))

(defmacro count-past-guard (x max)
  `(and (natp ,x) (natp ,max)))

(defmacro count-past-done (x max)
  `(mbe :logic (zp (- (nfix ,max) (nfix ,x)))
        :exec (>= ,x ,max)))

(defmacro lnfix (x)
  `(mbe :logic (nfix ,x) :exec ,x))

(defmacro nincr (x)
  `(1+ (lnfix ,x)))

;; examples:
(local
 (defun collect-range (min max)
   (declare (xargs :guard (count-up-guard min max)
                   :measure (count-up-meas min max)))
   (if (count-up-done min max)
       (list max)
     (cons (lnfix min)
           (collect-range (nincr min) max)))))

(local
 (defun collect-range-by (min incr max)
   (declare (Xargs :guard (and (count-past-guard min max)
                               (posp incr))
                   :measure (count-up-meas min max)))
   (if (count-past-done min max)
       nil
     (cons (lnfix min)
           (collect-range-by
            (+ (lnfix min)
               ;; (lpfix incr)
               (mbe :logic (if (and (integerp incr)
                                    (< 0 incr))
                               incr
                             1)
                    :exec incr))
            incr max)))))
