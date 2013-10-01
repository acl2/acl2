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


;; Defines a function that swaps the contents of two (congruent) stobjs.
;; Logically, just return one and the other.

;; Defines a function called swap-stobj1.  Stobj2 should be another stobj
;; declared congruent to stobj1.
(defmacro def-stobj-swap (stobj1 stobj2)
  (let* ((swap-nx (intern-in-package-of-symbol
                   (concatenate 'string "SWAP-" (symbol-name stobj1) "S-NX")
                   stobj1))
         (swap    (intern-in-package-of-symbol
                   (concatenate 'string "SWAP-" (symbol-name stobj1) "S")
                   stobj1)))
  `(progn
     (make-event
      (if (eq (congruent-stobj-rep ',stobj1 (w state))
              (congruent-stobj-rep ',stobj2 (w state)))
          '(value-triple :invisible)
        (er hard? 'def-stobj-swap
            "The two stobjs must be declared congruent to define a swapping function.~%")))
     (defun-nx ,swap-nx (,stobj1 ,stobj2)
       (declare (Xargs :stobjs (,stobj1 ,stobj2)))
       (mv ,stobj2 ,stobj1))
     (defun ,swap (,stobj1 ,stobj2)
       (declare (xargs :stobjs (,stobj1 ,stobj2)))
       (mv-let (,stobj1 ,stobj2)
         (,swap-nx ,stobj1 ,stobj2)
         (mv ,stobj1 ,stobj2)))
     (defttag ,swap)
     (progn!
      (set-raw-mode t)
      (defun ,swap (,stobj1 ,stobj2)
        (let* ((bound (1- (length ,stobj1))))
          (loop for i from 0 to bound do
                (psetf (svref i ,stobj1) (svref i ,stobj2)
                       (svref i ,stobj2) (svref i ,stobj1)))
          (mv ,stobj1 ,stobj2)))))))


