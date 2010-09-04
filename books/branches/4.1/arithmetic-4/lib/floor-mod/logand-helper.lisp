; Arithmetic-4 Library
; Copyright (C) 2008 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; logand-helper.lisp
;;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "more-floor-mod"))

(local
 (include-book "floor-mod"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "truncate-rem"))

(local
 (set-default-hints '((nonlinearp-default-hint
		       stable-under-simplificationp hist pspv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (encapsulate
  ((op (x y) t))

  (local
   (defun op (x y)
     (+ x y)))

  (defthm op-comm
    (equal (op y x)
	   (op x y)))

  (defthm op-assoc
    (equal (op (op x y) z)
	   (op x (op y z))))
  ))

(local
 (defthm op-comm-2
   (equal (op y (op x z))
	  (op x (op y z)))
   :hints (("Goal" :in-theory (disable op-comm
				       op-assoc)
	    :use ((:instance op-assoc
			     (x y)
			     (y x)
			     (z z))
		  (:instance op-comm)
		  (:instance op-assoc))))))

(defthm |(equal (logand x y) -1)|
  (equal (equal (logand x y) -1)
	 (and (equal x -1)
	      (equal y -1))))

(local
 (defthm logand-=-0-crock-a
   (implies (equal (logand y z) 0)
	    (equal (logand (logand x y) z) 0))))

(defthm logand-assoc
  (equal (logand (logand x y) z)
	 (logand x (logand y z)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm logand-y-x
  (equal (logand y x)
	 (logand x y)))

(defthm logand-y-x-z
  (equal (logand y x z)
	 (logand x y z))
  :hints (("Goal" :use (:functional-instance
			op-comm-2
			(op binary-logand)))))


