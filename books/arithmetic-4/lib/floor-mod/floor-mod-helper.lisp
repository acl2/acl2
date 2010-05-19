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
;;; floor-mod-helper.lisp
;;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "forcing-types"))

(local
 (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT++ ID STABLE-UNDER-SIMPLIFICATIONP
						 HIST NIL))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (local
  (defthm floor-sum-cases-helper-a
    (implies (and (rationalp (/ x z))
		  (rationalp (/ y z)))
	     (<= (floor (+ x y) z)
		 (cond ((not (acl2-numberp z))
			0)
		       ((equal z 0)
			0)
		       ((< 0 z)
			(if (< (+ (mod x z) (mod y z)) z)
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z))))
		       (t
			(if (< z (+ (mod x z) (mod y z)))
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z)))))))
    :hints (("Goal" :in-theory (enable mod)))))

 (local
  (defthm floor-sum-cases-helper-b
    (implies (and (rationalp (/ x z))
		  (rationalp (/ y z)))
	     (<= (cond ((not (acl2-numberp z))
			0)
		       ((equal z 0)
			0)
		       ((< 0 z)
			(if (< (+ (mod x z) (mod y z)) z)
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z))))
		       (t
			(if (< z (+ (mod x z) (mod y z)))
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z)))))
		 (floor (+ x y) z)))
    :hints (("Goal" :in-theory (enable mod)))))

 (local
  (in-theory (disable floor-sum-cases-helper-a
		      floor-sum-cases-helper-b)))

 (defthm |(floor (+ x y) z)|
   (implies (and (rationalp (/ x z))
		 (rationalp (/ y z)))
	    (equal (floor (+ x y) z)
		   (cond ((not (acl2-numberp z))
			  0)
			 ((equal z 0)
			  0)
			 ((< 0 z)
			  (if (< (+ (mod x z) (mod y z)) z)
			      (+ (floor x z) (floor y z))
			    (+ 1 (floor x z) (floor y z))))
			 (t
			  (if (< z (+ (mod x z) (mod y z)))
			      (+ (floor x z) (floor y z))
			    (+ 1 (floor x z) (floor y z)))))))
   :hints (("Goal" :use ((:instance floor-sum-cases-helper-a)
			 (:instance floor-sum-cases-helper-b)))))

 )

(defthm |(mod (+ x y) z)|
  (implies (and (rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (mod (+ x y) z)
		  (if (<= 0 z)
		      (if (< (+ (mod x z) (mod y z)) z)
			  (+ (mod x z) (mod y z))
			(+ (mod x z) (mod y z) (- z)))
		    (if (< z (+ (mod x z) (mod y z)))
			(+ (mod x z) (mod y z))
		      (+ (mod x z) (mod y z) (- z))))))
  :hints (("Goal" :in-theory (enable mod))))








(encapsulate
 ()

 (local
  (defthm crock-xxx33-helper
    (implies (and (acl2-numberp md0)
		  (acl2-numberp j)
		  (acl2-numberp z)
		  (not (equal z 0))
		  (equal 0 (+ md0 (* j z))))
	     (equal (* md0 (/ z)) (- j)))
    :rule-classes nil))

 (local
  (defthm crock-xxx33a
    (implies (and (acl2-numberp md0)
		  (integerp j)
		  (acl2-numberp z)
		  (not (equal z 0))
		  (equal 0 (+ md0 (* j z))))
	     (integerp (* md0 (/ z))))
    :hints (("Goal" :use crock-xxx33-helper))))
 
 (defthm rewrite-floor-mod
   (implies (and ;(acl2-numberp x)
		 ;(acl2-numberp y)
		 (rationalp (/ x y))
		 (rationalp (/ x z))
		 (rationalp (/ (mod x y) z))
		 (equal i (/ y z))
		 (integerp i))
	    (equal (floor (mod x y) z)
		   (- (floor x z) (* i (floor x y))))))

 (defthm rewrite-mod-mod
   (implies (and (acl2-numberp z)
		 (rationalp (/ x y))
		 (rationalp (/ x z))
		 (not (equal z 0))
		 (equal i (/ y z))
		 (integerp i))
	    (equal (mod (mod x y) z)
		   (mod x z)))
   :hints (("Subgoal 1" :in-theory (enable mod)))
   :otf-flg t)
 )
