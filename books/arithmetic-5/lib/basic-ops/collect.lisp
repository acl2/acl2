; Arithmetic-5 Library
; Copyright (C) 2009 Robert Krug <rkrug@cs.utexas.edu>
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
;;; collect.lisp
;;;
;;; This book contains the rules used to collect like terms, after
;;; things have been prepared by the bind-free rules in normalize.lisp
;;; and simplify.lisp.
;;;
;;; See common.lisp for a short description of the general strategy
;;; used.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local 
 (include-book "../../support/top"))

(local 
 (include-book "expt-helper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hack516
     (equal (EXPT X (- M))
            (/ (EXPT X M)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next two sections of rules do the actual work of combining
;;; "like" terms for the rules in normalize.lisp and simplify.lisp.

(defun collect-+ (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defthm collect-+-problem-finder
    (implies (and (cw "There is a missing rule for collect-+.  ~
                       Please report this to the maintainers of ~
                       ACL2.  The offending pattern is:~%~
                       (collect-+ ~x0 ~x1)."
		      x y)
		  (not (equal x x)))
             (equal (collect-+ x y)
                    (+ x y))))

(defthm |(+ x x)|
    (equal (collect-+ x x)
           (* 2 x)))

(defthm |(+ x (- x))|
    (equal (collect-+ x (- x))
           0))

(defthm |(+ x (* c x))|
    (implies (syntaxp (quotep c))
             (equal (collect-+ x (* c x))
                    (* (+ c 1) x))))


(defthm |(+ (- x) (* c x))|
    (implies (syntaxp (quotep c))
             (equal (collect-+ (- x) (* c x))
                    (* (- c 1) x))))

(defthm |(+ (* c x) (* d x))|
    (implies (and (syntaxp (quotep c))
                  (syntaxp (quotep d)))
             (equal (collect-+ (* c x) (* d x))
                    (* (+ c d) x))))

(defthm |(collect-+ y x)|
    (equal (collect-+ y x)
           (collect-+ x y)))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (and (active-runep '(:rewrite |(+ x x)|))
	  (active-runep '(:rewrite |(+ x (- x))|))
	  (active-runep '(:rewrite |(+ x (* c x))|))
	  (active-runep '(:rewrite |(+ (- x) (* c x))|))
	  (active-runep '(:rewrite |(+ (* c x) (* d x))|))
	  (active-runep '(:rewrite |(collect-+ y x)|)))
   t)
 :error nil)

(in-theory (disable collect-+))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (not (active-runep '(:definition collect-+)))
   t)
 :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pow-2 (x to-bind)
  (let ((pow (power-of-2-generalized x)))
    (if pow
	`((,to-bind . ',pow))
      nil)))

(defun collect-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defthm collect-*-problem-finder
    (implies (and (cw "There is a missing rule for collect-*.  ~
                       Please report this to the maintainers of ~
                       ACL2.  The offending pattern is:~%~
                       (collect-* ~x0 ~x1)."
		      x y)
		  (not (equal x x)))
             (equal (collect-* x y)
                    (* x y))))

(defthm |(* x x)|
    (equal (collect-* x x)
           (expt x 2)))

(defthm |(* x (/ x))|
    (equal (collect-* x (/ x))
           (if (equal (if (acl2-numberp x) x 0) 0)
               0
             1)))

(defthm |(* x (expt x n))|
    (implies (integerp n)
             (equal (collect-* x (expt x n))
                    (if (equal (if (acl2-numberp x) x 0) 0)
                        0
                      (expt x (+ n 1))))))

(defthm |(* c (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* c (expt d n))
                    (if (equal (fix c) 0)
                        0
                      (expt 2 (+ c-pow (* d-pow n)))))))

(defthm |(* (- c) (expt c n))|
    (implies (and (syntaxp (numeric-constant-p c))
		  (integerp n))
             (equal (collect-* (- c) (expt c n))
                    (if (equal (fix c) 0)
                        0
                      (- (expt c (+ n 1)))))))

(defthm |(* (- c) (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (- c) (expt d n))
                    (if (equal (fix c) 0)
                        0
                      (- (expt 2 (+ c-pow (* d-pow n))))))))

(defthm |(* (/ x) (expt x n))|
    (implies (integerp n)
             (equal (collect-* (/ x) (expt x n))
                    (if (equal (if (acl2-numberp x) x 0) 0)
                        0
                      (expt x (- n 1))))))

(defthm |(* (/ c) (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (/ c) (expt d n))
                    (if (equal (fix c) 0)
                        0
                      (expt 2 (+ (- c-pow) (* d-pow n)))))))

(defthm |(* (- (/ c)) (expt c n))|
    (implies (and (syntaxp (numeric-constant-p c))
		  (integerp n))
             (equal (collect-* (- (/ c)) (expt c n))
                    (if (equal (fix c) 0)
                        0
                      (- (expt c (- n 1)))))))

(defthm |(* (- (/ c)) (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (- (/ c)) (expt d n))
                    (if (equal (fix c) 0)
                        0
                      (- (expt 2 (+ (- c-pow) (* d-pow n))))))))

(defthm |(* x (/ (expt x n)))|
    (implies (integerp n)
             (equal (collect-* x (/ (expt x n)))
                    (if (equal (if (acl2-numberp x) x 0) 0)
                        0
                      (/ (expt x (- n 1)))))))

(defthm |(* c (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* c (/ (expt d n)))
                    (if (equal (fix c) 0)
                        0
                      (/ (expt 2 (+ (- c-pow) (* d-pow n))))))))

(defthm |(* (- c) (/ (expt c n)))|
    (implies (and (syntaxp (numeric-constant-p c))
		  (integerp n))
             (equal (collect-* (- c) (/ (expt c n)))
                    (if (equal (fix c) 0)
                        0
                      (- (/ (expt c (- n 1))))))))

(defthm |(* (- c) (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (- c) (/ (expt d n)))
                    (if (equal (fix c) 0)
                        0
                      (- (/ (expt 2 (+ (- c-pow) (* d-pow n)))))))))

(defthm |(* (/ x) (/ (expt x n)))|
    (implies (integerp n)
             (equal (collect-* (/ x) (/ (expt x n)))
                    (if (equal (if (acl2-numberp x) x 0) 0)
                        0
                      (/ (expt x (+ n 1)))))))

(defthm |(* (/ c) (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (/ c) (/ (expt d n)))
                    (if (equal (fix c) 0)
                        0
                      (/ (expt 2 (+ c-pow (* d-pow n))))))))

(defthm |(* (- (/ c)) (/ (expt c n)))|
    (implies (and (syntaxp (numeric-constant-p c))
		  (integerp n))
             (equal (collect-* (- (/ c)) (/ (expt c n)))
                    (if (equal (fix c) 0)
                        0
                      (- (/ (expt c (+ n 1))))))))

(defthm |(* (- (/ c)) (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp n))
             (equal (collect-* (- (/ c)) (/ (expt d n)))
                    (if (equal (fix c) 0)
                        0
                      (- (/ (expt 2 (+ c-pow (* d-pow n)))))))))

(defthm |(* (expt x m) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (expt x n))
                    (if (and (equal (if (acl2-numberp x) x 0) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (+ m n))))))

(defthm |(* (expt c m) (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp m)
		  (integerp n))
             (equal (collect-* (expt c m) (expt d n))
                    (if (or (and (equal (fix c) 0)
				 (not (equal m 0)))
			    (and (equal (fix d) 0)
				 (not (equal n 0))))
                        0
                      (expt 2 (+ (* c-pow m) (* d-pow n)))))))

(defthm |(* (/ (expt x m)) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (/ (expt x m)) (expt x n))
                    (if (and (equal (if (acl2-numberp x) x 0) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- n m))))))

(defthm |(* (/ (expt c m)) (expt d n))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp m)
		  (integerp n))
             (equal (collect-* (/ (expt c m)) (expt d n))
                    (if (or (and (equal (fix c) 0)
				 (not (equal m 0)))
			    (and (equal (fix d) 0)
				 (not (equal n 0))))
                        0
                      (expt 2 (+ (* (- c-pow) m) (* d-pow n)))))))

(defthm |(* (expt x m) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (/ (expt x n)))
                    (if (and (equal (if (acl2-numberp x) x 0) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- m n))))))

(defthm |(* (expt c m) (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp m)
		  (integerp n))
             (equal (collect-* (expt c m) (/ (expt d n)))
                    (if (or (and (equal (fix c) 0)
				 (not (equal m 0)))
			    (and (equal (fix d) 0)
				 (not (equal n 0))))
                        0
                      (expt 2 (+ (* c-pow m) (* (- d-pow) n)))))))

(defthm |(* (/ (expt x m)) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (/ (expt x m)) (/ (expt x n)))
                    (if (and (equal (if (acl2-numberp x) x 0) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (/ (expt x (+ m n)))))))

(defthm |(* (/ (expt c m)) (/ (expt d n)))|
    (implies (and (syntaxp (rational-constant-p c))
		  (syntaxp (rational-constant-p d))
		  (bind-free (pow-2 c 'c-pow) (c-pow))
		  (bind-free (pow-2 d 'd-pow) (d-pow))
		  (integerp c-pow)
		  (integerp d-pow)
		  (equal c (expt 2 c-pow))
		  (equal d (expt 2 d-pow))
		  (integerp m)
		  (integerp n))
             (equal (collect-* (/ (expt c m)) (/ (expt d n)))
                    (if (or (and (equal (fix c) 0)
				 (not (equal m 0)))
			    (and (equal (fix d) 0)
				 (not (equal n 0))))
                        0
                      (/ (expt 2 (+ (* c-pow m) (* d-pow n))))))))

(defthm |(* (expt x n) (expt y n))|
    (implies (integerp n)
             (equal (collect-* (expt x n) (expt y n))
                    (expt (* x y) n))))

(defthm |(collect-* y x)|
    (equal (collect-* y x)
           (collect-* x y)))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (and (active-runep '(:rewrite |(* x x)|))
	  (active-runep '(:rewrite |(* x (/ x))|))
	  (active-runep '(:rewrite |(* x (expt x n))|))
	  (active-runep '(:rewrite |(* c (expt d n))|))
	  (active-runep '(:rewrite |(* (- c) (expt c n))|))
	  (active-runep '(:rewrite |(* (- c) (expt d n))|))
	  (active-runep '(:rewrite |(* (/ x) (expt x n))|))
	  (active-runep '(:rewrite |(* (/ c) (expt d n))|))
	  (active-runep '(:rewrite |(* (- (/ c)) (expt c n))|))
	  (active-runep '(:rewrite |(* (- (/ c)) (expt d n))|))
	  (active-runep '(:rewrite |(* x (/ (expt x n)))|))
	  (active-runep '(:rewrite |(* c (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (- c) (/ (expt c n)))|))
	  (active-runep '(:rewrite |(* (- c) (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (/ x) (/ (expt x n)))|))
	  (active-runep '(:rewrite |(* (/ c) (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (- (/ c)) (/ (expt c n)))|))
	  (active-runep '(:rewrite |(* (- (/ c)) (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (expt x m) (expt x n))|))
	  (active-runep '(:rewrite |(* (expt c m) (expt d n))|))
	  (active-runep '(:rewrite |(* (/ (expt x m)) (expt x n))|))
	  (active-runep '(:rewrite |(* (/ (expt c m)) (expt d n))|))
	  (active-runep '(:rewrite |(* (expt x m) (/ (expt x n)))|))
	  (active-runep '(:rewrite |(* (expt c m) (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (/ (expt x m)) (/ (expt x n)))|))
	  (active-runep '(:rewrite |(* (/ (expt c m)) (/ (expt d n)))|))
	  (active-runep '(:rewrite |(* (expt x n) (expt y n))|))
	  (active-runep '(:rewrite |(collect-* y x)|)))
   t)
 :error nil)

(in-theory (disable collect-*))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (not (active-runep '(:definition collect-*)))
   t)
 :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This set of commutative rules puts terms into a proper form
;;; for the above two sets of rules to fire.  They are needed by
;;; the rules in normalize.

(local
 (in-theory (enable collect-+ collect-*)))

(defun bubble-down (x match)
  (declare (xargs :guard t))
  (declare (ignore match))
  x)

(defthm bubble-down-+-problem-finder
    (implies (equal x x)
             (equal (+ (bubble-down x match) y)
                    (+ x y))))

(in-theory (disable bubble-down-+-problem-finder))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (not (active-runep '(:rewrite bubble-down-+-problem-finder)))
   t)
 :error nil)

(defthm bubble-down-+-bubble-down
    (equal (+ (bubble-down x match) y z)
           (+ y (bubble-down x match) z)))

(defthm bubble-down-+-match-1
    (implies (syntaxp (equal match y))
             (equal (+ (bubble-down x match) y)
                    (collect-+ x y))))

(defthm bubble-down-+-match-2
    (implies (syntaxp (equal match y))
             (equal (+ y (bubble-down x match))
                    (collect-+ x y))))

(defthm bubble-down-+-match-3
    (implies (syntaxp (equal match y))
             (equal (+ (bubble-down x match) y z)
                    (+ (collect-+ x y) z))))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (and (active-runep '(:rewrite bubble-down-+-bubble-down))
	  (active-runep '(:rewrite bubble-down-+-match-1))
	  (active-runep '(:rewrite bubble-down-+-match-2))
	  (active-runep '(:rewrite bubble-down-+-match-3)))
   t)
 :error nil)

(defthm bubble-down-*-problem-finder
    (implies (equal x x)
             (equal (* (bubble-down x match) y)
                    (* x y))))

(in-theory (disable bubble-down-*-problem-finder))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (not (active-runep '(:rewrite bubble-down-*-problem-finder)))
   t)
 :error nil)

(defthm bubble-down-*-bubble-down
    (equal (* (bubble-down x match) y z)
           (* y (bubble-down x match) z)))

(defthm bubble-down-*-match-1
    (implies (syntaxp (equal match y))
             (equal (* (bubble-down x match) y)
                    (collect-* x y))))

(defthm bubble-down-*-match-2
    (implies (syntaxp (equal match y))
             (equal (* y (bubble-down x match))
                    (collect-* x y))))

(defthm bubble-down-*-match-3
    (implies (syntaxp (equal match y))
             (equal (* (bubble-down x match) y z)
                    (* (collect-* x y) z))))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (and (active-runep '(:rewrite bubble-down-*-bubble-down))
	  (active-runep '(:rewrite bubble-down-*-match-1))
	  (active-runep '(:rewrite bubble-down-*-match-2))
	  (active-runep '(:rewrite bubble-down-*-match-3)))
   t)
 :error nil)

(in-theory (disable bubble-down (:executable-counterpart bubble-down)))

(theory-invariant 
 (if (active-runep '(:definition boil-that-dustspeck))
     (and (not (active-runep '(:rewrite bubble-down)))
	  (not (active-runep '(:executable-counterpart bubble-down))))
   t)
 :error nil)
