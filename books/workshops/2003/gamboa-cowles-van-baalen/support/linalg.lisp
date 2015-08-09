; The ACL2 Linear Algebra Book.
; Copyright (C) 2002 Ruben Gamboa and John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; Ruben Gamboa and John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Summer and Fall 2002.
;  Last modified 16 June 2003.
#|
 To certify in
      ACL2 Version 2.8 alpha (as of May 11 03)

(certify-book "linalg"
	      0
	      nil ;;compile-flg
	      )
|#
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Date: Mon, 23 Sep 2002 12:22:26 -0600
From: Ruben Gamboa <ruben@cs.uwyo.edu>
To: cowles@cs.uwyo.edu
Subject: linear algebra
|#
#|
~ruben/home/projects/kalman/linalg.lisp
|#
#|
  (ld ;; Newline to fool dependency scanner
   "defpkg.lsp")
  (certify-book "linalg" 1)
|#
#|
(in-package "KALMAN")
|#;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
At UW:

:set-cbd "/home/faculty/cowles/acl2/matrix/" ;;pyramid

:set-cbd "/home/cowles/matrix/" ;; turing
|#

(in-package "ACL2")

#|
(include-book  ;;turing
 "/home/cowles/acl2-sources/books/arithmetic-2.8/top")

(include-book  ;;pyramid
 "/home/acl2/acl2-2.8/v2-8-alpha-05-11-03/books/arithmetic/top")
|#

(include-book "../../../../arithmetic/top")

(include-book "../../cowles-gamboa-van-baalen_matrix/support/matalg")

(ADD-BINOP M-+ M-BINARY-+)
(ADD-MACRO-ALIAS M-- M-UNARY--)
(ADD-BINOP M-* M-BINARY-*)

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (encapsulate
;;  ((m-matrixp (m n x) t) ;; (matrixp (m n x) t)
;;   (l (x) t)             ;; (r (x) t)
;;   (c (x) t)
;;   (m-* (x y) t)
;;   (s-* (k x) t)
;;   (m-+ (x y) t)
;;   (m-- (x y) t)         ;; macro for both matrix
;;   (m-unary-- (x) t)     ;;  unary and binary minus
;;   (m-trans (x) t)
;;   (m-zero (m n) t)      ;; (m-0 (m n) t)
;;   (m-id (n) t)          ;; (m-1 (n) t)
;;   (m-singular (x) t)    ;; (m-singularp (x) t)
;;   (m-inv (x) t))        ;; (m-/ (x) t)
;;                         ;; (m-= (M N) t)

;;  (local (defun m-matrixp (m n x)
;; 	  (and (consp x)
;; 	       (equal (car x) m)
;; 	       (equal (cadr x) n)
;; 	       (acl2-numberp (caddr x))
;; 	       (equal (cdddr x) nil))))
;;  (local (defun l (x) (car x)))
;;  (local (defun c (x) (cadr x)))
;;  (local (defun m-* (x y) (list (car x) (cadr y) (* (caddr x) (caddr y)))))
;;  (local (defun s-* (x y) (list (car y) (cadr y) (* x (caddr y)))))
;;  (local (defun m-+ (x y) (list (car x) (cadr x) (+ (caddr x) (caddr y)))))
;;  (local (defun m-- (x y) (list (car x) (cadr x) (- (caddr x) (caddr y)))))
;;  (local (defun m-unary-- (x) (list (car x) (cadr x) (- (caddr x)))))
;;  (local (defun m-trans (x) (list (cadr x) (car x) (fix (caddr x)))))
;;  (local (defun m-zero (l c) (list l c 0)))
;;  (local (defun m-id (l) (list l l 1)))
;;  (local (defun m-singular (x) (or (not (equal (car x) (cadr x)))
;; 				  (equal (caddr x) 0))))
;;  (local (defun m-inv (x) (list (car x) (cadr x) (/ (caddr x)))))
|#
#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-p-numrows-cols
;;    (implies (m-matrixp m n p)
;; 	    (and (equal (l p) m)
;; 		 (equal (c p) n))))
|#

(defthm matrix-p-numrows-cols
  (implies (matrixp m n p)
	   (and (equal (r p) m)
		(equal (c p) n)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-zero
;;    (m-matrixp m n (m-zero m n)))
|#

(defabbrev
  m-dim-p (n)
  "Determine if n is a legal matrix dimension."
  (and (integerp n)
       (> n 0)
       (<= n *INT-SQRT-MAXIMUM-POSITIVE-32-BIT-INTEGER*)))

(defthm matrix-zero
  (implies (and (m-dim-p m)
		(m-dim-p n))
	   (matrixp m n (m-0 m n))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-id
;;    (m-matrixp n n (m-id n)))
|#

(defthm matrix-id
  (implies (m-dim-p n)
	   (matrixp n n (m-1 n))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-trans
;;    (implies (and (equal (l p) m)
;; 		 (equal (c p) n))
;; 	    (m-matrixp n m (m-trans p))))
|#

(defthm matrix-trans
  (implies (matrixp m n P)
	   (matrixp n m (m-trans P))))

(in-theory (disable MATRIXP-M-TRANS))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-inv
;;    (implies (and (equal (l p) n)
;; 		 (equal (c p) n)
;; 		 (not (m-singular p)))
;; 	    (m-matrixp n n (m-inv p))))
|#

(defthm matrix-inv
  (implies (and (matrixp (r P)(c P) P)
		(equal (r P) n)
		(equal (c P) n))
	   (matrixp n n (m-/ P)))
  :hints (("Goal"
	   :use (:instance
		  matrixp-m-/
		  (M P)))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-*
;;    (implies (and (equal (l p) m)
;; 		 (equal (c p) (l q))
;; 		 (equal (c q) n))
;; 	    (m-matrixp m n (m-* p q))))
|#

(defthm matrix-*
  (implies (and (matrixp m (c P) P)
		(matrixp (r Q) n Q)
		(equal (c P)(r Q)))
	   (matrixp m n (m-* P Q))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-s*
;;    (implies (and (equal (l p) m)
;; 		 (equal (c p) n))
;; 	    (m-matrixp m n (s-* k p))))
|#

(defthm matrix-s*
   (implies (matrixp m n P)
	    (matrixp m n (s-* k p))))

(in-theory (disable MATRIXP-S-*))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q))
;; 		 (equal (l p) m)
;; 		 (equal (c p) n))
;; 	    (m-matrixp m n (m-+ p q))))
|#

(defthm matrix-+
   (implies (and (matrixp m n P)
		 (matrixp m n Q))
	    (matrixp m n (m-+ P Q))))

(in-theory (disable MATRIXP-M-+))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix--
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q))
;; 		 (equal (l p) m)
;; 		 (equal (c p) n))
;; 	    (m-matrixp m n (m-- p q))))
|#

(defthm matrix--
   (implies (and (matrixp m n P)
		 (matrixp m n Q))
	    (matrixp m n (m-- P Q))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm matrix-unary--
;;    (implies (and (equal (l p) m)
;; 		 (equal (c p) n))
;; 	    (m-matrixp m n (m-unary-- p))))
|#

(defthm matrix-unary--
  (implies (matrixp m n P)
	   (matrixp m n (m-- P))))

(in-theory (disable MATRIXP-M-UNARY--))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-zero
;;    (equal (l (m-zero m n)) m))
|#

(defthm numrows-zero
   (equal (r (m-0 m n)) m))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-zero
;;    (equal (c (m-zero m n)) n))
|#

(defthm numcols-zero
  (equal (c (m-0 m n)) n))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm zero-*-x
;;    (implies (equal (l p) n)
;; 	    (equal (m-* (m-zero m n) p)
;; 		   (m-zero m (c p)))))
|#

(defthm zero-*-x
  (implies (and (matrixp (r P)(c P) P)
		(integerp m)
		(> m 0)
		(equal (r P) n))
	   (m-= (m-* (m-0 m n) P)
		(m-0 m (c P))))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-*-zero
;;    (implies (equal (c p) m)
;; 	    (equal (m-* p (m-zero m n))
;; 		   (m-zero (l p) n))))
|#

(defthm x-*-zero
  (implies (and (matrixp (r P)(c P) P)
		(integerp n)
		(> n 0)
		(equal (c P) m))
	    (m-= (m-* P (m-0 m n))
		 (m-0 (r P) n)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm unary---zero
;;    (equal (m-unary-- (m-zero m n))
;; 	  (m-zero m n)))
|#

(defthm unary---zero
  (implies (and (integerp m)
		(> m 0)
		(integerp n)
		(> n 0))
	   (m-= (m-- (m-0 m n))
		(m-0 m n))))

(in-theory (disable m--_m-0))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm zero-+-x
;;    (implies (and (equal (l p) m)
;; 		 (equal (c p) n)
;; 		 (m-matrixp m n p))
;; 	    (equal (m-+ (m-zero m n) p) p)))
|#

(defthm zero-+-x
  (implies (matrixp m n P)
	   (m-= (m-+ (m-0 m n) P) P))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-+---x
;;    (equal (m-+ p (m-unary-- p))
;; 	  (m-zero (l p) (c p))))
|#

(local (in-theory (enable matrixp)))

(defthm x-+---x
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-+ P (m-- P))
		(m-0 (r P) (c P))))
  :hints (("Goal"
	   :in-theory (disable
		       right-m-+-inverse-of-m--)
	   :use (:instance
		 right-m-+-inverse-of-m--
		 (M P)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm -x-+-x
;;    (equal (m-+ (m-unary-- p) p)
;; 	  (m-zero (l p) (c p))))
|#

(defthm -x-+-x
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-+ (m-- P) P)
		(m-0 (r P) (c P)))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm scalar-*-zero
;;    (equal (s-* k (m-zero m n))
;; 	  (m-zero m n)))
|#

(defthm scalar-*-zero
  (implies (and (integerp m)
		(> m 0)
		(integerp n)
		(> n 0))
	   (m-= (s-* k (m-0 m n))
		(m-0 m n))))

(in-theory (disable M-=-S-*-M-0))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm zero-trans
;;    (equal (m-trans (m-zero m n))
;; 	  (m-zero n m)))
|#

(defthm zero-trans
  (implies (and (integerp m)
		(> m 0)
		(integerp n)
		(> n 0))
	   (m-= (m-trans (m-0 m n))
		(m-0 n m))))

(in-theory (disable M-=-M-TRANS-M-0))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-id
;;    (equal (l (m-id n)) n))
|#

(defthm numrows-id
  (equal (r (m-1 n)) n))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-id
;;    (equal (c (m-id n)) n))
|#

(defthm numcols-id
  (equal (c (m-1 n)) n))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm id-*-x
;;    (implies (m-matrixp n n2 p)
;; 	    (equal (m-* (m-id n) p) p)))
|#

(defthm id-*-x
  (implies (matrixp n n2 P)
	   (m-= (m-* (m-1 n) P) P))
  :hints (("Goal"
	  :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-*-id
;;    (implies (m-matrixp m n p)
;; 	    (equal (m-* p (m-id n)) p)))
|#

(defthm x-*-id
  (implies (matrixp m n P)
	   (m-= (m-* P (m-1 n)) P))
  :hints (("Goal"
	  :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm id-trans
;;    (equal (m-trans (m-id n))
;; 	  (m-id n)))
|#

(defthm id-trans
  (implies (and (integerp n)
		(> n 0))
	   (m-= (m-trans (m-1 n))
		(m-1 n))))

(in-theory (disable M-=-M-TRANS-M-1))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-*
;;    (implies (equal (c p) (l q))
;; 	    (equal (l (m-* p q))
;; 		   (l p))))
|#

(defthm numrows-*
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P) (r Q)))
	   (equal (r (m-* P Q))
		  (r P)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-*
;;    (implies (equal (c p) (l q))
;; 	    (equal (c (m-* p q))
;; 		   (c q))))
|#

(defthm numcols-*
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P) (r Q)))
	   (equal (c (m-* P Q))
		  (c Q)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm assoc-*
;;    (implies (and (equal (c p) (l q))
;; 		 (equal (c q) (l r)))
;; 	    (equal (m-* (m-* p q) r)
;; 		   (m-* p (m-* q r)))))
|#

(defthm assoc-*
  (implies (and (equal (c p) (r q))
		(equal (c q) (r r)))
	   (m-= (m-* (m-* P Q) R)
		(m-* P (m-* Q R))))
  :rule-classes ((:rewrite
		  :corollary
		  (equal (m-* (m-* P Q) R)
			 (m-* P (m-* Q R))))))

(in-theory (disable ASSOCIATIVITY-OF-M-*))

#|;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-s*
;;    (equal (l (s-* k p))
;; 	     (l p)))
|#

(defthm numrows-s*
  (equal (r (s-* k P))
	 (r P)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-s*
;;    (equal (c (s-* k p))
;; 	  (c p)))
|#

(defthm numcols-s*
  (equal (c (s-* k P))
	 (c p)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm k-*-x-*-y
;;    (implies (equal (c p) (l q))
;; 	    (equal (m-* (s-* n p) q)
;; 		   (s-* n (m-* p q)))))
|#

(local (in-theory (enable matrixp)))

(defthm k-*-x-*-y
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P) (r Q)))
	   (m-= (m-* (s-* n P) Q)
		(s-* n (m-* P Q))))
  :hints (("Goal"
	   :in-theory (disable m-*-s-*-left)
	   :use (:instance
		 m-*-s-*-left
		 (M1 P)
		 (M2 Q)
		 (a n)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-*-k-*-y
;;    (implies (equal (c p) (l q))
;; 	    (equal (m-* p (s-* n q))
;; 		   (s-* n (m-* p q)))))
|#

(local (in-theory (enable matrixp)))

(defthm x-*-k-*-y
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P) (r Q)))
	   (m-= (m-* P (s-* n Q))
		  (s-* n (m-* P Q))))
  :hints (("Goal"
	   :in-theory (disable m-*-s-*-right)
	   :use (:instance
		 m-*-s-*-right
		 (M1 P)
		 (M2 Q)
		 (a n)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (l (m-+ p q))
;; 		   (l p))))
|#

(defthm numrows-+
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (r P) (r Q))
		(equal (c P) (c Q)))
	   (equal (r (m-+ P Q))
		  (r P)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (c (m-+ p q))
;; 		   (c p))))
|#

(defthm numcols-+
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (r P) (r Q))
		(equal (c P) (c Q)))
	   (equal (c (m-+ P Q))
		  (c P)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm assoc-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (l q) (l r))
;; 		 (equal (c p) (c q))
;; 		 (equal (c q) (c r)))
;; 	    (equal (m-+ (m-+ p q) r)
;; 		   (m-+ p (m-+ q r)))))
|#

(defthm assoc-+
  (implies (and (equal (r P) (r Q))
		(equal (r Q) (r R))
		(equal (c P) (c Q))
		(equal (c Q) (c R)))
	   (m-= (m-+ (m-+ P Q) R)
		(m-+ P (m-+ Q R))))
  :rule-classes ((:rewrite
		  :corollary
		  (equal (m-+ (m-+ P Q) R)
			 (m-+ P (m-+ Q R))))))

(in-theory (disable ASSOCIATIVITY-OF-M-+))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm comm-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (m-+ p q)
;; 		   (m-+ q p))))
|#

(defthm comm-+
  (implies (and (equal (r P) (r Q))
		(equal (c P) (c Q)))
	    (m-= (m-+ P Q)
		 (m-+ Q P)))
  :rule-classes ((:rewrite
		  :corollary
		  (equal (m-+ P Q)
			 (m-+ Q P)))))

(in-theory (disable COMMUTATIVITY-OF-M-+))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-+-x
;;    (equal (m-+ p p)
;; 	  (s-* 2 p)))
|#

(local (in-theory (enable matrixp)))

(defthm x-+-x
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-+ P P)
		(s-* 2 P)))
  :hints (("Goal"
	   :in-theory (disable double-m-+-s-*)
	   :use (:instance
		 double-m-+-s-*
		 (M P)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm k-*-x-+-y
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (s-* n (m-+ p q))
;; 		   (m-+ (s-* n p)
;; 			(s-* n q)))))
|#

(defthm k-*-x-+-y
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (r P) (r Q))
		(equal (c P) (c Q)))
	   (m-= (s-* n (m-+ P Q))
		(m-+ (s-* n P)
		     (s-* n Q))))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm *-+-right
;;    (implies (and (equal (l q) (l r))
;; 		 (equal (c q) (c r))
;; 		 (equal (c p) (l q)))
;; 	    (equal (m-* p (m-+ q r))
;; 		   (m-+ (m-* p q)
;; 			(m-* p r)))))
|#

(defthm *-+-right
  (implies (and (equal (r Q) (r R))
		(equal (c Q) (c R))
		(equal (c P) (r Q)))
	   (m-= (m-* P (m-+ Q R))
		(m-+ (m-* P Q)
		     (m-* P R))))
  :rule-classes ((:rewrite
		  :corollary
		  (m-= (m-* P (m-+ Q R))
		       (m-+ (m-* P Q)
			    (m-* P R))))))

(in-theory
 (disable LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm *-+-left
;;    (implies (and (equal (l q) (l r))
;; 		 (equal (c q) (c r))
;; 		 (equal (c q) (l p)))
;; 	    (equal (m-* (m-+ q r) p)
;; 		   (m-+ (m-* q p)
;; 			(m-* r p)))))
|#

(defthm *-+-left
   (implies (and (equal (r Q) (r R))
		 (equal (c Q) (c R))
		 (equal (c Q) (r P)))
	    (m-= (m-* (m-+ Q R) P)
		 (m-+ (m-* Q P)
		      (m-* R P))))
   :rule-classes ((:rewrite
		   :corollary
		   (m-= (m-* (m-+ Q R) P)
			(m-+ (m-* Q P)
			     (m-* R P))))))

(in-theory
 (disable RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm minus-as-plus-inverse
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (m-- p q)
;; 		   (m-+ p (m-unary-- q)))))
|#

; Matt K., after v4-2:
; Commenting out the following rule, which rewrites a term to itself!
; -- Well, instead, given the comment below, I'll just make it not be a rewrite
;    rule.
(defthm minus-as-plus-inverse
  (equal (m-- P Q)
	 (m-+ P (m-unary-- Q)))
  :rule-classes nil)

;; m-- is a macro that expands into the second term of the
;;  above equality. So the equality above expands into a special
;;  case of the reflexivity of equal.
; Matt K. mod: See comment above for why I'm commenting this out.
; (in-theory (disable minus-as-plus-inverse))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm k-*---p
;;    (equal (s-* n (m-unary-- p))
;; 	  (m-unary-- (s-* n p))))
|#

(local (in-theory (enable matrixp)))

(defthm k-*---p
  (implies (matrixp (r P)(c P) P)
	   (m-= (s-* n (m-- P))
		(m-- (s-* n P))))
  :hints (("Goal"
	   :in-theory (disable m-=_s-*_m--)
	   :use (:instance
		 m-=_s-*_m--
		 (M P)
		 (a n)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-unary--
;;    (equal (l (m-unary-- p))
;; 	  (l p)))
|#

(defthm numrows-unary--
  (equal (r (m-- P))
	 (r P)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-unary--
;;    (equal (c (m-unary-- p))
;; 	  (c p)))
|#

(defthm numcols-unary--
  (equal (c (m-- P))
	 (c P)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm unary---unary--
;;    (implies (m-matrixp m n p)
;; 	    (equal (m-unary-- (m-unary-- p))
;; 		   p)))
|#

(defthm unary---unary--
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-- (m-- P))
		P))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm unary---+
;;    (equal (m-unary-- (m-+ p q))
;; 	  (m-+ (m-unary-- p) (m-unary-- q))))
|#

(defthm unary---+
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (r P)(r Q))
		(equal (c P)(c Q)))
	   (m-= (m-- (m-+ P Q))
		(m-+ (m-- P)(m-- Q))))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm *---left
;;    (equal (m-* (m-unary-- p) q)
;; 	  (m-unary-- (m-* p q))))
|#

(local (in-theory (enable matrixp)))

(defthm *---left
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P)(r Q)))
	   (m-= (m-* (m-- P) Q)
		(m-- (m-* P Q))))
  :hints (("Goal"
	   :in-theory (disable M-*-M--_LEFT)
	   :use (:instance
		  M-*-M--_LEFT
		  (M1 P)
		  (M2 Q)
		  (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm *---right
;;    (equal (m-* p (m-unary-- q))
;; 	  (m-unary-- (m-* p q))))
|#

(local (in-theory (enable matrixp)))

(defthm *---right
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P)(r Q)))
	   (m-= (m-* P (m-- Q))
		(m-- (m-* P Q))))
  :hints (("Goal"
	   :in-theory (disable M-*-M--_right)
	   :use (:instance
		  M-*-M--_right
		  (M1 P)
		  (M2 Q)
		  (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-trans
;;    (equal (l (m-trans p)) (c p)))
|#

(defthm numrows-trans
   (equal (r (m-trans P))(c P)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-trans
;;    (equal (c (m-trans p)) (l p)))
|#

(defthm numcols-trans
  (equal (c (m-trans P))(r P)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm trans-*-scalar
;;    (equal (m-trans (s-* n p))
;; 	  (s-* n (m-trans p))))
|#

(local (in-theory (enable matrixp)))

(defthm trans-*-scalar
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-trans (s-* n P))
		(s-* n (m-trans P))))
  :hints (("Goal"
	   :in-theory (disable M-=-M-TRANS-S-*)
	   :use (:instance
		 M-=-M-TRANS-S-*
		 (s n)
		 (M P)
		 (name '$arg)))))


(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm trans---
;;    (equal (m-trans (m-unary-- p))
;; 	  (m-unary-- (m-trans p))))
|#

(local (in-theory (enable matrixp)))

(defthm trans---
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-trans (m-- P))
		(m-- (m-trans P))))
  :hints (("Goal"
	   :in-theory (disable M-=-M-TRANS-M-UNARY--)
	   :use (:instance
		 M-=-M-TRANS-M-UNARY--
		 (M P)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm trans-trans
;;    (implies (m-matrixp m n p)
;; 	    (equal (m-trans (m-trans p))
;; 		   p)))
|#

(defthm trans-trans
  (implies (matrixp (r P)(c P) P)
	   (m-= (m-trans (m-trans P))
		P))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm trans-+
;;    (implies (and (equal (l p) (l q))
;; 		 (equal (c p) (c q)))
;; 	    (equal (m-trans (m-+ p q))
;; 		   (m-+ (m-trans p) (m-trans q)))))
|#

(defthm trans-+
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (r P)(r Q))
		(equal (c P)(c Q)))
	    (m-= (m-trans (m-+ P Q))
		 (m-+ (m-trans P)(m-trans Q))))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm trans-*
;;    (implies (equal (c p) (l q))
;; 	    (equal (m-trans (m-* p q))
;; 		   (m-* (m-trans q) (m-trans p)))))
|#

(local (in-theory (enable matrixp)))

(defthm trans-*
  (implies (and (matrixp (r P)(c P) P)
		(matrixp (r Q)(c Q) Q)
		(equal (c P)(r Q)))
	   (m-= (m-trans (m-* P Q))
		(m-* (m-trans Q)(m-trans P))))
  :hints (("Goal"
	   :in-theory (disable
		       M-TRANS-M-*=M-*-M-TRANS)
	   :use (:instance
		 M-TRANS-M-*=M-*-M-TRANS
		 (M1 P)
		 (M2 Q)
		 (name '$arg)))))

(local (in-theory (disable matrixp)))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numrows-inv
;;    (implies (equal (c p) (l p))
;; 	    (equal (l (m-inv p)) (l p))))
|#

(defthm numrows-inv
  (implies (and (matrixp (r P)(c P) P)
		(equal (c P) (r P)))
	    (equal (r (m-/ P)) (r P)))
  :hints (("Goal"
	   :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm numcols-inv
;;    (implies (equal (c p) (l p))
;; 	    (equal (c (m-inv p)) (c p))))
|#

(defthm numcols-inv
   (implies (and (matrixp (r P)(c P) P)
		 (equal (c P) (r P)))
	    (equal (c (m-/ P)) (c P)))
   :hints (("Goal"
	    :in-theory (enable matrixp))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm non-singulars-are-square
;;    (implies (not (m-singular p))
;; 	    (equal (c p) (l p))))
|#

(defthm non-singulars-are-square
  (implies (not (m-singularp P))
	   (equal (c P)(r P))))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm inv-*-x
;;    (implies (and (m-matrixp m n p)
;; 		 (not (m-singular p)))
;; 	    (equal (m-* (m-inv p) p)
;; 		   (m-id (l p)))))
|#

(defthm inv-*-x
  (implies (not (m-singularp P))
	   (m-= (m-* (m-/ P) P)
		(m-1 (r P)))))

(in-theory (disable LEFT-M-*-INVERSE-OF-M-/))

#|;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  (defthm x-*-inv
;;    (implies (and (m-matrixp m n p)
;; 		 (not (m-singular p)))
;; 	    (equal (m-* p (m-inv p))
;; 		   (m-id (l p)))))
|#

(defthm x-*-inv
  (implies (not (m-singularp P))
	   (m-= (m-* P (m-/ P))
		(m-1 (r P)))))

(in-theory (disable RIGHT-M-*-INVERSE-OF-M-/))

;; )
