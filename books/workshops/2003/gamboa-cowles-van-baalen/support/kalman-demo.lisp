; The ACL2 Matrix Algebra Book. Summary of definitions and algebra in matrix.lisp.
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
;  Last modified 1 November 2002.

#|
 To certify in ACL2 Version 2.6

  (ld ;; Newline to fool dependency scanner
    "defpkg.lsp")
  (certify-book "kalman-demo" 1)
|#

(in-package "KALMAN")

(include-book "kalman-proof")

(defun kalman-loop-body (xhatmin-prev pminus-prev k)
  (let* ((gain (m-* pminus-prev
		    (m-* (m-trans (h k))
			 (m-inv (m-+ (m-* (h k)
					  (m-* pminus-prev
					       (m-trans (h k))))
				     (r k))))))
	 (xhat (m-+ xhatmin-prev
		    (m-* gain
			 (m-- (z k)
			      (m-* (h k) xhatmin-prev)))))
	 (pplus (m-* (m-- (m-id (n))
			  (m-* gain (h k)))
		     pminus-prev))
	 (xhatmin (m-* (phi k) xhat))
	 (pminus (m-+ (m-* (phi k)
			   (m-* pplus
				(m-trans (phi k))))
		      (q k))))
    (mv gain xhat pplus xhatmin pminus)))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (integerp k)
		  (<= 0 k)
		  (equal xhatmin-prev (xhatmin k))
		  (equal pminus-prev (pminus k)))
	     (mv-let (gain xhat pplus xhatmin pminus)
		     (kalman-loop-body xhatmin-prev pminus-prev k)
		     (declare (ignore xhat pplus xhatmin pminus))
		     (equal gain (gain k))))
    :hints (("Goal"
	     :in-theory (disable acl2::*-+-right acl2::*-+-left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+)))))

 (local
  (defthm lemma-2
    (implies (and (integerp k)
		  (<= 0 k)
		  (equal xhatmin-prev (xhatmin k))
		  (equal pminus-prev (pminus k)))
	     (mv-let (gain xhat pplus xhatmin pminus)
		     (kalman-loop-body xhatmin-prev pminus-prev k)
		     (declare (ignore gain pplus xhatmin pminus))
		     (equal xhat (xhat k))))
    :hints (("Goal"
	     :in-theory (disable acl2::*-+-right acl2::*-+-left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+)))))

 (local
  (defthm lemma-3
    (implies (and (integerp k)
		  (<= 0 k)
		  (equal xhatmin-prev (xhatmin k))
		  (equal pminus-prev (pminus k)))
	     (mv-let (gain xhat pplus xhatmin pminus)
		     (kalman-loop-body xhatmin-prev pminus-prev k)
		     (declare (ignore gain xhat xhatmin pminus))
		     (equal pplus (pplus k))))
    :hints (("Goal"
	     :in-theory (disable pplus-as-mean
				 acl2::*-+-right acl2::*-+-left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+)))))

 (local
  (defthm lemma-4
    (implies (and (integerp k)
		  (<= 0 k)
		  (equal xhatmin-prev (xhatmin k))
		  (equal pminus-prev (pminus k)))
	     (mv-let (gain xhat pplus xhatmin pminus)
		     (kalman-loop-body xhatmin-prev pminus-prev k)
		     (declare (ignore gain xhat pplus pminus))
		     (equal xhatmin (xhatmin (1+ k)))))
    :hints (("Goal"
	     :in-theory (disable acl2::*-+-right acl2::*-+-left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+)))))

 (local
  (defthm lemma-5
    (implies (and (integerp k)
		  (<= 0 k)
		  (equal xhatmin-prev (xhatmin k))
		  (equal pminus-prev (pminus k)))
	     (mv-let (gain xhat pplus xhatmin pminus)
		     (kalman-loop-body xhatmin-prev pminus-prev k)
		     (declare (ignore gain xhat pplus xhatmin))
		     (equal pminus (pminus (1+ k)))))
    :hints (("Goal"
	     :in-theory (disable pplus-as-mean
				 pminus-as-mean
				 pminus-as-mean-almost
				 acl2::*-+-right acl2::*-+-left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+)))))

 (defthm kalman-loop-invariant
   (implies (and (integerp k)
		 (<= 0 k)
		 (equal xhatmin-prev (xhatmin k))
		 (equal pminus-prev (pminus k)))
	    (mv-let (gain xhat pplus xhatmin pminus)
		    (kalman-loop-body xhatmin-prev pminus-prev k)
		    (and (equal gain (gain k))
			 (equal xhat (xhat k))
			 (equal pplus (pplus k))
			 (equal xhatmin (xhatmin (1+ k)))
			 (equal pminus (pminus (1+ k))))))
   :hints (("Goal"
	    :use ((:instance lemma-1)
		  (:instance lemma-2)
		  (:instance lemma-3)
		  (:instance lemma-4)
		  (:instance lemma-5)))))
 )

