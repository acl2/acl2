; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.

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
; Ruben Gamboa
; LIM International, Inc.
; 9390 Research Blvd, Suite II-200
; Austin, TX 78759 U.S.A.

; Plagiarized from rational-listp.lisp.

(in-package "ACL2")

#+:non-standard-analysis
(defthm append-preserves-real-listp
  (implies (true-listp x)
           (equal (real-listp (append x y))
                  (and (real-listp x)
                       (real-listp y)))))

#+:non-standard-analysis
(defthm realp-car-real-listp
  (implies (and (real-listp x)
		x)
	   (realp (car x)))
  :rule-classes :forward-chaining)
