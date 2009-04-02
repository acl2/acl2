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
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

#| Modified by John Cowles, University of Wyoming, Summer 1998
     Last modified 30 June 1998
|#

(in-package "ACL2")

(include-book "equalities")

; The following depends on nothing.

(include-book "rational-listp")

;; Ruben Gamboa added the following books for ACL2(r) (see :doc real).

#+:non-standard-analysis
(include-book "realp")
#+:non-standard-analysis
(include-book "real-listp")

; The following two depend individually on the first.

(include-book "inequalities")

(include-book "natp-posp")

(include-book "rationals")

