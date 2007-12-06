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
     Last modified  2 June 2004
|#

(in-package "ACL2")

(ubt! 1)

; In each case, we include the necessary books (presumably because at
; least something needs to be included in order to provide the
; necessary packages), then we certify a book, then we undo back to
; the start, avoiding all queries by using :u.

(certify-book "rational-listp" 0 nil)
:u

(defpkg 
  "ACL2-ASG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))

(defpkg 
  "ACL2-AGP"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))

(defpkg 
  "ACL2-CRG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))

(certify-book "equalities" 3 nil)
:u :u :u :u

(certify-book "inequalities" 0 nil)
:u

(certify-book "mod-gcd")
:u

(certify-book "rationals" 0 nil)
:u

; Here are some miscellaneous books added by Ruben Gamboa.

#+:non-standard-analysis
(certify-book "realp" 0 nil)
#+:non-standard-analysis
:u

#+:non-standard-analysis
(certify-book "real-listp" 0 nil)
#+:non-standard-analysis
:u

(certify-book "natp-posp" 0 nil)
:u

; Build the top-level book.

(certify-book "top" 0 nil)
:u

; Build some other books from Ruben Gamboa.

(certify-book "idiv" 0 nil)
:u

(certify-book "abs" 0 nil)
:u

(certify-book "factorial" 0 nil)
:u

(certify-book "sumlist" 0 nil)
:u

(certify-book "binomial" 0 nil)
:u
