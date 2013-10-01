;; ACL2 books for Archimedean Ordered Fields and
;;  Knuth's Generalized 91 Recursion.
; Copyright (C) 2000  John R. Cowles, University of Wyoming

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
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

;; Certify the ACL2 Archimedean Ordered Field book and the
;;  ACL2 book for Knuth's Generalized 91 Recursion.

(in-package "ACL2")

(ubt! 1)

;; We certify a book, then we undo back to the start, 
;;  avoiding all queries by using :u.

(defpkg 
  "ACL2-ASG"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
(defpkg 
  "ACL2-AGP"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
(defpkg 
  "ACL2-CRG"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))

(certify-book "aof" 3 nil)
:u :u :u :u

(certify-book "knuth-arch" 0 nil)


