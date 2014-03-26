; ACL2 books on arithmetic metafunctions
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

; Written by:  John Cowles and Matt Kaufmann
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.



(in-package "ACL2")

(include-book "term-defuns")

(defthm delete-non-member
  (implies (not (memb x y))
           (equal (del x y) y)))

(defthm member-delete
     (implies (memb x (del u v))
	      (memb x v)))

(defthm delete-commutativity
     (equal (del x (del y z))
	    (del y (del x z))))

(defthm subbagp-delete
     (implies (subbagp x (del u y))
	      (subbagp x y)))

(defthm subbagp-cdr1
     (implies (and (subbagp x y)
                   (consp x))
	      (subbagp (cdr x) y)))

(defthm subbagp-cdr2
     (implies (and (subbagp x (cdr y))
                   (consp y))
	      (subbagp x y)))

(defthm subbagp-bagint1
     (subbagp (bagint x y) x))

(defthm subbagp-bagint2
     (subbagp (bagint x y) y))

(defthm memb-append
  (equal (memb a (append x y))
         (or (memb a x)
             (memb a y))))

(defthm binary-op_tree-opener
  (and (implies (not (consp lst))
                (equal (binary-op_tree binary-op-name constant-name fix-name lst)
                       (list 'quote constant-name)))
       (equal (binary-op_tree binary-op-name constant-name fix-name (cons x lst))
              (cond
               ((not (consp lst))
                (list fix-name x))
               ((and (consp lst)
                     (not (consp (cdr lst))))
                (list binary-op-name x (car lst)))
               (t (list binary-op-name x
                        (binary-op_tree binary-op-name constant-name fix-name
                                        lst)))))))

(defthm binary-op_tree-simple-opener
  (and (implies (not (consp lst))
                (equal (binary-op_tree-simple binary-op-name constant-name lst)
                       (list 'quote constant-name)))
       (equal (binary-op_tree-simple binary-op-name constant-name (cons x lst))
              (cond
               ((not (consp lst))
                x)
               (t (list binary-op-name x
                        (binary-op_tree-simple binary-op-name constant-name
                                               lst)))))))

(defthm fringe-occur-same-as-occur-in-fringe
  (equal (fringe-occur binop arg term)
         (memb arg (binary-op_fringe binop term))))

