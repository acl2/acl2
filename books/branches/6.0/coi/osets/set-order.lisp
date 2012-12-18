#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
#|

   Fully Ordered Finite Sets, Version 0.81
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.

 set-order.lisp

   This is a top level file which you should use if you intend to 
   reason about the set order.  Normally you should not do this, 
   but you might need it if you want to argue "from first principles"
   that list operations create sets, i.e. for efficiency reasons.

   Note that merely including this file will do nothing for you.  
   You need to also enable the relavent theories:
    
      primitive-reasoning
        basic definitions of the primitive functions.  useful if you
        have a very low level proof about the stucture of sets or 
        something.  doesn't pertain to the order itself.

      order-reasoning
        properties of the order itself, and its relation to the set
        primitives.  most of the membership level is based on this.

      cons-reasoning
        properties relating cons to sets through the set order.  
        this might be useful if you are introducing new "fast" 
        functions, based on cons rather than insert to construct
        sets.  it is not easy to reason with. 

|#

(in-package "SET")
(set-verify-guards-eagerness 2)

(local (include-book "primitives"))
(local (include-book "membership"))
(local (include-book "fast"))
(include-book "sets")

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))


; -------------------------------------------------------------------
; primitive-reasoning 

(deftheory primitive-reasoning
  '(setp
    empty
    head
    tail
    sfix
    insert))



; -------------------------------------------------------------------
; order-reasoning

;;; Replaced by Matt K. after Jared D.'s modification
;;; in svn 1015 of that book, since there is now a conflict:
(include-book "misc/total-order" :dir :system)
#||
(defthmd <<-type
  (or (equal (<< a b) t)
      (equal (<< a b) nil))
  :rule-classes :type-prescription)

(defthmd <<-irreflexive
  (not (<< a a)))

(defthmd <<-transitive
  (implies (and (<< a b) (<< b c))
           (<< a c)))

(defthmd <<-asymmetric
  (implies (<< a b)
           (not (<< b a))))

(defthmd <<-trichotomy
  (implies (and (not (<< b a))
                (not (equal a b)))
           (<< a b)))
||#

(defthmd head-insert
  (equal (head (insert a X))
         (cond ((empty X) a)
               ((<< a (head X)) a)
               (t (head X)))))

(defthmd tail-insert
  (equal (tail (insert a X))
         (cond ((empty X) (sfix X))
               ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthmd head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthmd head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(deftheory order-reasoning
  '(; <<-type ; see comment above about svn 1015
    <<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    (:induction insert)
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

; -------------------------------------------------------------------
; cons-reasoning

(defthmd cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X)))))

(defthmd cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a)))

(defthmd cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X))))

(defthmd cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X))))

(defthmd cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))

(deftheory cons-reasoning
  '(cons-set
    cons-head
    cons-to-insert-empty
    cons-to-insert-nonempty
    cons-in))

