; Finite Set Theory for ACL2

; Copyright (C) 2001  Georgia Institute of Technology

; This book is derived from the book "total-ordering-original" by J
; Moore, which is included in this directory.  The difference between
; this version and J Moore's version is that I use the total order
; built into ACL2 (starting with version 2.6).  This allows me to
; significantly simplify some of the theorems and to also remove
; theorems.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Panagiotis Manolios
; email:      manolios@cc.gatech.edu
; College of Computing
; CERCS Lab
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

(in-package "ACL2")

; We define an irreflexive total ordering on the ACL2 universe.

; We export
; (<< x y)                 disabled   the total ordering

; <<-irreflexivity                    the four obvious theorems about
; <<-trichotomy            disabled   total orders
; <<-mutual-exclusion      disabled
; <<-transitivity          disabled

; We provide ``fast'' versions of the slow rules, named

; fast-<<-trichotomy       enabled
; fast-<<-mutual-exclusion enabled
; fast-<<-transitivity     enabled

; We also provide two theory macros for fiddling with the status of
; these rules.

; Options:
; :in-theory (fast-<<-rules)      ; the default setting above
; :in-theory (fast-<<-rules <<)   ; default plus << enabled
; :in-theory (slow-<<-rules)      ; slow rules enabled but << disabled
; :in-theory (slow-<<-rules <<)   ; slow rules and << enabled

; These macros never enable BOTH the fast and slow rules.  Sometimes
; you need << and sometimes you don't.  The optional << always has the
; same effect whether you're using fast- or slow-<<-rules.  Including
; the << arg ENABLES <<.

(defun <<< (x y)
  (declare (xargs :guard t))
  (and (not (equal x y))
       (lexorder x y)))

(defun << (x y)
  (declare (xargs :guard t))
  (cond ((eq x nil)
	 (not (eq y nil)))
	((atom x)
	 (cond ((eq y nil) nil)
	       (t (<<< x y))))
        ((atom y) nil)
        ((equal (car x) (car y))
         (<< (cdr x) (cdr y)))
        (t (<< (car x) (car y)))))

(defthm <<-irreflexivity
  (not (<< x x)))

(local
(defthm lexorder-atom
  (implies (and (atom x)
		(consp y))
	   (lexorder x y))
  :hints (("Goal" :in-theory (enable lexorder)))))

(defthm <<-trichotomy
  (or (<< x y)
      (equal x y)
      (<< y x))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (not (<< x y))
                           (not (equal x y)))
                      (<< y x)))))

(defthm <<-mutual-exclusion
  (implies (<< x y)
           (and (not (equal x y))
                (not (<< y x)))))

(defthm <<-transitivity
  (implies (and (<< x y)
                (<< y z))
           (<< x z)))

(defthm fast-<<-trichotomy
  (and (implies (and (not (<< xxx y))
                     (equal xxx x)
                     (not (equal x y)))
                (<< y x))
       (implies (and (not (<< x yyy))
                     (equal yyy y)
                     (not (equal x y)))
                (<< y x))))

(defthm fast-<<-mutual-exclusion
  (and (implies (and (<< xxx y)
                     (equal xxx x))
                (and (not (equal x y))
                     (not (<< y x))))
       (implies (and (<< x yyy)
                     (equal yyy y))
                (and (not (equal x y))
                     (not (<< y x))))))

(defthm fast-<<-transitivity
  (implies (and (<< x y)
                (<< yyy z)
                (equal yyy x))
           (<< x z)))

(defmacro fast-<<-rules (&optional <<)

; If << is non-nil, then enable <<, else, don't.

  `(set-difference-theories (enable ,@(if << '((:DEFINITION <<) (:definition acl2::alphorder)) nil)
                                    fast-<<-trichotomy
                                    fast-<<-mutual-exclusion
                                    fast-<<-transitivity)
                            '(,@(if << nil '((:DEFINITION <<)))
                              <<-trichotomy
                              <<-mutual-exclusion
                              <<-transitivity)))

(defmacro slow-<<-rules (&optional <<)

; If << is non-nil, then enable <<, else, don't.

  `(set-difference-theories (enable ,@(if << '((:DEFINITION <<) (:definition acl2::alphorder)) nil)
                                    <<-trichotomy
                                    <<-mutual-exclusion
                                    <<-transitivity)
                            '(,@(if << nil '((:DEFINITION <<)))
                              fast-<<-trichotomy
                              fast-<<-mutual-exclusion
                              fast-<<-transitivity)))

(in-theory (fast-<<-rules))
