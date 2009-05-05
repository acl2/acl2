;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(set-verify-guards-eagerness 2)

(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(local (defthm len-when-consp
         (implies (consp x)
                  (< 0 (len x)))
         :rule-classes ((:linear) (:rewrite))))

(defthm true-listp-of-revappend
  (equal (true-listp (revappend x y))
         (true-listp y)))
  
(defthm consp-of-revappend
  (equal (consp (revappend x y))
         (or (consp x)
             (consp y))))

(defthm len-of-revappend
  (equal (len (revappend x y))
         (+ (len x)
            (len y))))

(defthm nth-of-revappend
  (equal (nth n (revappend x y))
         (if (<= (len x) (nfix n))
             (nth (- (nfix n) (len x)) 
                  y)
           (nth (+ (1- (len x)) (- (nfix n))) 
                x))))

(defthm equal-when-revappend-same
  (equal (equal (revappend x y1)
                (revappend x y2))
         (equal y1 y2)))


(local (defthm revappend-last-is-car
         (implies (consp x)
                  (equal (nth (1- (len x)) 
                              (revappend x y))
                         (car x)))))

(local (defthm revappend-lengths-x
         (implies (not (equal (len x1) (len x2)))
                  (not (equal (revappend x1 y)
                              (revappend x2 y))))
         :hints(("Goal" :use ((:instance len (x (revappend x1 y)))
                              (:instance len (x (revappend x2 y))))))))
 
(local (defthm revappend-equal-x-cdrs-lemma
         (implies (and (true-listp x1) (consp x1)
                       (true-listp x2) (consp x2)
                       (not (equal x1 x2))
                       (equal (cdr x1) (cdr x2)))
                  (not (equal (revappend x1 y)
                              (revappend x2 y))))))

(local (defthm revappend-equal-x-cars-lemma
         (implies (and (true-listp x1) (consp x1)
                       (true-listp x2) (consp x2)
                       (not (equal (car x1) (car x2))))
                  (not (equal (revappend x1 y)
                              (revappend x2 y))))
         :hints(("Goal"
                 :in-theory (disable revappend-lengths-x
                                     revappend-last-is-car)
                 :use ((:instance revappend-lengths-x)
                       (:instance revappend-last-is-car (x x1))
                       (:instance revappend-last-is-car (x x2)))))))
        
(local (defthm revappend-nonempty-list
         (implies (consp x)
                  (not (equal (revappend x y) y)))
         :hints(("Goal" :use ((:instance len (x (revappend x y)))
                              (:instance len (x y)))))))
        
(local (defun revappend-induction-2 (x y acc)
         (if (and (consp x)
                  (consp y))
             (revappend-induction-2 (cdr x) (cdr y) (cons (car x) acc))
           (list x y acc))))

(defthm equal-of-revappends-when-true-listps
  (implies (and (true-listp x1)
                (true-listp x2))
           (equal (equal (revappend x1 y)
                         (revappend x2 y))
                  (equal x1 x2)))
  :hints(("Goal" 
          :induct (revappend-induction-2 x1 x2 y))
         ("Subgoal *1/1" 
          :in-theory (disable revappend-equal-x-cdrs-lemma
                              revappend-equal-x-cars-lemma)
          :use ((:instance revappend-equal-x-cdrs-lemma)
                (:instance revappend-equal-x-cars-lemma)))))