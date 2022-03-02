;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "PICK-A-POINT")
(include-book "coi/util/in-conclusion" :dir :system)

(defstub fix (x)
  nil)

(defun list-equiv (x y)
  (if (not (consp x))
      (not (consp y))
    (and (consp y)
         (let ((a (fix (car x)))
               (b (fix (car y))))
           (and (equal a b)
                (list-equiv (cdr x) (cdr y)))))))

(defun index (x y)
  (if (not (and (consp x) (consp y)))
      -1
    (let ((a (fix (car x)))
          (b (fix (car y))))
      (if (not (equal a b)) 0
        (+ 1 (index (cdr x) (cdr y)))))))

(defthm index-bounds
  (and (<= -1 (index x y))
       (< (index x y) (len x))
       (< (index x y) (len y))))

(defthm canary
  (list
   (fix x)
   (list-equiv x y)
   (index x y)
   )
  :rule-classes nil)

(defthm list-equiv-reduction
  (iff (list-equiv x y)
       (and (equal (len x) (len y))
            (equal (fix (nth (index x y) x))
                   (fix (nth (index x y) y))))))

(defmacro def::pick-a-point (&key (type-fix 'nil) (list-equiv 'nil) (in-theory 'nil))
  (let* ((index                           (acl2::packn-pos (list list-equiv '-point) 'index))
         (list-equiv-pick-a-point         (acl2::packn-pos (list list-equiv '-pick-a-point) list-equiv))
         (list-equiv-pick-a-point-rewrite (acl2::packn-pos (list list-equiv '-pick-a-point-rewrite) list-equiv))
         )
    `(encapsulate
         ()

       ,@(and in-theory `((in-theory ,in-theory)))
       
       (defun ,index (x y)
         (if (not (and (consp x) (consp y))) -1
           (let ((a (,type-fix (car x)))
                 (b (,type-fix (car y))))
             (if (not (equal a b)) 0
               (+ 1 (,index (cdr x) (cdr y)))))))

       (local
        (defthm ,(acl2::packn-pos (list list-equiv '-definition) 'index)
          (equal (,list-equiv x y)
                 (if (not (consp x))
                     (not (consp y))
                   (and (consp y)
                        (let ((a (,type-fix (car x)))
                              (b (,type-fix (car y))))
                          (and (equal a b)
                               (,list-equiv (cdr x) (cdr y)))))))
          :rule-classes :definition))
       
       (local
        (defthm ,(acl2::packn-pos (list list-equiv '-canary) 'index)
          (list
           (,type-fix x)
           (,list-equiv x y)
           (,index x y)
           )
          :hints (("Goal" :use ((:functional-instance canary
                                                      (fix ,type-fix)
                                                      (list-equiv ,list-equiv)
                                                      (index ,index)))))))

       (local (in-theory (acl2::theory 'acl2::minimal-theory)))

       (defthm ,(acl2::packn-pos (list index '-upper-bound) 'index)
         (and (< (,index x y) (len x))
              (< (,index x y) (len y)))
         :hints (("Goal" :use ((:functional-instance index-bounds
                                                     (fix ,type-fix)
                                                     (list-equiv ,list-equiv)
                                                     (index ,index)))))
         :rule-classes (:rewrite :linear))
       
       (defthmd ,list-equiv-pick-a-point
         (iff (,list-equiv x y)
              (and (equal (len x) (len y))
                   (equal (,type-fix (nth (,index x y) x))
                          (,type-fix (nth (,index x y) y)))))
         :hints (("Goal" :use ((:functional-instance list-equiv-reduction
                                                     (fix ,type-fix)
                                                     (list-equiv ,list-equiv)
                                                     (index ,index))))))
       
       (defthmd ,list-equiv-pick-a-point-rewrite
         (implies
          (in-conclusion-check (,list-equiv x y) :top :negated)
          (iff (,list-equiv x y)
               (and (equal (len x) (len y))
                    (equal (,type-fix (nth (,index x y) x))
                           (,type-fix (nth (,index x y) y))))))
         :hints (("Goal" :in-theory '(,list-equiv-pick-a-point))))
       
       
       )))
