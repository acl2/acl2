; More material on DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This characterizes the nodenums of a reversed DAG

(include-book "dags")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

;; TODO: Same as consecutivep of strip-cars?
(defund cars-increasing-by-1 (rev-dag)
  (declare (xargs :guard (weak-dagp-aux rev-dag)))
  (if (endp rev-dag)
      t
    (if (endp (cdr rev-dag))
        t
      (and (equal (car (second rev-dag))
                  (+ 1 (car (first rev-dag))))
           (cars-increasing-by-1 (rest rev-dag))))))

(defthm cars-increasing-by-1-of-append
  (equal (cars-increasing-by-1 (append x y))
         (if (not (consp x))
             (cars-increasing-by-1 y)
           (if (not (consp y))
               (cars-increasing-by-1 x)
             (and (cars-increasing-by-1 x)
                  (cars-increasing-by-1 y)
                  (equal (car (car y))
                         (+ 1 (car (car (last x)))))))))
  :hints (("Goal" :in-theory (enable cars-increasing-by-1))))

(defthm cars-increasing-by-1-of-reverse-list
  (implies (and (pseudo-dagp-aux dag nodenum)
                (integerp nodenum))
           (cars-increasing-by-1 (reverse-list dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux reverse-list cars-increasing-by-1))))

(defthm cars-increasing-by-1-of-reverse-list-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (cars-increasing-by-1 (reverse-list dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthmd car-of-cadr-when-cars-increasing-by-1
  (implies (and (cars-increasing-by-1 rev-dag)
                (consp rev-dag)
                )
           (equal (car (cadr rev-dag))
                  (if (consp (cdr rev-dag))
                      (+ 1 (car (car rev-dag)))
                    nil)))
  :hints (("Goal" :in-theory (enable cars-increasing-by-1))))

(defthm cars-increasing-by-1-of-cdr
  (implies (cars-increasing-by-1 rev-dag)
           (cars-increasing-by-1 (cdr rev-dag)))
  :hints (("Goal" :in-theory (enable cars-increasing-by-1))))

(defthmd car-of-car-of-last-when-cars-increasing-by-1-linear
  (implies (and (weak-dagp-aux rev-dag)
                (cars-increasing-by-1 rev-dag)
                (consp rev-dag))
           (<= (car (car rev-dag)) (car (car (last rev-dag)))))
  :rule-classes ((:linear :trigger-terms ((car (car (last rev-dag))))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux
                                     cars-increasing-by-1))))
