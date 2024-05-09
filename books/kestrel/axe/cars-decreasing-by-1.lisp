(in-package "ACL2")

(include-book "cars-increasing-by-1")
(local (include-book "kestrel/lists-light/append" :dir :system))

(defund cars-decreasing-by-1 (rev-dag)
  (declare (xargs :guard (weak-dagp-aux rev-dag)))
  (if (endp rev-dag)
      t
    (if (endp (cdr rev-dag))
        t
      (and (equal (car (second rev-dag))
                  (+ -1 (car (first rev-dag))))
           (cars-decreasing-by-1 (rest rev-dag))))))

(defthm cars-decreasing-by-1-of-append
  (equal (cars-decreasing-by-1 (append x y))
         (if (not (consp x))
             (cars-decreasing-by-1 y)
           (if (not (consp y))
               (cars-decreasing-by-1 x)
             (and (cars-decreasing-by-1 x)
                  (cars-decreasing-by-1 y)
                  (equal (car (car y))
                         (+ -1 (car (car (last x)))))))))
  :hints (("Goal" :in-theory (enable cars-decreasing-by-1 append))))

(defthm cars-decreasing-by-1-of-reverse
  (implies (integer-listp (strip-cars dag)) ;drop?
           (equal (cars-decreasing-by-1 (reverse-list dag))
                  (cars-increasing-by-1 dag)))
  :hints (("Goal" :in-theory (enable cars-decreasing-by-1 cars-increasing-by-1 reverse-list))))
