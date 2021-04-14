; Recognize when all elems of one list are <= all elems of another
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-less-than-or-equal")

;;;
;;; all-<=-all
;;;

;move
(defund all-<=-all (x y)
  (if (endp y)
      t
    (and (all-<= x (first y))
         (all-<=-all x (rest y)))))

(defthm all-<=-of-car-of-last
  (implies (and (all-<=-all x y)
                (consp y))
           (all-<= x (car (last y))))
  :hints (("Goal" :in-theory (enable all-<= all-<=-all))))

(defthm all-<=-all-of-append
  (equal (all-<=-all x (append y1 y2))
         (and (all-<=-all x y1)
              (all-<=-all x y2)))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-of-reverse-list-arg2
  (equal (all-<=-all x (reverse-list y))
         (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all reverse-list))))

(defthm all-<=-all-of-cdr-arg1
  (implies (all-<=-all x y)
           (all-<=-all (cdr x) y))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (all-<=-all x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-<=-all))))
