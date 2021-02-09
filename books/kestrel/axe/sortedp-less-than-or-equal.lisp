; Recognizing a sorted list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund sortedp-<= (x)
  (declare (xargs :guard (rational-listp x)))
  (if (endp x)
      t
    (if (endp (rest x))
        t
      (and (<= (first x) (second x)) ;allows dups
           (sortedp-<= (rest x))))))

(defthm sortedp-<=-of-cdr
  (implies (sortedp-<= x)
           (sortedp-<= (cdr x)))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthmd <=-of-first-and-second-when-sortedp
  (implies (and (sortedp-<= x)
                (consp (cdr x)))
           (<= (first x) (second x)))
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthm sortedp-<=-of-singleton
  (sortedp-<= (list x))
  :hints (("Goal" :in-theory (enable sortedp-<=))))
