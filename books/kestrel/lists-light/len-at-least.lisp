; A function to compare a list's length to a number
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Test whether the length of LST is at least N.  This may be faster than
;; computing and comparing the len, especially when the list is long and N is
;; small, because this function does not have to walk all the way to the end of
;; the list.
(defund len-at-least (n lst)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (consp lst)
         (len-at-least (+ -1 n) (rest lst)))))

(defthm len-at-least-correct
  (implies (natp n)
           (equal (len-at-least n lst)
                  (<= n (len lst))))
  :hints (("Goal" :in-theory (enable len-at-least))))

(defthm len-at-least-of-append
  (implies (len-at-least n x)
           (len-at-least n (append x y)))
  :hints (("Goal" :in-theory (enable len-at-least))))
