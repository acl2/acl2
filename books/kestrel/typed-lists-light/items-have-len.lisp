; A function to check that all elements of a list have a given length
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Rename to all-have-lenp?
(defund items-have-len (n lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      t
    (and (equal n (len (car lst))) ;faster to walk down the list and decrement n simultaneously?
         (items-have-len n (cdr lst)))))

(defthm items-have-len-of-nil
  (items-have-len n nil)
  :hints (("Goal" :in-theory (enable items-have-len))))

(defthm items-have-len-of-cdr
  (implies (items-have-len n lst)
           (items-have-len n (cdr lst)))
  :hints (("Goal" :in-theory (enable items-have-len))))

(defthm items-have-len-of-cons
  (equal (items-have-len n (cons item lst))
         (and (equal n (len item))
              (items-have-len n lst)))
  :hints (("Goal" :in-theory (enable items-have-len))))

;should the quantify macro include this?
(defthm items-have-len-of-update-nth
  (implies (and (equal n (len val))
                (natp m)
                ;; (natp n)
                (< m (len lst))
                (items-have-len n lst))
           (items-have-len n (update-nth m val lst)))
  :hints (("Goal" :in-theory (enable update-nth items-have-len))))

(defthm items-have-len-of-append
  (equal (items-have-len n (append x y))
         (and (items-have-len n x)
              (items-have-len n y)))
  :hints (("Goal" :in-theory (enable items-have-len append))))

(defthm items-have-len-of-true-list-fix
  (equal (items-have-len n (true-list-fix lst))
         (items-have-len n lst))
  :hints (("Goal" :expand (items-have-len n (true-list-fix lst))
           :in-theory (enable items-have-len))))

(defthm items-have-len-when-not-consp
  (implies (not (consp lst))
           (items-have-len n lst))
  :hints (("Goal" :in-theory (enable items-have-len))))

(defthm items-have-len-of-nthcdr
  (implies (items-have-len n lst)
           (items-have-len n (nthcdr m lst)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm len-of-car-when-items-have-len
  (implies (and (items-have-len n lst) ;n is a free var
                (consp lst))
           (equal (len (car lst))
                  n)))

(defthm len-of-nth-when-items-have-len
  (implies (items-have-len n lst)
           (equal (len (nth n2 lst))
                  (if (<= (len lst) (nfix n2))
                      0
                    n)))
  :hints (("Goal" :in-theory (enable nth))))
