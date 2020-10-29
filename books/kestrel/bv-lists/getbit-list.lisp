; BV Lists Library: getbit-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/getbit-def" :dir :system)
(local (include-book "kestrel/bv/getbit" :dir :system))
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "bvchop-list")

;use a map
(defund getbit-list (n lst)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (true-listp lst)
                              (all-integerp lst))))
  (if (endp lst)
      nil
    (cons (getbit n (car lst))
          (getbit-list n (cdr lst)))))

(defthm nth-of-getbit-list
  (implies (natp i)
           (equal (nth i (getbit-list esize data))
                  (if (< i (len data))
                      (getbit esize (nth i data))
                    nil)))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
    :in-theory (e/d (;list::nth-of-cons
                     nth getbit-list)
                    (;nth-of-cdr
                     )))))


;more generally, getbit-list of a bit list...
(defthm getbit-list-of-0-and-getbit-list-of-0
  (equal (getbit-list 0 (getbit-list 0 data))
         (getbit-list 0 data))
  :hints (("Goal" :in-theory (enable getbit-list))))

(defthm getbit-list-of-update-nth
  (implies (and (natp n) (< n (len lst)))
           (equal (getbit-list m (update-nth n val lst))
                  (update-nth n (getbit m val)
                              (getbit-list m lst))))
  :hints (("Goal" :in-theory (enable getbit-list update-nth))))

(defthm len-of-getbit-list
  (equal (len (getbit-list size lst))
         (len lst))
  :hints (("Goal" :in-theory (enable getbit-list))))

(defthm getbit-list-of-bvchop-list
  (implies (and (< n size)
                (natp n)
                (natp size))
           (equal (getbit-list n (bvchop-list size lst))
                  (getbit-list n lst)))
  :hints (("Goal" :in-theory (e/d (bvchop-list getbit-list) (ifix)))))

(defthm all-unsigned-byte-p-of-getbit-list
  (all-unsigned-byte-p 1 (getbit-list n lst))
  :hints (("Goal" :in-theory (enable getbit-list all-unsigned-byte-p))))

(defthm getbit-list-of-take
  (implies (and (<= n (len lst))
                (natp n))
           (equal (getbit-list esize (take n lst))
                  (take n (getbit-list esize lst))))
  :hints (("Goal" :in-theory (e/d (getbit-list take) ()))))

(defthm getbit-list-of-cons
  (equal (getbit-list n (cons a b))
         (cons (getbit n a)
               (getbit-list n b)))
  :hints (("Goal" :in-theory (enable getbit-list))))

;bozo
(defthm getbit-list-of-0-does-nothing
  (implies (and (all-unsigned-byte-p 0 lst)
                (true-listp lst))
           (equal (getbit-list 1 lst)
                  lst))
  :hints (("Goal" :induct t
           :in-theory (enable GETBIT-LIST ALL-UNSIGNED-BYTE-P))))

(defthm getbit-list-too-high
  (implies (and (all-unsigned-byte-p n lst)
                (true-listp lst))
           (equal (getbit-list n lst)
                  (repeat (len lst) 0)))
  :hints (("Goal" :induct t
           :in-theory (enable GETBIT-LIST ALL-UNSIGNED-BYTE-P))))

(defthm getbit-list-of-true-list-fix
  (equal (getbit-list n (true-list-fix x))
         (getbit-list n x))
  :hints (("Goal" :in-theory (enable getbit-list))))
