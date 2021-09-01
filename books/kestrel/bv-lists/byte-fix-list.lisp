; Fix every element of a list to be a signed byte
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/logext" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

;; note that this fixes the items to be *signed* bytes
;bozo use logext-list?  maybe rename to sbyte-fix-list?
(defun byte-fix-list (items)
  (if (endp items)
      nil
    (cons (logext 8 (car items))
          (byte-fix-list (cdr items)))))

(defthm len-of-byte-fix-list
  (equal (len (byte-fix-list lst))
         (len lst))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

;; (defthm byte-fix-list-when-byte-p-list
;;   (implies (byte-p-list x)
;;            (equal (byte-fix-list x)
;;                   (true-list-fix x))))

(defthm car-of-byte-fix-list
  (implies (consp lst)
           (equal (car (byte-fix-list lst))
                  (logext 8 (car lst))))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

(defthm car-of-byte-fix-list-both
  (equal (car (byte-fix-list lst))
         (if (consp lst)
             (logext 8 (car lst))
           nil))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

(defthm cdr-of-byte-fix-list
  (equal (cdr (byte-fix-list lst))
         (byte-fix-list (cdr lst)))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

(defthm byte-fix-list-of-cons
  (equal (byte-fix-list (cons a b))
         (cons (logext 8 a)
               (byte-fix-list b)))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

;this didn;t seem to work when byte-fix-list was the test argument to an if during backchaining
(defthm byte-fix-list-iff
  (iff (byte-fix-list lst)
       (consp lst))
  :hints (("Goal" :in-theory (enable byte-fix-list))))

(defthm byte-fix-list-tp
  (implies (consp lst)
           (consp (byte-fix-list lst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable byte-fix-list))))



;; (defthm byte-p-list-of-byte-fix-list
;;   (byte-p-list (byte-fix-list lst))
;;   :hints (("Goal" :in-theory (enable byte-p-list byte-fix-list))))

(in-theory (disable BYTE-FIX-LIST))

;bozo move
(defthm nth-of-byte-fix-list
  (implies (and (< n (len lst))
                (natp n))
           (equal (nth n (byte-fix-list lst))
                  (logext 8 (nth n lst))))
  :hints (("Goal" :in-theory (e/d (byte-fix-list nth) (;nth-of-cdr
                                                       )))))

(defthm take-of-byte-fix-list
  (implies (and (<= n (len x))
                (natp n))
           (equal (take n (byte-fix-list x))
                  (byte-fix-list (take n x))))
  :hints (("Goal" :in-theory (e/d (take byte-fix-list BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (;TAKE-OF-CDR-BECOMES-SUBRANGE
                                   )))))

;bozo more like this for other types?
(defthm byte-fix-list-of-update-nth
  (implies (< n (len lst))
           (equal (byte-fix-list (update-nth n val lst))
                  (update-nth n (logext 8 val) (byte-fix-list lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-nth byte-fix-list
                                       len-of-cdr
                            bvchop-when-i-is-not-an-integer
                            ) (;list::update-nth-equal-rewrite
                               len
                               )))))
