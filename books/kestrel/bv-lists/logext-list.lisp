; Apply logext to every element of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-signed-byte-p")
(include-book "bvchop-list")
(include-book "kestrel/bv/logext" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

(defund logext-list (size lst)
  (declare (type (integer 1 *) size)
           (xargs :guard (all-integerp lst)))
  (if (atom lst)
      nil
      (cons (logext size (car lst))
            (logext-list size (cdr lst)))))

(defthm len-of-logext-list
  (equal (len (logext-list size lst))
         (len lst))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-equal-nil-rewrite
  (equal (equal nil (logext-list size lst))
         (not (consp lst)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-equal-nil-rewrite2
  (equal (equal (logext-list size lst) nil)
         (not (consp lst)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm true-listp-of-logext-list
  (equal (true-listp (logext-list size lst))
         t)
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm all-integerp-of-logext-list
  (all-integerp (logext-list size lst))
  :hints (("Goal" :in-theory (enable all-integerp logext-list))))

;would like to drop the hyps, but I'm not sure I can
(defthm logext-list-of-bvchop-list
  (implies (and (integerp size)
                (< 0 size))
           (equal (logext-list size (bvchop-list size lst))
                  (logext-list size lst)))
  :hints (("Goal" :in-theory (enable bvchop-list logext-list))))

(defthm bvchop-list-of-logext-list
  (equal (bvchop-list size (logext-list size lst))
         (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable logext-list BVCHOP-LIST))))

(defthm bvchop-list-of-logext-list-gen
  (implies (and (integerp size)
                (<= size2 size)
                (integerp size2)
;                (<= 0 size2)
                )
           (equal (bvchop-list size2 (logext-list size lst))
                  (bvchop-list size2 lst))
  )
  :hints (("Goal" :in-theory (enable logext-list BVCHOP-LIST))))

;compare to some stuff in looptool.lisp
(defthm nth-of-logext-list
  (implies (natp i)
           (equal (nth i (logext-list esize data))
                  (if (< i (len data))
                      (logext esize (nth i data))
                      nil)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (nth logext-list) (;nth-of-cdr
                                              )))))


;; (DEFTHM NTH-OF-LOGEXT-LIST
;;   (IMPLIES (AND (NATP I) (< I (LEN DATA)))
;;            (EQUAL (NTH I (LOGEXT-LIST ESIZE DATA))
;;                   (LOGEXT ESIZE (NTH I DATA))))
;;   :HINTS
;;   (("Goal" :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
;;     :IN-THEORY (E/D (LIST::NTH-OF-CONS NTH LOGEXT-LIST)
;;                     (NTH-OF-CDR)))))

(defthm cdr-of-logext-list
  (equal (cdr (logext-list size lst))
         (logext-list size (cdr lst)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthmd logext-list-of-cdr
  (equal (logext-list size (cdr lst))
         (cdr (logext-list size lst))))

(theory-invariant (incompatible (:rewrite cdr-of-logext-list)
                                (:rewrite logext-list-of-cdr)))

(defthm take-of-logext-list
  (implies (and (<= n (len lst))
                (natp n))
           (equal (take n (logext-list size lst))
                  (logext-list size (take n lst))))
  :hints
  (("Goal" :in-theory (e/d (take logext-list) nil))))

(defthm logext-list-does-nothing
  (implies (and (all-signed-byte-p size lst)
                (< 0 size)
                (integerp size)
                (true-listp lst))
           (equal (logext-list size lst)
                  lst))
  :hints (("Goal" :in-theory (enable logext-list all-signed-byte-p))))


;move
(defthm car-of-logext-list
  (equal (CAR (LOGEXT-LIST size lst))
         (if (consp lst)
             (logext size (car lst))
           nil))
  :hints (("Goal" :in-theory (e/d (LOGEXT-LIST) (;CAR-BECOMES-NTH-OF-0 ;yuck
                                                 )))))

(defthm nth-of-logext-list-weird-case
  (implies (not (natp i))
           (equal (nth i (logext-list esize data))
                  (if (CONSP DATA)
                      (logext esize (nth i data))
                    nil)))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
    :in-theory (e/d (nth ;NTH-WHEN-N-IS-ZP
                     )
                    (;nth-of-cdr
;CAR-BECOMES-NTH-OF-0
                     )))))

(defthm nth-of-logext-list-weird-case2
  (implies (and (natp i)
                (<= (len data) i))
           (equal (nth i (logext-list esize data))
                  nil))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
    :in-theory (enable ;LIST::NTH-WITH-LARGE-INDEX-2
                ))))

(defthm nth-of-logext-list-better
  (equal (nth i (logext-list esize data))
         (if (not (natp i))
             (if (consp data)
               (logext esize (nth i data))
             nil)
           (if (< i (len data))
               (logext esize (nth i data))
             nil)))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
    :in-theory (e/d (nth ;nth-when-n-is-zp
                     )
                    (;nth-of-cdr
                     ;;car-becomes-nth-of-0
                     )))))

(defthmd not-logext-list-rewrite
  (equal (not (logext-list n x))
         (not (consp x)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm consp-of-logext-list
  (equal (consp (logext-list n x))
         (consp x))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-logext-list
  (implies (and (< 0 size)
                (integerp size))
           (equal (logext-list size (logext-list size lst))
                  (logext-list size lst)))
  :hints (("Goal" :in-theory (enable logext-list))))
