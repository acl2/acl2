; A formalization of 2D arrays of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "arrays-2d")
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

;length is the length that each element of lst should have (these elements are themselves "arrays")
(defund bv-arrayp-list (bytesize length lst)
  (declare (xargs :guard t))
  (if (not (consp lst))
      t
    (and (bv-arrayp bytesize length (car lst))
         (bv-arrayp-list bytesize length (cdr lst)))))

;; Test whether VAL is a 2D array of unsigned-bytes, containing NUMROWS rows
;; and NUMCOLS columns, where each entry is of width BYTESIZE.
(defund 2d-bv-arrayp (bytesize numrows numcols val)
  (declare (xargs :guard t))
  (and (bv-arrayp-list bytesize numcols val)
       (true-listp val)
       (equal numrows (len val))))

(defthm len-of-nth-when-BV-ARRAYP-LIST
  (implies (and (BV-ARRAYP-LIST BYTESIZE NUMCOLS ITEM)
                (natp n)
                (< n (len item)))
           (equal (len (nth n item))
                  numcols))
  :hints (("Goal" :in-theory (e/d (BV-ARRAYP-LIST nth) (;nth-of-cdr
                                                        )))))

(defthm len-of-nth-when-2d-bv-arrayp
  (implies (and (2d-bv-arrayp bytesize numrows numcols item)
                (natp n)
                (< n numrows))
           (equal (len (nth n item))
                  numcols))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp))))

(defthm true-listp-of-nth-when-bv-arrayp-list
  (implies (and (bv-arrayp-list bytesize numcols item)
                (natp n)
                (< n (len item)))
           (true-listp (nth n item)))
  :hints (("Goal" :in-theory (e/d (bv-arrayp-list nth) (;nth-of-cdr
                                                        )))))

(defthm true-listp-of-nth-when-2d-bv-arrayp
  (implies (and (2d-bv-arrayp bytesize numrows numcols item)
                (natp n)
                (< n numrows))
           (true-listp (nth n item)))
  :hints (("Goal" :in-theory (e/d (2d-bv-arrayp) (;bozo
                                                  ;NTH-NON-NIL-RULE
                                                  )))))

(defthm len-when-2d-bv-arrayp
  (implies (2d-bv-arrayp bytesize numrows numcols item)
           (equal (len item)
                  numrows))
  :hints (("Goal" :in-theory (e/d (2d-bv-arrayp) ()))))

(defthm true-listp-when-2d-bv-arrayp
  (implies (2d-bv-arrayp bytesize numrows numcols item)
           (true-listp item))
  :hints (("Goal" :in-theory (e/d (2d-bv-arrayp) ()))))

(defthm bv-arrayp-of-nth
  (implies (and (bv-arrayp-list bytesize len item)
                (< m (len item))
                (natp m)
                )
           (equal (bv-arrayp bytesize len (nth m item))
                  t))
  :hints (("Goal" :in-theory (e/d (bv-arrayp-list nth) (;nth-of-cdr
                                                        )))))

(defthm all-unsigned-byte-p-of-nth2
  (implies (and (bv-arrayp-list bytesize len item)
                (< m (len item))
                (natp m)
                )
           (equal (all-unsigned-byte-p bytesize (nth m item))
                  t))
  :hints (("Goal" :use (:instance bv-arrayp-of-nth)
           :in-theory (e/d (BV-ARRAYP) ( bv-arrayp-of-nth)))))

(defthm all-unsigned-byte-p-of-nth3
  (implies (and (2d-bv-arrayp bytesize numrows numcols item)
                (< m numrows)
                (natp m)
                )
           (equal (all-unsigned-byte-p bytesize (nth m item))
                  t))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp))))

(defthm unsigned-byte-p-of-array-elem-2d
  (implies (and (2d-bv-arrayp bytesize numrows numcols item)
                (natp n)
                (< m numrows)
                (natp m)
                (< n numcols))
           (unsigned-byte-p bytesize (array-elem-2d m n item)))
  :hints (("Goal" :in-theory (e/d (array-elem-2d)
                                  (;array-elem-2d-recollapse
                                   ;nth-of-array-row
                                   )))))

(defthm natp-of-array-elem-2d
  (implies (and (2d-bv-arrayp bytesize numrows numcols item)
                (natp n)
                (< m numrows)
                (natp m)
                (< n numcols))
           (natp (array-elem-2d m n item)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance unsigned-byte-p-of-array-elem-2d)
           :in-theory (disable unsigned-byte-p-of-array-elem-2d))))


(defthm bv-arrayp-list-of-cons
  (equal (bv-arrayp-list bytesize numcols (cons item items))
         (and (bv-arrayp bytesize numcols item)
              (bv-arrayp-list bytesize numcols items)))
  :hints (("Goal" :in-theory (enable bv-arrayp-list))))

(defthm 2d-bv-arrayp-of-cons
  (equal (2d-bv-arrayp bytesize numrows numcols (cons item items))
         (and (bv-arrayp bytesize numcols item)
              (2d-bv-arrayp bytesize (+ -1 numrows) numcols items)))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp))))

(defthm bv-arrayp-list-of-append
  (equal (bv-arrayp-list bytesize len (append lst1 lst2))
         (and (bv-arrayp-list bytesize len lst1)
              (bv-arrayp-list bytesize len lst2)))
  :hints (("Goal" :in-theory (enable bv-arrayp-list))))

;BOZO stuff like this follows the general pattern!
(defthm bv-arrayp-list-of-reverse
  (equal (BV-ARRAYP-LIST BYTESIZE len (REVERSE-LIST lst))
         (BV-ARRAYP-LIST BYTESIZE len lst))
  :hints (("Goal" :in-theory (enable BV-ARRAYP-LIST REVERSE-LIST))))

(defthm BV-ARRAYP-LIST-when-lst-is-not-a-cons
  (implies (not (consp lst))
           (BV-ARRAYP-LIST BYTESIZE a lst))
  :hints (("Goal" :in-theory (enable BV-ARRAYP-LIST))))

(defthm BV-ARRAYP-of-COLS-TO-ROW
  (implies (and (BV-ARRAYP-LIST BYTESIZE NUMROWS COLS)
                (< n numrows)
                (natp n))
           (BV-ARRAYP BYTESIZE (len cols) (COLS-TO-ROW N COLS)))
  :hints (("Goal" :induct t
           :in-theory (enable COLS-TO-ROW))))

(defthm BV-ARRAYP-list-of-COLS-TO-ROW-aux
  (IMPLIES (AND (BV-ARRAYP-LIST BYTESIZE NUMROWS COLS)
                (TRUE-LISTP COLS)
                (< 0 NUMROWS)
                (INTEGERP NUMROWS)
                (< n numrows)
                )
           (BV-ARRAYP-LIST BYTESIZE (LEN COLS)
                                       (COLS-TO-ARRAY-AUX n COLS)))
  :hints (("Goal" :in-theory (enable COLS-TO-ARRAY-AUX))))

(defthm BV-ARRAYP-list-of-COLS-TO-array
  (IMPLIES (AND (BV-ARRAYP-LIST BYTESIZE NUMROWS COLS)
                (TRUE-LISTP COLS)
                (< 0 NUMROWS)
                (INTEGERP NUMROWS))
           (BV-ARRAYP-LIST BYTESIZE (LEN COLS)
                                       (COLS-TO-ARRAY NUMROWS COLS)))
  :hints (("Goal" :in-theory (enable COLS-TO-ARRAY))))

(defthm 2d-bv-arrayp-of-cols-to-array
  (implies (and (2d-bv-arrayp bytesize numrows numcols cols)
                (< 0 numcols)
                (integerp numcols))
           (2d-bv-arrayp bytesize numcols numrows (cols-to-array numcols cols)))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp ))))

(defthm bv-arrayp-list-of-repeat
  (equal (bv-arrayp-list size len (repeat n item))
         (or (zp n)
             (bv-arrayp size len item)))
  :hints (("Goal" :in-theory (e/d (repeat bv-arrayp-list)
                                  (;CONS-ONTO-REPEAT
                                   )))))

(defthm bv-arrayp-list-of-take
  (implies (and (bv-arrayp-list size len x)
                (integerp n))
           (equal (bv-arrayp-list size len (take n x))
                  (if (<= n (len x))
                      t
                    (equal len 0))))
  :hints (("Goal" :in-theory (e/d (bv-arrayp-list take zp) ()))))

(defthm bv-arrayp-list-of-nthcdr
  (implies (bv-arrayp-list size len x)
           (bv-arrayp-list size len (nthcdr n x)))
  :hints (("Goal" :in-theory (e/d (bv-arrayp-list nthcdr)
                                  (nthcdr-of-cdr-combine
                                   nthcdr-of-cdr-combine-strong)))))

(defthm bv-arrayp-list-of-subrange
  (implies (and (bv-arrayp-list size len x)
                (< end (len x)) ;hyps are new
                (natp start)
                (natp end))
           (bv-arrayp-list size len (subrange start end x)))
  :hints (("Goal" :in-theory (e/d (subrange) ()))))

(defthm 2d-bv-arrayp-of-subrange
  (implies (and (2d-bv-arrayp bytesize numrows numcols val)
                (equal (+ 1 end (- start)) numrows2)
                (natp start)
                (natp end)
                (<= start end)
                (natp numrows)
                (< end numrows)
                )
           (2d-bv-arrayp bytesize numrows2 numcols (subrange start end val)))
  :hints (("Goal" :in-theory (enable 2D-BV-ARRAYP subrange))))

;; ;use something more generic
;; (defund byte-p-list-list (lst)
;;   (if (endp lst)
;;       t
;;     (and (byte-p-list (car lst))
;;          (byte-p-list-list (cdr lst)))))


;; (defthm byte-p-list-list-of-cons
;;   (equal (BYTE-P-LIST-LIST (cons item lst))
;;          (AND (BYTE-P-LIST item)
;;               (BYTE-P-LIST-LIST LST)))
;;   :hints (("Goal" :in-theory (enable BYTE-P-LIST-LIST))))

;; (DEFTHM BYTE-P-LIST-NTH-FROM-BYTE-P-LIST-list
;;   (IMPLIES (AND (BYTE-P-LIST-list LST)
;;                 (< N (LEN LST))
;;                 (<= 0 N))
;;            (byte-p-list (NTH N LST)))
;;   :HINTS (("Goal" :IN-THEORY (E/D (BYTE-P-LIST-list LEN NTH)
;;                                   (LIST::LEN-OF-CDR CONSP-WHEN-LEN-EQUAL nth-of-cdr)))))

;; ;bozo gen the byte-fix stuff to logext stuff
;; (defun byte-fix-list-list (lst)
;;   (if (endp lst)
;;       nil
;;     (cons (byte-fix-list (car lst))
;;           (byte-fix-list-list (cdr lst)))))

;; (defthm len-byte-fix-list-list
;;   (equal (len (BYTE-FIX-LIST-LIST lst))
;;          (len lst))
;;   :hints (("Goal" :in-theory (enable BYTE-FIX-LIST-LIST))))


;; (defthm byte-fix-list-list-when-byte-p-list-list
;;   (implies (byte-p-list-list lst)
;;            (equal (byte-fix-list-list lst)
;;                   (true-list-fix (true-list-fix-list lst))))
;;   :hints (("Goal" :in-theory (enable TRUE-LIST-FIX-LIST  byte-p-list-list))))

;; (defthm byte-p-list-of-cons
;;   (equal (byte-p-list (cons a lst))
;;          (and (signed-byte-p 8 a)
;;               (byte-p-list lst)))
;;   :hints (("Goal" :in-theory (enable byte-p-list))))

;; (defthm items-have-len-of-BYTE-FIX-LIST-LIST
;;   (equal (ITEMS-HAVE-LEN n (BYTE-FIX-LIST-LIST lst))
;;          (ITEMS-HAVE-LEN n lst))
;;   :hints (("Goal" :in-theory (enable BYTE-FIX-LIST-LIST ITEMS-HAVE-LEN))))

;; (defthm byte-p-list-of-true-list-fix
;;  (equal (byte-p-list (true-list-fix lst))
;;         (byte-p-list lst))
;;  :hints (("Goal" :in-theory (enable byte-p-list true-list-fix))))

;; (defthm byte-p-list-list-of-true-list-fix-list
;;  (equal (byte-p-list-list (true-list-fix-list lst))
;;         (byte-p-list-list lst))
;;  :hints (("Goal" :in-theory (enable byte-p-list-list true-list-fix-list))))


;; (defthm BYTE-P-LIST-LIST-of-BYTE-FIX-LIST-LIST
;;   (BYTE-P-LIST-LIST (BYTE-FIX-LIST-LIST lst))
;;   :hints (("Goal" :in-theory (enable BYTE-P-LIST-LIST BYTE-FIX-LIST-LIST))))

;; (defthm BYTE-P-LIST-LIST-of-update-nth
;;   (implies (and (byte-p-list val)
;;                 (natp m)
;;                 (< m (len lst))
;;                 (BYTE-P-LIST-LIST lst))
;;            (BYTE-P-LIST-LIST (update-nth m val lst)))
;;   :hints (("Goal" :in-theory (enable update-nth BYTE-P-LIST-LIST))))

(defthm bv-arrayp-of-get-column
  (implies (and (bv-arrayp-list bytesize numrows cols)
                (< n numrows)
                (natp n))
           (equal (bv-arrayp bytesize len (get-column n cols))
                  (equal len (len cols))))
  :hints (("Goal" :induct t
           :in-theory (enable get-column bv-arrayp))))

(defthm 2d-bv-arrayp-of-get-columns
  (implies (and (2d-bv-arrayp bytesize numrows numcols array)
                (natp n)
                (< n numcols)
                (integerp numcols))
           (2d-bv-arrayp bytesize (+ 1 n) numrows (get-columns n array)))
  :hints (("Goal"            :do-not '(generalize eliminate-destructors)
           :expand ((GET-COLUMNS 0 ARRAY))
           :in-theory (e/d (2d-bv-arrayp get-columns) (consp-from-len-cheap)))))

(defthm 2d-bv-arrayp-of-get-columns-special-case
  (implies (and (2d-bv-arrayp bytesize numrows numcols array)
                (equal n (+ -1 numcols)) ;so that it will match
                ;; (< n numcols)
                (posp numcols))
           (2d-bv-arrayp bytesize numcols numrows (get-columns n array)))
  :hints (("Goal" :use (:instance 2d-bv-arrayp-of-get-columns
                                  (n (+ -1 numcols)))
           :in-theory (disable 2d-bv-arrayp-of-get-columns))))

(defthm bv-arrayp-list-when-2d-bv-arrayp
  (implies (2d-bv-arrayp bytesize numrows numcols val)
           (bv-arrayp-list bytesize numcols val))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp))))

(defthm 2d-array-height-when-2d-bv-arrayp
  (implies (2d-bv-arrayp bytesize numrows numcols val)
           (equal (2d-array-height val)
                  numrows))
  :hints (("Goal" :in-theory (enable 2d-array-height))))

(defthm 2d-array-width-when-2d-bv-arrayp
  (implies (and (2d-bv-arrayp bytesize numrows numcols val)
                (posp numrows))
           (equal (2d-array-width val)
                  (nfix numcols)))
  :hints (("Goal"
           :use (:instance len-of-nth-when-bv-arrayp-list  (n 1) (item val))
           :in-theory (e/d (2d-array-width
                            2d-bv-arrayp
                            bv-arrayp)
                           (len-of-nth-when-bv-arrayp-list)))))

(defthm all-unsigned-byte-p-of-get-column
  (implies (and (2d-bv-arrayp bytesize numrows numcols val)
                (natp colno)
                (< colno numcols))
           (all-unsigned-byte-p bytesize (get-column colno val)))
  :hints (("Goal" :in-theory (enable get-column
                                     2d-bv-arrayp))))

(defthm bv-arrayp-of-get-column-2
  (implies (and (2d-bv-arrayp bytesize numrows numcols val)
                (natp colno)
                (< colno numcols))
           (equal (bv-arrayp bytesize len (get-column colno val))
                  (equal len (len val))))
  :hints (("Goal" :in-theory (enable get-column
                                     2d-bv-arrayp))))

(defthm true-list-listp-when-bv-arrayp-list
  (implies (and (bv-arrayp-list bytesize numcols val)
                (true-listp val))
           (true-list-listp val))
  :hints (("Goal" :in-theory (enable bv-arrayp-list))))

(defthm items-have-len-when-bv-arrayp-list
  (implies (bv-arrayp-list bytesize len vals)
           (items-have-len len vals))
  :hints (("Goal" :in-theory (enable bv-arrayp-list items-have-len))))

(defthm 2d-arrayp-when-2d-bv-arrayp
  (implies (2d-bv-arrayp bytesize numrows numcols val)
           (2d-arrayp val))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp
                                     2d-arrayp
                                     bv-arrayp-list))))

(defthm 2d-bv-arrayp-of-nthcdr
  (implies (and (2d-bv-arrayp bytesize numrows numcols val)
                (<= n numrows))
           (equal (2d-bv-arrayp bytesize numrows2 numcols (nthcdr n val))
                  (equal numrows2 (- numrows (nfix n)))))
  :hints (("Goal" :in-theory (enable 2d-bv-arrayp))))
