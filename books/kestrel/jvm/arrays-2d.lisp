; Rules about 2D arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arrays")
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable jvm::typep)))

(defthm get-field-class-of-inner-array-2d
  (implies (and (array-refp ad  dims element-type heap)
                (eql 2 (len dims))
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad  heap))))
           (equal (get-field (nth n (get-field ad  (array-contents-pair) heap))
                             (class-pair)
                             heap)
                  (jvm::make-array-type 1 element-type)))
  :hints (("Goal" :expand ((array-refp ad dims element-type heap))
           :in-theory (enable array-refp))))

(defthm addressp-of-nth-of-array-contents
  (implies (and (array-refp ad  dims element-type heap)
                (eql 2 (len dims))
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad  heap))))
           (addressp (nth n (get-field ad (array-contents-pair) heap))))
  :hints (("Goal" :expand ((array-refp ad dims element-type heap))
           :in-theory (disable ;cons-equal-rewrite-constant-version
                       ))))

(defthm not-null-refp-of-nth-of-array-contents
  (implies (and (array-refp ad  dims element-type heap)
                (eql 2 (len dims))
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad  heap))))
           (not (null-refp (nth n (get-field ad (array-contents-pair) heap)))))
  :hints (("Goal" :expand ((array-refp ad  dims element-type heap))
           :in-theory (disable ;cons-equal-rewrite-constant-version
                       null-refp))))

;could instead have array-refp check no overlap between the array and it sub-arrays (but maybe not needed because the types differ)
;; The ads are unequal because they have different classes.  Gen?
(defthm equal-of-ad-and-nth-of-get-field-same
  (implies (and (array-refp ad dims element-type heap)
                (jvm::primitive-typep element-type)
                (equal 2 (len dims)) ;gen?
                (posp (car dims))    ;gen?
                )
           (not (equal ad (nth n (get-field ad (array-contents-pair) heap)))))
  :hints (("Goal" :use ((:instance get-field-class-when-array-refp (ad ad) (type element-type))
                        (:instance get-field-class-of-inner-array-2d (ad ad) (n (nfix n))))
           :in-theory (e/d (nth-when-<=-len)
                           (get-field-class-when-array-refp
                            get-field-class-of-inner-array-2d
                            equal-of-cons)))))

;for 2d arrays
(defthm len-of-contents-of-nth-of-array-contents
  (implies (and (array-refp ad  dims element-type heap)
                (eql 2 (len dims))
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad  heap)))) ;use (first dims) instead?
           (equal (len (get-field (nth n (get-field ad  (array-contents-pair) heap))
                                  (array-contents-pair)
                                  heap))
                  (cadr dims)))
  :hints (("Goal" :expand ((array-refp ad  dims element-type heap))
           :in-theory (disable ;cons-equal-rewrite-constant-version
                       null-refp
;                               ARRAY-ROW-RECOLLAPSE
                       ))))

(defthm elems-differ-when-array-refp
  (implies (and (array-refp ad (list dim1 dim2) type heap)
                (not (equal m n))
                (natp n)
                (< n (len (get-field ad (array-contents-pair) heap)))
                (natp m)
                (< m (len (get-field ad (array-contents-pair) heap)))
                )
           (not (equal (nth m (get-field ad (array-contents-pair) heap))
                       (nth n (get-field ad (array-contents-pair) heap)))))
  :hints (("Goal" :expand ((ARRAY-REFP AD (LIST DIM1 DIM2) TYPE HEAP)))))

;2d array
;gen
(defthm len-of-first-row-contents-when-array-refp
  (implies (and (ARRAY-REFP ad (list dim1 dim2) type HEAP)
                (not (zp dim1))
                )
           (equal (array-length (NTH '0 (GET-FIELD ad (array-contents-pair) HEAP)) HEAP)
                  dim2))
  :hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0)
           :expand ((ARRAY-REF-listP (GET-FIELD AD (array-contents-pair) HEAP)
                                     (LIST DIM2)
                                     TYPE HEAP)
                    (ARRAY-REFP AD (LIST DIM1 DIM2)
                                TYPE HEAP)))))




;this is for a 2d array
(defthm unsigned-byte-p-of-len-of-contents-of-nth-of-array-contents
  (implies (and (array-refp ad dims element-type heap)
                (eql 2 (len dims))
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad heap)))) ;use (first dims) instead?
           (unsigned-byte-p 31 (len (get-field (nth n (get-field ad (array-contents-pair) heap))
                                               (array-contents-pair)
                                               heap))))
  :hints (("Goal" :expand ((array-refp ad dims element-type heap))
           :in-theory (disable ;cons-equal-rewrite-constant-version
                       null-refp
                       ))))

(defthm 2d-array-ref-not-equal-to-one-of-its-rows
  (implies (and (array-refp ad dims element-type heap)
                (eql 2 (len dims))
                (true-listp dims)
                (posp (first dims))
                (natp n)
                (< n (len (array-contents ad heap)))) ;use (first dims) instead?
           (not (EQUAL ad
                       (NTH N
                            (GET-FIELD ad
                                       (array-contents-pair)
                                       HEAP)))))
  :hints (("Goal" :expand ((ARRAY-REFP AD DIMS ELEMENT-TYPE HEAP))
           :use ((:instance array-refp-when-memberp
                            (ad (NTH N (GET-FIELD AD (array-contents-pair) HEAP)))
                            (dims (cdr dims))
                            (ads (GET-FIELD AD (array-contents-pair) HEAP)))
                 (:instance GET-CLASS-WHEN-ARRAY-REFP (type element-type))
                 (:instance GET-CLASS-WHEN-ARRAY-REFP
                            (ad (NTH N (GET-FIELD AD (array-contents-pair) HEAP)))
                            (dims (cdr dims))
                            (type element-type)))
           :in-theory (e/d ( ;REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER
;                 refs-differ-when-classes
                            consp-of-cdr ;why?
                            not-equal-of-nth-when-not-memberp
                            ) (GET-ARRAY-DIMENSIONS-OF-REF
                            GET-CLASS-WHEN-ARRAY-REFP)))))

;we are setting a row of a 2d array
(defthm ARRAY-REFP-of-set-field-2d-when-set-row
  (implies (and (array-refp ad dims element-type heap)
                (eql 2 (len dims))
                (true-listp dims)
                (posp (first dims))
                (natp n)
                (jvm::primitive-typep element-type)
                (primitive-array-contents-okp val element-type)
                (equal (len val) (second dims))
                (true-listp val)
                (< n (len (array-contents ad heap)))) ;use (first dims) instead?
           (ARRAY-REFP ad dims element-type
                       (SET-FIELD (NTH n
                                       (GET-FIELD ad
                                                  (array-contents-pair)
                                                  heap))
                                  (array-contents-pair)
                                  val ;a bv-array
                                  heap)))
  :hints (("Goal" :in-theory (e/d (memberp-of-cons-when-constant)
                                  (2d-array-ref-not-equal-to-one-of-its-rows
                                   ;; ARRAY-REFP-OF-SET-FIELD-LEMMA
                                   EQUAL-OF-AD-AND-NTH-OF-GET-FIELD-SAME ;todo: compare this to the above
                                   jvm::primitive-typep
                                   ))
           :use (:instance 2d-array-ref-not-equal-to-one-of-its-rows)
           :expand ((:free (type) (ARRAY-REFP ad DIMS type
                                              (SET-FIELD (NTH N
                                                              (GET-FIELD ad
                                                                         (array-contents-pair)
                                                                         HEAP))
                                                         (array-contents-pair)
                                                         VAL HEAP)))
                    (:free (type) (ARRAY-REFP AD DIMS type HEAP))))))

;gen
(defthm get-field-class-of-nth-of-array-contents
  (IMPLIES (AND (array-refp ad (list dim1 dim2) ':int heap) ;gen
                (natp n)
                (< n (len (array-contents ad heap))))
           (equal (GET-FIELD (NTH N
                                  (GET-FIELD ad
                                             (array-contents-pair)
                                             HEAP))
                             (class-pair)
                             HEAP)
                  '(:array :int)))
  :hints (("Goal" :in-theory (disable ;CONS-EQUAL-REWRITE-CONSTANT-VERSION
                              )
           :expand ((ARRAY-REFP AD (LIST DIM1 DIM2) :INT HEAP)))))

;a 2d array ref cant be equal to any of its subarrays
(defthm ref-not-equal-nth-of-get-contents-when-array-refp-2d
  (IMPLIES (AND (array-refp ad (list dim1 dim2) ':int heap) ;gen
                (natp n)
                (< n (len (array-contents ad heap))))
           (not (EQUAL ad
                       (NTH N
                            (GET-FIELD ad
                                       (array-contents-pair)
                                       HEAP)))))
  :hints (("Goal" :in-theory (disable ;CONS-EQUAL-REWRITE-CONSTANT-VERSION
                              get-field-class-of-nth-of-array-contents)
           :use (:instance get-field-class-of-nth-of-array-contents)
           :expand ((ARRAY-REFP AD (LIST DIM1 DIM2) :INT HEAP)))))
