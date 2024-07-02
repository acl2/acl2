; A lightweight book about the built-in function compress1
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")
(local (include-book "compress11"))
(local (include-book "bounded-integer-alistp"))
(local (include-book "default"))
(local (include-book "dimensions"))
(local (include-book "header"))
(local (include-book "array1p"))
(local (include-book "aref1"))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(in-theory (disable compress1))

(local (in-theory (enable normalize-header-name
                          normalize-compress11-name
                          normalize-default-name
                          normalize-dimensions-name
                          normalize-alen1-name
                          normalize-array1p-name)))

(local
  (defthm alistp-of-reverse-list
    (equal (alistp (reverse-list x))
           (alistp (true-list-fix x)))
    :hints (("Goal" :in-theory (enable alistp reverse-list)))))

(local
  (defthm bounded-integer-alistp-of-reverse-list
    (equal (bounded-integer-alistp (reverse-list x) n)
           (bounded-integer-alistp (true-list-fix x) n))
    :hints (("Goal" :in-theory (enable alistp reverse-list)))))

(local
  (defthm strip-cars-of-reverse-list
    (equal (strip-cars (reverse-list alist))
           (reverse-list (strip-cars alist)))
    :hints (("Goal" :in-theory (enable reverse-list)))))

(local
  (defthm assoc-equal-of-reverse-list
    (implies (and (no-duplicatesp (strip-cars alist))
                  (alistp alist))
             (equal (assoc-equal key (reverse-list alist))
                    (assoc-equal key alist)))
    :hints (("Goal" :in-theory (enable assoc-equal
                                       reverse-list
                                       no-duplicatesp
                                       assoc-equal-iff-member-equal-of-strip-cars)))))

;todo: make local?
(defthm equal-of-assoc-equal-same
  (implies key
           (iff (equal key (car (assoc-equal key array)))
                (assoc-equal key array)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm header-of-compress1
  (equal (header array-name (compress1 array-name2 array))
         (header array-name array))
  :hints (("Goal" :in-theory (enable compress1 compress11 header))))

(defthm maximum-length-of-compress1
  (equal (maximum-length array-name (compress1 array-name2 array))
         (maximum-length array-name array))
  :hints (("Goal" :in-theory (enable compress1 compress11 maximum-length header))))

(defthm dimensions-of-compress1
  (equal (dimensions array-name (compress1 array-name2 array))
         (dimensions array-name array))
  :hints (("Goal" :in-theory (enable compress1 dimensions-intro header-intro))))

;odd rhs
(defthm default-of-compress1
  (equal (default name (compress1 name2 l))
         (if (or (equal (array-order (header name2 l)) '<)
                 (equal (array-order (header name2 l)) '>))
             (default name2 l)
           (default name l)))
  :hints (("Goal" :in-theory (e/d (compress1 default
                                             ;compress11 ;todo

                                             )
                                  (array-order default-intro)))))

(defthm alistp-of-compress1
  (implies (and (alistp array)
                (consp (header array-name array)) ;why?
                )
           (alistp (compress1 array-name array)))
  :hints (("Goal" :in-theory (enable compress1))))

(defthm bounded-integer-alistp-of-compress1
  (implies (and (bounded-integer-alistp array n)
                (natp n) ;drop?
                )
           (iff (bounded-integer-alistp (compress1 array-name array) n)
                (header array-name array)                 ;why?
                ))
  :hints (("Goal" :in-theory (enable compress1 ;bounded-integer-alistp
                                     ))))

(defthm array1p-of-compress1
  (implies (array1p array-name l)
           (array1p array-name (compress1 array-name2 l)))
  :hints (("Goal" :in-theory (enable array1p compress1 header))))

(defthmd normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress1))))

(defthm assoc-equal-of-compress1
  (implies (and (natp index)
                ;; (< index (car (dimensions name l)))
                (array1p :fake-name l) ;name is mostly irrel here?
                ;; (integerp (car (dimensions name l)))
                )
           (equal (assoc-equal index (compress1 name l))
                  (if (and (equal (cdr (assoc-equal index l))
                                  (default name l))
                           (or (equal (array-order (assoc-equal :header l)) '>)
                               (equal (array-order (assoc-equal :header l)) '<)))
                      ;;if it's equal to the default and we are sorting, then it gets removed
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (ARRAY1P
                            compress1
                            header-intro
                            not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
                            dimensions-intro)
                           (ASSOC-EQUAL header)))))


(local
  (defthm assoc-equal-of-reverse-list-iff
    (implies (or (alistp x)
                 key)
             (iff (assoc-equal key (reverse-list x))
                  (assoc-equal key x)))
    :hints (("Goal" :in-theory (enable reverse-list)))))

;; This one does not require array1p
(defthm assoc-equal-of-compress1-when-<
  (implies (and (natp index)
                (< index (car (dimensions name l)))
                (alistp l)
                (integerp (car (dimensions name l))))
           (equal (assoc-equal index (compress1 name l))
                  (if (and (equal (cdr (assoc-equal index l))
                                  (default name l))
                           (or (equal (array-order (assoc-equal :header l)) '>)
                               (equal (array-order (assoc-equal :header l)) '<)))
                      ;;if it's equal to the default and we are sorting, then it gets removed
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (compress1 ;array1p-rewrite2
                                      header
                                      not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
                                      )
                           (ASSOC-EQUAL array1p)))))

(defthm assoc-equal-of-header-of-compress1
  (equal (assoc-equal :header (compress1 name l))
         (header name l))
  :hints (("Goal" :in-theory (enable compress1 header-intro))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm aref1-of-compress1-small
   (implies (and (< n (alen1 array-name array))
                 (natp n)
                 ;;(array1p array-name array)
                 (alistp array)
                 (integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name2 array) n)
                   (aref1 array-name array n)))
   :hints (("Goal" :in-theory (e/d (aref1 dimensions-intro) ())))))

(local
 (defthm aref1-of-compress1-too-large
   (implies (and (<= (alen1 array-name array) n)
                 (natp n)
                 (array1p array-name array) ; drop?
                 (alistp array)
                 ;;(integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name2 array) n)
                   (default array-name array)))
   :hints (("Goal" :in-theory (e/d (aref1-when-too-large)
                                   (array1p))))))

(defthm aref1-of-compress1
  (implies (and (natp n)
                (array1p array-name array))
           (equal (aref1 array-name (compress1 array-name2 array) n)
                  (if (< n (alen1 array-name array))
                      (aref1 array-name array n)
                    (default array-name array))))
  :hints (("Goal" :in-theory (enable aref1-when-too-large))))
