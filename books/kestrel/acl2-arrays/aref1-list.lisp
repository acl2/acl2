; A function to read from an array at several indices
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "acl2-arrays")
(local (include-book "kestrel/lists-light/reverse" :dir :system))

;read from many indices in the array
(defund aref1-list-aux (array-name array indices acc)
  (declare (xargs :guard (and (array1p array-name array)
                              (true-listp indices)
                              (all-natp indices)
                              (all-< indices (alen1 array-name array))
                              (true-listp acc))))
  (if (endp indices)
      (reverse acc)
    (aref1-list-aux array-name
                    array
                    (rest indices)
                    (cons (aref1 array-name array (first indices))
                          acc))))

(defthm len-of-aref1-list-aux
  (equal (len (aref1-list-aux array-name array indices acc))
         (+ (len indices)
            (len acc)))
  :hints (("Goal" :in-theory (enable aref1-list-aux))))

(defthm true-listp-of-aref1-list-aux
  (implies (true-listp acc)
           (true-listp (aref1-list-aux array-name array indices acc)))
  :hints (("Goal" :in-theory (enable aref1-list-aux))))

(defthmd aref1-list-aux-acc-of-append
  (implies (and (true-listp acc1)
                (true-listp acc2))
           (equal (aref1-list-aux array-name array indices (append acc1 acc2))
                  (append (reverse acc2)
                          (aref1-list-aux array-name array indices acc1))))
  :hints (("Goal" :in-theory (enable aref1-list-aux))))

(defthmd aref1-list-aux-acc-normalize-acc
  (implies (and (syntaxp (not (equal acc *nil*))) ;prevent loops
                (true-listp acc))
           (equal (aref1-list-aux array-name array indices acc)
                  (append (reverse acc)
                          (aref1-list-aux array-name array indices nil))))
  :hints (("Goal" :use (:instance aref1-list-aux-acc-of-append
                                  (acc2 acc)
                                  (acc1 nil))
           :in-theory (disable aref1-list-aux-acc-of-append))))

(defthm aref1-list-aux-of-cons
  (implies (true-listp acc)
           (equal (aref1-list-aux array-name array indices (cons val acc))
                  (append (reverse acc)
                          (list val)
                          (aref1-list-aux array-name array indices nil))))
  :hints (("Goal" :in-theory (enable aref1-list-aux-acc-normalize-acc))))

(defund aref1-list (array-name array indices)
  (declare (xargs :guard (and (array1p array-name array)
                              (true-listp indices)
                              (all-natp indices)
                              (all-< indices (alen1 array-name array)))))
  (aref1-list-aux array-name array indices nil))

(defthm len-of-aref1-list
  (equal (len (aref1-list array-name array indices))
         (len indices))
  :hints (("Goal" :in-theory (enable aref1-list))))

(defthm true-listp-of-aref1-list
  (true-listp (aref1-list array-name array indices))
  :hints (("Goal" :in-theory (enable aref1-list))))
