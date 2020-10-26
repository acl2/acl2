; A function to write a value to an array at several indices
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
(include-book "acl2-arrays")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)

;set many indices to the same value
(defund aset1-list (array-name array indices value)
  (declare (xargs :guard (and (array1p array-name array)
                              (true-listp indices)
                              (all-natp indices)
                              (all-< indices (alen1 array-name array)))))
  (if (endp indices)
      array
    (aset1-list array-name
                (aset1 array-name array (car indices) value)
                (cdr indices)
                value)))

(defthm alen1-of-aset1-list
  (implies (all-natp nodenums)
           (equal (alen1 array-name (aset1-list array-name array nodenums value))
                  (alen1 array-name array)))
  :hints (("Goal" :in-theory (enable aset1-list))))

(defthm array1p-of-aset1-list
  (implies (and (all-natp nodenums)
                (all-< nodenums (alen1 array-name array))
                (array1p array-name array))
           (array1p array-name (aset1-list array-name array nodenums value)))
  :hints (("Goal" :in-theory (enable aset1-list))))

;; ;; Not tail recursive but easier to reason about
;; (defund aset1-list-alt (array-name array indices value)
;;   (declare (xargs :guard (and (array1p array-name array)
;;                               (true-listp indices)
;;                               (all-natp indices)
;;                               (all-< indices (alen1 array-name array)))
;;                   :verify-guards nil
;;                   ))
;;   (if (endp indices)
;;       array
;;     (aset1 array-name
;;            (aset1-list-alt array-name
;;                            array
;;                            (cdr indices)
;;                            value)
;;            (car indices)
;;            value)))

;; (defthm alen1-of-aset1-list-alt
;;   (implies (and (all-natp nodenums)
;;                 (all-< nodenums (alen1 array-name array))
;;                 (array1p array-name array))
;;            (equal (alen1 array-name (aset1-list-alt array-name array nodenums value))
;;                   (alen1 array-name array)))
;;   :hints (("Goal" :in-theory (enable aset1-list-alt))))

;; (defthm array1p-of-aset1-list-alt
;;   (implies (and (all-natp nodenums)
;;                 (all-< nodenums (alen1 array-name array))
;;                 (array1p array-name array))
;;            (array1p array-name (aset1-list-alt array-name array nodenums value)))
;;   :hints (("Goal" :in-theory (enable aset1-list-alt))))

;; (defthm aref1-of-aset1-list-alt
;;   (implies (and (array1p array-name array)
;;                 (all-natp indices)
;;                 (all-< indices (alen1 array-name array))
;;                 (natp index)
;;                 (< index (alen1 array-name array)))
;;            (equal (aref1 array-name (aset1-list-alt array-name array indices value) index)
;;                   (if (member-equal index indices)
;;                       value
;;                     (aref1 array-name array index))))
;;   :hints (("Goal" :in-theory (enable aset1-list-alt))))

;; we still get value if we write more values into the array
(defthm aref1-of-aset1-list-when-equal-of-aref1
  (implies (and (equal (aref1 array-name array index) value)
                (array1p array-name array)
                (all-natp indices)
                (all-< indices (alen1 array-name array))
                (natp index)
                (< index (alen1 array-name array))
                )
           (equal (aref1 array-name (aset1-list array-name array indices value) index)
                  value))
    :hints (("Goal" :in-theory (enable aset1-list))))

;; (defthm aref1-of-aset1-list-of-aset1-irrel
;;   (implies (and (not (equal index read-index)) ;this case
;;                 (array1p array-name array)
;;                 (all-natp indices)
;;                 (all-< indices (alen1 array-name array))
;;                 (natp index)
;;                 (< index (alen1 array-name array))
;;                 (natp read-index)
;;                 (< read-index (alen1 array-name array))
;;                 )
;;            (equal (aref1 array-name (aset1-list array-name (aset1 array-name array index value) indices value) read-index)
;;                   (aref1 array-name (aset1-list array-name array indices value) read-index)))
;;   :hints (("Goal" :in-theory (e/d (aset1-list) ((:i MEMBER-EQUAL))))))


;; ;; The two versions are equal wrt aref1
;; (thm
;;  (implies (and (array1p array-name array)
;;                (all-natp indices)
;;                (all-< indices (alen1 array-name array))
;;                (natp read-index)
;;                (< read-index (alen1 array-name array)))
;;           (equal (aref1 array-name (aset1-list-alt array-name array indices value) read-index)
;;                  (aref1 array-name (aset1-list array-name array indices value) read-index)))
;;  :hints (("Goal" :expand ((aset1-list array-name array indices value))
;;           :in-theory (enable aset1-list aset1-list-alt))))

;; (defthm aref1-of-aset1-list-of-aset1
;;   (implies (and (array1p array-name array)
;;                 (all-natp indices)
;;                 (all-< indices (alen1 array-name array))
;;                 (natp index)
;;                 (< index (alen1 array-name array))
;;                 (natp read-index)
;;                 (< read-index (alen1 array-name array))
;;                 )
;;            (equal (aref1 array-name (aset1-list array-name (aset1 array-name array index value) indices value) read-index)
;;                   (if (member-equal index indices)
;;                       (aref1 array-name (aset1-list array-name array indices value) read-index)
;;                     (aref1 array-name (aset1 array-name (aset1-list array-name array indices value) index value) read-index))))
;;   :hints (("Goal" :in-theory (e/d (aset1-list) ((:i MEMBER-EQUAL))))))

(defthm aref1-of-aset1-list
  (implies (and (array1p array-name array)
                (all-natp indices)
                (all-< indices (alen1 array-name array))
                (natp index)
                (< index (alen1 array-name array)))
           (equal (aref1 array-name (aset1-list array-name array indices value) index)
                  (if (member-equal index indices)
                      value
                    (aref1 array-name array index))))
  :hints (("Goal" :in-theory (enable aset1-list))))
