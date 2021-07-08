; Assigning types to nodes
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

(include-book "kestrel/axe/axe-types" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

;; Recognize alists that map from nodenums to axe-types.
;; TODO: Using an array might be more efficient.
(defund nodenum-type-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (let ((nodenum (car entry))
                 (type (cdr entry)))
             (and (natp nodenum)
                  (axe-typep type)
                  (nodenum-type-alistp (rest alist))))))))

(defthm nodenum-type-alistp-forward-to-eqlable-alistp
  (implies (nodenum-type-alistp alist)
           (eqlable-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable nodenum-type-alistp eqlable-alistp))))

(defthm nodenum-type-alistp-of-acons
  (equal (nodenum-type-alistp (acons key val alist))
         (and (natp key)
              (axe-typep val)
              (nodenum-type-alistp alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm axe-typep-of-cdr-of-assoc-equal-iff
  (implies (nodenum-type-alistp nodenum-type-alist)
           (iff (axe-typep (cdr (assoc-equal nodenum nodenum-type-alist)))
                (assoc-equal nodenum nodenum-type-alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp assoc-equal))))

(defthm alistp-when-nodenum-type-alistp-cheap
  (implies (nodenum-type-alistp alist)
           (alistp alist))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable alistp nodenum-type-alistp))))

;for sorting
(defund insert-pair-into-nodenum-type-alist (key val alist)
  (declare (xargs :guard (and (natp key)
                              (nodenum-type-alistp alist))
                  :verify-guards nil ;done below
                  ))
  (if (endp alist)
      (acons key val nil)
    (if (< key (caar alist))
        (acons key val alist)
      (acons (caar alist)
             (cdar alist)
             (insert-pair-into-nodenum-type-alist key val (cdr alist))))))

(defthm alistp-of-insert-pair-into-nodenum-type-alist
  (implies (alistp alist)
           (alistp (insert-pair-into-nodenum-type-alist key val alist)))
  :hints (("Goal" :in-theory (enable insert-pair-into-nodenum-type-alist))))

(verify-guards insert-pair-into-nodenum-type-alist :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm nodenum-type-alistp-of-insert-pair-into-nodenum-type-alist
  (implies (and (nodenum-type-alistp alist)
                (natp key)
                (axe-typep val))
           (nodenum-type-alistp (insert-pair-into-nodenum-type-alist key val alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp insert-pair-into-nodenum-type-alist))))

(defund sort-nodenum-type-alist (alist)
  (declare (xargs :guard (nodenum-type-alistp alist)
                  :verify-guards nil ;done below
                  ))
  (if (endp alist)
      nil
    (insert-pair-into-nodenum-type-alist (car (car alist)) (cdr (car alist)) (sort-nodenum-type-alist (cdr alist)))))

(defthm nodenum-type-alistp-of-sort-nodenum-type-alist
  (implies (nodenum-type-alistp alist)
           (nodenum-type-alistp (sort-nodenum-type-alist alist)))
  :hints (("Goal" :in-theory (enable sort-nodenum-type-alist nodenum-type-alistp))))

(verify-guards sort-nodenum-type-alist :hints (("Goal" :in-theory (enable NODENUM-TYPE-ALISTP))))

(defthm consp-of-sort-nodenum-type-alist
  (equal (consp (sort-nodenum-type-alist alist))
         (consp alist))
  :hints (("Goal" :in-theory (enable sort-nodenum-type-alist))))

(defthm rational-listp-of-strip-cars
  (implies (nodenum-type-alistp nodenum-type-alist)
           (rational-listp (strip-cars nodenum-type-alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm maxelem-of-strip-cars-of-insert-pair-into-nodenum-type-alist
  (implies (and (rationalp key)
                (rational-listp (strip-cars alist)))
           (equal (maxelem (strip-cars (insert-pair-into-nodenum-type-alist key val alist)))
                  (maxelem (cons key (strip-cars alist)))))
  :hints (("Goal" :in-theory (enable insert-pair-into-nodenum-type-alist))))

(defthm rational-listp-of-strip-cars-of-sort-nodenum-type-alist
  (implies (rational-listp (strip-cars cut-nodenum-type-alist))
           (rational-listp (strip-cars (sort-nodenum-type-alist cut-nodenum-type-alist))))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp
                                     sort-nodenum-type-alist
                                     insert-pair-into-nodenum-type-alist))))

;disable
(defthm rationalp-of-car-of-car
  (implies (rational-listp (strip-cars alist))
           (equal (rationalp (car (car alist)))
                  (consp alist))))

(defthm maxelem-of-strip-cars-of-sort-nodenum-type-alist
  (implies (rational-listp (strip-cars cut-nodenum-type-alist))
           (equal (maxelem (strip-cars (sort-nodenum-type-alist cut-nodenum-type-alist)))
                  (maxelem (strip-cars cut-nodenum-type-alist))))
  :hints (("Goal" :in-theory (enable sort-nodenum-type-alist))))
