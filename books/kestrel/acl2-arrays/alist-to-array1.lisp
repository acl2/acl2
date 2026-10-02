; A function to turn an alist into an array
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alist-to-array1-with-len")
(include-book "new-array1")
(local (include-book "array1p"))
(local (include-book "default"))
(local (include-book "dimensions"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;Consider adding an option to reuse an existing array if large enough (well, compress1 now does that internally)?
; The length of the resulting array is one more than the max key in the alist, unless the alist is empty, in which case the length is 1.
; TODO: Add an option for slack space (well, see alist-to-array1-with-len).
;; NOTE: If the len is known, calling alist-to-array1-with-len will be faster, since that avoids the call to max-key.
(defund alist-to-array1 (name alist)
  (declare (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist *max-1d-array-length*))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite))))
           (type symbol name))
  (let* ((len (if (consp alist)
                  ;; normal case:
                  (+ 1 (max-key alist 0)) ;todo: could save this max if we know it's decreasing (like a dag)
                ;; compress1 must be given a dimension of at least 1
                1)))
    (alist-to-array1-with-len name alist len)))

(in-theory (disable (:e alist-to-array1))) ;might blow up

(defthm array1p-of-alist-to-array1
  (implies (and (bounded-natp-alistp alist *max-1d-array-length*)
                (true-listp alist)
                ;alist
                (symbolp name)
                )
           (array1p name (alist-to-array1 name alist)))
  :hints (("Goal" :in-theory (e/d (array1p compress1 alist-to-array1) (normalize-array1p-name)))))

(defthm default-of-alist-to-array1
  (equal (default name1 (alist-to-array1 name2 alist))
         nil)
  :hints (("Goal" :in-theory (enable alist-to-array1))))

(defthm dimensions-of-alist-to-array1
  (equal (dimensions name1 (alist-to-array1 name2 alist))
         (if (consp alist)
             (list (+ 1 (max-key alist 0)))
           (list 1)))
  :hints (("Goal" :in-theory (enable alist-to-array1))))

(defthm alen1-of-alist-to-array1
  (equal (alen1 name1 (alist-to-array1 name2 alist))
         (if (consp alist)
             (+ 1 (max-key alist 0))
           1))
  :hints (("Goal" :in-theory (enable alist-to-array1))))

(defthm aref1-of-alist-to-array1
  (implies (and (bounded-natp-alistp alist *max-1d-array-length*)
                (true-listp alist)
                alist
                (symbolp name1)
                (natp index)
                (<= index (max-key alist 0)))
           (equal (aref1 name1 (alist-to-array1 name2 alist) index)
                  (cdr (assoc-equal index alist))))
  :hints (("Goal" :in-theory (enable alist-to-array1))))

(defthm alist-to-array1-of-nil
  (equal (alist-to-array1 name nil)
         (new-array1 name 1))
  :hints (("Goal" :in-theory (enable alist-to-array1 ALIST-TO-ARRAY1-WITH-LEN NEW-ARRAY1 NEW-ARRAY1-WITH-DEFAULT))))
