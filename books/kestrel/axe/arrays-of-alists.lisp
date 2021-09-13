; ACL2 arrays containing alists
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

(include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system)

;; TODO: Use def-typed-acl2-array for this?
(defund array-of-alistsp (max-nodenum array-name array)
  (declare (xargs :measure (nfix (+ 1 max-nodenum))
                  :guard (and (array1p array-name array)
                              (rationalp max-nodenum)
                              (< max-nodenum (alen1 array-name array))
                              )))
  (if (not (natp max-nodenum))
      t
    (and (alistp (aref1 array-name array max-nodenum))
         (array-of-alistsp (+ -1 max-nodenum) array-name array))))

;; (defthm alistp-of-aref1-when-array-of-alistsp
;;   (implies (and (array-of-alistsp top-index-to-check array-name array)
;;                 (natp top-index-to-check)
;;                 (natp index)
;;                 (<= index top-index-to-check))
;;            (alistp (aref1 array-name array index))))


(defthm alistp-of-aref1
  (implies (and (array-of-alistsp index array-name array)
                (natp index))
           (alistp (aref1 array-name array index)))
  :hints (("Goal" :in-theory (enable array-of-alistsp))))

(defthm array-of-alistsp-monotone
  (implies (and (array-of-alistsp nodenum2 array-name array)
                (<= nodenum nodenum2)
                (natp nodenum2)
                (natp nodenum))
           (array-of-alistsp nodenum array-name array))
  :hints (("Goal" :in-theory (enable array-of-alistsp))))

(defthm array-of-alistsp-of-aset1
  (implies (and (array-of-alistsp nodenum array-name array)
                (array1p array-name array)
                (natp index)
                (natp nodenum)
                (< index (alen1 array-name array))
                (< nodenum (alen1 array-name array))
                (alistp value))
           (array-of-alistsp nodenum array-name (aset1 array-name array index value)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((array-of-alistsp 0 array-name
                                      (aset1 array-name array index value))
                    (array-of-alistsp 0 array-name
                                      (aset1 array-name array 0 value)))
           :in-theory (enable array-of-alistsp))))
