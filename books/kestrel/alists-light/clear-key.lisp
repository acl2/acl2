; Clearing a key in an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund clear-key (key alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil ; or return alist here, to support fast-alists, which can end in a size or name
    (if (equal key (caar alist))
        (clear-key key (cdr alist))
      (cons (car alist)
            (clear-key key (cdr alist))))))

(defthm alistp-of-clear-key
  (implies (alistp alist)
           (alistp (clear-key key alist)))
  :hints (("Goal" :in-theory (enable clear-key))))

(defthm len-of-clear-key-linear
  (<= (len (clear-key key alist))
      (len alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable clear-key))))

(defthm true-listp-of-clear-key-type
  (implies (true-listp alist)
           (true-listp (clear-key key alist)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable clear-key))))

(defthm clear-key-when-not-member-equal-of-strip-cars
  (implies (not (member-equal key (strip-cars alist)))
           (equal (clear-key key alist)
                  (true-list-fix alist)))
  :hints (("Goal" :in-theory (enable clear-key))))
