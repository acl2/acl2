; A variant of ACONS that can keep the alist smaller
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Like ACONS but this one won't introduce a duplicate key.  This is slower
;; than ACONS but can keep the alist from growing very large.  Preserves the
;; order of the keys in the alist when KEY already exists among them.
(defund acons-unique (key val alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      (cons (cons key val) nil)
    (let ((entry (car alist)))
      (if (equal key (car entry)) ;we found the binding
          (cons (cons key val) (cdr alist))
        (cons entry (acons-unique key val (cdr alist)))))))

(defthm alistp-of-acons-unique
  (implies (alistp alist)
           (alistp (acons-unique key val alist)))
  :hints (("Goal" :in-theory (enable acons-unique))))

(defthmd not-member-equal-of-strip-cars-of-acons-unique
  (implies (and (not (member-equal key1 (strip-cars alist)))
                (not (equal key1 key2)))
           (not (member-equal key1 (strip-cars (acons-unique key2 val alist)))))
  :hints (("Goal" :in-theory (enable acons-unique))))

(defthmd no-duplicatesp-equal-of-strip-cars-of-acons-unique
  (implies (no-duplicatesp-equal (strip-cars alist))
           (no-duplicatesp-equal (strip-cars (acons-unique key val alist))))
  :hints (("Goal" :in-theory (enable acons-unique
                                     not-member-equal-of-strip-cars-of-acons-unique))))
