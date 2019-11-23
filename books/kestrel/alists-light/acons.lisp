; A lightweight book about the built-in function acons.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable acons))

(defthm alistp-of-acons
  (equal (alistp (acons key datum alist))
         (alistp alist))
  :hints (("Goal" :in-theory (enable acons))))

(defthm car-of-acons
  (equal (car (acons key datum alist))
         (cons key datum))
  :hints (("Goal" :in-theory (enable acons))))

(defthm cdr-of-acons
  (equal (cdr (acons key datum alist))
         alist)
  :hints (("Goal" :in-theory (enable acons))))

(defthm strip-cars-of-acons
  (equal (strip-cars (acons key datum alist))
         (cons key (strip-cars alist)))
  :hints (("Goal" :in-theory (enable acons))))

(defthm strip-cdrs-of-acons
  (equal (strip-cdrs (acons key datum alist))
         (cons datum (strip-cdrs alist)))
  :hints (("Goal" :in-theory (enable acons))))

(defthm len-of-acons
  (equal (len (acons key datum alist))
         (+ 1 (len alist)))
  :hints (("Goal" :in-theory (enable acons))))

(defthm equal-of-acons-and-acons
  (equal (equal (acons key1 datum1 alist1)
                (acons key2 datum2 alist2))
         (and (equal key1 key2)
              (equal datum1 datum2)
              (equal alist1 alist2)))
  :hints (("Goal" :in-theory (enable acons))))

(defthm true-listp-of-acons
  (equal (true-listp (acons key datum alist))
         (true-listp alist))
  :hints (("Goal" :in-theory (enable acons))))
