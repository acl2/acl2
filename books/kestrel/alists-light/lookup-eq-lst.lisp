; Look up a list of keys, using LOOKUP-EQ.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-eq")

(defund lookup-eq-lst (keys alist)
  (declare (xargs :guard (if (symbol-listp keys)
                             (alistp alist)
                           (symbol-alistp alist))))
  (if (atom keys)
      nil
    (cons (lookup-eq (car keys) alist)
          (lookup-eq-lst (cdr keys) alist))))

(defthm len-of-lookup-eq-lst
  (equal (len (lookup-eq-lst keys alist))
         (len keys))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))

(defthm cdr-of-lookup-eq-lst
  (equal (cdr (lookup-eq-lst keys alist))
         (lookup-eq-lst (cdr keys) alist))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))

(defthm car-of-lookup-eq-lst
  (implies (consp keys)
           (equal (car (lookup-eq-lst keys alist))
                  (lookup-eq (car keys) alist)))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))

(defthm lookup-eq-lst-of-append
  (equal (lookup-eq-lst (append keys1 keys2) alist)
         (append (lookup-eq-lst keys1 alist)
                 (lookup-eq-lst keys2 alist)))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))

(defthm lookup-eq-lst-when-not-consp
  (implies (not (consp keys))
           (equal (lookup-eq-lst keys alist)
                  nil))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))

(defthm consp-of-lookup-eq-lst
  (equal (consp (lookup-eq-lst keys alist))
         (consp keys))
  :hints (("Goal" :in-theory (enable lookup-eq-lst))))
