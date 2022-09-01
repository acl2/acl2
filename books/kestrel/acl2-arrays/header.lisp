; A lightweight book about the built-in function header
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable header))

;; Unfortunately, this has a free variable in the RHS.
(defthmd header-intro
  (equal (assoc-equal :header l)
         (header name l))
  :hints (("Goal" :in-theory (enable header))))

(theory-invariant (incompatible (:rewrite header-intro) (:definition header)))

(defthm header-when-array1p
  (implies (array1p name2 l)
           (header name l))
  :hints (("Goal" :in-theory (enable array1p header))))

(defthm consp-of-header-when-array1p-free
  (implies (array1p name2 l) ; name2 is a free var
           (consp (header name l)))
  :hints (("Goal" :in-theory (enable array1p header))))

(defthm consp-of-header-when-array1p
  (implies (array1p name array)
           (consp (header name array)))
  :hints (("Goal" :in-theory (enable array1p header))))

(defthmd keyword-value-listp-of-cdr-of-header-when-array1p
  (implies (array1p array-name array)
           (keyword-value-listp (cdr (header array-name array))))
  :hints (("Goal" :in-theory (enable array1p header))))

(defthm equal-of-header-and-car-of-header
  (iff (equal :header (car (header array-name array)))
       (header array-name array))
  :hints (("Goal" :in-theory (enable header))))

(defthm header-of-cons
  (equal (header array-name (cons entry alist))
         (if (eq :header (car entry))
             entry
           (header array-name alist)))
  :hints (("Goal" :in-theory (enable header))))

(defthm header-of-nil
  (equal (header name nil)
         nil)
  :hints (("Goal" :in-theory (enable header))))
