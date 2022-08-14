; A lightweight book about the built-in function compress1
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

(local (include-book "compress11"))
(local (include-book "bounded-integer-alistp"))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(in-theory (disable compress1))

(local (in-theory (disable default)))

;todo: make local?
(defthm equal-of-assoc-equal-same
  (implies key
           (iff (equal key (car (assoc-equal key array)))
                (assoc-equal key array)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm header-of-compress1
  (equal (header array-name (compress1 array-name array))
         (header array-name array))
  :hints (("Goal" :in-theory (enable compress1 compress11 dimensions header))))

(defthm maximum-length-of-compress1
  (equal (maximum-length array-name (compress1 array-name array))
         (maximum-length array-name array))
  :hints (("Goal" :in-theory (enable compress1 compress11 maximum-length header))))

(defthm dimensions-of-compress1
  (equal (dimensions array-name (compress1 array-name array))
         (dimensions array-name array))
  :hints (("Goal" :in-theory (enable dimensions))))

;odd rhs
(defthm default-of-compress1
  (equal (default name (compress1 name2 l))
         (if (or (equal (array-order (header name2 l)) '<)
                 (equal (array-order (header name2 l)) '>))
             (default name2 l)
           (default name l)))
  :hints (("Goal" :in-theory (e/d (compress1 default
                                             compress11 ;todo
                                             )
                                  (array-order)))))

(defthm alistp-of-compress1
  (implies (and (alistp array)
                (consp (header array-name array)) ;why?
                )
           (alistp (compress1 array-name array)))
  :hints (("Goal" :in-theory (enable compress1))))

(defthm bounded-integer-alistp-of-compress1
  (implies (and (bounded-integer-alistp array n)
                (natp n) ;drop?
                )
           (iff (bounded-integer-alistp (compress1 array-name array) n)
                (header array-name array)                 ;why?
                ))
  :hints (("Goal" :in-theory (enable compress1 ;bounded-integer-alistp
                                     ))))

(defthm array1p-of-compress1
  (implies (array1p array-name l)
           (array1p array-name (compress1 array-name l)))
  :hints (("Goal" :in-theory (enable array1p compress1 header))))
