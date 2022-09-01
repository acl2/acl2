; A lightweight book about the built-in function compress11
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

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "bounded-integer-alistp"))

(in-theory (disable compress11))

(local
 (defthm not-equal-of-car-of-assoc-equal
   (implies (and (not (equal val key))
                 val)
            (not (equal val (car (assoc-equal key array)))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(defthm assoc-equal-of-header-and-compress11
  (implies (and (integerp i)
                (integerp n))
           (equal (assoc-equal :header (compress11 name l i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm header-of-compress11
  (implies (integerp i)
           (equal (header name (compress11 name2 array i n default))
                 nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm default-of-compress11
  (implies (integerp i)
           (equal (default name (compress11 name2 array i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm alistp-of-compress11
  (implies (alistp array)
           (alistp (compress11 name array i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm assoc-equal-of-compress11-when-too-small
  (implies (< index i)
           (equal (assoc-equal index (compress11 name l i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm bounded-integer-alistp-of-compress11
  (implies (and (bounded-integer-alistp array n)
                (natp n))
           (bounded-integer-alistp (compress11 name array i index default) n))
  :hints (("Goal" :in-theory (e/d (compress11 bounded-integer-alistp
                                              assoc-equal-forward-when-bounded-integer-alistp)
                                  (
                                   car-of-assoc-equal-cheap)))))


(local
 (defthmd assoc-equal-of-compress11
  (implies (and (<= i index)
                (< index n)
                (integerp i)
                (integerp index)
                (integerp n)
                )
           (equal (assoc-equal index (compress11 name l i n default))
                  (if (equal default (cdr (assoc-equal index l)))
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable compress11)))))

(local
 (defthmd assoc-equal-of-compress11-too-high
  (implies (and (<= n index) ;this case
                (<= i index)
                (integerp i)
                (integerp index)
                (integerp n)
                )
           (equal (assoc-equal index (compress11 name l i n default))
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable compress11)))))

(defthm assoc-equal-of-compress11-both
  (implies (and (integerp i)
                (integerp index)
                (integerp n))
           (equal (assoc-equal index (compress11 name l i n default))
                  (if (or (< index i)
                          (<= n index))
                      nil
                    (if (equal default (cdr (assoc-equal index l)))
                        nil
                      (assoc-equal index l)))))
  :hints (("Goal" :use (assoc-equal-of-compress11-too-high
                        (:instance assoc-equal-of-compress11))
           :in-theory (e/d ()
                           (assoc-equal)))))
