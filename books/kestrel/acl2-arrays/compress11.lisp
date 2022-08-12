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
