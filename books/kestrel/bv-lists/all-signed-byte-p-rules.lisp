; Rules about all-signed-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: perhaps move this to typed-lists-light

(include-book "all-signed-byte-p")
(include-book "all-unsigned-byte-p")
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(local (include-book "kestrel/bv/signed-byte-p" :dir :system))

(defthmd all-integerp-when-all-signed-byte-p
  (implies (all-signed-byte-p free x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-signed-byte-p all-integerp))))

(defthm all-signed-byte-p-of-myif
  (implies (and (all-signed-byte-p n a)
                (all-signed-byte-p n b))
           (all-signed-byte-p n (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm all-signed-byte-p-of-myif-strong
  (equal (all-signed-byte-p n (myif test a b))
         (myif test (all-signed-byte-p n a)
               (all-signed-byte-p n b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm all-signed-byte-p-when-all-unsigned-byte-p
  (implies (and (all-unsigned-byte-p n x)
                (natp n)
                (< 0 n))
           (equal (all-signed-byte-p n x)
                  (all-unsigned-byte-p (+ -1 n) x)))
  :hints (("Goal" :in-theory (e/d (all-signed-byte-p all-unsigned-byte-p)
                                  (signed-byte-p)))))
