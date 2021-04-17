; Rules about mod-expt-fast when the modulus is prime
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "mod")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable mod expt)))

;; Note that books/kestrel/arithmetic-light/mod-and-expt.lisp also deals with
;; mod-and-expt but not with primality.

(defthm equal-of-0-and-mod-expt-fast-when-primep
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (equal 0 (acl2::mod-expt-fast a i n))
                  (and (not (equal 0 i)) ;odd case where we get 1
                       (equal 0 (mod a n)))))
  :hints (("Goal" :cases ((equal 0 (mod a n))
                          (< 0 (mod a n))))))

(defthm <-of-0-and-mod-expt-fast-when-primep
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (< 0 (acl2::mod-expt-fast a i n))
                  (or (equal 0 i) ;odd case where we get 1
                      (< 0 (mod a n)))))
  :hints (("Goal" :cases ((equal 0 (mod a n))
                          (< 0 (mod a n))))))
