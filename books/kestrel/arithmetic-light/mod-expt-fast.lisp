; A book that adds a theorem about mod-expt-fast.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../../arithmetic-3/floor-mod/mod-expt-fast")
(local (include-book "mod"))
(local (include-book "expt"))

;; Note that there is also an (incompatible) version of mod-expt-fast in
;; books/arithmetic-5/lib/floor-mod/mod-expt-fast.lisp.  It is not clear which
;; one is better.

(defthm integerp-of-mod-expt-fast
  (implies (and (integerp a)
                (natp i)
                (integerp n))
           (integerp (acl2::mod-expt-fast a i n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable acl2::mod-expt-fast))))

;; Other variants may be possible
(defthm <=-of-0-and-mod-expt-fast
  (implies (and (<= 0 a)
                (rationalp a)
                (<= 0 n)
                (rationalp n))
           (<= 0 (acl2::mod-expt-fast a i n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :cases ((equal 0 n))
           :in-theory (enable acl2::mod-expt-fast))))
