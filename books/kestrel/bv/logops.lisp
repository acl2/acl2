; Rules mixing more than one of the logops
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lognot")
(include-book "logext")
(local (include-book "rules")) ;todo: reduce
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(defthmd lognot-of-logext
  (implies (posp size)
           (equal (lognot (logext size x))
                  (logext size (lognot x))))
  :hints (("Goal" :in-theory (enable lognot logext-of-plus
                                     logext-cases
                                     expt-of-+))))

(defthm logext-of-lognot
  (implies (posp size)
           (equal (logext size (lognot x))
                  (lognot (logext size x))))
  :hints (("Goal" :in-theory (enable lognot-of-logext))))

(theory-invariant (incompatible (:rewrite lognot-of-logext)
                                (:rewrite logext-of-lognot)))
