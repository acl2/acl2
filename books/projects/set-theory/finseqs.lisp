; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "fun-space")

(zsub finseqs (s)                  ; name, args
      fn                           ; x
      (powerset (prod2 (omega) s)) ; s
      (and (funp fn)
           (in (domain fn) (omega)))
      )

(local (defthmz in-finseqs-lemma
         (implies (and (funp fn)
                       (natp (domain fn))
                       (subset (codomain fn) a))
                  (subset fn (prod2 (omega) a)))
         :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop)
         :hints (("Goal"
                  :restrict
                  ((subset-transitivity
                    ((y (prod2 (domain fn) (codomain fn))))))))))

(local (defthm iff-implies-equal
         (implies (and (booleanp x) (booleanp y))
                  (equal (equal x y)
                         (iff x y)))))

(defthmz in-finseqs ; alternate form of finseqs$comprehension
  (equal (in fn (finseqs a))
         (and (funp fn)
              (in (domain fn) (omega))
              (subset (codomain fn) a)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))
