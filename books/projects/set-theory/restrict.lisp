; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "projects/set-theory/set-algebra" :dir :system)

; We introduce (restrict f s), sometimes denoted f|s.
(zsub restrict (f s) ; name, args
      p              ; x
      f              ; s
      (in (car p) s) ; u
      )

(defthmz relation-p-restrict
  (implies (relation-p f)
           (relation-p (restrict f s)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((relation-p (restrict f s))))))

(defthmz funp-restrict
  (implies (funp f)
           (funp (restrict f s)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((funp (restrict f s))))))

(defthmz domain-restrict-1
  (implies (in x (domain (restrict f s)))
           (in x (domain f)))
  :hints (("Goal" :in-theory (enable in-domain-rewrite)))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict-2
  (implies (in x (domain (restrict f s)))
           (in x s))
  :hints (("Goal" :in-theory (enable in-domain-rewrite)))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict-3
  (implies (and (in x (domain f))
                (in x s))
           (in x (domain (restrict f s))))
  :hints (("Goal"
           :restrict ((in-car-domain-alt
                       ((p (cons x (apply f x))))))
           :in-theory (enable in-domain-rewrite)))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict
  (equal (domain (restrict f s))
         (int2 (domain f) s))
  :props (zfc restrict$prop domain$prop diff$prop)
  :hints (("Goal"
           :in-theory (enable extensionality-rewrite subset))))

(defthmz apply-restrict
  (implies (and (funp f)
                (force (subset x (domain f)))
                (force (in a x)))
           (equal (apply (restrict f x) a)
                  (apply f a)))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal" :in-theory (enable apply-intro))))
