; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "inverse")

; Possibly useful if injective-funp is disabled:
(defthm injective-funp-forward-to-funp
  (implies (injective-funp f)
           (and (funp f)
                (funp (inverse f))))
  :rule-classes :forward-chaining)

(encapsulate ()

(local
 (defthm injective-funp-is-injective-lemma
   (implies (and (injective-funp f)
                 (in x (domain f))
                 (in y (domain f))
                 (not (equal (apply (inverse f) (apply f x))
                             (apply (inverse f) (apply f y)))))
            (not (equal (apply f x)
                        (apply f y))))
   :hints (("Goal" :in-theory nil))))

(defthmz apply-inverse-apply
  (implies (and (relation-p f)
                (funp (inverse f))
                (in x (domain f)))
           (equal (apply (inverse f) (apply f x))
                  x))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz injective-funp-is-injective
  (implies (and (injective-funp f)
                (in x (domain f))
                (in y (domain f))
                (not (equal x y)))
           (not (equal (apply f x)
                       (apply f y))))
  :props (zfc domain$prop prod2$prop inverse$prop))
)
