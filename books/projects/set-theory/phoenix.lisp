; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; We define the 3-fold composition phoenix(g,f1,f2) = g(<f1(x),f2(x)>), where
; the name "Phoenix" may be found in https://combinatorylogic.com/table.html.
; The operator here is really a sort of uncurried version.

(in-package "ZF")

(include-book "base")
(include-book "image-plus")

(zsub phoenix (g f1 f2)
      p                              ; x
      (prod2 (domain f1) (image+ g)) ; s
      (equal (cdr p)                 ; u
             (apply g
                    (cons (apply f1 (car p))
                          (apply f2 (car p))))))

(defthmz relation-p-phoenix
  (relation-p (phoenix g f1 f2))
  :hints (("Goal" :in-theory (enable relation-p)))
  :props (zfc phoenix$prop prod2$prop))

(defthmz funp-phoenix
  (funp (phoenix g f1 f2))
  :hints (("Goal" :in-theory (enable funp)))
  :props (zfc phoenix$prop prod2$prop))

(defthmz domain-phoenix-1-1
  (implies (in x (domain (phoenix g f1 f2)))
           (in x (domain f1)))
  :hints (("Goal" :in-theory (e/d (domain$comprehension)
                                  (in-cons-apply))))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))

(defthmz domain-phoenix-1
  (subset (domain (phoenix g f1 f2))
          (domain f1))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))

(local (defthmz domain-phoenix-2-1-1
         (implies (in x (domain f1))
                  (in (cons x
                            (apply g
                                   (cons (apply f1 x)
                                         (apply f2 x))))
                      (phoenix g f1 f2)))
         :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop)
         :rule-classes nil))

(defthmz domain-phoenix-2-1
  (implies (in x (domain f1))
           (in x (domain (phoenix g f1 f2))))
  :hints (("Goal"
           :use domain-phoenix-2-1-1
           :in-theory (disable phoenix$comprehension)))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))

(defthmz domain-phoenix-2
  (subset (domain f1)
          (domain (phoenix g f1 f2)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))

(defthmz domain-phoenix
  (equal (domain (phoenix g f1 f2))
         (domain f1))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))

(defthmz apply-phoenix
  (implies (in x (domain f1))
           (equal (apply (phoenix g f1 f2) x)
                  (apply g
                         (cons (apply f1 x)
                               (apply f2 x)))))
  :props (zfc phoenix$prop prod2$prop domain$prop inverse$prop))
