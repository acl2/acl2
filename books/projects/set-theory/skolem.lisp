; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; The following book includes the rule domain-skolem-1, which is necessary for
; the proof of domain-skolem-1 below.
(include-book "set-algebra")

(zsub skolem (r)
      p
      r
      (and (consp p)
           (equal (cdr p) (apply r (car p))))
      )

(defthmz subset-skolem ; a key property
  (subset (skolem r) r) 
  :props (zfc domain$prop skolem$prop))

(local (defthmz domain-skolem-1
         (subset (domain (skolem r))
                 (domain r))
         :hints (("Goal" :use ((:instance subset-criterion
                                          (x (domain (skolem r)))
                                          (y (domain r))))))
         :props (zfc domain$prop skolem$prop)
         :rule-classes nil))

; Informal proof of domain-skolem-2-1..  Suppose x \in domain(r).  Then by
; in-cons-apply, <x,r(x)> \in r.  By skolem$comprehension, <x,r(x)> \in
; skolem(r).  So x \in domain(skolem(r)).

(local (progn

(defthmz domain-skolem-2-1-1
  (implies (in x (domain r))
           (in (cons x (apply r x)) r))
  :props (zfc domain$prop)
  :rule-classes nil)

(defthmz domain-skolem-2-1-2
  (implies (in (cons x (apply r x)) r)
           (in (cons x (apply r x)) (skolem r)))
  :props (zfc domain$prop skolem$prop)
  :rule-classes nil)

(defthmz domain-skolem-2-1
  (implies (in x (domain r))
           (in x (domain (skolem r))))
  :props (zfc domain$prop skolem$prop)
  :hints (("Goal"
           :use (domain-skolem-2-1-1 domain-skolem-2-1-2)
           :in-theory (disable skolem$comprehension))))

(defthmz domain-skolem-2
  (subset (domain r)
          (domain (skolem r)))
  :hints (("Goal" :use ((:instance subset-criterion
                                   (x (domain r))
                                   (y (domain (skolem r)))))))
  :props (zfc domain$prop skolem$prop)
  :rule-classes nil)
))

(defthmz domain-skolem ; a key property
  (equal (domain (skolem r))
         (domain r))
  :props (zfc domain$prop skolem$prop)
  :hints (("Goal"
           :in-theory (disable domain-preserves-subset)
           :use (domain-skolem-1 domain-skolem-2))))

(defthmz relation-p-skolem
  (relation-p (skolem r))
  :props (zfc skolem$prop)
  :hints (("Goal" :expand ((relation-p (skolem r))))))

(defthmz funp-skolem ; a key property
  (funp (skolem r))
  :props (zfc skolem$prop)
  :hints (("Goal" :in-theory (enable funp))))

(local (defthmz skolem-skolemizes-1
         (implies (in x (domain (skolem r)))
                  (in (cons x (apply (skolem r) x))
                      (skolem r)))
         :hints (("Goal"
                  :in-theory (disable in-cons-apply)
                  :use ((:instance in-domain-rewrite (x x) (r (skolem r))))))
         :props (zfc domain$prop skolem$prop)
         :rule-classes nil))

(defthmz skolem-skolemizes
; This might be useful, but perhaps the other key properties suffice.
  (implies (in x (domain r))
           (in (cons x (apply (skolem r) x))
               r))
  :hints (("Goal"
           :in-theory '(subset-skolem domain-skolem subset-preserves-in-1)
           :use skolem-skolemizes-1))
  :props (zfc domain$prop skolem$prop))
