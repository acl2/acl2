; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; BOZO we could consider removing osets now...
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "std/lists/sets" :dir :system)
(include-book "witness-cp")



;; Set reasoning for WITNESS-CP.

;; BOZO maybe change the variable names from all Ks to appropriate short names,
;; i.e. ssew for subsetp-witness?
(defquantexpr subsetp
  :predicate (subsetp-equal x y)
  :quantifier :forall
  :witnesses ((k (subsetp-witness x y)))
  :expr (implies (member k x)
                 (member k y))
  :witness-hints ('(:in-theory '(subsetp-witness-correct)))
  :instance-hints ('(:in-theory '(subsetp-member)))
  :in-package-of acl2::foo)

(defquantexpr intersectp
  :predicate (intersectp-equal x y)
  :quantifier :exists
  :witnesses ((k (intersectp-witness x y)))
  :expr (and (member k x)
             (member k y))
  :witness-hints ('(:in-theory '(intersectp-witness-correct)))
  :instance-hints ('(:in-theory '(intersectp-member)))
  :in-package-of acl2::foo)

(defquantexpr set-equiv
  :predicate (set-equiv x y)
  :quantifier :forall
  :witnesses ((k (set-unequal-witness x y)))
  :expr (iff (member k x)
             (member k y))
  :witness-hints ('(:in-theory '(set-unequal-witness-correct)))
  :instance-hints ('(:in-theory '(set-equiv-implies-iff-member-2))))

(defquantexpr set-consp
  :predicate (consp x)
  :quantifier :exists
  :witnesses ((k (car x)))
  :expr (member k x)
  :generalize nil
  :witness-hints ('(:in-theory nil
                    :expand ((:with member-equal
                              (:free (k) (member-equal k x))))))
  :instance-hints ('(:in-theory nil
                    :expand ((:with member-equal
                              (:free (k) (member-equal k x)))))))


(defexample set-reasoning-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rules
  (subsetp-instancing
   intersectp-instancing
   set-equiv-instancing
   set-consp-instancing))

(defexample set-reasoning-no-consp-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rules
  (subsetp-instancing
   intersectp-instancing
   set-equiv-instancing))

(def-witness-ruleset set-reasoning-rules
  '(subsetp-witnessing
    intersectp-witnessing
    set-equiv-witnessing
    set-consp-witnessing
    subsetp-instancing
    set-equiv-instancing
    intersectp-instancing
    set-consp-instancing
    set-reasoning-member-template))

(def-witness-ruleset set-reasoning-no-consp
  '(subsetp-witnessing
    intersectp-witnessing
    set-equiv-witnessing
    subsetp-instancing
    set-equiv-instancing
    intersectp-instancing
    intersectp-member-template
    subsetp-member-template
    set-equiv-member-template
    set-reasoning-no-consp-member-template))

(def-witness-ruleset set-reasoning-no-consp-manual-examples
  '(subsetp-witnessing
    intersectp-witnessing
    set-equiv-witnessing
    subsetp-instancing
    set-equiv-instancing
    intersectp-instancing
    intersectp-member-template
    subsetp-member-template
    set-equiv-member-template))

(def-witness-ruleset set-reasoning-manual-examples
  '(subsetp-witnessing
    intersectp-witnessing
    set-equiv-witnessing
    set-consp-witnessing
    subsetp-instancing
    set-equiv-instancing
    intersectp-instancing
    set-consp-instancing))


(defmacro set-reasoning ()
  '(witness :ruleset set-reasoning-rules))



(defthmd intersectp-of-superset
  (implies (and (intersectp a b)
                (subsetp a c))
           (intersectp c b))
  :hints ((set-reasoning))
  :rule-classes ((:rewrite :match-free :all)))

(defthmd intersectp-of-superset2
  (implies (and (subsetp a c)
                (intersectp b a))
           (intersectp b c))
  :hints ((set-reasoning))
  :rule-classes ((:rewrite :match-free :all)))




(in-theory (disable set-difference-equal intersection-equal))


