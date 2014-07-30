; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; BOZO we could consider removing osets now...
(include-book "std/osets/top" :dir :system)
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


