; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For background, see file README.txt.

(in-package "HOL")

; (depends-on "ex1.defhol")

(include-book "../acl2/theories")

(import-theory ex1)

; A trivial consequence of the imported axiom for FST:
(defgoal fst-comma

; This call of defgoal generates (DEFTHM HOL{FST-COMMA} ...).  It checks that
; the formula below is appropriate for an earlier defhol event with the name
; indicated here, fst-comma, as indicated by the value of :goal in that event
; as a translation from HOL4 associated with that name (i.e., with fst-comma).
; The hint below has been added manually in order for the proof of this
; theoerem to succeed.

  (implies
   (and (alist-subsetp (ex1$hta) hta)
        (hpp x hta)
        (equal (hp-type x) (typ a))
        (hpp y hta)
        (equal (hp-type y) (typ b))
        (force (ex1$prop)))
   (equal (hp= (hap* (fst (typ (:arrow* (:hash a b) a)))
                     (hp-comma x y))
               x)
          (hp-true)))
  :hints (("Goal" :in-theory (disable hp-comma))))

; See ex1-proof.lisp:
#|
(defgoal pair_fst_snd_eq
  (implies
   (and (alist-subsetp (ex1$hta) hta)
        (hpp p hta)
        (equal (hp-type p) (typ (:hash a b)))
        (hpp q hta)
        (equal (hp-type q) (typ (:hash a b)))
        (force (ex1$prop)))
   (equal (hp= (hp-and
                (hp= (hap* (fst (typ (:arrow* (:hash a b) a))) p)
                     (hap* (fst (typ (:arrow* (:hash a b) a))) q))
                (hp= (hap* (snd (typ (:arrow* (:hash a b) b))) p)
                     (hap* (snd (typ (:arrow* (:hash a b) b))) q)))
               (hp= p q))
          (hp-true))))
|#
