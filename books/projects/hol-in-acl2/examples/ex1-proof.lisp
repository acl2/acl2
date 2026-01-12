; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; The goal in this book is to prove (DEFGOAL pair_fst_snd_eq ...) from
; ex1-thy.lisp, which is a file produced with a translator from HOL to ACL2
; written by Konrad Slind.  That goal is stated in the ZF package as the final
; theorem, HOL{pair_fst_snd_eq}, in the present book; it is redundantly phrased
; in terms of DEFGOAL in ex1-top.lisp.

; This theorem is a bit of a nightmare to read, but we can get a prettier
; picture as follows.

;  (include-book "../acl2/hol-pprint")
;  (include-book "ex1-thy")
;  (in-package "HOL")

; And then, applying hol-pprint to the conclusion of the IMPLIES in the main
; theorem returns:

#|
(EQUAL (= (AND (= (FST P) (FST Q))
               (= (SND P) (SND Q)))
          (= P Q))
       HP-TRUE)
|#

; As with eval-poly-proof.lisp, we start by including some books.

; Define fst and snd in HOL.
(include-book "ex1-thy")

; Include a book of general lemmas, developed during the proof in
; eval-poly-proof.lisp and reusable here and elsewhere.
; NOTE: At some point, some lemmas below should probably be incorporated into
; the following book.
(include-book "../acl2/lemmas")

; Include the set-theory library.
(include-book "projects/set-theory/top" :dir :system)

(defthmz hpp-for-hash
  (implies (hpp x hta)
           (equal (equal (cdr x) (typ (:hash a b)))
                  (equal x (make-hp (cons (car (hp-value x))
                                          (cdr (hp-value x)))
                                    (typ (:hash a b))))))
  :rule-classes nil
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthm cdr-hp-comma
  (equal (cdr (hp-comma x y))
         (list :hash (hp-type x) (hp-type y)))
  :hints (("Goal" :in-theory (enable hp-comma))))

(defthmz hpp-hp-comma-forward
  (implies (hpp (hp-comma x y) hta)
           (and (hpp x hta)
                (hpp y hta)))
  :props (zfc prod2$prop)
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval))))

#!hol
(DEFTHM HOL{pair_fst_snd_eq}-lemma
  (let ((p (hp-comma p1 p2))
        (q (hp-comma q1 q2)))
    (implies
     (and (alist-subsetp (ex1$hta) hta)
          (hpp p hta)
          (equal (hp-type p) (typ (:hash a b)))
          (hpp q hta)
          (equal (hp-type q) (typ (:hash a b)))
          (force (ex1$prop)))
     (equal (hp= (hp-and (hp= (hap* (fst (typ (:arrow* (:hash a b) a))) p)
                              (hap* (fst (typ (:arrow* (:hash a b) a))) q))
                         (hp= (hap* (snd (typ (:arrow* (:hash a b) b))) p)
                              (hap* (snd (typ (:arrow* (:hash a b) b))) q)))
                 (hp= p q))
            (hp-true)))))

(defthmz hp-comma-hp-hash-car-hp-hash-cdr-alt-lemma
  (implies (and (hpp x hta)
                (equal (cdr x)
                       (list :hash (caddr x) (cadddr x))))
           (hp-comma-p x))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthmz hp-comma-hp-hash-car-hp-hash-cdr-alt
  (implies (and (hpp x hta)
                (equal (cdr x)
                       (list :hash (caddr x) (cadddr x))))
           (equal (hp-comma (hp-hash-car x)
                            (hp-hash-cdr x))
                  x))
  :props (zfc prod2$prop))

(defthmz hpp-hp-comma
  (equal (hpp (hp-comma x y) hta)
         (and (hpp x hta)
              (hpp y hta)))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthmz hpp-hash-car
  (implies (and (hpp x hta)
                (equal (cdr x)
                       (list :hash (caddr x) (cadddr x))))
           (hpp (hp-hash-car x) hta))
  :props (zfc prod2$prop)
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthmz hpp-hash-cdr
  (implies (and (hpp x hta)
                (equal (cdr x)
                       (list :hash (caddr x) (cadddr x))))
           (hpp (hp-hash-cdr x) hta))
  :props (zfc prod2$prop)
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-type-eval))))

; The following leads to a forcing round in HOL{pair_fst_snd_eq}.  We have
; zf::hp-comma-hp-hash-car-hp-hash-cdr-alt instead, which suffices for the
; proof.
(in-theory (disable zf::hp-comma-hp-hash-car-hp-hash-cdr))

#!hol
(DEFTHM HOL{pair_fst_snd_eq}
  (implies
   (and (alist-subsetp (ex1$hta) hta)
        (hpp p hta)
        (equal (hp-type p) (typ (:hash a b)))
        (hpp q hta)
        (equal (hp-type q) (typ (:hash a b)))
        (force (ex1$prop)))
   (equal (hp= (hp-and (hp= (hap* (fst (typ (:arrow* (:hash a b) a))) p)
                            (hap* (fst (typ (:arrow* (:hash a b) a))) q))
                       (hp= (hap* (snd (typ (:arrow* (:hash a b) b))) p)
                            (hap* (snd (typ (:arrow* (:hash a b) b))) q)))
               (hp= p q))
          (hp-true)))
  :hints (("Goal" :use ((:instance HOL{pair_fst_snd_eq}-lemma
                                   (p1 (hp-hash-car p))
                                   (p2 (hp-hash-cdr p))
                                   (q1 (hp-hash-car q))
                                   (q2 (hp-hash-cdr q)))
                        (:instance zf::hpp-for-hash
                                   (zf::x p)
                                   (zf::hta hta)
                                   (zf::a a)
                                   (zf::b b))
                        (:instance zf::hpp-for-hash
                                   (zf::x q)
                                   (zf::hta hta)
                                   (zf::a a)
                                   (zf::b b))))))
