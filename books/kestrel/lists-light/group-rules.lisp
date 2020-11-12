; Rules about group, group2, etc.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: harvest good lemmas from this book

(include-book "rules2") ; for things like EQUAL-OF-TAKE-AND-TAKE-WHEN-NOT-EQUAL-OF-SUBRANGES
(include-book "ungroup")
(include-book "group2")
(include-book "group")
(local (include-book "take2"))
(local (include-book "nth"))
(local (include-book "len"))
(local (include-book "nthcdr"))
(local (include-book "cdr"))
(local (include-book "cons"))
(local (include-book "append"))
(local (include-book "subrange"))
(local (include-book "firstn"))
(local (include-book "take"))
(local (include-book "true-list-fix"))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))

(defthm group-becomes-group2
  (implies (and (equal 0 (mod (len x) n))
                (posp n))
           (equal (group n x)
                  (group2 n x)))
  :hints (("Goal" :in-theory (enable group group2))))

(in-theory (disable firstn)) ; move up?!

(defthm take-of-group-2
  (implies (and (<= m (floor (len x) n)) ;m is at most the number of complete blocks
                (posp n)
                (natp m))
           (equal (take m (group n x))
                  (group n (take (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((GROUP N (FIRSTN (* M N) X)))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group firstn TAKE-OF-CDR-BECOMES-SUBRANGE)
                           (FIRSTN-BECOMES-TAKE
                            ;FLOOR-BOUND-ARG1-LINEAR
                            ;*-STRONGLY-MONOTONIC
                            GROUP-BECOMES-GROUP2
                            firstn-becomes-take-gen)))))

(defthm take-of-group2
  (implies (and (<= m (floor (len x) n))
                (posp n)
                (natp m))
           (equal (take m (group2 n x))
                  (group2 n (take (* m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((GROUP2 N (FIRSTN (* M N) X)))
           :induct (firstn-of-group-induct x n m)
           :in-theory (e/d (group2 firstn TAKE-OF-CDR-BECOMES-SUBRANGE)
                           (FIRSTN-BECOMES-TAKE
                            ;FLOOR-BOUND-ARG1-LINEAR
                            ;*-STRONGLY-MONOTONIC
                            GROUP-BECOMES-GROUP2
                            firstn-becomes-take-gen)))))

;move
;use polarity?
(defthm equal-of-takes-extend
  (implies (and (equal (subrange n free x)
                       (subrange n free y))
                (<= n free)
                (natp n)
                (natp free))
           (equal (equal (take n x) (take n y))
                  (equal (take (+ 1 free) x) (take (+ 1 free) y))))
  :hints (("Goal"
           :in-theory (e/d (subrange ;take-of-nthcdr
                            ;equal-of-append
                            )
                           (;list::equal-append-reduction!
                            ;LIST::EQUAL-APPEND-REDUCTION!-ALT ;disable above
                            take-of-nthcdr-becomes-subrange
                            nthcdr-of-take-becomes-subrange
                            cdr-of-take-becomes-subrange-better
                            TAKE-OF-CDR-BECOMES-SUBRANGE
                            nthcdr-of-take
                            ))
           :use ((:instance APPEND-OF-TAKE-AND-NTHCDR-2 (l (take (+ 1 free) x)) (n n))
                 (:instance APPEND-OF-TAKE-AND-NTHCDR-2 (l (take (+ 1 free) y)) (n n)))
           )))

(defun group2-induct (x y n)
  (if (or (not (posp n))
          (< (len x) n)
          (< (len y) n))
      (list x y n)
    (group2-induct (nthcdr n x)
                   (nthcdr n y)
                   n)))

(defthm equal-of-group2-and-group2
  (implies (posp n)
           (equal (equal (group2 n x) (group2 n y))
                  (and (equal (floor (len x) n)
                              (floor (len y) n))
                       (equal (take (* n (floor (len x) n)) x)
                              (take (* n (floor (len y) n)) y)))))
  :hints (("Subgoal *1/2" :cases ((NOT (< (BINARY-* N (FLOOR (LEN Y) N)) (BINARY-+ '1 N)))))
          ("Goal"
           :do-not '(generalize eliminate-destructors)
           :induct (group2-induct x y n)
           :in-theory (e/d (group2
                            take-of-nthcdr-becomes-subrange)
                           (CDR-OF-TAKE)))))

(defthmd group2-in-terms-of-group
  (implies (posp n)
           (equal (group2 n x)
                  (group n (firstn (* n (floor (len x) n)) x)))))

(defthm equal-of-takes-extend2
  (implies (and (equal (nthcdr n x)
                       (subrange n free y))
                (<= n free)
                (natp n)
                (natp free))
           (equal (equal (take n x) (take n y))
                  (equal x (take (+ 1 free) y))))
  :hints (("Goal"
           :in-theory (e/d (subrange ;take-of-nthcdr
                            )
                           (;list::equal-append-reduction!
                            ;LIST::EQUAL-APPEND-REDUCTION!-ALT ;disable above
                            take-of-nthcdr-becomes-subrange
                            nthcdr-of-take-becomes-subrange
                            TAKE-OF-CDR-BECOMES-SUBRANGE
                            cdr-of-take-becomes-subrange-better
                            nthcdr-of-take
                            ))
           :use ((:instance list-split (x x) (n n))
                 (:instance list-split (x (take (+ 1 free) y)) (n n))))))

(defthm equal-of-takes-extend2-alt
  (implies (and (equal (nthcdr n x)
                       (subrange n free y))
                (<= n free)
                (natp n)
                (natp free))
           (equal (equal (take n y) (take n x))
                  (equal x (take (+ 1 free) y))))
  :hints (("Goal" :use (:instance equal-of-takes-extend2)
           :in-theory (disable equal-of-takes-extend2))))

(local (in-theory (disable NTHCDR-OF-TRUE-LIST-FIX)))

(defthm equal-of-group-and-group2-helper
  (implies (and (posp n)
                (true-listp x)
                (true-listp y))
           (equal (equal (group n x) (group2 n y))
                  (and (equal (len x) (* n (floor (len y) n)))
                       (equal (take (len x) x)
                              (take (len x) y)))))
  :hints (("Subgoal *1/2" :cases ((not (< (binary-* n (floor (len y) n)) (binary-+ '1 n)))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (group2-induct x y n)
           :in-theory (enable group group2
                              take-of-nthcdr-becomes-subrange))))

;; (defthm equal-of-group-and-group2-helper
;;   (implies (and (posp n)
;;                 (true-listp x)
;;                 (true-listp y)
;;                 )
;;            (equal (equal (group n x) (group2 n y))
;;                   (and (equal (len x) (* n (floor (len y) n)))
;;                        (equal (take (len x) x)
;;                               (take (len x) y)))))
;;   :hints (("Subgoal *1/2" :cases ((NOT (< (BINARY-* N (FLOOR (LEN Y) N)) (BINARY-+ '1 N)))))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (group2-induct x y n)
;;            :in-theory (e/d (group group2
;;                               true-list-fix-of-nthcdr
;; ;take-of-nthcdr-becomes-subrange
;;                               ) (CONSP-FROM-LEN-CHEAP
;;                                  cdr-iff
;;                                  CONSP-OF-CDR-WHEN-LEN-KNOWN))))
;;   )

(defthm equal-of-group-and-group2
  (implies (posp n)
           (equal (equal (group n x) (group2 n y))
                  (and (equal (len x) (* n (floor (len y) n)))
                       (equal (take (len x) x)
                              (take (len x) y)))))

  :hints (("Goal" :use (:instance equal-of-group-and-group2-helper (x (true-list-fix x)) (y (true-list-fix y)))
           :in-theory (disable equal-of-group-and-group2-helper))))

(defthm equal-of-group-and-group2-alt
  (implies (posp n)
           (equal (equal (group2 n y) (group n x))
                  (and (equal (len x) (* n (floor (len y) n)))
                       (equal (take (len x) x)
                              (take (len x) y)))))
  :hints (("Goal" :use (:instance equal-of-group-and-group2)
           :in-theory (disable equal-of-group-and-group2))))


(defthm items-have-len-of-group-strong
  (implies (posp n)
           (equal (items-have-len n (group n x))
                  (equal 0 (mod (len x) n))))
  :hints (("Goal" :in-theory (enable GROUP items-have-len))))

(defthmd equal-of-*-of-floor
  (implies (and (rationalp m)
                (rationalp n)
                (not (equal n 0)))
           (equal (EQUAL (* N (FLOOR M N)) M)
                  (equal 0 (mod m n)))))

(defthm equal-of-group-and-group
  (implies (and (posp n)
                (true-listp x)
                (true-listp y))
           (equal (equal (group n x) (group n y))
                  (equal x y)))
  :hints (("Subgoal *1/2" :cases ((NOT (< (BINARY-* N (FLOOR (LEN Y) N)) (BINARY-+ '1 N)))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (group2-induct x y n)
           :in-theory (enable group group2))))

(defthm subrange-of-group
  (implies (and (< m2 (floor (len x) n)) ;drop or gen?
                (posp n)
                (natp m)
                (<= m m2)
                (natp m2))
           (equal (subrange m m2 (group n x))
                  (group n (subrange (* n m) (+ (* n m) (+ -1 (* n (+ 1 (- m2 m))))) x))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (subrange) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                              CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                                              TAKE-OF-CDR-BECOMES-SUBRANGE
                                              NTHCDR-OF-TAKE-BECOMES-SUBRANGE)))))

(defthm firstn-of-ungroup
  (implies (and (equal 0 (mod m n))
                (<= m (* n (len x)))
                (posp n)
                (natp m))
           (equal (firstn m (ungroup n x))
                  (ungroup n (firstn (floor m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (ungroup-induct x m n)
           :expand ((NTH 1 X)
                    (NTH 0 (CDR X))
                    (UNGROUP N (TAKE (* M (/ N)) X)))
           :in-theory (e/d (natp
                            posp
                            ungroup ;take
                            len-of-cdr
                            consp-of-cdr
                            EQUAL-OF-0-AND-MOD)
                           (DIVISIBILITY-IN-TERMS-OF-FLOOR
                            TAKE-OF-CDR-BECOMES-SUBRANGE
                            NTH-OF-CDR
                            ;; list::NTH-OF-CDR
                            ;; LIST::EQUAL-APPEND-REDUCTION!
                            ;; LIST::LEN-POS-REWRITE
                            )))))

(defthmd group-unroll
  (implies (not (or (not (posp n))
                    (atom x)))
           (equal (group n x)
                  (cons (firstn n x)
                        (group n (nthcdr n x)))))
  :hints (("Goal" :in-theory (enable group))))

(in-theory (disable integerp-of-small))

;this can probably loop!
(defthmd nth-when-equal-of-take
  (implies (and (equal k (take m x))
;                (syntaxp (and (quotep k) (not (quotep x))))
                (< n m)
                (natp n)
                (natp m))
           (equal (nth n x) (nth n k))))

;this can probably loop!
(defthmd nth-when-equal-of-firstn
  (implies (and (equal free (firstn m x))
;(syntaxp (and (quotep k) (not (quotep x))))
                (< n m)
                (natp n)
                (natp m))
           (equal (nth n x) (nth n free))))

;hope this is okay. i need it for sha1
(defthmd nth-when-equal-of-take-hack
  (implies (and (equal (group 16 k) ;
                       (take m x))
;                (syntaxp (and (quotep k) (not (quotep x))))
;                (< n (CEILING (LEN k) 16))
                (< n m) ;move to conclusion? maybe we can't
                (natp n)
                (natp m))
           (equal (nth n x)
                  (FIRSTN 16 (NTHCDR (* n 16) k))))
  :hints (("Goal" :use (:instance nth-when-equal-of-take (k (group 16 k)))))
  )

;; (defthm group-of-finalcdr
;;   (equal (group n (list::finalcdr x))
;;          nil))

(defthm group2-of-ungroup-same
  (implies (and (items-have-len n x)
                (posp n)
                (true-listp x)
                (all-true-listp x)
                )
           (equal (group2 n (ungroup n x))
                  x))
  :hints (("Goal" :in-theory (e/d (ungroup len-of-cdr) (group-becomes-group2))
           :expand (GROUP2 (LEN (CAR X))
                        (APPEND (CAR X)
                                (UNGROUP (LEN (CAR X)) (CDR X)))))))
