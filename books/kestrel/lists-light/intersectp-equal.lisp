; A lightweight book about the built-in function intersectp-equal.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))
(local (include-book "subsetp-equal"))

(in-theory (disable intersectp-equal))

;; INTERSECTP-EQUAL is the boolean-valued counterpart of INTERSECTION-EQUAL
;; (see intersection-equal.lisp).  It recurses on, and so directly decomposes
;; a CONS in, its FIRST argument; the rules below supply the corresponding
;; decompositions for the second argument, along with commutativity and the
;; interaction with MEMBER-EQUAL and SUBSETP-EQUAL.

(defthm booleanp-of-intersectp-equal
  (booleanp (intersectp-equal x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-of-nil-arg1
  (equal (intersectp-equal nil x)
         nil)
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-of-nil-arg2
  (equal (intersectp-equal x nil)
         nil)
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (equal (intersectp-equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-when-not-consp-arg2-cheap
  (implies (not (consp y))
           (equal (intersectp-equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-of-cons-arg1
  (equal (intersectp-equal (cons a x) y)
         (if (member-equal a y)
             t
           (intersectp-equal x y)))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-of-cons-arg2
  (equal (intersectp-equal x (cons a y))
         (if (member-equal a x)
             t
           (intersectp-equal x y)))
  :hints (("Goal" :in-theory (enable intersectp-equal member-equal))))

(defthm intersectp-equal-of-append-arg1
  (equal (intersectp-equal (append x y) z)
         (or (intersectp-equal x z)
             (intersectp-equal y z)))
  :hints (("Goal" :in-theory (enable intersectp-equal append))))

(defthm intersectp-equal-of-append-arg2
  (equal (intersectp-equal x (append y z))
         (or (intersectp-equal x y)
             (intersectp-equal x z)))
  :hints (("Goal" :in-theory (enable intersectp-equal append))))

;; Disabled by default: as a permutative rule this normalizes the argument
;; order of every INTERSECTP-EQUAL term, which collapses the distinctions the
;; fixed-orientation monotonicity rules below are stated in terms of, and so
;; fights with them.  Enable it where a commutation is actually wanted.
(defthmd intersectp-equal-commutative
  (equal (intersectp-equal x y)
         (intersectp-equal y x))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

(defthm intersectp-equal-same
  (equal (intersectp-equal x x)
         (consp x))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

;; Disabled because A is a free variable.
(defthmd intersectp-equal-when-member-equal-and-member-equal
  (implies (and (member-equal a x)
                (member-equal a y))
           (intersectp-equal x y))
  :hints (("Goal" :in-theory (enable intersectp-equal))))

;; The contrapositive of the rule just above, oriented to refute a membership
;; claim.  Disabled because Y is a free variable.
(defthmd not-member-equal-when-not-intersectp-equal
  (implies (and (not (intersectp-equal x y))
                (member-equal a y))
           (not (member-equal a x)))
  :hints (("Goal" :in-theory (enable intersectp-equal
                                     intersectp-equal-when-member-equal-and-member-equal))))

;; Appending two lists gives a duplicate-free list exactly when each is
;; duplicate-free and the two are disjoint.  The -ALT avoids a name clash with
;; NO-DUPLICATESP-EQUAL-OF-APPEND in no-duplicatesp-equal.lisp, which states
;; the same fact with INTERSECTION-EQUAL in place of INTERSECTP-EQUAL.
;; Disabled for that reason too: the two rules have the same left-hand side
;; but different right-hand sides, so a book that includes both and leaves
;; both enabled would get whichever normal form happened to fire first.
(defthmd no-duplicatesp-equal-of-append-alt
  (equal (no-duplicatesp-equal (append x y))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal y)
              (not (intersectp-equal x y))))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable no-duplicatesp-equal intersectp-equal
                              append member-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Monotonicity of non-intersection in a subset, in all four orientations:
;; which argument of INTERSECTP-EQUAL the known-disjoint bigger list occupies
;; in the hypothesis, and which argument the smaller list occupies in the
;; conclusion.  All four are disabled, since BIG is a free variable in each
;; and they are expensive as blanket rewrites; enable them where needed.

(defthmd not-intersectp-equal-when-subsetp-equal-arg2
  (implies (and (not (intersectp-equal x big))
                (subsetp-equal small big))
           (not (intersectp-equal x small)))
  :hints (("Goal" :in-theory (enable intersectp-equal
                                     not-member-equal-when-subsetp-equal-2))))

(defthmd not-intersectp-equal-when-subsetp-equal-arg1
  (implies (and (not (intersectp-equal big x))
                (subsetp-equal small big))
           (not (intersectp-equal small x)))
  :hints (("Goal"
           :use (not-intersectp-equal-when-subsetp-equal-arg2
                 (:instance intersectp-equal-commutative (x big) (y x))
                 (:instance intersectp-equal-commutative (x small) (y x))))))

(defthmd not-intersectp-equal-when-subsetp-equal-arg1-alt
  (implies (and (not (intersectp-equal x big))
                (subsetp-equal small big))
           (not (intersectp-equal small x)))
  :hints (("Goal"
           :use (not-intersectp-equal-when-subsetp-equal-arg2
                 (:instance intersectp-equal-commutative (x small) (y x))))))

(defthmd not-intersectp-equal-when-subsetp-equal-arg2-alt
  (implies (and (not (intersectp-equal big x))
                (subsetp-equal small big))
           (not (intersectp-equal x small)))
  :hints (("Goal"
           :use (not-intersectp-equal-when-subsetp-equal-arg2
                 (:instance intersectp-equal-commutative (x big) (y x))))))

;; The same two facts with the SUBSETP-EQUAL hypothesis stated FIRST.  BIG is
;; a free variable in all of these, and ACL2 binds it by matching the first
;; hypothesis it can relieve; which order is usable therefore depends on which
;; fact is present in the context.  When BIG is a term that appears only in a
;; containment hypothesis -- an APPEND, say -- and never in a disjointness
;; one, only these orderings can find it.  Disabled, like the four above.

(defthmd not-intersectp-equal-when-subsetp-equal-arg2-subsetp-first
  (implies (and (subsetp-equal small big)
                (not (intersectp-equal x big)))
           (not (intersectp-equal x small)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable not-intersectp-equal-when-subsetp-equal-arg2))))

(defthmd not-intersectp-equal-when-subsetp-equal-arg1-subsetp-first
  (implies (and (subsetp-equal small big)
                (not (intersectp-equal big x)))
           (not (intersectp-equal small x)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable not-intersectp-equal-when-subsetp-equal-arg1))))
