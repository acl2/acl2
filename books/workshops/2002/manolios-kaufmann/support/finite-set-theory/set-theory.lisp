; Finite Set Theory for ACL2
; Copyright (C) 2001  Georgia Institute of Technology

; This book is derived from the book "set-theory-original" by J Moore,
; which is included in this directory.  The only difference between
; this version and J Moore's version is that I use the book
; "total-ordering" also in this directory instead of the orginal
; "total-ordering-original".  This allows me to simplify some of the
; theorems and to also remove theorems.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Panagiotis Manolios
; email:      manolios@cc.gatech.edu
; College of Computing
; CERCS Lab
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

(in-package "S")

(include-book "total-ordering")

(defun ur-elementp (x)
  (or (atom x)
      (eq (car x) :UR-CONS)))

; Example objects are
; 3                                  numbers
; #\A                                characters
; "Abc"                              strings
; ABC                                symbols
; (:UR-CONS (a b c))                 lists
; (1 2 1 3 (:UR-CONS (a b c)))       sets

; Some Comments on :UR-CONS

; It is simplest never to write the symbol :UR-CONS in your sets
; unless you mean to mark consp ur-elements.  The symbol :UR-CONS if
; encountered in unexpected places produces counter-intuitive results.

; For example, (1 2 :UR-CONS) might be thought of as {1 2 :UR-CONS}
; but in fact is {1 2}.  The reason is that it is parsed as (1 2
; . (:UR-CONS)).  The enumeration of the elements of a set is
; terminated by the first ur-element cdr.  So just as (1 2 . 3) is {1
; 2}, so is (1 2 . (:UR-CONS ...)).  Any attempt to include :UR-CONS
; as an element of an explicit set constant terminates the enumeration
; of the set elements and so fails to include :UR-CONS as an element.

; Is it possible to use scons to add :UR-CONS to a list?  You might
; expect (scons :UR-CONS '(1 2)) to be {:UR-CONS 1 2}.  But it is in
; fact {CONS 1 2}.  If you ever succeed in using :UR-CONS as an
; ur-element it is treated as though it were a non-canonical
; representation of the symbol ACL2::CONS.

; These considerations make it simplest to avoid using :UR-CONS except
; in the syntax of sets.

(defun set-insert (e s)

; NIL is the only ur-elementp upon which set-insert is ever called, in
; the process of canonicalizing.  But I prove theorems about
; set-insert and to make them simpler to state, I have it treat all
; ur-elements s as the empty set.  Also, both e and s are assumed to
; be canonical.

  (cond ((ur-elementp s) (cons e nil))
        ((equal e (car s)) s)
        ((<< e (car s))
         (cons (car s)
               (set-insert e (cdr s))))
        (t (cons e s))))

(defun ur-fix (x)

; This converts an arbitrary Lisp object into an ordinary ur-element
; without changing the type.  We do not want to change the type so
; that set equality refines IFF and is a congruence relation for the
; arithmetic primitives in ACL2.  We discuss the conversions below.

  (cond ((atom x)
         (cond ((eq x :UR-CONS) 'ACL2::UR-CONS)
               (t x)))
        ((eq (car x) :UR-CONS)
         (cond ((or (atom (cdr x))
                    (atom (cadr x)))
                '(:UR-CONS (NIL)))
               (t (list :UR-CONS (cadr x)))))
        (t nil)))

; Conversions:
; (1) If we encounter :UR-CONS where an ur-element is expected, we convert it
;     the symbol ACL2::UR-CONS.  This prevents the accidental formation of
;     a :UR-CONS by set operations on data containing :UR-CONS.  For example,
;     (scons :UR-CONS '(a b c)) will produce the set {ACL2::UR-CONS a b c}, not
;     the set {:UR-CONS a b c} and not the ``ur-element'' (:UR-CONS a b c).
; (2) If we encounter (:UR-CONS . xxx) where an ur-element is expected, we
;     are sure to return something of the form (:UR-CONS (...)).  An ur-element
;     marked :UR-CONS means a cons of some sort, no matter what is inside.
;     A rough model of the conversion rule is that if the :UR-CONS expression
;     is ill-formed it denotes (:UR-CONS (NIL)).  More accurately, there are
;     three cases:
;     (a) (:UR-CONS . atom)           => (:UR-CONS (NIL))
;     (b) (:UR-CONS atom . anything)  => (:UR-CONS (NIL))
;     (c) (:UR-CONS (...) . anything) => (:UR-CONS (...))


; (in-theory (disable ur-fix))

(defun canonicalize (x)
  (cond ((ur-elementp x) (ur-fix x))
        ((ur-elementp (cdr x))
         (list (canonicalize (car x))))
        (t (set-insert (canonicalize (car x))
                       (canonicalize (cdr x))))))


(defun orderedp (x)
  (cond ((ur-elementp x) t)
        ((ur-elementp (cdr x)) t)
        ((<< (cadr x) (car x))
         (orderedp (cdr x)))
        (t nil)))

(defun canonicalp (x)
  (cond ((atom x)
         (not (eq x :UR-CONS)))
        ((eq (car x) :UR-CONS)
         (and (consp (cdr x))
              (consp (cadr x))
              (equal (cddr x) nil)))
        ((ur-elementp (cdr x))
         (and (canonicalp (car x))
              (equal (cdr x) nil)))
        (t (and (canonicalp (car x))
                (canonicalp (cdr x))
                (orderedp x)))))

(defthm orderedp-set-insert
  (implies (and (canonicalp e)
                (canonicalp a))
           (orderedp (set-insert e a)))
  :hints (("Goal" :induct (set-insert e a))))

(defthm canonicalp-set-insert
  (implies (and (canonicalp e)
                (canonicalp a))
           (canonicalp (set-insert e a)))
  :hints (("Goal" :induct (set-insert e a))))

(defthm canonicalp-ur-fix
  (canonicalp (ur-fix X)))

(defthm canonicalp-canonicalize
  (canonicalp (canonicalize x)))

(defthm canonicalize-canonicalp
  (implies (canonicalp x) (equal (canonicalize x) x)))

; So here is equality in our system.

(defun = (x y)
  (equal (canonicalize x)
         (canonicalize y)))

(defequiv =)

; ----------------------------------------------------------------------------
; The Set Constructor/Destructor Primitives

; It is very convenient to pretend that sets are built as a new data
; type.  So here are the basic functions.  I will keep them enabled
; until I have proved the necessary facts about canonicalization,
; equality (=) and subsetp.  Then I'll disable them.  But I introduce
; them now so that mem and subsetp can be defined in terms of them.  I
; have also collected together certain of their elementary properties.
; Most of these theorems are not used until after I have disabled
; these primitives.

(defun sfix (a)
  (if (ur-elementp a)
      nil
    a))

(defun scons (e a)
  (if (equal e :UR-CONS)
      (cons (canonicalize e)
            (sfix a))
    (cons e (sfix a))))

; The macro below allows me to write (brace a b c) to mean {a, b, c}.

(defmacro brace (&rest args)
  (cond ((endp args) nil)
        (t `(scons ,(car args)
                   (brace ,@(cdr args))))))

; Here are some timings of this entire library.  These timings started
; when I began experimenting with three different flavors of scar and
; scdr.  The flavors are shown below along with some Caerlaverock
; timings.  I chose functionp1-set-insert as a representative expensive
; proof.

; When these timings were done, there were 279 events and the last one
; was APPLY-RESTRICT.  Since the book has probably changed since then,
; these timings are only relevant insofar as they reflect the relative
; effects of the various experiments.  Even that claim is suspect:
; since doing these timings I have discovered that there can be a
; considerable difference (30%) between the time it takes in a fresh
; GCL and the time it takes to ``repeat'' the computation in a soiled
; GCL.  Fresh GCL is faster.  I did not record whether the times below
; were done in fresh system or not.

; During the first three experiments, I had the <<-rules -- namely <<,
; transitivity, mutual-exclusion, and trichotomy -- disabled by
; default and turned them on during certain proofs.  They were on
; during functionp1-set-insert, even though I eventually discovered
; they didn't have to be for the proof to go through.

;                                    functionp1-set-insert  entire file

(defun scar (a)
; (car a)                                  ;;; 232 secs      1153 secs
; (if (equal (car a) :UR-CONS) nil (car a))   ;;; 404 secs      1212 secs
  (if (ur-elementp a) nil (car a))         ;;; 308 secs      1239 secs
  )

; I then learned that I did not have to have <<-rules enabled during
; the functionp1-set-insert proof or the analogous ones.  So I took out
; those theory commands and got:

;                                          ;;;   2 secs       889 secs

; Then I had the idea of coding up the ``fast << rules.''  Operating
; in the fast-<<-rules theory by default and occasionally either
; enabling << or switching over to the slow-<<-rules, I got the
; following times in a fresh GCL:

;                                          ;;;   2 secs       370 secs


(defun scdr (a)
; (sfix (cdr a))
; (if (equal (car a) :UR-CONS) nil (sfix (cdr a)))
  (if (ur-elementp a) nil (sfix (cdr a)))
  )

(defcong = = (scons e a) 1
  :hints (("Goal" :in-theory (enable =))))

(defcong = = (scons e a) 2
  :hints (("Goal" :in-theory (enable =))))

(defthm scar-scons
  (= (scar (scons e a)) e))

(defthm scdr-scons
  (= (scdr (scons e a)) (sfix a)))

(defthm ur-elementp-scar
  (implies (ur-elementp x) (equal (scar x) nil)))

(defthm ur-elementp-scdr
  (implies (ur-elementp x) (equal (scdr x) nil)))

(defun setp (x)
  (or (equal x nil)
      (not (ur-elementp x))))

(defthm setp-scdr
  (setp (scdr a))
  :rule-classes (:type-prescription :generalize))

(defthm scons-scar-scdr
  (implies (not (ur-elementp a))
           (= (scons (scar a) (scdr a)) a))
  :rule-classes :elim)

(defthm acl2-count-scdr
  (implies (not (ur-elementp a))
           (o< (acl2-count (scdr a))
	       (acl2-count a)))
  :rule-classes
  ((:built-in-clause)
   (:linear :corollary
            (implies (not (ur-elementp a))
                     (< (acl2-count (scdr a))
                        (acl2-count a))))))

(defthm consp-set-insert
  (consp (set-insert e a))
  :rule-classes :type-prescription)

(defthm car-set-insert-not-equal-ur-cons
  (implies (and (canonicalp e)
                (canonicalp a))
           (not (equal (set-insert e a) (cons :UR-CONS x)))))

(defcong = equal (ur-elementp x) 1)

; Note: We will generally keep sfix enabled, so this rule will not be
; of much use.

(defcong = = (sfix x) 1)

(defthm not-ur-elementp-scons
  (not (ur-elementp (scons e a))))

(defthm not-consp-implies-ur-elementp
  (implies (not (consp e))
           (ur-elementp e)))

(defthm scons-nil
  (implies (and (syntaxp (not (equal a ''nil)))
                (ur-elementp a))
           (= (scons e a)
              (scons e nil))))

(defthm canonicalize-ur-cons
  (not (equal (canonicalize x) :UR-CONS)))

(defthm set-insert-set-insert
  (implies (and (canonicalp e)
                (canonicalp d)
                (canonicalp a))
           (equal (set-insert e (set-insert d a))
                  (set-insert d (set-insert e a))))
  :hints (("Goal" :induct (set-insert e a)
          :in-theory (slow-<<-rules))))

; This rule lets us do a cross-fertilization without waiting for the
; prior elim.  The version of this rule that rewrites (set-insert e xxx)
; to (set-insert d (set-insert e a)) has been known to cause infinite
; loops, even with a hand-picked :loop-stopper.

(defthm set-insert-short-cut
  (implies (and (equal xxx (set-insert d a))
                (canonicalp e)
                (canonicalp d)
                (canonicalp a))
           (equal (equal (set-insert e xxx)
                         (set-insert d (set-insert e a)))
                  t)))

(defthm set-insert-dup
  (implies (and (canonicalp e)
                (canonicalp a))
           (equal (set-insert e (set-insert e a))
                  (set-insert e a)))
  :hints (("Goal" :induct (set-insert e a))))

(defthm scons-scons-2
  (= (scons e (scons d a))
     (scons d (scons e a))))

(defthm scons-scons-1
  (= (scons e (scons e a))
     (scons e a)))

(defthm equal-singleton-set-insert
  (implies (and (canonicalp e)
                (canonicalp d)
                (canonicalp a))
           (equal (equal (list e) (set-insert d a))
                  (and (equal e d)
                       (or (equal (sfix a) nil)
                           (equal (list e) a)))))
  :hints (("Goal" :induct (set-insert d a))))

(defthm car-set-insert
  (implies (and (canonicalp e)
                (canonicalp a))
           (equal (car (set-insert e a))
                  (if (ur-elementp a)
                      e
                    (if (<< (car a) e)
                        e
                      (car a)))))
  :hints (("Goal"
           :induct (set-insert e a)
           :in-theory (enable ur-elementp))))

(defthm =-singletons
  (equal (= (scons e nil) (scons d a))
         (and (= e d)
              (or (ur-elementp a)
                  (= (scons e nil) a))))
  :hints (("Goal" :in-theory (enable = scons ur-elementp)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
             (equal (= (scons d a) (scons e nil))
                    (and (= e d)
                         (or (ur-elementp a)
                             (= (scons e nil) a))))

; Note: This hint is required here because we do not know that
; = is commutative (except by opening it up)!

             :hints (("Goal" :in-theory (enable =))))))

; Basic...
(defun <<-cons-1-hint (x y)
  (if (consp x)
      (list (<<-cons-1-hint (car x) (cdr x)))
    y))

(defthm <<-cons-1
  (<< x (cons x y))
  :hints (("Goal" :induct (<<-cons-1-hint x y)
           :in-theory (cons 'acl2::lexorder (slow-<<-rules <<)))))

(defthm not-=-x-set-insert-x
  (implies (and (canonicalp e)
                (canonicalp x))
           (not (equal e (set-insert e x))))
  :hints (("Goal" :in-theory (cons 'ur-elementp
                                   (slow-<<-rules)))))

(defthm not-=-x-scons-x
  (not (= e (scons e x)))
  :hints (("Goal" :in-theory (enable = scons ur-elementp)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary (not (= (scons e x) e)))))

; ----------------------------------------------------------------------------
; Set Membership and the Subset Relation

(defun mem (e a)
  (cond ((ur-elementp a) nil)
        (t (or (= e (scar a))
               (mem e (scdr a))))))

(defun subsetp (a b)
  (cond ((ur-elementp a) t)
        (t (and (mem (scar a) b)
                (subsetp (scdr a) b)))))

; I now prove that = is a congruence for both arguments of mem.  The
; proof for the first argument is easy because (mem e s) only uses
; (canonicalize e).  [So, if (canonicalize e) is (canonicalize e')
; it is obvious that (mem e s) is (mem e' s).]

; The proof for the second argument is harder and works this way.  We
; will establish that (mem e (canonicalize s)) is the same as (mem e
; s).  Suppose that is proved.  Then suppose (= s s').  That is,
; (canonicalize s) is (canonicalize s').  We must show that (mem e s)
; is (mem e s').  Use the theorem to replace each by (mem e
; (canonicalize s)) and (mem e (canonicalize s')), then substitute.

; Even though I don't need it, I will prove the following for regularity.

(defthm mem-canonicalize-1
  (equal (mem (canonicalize e) a)
         (mem e a)))

; We need to little lemmas to do the second argument.

; In the lemma below we must assume that the arguments to set-insert
; are canonical.  That is because it really compares using EQUAL.
; When we use the lemma it will be on canonicalized arguments.

(defthm mem-set-insert
  (implies (and (canonicalp d)
                (canonicalp a))
           (equal (mem e (set-insert d a))
                  (or (= e d)
                      (mem e a))))
  :hints (("Goal"
           :induct (set-insert d a))))

; Here is the second lemma.

(defthm mem-canonicalize-2
  (equal (mem e (canonicalize a))
         (mem e a)))

(defcong = equal (mem e a) 1)

(defcong = equal (mem e a) 2
  :hints (("Goal" :in-theory (disable mem-canonicalize-2)
           :use ((:instance mem-canonicalize-2
                            (e e)
                            (a a))
                 (:instance mem-canonicalize-2
                            (e e)
                            (a a-equiv))))))


; Now I repeat it for subsetp.  The first argument of subsetp is the
; harder, because we are recursing down it.  The second argument is
; easy and follows from what we already know about mem.

(defthm subsetp-set-insert-1
  (implies (and (canonicalp e)
                (canonicalp a))
           (equal (subsetp (set-insert e a) b)
                  (and (mem e b)
                       (subsetp a b))))
  :hints (("Goal" :induct (set-insert e a))))

(defthm subsetp-canonicalize-1
  (equal (subsetp (canonicalize a) b)
         (subsetp a b))
  :hints (("Goal" :induct (subsetp a b))))

(defcong = equal (subsetp a b) 1
  :hints (("Goal"
           :in-theory (disable subsetp-canonicalize-1)
           :use ((:instance subsetp-canonicalize-1
                            (a a)
                            (b b))
                 (:instance subsetp-canonicalize-1
                            (a a-equiv)
                            (b b))))))

(defcong = equal (subsetp a b) 2
  :hints (("Goal" :in-theory (disable =))))

; For regularity:

(defthm subsetp-canonicalize-2
  (equal (subsetp a (canonicalize b))
         (subsetp a b)))

; Next, I will prove the key facts about subsetp.

(defthm subsetp-cons
  (implies (and (not (equal e :UR-CONS))
                (subsetp a b))
           (subsetp a (cons e b))))

(defthm subsetp-x-x
  (subsetp x x))

(in-theory (disable =))

(defthm mem-subsetp
  (implies (and (mem e a)
                (subsetp a b))
           (mem e b)))

(defthm transitivity-of-subsetp
  (implies (and (subsetp a b)
                (subsetp b c))
           (subsetp a c)))

; ----------------------------------------------------------------------------
; The Canonicality Theorem

; Finally, I want to establish the key fact about equality and subset,
; namely, that two sets are = iff they are subsets of eachother.

; If (= a b), then it is obvious that (subsetp a b) and vice versa,
; given the congruence rules above.

; Suppose therefore that (subsetp a b) and (subsetp b a).  We
; prove (= a b).  The proof relies on the fact that << is a total
; ordering.

; Proof.  Let ca and cb be (canonicalize a) and (canonicalize b).
; Observe that they are both ordinary.  By the subsetp-canonicalize-i
; lemmas we know that (subsetp ca cb) and (subsetp cb ca).  We will
; prove that (subsetp ca cb) implies (not (<< cb ca)).  Thus,
; ca equals cb.  Q.E.D.

(defthm =-is-equal
  (implies (and (canonicalp x)
                (canonicalp y))
           (equal (= x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (enable =))))

; I do not want to further encumber << with another rule.  But this
; is an important fact and I will :use it.

(defthm mem-<<
  (implies (and (canonicalp e)
                (canonicalp a)
                (mem e a))
           (<< e a))
  :rule-classes nil
  :hints (("Goal" :in-theory (slow-<<-rules <<))))

(defthm not-mem-e-e
  (not (mem e e))
  :hints (("Goal"
           :use (:instance MEM-<<
                           (e (canonicalize e))
                           (a (canonicalize e))))))

; This rule seems overly expensive so I keep it disabled most of the time.

(defthm mem-container
  (implies (mem e a)
           (not (mem a e)))
  :hints (("Goal"
           :use ((:instance mem-<<
                            (e (canonicalize e))
                            (a (canonicalize a)))
                 (:instance mem-<<
                            (a (canonicalize e))
                            (e (canonicalize a)))))))

(in-theory (disable mem-container))

(defthm mem-implies-not-<<-car
  (implies (and (canonicalp e)
                (canonicalp a)
                (mem e a))
           (not (<< (car a) e)))
  :hints (("Goal" :in-theory (slow-<<-rules <<))))

(defthm <<-cons
  (implies (and (canonicalp e)
                (canonicalp a)
                (mem e a))
           (equal (<< a (cons e z))
                  (if (equal (car a) e)
                      (<< (cdr a) z)
                    nil)))
  :hints (("Goal" :in-theory (enable <<) ; (fast-<<-rules <<)
           )))

(defthm subsetp-cons-reversed
  (implies (and (subsetp a (cons e b))
                (not (equal e :UR-CONS))
                (not (mem e a)))
           (subsetp a b)))

(defthm yucko
  (implies (and (canonicalp a)
                (canonicalp b)
                (subsetp a b)
                (mem (car b) a))
           (equal (car a) (car b)))
  :rule-classes nil)

(defthm subsetp-<<
  (implies (and (setp a)
                (setp b)
                (canonicalp a)
                (canonicalp b)
                (subsetp a b))
           (not (<< b a)))
  :rule-classes nil
  :hints (("Goal" :induct (<< b a))
          ("Subgoal *1/5.3"
           :use (:instance yucko
                           (a (cdr a))
                           (b b)))
          ("Subgoal *1/4''" :in-theory (enable <<) ; (fast-<<-rules <<)
           )))

(defthm setp-canonicalize
  (implies (setp x)
           (setp (canonicalize x))))

; The Canonalicality Theorem:
(defthm =-iff-subsetps
  (implies (and (setp a)
                (setp b))
           (iff (= a b)
                (and (subsetp a b)
                     (subsetp b a))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory (union-theories '(=)
                               (disable subsetp-canonicalize-1
                                        subsetp-canonicalize-2
                                        canonicalize
                                        setp
                                        transitivity-of-subsetp))

    :use ((:instance subsetp-canonicalize-1
                     (a a)
                     (b b))
          (:instance subsetp-canonicalize-2
                     (a (canonicalize a))
                     (b b))
          (:instance subsetp-canonicalize-1
                     (a b)
                     (b a))
          (:instance subsetp-canonicalize-2
                     (a (canonicalize b))
                     (b a))
          (:instance subsetp-<<
                     (a (canonicalize a))
                     (b (canonicalize b)))
          (:instance subsetp-<<
                     (a (canonicalize b))
                     (b (canonicalize a)))))))

; Now we disable those of the above rules that we don't think are
; worth their cost.

(in-theory (disable =-is-equal
                    mem-implies-not-<<-car
                    <<-cons))

;----------------------------------------------------------------------------
; = Refines iff and is a Congruence for Many ACL2 Functions


(defcong = equal (canonicalize x) 1
  :hints (("Goal" :in-theory (enable =))))

(defthm canonicalize-=
  (= (canonicalize x) x)
  :hints (("Goal" :in-theory (enable =))))

(defthm canonicalize-non-nil
  (iff (canonicalize x) x)
  :hints (("Goal" :in-theory (enable ur-elementp))))

(defrefinement = iff
  :hints (("Goal" :in-theory (enable =))))

(defthm canonicalize-fix
  (equal (canonicalize (fix x))
         (fix (canonicalize x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable ur-elementp))))

(defthm <-fixes
  (equal (< x y) (< (fix x) (fix y)))
  :rule-classes nil)

(defcong = equal (< x y) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance <-fixes
                            (x x)
                            (y y))
                 (:instance <-fixes
                            (x x-equiv)
                            (y y))
                 (:instance canonicalize-fix
                            (x x))
                 (:instance canonicalize-fix
                            (x x-equiv))))))

(defcong = equal (< x y) 2
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance <-fixes
                            (x x)
                            (y y))
                 (:instance <-fixes
                            (x x)
                            (y y-equiv))
                 (:instance canonicalize-fix
                            (x y))
                 (:instance canonicalize-fix
                            (x y-equiv))))))

(defthm +-fixes
  (equal (+ x y) (+ (fix x) (fix y)))
  :rule-classes nil)

(defcong = equal (+ x y) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance +-fixes
                            (x x)
                            (y y))
                 (:instance +-fixes
                            (x x-equiv)
                            (y y))
                 (:instance canonicalize-fix
                            (x x))
                 (:instance canonicalize-fix
                            (x x-equiv))))))

(defcong = equal (+ x y) 2
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance +-fixes
                            (x x)
                            (y y))
                 (:instance +-fixes
                            (x x)
                            (y y-equiv))
                 (:instance canonicalize-fix
                            (x y))
                 (:instance canonicalize-fix
                            (x y-equiv))))))

(defthm --fixes
  (equal (- x) (- (fix x)))
  :rule-classes nil)

(defcong = equal (- x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance --fixes
                            (x x))
                 (:instance --fixes
                            (x x-equiv))
                 (:instance canonicalize-fix
                            (x x))
                 (:instance canonicalize-fix
                            (x x-equiv))))))


(defthm *-fixes
  (equal (* x y) (* (fix x) (fix y)))
  :rule-classes nil)

(defcong = equal (* x y) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance *-fixes
                            (x x)
                            (y y))
                 (:instance *-fixes
                            (x x-equiv)
                            (y y))
                 (:instance canonicalize-fix
                            (x x))
                 (:instance canonicalize-fix
                            (x x-equiv))))))

(defcong = equal (* x y) 2
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =) '(fix))
           :use ((:instance *-fixes
                            (x x)
                            (y y))
                 (:instance *-fixes
                            (x x)
                            (y y-equiv))
                 (:instance canonicalize-fix
                            (x y))
                 (:instance canonicalize-fix
                            (x y-equiv))))))

(defthm integerp-canonicalize
  (equal (integerp (canonicalize x))
         (integerp x)))

(defthm rationalp-canonicalize
  (equal (rationalp (canonicalize x))
         (rationalp x)))

(defthm symbolp-canonicalize
  (equal (symbolp (canonicalize x))
         (symbolp x)))

(defthm stringp-canonicalize
  (equal (stringp (canonicalize x))
         (stringp x)))

(defthm characterp-canonicalize
  (equal (characterp (canonicalize x))
         (characterp x)))

(defthm consp-canonicalize
  (equal (consp (canonicalize x))
         (consp x))
  :hints (("Goal" :in-theory (enable ur-elementp))))

(defcong = equal (integerp x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =)
                                               '(integerp-canonicalize))
           :use ((:instance integerp-canonicalize
                            (x x))
                 (:instance integerp-canonicalize
                            (x x-equiv))))))

(defcong = equal (rationalp x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =)
                                               '(rationalp-canonicalize))
           :use ((:instance rationalp-canonicalize
                            (x x))
                 (:instance rationalp-canonicalize
                            (x x-equiv))))))

(defcong = equal (symbolp x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =)
                                               '(symbolp-canonicalize))
           :use ((:instance symbolp-canonicalize
                            (x x))
                 (:instance symbolp-canonicalize
                            (x x-equiv))))))

(defcong = equal (stringp x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =)
                                               '(stringp-canonicalize))
           :use ((:instance stringp-canonicalize
                            (x x))
                 (:instance stringp-canonicalize
                            (x x-equiv))))))

(defcong = equal (consp x) 1
  :hints (("Goal"
           :in-theory (set-difference-theories (enable =)
                                               '(consp-canonicalize))
           :use ((:instance consp-canonicalize
                            (x x))
                 (:instance consp-canonicalize
                            (x x-equiv))))))


; We do not get (defcong = equal (characterp x) 1) because we
; canonicalize non-standard atoms to (code-char 255).

; ----------------------------------------------------------------------------
; Codified Theorem Proving Strategies

; The following all turn into the corresponding defthms:
; (defx name term)
; (defx name term :hints ... :rule-classes ...)

; But if you write
; (defx ...a... :strategy xxx ...b...)
; it macro expands to
; (xxx  ...a... ...b...)

; Thus, if you want to codify a new theorem proving strategy xxx, you can
; defmacro xxx and then write (defx ... :strategy xxx ...).

; The main point of this is to let me write defx events and introduce
; new strategies as I go.  Also, I can name my strategies without
; including ``def'' in front of them and still search for ``(def...''
; when looking for things.

(defun packn-in-pkg (lst pkg-witness)
  (declare (xargs :mode :program))
  (acl2::intern-in-package-of-symbol (coerce (acl2::packn1 lst) 'string)
                                     pkg-witness))

(defmacro defx (&rest args)
  (let ((temp (member :strategy args)))

; We allow the strategy to be a keyword, in which case we convert it
; to the corresponding symbol in this package.  If the strategy is not
; a keyword, it is used as supplied.

    (cond
     (temp
      `(,(if (keywordp (cadr temp))
             (packn-in-pkg (list (symbol-name (cadr temp))) 'defx)
           (cadr temp))
        ,@(butlast args (length temp))
        ,@(cddr temp)))
     (t `(defthm ,@args)))))

; ----------------------------------------------------------------------------
; Proving Congruences

; There are two common ways to prove congruence rules in this theory.

; (1) The :canonicalize strategy: prove that (fn (canonicalize x)) is
; (fn x).  This is generally used if fn returns an ur-element (as
; opposed to a set).

; (2) The :subsetp stragegy: prove that (subsetp a1 a2) implies
; (subsetp (fn a1) (fn a2)).  This is generally used if fn returns a
; set.

(defun genname1 (name n avoid)
  (declare (xargs :mode :program))
  (let ((new-name (packn-in-pkg (list name n) name)))
    (cond ((acl2::member-equal new-name avoid)
           (genname1 name (+ 1 n) avoid))
          (t new-name))))

(defun genname (name avoid)
  (declare (xargs :mode :program))
  (cond ((acl2::member-equal name avoid)
         (genname1 name 1 avoid))
        (t name)))

(defun put-nth (e n lst)
  (cond ((zp n) (cons e (cdr lst)))
        (t (cons (car lst) (put-nth e (- n 1) (cdr lst))))))

; And here is the macro

(defmacro congruence (expr n &key method)
  (cond
   ((eq method :canonicalize)
    (let* ((fn (car expr))
           (vars (cdr expr))
           (x (nth (- n 1) vars))
           (name1
            (packn-in-pkg (list fn "-SET-INSERT") fn))
           (name2
            (packn-in-pkg (list fn "-CANONICALIZE") fn))
           (vars1 (acl2::remove1-eq x vars)) ; Matt K. mod from delete1-eq, v2-9-4
           (e (genname 'e vars1))
           (a (genname x vars1))
           (x-equiv (packn-in-pkg (list x "-EQUIV") x)))
      `(encapsulate
        nil
        (local (in-theory (enable scons scar scdr ur-elementp)))

        (defthm ,name1
          (implies (and (canonicalp ,e)
                        (canonicalp ,a))
                   (equal (,fn ,@(put-nth `(set-insert ,e ,a)
                                          (- n 1)
                                          vars))
                          (,fn ,@(put-nth `(cons ,e ,a)
                                          (- n 1)
                                          vars))))
          :hints (("Goal"
                   :induct (set-insert ,e ,a)

; Note that the following in-theory is commented out!  I learned that
; if you enable = during these proofs it is generally slower.  So I
; don't.
;                  :in-theory (enable =)


                   )))

        (defthm ,name2
          (equal (,fn ,@(put-nth `(canonicalize ,x)
                                 (- n 1)
                                 vars))
                 (,fn ,@vars)))

        (defcong = equal ,expr ,n
          :hints
          (("Goal"
            :in-theory (disable ,name2)
            :use ((:instance ,name2 (,x ,x))
                  (:instance ,name2
                             (,x ,x-equiv)))))))))
   ((eq method :subsetp)
    (let* ((fn (car expr))
           (vars (cdr expr))
           (x (nth (- n 1) vars))
           (name1
            (packn-in-pkg (list "SUBSETP-" fn "-" fn) fn))
           (vars1 (acl2::remove1-eq x vars)) ; Matt K. mod from delete1-eq, v2-9-4
           (a1 (genname1 x 1 vars1))
           (a2 (genname1 x 2 (cons a1 vars1)))
           (x-equiv (packn-in-pkg (list x "-EQUIV") x)))
      `(encapsulate
        nil
        (defthm ,name1
          (implies (subsetp ,a1 ,a2)
                   (subsetp (,fn ,@(put-nth a1 (- n 1) vars))
                            (,fn ,@(put-nth a2 (- n 1) vars)))))

        (defcong = = ,expr ,n
          :hints (("Goal"
                   :use (:instance =-iff-subsetps
                                   (a ,expr)
                                   (b (,fn ,@(put-nth x-equiv
                                                      (- n 1)
                                                      vars))))))))))
   ((eq method nil)
    `(defcong = = ,expr ,n))
   (t `(acl2::er acl2::soft 'congruence
                 "The :method ~x0 is unknown."
                 ',method))))

; ----------------------------------------------------------------------------
; The User Level Theory

(in-theory (disable scons scar scdr ur-elementp))

; ----------------------------------------------------------------------------
; Set Union

(defun union (a b)
  (if (ur-elementp a)
      (sfix b)
    (scons (scar a)
           (union (scdr a) b))))

; My next goal is to prove both

; (defcong = = (union a b) 1)
; (defcong = = (union a b) 2)

; The first of these is problematic but the second is easy.
; Generally, if the congruence rule is in a slot that is held fixed in
; the recursion (as in the second case above), the proof is an easy
; induction, using congruence rules for the subfunctions.  But if the
; congruence rule is in a controller slot, you generally need lemmas.

(defthm mem-union
  (equal (mem e (union a b))
         (or (mem e a)
             (mem e b))))

(defthm subsetp-scons
  (implies (subsetp a b)
           (subsetp a (scons e b))))

(defthm subsetp-union-1
  (subsetp a (union a b)))

(defthm subsetp-union-2
  (subsetp a (union b a)))

(defthm subsetp-union
  (implies (subsetp a1 a2)
           (subsetp (union a1 b)
                    (union a2 b))))
(defthm setp-union
  (setp (union a b)))

(defx :strategy :congruence (union a b) 1 :method :subsetp)

(defx :strategy :congruence (union a b) 2)

(defthm union-right-id
  (implies (ur-elementp b)
           (= (union a b) (sfix a))))

(defthm union-scons
  (= (union a (scons e b))
     (scons e (union a b))))

(defthm commutativity-of-union
  (= (union a b) (union b a)))

(defthm ur-elementp-union
  (equal (ur-elementp (union a b))
         (and (ur-elementp a)
              (ur-elementp b))))

(defthm associativity-of-union
  (= (union (union a b) c)
     (union a (union b c))))


; ----------------------------------------------------------------------------
; Set Intersection

(defun intersection (a b)
  (if (ur-elementp a)
      nil
    (if (mem (scar a) b)
        (scons (scar a)
               (intersection (scdr a) b))
      (intersection (scdr a) b))))

(defthm mem-intersection
  (equal (mem e (intersection a b))
         (and (mem e a)
              (mem e b))))

(defthm subsetp-intersection-1
  (subsetp (intersection a b) a))

(defthm subsetp-intersection-2
  (subsetp (intersection b a) a))

(defthm subsetp-intersection
  (implies (subsetp a1 a2)
           (subsetp (intersection a1 b)
                    (intersection a2 b))))

(defthm setp-intersection
  (setp (intersection a b)))

(defx :strategy :congruence (intersection a b) 1 :method :subsetp)
(defx :strategy :congruence (intersection a b) 2)

(defthm intersection-right-id
  (implies (ur-elementp b)
           (= (intersection a b) nil)))

(defthm scons-id
  (implies (mem e a)
           (= (scons e a) a)))

(defthm intersection-scons
  (= (intersection a (scons e b))
     (if (mem e a)
         (scons e (intersection a b))
       (intersection a b))))

(defthm commutativity-of-intersection
  (= (intersection a b) (intersection b a)))

(defthm associativity-of-intersection
  (= (intersection (intersection a b) c)
     (intersection a (intersection b c))))

; ----------------------------------------------------------------------------
; Arithmetic

(include-book "../../../../../arithmetic/top-with-meta")


(defun cardinality (a)
  (if (ur-elementp a)
      0
    (if (mem (scar a) (scdr a))
        (cardinality (scdr a))
      (+ 1 (cardinality (scdr a))))))

(defx :strategy :congruence (cardinality a) 1 :method :canonicalize)

(defthm cardinality-union-2
  (<= (cardinality b) (cardinality (union a b)))
  :rule-classes :linear)

; Observe that we proved the easy case first, by induction on b,
; and then we prove the other case by commutativity.

(defthm cardinality-union-1
  (<= (cardinality b) (cardinality (union b a)))
  :rule-classes :linear)

(defthm cardinality-union-3
  (<= (cardinality (union a b))
      (+ (cardinality a)
         (cardinality b)))
  :rule-classes :linear)

(defthm cardinality-0
  (equal (equal (cardinality a) 0)
         (ur-elementp a)))

(defthm cardinality-non-0
  (implies (mem e x)
           (< 0 (cardinality x)))
     :rule-classes :linear)

(defthm cardinality-intersection-1
  (<= (cardinality (intersection a b)) (cardinality a))
  :rule-classes :linear)

(defthm cardinality-intersection-2
  (<= (cardinality (intersection b a)) (cardinality a))
  :rule-classes :linear)

(defthm cardinality-scons
  (equal (cardinality (scons e a))
         (if (mem e a)
             (cardinality a)
           (+ 1 (cardinality a)))))

(defthm cardinality-disjoint-union
  (implies (not (intersection a b))
           (= (cardinality (union a b))
              (+ (cardinality a)
                 (cardinality b)))))


; ----------------------------------------------------------------------------
; Choose

(defun choose (a)
  (car (sfix (canonicalize a))))

(defx :strategy :congruence (choose a) 1)

(defthm ur-elementp-canonicalize
  (equal (ur-elementp (canonicalize x))
         (ur-elementp x)))

(defthm mem-choose-lemma
  (equal (mem (car (canonicalize a)) a)
         (not (ur-elementp a)))
  :hints (("Goal"
           :in-theory (enable scar scdr ur-elementp))))

(defthm mem-choose
  (equal (mem (choose a) a)
         (not (ur-elementp a))))

; One might think that the following follows from the previous
; theorems about choose.  But that is not correct.  For example,
; (choose {1 2 3}) might be 2 but (choose {2 3}) might be 3.  This
; property is due to the fact that choose is really the biggest
; element of the set.

(defthm car-canonicalize-ur-cons
  (equal (equal (car (canonicalize a)) :UR-CONS)
         (and (consp a)
              (equal (car a) :UR-CONS)))
  :hints (("Goal" :in-theory (enable ur-elementp))))

(defthm choose-scons
  (implies (not (= (choose (scons e a)) e))
           (= (choose (scons e a)) (choose a)))
  :hints (("Goal"
           :in-theory
           (enable = scons ur-elementp))))

(defthm choose-singleton
  (= (choose (scons e nil)) e)
  :hints (("Goal" :in-theory (enable = scons ur-elementp))))

(in-theory (disable choose))

(defthm elim-choose-singleton
  (implies (equal (cardinality x) 1)
           (= (scons (choose x) nil) x)))

(defthm mem-singleton
  (implies (and (equal (cardinality x) 1)
                (mem e x))
           (= (scons e nil) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable elim-choose-singleton)
                  :use elim-choose-singleton)))

(defthm choose-ur-elementp
  (implies (ur-elementp x)
           (= (choose x) nil))
  :hints (("Goal" :in-theory (enable choose ur-elementp sfix))))


; ----------------------------------------------------------------------------
; Set Difference

(defun diff (a b)
  (cond ((ur-elementp a)
         nil)
        ((mem (scar a) b)
         (diff (scdr a) b))
        (t (scons (scar a)
                  (diff (scdr a) b)))))

(defthm mem-diff
  (equal (mem e (diff a b))
         (and (mem e a)
              (not (mem e b)))))

(defthm subsetp-diff-1
  (subsetp (diff a b) a))

(defthm subsetp-diff
  (implies (subsetp a1 a2)
           (subsetp (diff a1 b)
                    (diff a2 b))))

(defthm setp-diff
  (setp (diff a b)))

(defx :strategy :congruence (diff a b) 1 :method :subsetp)
(defx :strategy :congruence (diff a b) 2)

(defthm diff-right-id
  (implies (ur-elementp b)
           (= (diff a b) (sfix a))))

(defthm cardinality-diff-singleton
  (equal (cardinality (diff y (scons x nil)))
         (if (mem x y)
             (- (cardinality y) 1)
           (cardinality y))))

(defthm cardinality-diff
  (<= (cardinality (diff a b)) (cardinality a))
  :rule-classes :linear)

(defthm diff-nil
  (implies (subsetp x y)
           (= (diff x y) nil)))

(defthm diff-scons
  (implies (not (mem e s))
           (= (diff s (scons e y)) (diff s y))))

(encapsulate nil
             (local
              (defthm scons-x-diff-x
                (implies (mem x s)
                         (= (scons x (diff s (scons x nil))) s))
                :hints (("Subgoal *1/3'5'"
                         :cases ((mem sr sr0))))))

             (defthm scons-diff-scons
               (= (scons e (diff a (scons e nil)))
                  (scons e a))
               :hints (("Goal" :cases ((mem e a))))))

(defthm elim-choose-doubleton
  (implies (equal (cardinality x) 2)
           (= (scons (choose x)
                     (scons (choose (diff x (scons (choose x) nil)))
                            nil))
              x)))

(defthm subsetp-diff-1-corrollary
  (implies (subsetp a b)
           (subsetp (diff a c) b)))

(defthm subsetp-not-subsetp-trick
  (implies (and (subsetp a b)
                (not (subsetp a (scdr b))))
           (mem (scar b) a)))

(defthm intersection-diff-2
  (= (intersection a (diff b c))
     (diff (intersection a b) c)))

(defthm intersection-diff-1
  (= (intersection (diff b c) a)
     (diff (intersection a b) c)))

; There are others, but I am not going to prove them now.

; ----------------------------------------------------------------------------
; Ordered Pairs as Sets

; It is possible to provide ordered pairs as ur-elements.  For example
; we could define (pair x y) to be (list :UR-CONS (cons x y)).  But here
; we develop the classical treatment of ordered pairs.

(defun pair (x y)
  (brace x (brace x y)))

; Observe that a pair necessarily has cardinality 2.  But the larger
; element need not have cardinality 2.  For example, (pair x x) is
; {x {x}}.

; We must be able to determine whether a set of cardinality 2 is a
; pair.  Call the two elements x and y.  Then either (mem x y) or (mem
; y x).  Furthermore, the larger must be of cardinality 2 or less.  To
; code this up, we have to have a way of finding ``the two elements''
; of a set, a, of cardinality 2, when a is not necessarily in
; canonical form.  E.g., (1 (1 2)) is a pair but so is (1 1 (2 1) (1
; 2)).  At first, I wanted to avoid canonicalizing the set, for
; efficiency reasons.

; Here was my first attempt to extract ``the other'' element of a
; set of cardinality 2.

; (defun find-other (e s)
; ; Find the first element of s that is not e.
;   (cond ((ur-elementp s) nil)
;         ((= e (scar s)) (find-other e (scdr s)))
;         (t (scar s))))

; Unfortunately, this function does not admit = as a congruence in
; the second argument.  For example (find-other 1 '(1 2 3)) and
; (find-other 1 '(1 3 2)) return different things, even though their
; arguments are =.  (It would admit it if we limited s to sets of
; cardinality 2, but we can't.)

; So I have decided simply use the classical approach in terms of
; choose.  If the first element of a pair is a number, this is not too
; expensive.

(defun pairp (a)
  (if (equal (cardinality a) 2)
      (let* ((x (choose a))
             (y (choose (diff a (brace x)))))
        (or (and (mem x y)
                 (<= (cardinality y) 2))
            (and (mem y x)
                 (<= (cardinality x) 2))))
    nil))

(defun hd (a)
  (cond ((pairp a)
         (let* ((x (choose a))
                (y (choose (diff a (brace x)))))
           (if (mem x y)
               x
             y)))
        (t nil)))

(defun tl (a)
  (cond ((pairp a)
         (let* ((x (choose a))
                (y (choose (diff a (brace x)))))
           (if (mem x y)
               (if (equal (cardinality y) 1)
                   x
                 (choose (diff y (brace x))))
             (if (equal (cardinality x) 1)
                   y
                 (choose (diff x (brace y)))))))
        (t nil)))

(defthm setp-pair
  (setp (pair x y)))

(defcong = = (pair a b) 1)
(defcong = = (pair a b) 2)
(defcong = equal (pairp a) 1)
(defcong = = (hd a) 1)
(defcong = = (tl a) 1)

(in-theory (enable mem-container))

(defthm hd-pair
  (= (hd (pair x y)) x))

(defthm tl-pair
  (= (tl (pair x y)) y))

(defthm pairp-pair
  (pairp (pair x y))
  :rule-classes (:type-prescription :generalize))

(defthm pairp-implies-setp
  (implies (pairp x) (setp x)))

(encapsulate
 nil

; Our goal here is to prove

; (implies (pairp a)
;          (= (pair (hd a) (tl a)) a))

; We have to give the proof pretty explicitly.  It exploits the fact
; that we know how to represent singleton and doubleton sets in terms
; of choose.  Since we have to use these lemmas explicitly, we disable
; them.

 (local (in-theory (disable elim-choose-doubleton
                            elim-choose-singleton)))

; To make the proof easier to understand, we give names to certain
; expressions.  In the definitions of pair, hd and tl, we use two
; local variables,

; (let* ((x (choose a))
;        (y (choose (diff a (brace x)))))
;       ...)

; Here we define functions corresponding to their values.

 (local (defun x (a) (choose a)))
 (local (defun y (a) (choose (diff a (brace (x a))))))

; Given that a is known to be a pairp, there are four cases, depending
; on which of x and y is an element of the other and whether the
; cardinality of the bigger is 1 or 2.  We will prove the main goal
; for each of the four cases.

 (local
  (defthm case-1
    (implies (and (mem (x a) (y a))
                  (equal (cardinality (y a)) 2)
                  (pairp A))
             (= (pair (hd A) (tl A)) A))
    :hints
    (("Goal"
      :use
      (

; Proof of Case 1:

; (i) Represent A as a doubleton in terms of choose.

       (:instance elim-choose-doubleton (x A))

; (ii) Represent y as a doubleton.

       (:instance elim-choose-doubleton (x (y a)))

; (iii) When x is removed from y, the result is a singleton, which can
; be represented with choose.

       (:instance elim-choose-singleton
                  (x (diff (y a) (scons (x a) nil))))

; (iv) If x is a member of a singleton set, the set is {x}.

       (:instance mem-singleton
                  (e (x a))
                  (x (diff (y a) (scons (x a) nil)))))))))

 (local
  (defthm case-2
    (implies (and (mem (x a) (y a))
                  (equal (cardinality (y a)) 1)
                  (pairp A))
             (= (pair (hd A) (tl A)) A))
    :hints
    (("Goal"
      :use
      (

; Proof of Case 2:

; (i) Represent A as a doubleton in terms of choose.

       (:instance elim-choose-doubleton (x A))

; (ii) Represent y as a singleton.

       (:instance elim-choose-singleton (x (y a)))

; (iii) If x is a member of singleton set, the set is {x}.

       (:instance mem-singleton
                  (e (x a))
                  (x (y a))))))))

; Cases 3 and 4 are symmetric with Cases 1 and 2, interchanging the
; roles of x and y.

 (local
  (defthm case-3
    (implies (and (mem (y a) (x a))
                  (equal (cardinality (x a)) 2)
                  (pairp A))
             (= (pair (hd A) (tl A)) A))
    :hints
    (("Goal"
      :use
      ((:instance elim-choose-doubleton (x A))
       (:instance elim-choose-doubleton (x (x a)))
       (:instance elim-choose-singleton
                  (x (diff (x a) (scons (y a) nil))))
       (:instance mem-singleton
                  (e (y a))
                  (x (diff (x a) (scons (y a) nil)))))))))

 (local
  (defthm case-4
    (implies (and (mem (y a) (x a))
                  (equal (cardinality (x a)) 1)
                  (pairp A))
             (= (pair (hd A) (tl A)) A))
    :hints
    (("Goal"
      :use
      ((:instance elim-choose-doubleton (x A))
       (:instance elim-choose-singleton (x (x a)))
       (:instance mem-singleton
                  (e (y a))
                  (x (x a))))))))

 (defthm pair-hd-tl
   (implies (pairp A)
            (= (pair (hd A) (tl A)) A))
   :hints
   (("Goal" :in-theory (disable pair hd tl)
     :cases ((and (mem (x a) (y a))                     ;;; Case 1
                  (equal (cardinality (y a)) 2))
             (and (mem (x a) (y a))                     ;;; Case 2
                  (equal (cardinality (y a)) 1))
             (and (mem (y a) (x a))                     ;;; Case 3
                  (equal (cardinality (x a)) 2))
             (and (mem (y a) (x a))                     ;;; Case 4
                  (equal (cardinality (x a)) 1)))))
   :rule-classes (:rewrite :elim)))

(in-theory (disable mem-container))

(in-theory (disable pairp pair hd tl))

(defthm equal-booleans
  (implies (and (acl2::booleanp p)
                (acl2::booleanp q))
           (equal (equal p q)
                  (iff p q))))

(defthm equal-pair
  (equal (= (pair x1 y1)
            (pair x2 y2))
         (and (= x1 x2)
              (= y1 y2)))
  :hints
  (("Goal" :in-theory (disable hd-pair tl-pair)
    :use ((:instance hd-pair (x x1) (y y1))
          (:instance hd-pair (x x2) (y y2))
          (:instance tl-pair (x x1) (y y1))
          (:instance tl-pair (x x2) (y y2))))))

(in-theory (disable equal-booleans))

(defthm equal-pair-generalized
  (equal (= (pair x1 x2) y)
         (and (pairp y)
              (= x1 (hd y))
              (= x2 (tl y)))))

(in-theory (disable equal-pair-generalized))



; ----------------------------------------------------------------------------
; Functions as Sets

; The following is an example of set comprehension.  In particular, it
; is

; { x in s | (and (pairp x) (= e (hd x)))}

(defun subset-such-that1 (s e)
  (cond ((ur-elementp s) nil)
        ((and (pairp (scar s))
              (= e (hd (scar s))))
         (scons (scar s) (subset-such-that1 (scdr s) e)))
        (t (subset-such-that1 (scdr s) e))))

; When such a function is defined we should immediately prove the
; obvious three relationships:

(defthm setp-subset-such-that1
  (setp (subset-such-that1 a e)))

(defthm mem-subset-such-that1
  (iff (mem pair (subset-such-that1 a x))
       (and (pairp pair)
            (mem pair a)
            (= (hd pair) x)))
  :hints (("Goal" :do-not '(generalize))))

(defthm subsetp-subset-such-that1
  (subsetp (subset-such-that1 a x) a))

; The congruence rules are easy.

(defx :strategy :congruence (subset-such-that1 a e) 1 :method :subsetp)
(defx :strategy :congruence (subset-such-that1 a e) 2)

(defthm mem-subset-such-that1-corrollary
  (implies (and (subsetp a (subset-such-that1 f x))
                (mem e a))
           (and (pairp e)
                (= (hd e) x))))

; Now we define apply:

(defun apply (s e)
  (tl (choose (subset-such-that1 s e))))

(defcong = = (apply s e) 1)
(defcong = = (apply s e) 2)

(defun except (s e v)
  (scons (pair e v)
         (diff s (subset-such-that1 s e))))

(defcong = = (except s e v) 1)
(defcong = = (except s e v) 2)
(defcong = = (except s e v) 3)

(defthm diff-scons-1
  (implies (acl2::syntaxp (not (equal b ''nil)))
           (= (diff a (scons e b))
              (diff (diff a b) (brace e)))))

(defthm ur-elementp-diff
  (iff (ur-elementp (diff a b))
       (subsetp a b)))

(defthm subset-such-that1-diff-subset-such-that-1
    (= (subset-such-that1 (diff f (subset-such-that1 f x)) y)
       (if (= x y)
           nil
         (subset-such-that1 f y))))

(encapsulate
 nil
 (local
  (defthm lemma2
    (implies (and (subsetp f (subset-such-that1 g x))
                  (not (= x y)))
             (= (subset-such-that1 f y)
                nil))))

 (defthm apply-except
   (= (apply (except f x v) y)
      (if (= x y)
          v
        (apply f y)))))

(defthm mem-except
  (equal (mem e (except f x v))
         (if (pairp e)
             (if (= (hd e) x)
                 (= (tl e) v)
               (mem e f))
           (mem e f))))

(defthm subsetp-except
  (iff (subsetp (except f x v) g)
       (and (mem (pair x v) g)
            (subsetp (diff f (subset-such-that1 f x))
                     g))))

(defthm ur-elementp-except
  (not (ur-elementp (except f x v))))

(in-theory (disable apply except))

(defmacro func* (&rest args)
  (cond ((endp args) nil)
        ((endp (cdr args)) (car args))
        (t `(except (func* ,@(cdr args))
                    ,(car (car args))
                    ,(cadr (car args))))))

(defmacro func (&rest args)
  `(func* ,@args nil))


; ----------------------------------------------------------------------------
; Sets of ordered pairs.

; This is really just a simple map over a checking a predicate.  I
; need to automate this sort of thing but I will do it by hand right
; now.

(defun pairsp (a)
  (cond ((ur-elementp a) t)
        (t (and (pairp (scar a))
                (pairsp (scdr a))))))

(defx :strategy :congruence (pairsp a) 1 :method :canonicalize)

(defthm pairsp-union
  (equal (pairsp (union a b))
         (and (pairsp a)
              (pairsp b))))

(defthm pairsp-diff
  (implies (pairsp a)
           (pairsp (diff a b))))

; This one is more useful when dealing with sets created by EXCEPT.

(defthm pairsp-diff-subset-such-that1
  (equal (pairsp (diff a (subset-such-that1 b x)))
         (pairsp a)))

(defthm pairsp-scons
  (equal (pairsp (scons e a))
         (and (pairp e)
              (pairsp a))))

(defthm mem-pairsp
  (implies (and (mem e f)
                (pairsp f))
           (pairp e)))

(defthm pairsp-subset-such-that1
  (implies (pairsp f)
           (pairsp (subset-such-that1 f x))))

(defthm nil-not-mem-pairsp
  (implies (pairsp f)
           (not (mem nil f))))

; ----------------------------------------------------------------------------
; Recognizing Functions

; The basic idea is to define the predicate that recognizes when a set
; is both pairsp and has unique hds.  We've got the first part.  The
; second part is called functionp1.

; Here is my first functionp1.  It does not insure that every element
; of f is a pair.  Thus,

; (functionp1 (brace (pair 1 2)) (brace (pair 1 2) 3)) = t

; Second, it is fragile in the sense that if a is not a subset of f, it
; fails, e.g.,

; (functionp1 (brace (pair 1 2)) (brace (pair 3 4))) = nil

; This is not a problem at the top level, where a is f.  But in stating
; theorems about functionp1 it would be convenient to allow arbitrary a
; with sensible results.

; (defun functionp1 (a f)
;   (cond ((ur-elementp a) t)
;         (t (and (pairp (scar a))
;                 (equal (cardinality (subset-such-that1 f (hd (scar a)))) 1)
;                 (functionp1 (scdr a) f)))))

; So here is my second:

(defun functionp1 (a f)
  (cond ((ur-elementp a) t)
        (t (and (<= (cardinality (subset-such-that1 f (hd (scar a)))) 1)
                (functionp1 (scdr a) f)))))

(defx :strategy :congruence (functionp1 a f) 1 :method :canonicalize)
(defcong = equal (functionp1 a f) 2)


; Is 8 a function?  I say no.  The reason I say no, is that I want it
; to be the case that two functions are equal iff apply gives the same
; answers on both.  But if I defined a function as (and (pairsp f)
; (functionp1 f f)) then 8 is a functionp, because every element of 8
; is a pair and their hds are unique.

(defun functionp (f)
  (if (ur-elementp f)
      (= f nil)
    (and (pairsp f)
         (functionp1 f f))))

(defcong = equal (functionp f) 1)

; My next goal is to prove that functionp is preserved by EXCEPT.
; I need some lemmas about functionp1

(defthm cardinality-subset-such-that1
  (<= (cardinality (subset-such-that1 f x))
      (cardinality f))
  :rule-classes :linear)

(defun simultaneously (a b)
  (declare (xargs :measure (cardinality a)))
  (cond ((ur-elementp a) b)
        (t (simultaneously (diff a (brace (scar a)))
                           (diff b (brace (scar a)))))))

(defthm cardinality-subsetp
  (implies (subsetp a b)
           (<= (cardinality a)
               (cardinality b)))
  :hints (("Goal" :induct (simultaneously a b)))
  :rule-classes :linear)



; The next two theorems are not used until later, but they seem
; natural to have around.

(defthm functionp1-subsetp-2
  (implies (and (functionp1 a g)
                (subsetp f g))
           (functionp1 a f))
  :hints
  (("Subgoal *1/4'"
    :in-theory (disable cardinality-subsetp)
    :use (:instance cardinality-subsetp
                    (a (SUBSET-SUCH-THAT1 F (HD (SCAR A))))
                    (b (SUBSET-SUCH-THAT1 G (HD (SCAR A))))))))

(defthm functionp1-diff
  (implies (functionp1 a f)
           (functionp1 a (diff f b)))
  :hints (("Goal" :in-theory (disable subsetp-diff-1)
           :use (:instance subsetp-diff-1
                           (a f)
                           (b b)))))

; Consider the goal (implies (functionp f) (functionp f')), where f'
; is (except f x v).  Ignoring the pairsp part, this opens into

; (implies (functionp1 f f) (functionp1 f' f'))

; We have to break both duplications.  Each requires a lemma.  Then
; we put the two lemmas together to get something like:

; (implies (functionp1 b f) (functionp1 a f'))

; where (subsetp a b).

; Here is one of the two ``breakers.''

(defthm functionp1-subsetp-1
  (implies (and (subsetp a b)
                (functionp1 b f))
           (functionp1 a f))
  :hints (("Goal" :do-not '(generalize))))

(encapsulate
 nil

; This is the other ``breaker''.  The scons below is f', i.e., the
; expansion of (except f x v).

 (local
  (defthm functionp1-except-lemma
    (implies (functionp1 a f)
             (functionp1 a (scons (pair x v)
                                  (diff f (subset-such-that1 f x)))))))

; Now we put the two breakers together to get the main lemma about
; functionp1 and except.

 (defthm functionp1-except
   (implies (and (functionp1 b f)
                 (subsetp a b))
            (functionp1 a (scons (pair x v)
                                 (diff f (subset-such-that1 f x)))))))

(defthm functionp-except
  (implies (functionp f)
           (functionp (except f x v)))
  :hints (("Goal" :in-theory (enable except))))

(defthm functionp-implies-pairsp
  (implies (functionp f)
           (pairsp f)))

(in-theory (disable functionp))

;----------------------------------------------------------------------------
; Domain and Range

(defun domain (f)
  (cond ((ur-elementp f) nil)
        (t (scons (hd (scar f))
                  (domain (scdr f))))))

(defun range (f)
  (cond ((ur-elementp f) nil)
        (t (scons (tl (scar f)) (range (scdr f))))))

(defthm mem-implies-mem-domain
  (implies (mem e f)
           (mem (hd e) (domain f))))

(defthm ur-elementp-domain
  (equal (ur-elementp (domain f))
         (ur-elementp f)))

(defx :strategy :congruence (domain f) 1 :method :subsetp)

(defthm mem-implies-mem-range
  (implies (mem e f)
           (mem (tl e) (range f))))

(defthm ur-elementp-range
  (equal (ur-elementp (range f))
         (ur-elementp f)))

(defx :strategy :congruence (range f) 1 :method :subsetp)

(defthm domain-scons
  (= (domain (scons e f))
     (scons (hd e) (domain f))))

(defthm domain-diff-subset-such-that1
  (implies (pairsp f)
           (= (domain (diff f (subset-such-that1 f x)))
              (diff (domain f) (brace x)))))

(defthm domain-except
  (implies (pairsp f)
           (= (domain (except f x v))
              (scons x (domain f))))
  :hints (("Goal" :in-theory (enable except))))

; The range of (except f x v) is harder to characterize.  If f is
; not a function, then (except f x v) might be.  The range of f
; might include many things that are removed by the except.

(defthm range-scons
  (= (range (scons e f))
     (scons (tl e) (range f))))

(defthm subsetp-range-except
  (subsetp (range (except f x v))
           (scons v (range f)))
  :hints (("Goal" :in-theory (enable except))))

; We have these two, even though the union is not necessarily a
; function.

(defthm domain-union
  (= (domain (union f g))
     (union (domain f) (domain g))))

(defthm range-union
  (= (range (union f g))
     (union (range f) (range g))))

(defthm cardinality-domain
  (<= (cardinality (domain f)) (cardinality f))
  :rule-classes :linear)

(defthm cardinality-range
  (<= (cardinality (range f)) (cardinality f))
  :rule-classes :linear)

(defthm ur-element-subset-such-that1
  (implies (pairsp f)
           (equal (ur-elementp (subset-such-that1 f x))
                  (not (mem x (domain f))))))

(defthm cardinality-<=-0
  (equal (< 0 (cardinality a))
         (not (ur-elementp a))))

(defthm cardinality-domain-functionp
  (implies (functionp f)
           (equal (cardinality (domain f))
                  (cardinality f)))
  :hints (("Goal" :in-theory (enable functionp))))

(defthm subset-such-that1-empty
  (implies (not (mem e (domain b)))
           (= (subset-such-that1 b e)
              nil)))

; Is the (pairsp b) hypothesis below necessary?  Yes.  Here is a counterexample
; of the formula without the hypothesis.

#|(let ((b (brace 123))
        (a (brace (pair nil 33)))
        (pair (pair nil 2)))
    (equal (functionp1 a (scons pair b))
           (if (and (pairp pair)
                    (mem (hd pair) (domain a)))
               (and (functionp1 a b)
                    (or (mem pair b)
                        (not (mem (hd pair) (domain b)))))
             (functionp1 a b))))|#

(defthm functionp1-scons
  (implies (pairsp b)
           (equal (functionp1 a (scons pair b))
                  (if (and (pairp pair)
                           (mem (hd pair) (domain a)))
                      (and (functionp1 a b)
                           (or (mem pair b)
                               (not (mem (hd pair) (domain b)))))
                    (functionp1 a b)))))

(defthm cardinality-<=-1-cases
  (iff (< 1 (cardinality x))
       (not (or (ur-elementp x)
                (equal (cardinality x) 1)))))

(defthm functionp-scons-lemma
  (implies (and (functionp1 a b)
                (subsetp a b)
                (pairsp b)
                (mem e a))
           (equal (cardinality (subset-such-that1 b (hd e)))
                  1)))

; Note that the following theorem is essentially a recursive
; alternative definition of functionp.

(defthm functionp-scons
  (equal (functionp (scons e a))
         (if (ur-elementp a)
             (pairp e)
           (and (functionp a)
                (pairp e)
                (or (mem e a)
                    (not (mem (hd e) (domain a)))))))
  :hints (("Goal" :in-theory (enable functionp))))

(defthm functionp-union
  (implies (and (functionp a)
                (functionp b)
                (not (intersection (domain a) (domain b))))
           (functionp (union a b))))

(defthm disjoint-domains-implies-disjoint
  (implies (not (intersection (domain a) (domain b)))
           (not (intersection a b)))
  :rule-classes nil)

(defthm cardinality-except
  (implies (functionp f)
           (= (cardinality (except f x v))
              (if (mem x (domain f))
                  (cardinality f)
                (+ 1 (cardinality f)))))
  :hints (("Goal"
           :use ((:instance cardinality-domain-functionp (f (except f x v)))
                 (:instance cardinality-domain-functionp (f f)))
           :in-theory (disable cardinality-domain-functionp))))

(defthm apply-outside-domain
  (implies (not (mem e (domain f)))
           (= (apply f e) nil))
  :hints (("Goal" :in-theory (enable apply))))

;----------------------------------------------------------------------------
; Restrictions

; I can think of three slightly different ways to define the restriction
; of a function f to some domain s.

; (1) Iterate over s and make a function of the defined values.  This
; always produces a function.  However, if f is not a function, the
; function it produces is sort of unpredictable because it uses apply,
; so the restricted function chooses the largest pairs.

(defun restrict (f s)
  (cond ((ur-elementp s) nil)
        ((mem (scar s) (domain f))
         (except (restrict f (scdr s))
                 (scar s)
                 (apply f (scar s))))
        (t (restrict f (scdr s)))))

; (2) Iterate over f and make a function of the values of elements of
; s.  This always produces a function.  But if f is not a function,
; the restricted function is unpredictable because it chooses the
; first pair presented for each domain element.  I reject this
; definition because it does not do the ``normal'' things with a
; function.  The normal things you do with a function are enquire
; about its domain and apply it.  Looking at its internal structure is
; an invitation to low-level work.

; (defun restrict2 (f s)
;   (cond ((ur-elementp f) nil)
;         ((and (pairp (scar f))
;               (mem (hd (scar f)) s))
;          (except (restrict2 (scdr f) s)
;                  (hd (scar f))
;                  (tl (scar f))))
;         (t (restrict2 (scdr f) s))))

; (3) Iterate over f and collect everything whose hd is in s.  The
; result may not be a function, but it is if f is.  This has the
; appeal of being really simple, but, again, uses f in an abnormal
; way.

; (defun restrict3 (f s)
;   (cond ((ur-elementp f) nil)
;         ((mem (hd (scar f)) s)
;          (scons (scar f) (restrict3 (scdr f) s)))
;         (t (restrict3 (scdr f) s))))

(defx :strategy :congruence (restrict f s) 1)

; Next we prove that the second argument of restrict admits = as a
; congruence relation.  For some reason it took me a while to
; realize that if you are going to prove that something is a
; subset of (restrict f s) you must be able to answer the question
; ``when is e a member of (restrict f s)?''  I was seeing this question
; come up and generalized it to ``when is e a member of a function?''
; Answering that was harder than answering it for (restrict f s),
; which is always a function but which is built in a way that makes
; it easier to answer the question.  Here is how you do it.

; The system can prove mem-restrict, below, without further help.  It
; generates three inductively proved subgoals.  These are not worth
; turning into rules because mem-restrict, once proved, is better than
; each of them.

(defthm mem-restrict
  (equal (mem e (restrict f s))
         (and (pairp e)
              (mem (hd e) (domain f))
              (= (tl e) (apply f (hd e)))
              (mem (hd e) s)))
  :hints (("Goal" :do-not '(generalize))))

; At first I wrote (= (restrict f s) nil) instead of the inner equal.
; But I really need the stronger equal because in the defcong= proof
; below the question of whether (restrict f s) is a set comes up.  To
; be a set it must be either not an ur-element or nil.  This means
; that we end up testing (restrict f s) against nil in a propositional
; setting, not a set theory setting.  Since = does not refine iff
; (because '(:UR-CONS NIL) is canonicalized to NIL), knowing that
; (restrict f s) is not = nil does not help us.

(defthm ur-elementp-restrict
  (equal (ur-elementp (restrict f s))
         (equal (restrict f s) nil)))

(defx :strategy :congruence (restrict f s) 2 :method :subsetp)

(defthm functionp-restrict
  (functionp (restrict f s)))

; My next main goal is the fundamental fact characterizing the elements
; of a function.

; Perhaps disable this when we're done?


(defthm pigeon-hole-1
  (implies (and (mem e a)
                (mem d a)
                (equal (cardinality a) 1))
           (= e d))
  :rule-classes nil)

; The next three theorems are trivial consequences of other lemmas
; given the fact that (choose a) is an element of a.  I really ought
; to provide macros that capture these kind of theorems.  The idea in
; all of them is that if every element of a has some property then
; (choose a) has that property if a is non-empty.

(defthm hd-choose-subset-such-that1
  (= (hd (choose (subset-such-that1 f x)))
     (if (ur-elementp (subset-such-that1 f x))
         nil
       x))
  :hints (("Goal"
           :in-theory (disable mem-choose)
           :use ((:instance mem-choose
                            (a (subset-such-that1 f x)))))))

(defthm pairp-choose-subset-such-that1
  (implies (pairsp f)
           (equal (pairp (choose (subset-such-that1 f x)))
                  (and (not (ur-elementp f))
                       (mem x (domain f)))))
  :hints (("Goal"
           :in-theory (cons 'equal-booleans
                            (disable mem-choose))
           :use ((:instance mem-choose
                            (a (subset-such-that1 f x)))))))

(defthm mem-choose-subset-such-that1
  (implies (pairsp f)
           (equal (mem (choose (subset-such-that1 f x)) f)
                  (and (not (ur-elementp f))
                       (mem x (domain f)))))
  :hints (("Goal"
           :in-theory (cons 'equal-booleans
                            (disable mem-choose))
           :use ((:instance mem-choose
                            (a (subset-such-that1 f x)))))))

; This is a pretty obscure fact, I think.  If x is a pair in f and
; there is only one pair in f with its hd, then choose chooses x.

(defthm mem-x-implies-not-ur-elementp-subset-such-that1
  (implies (and (mem x f)
                (pairp x))
           (not (ur-elementp (subset-such-that1 f (hd x))))))

(defthm choose-subset-such-that1
  (implies (and (<= (cardinality (subset-such-that1 f (hd x))) 1)
                (mem x f)
                (pairp x)
                (pairsp f))
           (= (choose (subset-such-that1 f (hd x)))
              x))
  :hints (("Goal"
           :use (:instance pigeon-hole-1
                           (e x)
                           (d (choose (subset-such-that1 f (hd x))))
                           (a (subset-such-that1 f (hd x)))))))

(defthm functionp-implies-mem-1
  (implies (and (functionp1 a f)
                (pairsp f)
                (subsetp a f)
                (mem hd (domain a)))
           (mem (pair hd (tl (choose (subset-such-that1 f hd))))
                f)))

(defthm functionp-implies-mem-2
  (implies (and (functionp1 a f)
                (pairsp f)
                (subsetp a f)
                (mem (hd x) (domain a))
                (pairp x)
                (mem x f))
           (= (choose (subset-such-that1 f (hd x)))
              x)))

; This is the fundamental fact about membership in a function.  It
; loops if made into a rewrite rule.

(defthm mem-functionp
  (implies (functionp f)
           (equal (mem e f)
                  (and (pairp e)
                       (mem (hd e) (domain f))
                       (= (tl e) (apply f (hd e))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable functionp apply equal-booleans))))

(defthm domain-restrict
  (= (domain (restrict f s))
     (intersection s (domain f))))

(defthm apply-restrict
  (implies (and (mem x (domain f))
                (mem x s))
           (= (apply (restrict f s) x)
              (apply f x))))

(defthm except-scdr-scar-elim
  (implies (and (functionp f)
                (not (ur-elementp f)))
           (= (except (scdr f) (hd (scar f)) (tl (scar f)))
              f))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (enable except functionp equal-pair-generalized)
    :use ((:instance mem-functionp
                     (e (pair (hd (scar f)) (tl (scar f))))
                     (f f))
          (:instance mem-singleton
                     (e (pair (hd (scar f)) (tl (scar f))))
                     (x (subset-such-that1 (scdr f) (hd (scar f)))))))))

(defthm functionp-nil
  (implies (ur-elementp f)
           (equal (functionp f) (= f nil)))
  :hints (("Goal" :in-theory (enable functionp))))

(defthm functionp-pairp
  (implies (not (pairp x))
           (not (functionp (scons x y))))
  :hints (("Goal" :in-theory (enable functionp))))

(defthm except-scdr-scar-elim-special-case
  (implies (and (functionp f)
                (not (ur-elementp f))
                (ur-elementp (scdr f)))
           (= (except nil (hd (scar f)) (tl (scar f)))
              f))
  :hints (("Goal" :in-theory (enable except))))

(defthm functionp-scdr
  (implies (functionp f)
           (functionp (scdr f)))
  :hints (("Goal" :in-theory (enable functionp))))

(defthm restrict-domain
  (implies (and (functionp f)
                (functionp g)
                (subsetp f g))
           (= (restrict g (domain f)) f))
  :hints
  (("Subgoal *1/4"
    :use ((:instance mem-functionp (e (scar f)) (f g))))))

; The lemma above will rewrite (restrict a (domain a)) to a, provided
; (functionp a).  But it is often the case that the domain expression
; will be rewritten to something else, e.g., an intersection.  So
; we provide a bridge.

(defthm restrict-domain-special-case
  (implies (and (functionp f)
                (= a (domain f)))
           (= (restrict f a) f)))

(defthm restrict-scons
  (= (restrict f (scons e s))
     (if (mem e (domain f))
         (except (restrict f s)
                 e
                 (apply f e))
       (restrict f s))))

; ----------------------------------------------------------------------------
; Strategies for Proving Functions and Sets Equivalent

(encapsulate ((functional-equiv-fn1 () t)
              (functional-equiv-fn2 () t))
             (local (defun functional-equiv-fn1 nil nil))
             (local (defun functional-equiv-fn2 nil nil))
             (defthm functional-equivalence-constraint-1
               (functionp (functional-equiv-fn1)))
             (defthm functional-equivalence-constraint-2
               (functionp (functional-equiv-fn2)))
             (defthm functional-equivalence-constraint-3
               (= (domain (functional-equiv-fn2))
                  (domain (functional-equiv-fn1))))

; We use the unusual variable name fex (``functional equivalence x'') because
; any variable appearing in a constraint is prohibited from occurring in
; any theorem proved with functional-instantiation from this constraint.

             (defthm functional-equivalence-constraint-4
               (implies (mem fex (domain (functional-equiv-fn1)))
                        (= (apply (functional-equiv-fn1) fex)
                           (apply (functional-equiv-fn2) fex)))))

(defun every-where-= (s f g)
  (cond ((ur-elementp s) t)
        (t (and (= (apply f (scar s))
                   (apply g (scar s)))
                (every-where-= (scdr s) f g)))))

(defthm every-where-=-implies-=-restrict
  (implies (and (functionp f)
                (functionp g)
                (subsetp s (domain f))
                (subsetp s (domain g))
                (every-where-= s f g))
           (= (restrict f s)
              (restrict g s)))
  :rule-classes nil)

(encapsulate
 nil
 (local
  (defthm every-where-=-functional-equiv-fn1-functional-equiv-fn2
    (implies (subsetp s (domain (functional-equiv-fn1)))
             (every-where-= s (functional-equiv-fn1) (functional-equiv-fn2)))))

 (defthm functional-equivalence-theorem
   (= (functional-equiv-fn1) (functional-equiv-fn2))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance every-where-=-implies-=-restrict
                            (f (functional-equiv-fn1))
                            (g (functional-equiv-fn2))
                            (s (domain (functional-equiv-fn1))))))))

; The above encapsulation provides a nice way to prove two functions
; are equal.  You can just instantiate the lemma above with any two
; functions that are known to have the same domain and that are
; apply-equal everywhere.

(defmacro functional-equivalence (name term
                                       &key
                                       hints
                                       (rule-classes 'nil rule-classesp)
                                       (otf-flg 'nil otf-flgp))
  (let* ((xterm
          (acl2::case-match
           term
           (('implies acl2::& ('= acl2::& acl2::&))
            term)
           (('= acl2::& acl2::&)
            `(implies t ,term))
           (t nil))))
    (cond
     ((null xterm)
      `(acl2::er acl2::soft 'functional-equivalence
                 "The functional-equivalence strategy requires a term of ~
                  the form (= f g) or (implies h (= f g)).  Your term, ~x0, ~
                  is not of this form."
                 ',term))
     ((acl2::assoc-equal "Goal" hints)
      `(acl2::er acl2::soft 'functional-equivalence
                 "The functional-equivalence strategy provides hints for ~
                  \"Goal\".  Your hints should be provided for some Subgoal."))
     (t
      (let ((hyps (cadr xterm))
            (lhs (cadr (caddr xterm)))
            (rhs (caddr (caddr xterm))))
        `(defthm ,name ,term
           :hints
           (("Goal"
             :use ((:functional-instance
                    functional-equivalence-theorem
                    (functional-equiv-fn1
                     (lambda ()
                       ,(if (eq hyps t)
                            lhs
                          `(if ,hyps ,lhs nil))))
                    (functional-equiv-fn2
                     (lambda ()
                       ,(if (eq hyps t)
                            rhs
                          `(if ,hyps ,rhs nil)))))))
            ,@hints)
           ,@(if rule-classesp
                 `(:rule-classes ,rule-classes)
               nil)
           ,@(if otf-flgp
                 `(:otf-flg ,otf-flg)
               nil)))))))

; While I'm at it, I'll provide a way to prove that two sets are equal.

; Suppose you have two arbitrary sets with the property that if x is a
; member of one, then x is a member of the other.

(encapsulate ((subsetp-strategy-set1 () t)
              (subsetp-strategy-set2 () t))
             (local (defun subsetp-strategy-set1 () nil))
             (local (defun subsetp-strategy-set2 () nil))

; We use the unusual variable name ssx (``subsetp strategy x'') because whatever
; var we use in a constraint is off-limits to the user in any theorem proved
; via functional instantiation based on these constraints.

             (defthm subsetp-strategy-constraint
               (implies (mem ssx (subsetp-strategy-set1))
                        (mem ssx (subsetp-strategy-set2)))))

; Then the first set is a subset of the second.

(encapsulate
 nil
 (local
  (defthm subsetp-strategy-lemma
    (implies (subsetp a (subsetp-strategy-set1))
             (subsetp a (subsetp-strategy-set2)))))

 (defthm subsetp-strategy
   (subsetp (subsetp-strategy-set1)
            (subsetp-strategy-set2))
   :rule-classes nil))

; And here is a handy macro to use this strategy to prove the subsetp
; relation between two expressions under a hypothesis.

; This macro allows us to write:
; (defx foo (subsetp ... ...)
;   :strategy subset-relation
;   :rule-classes ...)

(defmacro subset-relation (name term
                                &key
                                hints
                                (rule-classes 'nil rule-classesp)
                                (otf-flg 'nil otf-flgp))
  (let* ((xterm
          (acl2::case-match
           term
           (('implies acl2::& ('subsetp acl2::& acl2::&))
            term)
           (('subsetp acl2::& acl2::&)
            `(implies t ,term))
           (t nil))))
    (cond
     ((null xterm)
      `(acl2::er acl2::soft 'subset-relation
                 "The subset-relation strategy requires a term of ~
                  the form (subsetp a b) or (implies h (subsetp a b)).  Your term, ~x0, ~
                  is not of this form."
                 ',term))
     ((acl2::assoc-equal "Goal" hints)
      `(acl2::er acl2::soft 'subset-relation
                 "The subset-relation strategy provides hints for ~
                  \"Goal\".  Your hints should be provided for some Subgoal."))
     (t
      (let ((hyps (cadr xterm))
            (lhs (cadr (caddr xterm)))
            (rhs (caddr (caddr xterm))))
        `(defthm ,name ,term
           :hints
           (("Goal"
             :use ((:functional-instance
                    subsetp-strategy
                    (subsetp-strategy-set1
                     (lambda ()
                       ,(if (eq hyps t)
                            lhs
                          `(if ,hyps ,lhs nil))))
                    (subsetp-strategy-set2
                     (lambda ()
                       ,(if (eq hyps t)
                            rhs
                          `(if ,hyps ,rhs nil)))))))
            ,@hints)
           ,@(if rule-classesp
                 `(:rule-classes ,rule-classes)
               nil)
           ,@(if otf-flgp
                 `(:otf-flg ,otf-flg)
               nil)))))))

; Here is a way to set equality using two subsets.  It requires
; proving (mem x a) <-> (mem x b).

; We can thus write
; (defx foo (implies ... (= ... ...))
;   :strategy equivalence-relation
;   :rule-classes ...)

; Two proof obligations are generated, each a mem implying a mem.  You
; can provide hints for them with :hints-1 and :hints-2.

(defmacro set-equivalence (name term
                                &key hints
                                (rule-classes 'nil rule-classesp)
                                (otf-flg 'nil otf-flgp)
                                (hints-1 'nil hints-1p)
                                (otf-flg-1 'nil otf-flg-1p)
                                (hints-2 'nil hints-2p)
                                (otf-flg-2 'nil otf-flg-2p))
  (let* ((xterm
          (acl2::case-match term
                            (('implies acl2::& ('= acl2::& acl2::&))
                             term)
                            (('= acl2::& acl2::&)
                             `(implies t ,term))
                            (t nil))))
    (cond
     ((null xterm)
      `(acl2::er acl2::soft 'set-equivalence
                 "~x0 is not of the form (= x y) or of the form ~
                  (implies hyps (= x y))."
                 ',term))
     ((or (acl2::assoc-equal "Goal" hints)
          (acl2::assoc-equal "Goal" hints-1)
          (acl2::assoc-equal "Goal" hints-2))
      `(acl2::er acl2::soft 'set-equivalence
                 "The set-equivalence strategy provides hints for ~
                  \"Goal\".  Your hints should be provided for some Subgoal."))
     (t
      (let ((hyps (cadr xterm))
            (lhs (cadr (caddr xterm)))
            (rhs (caddr (caddr xterm)))
            (name-1 (packn-in-pkg (list name "-1") name))
            (name-2 (packn-in-pkg (list name "-2") name)))
        `(encapsulate
          nil
          (local
           (defx ,name-1
             ,(if (eq hyps t)
                  `(subsetp ,lhs ,rhs)
                `(implies ,hyps (subsetp ,lhs ,rhs)))
             :strategy subset-relation
             ,@(if hints-1p `(:hints ,hints-1) nil)
             ,@(if otf-flg-1p `(:otf-flg ,otf-flg-1) nil)
             :rule-classes nil))
          (local
           (defx ,name-2
             ,(if (eq hyps t)
                  `(subsetp ,rhs ,lhs)
                `(implies ,hyps (subsetp ,rhs ,lhs)))
             :strategy subset-relation
             ,@(if hints-2p `(:hints ,hints-2) nil)
             ,@(if otf-flg-2p `(:otf-flg ,otf-flg-2) nil)
             :rule-classes nil))
          (defthm ,name ,term
            :hints
            (("Goal"
              :use ((:instance =-iff-subsetps
                               (a ,(if (eq hyps t)
                                       lhs
                                     `(if ,hyps ,lhs nil)))
                               (b ,(if (eq hyps t)
                                       rhs
                                     `(if ,hyps ,rhs nil))))
                    (:instance ,name-1)
                    (:instance ,name-2))
              ,@hints))
            ,@(if rule-classesp
                  `(:rule-classes ,rule-classes)
                nil)
            ,@(if otf-flgp
                  `(:otf-flg ,otf-flg)
                nil))))))))

; ----------------------------------------------------------------------------
; An Example

(defx union-diff-diff
  (implies (and (subsetp a b)
                (subsetp b c))
           (= (union (diff b a)
                     (diff c b))
              (diff c a)))
  :strategy :set-equivalence)

;----------------------------------------------------------------------------
; Sequences

; A sequence is a function whose domain is an initial subset of the
; natural numbers.

(defun nats (n)
  (if (zp n)
      '(0)
    (scons n (nats (- n 1)))))

(defthm ur-elementp-nats
  (not (ur-elementp (nats n))))

(defcong = = (nats n) 1
  :hints (("Goal" :in-theory (enable zp))))

(defthm mem-nats
  (equal (mem e (nats n))
         (and (integerp e)
              (<= 0 e)
              (<= e (nfix n))))
  :hints (("Goal" :in-theory (enable =))))

(defun sequencep (s)
  (and (functionp s)
       (= (domain s)
          (diff (nats (cardinality s)) '(0)))))

(defthm functionp-sequencep
  (implies (sequencep s)
           (functionp s)))

(defthm domain-sequencep
  (implies (sequencep s)
           (= (domain s)
              (diff (nats (cardinality s)) '(0)))))

(in-theory (disable sequencep))

(defun shift (i j f delta)
  (declare (xargs :measure (nfix (- (+ 1 (acl2::ifix j)) (acl2::ifix i)))))
  (cond ((and (integerp i)
              (integerp j)
              (<= i j))
         (except (shift (+ 1 i) j f delta)
                 (+ i delta)
                 (apply f i)))
        (t nil)))

(defcong = = (shift i j f delta) 1)
(defcong = = (shift i j f delta) 2)
(defcong = = (shift i j f delta) 3)
(defcong = = (shift i j f delta) 4)

(defthm functionp-shift
  (functionp (shift i j f delta)))

; If f is a sequence, its domain is [1...n].  So (shift i j f delta)
; takes [i...j] to [i+delta ... j+delta].  This is

(defthm mem-domain-shift
  (implies (integerp delta)
           (= (mem x (domain (shift i j f delta)))
              (and (integerp i)
                   (integerp j)
                   (<= i j)
                   (integerp x)
                   (<= (+ i delta) x)
                   (<= x (+ j delta))))))

; We can express the domain of a shift of a sequence as a set of nats.

(defx domain-shift
  (implies (and (sequencep s)
                (integerp delta)
                (<= 0 delta))
           (= (domain (shift 1 (cardinality s) s delta))
              (diff (nats (+ delta (cardinality s)))
                    (nats delta))))
  :strategy :set-equivalence)

(defun concat (r s)
  (union r (shift 1 (cardinality s) s (cardinality r))))

(defcong = = (concat r s) 1)
(defcong = = (concat r s) 2)

(defthm functionp-concat
  (implies (and (sequencep r)
                (sequencep s))
           (functionp (concat r s))))

(defthm subsetp-nats-0
  (subsetp '(0) (nats i)))

(defthm =-0
  (equal (= i 0)
         (equal i 0))
  :hints (("Goal" :in-theory (enable =))))

(defthm subsetp-nats-nats
  (equal (subsetp (nats i) (nats j))
         (<= (nfix i) (nfix j))))

(defthm domain-concat
  (implies (and (sequencep r)
                (sequencep s))
           (= (domain (concat r s))
              (diff (nats (+ (cardinality r) (cardinality s)))
                    '(0)))))

; I need the (integerp delta) hypothesis because cardinality raises
; the question of membership in the shifted domain and
; mem-domain-shift has an integerp hyp.

(defthm cardinality-shift
  (implies (integerp delta)
           (= (cardinality (shift i j f delta))
              (if (and (integerp i)
                       (integerp j)
                       (<= i j))
                  (+ 1 (- j i))
                0))))

(defthm cardinality-concat
  (implies (and (sequencep r)
                (sequencep s))
           (= (cardinality (concat r s))
              (+ (cardinality r) (cardinality s))))
  :hints (("Goal"
           :use (:instance disjoint-domains-implies-disjoint
                           (a r)
                           (b (shift 1 (cardinality s) s (cardinality r)))))))

(defthm sequencep-concat
  (implies (and (sequencep r)
                (sequencep s))
           (sequencep (concat r s)))
  :hints (("Goal"
           :in-theory
           (set-difference-theories (enable sequencep)
                                    '(concat)))))

; Here is a recursive alternative definition of apply.

(defthm apply-scons
  (implies (functionp (scons pair f))
           (= (apply (scons pair f) x)
              (if (= (hd pair) x)
                  (tl pair)
                (apply f x))))
  :hints (("Goal" :in-theory (enable apply))
          ("Subgoal 2.1'"
           :in-theory (set-difference-theories (enable functionp)
                                               '(functionp-scons-lemma))

           :use ((:instance functionp-scons-lemma
                            (a f)
                            (b f)
                            (e (pair hd tl)))
                 (:instance mem-singleton
                            (x (subset-such-that1 f hd))
                            (e (pair hd tl)))))))

(defthm apply-disjoint-union
  (implies (and (functionp a)
                (functionp b)
                (not (intersection (domain a) (domain b))))
           (= (apply (union a b) x)
              (if (mem x (domain a))
                  (apply a x)
                (apply b x)))))

; Suppose you have a function, f, (not necessarily a sequence) and you
; form another function, f', by shifting [i...j] of f up by delta.
; What is (apply f' x)?  The domain of f' is [i+delta ... j+delta].
; If x is in that domain, then (apply f' x) is (apply f (- x delta)).

; To prove this we need the important fact:

(defthm apply-shift
  (= (apply (shift i j f delta) x)
     (if (mem x (domain (shift i j f delta)))
         (apply f (- x delta))
       nil)))

(defthm apply-concat
  (implies (and (sequencep r)
                (sequencep s))
           (= (apply (concat r s) i)
              (cond ((and (integerp i)
                          (< 0 i))
                     (if (<= i (cardinality r))
                         (apply r i)
                       (apply s (- i (cardinality r)))))
                    (t nil))))
  :hints (("Subgoal 11"
           :in-theory (disable apply-outside-domain)
           :use
           ((:instance apply-outside-domain
                       (e (- i (cardinality r)))
                       (f s))))))

(in-theory (disable concat))

(defx associativity-of-concat
  (implies (and (sequencep a)
                (sequencep b)
                (sequencep c))
           (= (concat (concat a b) c)
              (concat a (concat b c))))
  :strategy :functional-equivalence)

; Now I will define seq-hd and seq-tl to let me do recursion down
; sequences.

(defun seq-hd (s) (apply s 1))

(defcong = = (seq-hd s) 1)

(defun seq-tl (s)
  (restrict (shift 1 (cardinality s) s -1)
            (diff (nats (- (cardinality s) 1))
                  (brace 0))))

(defcong = = (seq-tl s) 1)

(defthm functionp-seq-tl
  (functionp (seq-tl s)))

(defthm cardinality-restrict
  (= (cardinality (restrict f s))
     (cardinality (intersection (domain f) s))))



(defx domain-shift-generalized
  (implies (and (integerp i)
                (integerp j)
                (<= i j)
                (integerp delta)
                (<= 0 (+ i delta)))
           (= (domain (shift i j s delta))
              (if (= (+ delta i) 0)
                  (nats (+ delta j))
              (diff (nats (+ delta j))
                    (nats (+ delta i -1))))))
  :strategy :set-equivalence)

(defthm cardinality-positive
  (implies (not (ur-elementp s))
           (< 0 (cardinality s)))
  :rule-classes :linear)

(defthm intersection-x-x
  (= (intersection x x) (sfix x)))

(defthm cardinality-diff-nats-0
  (implies (and (integerp i)
                (<= 0 i))
           (= (cardinality (diff (nats i) '(0)))
              i)))

(defthm cardinality-seq-tl
  (implies (not (ur-elementp s))
           (= (cardinality (seq-tl s))
              (- (cardinality s) 1))))

(defthm sequencep-seq-tl
  (implies (not (ur-elementp s))
           (sequencep (seq-tl s)))
  :hints (("Goal" :in-theory (enable sequencep))))

(defthm seq-tl-recursion
  (implies (not (ur-elementp s))
           (< (cardinality (seq-tl s))
              (cardinality s)))
  :rule-classes (:built-in-clause :linear))

(in-theory (disable seq-hd seq-tl))

; Next, I define defmap.  Thus,

; (defmap subset (a s b) :for x :in s :such-that (bd a x b))
; and
; (defmap image  (a s b) :for x :in s :map       (bd a x b))

; will define subset and image recursively so that they return the
; sets described below

; (subset a s b) = {x in s | (bd a x b)}
; and
; (image  a s b) = {(bd a x b) | x in s}

; In addition, I get a few useful theorems about these functions, including
; that = is a congruence for every argument.

; It must be the case that congruence rules are already in place for
; (bd a x b).

(defun defmap-congruences (vars call sloc i)
  (cond
   ((endp vars) nil)
   (t (cons (if (equal sloc i)
                `(defx :strategy :congruence ,call ,i :method :subsetp)
              `(defx :strategy :congruence ,call ,i))
            (defmap-congruences (cdr vars) call sloc (+ 1 i))))))

(defmacro defmap (name vars
                       &key
                       (for 'nil forp)
                       (in 'nil inp)
                       (such-that 'nil such-thatp)
                       (map 'nil mapp))

; (defmap foo (s ...) :for x :in s :such-that px)
; or
; (defmap foo (s ...) :for x :in s :map px)

  (cond
   ((not (and (symbolp name)
              (acl2::symbol-listp vars)
              forp
              (symbolp for)
              (not (acl2::member-equal for vars))
              inp
              (symbolp in)
              (acl2::member-equal in vars)
              (or (and such-thatp (not mapp))
                  (and (not such-thatp) mapp))))
    `(acl2::er acl2::soft 'defmap
               "The proper form of a defmap command is~%~
                (defmap name vars :for x :in v :such-that body)~%~
                or~%~
                (defmap name vars :for x :in v :map body),~%~
                where name is a new function name, vars is a list of ~
                variables, x is a variable not in vars, ~
                v is a variable in vars, and body is a term."))
   (such-thatp
    (let* ((x for)
           (s in)
           (sloc (- (length vars) (length (member s vars))))
           (body such-that)
           (s1 (genname1 s 1 (cons x vars)))
           (call `(,name ,@vars))
           (rcall `(,name ,@(put-nth `(scdr ,s) sloc vars))))
      `(encapsulate
        nil
        (defun ,name (,@vars)
          (if (ur-elementp ,s)
              nil
            (let ((,x (scar ,s)))
              (if ,body
                  (scons (scar ,s) ,rcall)
                ,rcall))))

        (defthm ,(packn-in-pkg (list "SETP-" name) 'defmap)
          (setp ,call))

        (defthm ,(packn-in-pkg (list "UR-ELEMENTP-" name) 'defmap)
          (equal (ur-elementp ,call)
                 (equal ,call nil)))

        (defthm ,(packn-in-pkg (list "MEM-" name) 'defmap)
          (equal (mem ,x ,call)
                 (and ,body             ; we write it this way in case body
                      (mem ,x ,s)))     ; is not Boolean!
          :otf-flg t)

        (defthm ,(packn-in-pkg (list "SUBSETP-" name) 'defmap)
          (subsetp ,call ,s))

        ,@(defmap-congruences vars call (+ sloc 1) 1)

        (defthm ,(packn-in-pkg (list "MEM-" name "-CORROLLARY") 'defmap)
          (implies (and (subsetp ,s1 ,call)
                        (mem ,x ,s1))
                   ,body))

        (defthm ,(packn-in-pkg (list "CARDINALITY-" name) 'defmap)
          (<= (cardinality ,call)
              (cardinality ,s))
          :rule-classes :linear)

        (defthm ,(packn-in-pkg (list "UNION-" name) 'defmap)
          (= (,name ,@(put-nth `(union ,s1 ,s) sloc vars))
             (union (,name ,@(put-nth s1 sloc vars))
                    ,call)))

        (defthm ,(packn-in-pkg (list "INTERSECTION-" name) 'defmap)
          (= (,name ,@(put-nth `(intersection ,s1 ,s) sloc vars))
             (intersection (,name ,@(put-nth s1 sloc vars))
                           ,call)))

        )))
   (t ;;; :map

    (let* ((x for)
           (s in)
           (sloc (- (length vars) (length (member s vars))))
           (body map)
           (fx (genname1 x 1 (cons x vars)))
           (s1 (genname1 s 1 (cons fx (cons x vars))))
           (call `(,name ,@vars))
           (rcall `(,name ,@(put-nth `(scdr ,s) sloc vars))))
      `(encapsulate
        nil
        (defun ,name (,@vars)
          (if (ur-elementp ,s)
              nil
            (let ((,x (scar ,s)))
              (scons ,body ,rcall))))

        (defthm ,(packn-in-pkg (list "SETP-" name) 'defmap)
          (setp ,call))

        (defthm ,(packn-in-pkg (list "UR-ELEMENTP-" name) 'defmap)
          (equal (ur-elementp ,call)
                 (ur-elementp ,s)))

        (defthm ,(packn-in-pkg (list "WEAK-MEM-" name) 'defmap)
          (implies (and (mem ,x ,s)
                        (= ,fx ,body))
                   (mem ,fx ,call)))


        (defthm ,(packn-in-pkg (list "SUBSETP-" name) 'defmap)
          (implies (subsetp ,s1 ,s)
                   (subsetp (,name ,@(put-nth s1 sloc vars))
                            ,call)))

        ,@(defmap-congruences vars call (+ sloc 1) 1)

        (defthm ,(packn-in-pkg (list "CARDINALITY-" name) 'defmap)
          (<= (cardinality ,call)
              (cardinality ,s))
          :rule-classes :linear)

        (defthm ,(packn-in-pkg (list "UNION-" name) 'defmap)
          (= (,name ,@(put-nth `(union ,s1 ,s) sloc vars))
             (union (,name ,@(put-nth s1 sloc vars))
                    ,call)))

; Once I thought that
; (image (intersection s1 s)) = (intersection (image s1) (image s))
; But this is wrong.  Consider
; s1 = {(0 . 1) (0 . 2)}
; s  = {(1 . 1) (1 . 2)}
; let (body e) = (cdr e) (or (tl e) if the elements are pairps)
; Then the lhs is nil because the two sets are disjoint, but the
; rhs is {1 2}.

        (defthm ,(packn-in-pkg (list "INTERSECTION-" name) 'defmap)
          (subsetp (,name ,@(put-nth `(intersection ,s1 ,s) sloc vars))
                   (intersection (,name ,@(put-nth s1 sloc vars))
                                 ,call)))

        )))))

#|
; Here are examples of both styles of defmap:

(defstub bd (a x b) t)
(acl2::skip-proofs
 (progn (defcong = = (bd a x b) 1)
        (defcong = = (bd a x b) 2)
        (defcong = = (bd a x b) 3)))

(defmap subset (a s b) :for x :in s :such-that (bd a x b))
(defmap image  (a s b) :for x :in s :map       (bd a x b))

|#

