;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "../utilities/utilities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


; Integer base -- integerp, ifix, zip, ineg, i+, i<, i<=

(defsection integerp

  (definlined integerp (a)
    (declare (xargs :guard t))
    (or (natp a)
        (and (consp a)
             (equal (car a) 'minus)
             (< 0 (cdr a)))))

  (local (in-theory (enable integerp)))

  (defthm booleanp-of-integerp
    (booleanp (integerp x)))

  (defthm integerp-when-natp
    (implies (natp x)
             (integerp x))))


(defsection ifix

  (definlined ifix (a)
    (declare (xargs :guard t))
    (if (integerp a)
        a
      0))

  (local (in-theory (enable integerp ifix)))

  (defthm ifix-under-iff
    (iff (ifix a)
         t))

  (defthm integerp-of-ifix
    (equal (integerp (ifix a))
           t))

  (defthm ifix-when-integerp-cheap
    (implies (integerp a)
             (equal (ifix a)
                    a))
    :rule-classes ((:rewrite :backchain-limit-lst 2)))

  (defthm ifix-when-not-integerp-cheap
    (implies (not (integerp a))
             (equal (ifix a)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm ifix-of-ifix
    (equal (ifix (ifix a))
           (ifix a)))

  (defthm equal-of-ifix-of-self
    ;; No symmetric rule because of term order
    (equal (equal a (ifix a))
           (integerp a))))


(defsection zip

  (definline zip (a)
    (declare (xargs :guard t))
    (or (not (integerp a))
        (equal a 0)))

  (local (in-theory (enable zip integerp ifix)))

  (defthm booleanp-of-zip
    (equal (booleanp (zip a))
           t))

  (defthm zip-when-integerp-cheap
    (implies (integerp a)
             (equal (zip a)
                    (equal a 0)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm zip-when-not-integerp-cheap
    (implies (not (integerp a))
             (equal (zip a)
                    t))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm integerp-when-not-zip-cheap
    (implies (not (zip a))
             (equal (integerp a)
                    t))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm ifix-when-zip-cheap
    (implies (zip a)
             (equal (ifix a)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm zip-of-ifix
    (equal (zip (ifix a))
           (zip a)))

  (defthm equal-of-zero-and-ifix
    ;; No symmetric rule because of term order
    (equal (equal 0 (ifix a))
           (zip a)))

  (definlined fast-zip (a)
    (declare (xargs :guard (integerp a)))
    (equal a 0))

  (defthm fast-zip-removal
    (implies (force (integerp a))
             (equal (fast-zip a)
                    (zip a)))
    :hints(("Goal" :in-theory (enable fast-zip)))))



(defsection ineg

  (defund ineg (a)
    (declare (xargs :guard t))
    (let ((a (ifix a)))
      (cond ((consp a)
             (cdr a))
            ((equal a 0)
             0)
            (t
             (cons 'minus a)))))

  (local (in-theory (enable integerp ineg ifix zip)))

  (defthm ineg-under-iff
    (iff (ineg a)
         t))

  (defthm integerp-of-ineg
    (equal (integerp (ineg a))
           t))

  (defthm ineg-of-ifix
    (equal (ineg (ifix a))
           (ineg a)))

  (defthm zip-of-ineg
    (equal (zip (ineg a))
           (zip a)))

  (defthm |(equal 0 (ineg a))|
    (equal (equal 0 (ineg a))
           (zip a)))

  (defthm |(ineg (ineg a))|
    (equal (ineg (ineg a))
           (ifix a))))


(defsection i+

  (defund i+ (a b)
    (declare (xargs :guard t))
    (let ((a (ifix a))
          (b (ifix b)))
      (if (consp a)
          (if (consp b)
              ;; -5 + -3 = -(5 + 3)
              (cons 'minus (+ (cdr a) (cdr b)))
            ;; Subtle: to avoid creating -0, we need to arrange the IF tests so
            ;; that the inequality is strict on the negative side.  That is, we
            ;; check (< b (cdr a)) here instead of (< a (cdr b)), because that
            ;; way the (equal a b) case makes a +0 instead of a -0.
            (if (< b (cdr a))
                ;; -5 + 3 = -(5 - 3)
                (cons 'minus (- (cdr a) b))
              ;; -3 + 5 = 5 - 3 and the zero case
              (- b (cdr a))))
        (if (consp b)
            (if (< a (cdr b))
                ;; 3 + -5 = -(5 - 3)
                (cons 'minus (- (cdr b) a))
              ;; 5 + -3 = 5 - 3
              (- a (cdr b)))
          ;; 5 + 3
          (+ a b)))))

  (local (in-theory (enable i+ integerp zip ifix)))

  (defthm i+-under-iff
    (iff (i+ a b)
         t))

  (defthm integerp-of-i+
    (equal (integerp (i+ a b))
           t))

  (defthm commutativity-of-i+
    (equal (i+ a b)
           (i+ b a)))

  (defthm associativity-of-i+
    (equal (i+ (i+ a b) c)
           (i+ a (i+ b c))))

  (defthm commutativity-of-i+-two
    (equal (i+ a (i+ b c))
           (i+ b (i+ a c))))

  (defthm gather-constants-from-i+-of-i+
    (implies (and (syntaxp (ACL2::quotep a))
                  (syntaxp (ACL2::quotep b)))
             (equal (i+ a (i+ b c))
                    (i+ (i+ a b) c))))

  (defthmd i+-completion-left
    (implies (not (integerp a))
             (equal (i+ a b)
                    (ifix b))))

  (defthmd i+-completion-right
    (implies (not (integerp b))
             (equal (i+ a b)
                    (ifix a))))

  (defthm i+-when-zip-left-cheap
    (implies (zip a)
             (equal (i+ a b)
                    (ifix b)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm i+-when-zip-right-cheap
    (implies (zip b)
             (equal (i+ a b)
                    (ifix a)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm i+-of-zero-left
    (equal (i+ 0 b)
           (ifix b)))

  (defthm i+-of-zero-right
    (equal (i+ a 0)
           (ifix a)))

  (defthm i+-of-ifix-left
    (equal (i+ (ifix a) b)
           (i+ a b)))

  (defthm i+-of-ifix-right
    (equal (i+ a (ifix b))
           (i+ a b))))


(defsection fast-i+

  (defund fast-i+ (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (consp a)
        (if (consp b)
            (cons 'minus (+ (cdr a) (cdr b)))
          (if (< b (cdr a))
              (cons 'minus (- (cdr a) b))
            (- b (cdr a))))
      (if (consp b)
          (if (< a (cdr b))
              (cons 'minus (- (cdr b) a))
            (- a (cdr b)))
        (+ a b))))

  (local (in-theory (enable fast-i+ i+)))

  (defthm fast-i+-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-i+ a b)
                    (i+ a b)))))


(defsection i<

  (defund i< (a b)
    (declare (xargs :guard t))
    (let ((a (ifix a))
          (b (ifix b)))
      (if (consp a)
          (if (consp b)
              ;; -5 < -3 = 3 < 5
              (< (cdr b) (cdr a))
            ;; -5 < 3 = T
            t)
        (if (consp b)
            ;; 5 < -3 = NIL
            nil
          ;; 5 < 3, natural case
          (< a b)))))

  (definline i<= (a b)
    ;; We just leave this enabled
    (declare (xargs :guard t))
    (not (i< b a)))

  (local (in-theory (enable i< i+ integerp ifix zip)))

  (defthm booleanp-of-i<
    (equal (booleanp (i< a b))
           t))

  (defthm irreflexivity-of-i<
    (equal (i< a a)
           nil))

  (defthm i<-completion-left
    (implies (not (integerp a))
             (equal (i< a b)
                    (i< 0 b)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm i<-completion-right
    (implies (not (integerp b))
             (equal (i< a b)
                    (i< a 0)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm i<-of-ifix-left
    (equal (i< (ifix a) b)
           (i< a b)))

  (defthm i<-of-ifix-right
    (equal (i< a (ifix b))
           (i< a b)))

  (defthm antisymmetry-of-i<
    (implies (i< a b)
             (equal (i< b a)
                    nil)))

  (defthm transitivity-of-i<
    (implies (and (i< a b)
                  (i< b c))
             (i< a c)))

  (defthm trichotomy-of-i<
    (implies (and (not (equal (ifix a) (ifix b)))
                  (not (i< a b)))
             (equal (i< b a)
                    t)))

  (defthm one-i+-trick
    (implies (i< a b)
             (equal (i< b (i+ 1 a))
                    nil)))

  (defthm |(i< 0 (ineg a))|
    (equal (i< 0 (ineg a))
           (i< a 0))
    :hints(("Goal" :in-theory (enable ineg))))

  (defthm |(i< (ineg a) 0)|
    (equal (i< (ineg a) 0)
           (i< 0 a))
    :hints(("Goal" :in-theory (enable ineg))))

  (defthm transitivity-of-i<-two
    (implies (and (i< a b)
                  (not (i< c b)))
             (equal (i< a c)
                    t)))

  (defthm transitivity-of-i<-three
    (implies (and (not (i< b a))
                  (i< b c))
             (equal (i< a c)
                    t)))

  (defthm transitivity-of-i<-four
    (implies (and (not (i< b a))
                  (not (i< c b)))
             (equal (i< c a)
                    nil))))


(defsection fast-i<

  (defund fast-i< (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (if (consp a)
        (if (consp b)
            ;; -5 < -3 = 3 < 5
            (< (cdr b) (cdr a))
          ;; -5 < 3 = T
          t)
      (if (consp b)
          ;; 5 < -3 = NIL
          nil
        ;; 5 < 3, natural case
        (< a b))))

  (defthm fast-i<-removal
    (implies (force (and (integerp a)
                         (integerp b)))
             (equal (fast-i< a b)
                    (i< a b)))
    :hints(("Goal" :in-theory (enable fast-i< i<))))

  (definline fast-i<= (a b)
    ;; We just leave this enabled
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (not (fast-i< b a))))



(defsection i<-of-sums

  (local (in-theory (enable i< i+ integerp ifix zip)))

  (defthm |(i< (i+ a b) (i+ a c))|
    (equal (i< (i+ a b) (i+ a c))
           (i< b c)))

  (defthm |(i< a (i+ a b))|
    (equal (i< a (i+ a b))
           (i< 0 b)))

  (defthm |(i< a (i+ b a))|
    (equal (i< a (i+ b a))
           (i< 0 b)))

  (defthm |(i< (i+ a b) a)|
    (equal (i< (i+ a b) a)
           (i< b 0)))

  (defthm |(i< (i+ b a) a)|
    (equal (i< (i+ b a) a)
           (i< b 0)))

  (local (in-theory (disable i< i+ ifix integerp zip)))

  (defthm |(i< a (i+ b c a))|
    (equal (i< a (i+ b (i+ c a)))
           (i< 0 (i+ b c))))

  (defthm |(i< a (i+ b a c))|
    (equal (i< a (i+ b (i+ a c)))
           (i< 0 (i+ b c))))

  (defthm |(i< a (i+ b c d a))|
    (equal (i< a (i+ b (i+ c (i+ d a))))
           (i< 0 (i+ b (i+ c d)))))

  (defthm |(i< a (i+ b c a d))|
    (equal (i< a (i+ b (i+ c (i+ a d))))
           (i< 0 (i+ b (i+ c d)))))

  (defthm |(i< a (i+ b c d e a))|
    (equal (i< a (i+ b (i+ c (i+ d (i+ e a)))))
           (i< 0 (i+ b (i+ c (i+ d e))))))

  (defthm |(i< a (i+ b c d a e))|
    (equal (i< a (i+ b (i+ c (i+ d (i+ a e)))))
           (i< 0 (i+ b (i+ c (i+ d e))))))

  (defthm |(i< a (i+ b c d e f a))|
    (equal (i< a (i+ b (i+ c (i+ d (i+ e (i+ f a))))))
           (i< 0 (i+ b (i+ c (i+ d (i+ e f)))))))

  (defthm |(i< a (i+ b c d e a f))|
    (equal (i< a (i+ b (i+ c (i+ d (i+ e (i+ a f))))))
           (i< 0 (i+ b (i+ c (i+ d (i+ e f)))))))

  (defthm |(i< (i+ a b) (i+ c a))|
    (equal (i< (i+ a b) (i+ c a))
           (i< b c)))

  (defthm |(i< (i+ b a) (i+ c a))|
    (equal (i< (i+ b a) (i+ c a))
           (i< b c)))

  (defthm |(i< (i+ b a) (i+ a c))|
    (equal (i< (i+ b a) (i+ a c))
           (i< b c)))

  (defthm |(i< (i+ a b) (i+ c a d))|
    (equal (i< (i+ a b) (i+ c (i+ a d)))
           (i< b (i+ c d))))

  (defthm |(i< (i+ b a c) (i+ d a))|
    (equal (i< (i+ b (i+ a c)) (i+ d a))
           (i< (i+ b c) d)))

  (local (in-theory (enable i< i+ ifix integerp zip)))

  (defthm |(i<= a b), c > 0 --> (i< a (i+ b c))|
    (implies (and (i<= a b)
                  (not (zp c)))
             (equal (i< a (i+ b c))
                    t)))

  (defthm |(i<= a b), c > 0 --> (i< a (i+ c b))|
    (implies (and (i<= a b)
                  (not (zp c)))
             (equal (i< a (i+ c b))
                    t)))

  (local (in-theory (disable i< i+ ifix integerp zip)))

  (defthm |(i< c a), (i<= d b) --> (i< (i+ c d) (i+ a b))|
    (implies (and (i< c a)
                  (i<= d b))
             (equal (i< (i+ c d) (i+ a b))
                    t))
    :hints(("Goal" :use ((:instance transitivity-of-i<-three
                                    (a (i+ c d))
                                    (b (i+ c b))
                                    (c (i+ a b)))))))

  (defthm |(i< c a), (i<= d b) --> (i< (i+ c d) (i+ b a))|
    (implies (and (i< c a)
                  (i<= d b))
             (equal (i< (i+ c d) (i+ b a))
                    t)))

  (defthm |(i<= c a), (i< d b) --> (i< (i+ c d) (i+ a b))|
    (implies (and (i<= c a)
                  (i< d b))
             (equal (i< (i+ c d) (i+ a b))
                    t))
    :hints(("Goal" :use ((:instance |(i< c a), (i<= d b) --> (i< (i+ c d) (i+ b a))|
                                    (c d) (a b) (d c) (b a))))))

  (defthm |(i<= c a), (i< d b) --> (i< (i+ c d) (i+ b a))|
    (implies (and (i<= c a)
                  (i< d b))
             (equal (i< (i+ c d) (i+ b a))
                    t)))

  (defthm |(i<= c a), (i<= d b) --> (i<= (i+ c d) (i+ a b))|
    (implies (and (i<= c a)
                  (i<= d b))
             (equal (i< (i+ a b) (i+ c d))
                    nil))
    :hints(("Goal" :use ((:instance transitivity-of-i<-four
                                    (a (i+ c d))
                                    (b (i+ c b))
                                    (c (i+ a b)))))))

  (defthm |(i<= c a), (i<= d b) --> (i<= (i+ c d) (i+ b a))|
    (implies (and (i<= c a)
                  (i<= d b))
             (equal (i< (i+ b a) (i+ c d))
                    nil))))



(defsection equality-of-sums

  (local (in-theory (enable i< i+ ifix integerp zip)))

  (defthm |(= a (i+ a b))|
    (equal (equal a (i+ a b))
           (and (integerp a)
                (zip b))))

  (defthm |(= a (i+ b a))|
    (equal (equal a (i+ b a))
           (and (integerp a)
                (zip b))))

  (local (in-theory (disable i< i+ ifix integerp zip)))

  (encapsulate
    ()
    (defthm |lemma for (= (i+ a b) (i+ a c))|
      (implies (and (integerp b)
                    (integerp c)
                    (equal (i+ a b) (i+ a c)))
               (equal b c))
      :rule-classes nil
      :hints(("Goal"
              :in-theory (disable |(i< (i+ a b) (i+ a c))|)
              :use ((:instance |(i< (i+ a b) (i+ a c))| (a a) (b b) (c c))
                    (:instance |(i< (i+ a b) (i+ a c))| (a a) (b c) (c b))))))

    (defthm |(= (i+ a b) (i+ a c))|
      (equal (equal (i+ a b) (i+ a c))
             (equal (ifix b) (ifix c)))
      :hints(("Goal"
              :in-theory (enable ifix)
              :use ((:instance |lemma for (= (i+ a b) (i+ a c))|
                               (a a)
                               (b (ifix b))
                               (c (ifix c))))))))

  (defthm |(= (i+ a b) (i+ c a))|
    (equal (equal (i+ a b) (i+ c a))
           (equal (ifix b) (ifix c))))

  (defthm |(= (i+ b a) (i+ c a))|
    (equal (equal (i+ b a) (i+ c a))
           (equal (ifix b) (ifix c))))

  (defthm |(= (i+ b a) (i+ a c))|
    (equal (equal (i+ b a) (i+ a c))
           (equal (ifix b) (ifix c))))

  (defthm |(= 0 (i+ a b))|
    (equal (equal 0 (i+ a b))
           (equal (ifix a) (ineg b)))
    :hints(("Goal" :in-theory (enable i< i+ ifix integerp zip ineg))))

  (encapsulate
    ()
    (defthmd |lemma for (= (i+ a x b) (i+ c x d))|
      ;; hackery with names to make it commute them nicely
      (equal (equal (i+ e (i+ b c))
                    (i+ d (i+ b f)))
             (equal (i+ e c)
                    (i+ d f))))

    (defthm |(= (i+ a x b) (i+ c x d))|
      (equal (equal (i+ a (i+ x b))
                    (i+ c (i+ x d)))
             (equal (i+ a b)
                    (i+ c d)))
      :hints(("Goal" :in-theory (enable |lemma for (= (i+ a x b) (i+ c x d))|))))))



(defsection i<-squeeze-laws

  (defthm i<-squeeze-law-one
    (implies (not (i< b a))
             (equal (i< (i+ 1 a) b)
                    (and (not (equal (ifix a) (ifix b)))
                         (not (equal (i+ 1 a) (ifix b))))))
    :hints(("Goal" :in-theory (enable ifix integerp i< i+))))

  (defthm i<-squeeze-law-two
    (implies (not (i< b a))
             (equal (i< b (i+ 1 a))
                    (equal (ifix b) (ifix a))))
    :hints(("Goal" :in-theory (enable ifix integerp i< i+))))

  (defthm i<-squeeze-law-three
    (implies (i< a b)
             (equal (i< (i+ 1 a) b)
                    (not (equal (ifix b) (i+ 1 a)))))
    :hints(("Goal" :in-theory (enable ifix)))))



(defsection i-

; We just leave this enabled, and use (i+ a (ineg b)) as our normal form.  Now,
; we don't have any special handling for sums with inegs in them.  It might be
; worth thinking about how to make a fancy commutativity rule that will either
; ignore the ineg for the purposes of sorting the sum, or to always make the
; negative terms on the right?  I'm not sure which would work better.

  (definline i- (a b)
    (declare (xargs :guard t))
    (i+ a (ineg b)))

  (definline fast-i- (a b)
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (fast-i+ a (ineg b))))



(defsection minus-basics

  (defthm |(i+ a (ineg a))|
    (equal (i+ a (ineg a))
           0)
    :hints(("Goal" :in-theory (enable i+ ineg ifix integerp))))

  (defthm |(ineg (i+ a b))|
    (equal (ineg (i+ a b))
           (i+ (ineg a) (ineg b)))
    :hints(("Goal" :in-theory (enable i+ ineg ifix integerp))))

  (defthm |(i+ a b (ineg b))|
    (equal (i+ a (i+ b (ineg b)))
           (ifix a)))

  (defthm |(i+ a b (ineg a))|
    (equal (i+ a (i+ b (ineg a)))
           (ifix b))
    :hints(("Goal"
            :in-theory (disable commutativity-of-i+-two)
            :use ((:instance commutativity-of-i+-two
                             (a a) (b b) (c (ineg a)))))))

  (defthm |(i+ a (ineg a) b)|
    (equal (i+ a (i+ (ineg a) b))
           (ifix b)))

  (defthm |(i< (i+ a (ineg b)) c)|
    (equal (i< (i+ a (ineg b)) c)
           (i< a (i+ b c)))
    :hints(("Goal" :in-theory (enable i+ ineg i< ifix integerp))))

  (defthm |(i< (i+ (ineg a) b) c)|
    (equal (i< (i+ (ineg a) b) c)
           (i< b (i+ a c))))

  (defthm |(i< a (i+ b (ineg c)))|
    (equal (i< a (i+ b (ineg c)))
           (i< (i+ a c) b))
    :hints(("Goal" :in-theory (enable i+ ineg i< ifix integerp))))

  (defthm |(i< a (i+ b (i+ c (ineg d))))|
    (equal (i< a (i+ b (i+ c (ineg d))))
           (i< (i+ a d) (i+ b c)))
    :hints(("Goal"
            :in-theory (disable |(i< (i+ a b) (i+ a c))|)
            :use ((:instance |(i< (i+ a b) (i+ a c))|
                             (a d)
                             (b a)
                             (c (i+ b (i+ c (ineg d)))))))))

  (defthm |(i< a (i+ b (i+ (ineg c) d)))|
    (equal (i< a (i+ b (i+ (ineg c) d)))
           (i< (i+ a c) (i+ b d))))

  (defthm |(= (i+ a (ineg b)) c)|
    (equal (equal (i+ a (ineg b)) c)
           (if (integerp c)
               (equal (ifix a) (i+ b c))
             nil))
    :hints(("Goal" :in-theory (enable integerp ifix i+ ineg))))

  (defthm |(= (i+ (ineg a) b) c)|
    (equal (equal (i+ (ineg a) b) c)
           (if (integerp c)
               (equal (ifix b) (i+ a c))
             nil)))

  (defthm |(= c (i+ a (ineg b)))|
    (equal (equal c (i+ a (ineg b)))
           (if (integerp c)
               (equal (ifix a) (i+ b c))
             nil)))

  (defthm |(= c (i+ (ineg a) b))|
    (equal (equal c (i+ (ineg a) b))
           (if (integerp c)
               (equal (ifix b) (i+ a c))
             nil))))



(defsection i-constant-gathering

  (defthm gather-constants-from-i<-of-i+
    (implies (and (syntaxp (ACL2::quotep const))
                  (syntaxp (ACL2::quotep const2)))
             (equal (i< (i+ const x) const2)
                    (i< x (i+ const2 (ineg const))))))

  (defthm gather-constants-from-i<-of-i+-two
    (implies (and (syntaxp (ACL2::quotep const))
                  (syntaxp (ACL2::quotep const2)))
             (equal (i< const (i+ const2 x))
                    (i< (i+ const (ineg const2)) x))))

  (defthm gather-constants-from-i<-of-i+-and-i+
    (implies (and (syntaxp (ACL2::quotep a))
                  (syntaxp (ACL2::quotep b)))
             (equal (i< (i+ a x) (i+ b y))
                    (i< x (i+ b (i+ (ineg a) y))))))

  (defthm gather-constants-from-equal-of-i+-and-i+
    (implies (and (syntaxp (ACL2::quotep c1))
                  (syntaxp (ACL2::quotep c2)))
             (equal (equal (i+ c1 x) (i+ c2 y))
                    (equal (ifix x) (i+ (i+ c2 (ineg c1)) y))))
    :hints(("Goal"
            :in-theory (disable |(= (i+ a b) (i+ a c))|)
            :use ((:instance |(= (i+ a b) (i+ a c))|
                             (a (ineg c1))
                             (b (i+ c1 x))
                             (c (i+ c2 y))))))))


