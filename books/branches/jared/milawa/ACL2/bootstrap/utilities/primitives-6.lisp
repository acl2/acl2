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
(include-book "primitives-5")
(%interactive)


(%autoprove not-equal-when-less)
(%autoprove not-equal-when-less-two)

(%autoprove |a <= d, b+c <= e --> b+a+c <= d+e|)

(%autoprove |(< (+ a b) (+ c b d))|)

(%autoprove |(< (+ a b c)) (+ d c))|
            (%disable default
                      |(< (+ b a c) (+ d a))|
                      |[OUTSIDE](< (+ b a c) (+ d a))|)
            (%use (%instance (%thm |(< (+ b a c) (+ d a))|)
                             (a c) (b a) (c b) (d d))))

(%autoprove |a <= b, b <= c --> a < 1+c|)
(%autoprove |b <= c, a <= b --> a < 1+c|)

(%autoprove natp-of-max)
(%autoprove equal-of-max-and-zero)
(%autoprove max-of-zero-left)
(%autoprove max-of-zero-right)

(%autoprove natp-of-min)
(%autoprove equal-of-min-and-zero)
(%autoprove min-of-zero-left)
(%autoprove min-of-zero-right)


;; Special admission for ordp, ord<, and rank.  We don't use %autoadmit, instead we add
;; their definitions as axioms, which we convert into theorems now.

(defsection ordp
  (%prove (%rule ordp
                 :lhs (ordp x)
                 :rhs (if (not (consp x))
                          (natp x)
                        (and (consp (car x))
                             (ordp (car (car x)))
                             (not (equal (car (car x)) 0))
                             (< 0 (cdr (car x)))
                             (ordp (cdr x))
                             (if (consp (cdr x))
                                 (ord< (car (car (cdr x))) (car (car x)))
                               t)))))
  (%use (build.axiom (definition-of-ordp)))
  (%cleanup)
  (%qed)
  ;; Don't enable; definition
  )

(defsection ord<
  (%prove (%rule ord<
                 :lhs (ord< x y)
                 :rhs (cond ((not (consp x))
                             (if (consp y) t (< x y)))
                            ((not (consp y)) nil)
                            ((not (equal (car (car x)) (car (car y))))
                             (ord< (car (car x)) (car (car y))))
                            ((not (equal (cdr (car x)) (cdr (car y))))
                             (< (cdr (car x)) (cdr (car y))))
                            (t (ord< (cdr x) (cdr y))))))
  (%use (build.axiom (definition-of-ord<)))
  (%cleanup)
  (%qed)
  ;; Don't enable; definition
  )

(defsection rank
  (%prove (%rule rank
                 :lhs (rank x)
                 :rhs (if (consp x)
                          (+ 1 (+ (rank (car x))
                                  (rank (cdr x))))
                        0)))
  (%use (build.axiom (definition-of-rank)))
  (%cleanup)
  (%qed)
  ;; Don't enable; definition
  )



;; NOTE: we had to move booleanp-of-ord< after the rank stuff.
;; NOTE: we had to move booleanp-of-ordp after the rank stuff.

(%autoprove ord<-when-naturals
            (%restrict default ord< (equal x 'x)))

(%autoprove ordp-when-natp
            (%restrict default ordp (equal x 'x)))

(%autoprove natp-of-rank
            (%restrict default rank (equal x 'x)))

(%autoprove rank-when-not-consp
            (%restrict default rank (equal x 'x)))

(%autoprove rank-of-cons
            (%restrict default rank (equal x '(cons x y))))

(%autoprove |(< 0 (rank x))|
            (%restrict default rank (equal x 'x)))

(%autoprove ordp-of-rank)

(%autoprove rank-of-car
            (%restrict default rank (equal x 'x)))

(%autoprove rank-of-car-weak
            (%restrict default rank (equal x 'x)))

(%autoprove rank-of-cdr
            (%restrict default rank (equal x 'x)))

(%autoprove rank-of-cdr-weak
            (%restrict default rank (equal x 'x)))

(%autoprove rank-of-second)

(%autoprove rank-of-second-weak
            (%use (%instance (%thm transitivity-of-<-three)
                             (a (rank (car (cdr x))))
                             (b (rank (cdr x)))
                             (c (rank x)))))

(%autoprove rank-of-third)

(%autoprove rank-of-third-weak
            (%use (%instance (%thm transitivity-of-<-three)
                             (a (rank (third x)))
                             (b (rank (cdr x)))
                             (c (rank x)))))

(%autoprove rank-of-fourth)

(%autoprove rank-of-fourth-weak
            (%use (%instance (%thm transitivity-of-<-four)
                             (a (rank (fourth x)))
                             (b (rank (cdr x)))
                             (c (rank x)))))

(%autoprove booleanp-of-ord<
            ;; Note.  This is a simpler induction scheme than ACL2 picks.  Originally I
            ;; used ACL2's induction scheme, but with this simpler scheme the proof was
            ;; about 1/5 the size.
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x (cdr x)) (y (cdr y)))
                       ((x (car (car x))) (y (car (car y)))))))
            (%split)
            (%restrict default ord< (equal x 'x) (equal y 'y)))

(%autoprove booleanp-of-ordp
            ;; Again we use a simpler induction scheme than ACL2.
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x (car (car x))))
                       ((x (cdr x))))))
            (%split)
            (%restrict default ordp (equal x 'x)))




;; We don't need an equivalent of ord<-is-well-founded; that's just to instruct ACL2
;; about which well founded relation to use.

(%autoadmit two-nats-measure)

(%autoprove ordp-of-two-nats-measure
            (%enable default two-nats-measure)
            (%restrict default ordp (equal x '(CONS (CONS '1 (+ '1 A)) (NFIX B)))))

(%autoprove ord<-of-two-nats-measure
            (%enable default two-nats-measure)
            (%restrict default ord< (equal x '(CONS (CONS '1 (+ '1 A1)) (NFIX B1)))))

(%autoadmit three-nats-measure)

(%autoprove ordp-of-three-nats-measure
            (%enable default three-nats-measure)
            (%restrict default ordp (or (equal x '(CONS (CONS '2 (+ '1 A)) (CONS (CONS '1 (+ '1 B)) (NFIX C))))
                                        (equal x '(CONS (CONS '1 (+ '1 B)) (NFIX C))))))

(%autoprove ord<-of-three-nats-measure
            (%enable default three-nats-measure)
            (%restrict default ord< (or (equal x '(CONS (CONS '2 (+ '1 A1)) (CONS (CONS '1 (+ '1 B1)) (NFIX C1))))
                                        (equal x '(CONS (CONS '1 (+ '1 B1)) (NFIX C1))))))
