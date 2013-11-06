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
(include-book "../defderiv/defderiv")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defax axiom-reflexivity
  (= x x))

(defax axiom-equality
  (v (!= x1 y1)
     (v (!= x2 y2)
        (v (!= x1 x2)
           (= y1 y2)))))

(defax axiom-t-not-nil
  (!= t nil))

(defax axiom-equal-when-same
  (v (!= x y)
     (= (equal x y) t)))

(defax axiom-equal-when-diff
  (v (= x y)
     (= (equal x y) nil)))

(defax axiom-if-when-nil
  (v (!= x nil)
     (= (if x y z) z)))

(defax axiom-if-when-not-nil
  (v (= x nil)
     (= (if x y z) y)))



(defax axiom-consp-of-cons
  (= (consp (cons x y)) t))

(defax axiom-car-of-cons
  (= (car (cons x y)) x))

(defax axiom-cdr-of-cons
  (= (cdr (cons x y)) y))

(defax axiom-consp-nil-or-t
  (v (= (consp x) nil)
     (= (consp x) t)))

(defax axiom-car-when-not-consp
  (v (!= (consp x) nil)
     (= (car x) nil)))

(defax axiom-cdr-when-not-consp
  (v (!= (consp x) nil)
     (= (cdr x) nil)))

(defax axiom-cons-of-car-and-cdr
  (v (= (consp x) nil)
     (= (cons (car x) (cdr x)) x)))



(defax axiom-symbolp-nil-or-t
  (v (= (symbolp x) nil)
     (= (symbolp x) t)))

(defax axiom-symbol-<-nil-or-t
  (v (= (symbol-< x y) nil)
     (= (symbol-< x y) t)))

(defax axiom-irreflexivity-of-symbol-<
  (= (symbol-< x x) nil))

(defax axiom-antisymmetry-of-symbol-<
  (v (= (symbol-< x y) nil)
     (= (symbol-< y x) nil)))

(defax axiom-transitivity-of-symbol-<
  (v (= (symbol-< x y) nil)
     (v (= (symbol-< y z) nil)
        (= (symbol-< x z) t))))

(defax axiom-trichotomy-of-symbol-<
  (v (= (symbolp x) nil)
     (v (= (symbolp y) nil)
        (v (= (symbol-< x y) t)
           (v (= (symbol-< y x) t)
              (= x y))))))

(defax axiom-symbol-<-completion-left
  (v (= (symbolp x) t)
     (= (symbol-< x y)
        (symbol-< nil y))))

(defax axiom-symbol-<-completion-right
  (v (= (symbolp y) t)
     (= (symbol-< x y)
        (symbol-< x nil))))



(defax axiom-disjoint-symbols-and-naturals
  (v (= (symbolp x) nil)
     (= (natp x) nil)))

(defax axiom-disjoint-symbols-and-conses
  (v (= (symbolp x) nil)
     (= (consp x) nil)))

(defax axiom-disjoint-naturals-and-conses
  (v (= (natp x) nil)
     (= (consp x) nil)))



(defax axiom-natp-nil-or-t
  (v (= (natp x) nil)
     (= (natp x) t)))

(defax axiom-natp-of-plus
  (= (natp (+ a b)) t))

(defax axiom-commutativity-of-+
  (= (+ a b) (+ b a)))

(defax axiom-associativity-of-+
  (= (+ (+ a b) c)
     (+ a (+ b c))))

(defax axiom-plus-when-not-natp-left
  (v (= (natp a) t)
     (= (+ a b) (+ 0 b))))

(defax axiom-plus-of-zero-when-natural
  (v (= (natp a) nil)
     (= (+ a 0) a)))

(defax axiom-<-nil-or-t
  (v (= (< x y) nil)
     (= (< x y) t)))

(defax axiom-irreflexivity-of-<
  (= (< a a) nil))

(defax axiom-less-of-zero-right
  (= (< a 0) nil))

(defax axiom-less-of-zero-left-when-natp
  (v (= (natp a) nil)
     (= (< 0 a)
        (if (equal a 0)
            nil
          t))))

(defax axiom-less-completion-left
  (v (= (natp a) t)
     (= (< a b)
        (< 0 b))))

(defax axiom-less-completion-right
  (v (= (natp b) t)
     (= (< a b)
        nil)))

(defax axiom-transitivity-of-<
  (v (= (< a b) nil)
     (v (= (< b c) nil)
        (= (< a c) t))))

(defax axiom-trichotomy-of-<-when-natp
  (v (= (natp a) nil)
     (v (= (natp b) nil)
        (v (= (< a b) t)
           (v (= (< b a) t)
              (= a b))))))

(defax axiom-one-plus-trick
  (v (= (< a b) nil)
     (= (< b (+ 1 a)) nil)))

(defax axiom-natural-less-than-one-is-zero
  (v (= (natp a) nil)
     (v (= (< a 1) nil)
        (= a 0))))

(defax axiom-less-than-of-plus-and-plus
  (= (< (+ a b) (+ a c))
     (< b c)))



;; BOZO we could probably "weaken" some of these axioms and assume less

(defax axiom-natp-of-minus
  (= (natp (- a b)) t))

(defax axiom-minus-when-subtrahend-as-large
  (v (= (< b a) t)
     (= (- a b) 0)))

(defax axiom-minus-cancels-summand-right
  (= (- (+ a b) b)
     (if (natp a)
         a
       0)))

(defax axiom-less-of-minus-left
  (v (= (< b a) nil)
     (= (< (- a b) c)
        (< a (+ b c)))))

(defax axiom-less-of-minus-right
  (= (< a (- b c))
     (< (+ a c) b)))

(defax axiom-plus-of-minus-right
  (v (= (< c b) nil)
     (= (+ a (- b c))
        (- (+ a b) c))))

(defax axiom-minus-of-minus-right
  (v (= (< c b) nil)
     (= (- a (- b c))
        (- (+ a c) b))))

(defax axiom-minus-of-minus-left
  (= (- (- a b) c)
     (- a (+ b c))))

(defax axiom-equal-of-minus-property
  (v (= (< b a) nil)
     (= (equal (- a b) c)
        (equal a (+ b c)))))


(defax axiom-closed-universe
  (v (= (natp x) t)
     (v (= (symbolp x) t)
        (= (consp x) t))))


(defax definition-of-rank
  (= (rank x)
     (if (consp x)
         (+ 1
            (+ (rank (car x))
               (rank (cdr x))))
       0)))

(ACL2::make-event
 `(defax definition-of-ord<
    (= (ord< x y)
       ,(logic.translate '(cond ((not (consp x))
                                 (if (consp y) t (< x y)))
                                ((not (consp y)) nil)
                                ((not (equal (car (car x)) (car (car y))))
                                 (ord< (car (car x)) (car (car y))))
                                ((not (equal (cdr (car x)) (cdr (car y))))
                                 (< (cdr (car x)) (cdr (car y))))
                                (t (ord< (cdr x) (cdr y))))))))

(ACL2::make-event
 `(defax definition-of-ordp
    (= (ordp x)
       ,(logic.translate '(if (not (consp x))
                              (natp x)
                              (and (consp (car x))
                                   (ordp (car (car x)))
                                   (not (equal (car (car x)) 0))
                                   (< 0 (cdr (car x)))
                                   (ordp (cdr x))
                                   (if (consp (cdr x))
                                       (ord< (car (car (cdr x))) (car (car x)))
                                       t)))))))


