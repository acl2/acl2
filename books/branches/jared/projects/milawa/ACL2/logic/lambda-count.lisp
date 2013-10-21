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

#|

(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defun ord.simple-increment (depth amount x)
  ;; Returns the ordinal x + amount * w^depth
  (declare (xargs :guard (and (ordp depth)
                              (natp amount)
                              (ordp x))))
  (if (consp x)
      (if (equal (car x)




;; A size-alist is a mapping of ranks to values, where all of the ranks and
;; values are natural numbers.

(defund simple-ordinalp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (natp (car (car x)))
           (natp (cdr (car x)))
           (simple-ordinalp (cdr x)))
    (equal x 0)))

(defthm simple-ordinalp-when-not-consp
  (implies (not (consp x))
           (equal (simple-ordinalp x)
                  (equal x 0)))
  :hints(("Goal" :in-theory (enable simple-ordinalp))))

(defthm simple-ordinalp-of-cons
  (equal (simple-ordinalp (cons a x))
         (and (natp (car a))
              (natp (cdr a))
              (simple-ordinalp x)))
  :hints(("Goal" :in-theory (enable simple-ordinalp))))

(defthm booleanp-of-simple-ordinalp
  (equal (booleanp (simple-ordinalp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordp-when-simple-ordinalp
  (implies (simple-ordinalp x)
           (equal (ordp x)
                  t))
  :hints(("Goal"
          :in-theory (enable ordp)
          :induct (cdr-induction x))))


(defmap :map (size-alistp x)
        :key (natp x)
        :val (natp x)
        :key-list (nat-listp x)
        :val-list (nat-listp x)
        :val-of-nil nil)

(defthm forcing-size-alistp-of-update
  ;; BOZO add to defmap?
  (implies (force (and (size-alistp map)
                       (natp key)
                       (natp val)))
           (equal (size-alistp (update key val map))
                  t))
  :hints(("Goal" :in-theory (enable update))))

;; Adding two size-alists means adding the values associated with each rank.

(defund size-alist-add-aux (domain x y)
  (declare (xargs :guard (and (nat-listp domain)
                              (size-alistp x)
                              (size-alistp y))
                  :verify-guards nil))
  (if (consp domain)
      (let ((x-value (cdr (lookup (car domain) x)))
            (y-value (cdr (lookup (car domain) y))))
        (update (car domain)
                (+ x-value y-value)
                (size-alist-add-aux (cdr domain) x y)))
    nil))

(defthm forcing-size-alistp-of-size-alist-add-aux
  (implies (force (and (nat-listp domain)
                       (size-alistp x)
                       (size-alistp y)))
           (equal (size-alistp (size-alist-add-aux domain x y))
                  t))
  :hints(("Goal"
          :in-theory (enable size-alist-add-aux))))

(verify-guards size-alist-add-aux)








;; A challenge.  Walk over a term and do the beta-reduction in place, but still
;; know that your function terminates.  Let's just write a function that counts the
;; beta-reduced size of a term.


;; we want to devise a measure which satisfies four properties.

;; the measure we are looking at is consider the "depth" of each lambda as follows.
;; a top level lambda has depth 0
;; an embedded lambda has depth 1
;; etc.
;; so each lambda's depth is the number of lambdas above it.  we want to show that
;; the depth of our lambdas decreases.

;; is it equivalent to consider the depth of each lambda as the maximum depth of
;; any subterm plus one?  i think so, then the top level lambda has the highest
;; depth and things work out more nicely.


(defmap

(defund alist-plus (x y)
  (declare


(defund lambda-count (flag x)
  ;; We return an ordinal that describes the number and ranks of lambdas in this
  ;; term.
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) 0)
            ((logic.variablep x) 0)
            ((logic.functionp x)

             (flag-beta-depth 'list (logic.function-args x)))
            ((logic.lambdap x)
             ;; one more than maximum of any argument or body's depth
             (+ 1 (max (flag-beta-depth 'term (logic.lambda-body x))
                       (flag-beta-depth 'list (logic.lambda-actuals x)))))
            (t 0))
    (if (consp x)
        (max (flag-beta-depth 'term (car x))
             (flag-beta-depth 'list (cdr x)))
      0)))








(set-well-founded-relation ord<)
(set-measure-function rank)

(defund flag-beta-depth (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) 0)
            ((logic.variablep x) 0)
            ((logic.functionp x)
             ;; maximum of any argument's depth
             (flag-beta-depth 'list (logic.function-args x)))
            ((logic.lambdap x)
             ;; one more than maximum of any argument or body's depth
             (+ 1 (max (flag-beta-depth 'term (logic.lambda-body x))
                       (flag-beta-depth 'list (logic.lambda-actuals x)))))
            (t 0))
    (if (consp x)
        (max (flag-beta-depth 'term (car x))
             (flag-beta-depth 'list (cdr x)))
      0)))

(


|#