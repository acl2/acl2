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
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (logic.term-< x y) allows us to compare the "sizes" of terms.  This function
;; is inspired by ACL2's term-order, although the particulars of the order are
;; somewhat different.  We order the terms according to three criteria:
;;
;; 1. Our first consideration is the number of variable occurrences in a term.
;; If x has more variable occurrences than y, we say that x is bigger than y.
;;
;; 2. If x and y have the same number of variables, our next consideration is
;; the number of function name occurrences.  If x has more function name
;; occurrences than y, we say that x is bigger than y.
;;
;; 3. If x and y have the same number of variable and functions symbol
;; occurrences, we count sizes of constants within the terms, where sizes are
;; given as follows:
;;
;;   - The size of a natural number is its value
;;   - The size of a symbol is 1
;;   - The size of a cons is one more than the sizes of its car and cdr
;;
;; 4. As a last resort, if x and y have the same sizes of constants, we order
;; them "arbitrarily" according to <<, which is a total order on Milawa
;; objects.

(defund logic.fast-constant-size (x acc)
  (declare (xargs :guard (natp acc)
                  :verify-guards nil
                  :export (cond ((symbolp x)
                                 (+ 1 acc))
                                ((natp x)
                                 (+ x acc))
                                (t
                                 (logic.fast-constant-size (cdr x)
                                                           (logic.fast-constant-size (car x) (+ 1 acc)))))))
  (cond ((symbolp x)
         (+ 1 acc))
        ((natp x)
         (+ x acc))
        ((not (consp x))
         ;; HACK: Special case for ACL2 compatibility.  We should not need
         ;; this case in Milawa.
         (nfix acc))
        (t
         (logic.fast-constant-size (cdr x)
                                   (logic.fast-constant-size (car x) (+ 1 acc))))))

(defthm forcing-natp-of-logic.fast-constant-size
  (implies (force (natp acc))
           (equal (natp (logic.fast-constant-size x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.fast-constant-size))))

(verify-guards logic.fast-constant-size)

(definlined logic.constant-size (x)
  (declare (xargs :guard t))
  (logic.fast-constant-size x 0))

(defund logic.slow-constant-size (x)
  (declare (xargs :guard t
                  :export (cond ((symbolp x)
                                 1)
                                ((natp x)
                                 x)
                                (t
                                 (+ 1 (+ (logic.slow-constant-size (car x))
                                         (logic.slow-constant-size (cdr x))))))))
  (cond ((symbolp x)
         1)
        ((natp x)
         x)
        ((not (consp x))
         ;; HACK: Special case for ACL2 compatibility.  We should not need
         ;; this case in Milawa.
         0)
        (t
         (+ 1 (+ (logic.slow-constant-size (car x))
                 (logic.slow-constant-size (cdr x)))))))

(defthm natp-of-logic.slow-constant-size
  (equal (natp (logic.slow-constant-size x))
         t)
  :hints(("Goal" :in-theory (enable logic.slow-constant-size))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthmd lemma-for-definition-of-logic.constant-size
   (implies (force (natp acc))
            (equal (logic.fast-constant-size x acc)
                   (+ (logic.slow-constant-size x) acc)))
   :hints(("Goal"
           :in-theory (enable logic.fast-constant-size logic.slow-constant-size)
           :induct (logic.fast-constant-size x acc)))))

(defthmd definition-of-logic.constant-size
  (equal (logic.constant-size x)
         (cond ((symbolp x) 1)
               ((natp x) x)
               ((not (consp x))
                ;; HACK: Special case for ACL2 compatibility.  We should not need
                ;; this case in Milawa.
                0)
               (t
                (+ 1 (+ (logic.constant-size (car x))
                        (logic.constant-size (cdr x)))))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.constant-size
                                    logic.slow-constant-size
                                    lemma-for-definition-of-logic.constant-size))))

(defthm forcing-fast-constant-size-removal
  (implies (force (natp acc))
           (equal (logic.fast-constant-size x acc)
                  (+ (logic.constant-size x) acc)))
  :hints(("Goal" :in-theory (enable logic.constant-size
                                    lemma-for-definition-of-logic.constant-size))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.constant-size))))

(defthm natp-of-logic.constant-size
  (equal (natp (logic.constant-size x))
         t)
  :hints(("Goal"
          :in-theory (enable definition-of-logic.constant-size)
          :induct (car-cdr-induction x))))




(defund logic.flag-count-variable-occurrences (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (natp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) (+ 1 acc))
            ((logic.functionp x)
             (logic.flag-count-variable-occurrences 'list (logic.function-args x) acc))
            ((logic.lambdap x)
             (logic.flag-count-variable-occurrences 'list (logic.lambda-actuals x) acc))
            (t acc))
    (if (consp x)
        (logic.flag-count-variable-occurrences 'list (cdr x)
                                               (logic.flag-count-variable-occurrences 'term (car x) acc))
      acc)))

(defthm forcing-natp-of-logic.flag-count-variable-occurrences
  (implies (force (natp acc))
           (equal (natp (logic.flag-count-variable-occurrences flag x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.flag-count-variable-occurrences))))

(verify-guards logic.flag-count-variable-occurrences)

(definlined logic.count-variable-occurrences (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-count-variable-occurrences 'term x 0))

(definlined logic.count-variable-occurrences-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (logic.flag-count-variable-occurrences 'list x 0))

(defund logic.slow-count-variable-occurrences (flag x)
  (declare (xargs :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) 0)
            ((logic.variablep x) 1)
            ((logic.functionp x)
             (logic.slow-count-variable-occurrences 'list (logic.function-args x)))
            ((logic.lambdap x)
             (logic.slow-count-variable-occurrences 'list (logic.lambda-actuals x)))
            (t 0))
    (if (consp x)
        (+ (logic.slow-count-variable-occurrences 'term (car x))
           (logic.slow-count-variable-occurrences 'list (cdr x)))
      0)))

(defthmd lemma-logic.flag-count-variable-occurrences-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-variable-occurrences flag x acc)
                  (+ (logic.slow-count-variable-occurrences flag x) acc)))
  :hints(("Goal"
          :in-theory (enable logic.flag-count-variable-occurrences
                             logic.slow-count-variable-occurrences)
          :induct (logic.flag-count-variable-occurrences flag x acc))))

(defthmd definition-of-logic.count-variable-occurrences
  (equal (logic.count-variable-occurrences x)
         (cond ((logic.constantp x) 0)
               ((logic.variablep x) 1)
               ((logic.functionp x)
                (logic.count-variable-occurrences-list (logic.function-args x)))
               ((logic.lambdap x)
                (logic.count-variable-occurrences-list (logic.lambda-actuals x)))
               (t 0)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-variable-occurrences
                                    logic.count-variable-occurrences-list
                                    logic.slow-count-variable-occurrences
                                    lemma-logic.flag-count-variable-occurrences-removal
                                    ))))

(defthmd definition-of-logic.count-variable-occurrences-list
  (equal (logic.count-variable-occurrences-list x)
         (if (consp x)
             (+ (logic.count-variable-occurrences (car x))
                (logic.count-variable-occurrences-list (cdr x)))
           0))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-variable-occurrences
                                    logic.count-variable-occurrences-list
                                    logic.slow-count-variable-occurrences
                                    lemma-logic.flag-count-variable-occurrences-removal
                                    ))))

(defthm logic.flag-count-variable-occurrences-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-variable-occurrences flag x acc)
                  (if (equal flag 'term)
                      (+ (logic.count-variable-occurrences x) acc)
                    (+ (logic.count-variable-occurrences-list x) acc))))
  :hints(("Goal"
          :in-theory (enable lemma-logic.flag-count-variable-occurrences-removal
                             logic.count-variable-occurrences
                             logic.count-variable-occurrences-list
                             logic.slow-count-variable-occurrences))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-variable-occurrences))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-variable-occurrences-list))))


(defthm logic.count-variables-occurrences-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.count-variable-occurrences-list x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-variable-occurrences-list))))

(defthm logic.count-variables-occurrences-list-of-cons
  (equal (logic.count-variable-occurrences-list (cons a x))
         (+ (logic.count-variable-occurrences a)
            (logic.count-variable-occurrences-list x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-variable-occurrences-list))))

(defthms-flag
  :thms ((term natp-of-logic.count-variable-occurrences
               (equal (natp (logic.count-variable-occurrences x))
                      t))
         (t natp-of-logic.count-variable-occurrences-list
            (equal (natp (logic.count-variable-occurrences-list x))
                   t)))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable definition-of-logic.count-variable-occurrences))))

(defthm logic.count-variable-occurrences-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.count-variable-occurrences x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-variable-occurrences))))

(defthm logic.count-variable-occurrences-when-logic.variablep
  (implies (logic.variablep x)
           (equal (logic.count-variable-occurrences x)
                  1))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-variable-occurrences))))





(defund logic.flag-count-function-occurrences (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (natp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) acc)
            ((logic.functionp x)
             (logic.flag-count-function-occurrences 'list (logic.function-args x) (+ 1 acc)))
            ((logic.lambdap x)
             (logic.flag-count-function-occurrences 'list (logic.lambda-actuals x) (+ 1 acc)))
            (t acc))
    (if (consp x)
        (logic.flag-count-function-occurrences 'list (cdr x)
         (logic.flag-count-function-occurrences 'term (car x) acc))
      acc)))

(defthm forcing-natp-of-logic.flag-count-function-occurrences
  (implies (force (natp acc))
           (equal (natp (logic.flag-count-function-occurrences flag x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.flag-count-function-occurrences))))

(verify-guards logic.flag-count-function-occurrences)

(definlined logic.count-function-occurrences (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-count-function-occurrences 'term x 0))

(definlined logic.count-function-occurrences-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (logic.flag-count-function-occurrences 'list x 0))

(defund logic.slow-count-function-occurrences (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) 0)
            ((logic.variablep x) 0)
            ((logic.functionp x)
             (+ 1 (logic.slow-count-function-occurrences 'list (logic.function-args x))))
            ((logic.lambdap x)
             (+ 1 (logic.slow-count-function-occurrences 'list (logic.lambda-actuals x))))
            (t 0))
    (if (consp x)
        (+ (logic.slow-count-function-occurrences 'term (car x))
           (logic.slow-count-function-occurrences 'list (cdr x)))
      0)))

(defthmd lemma-forcing-logic.flag-count-function-occurrences-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-function-occurrences flag x acc)
                  (+ (logic.slow-count-function-occurrences flag x) acc)))
  :hints(("Goal"
          :in-theory (enable logic.flag-count-function-occurrences
                             logic.slow-count-function-occurrences)
          :induct (logic.flag-count-function-occurrences flag x acc))))

(defthmd definition-of-logic.count-function-occurrences
  (equal (logic.count-function-occurrences x)
         (cond ((logic.constantp x) 0)
               ((logic.variablep x) 0)
               ((logic.functionp x)
                (+ 1 (logic.count-function-occurrences-list (logic.function-args x))))
               ((logic.lambdap x)
                (+ 1 (logic.count-function-occurrences-list (logic.lambda-actuals x))))
               (t 0)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-function-occurrences
                                    logic.count-function-occurrences-list
                                    logic.slow-count-function-occurrences
                                    lemma-forcing-logic.flag-count-function-occurrences-removal))))

(defthmd definition-of-logic.count-function-occurrences-list
  (equal (logic.count-function-occurrences-list x)
         (if (consp x)
             (+ (logic.count-function-occurrences (car x))
                (logic.count-function-occurrences-list (cdr x)))
           0))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-function-occurrences
                                    logic.count-function-occurrences-list
                                    logic.slow-count-function-occurrences
                                    lemma-forcing-logic.flag-count-function-occurrences-removal))))

(defthm logic.flag-count-function-occurrences-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-function-occurrences flag x acc)
                  (if (equal flag 'term)
                      (+ (logic.count-function-occurrences x) acc)
                    (+ (logic.count-function-occurrences-list x) acc))))
  :hints(("Goal" :in-theory (enable lemma-forcing-logic.flag-count-function-occurrences-removal
                                    logic.count-function-occurrences
                                    logic.count-function-occurrences-list
                                    logic.slow-count-function-occurrences
                                    ))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-function-occurrences))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-function-occurrences-list))))

(defthm logic.count-function-occurrences-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.count-function-occurrences-list x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-function-occurrences-list))))

(defthm logic.count-function-occurrences-list-of-cons
  (equal (logic.count-function-occurrences-list (cons a x))
         (+ (logic.count-function-occurrences a)
            (logic.count-function-occurrences-list x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-function-occurrences-list))))

(defthms-flag
  :thms ((term natp-of-logic.count-function-occurrences
               (equal (natp (logic.count-function-occurrences x))
                      t))
         (t natp-of-logic.count-function-occurrences-list
            (equal (natp (logic.count-function-occurrences-list x))
                   t)))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable definition-of-logic.count-function-occurrences))))

(defthm logic.count-function-occurrences-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.count-function-occurrences x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-function-occurrences))))

(defthm logic.count-function-occurrences-positive-when-logic.functionp
  (implies (logic.functionp x)
           (equal (equal (logic.count-function-occurrences x) 0)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-function-occurrences))))

(defthm logic.count-function-occurrences-positive-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (equal (logic.count-function-occurrences x) 0)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-function-occurrences))))




(defund logic.flag-count-constant-sizes (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (natp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             (logic.fast-constant-size (logic.unquote x) acc))
            ((logic.variablep x)
             acc)
            ((logic.functionp x)
             (logic.flag-count-constant-sizes 'list (logic.function-args x) acc))
            ((logic.lambdap x)
             (logic.flag-count-constant-sizes 'list (logic.lambda-actuals x) acc))
            (t acc))
    (if (consp x)
        (logic.flag-count-constant-sizes 'list (cdr x)
                                         (logic.flag-count-constant-sizes 'term (car x) acc))
      acc)))

(defthm forcing-natp-of-logic.flag-count-constant-sizes
  (implies (force (natp acc))
           (equal (natp (logic.flag-count-constant-sizes flag x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.flag-count-constant-sizes))))

(verify-guards logic.flag-count-constant-sizes)

(definlined logic.count-constant-sizes (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-count-constant-sizes 'term x 0))

(definlined logic.count-constant-sizes-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (logic.flag-count-constant-sizes 'list x 0))

(defund logic.slow-count-constant-sizes (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             (logic.constant-size (logic.unquote x)))
            ((logic.variablep x)
             0)
            ((logic.functionp x)
             (logic.slow-count-constant-sizes 'list (logic.function-args x)))
            ((logic.lambdap x)
             (logic.slow-count-constant-sizes 'list (logic.lambda-actuals x)))
            (t 0))
    (if (consp x)
        (+ (logic.slow-count-constant-sizes 'term (car x))
           (logic.slow-count-constant-sizes 'list (cdr x)))
      0)))

(defthm natp-of-logic.slow-count-constant-sizes
  (equal (natp (logic.slow-count-constant-sizes flag x))
         t)
  :hints(("Goal" :in-theory (enable logic.slow-count-constant-sizes))))

(defthm lemma-forcing-logic.flag-count-constant-sizes-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-constant-sizes flag x acc)
                  (+ (logic.slow-count-constant-sizes flag x) acc)))
  :hints(("Goal"
          :in-theory (enable logic.flag-count-constant-sizes
                             logic.slow-count-constant-sizes)
          :induct (logic.flag-count-constant-sizes flag x acc))))

(defthmd definition-of-logic.count-constant-sizes
  (equal (logic.count-constant-sizes x)
         (cond ((logic.constantp x)
                (logic.constant-size (logic.unquote x)))
               ((logic.variablep x)
                0)
               ((logic.functionp x)
                (logic.count-constant-sizes-list (logic.function-args x)))
               ((logic.lambdap x)
                (logic.count-constant-sizes-list (logic.lambda-actuals x)))
               (t 0)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-constant-sizes
                                    logic.count-constant-sizes-list
                                    logic.slow-count-constant-sizes))))

(defthmd definition-of-logic.count-constant-sizes-list
  (equal (logic.count-constant-sizes-list x)
         (if (consp x)
             (+ (logic.count-constant-sizes (car x))
                (logic.count-constant-sizes-list (cdr x)))
           0))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.count-constant-sizes
                                    logic.count-constant-sizes-list
                                    logic.slow-count-constant-sizes))))

(defthm logic.flag-count-constant-sizes-removal
  (implies (force (natp acc))
           (equal (logic.flag-count-constant-sizes flag x acc)
                  (if (equal flag 'term)
                      (+ (logic.count-constant-sizes x) acc)
                    (+ (logic.count-constant-sizes-list x) acc))))
  :hints(("Goal" :in-theory (enable logic.count-constant-sizes-list
                                    logic.count-constant-sizes
                                    lemma-forcing-logic.flag-count-constant-sizes-removal
                                    logic.slow-count-constant-sizes))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-constant-sizes))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.count-constant-sizes-list))))

(defthm logic.count-constant-sizes-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.count-constant-sizes-list x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-constant-sizes-list))))

(defthm logic.count-constant-sizes-list-of-cons
  (equal (logic.count-constant-sizes-list (cons a x))
         (+ (logic.count-constant-sizes a)
            (logic.count-constant-sizes-list x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.count-constant-sizes-list))))

(defthms-flag
  :thms ((term natp-of-logic.count-constant-sizes
               (equal (natp (logic.count-constant-sizes x))
                      t))
         (t natp-of-logic.count-constant-sizes-list
            (equal (natp (logic.count-constant-sizes-list x))
                   t)))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable definition-of-logic.count-constant-sizes))))





(defund logic.flag-count-term-sizes (flag x var-acc fn-acc const-acc)
  ;; This is a combined count that only does one recursive pass over x.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (natp var-acc)
                              (natp fn-acc)
                              (natp const-acc))
                  :verify-guards nil))
  ;; Returns (CONS VAR-ACC (CONS FN-ACC CONST-ACC))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             (cons var-acc
                   (cons fn-acc
                         (logic.fast-constant-size (logic.unquote x) const-acc))))
            ((logic.variablep x)
             (cons (+ 1 var-acc) (cons fn-acc const-acc)))
            ((logic.functionp x)
             (logic.flag-count-term-sizes 'list
                                          (logic.function-args x)
                                          var-acc (+ 1 fn-acc) const-acc))
            ((logic.lambdap x)
             (logic.flag-count-term-sizes 'list
                                          (logic.lambda-actuals x)
                                          var-acc (+ 1 fn-acc) const-acc))
            (t
             (cons var-acc (cons fn-acc const-acc))))
    (if (consp x)
        (let ((car-counts (logic.flag-count-term-sizes 'term
                                                       (car x)
                                                       var-acc fn-acc const-acc)))
          (logic.flag-count-term-sizes 'list
                                       (cdr x)
                                       (car car-counts)
                                       (car (cdr car-counts))
                                       (cdr (cdr car-counts))))
      (cons var-acc
            (cons fn-acc const-acc)))))

(defthm natp-of-car-of-logic.flag-count-term-sizes
  (implies (natp var-acc)
           (natp (car (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc))))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(defthm natp-of-cdar-of-logic.flag-count-term-sizes
  (implies (natp fn-acc)
           (natp (car (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc)))))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(defthm natp-of-cddr-of-logic.flag-count-term-sizes
  (implies (natp const-acc)
           (natp (cdr (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc)))))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(verify-guards logic.flag-count-term-sizes)

(defthm car-of-logic.flag-count-term-sizes
  (equal (car (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc))
         (logic.flag-count-variable-occurrences flag x var-acc))
  :hints(("Goal"
          :in-theory (e/d (logic.flag-count-term-sizes
                           logic.flag-count-variable-occurrences)
                          ((acl2::force))))))

(defthm cadr-of-logic.flag-count-term-sizes
  (equal (car (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc)))
         (logic.flag-count-function-occurrences flag x fn-acc))
  :hints(("Goal"
          :in-theory (e/d (logic.flag-count-term-sizes
                           logic.flag-count-function-occurrences)
                          ((acl2::force))))))

(defthm cddr-of-logic.flag-count-term-sizes
  (equal (cdr (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc)))
         (logic.flag-count-constant-sizes flag x const-acc))
  :hints(("Goal"
          :in-theory (e/d (logic.flag-count-term-sizes
                           logic.flag-count-constant-sizes)
                          ((acl2::force))))))

(defthmd consp-of-logic.flag-count-term-sizes-1
  (consp (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(defthmd consp-of-logic.flag-count-term-sizes-2
  (consp (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc)))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(defthmd consp-of-logic.flag-count-term-sizes-3
  (implies (natp const-acc)
           (equal (consp (cdr (cdr (logic.flag-count-term-sizes flag x var-acc fn-acc const-acc))))
                  nil))
  :hints(("Goal" :in-theory (e/d (logic.flag-count-term-sizes)
                                 ((acl2::force))))))

(defund logic.count-term-sizes (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-count-term-sizes 'term x 0 0 0))

(defthm definition-of-logic.count-term-sizes
  (implies (logic.termp x)
           (equal (logic.count-term-sizes x)
                  (cons (logic.count-variable-occurrences x)
                        (cons (logic.count-function-occurrences x)
                              (logic.count-constant-sizes x)))))
  :hints(("Goal" :in-theory (enable logic.count-term-sizes
                                    consp-of-logic.flag-count-term-sizes-1
                                    consp-of-logic.flag-count-term-sizes-2
                                    consp-of-logic.flag-count-term-sizes-3))))





(defund logic.term-< (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (let ((counts-x (logic.count-term-sizes x))
        (counts-y (logic.count-term-sizes y)))
    (let ((x-numvars (car counts-x))
          (y-numvars (car counts-y)))
      (cond
       ((< x-numvars y-numvars) t)
       ((< y-numvars x-numvars) nil)
       (t
        (let ((x-numfuns (car (cdr counts-x)))
              (y-numfuns (car (cdr counts-y))))
          (cond
           ((< x-numfuns y-numfuns) t)
           ((< y-numfuns x-numfuns) nil)
           (t
            (let ((x-const-sizes (cdr (cdr counts-x)))
                  (y-const-sizes (cdr (cdr counts-y))))
              (cond
               ((< x-const-sizes y-const-sizes) t)
               ((< y-const-sizes x-const-sizes) nil)
               (t
                (<< x y))))))))))))

(defthmd definition-of-logic.term-<
  (equal (logic.term-< x y)
         (let ((x-numvars (logic.count-variable-occurrences x))
               (y-numvars (logic.count-variable-occurrences y)))
           (cond
            ((< x-numvars y-numvars) t)
            ((< y-numvars x-numvars) nil)
            (t
             (let ((x-numfuns (logic.count-function-occurrences x))
                   (y-numfuns (logic.count-function-occurrences y)))
               (cond
                ((< x-numfuns y-numfuns) t)
                ((< y-numfuns x-numfuns) nil)
                (t
                 (let ((x-const-sizes (logic.count-constant-sizes x))
                       (y-const-sizes (logic.count-constant-sizes y)))
                   (cond
                    ((< x-const-sizes y-const-sizes) t)
                    ((< y-const-sizes x-const-sizes) nil)
                    (t
                     (<< x y)))))))))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.term-<
                                    logic.count-term-sizes))))


(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-<))))

(defthm booleanp-of-logic.term-<
  (equal (booleanp (logic.term-< x y))
         t)
  :hints(("Goal" :in-theory (enable definition-of-logic.term-<))))

(defthm irreflexivity-of-logic.term-<
  (equal (logic.term-< x x)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-logic.term-<))))

(defthm antisymmetry-of-logic.term-<
  (implies (logic.term-< x y)
           (equal (logic.term-< y x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-<))))

(defthm transitivity-of-logic.term-<
  (implies (and (logic.term-< x y)
                (logic.term-< y z))
           (equal (logic.term-< x z)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-<))))

(defthm trichotomy-of-logic.term-<
  (implies (and (not (logic.term-< x y))
                (not (equal x y)))
           (equal (logic.term-< y x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-<))))

(defthm transitivity-of-logic.term-<-two
  (implies (and (logic.term-< x y)
                (not (logic.term-< z y)))
           (equal (logic.term-< x z)
                  t))
  :hints(("Goal" :cases ((logic.term-< y z)))
         ("Subgoal 2"
          :in-theory (disable trichotomy-of-logic.term-<)
          :use ((:instance trichotomy-of-logic.term-<
                           (x y)
                           (y z))))))

(defthm forcing-transitivity-of-logic.term-<-three
  (implies (and (not (logic.term-< y x))
                (logic.term-< y z))
           (equal (logic.term-< x z)
                  t)))

(defthm forcing-transitivity-of-logic.term-<-four
  (implies (and (not (logic.term-< y x))
                (not (logic.term-< z y)))
           (equal (logic.term-< x z)
                  (not (equal x z)))))

(defthm forcing-minimality-of-constants-under-logic.term-<
  (implies (and (logic.constantp x)
                (not (logic.constantp y))
                (force (logic.termp x))
                (force (logic.termp y)))
           (equal (logic.term-< x y)
                  t))
  :hints(("Goal"
          :in-theory (enable definition-of-logic.term-<)
          :cases ((logic.variablep y)
                  (logic.functionp y)))))



(deflist logic.all-terms-largerp (b x)
  (logic.term-< b x)
  :guard (and (logic.termp b)
              (logic.term-listp x)))

(defthm all-terms-larger-when-all-terms-larger-than-something-bigger
  (implies (and (logic.all-terms-largerp a x)
                (logic.term-< b a))
           (equal (logic.all-terms-largerp b x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-<-when-memberp-of-logic.all-terms-largerp-two
  (implies (and (logic.all-terms-largerp a x)
                (memberp b x))
           (equal (logic.term-< b a)
                  nil)))

(defthm logic.term-<-when-memberp-of-logic.all-terms-largerp-two-alt
  (implies (and (memberp b x)
                (logic.all-terms-largerp a x))
           (equal (logic.term-< b a)
                  nil)))

(defthm memberp-when-logic.all-terms-larger-cheap
   (implies (logic.all-terms-largerp a x)
            (equal (memberp a x)
                   nil))
   :rule-classes ((:rewrite :backchain-limit-lst 1))
   :hints(("Goal" :induct (cdr-induction x))))





(defund logic.all-terms-largerp-badguy (a x)
  (declare (xargs :guard (and (logic.termp a)
                              (logic.term-listp x))))
  (if (consp x)
      (if (logic.term-< a (car x))
          (logic.all-terms-largerp-badguy a (cdr x))
        (car x))
    nil))

(defthm logic.all-terms-largerp-badguy-when-not-consp
  (implies (not (consp x))
           (equal (logic.all-terms-largerp-badguy a x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.all-terms-largerp-badguy))))

(defthm logic.all-terms-largerp-badguy-of-cons
  (equal (logic.all-terms-largerp-badguy a (cons b x))
         (if (logic.term-< a b)
             (logic.all-terms-largerp-badguy a x)
           b))
  :hints(("Goal" :in-theory (enable logic.all-terms-largerp-badguy))))

(defthmd logic.all-terms-largerp-badguy-membership-property
  (implies (logic.all-terms-largerp-badguy a x)
           (and (memberp (logic.all-terms-largerp-badguy a x) x)
                (not (logic.term-< a (logic.all-terms-largerp-badguy a x)))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-terms-largerp-when-not-logic.all-terms-largerp-badguy
  (implies (and (not (logic.all-terms-largerp-badguy a x))
                (force (logic.term-listp x)))
           (equal (logic.all-terms-largerp a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
