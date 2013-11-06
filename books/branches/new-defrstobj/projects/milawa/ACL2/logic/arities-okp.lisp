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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Arity checking of large structures (e.g., worlds and traces) using simple
;; functions in the logic.term-atblp style can become quite expensive.  That
;; is, this approach is O(n*m) where n is the number of functions named in
;; the structure, and m is the number of functions in the arity table.
;;
;; Since these structures often have repeated function names, we can
;; drastically reduce n by first collecting up all a list of "obligations" --
;; the function names encountered in the structure, paired with the number of
;; arguments they have been given -- and then sorting it to remove duplicates.

(defund logic.arities-okp (arities atbl)
  (declare (xargs :guard (logic.arity-tablep atbl)))

;; This function checks whether a list of collected up arities, which should be
;; a list of (function-name . length) pairs, are all okay according to an arity
;; table.
;;
;; We do not expect to actually run this function, and it is only a convenient
;; definition for reasoning.  Instead, see below for logic.fast-arities-okp, an
;; equivalent version that implements some important optimizations.

  (if (consp arities)
      (and (consp (car arities))
           (equal (lookup (car (car arities)) atbl)
                  (car arities))
           (logic.arities-okp (cdr arities) atbl))
    t))

(defthm logic.arities-okp-when-not-consp
  (implies (not (consp arities))
           (equal (logic.arities-okp arities atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.arities-okp))))

(defthm logic.arities-okp-of-cons
  (equal (logic.arities-okp (cons a x) atbl)
         (and (consp a)
              (equal (lookup (car a) atbl) a)
              (logic.arities-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.arities-okp))))

(defthm booleanp-of-logic.arities-okp
  (equal (booleanp (logic.arities-okp arities atbl))
         t)
  :hints(("Goal" :induct (cdr-induction arities))))

(defthm logic.arities-okp-of-list-fix
  (equal (logic.arities-okp (list-fix x) atbl)
         (logic.arities-okp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.arities-okp-of-app
  (equal (logic.arities-okp (app x y) atbl)
         (and (logic.arities-okp x atbl)
              (logic.arities-okp y atbl)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.arities-okp-of-rev
  (equal (logic.arities-okp (rev x) atbl)
         (logic.arities-okp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.arities-okp-of-cdr
  (implies (logic.arities-okp x atbl)
           (equal (logic.arities-okp (cdr x) atbl)
                  t)))

(defthmd lemma-1-for-logic.arities-okp-when-subsetp
  (implies (and (LOGIC.ARITIES-OKP x ATBL)
                (memberp a x))
           (consp a))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-2-for-logic.arities-okp-when-subsetp
  (implies (and (logic.arities-okp x atbl)
                (memberp a x))
           (EQUAL (LOOKUP (FIRST a) ATBL)
                  a))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.arities-okp-when-subsetp-1
  (implies (and (subsetp x y)
                (logic.arities-okp y atbl))
           (equal (logic.arities-okp x atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-1-for-logic.arities-okp-when-subsetp
                             lemma-2-for-logic.arities-okp-when-subsetp))))

(defthm logic.arities-okp-when-subsetp-2
  (implies (and (logic.arities-okp y atbl)
                (subsetp x y))
           (equal (logic.arities-okp x atbl)
                  t)))



;; We are now ready for our fast version of logic.arities-okp.  We sort the
;; collected obligations and also sort the arity table.  Then we can just use
;; the ordered list subsetp check, which is O(n) instead of O(n^2) like
;; ordinary subsetp, to perform the check.  Hence, our total time becomes O(n
;; log_2 n) for the sorting.
;;
;; The most heavy optimization we can do is to sort both the obligations and
;; also to sort the arity table.  This allows us to use an ordered list subset
;; check, which is O(n) instead of O(n^2) like the ordinary subset routine, to
;; perform the check.  Hence, the total time is essentially O( max (n log_2 n ,
;; m log_2 m) ).
;;
;; In certain cases, it may be more expensive to sort the arity table than to
;; perform the actual check.  To try to get a feel for this, we looked at how
;; long it took to sort the arity table in the bare level10 directory.  Sorting
;; it 1000 times took 5.37 seconds, so we are going to estimate the cost of
;; mergesort-map at .005 seconds.
;;
;; (defconstant *atbl* (MILAWA::tactic.harness->atbl (w state)))
;; (progn
;;   (ccl::gc)
;;   (time (loop for i fixnum from 1 to 1000
;;               do
;;               (MILAWA::mergesort-map *atbl*)))
;;   nil)
;;
;; The question then is: when will using the ordered-subsetp check save us more
;; than .005 seconds.  We can pick n objects that are "evenly spaced" through
;; the arity table via every-nth-entry.
;;
;; (defun every-nth-entry-aux (n i x)
;;   (declare (xargs :guard (and (natp n)
;;                               (natp i))))
;;   (if (not (consp x))
;;       nil
;;     (if (zp i)
;;         (cons (car x)
;;               (every-nth-entry-aux n n (cdr x)))
;;       (every-nth-entry-aux n (- i 1) (cdr x)))))
;;
;; (defun every-nth-entry (n x)
;;   (declare (xargs :guard (natp n)))
;;   (every-nth-entry-aux n 0 x))
;;
;; Now, we can do some timing checks, such as shown below, varying the number
;; of entries we take, to get some data.
;;
;; (defparameter *subset* nil)
;; (progn
;;   (ccl::gc)
;;   (setf *subset* (every-nth-entry 8 *atbl*))
;;   (format t "Length of subset is ~a.~%" (len *subset*))
;;   (time (loop for i fixnum from 1 to 1000
;;               do
;;               (MILAWA::logic.arities-okp *subset* *atbl*)))
;;   nil)
;;
;; We find the following results.
;;
;;   Length    Time     Time-per-call
;;   154       3.46s    .0034
;;   189       4.26s    .0042
;;   212       4.76s    .0047
;;   242       5.42s    .0054
;;   283       6.37s    .0063
;;
;; So, as a rough heuristic, we will say that if there are at least 250
;; functions to check, we'd prefer to do sort the atbl and do an ordered check.
;; Otherwise, we'll just do the logic.arities-okp call.
;;
;; In the end, our check is as follows.

(defund logic.fast-arities-okp (x atbl)
  (declare (xargs :guard (logic.arity-tablep atbl)))
  (let ((sorted-x (mergesort x)))
    (if (len-over-250p sorted-x)
        (ordered-list-subsetp (mergesort x)
                              (mergesort-map atbl))
      (logic.arities-okp sorted-x atbl))))



;; Optimization Lemma #1.  Sorting the list of collected obligations, before we
;; check them, does not affect the result.  This is a big improvement since our
;; mergesort operation eats duplicates, and is O(n log_2 n) instead of O(n^2).

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm logic.arities-okp-of-halve-list
   (equal (logic.arities-okp x atbl)
          (and (logic.arities-okp (car (halve-list x)) atbl)
               (logic.arities-okp (cdr (halve-list x)) atbl)))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (disable halve-list-correct
                               logic.arities-okp-of-list-fix
                               logic.arities-okp-when-subsetp-1
                               logic.arities-okp-when-subsetp-2)
          :use ((:instance halve-list-correct)
                (:instance logic.arities-okp-of-list-fix))))))

(defthm logic.arities-okp-of-merge-lists
  (equal (logic.arities-okp (merge-lists x y) atbl)
         (and (logic.arities-okp x atbl)
              (logic.arities-okp y atbl)))
  :hints(("Goal"
          :in-theory (e/d (merge-lists)
                          (logic.arities-okp-when-subsetp-1
                           logic.arities-okp-when-subsetp-2)))))

(defthm logic.arities-okp-of-mergesort
  (equal (logic.arities-okp (mergesort x) atbl)
         (logic.arities-okp x atbl))
  :hints(("Goal" :in-theory (enable mergesort))
         ("Subgoal *1/3" :use ((:instance logic.arities-okp-of-halve-list)))))



;; Optimization Lemma #2.  Sorting the arity table (using mergesort-map) does
;; not affect the result.  This is mainly a lemma for our next optimization.

(defthm logic.arities-okp-of-mergesort-map
  (equal (logic.arities-okp x (mergesort-map atbl))
         (logic.arities-okp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))



;; Optimization Lemma #3.  Logic.arities-okp can be replaced by an ordinary
;; subset check, as long as the arity table has unique keys.  (And via our use
;; of mergesort-map, we know that the keys are unique).

(defthm mapp-of-cdr-when-mapp
  (implies (mapp x)
           (equal (mapp (cdr x))
                  t))
  :hints(("Goal" :in-theory (enable mapp))))

(defthm memberp-of-nil-when-mapp
  (implies (mapp x)
           (equal (memberp nil x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-1-for-logic.arities-okp-when-subsetp-of-unique-atbl
  (implies (and (mapp x)
                (uniquep (domain x))
                (memberp a x))
           (equal (lookup (first a) x)
                  (cons-fix a)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-2-for-logic.arities-okp-when-subsetp-of-unique-atbl
  (implies (subsetp (cdr x) y)
           (equal (subsetp x y)
                  (if (consp x)
                      (memberp (car x) y)
                    t))))

(defthmd lemma-3-for-logic.arities-okp-when-subsetp-of-unique-atbl
   (implies (and (equal (lookup key x) val)
                 (mapp x)
                 (consp val))
            (equal (memberp val x)
                   t))
    :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-4-for-logic.arities-okp-when-subsetp-of-unique-atbl
  (implies (and (memberp a x)
                (mapp x))
           (equal (consp a)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd logic.arities-okp-when-subsetp-of-unique-atbl
  (implies (and (mapp atbl)
                (uniquep (domain atbl)))
           (equal (logic.arities-okp x atbl)
                  (subsetp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-1-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-2-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-3-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-4-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             ))))


;; Finally, we have the main correctness result for logic.fast-arities-okp.

(defthm logic.fast-arities-okp-removal
  (implies (force (mapp atbl))
           (equal (logic.fast-arities-okp x atbl)
                  (logic.arities-okp x atbl)))
  :hints(("Goal"
          :in-theory (enable logic.fast-arities-okp)
          :use ((:instance logic.arities-okp-when-subsetp-of-unique-atbl
                           (atbl (mergesort-map atbl))
                           (x x))))))






;; Now we move on to the matter of actually collecting the obligations.
;;
;; This can be done pretty efficiently using tail-recursive functions that just
;; throw all of the obligations they find into an accumualtor.  But for
;; reasoning, we also introduce slow functions based on app.  Handling terms is
;; irritatingly verbose because of the mutual recursion, but after that it's
;; not so bad.

(defund logic.flag-slow-term-arities (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (and (equal flag 'list)
                                (logic.term-listp x)))))
  (if (equal flag 'term)
      (cond ((logic.variablep x) nil)
            ((logic.constantp x) nil)
            ((logic.functionp x)
             (let ((args (logic.function-args x)))
               ;; This looks goofy, but it works out with the accumulator
               ;; version so that we can make a tail call here.
               (app (logic.flag-slow-term-arities 'list args)
                    (list (cons (logic.function-name x)
                                (fast-len args 0))))))
            ((logic.lambdap x)
             (let ((actuals (logic.lambda-actuals x))
                   (body    (logic.lambda-body x)))
               (app (logic.flag-slow-term-arities 'term body)
                    (logic.flag-slow-term-arities 'list actuals))))
            (t nil))
    (if (consp x)
        (app (logic.flag-slow-term-arities 'term (car x))
             (logic.flag-slow-term-arities 'list (cdr x)))
      nil)))

(defund logic.slow-term-arities (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-slow-term-arities 'term x))

(defund logic.slow-term-list-arities (x)
  (declare (xargs :guard (logic.term-listp x)))
  (logic.flag-slow-term-arities 'list x))

(defthmd definition-of-logic.slow-term-arities
  (equal (logic.slow-term-arities x)
         (cond ((logic.variablep x) nil)
               ((logic.constantp x) nil)
               ((logic.functionp x)
                (let ((args (logic.function-args x)))
                  (app (logic.slow-term-list-arities args)
                       (list (cons (logic.function-name x)
                                   (fast-len args 0))))))
               ((logic.lambdap x)
                (let ((actuals (logic.lambda-actuals x))
                      (body    (logic.lambda-body x)))
                  (app (logic.slow-term-arities body)
                       (logic.slow-term-list-arities actuals))))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.slow-term-arities
                             logic.slow-term-list-arities)
          :expand ((logic.flag-slow-term-arities 'term x)))))

(defthmd definition-of-logic.slow-term-list-arities
  (equal (logic.slow-term-list-arities x)
         (if (consp x)
             (app (logic.slow-term-arities (car x))
                  (logic.slow-term-list-arities (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.slow-term-arities
                             logic.slow-term-list-arities)
          :expand ((logic.flag-slow-term-arities 'list x)))))

(defthm logic.flag-slow-term-arities-of-term
  (equal (logic.flag-slow-term-arities 'term x)
         (logic.slow-term-arities x))
  :hints(("Goal" :in-theory (enable logic.slow-term-arities))))

(defthm logic.flag-slow-term-arities-of-list
  (equal (logic.flag-slow-term-arities 'list x)
         (logic.slow-term-list-arities x))
  :hints(("Goal" :in-theory (enable logic.slow-term-list-arities))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.slow-term-arities))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.slow-term-list-arities))))

(defthm logic.slow-term-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (logic.slow-term-list-arities x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.slow-term-list-arities))))

(defthm logic.slow-term-list-arities-of-cons
  (equal (logic.slow-term-list-arities (cons a x))
         (app (logic.slow-term-arities a)
              (logic.slow-term-list-arities x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.slow-term-list-arities))))




(defund logic.flag-term-arities (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (true-listp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.variablep x) acc)
            ((logic.constantp x) acc)
            ((logic.functionp x)
             (let ((args (logic.function-args x)))
               (logic.flag-term-arities 'list args
                                        (cons (cons (logic.function-name x)
                                                    (fast-len args 0))
                                              acc))))
            ((logic.lambdap x)
             (logic.flag-term-arities 'term
                                      (logic.lambda-body x)
                                      (logic.flag-term-arities 'list
                                                               (logic.lambda-actuals x)
                                                               acc)))
            (t acc))
    (if (consp x)
        (logic.flag-term-arities 'term (car x)
                                 (logic.flag-term-arities 'list (cdr x) acc))
      acc)))

(in-theory (enable (:induction logic.flag-term-arities)))

(defund logic.term-arities (x acc)
  (declare (xargs :guard (and (logic.termp x)
                              (true-listp acc))
                  :verify-guards nil))
  (logic.flag-term-arities 'term x acc))

(defund logic.term-list-arities (x acc)
  (declare (xargs :guard (and (logic.term-listp x)
                              (true-listp acc))
                  :verify-guards nil))
  (logic.flag-term-arities 'list x acc))

(defthmd definition-of-logic.term-arities
  (equal (logic.term-arities x acc)
         (cond ((logic.variablep x) acc)
               ((logic.constantp x) acc)
               ((logic.functionp x)
                (let ((args (logic.function-args x)))
                  (logic.term-list-arities args
                                           (cons (cons (logic.function-name x)
                                                       (fast-len args 0))
                                                 acc))))
               ((logic.lambdap x)
                (let ((actuals (logic.lambda-actuals x))
                      (body    (logic.lambda-body x)))
                  (logic.term-arities body
                                      (logic.term-list-arities actuals acc))))
               (t acc)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.term-arities
                             logic.term-list-arities)
          :expand ((logic.flag-term-arities 'term x acc)))))

(defthmd definition-of-logic.term-list-arities
  (equal (logic.term-list-arities x acc)
         (if (consp x)
             (logic.term-arities (car x)
                                 (logic.term-list-arities (cdr x) acc))
           acc))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.term-arities
                             logic.term-list-arities)
          :expand ((logic.flag-term-arities 'list x acc)))))

(defthm logic.flag-term-arities-of-term
  (equal (logic.flag-term-arities 'term x acc)
         (logic.term-arities x acc))
  :hints(("Goal" :in-theory (enable logic.term-arities))))

(defthm logic.flag-term-arities-of-list
  (equal (logic.flag-term-arities 'list x acc)
         (logic.term-list-arities x acc))
  :hints(("Goal" :in-theory (enable logic.term-list-arities))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-arities))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-list-arities))))

(defthm logic.term-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (logic.term-list-arities x acc)
                  acc))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-arities))))

(defthm logic.term-list-arities-of-cons
  (equal (logic.term-list-arities (cons a x) acc)
         (logic.term-arities a (logic.term-list-arities x acc)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-arities))))


(defthms-flag
  :thms ((term true-listp-of-logic.slow-term-arities
               (true-listp (logic.slow-term-arities x)))
         (t true-listp-of-logic.slow-term-list-arities
            (true-listp (logic.slow-term-list-arities x))))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :expand (logic.slow-term-arities x))))

(defthms-flag
  :thms ((term true-listp-of-logic.term-arities
               (equal (true-listp (logic.term-arities x acc))
                      (true-listp acc)))
         (t true-listp-of-logic.term-list-arities
            (equal (true-listp (logic.term-list-arities x acc))
                   (true-listp acc))))
  :hints(("Goal"
          :induct (logic.flag-term-arities flag x acc)
          :expand (logic.term-arities x acc))))

(verify-guards logic.flag-term-arities)
(verify-guards logic.term-arities)
(verify-guards logic.term-list-arities)

(defthms-flag
  :shared-hyp (force (true-listp acc))
  :thms ((term logic.term-arities-removal
               (equal (logic.term-arities x acc)
                      (app (logic.slow-term-arities x)
                           acc)))
         (t logic.term-list-arities-removal
            (equal (logic.term-list-arities x acc)
                   (app (logic.slow-term-list-arities x)
                        acc))))
  :hints(("Goal"
          :induct (logic.flag-term-arities flag x acc)
          :expand ((logic.term-arities x acc)
                   (logic.slow-term-arities x)))))

(defthmd lemma-2-for-logic.term-atblp-when-logic.arities-okp-of-logic.slow-term-arities
  (implies (and (EQUAL n (CDR (LOOKUP NAME ATBL)))
                (natp n))
           (iff (lookup name atbl)
                t)))

(defthms-flag
  :thms ((term logic.slow-term-arities-correct
               (implies (force (logic.termp x))
                        (equal (logic.arities-okp (logic.slow-term-arities x) atbl)
                               (logic.term-atblp x atbl))))
         (t logic.slow-term-list-arities-correct
            (implies (force (logic.term-listp x))
                     (equal (logic.arities-okp (logic.slow-term-list-arities x) atbl)
                            (logic.term-list-atblp x atbl)))))
  :hints(("Goal"
          :in-theory (e/d (lemma-2-for-logic.term-atblp-when-logic.arities-okp-of-logic.slow-term-arities)
                          (FORCING-LOGIC.TERM-LIST-ATBLP-OF-LOGIC.FUNCTION-ARGS
                           FORCING-LOOKUP-OF-LOGIC.FUNCTION-NAME))
          :induct (logic.term-induction flag x)
          :expand ((logic.slow-term-arities x)
                   (logic.term-atblp x atbl)))))




;; We now move on to the rest of the structures we need to arity-check.

(defund logic.slow-formula-arities (x)
  (declare (xargs :guard (logic.formulap x)))
  (let ((type (logic.fmtype x)))
    (cond ((equal type 'por*)
           (app (logic.slow-formula-arities (logic.vlhs x))
                (logic.slow-formula-arities (logic.vrhs x))))
          ((equal type 'pnot*)
           (logic.slow-formula-arities (logic.~arg x)))
          ((equal type 'pequal*)
           (app (logic.slow-term-arities (logic.=lhs x))
                (logic.slow-term-arities (logic.=rhs x))))
          (t
           nil))))

(defund logic.formula-arities (x acc)
  (declare (xargs :guard (and (logic.formulap x)
                              (true-listp acc))
                  :verify-guards nil))
  (let ((type (logic.fmtype x)))
    (cond ((equal type 'por*)
           (logic.formula-arities (logic.vlhs x)
                                  (logic.formula-arities (logic.vrhs x) acc)))
          ((equal type 'pnot*)
           (logic.formula-arities (logic.~arg x) acc))
          ((equal type 'pequal*)
           (logic.term-arities (logic.=lhs x)
                               (logic.term-arities (logic.=rhs x) acc)))
          (t
           acc))))

(defthm true-listp-of-logic.formula-arities
  (implies (force (true-listp acc))
           (equal (true-listp (logic.formula-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-arities))))

(verify-guards logic.formula-arities)

(defthm logic.formula-arities-removal
  (implies (force (true-listp acc))
           (equal (logic.formula-arities x acc)
                  (app (logic.slow-formula-arities x) acc)))
  :hints(("Goal" :in-theory (enable logic.formula-arities
                                    logic.slow-formula-arities))))

(defthm logic.slow-formula-arities-correct
  (implies (force (logic.formulap x))
           (equal (logic.arities-okp (logic.slow-formula-arities x) atbl)
                  (logic.formula-atblp x atbl)))
  :hints(("Goal"
          :in-theory (e/d (logic.slow-formula-arities)
                          (forcing-logic.formula-atblp-of-logic.~arg
                           forcing-logic.formula-atblp-of-logic.vlhs
                           forcing-logic.formula-atblp-of-logic.vrhs
                           forcing-logic.term-atblp-of-logic.=lhs
                           forcing-logic.term-atblp-of-logic.=rhs))
          :expand (logic.formula-atblp x atbl))))



(defund logic.slow-formula-list-arities (x)
  (declare (xargs :guard (logic.formula-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (logic.slow-formula-list-arities (cdr x))
           (logic.slow-formula-arities (car x)))
    nil))

(defund logic.formula-list-arities (x acc)
  (declare (xargs :guard (and (logic.formula-listp x)
                              (true-listp acc))))
  (if (consp x)
      (logic.formula-list-arities (cdr x)
                                  (logic.formula-arities (car x) acc))
    acc))

(defthm true-listp-of-logic.formula-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (logic.formula-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-list-arities))))

(defthm logic.formula-list-arities-removal
  (implies (force (true-listp acc))
           (equal (logic.formula-list-arities x acc)
                  (app (logic.slow-formula-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable logic.formula-list-arities
                                    logic.slow-formula-list-arities))))

(defthm logic.slow-formula-list-arities-correct
  (implies (force (logic.formula-listp x))
           (equal (logic.arities-okp (logic.slow-formula-list-arities x) atbl)
                  (logic.formula-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((logic.formula-list-atblp x atbl)
                   (logic.slow-formula-list-arities x)))))

