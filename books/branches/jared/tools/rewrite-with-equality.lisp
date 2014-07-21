; Massive Substitution via an Equality Hypothesis
; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore (original date April, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "rewrite-with-equality")

; This file contains a clause-processor that can be used to cause the following
; behavior:

; When a clause is stable under simplification and contains an equality
; hypothesis of the form (equal bad good), for two terms bad and good such that
; good is preferred over bad according to the :preferences entry in the
; rewrite-with-equality table, then it replaces all occurrences of bad by good
; (thus deleting the equality).

; Before using this clause-processor you must set the value of the :preferences
; key in the rewrite-with-equality table.  This table informs the clause
; processor as to which terms are preferred over others.  The :preferences list
; is a list of doublets, as in (((sem-0 sem-6 sem-16) (wr)) ...), meaning that
; any term starting with sem-0, sem-6 or sem-16 is ``worse than'' any term
; starting with wr.  Then you attach a computed hint to the theorem in
; question.

; Example:
; (table rewrite-with-equality
;        :preferences                 ; (...(bad-fns good-fns)...)
;        '(((x1::sem-6) (x1::wr))))   ; sem-6 is bad, wr is good

; (defthm <main>
;   <formula>
;   :hints ((rewrite-with-equality-when-stable id clause world
;                                              stable-under-simplificationp)))

; The hint fires on all clauses that are stable under simplification.  It looks
; for an equality hypothesis equating a good term with a bad term and replaces
; the bad term everywhere with the good one, deleting the hypothesis.

; There is a trivial example at the end of this book.

(in-package "ACL2")

(table rewrite-with-equality :preferences nil)

; The value of the :preferences key of the rewrite-with-equality table should
; be a list of doublets, (bad-fn-symbs good-fn-symbs), where each component of
; each doublet is a list of symbols.  Let's say we ``prefer'' a good term over
; a bad term if there is a doublet in :preferences such that the top-level
; function symbol of the good term is a member of the good-fn-symbs of the
; doublet and the top-level function symbol of the bad term is a member of the
; bad-fn-symbs of the doublet.

; We might wish to impose an invariant on the doublets in the table and do
; guard verification but we have not done so.

(defun preferred-terms-for-rewrite-with-equalp (preferences fn gn)

; We determine whether gn is preferred over fn, i.e., whether fn is a bad
; symbol in the same sense that gn is a good one.

  (cond
   ((endp preferences) nil)
   ((and (member-eq fn (car (car preferences)))
         (member-eq gn (cadr (car preferences))))
    t)
   (t (preferred-terms-for-rewrite-with-equalp (cdr preferences) fn gn))))

(defun triggering-lit-for-rewrite-with-equalp (preferences lit)

; We recognize literals of the form (not (equal bad good)) -- or the commuted
; version -- where the top-level function symbol of good is preferred over that
; of bad according to the preferences.  If we recognize lit, we return (mv lit
; bad good); otherwise we return (mv nil nil nil).

  (case-match lit
    (('NOT ('EQUAL (fn . &) (gn . &)))
     (cond
      ((preferred-terms-for-rewrite-with-equalp preferences fn gn)
       (mv lit
           (fargn (fargn lit 1) 1)
           (fargn (fargn lit 1) 2)))
      ((preferred-terms-for-rewrite-with-equalp preferences gn fn)
       (mv lit
           (fargn (fargn lit 1) 2)
           (fargn (fargn lit 1) 1)))
      (t (mv nil nil nil))))
    (& (mv nil nil nil))))

(defun find-triggering-lit-for-rewrite-with-equalp (preferences cl)

; If cl contains an equality hypothesis, lit, in which one side, good, is
; preferred over the other, bad, we return (mv lit bad good); else we return
; (mv nil nil nil).  Here, lit is the first such literal and is always either
; (NOT (EQUAL good bad)) or (NOT (EQUAL bad good)).

  (cond
   ((endp cl) (mv nil nil nil))
   (t (mv-let
       (lit lhs rhs)
       (triggering-lit-for-rewrite-with-equalp preferences (car cl))
       (cond
        (lit (mv lit lhs rhs))
        (t (find-triggering-lit-for-rewrite-with-equalp preferences (cdr cl))))))))

(defun my-subst-expr1 (flg new old x)
  (declare (xargs :measure (acl2-count x)))
  (if flg
      (cond ((equal x old) new)
            ((variablep x) x)
            ((fquotep x) x)
            (t (cons (ffn-symb x)
                     (my-subst-expr1 nil new old (fargs x)))))
      (cond ((endp x) nil)
            (t (cons (my-subst-expr1 t new old (car x))
                     (my-subst-expr1 nil new old (cdr x)))))))

; I would prefer to write (rewrite-clause-with-equal preferences cl) but as a clause
; processor the function must take the arguments in the order given below.

; Simplification: Rather than delete the equality, we just leave it in place
; but hit it, so that it becomes (not (equal good good)) and drops out on its
; own.

(defun rewrite-clause-with-equal (cl preferences)

; Here, hints must be of the form (lhs-fns rhs-fns), where the two components
; are lists of function symbols.  Search cl for an equality hypothesis, lit =
; (NOT (EQUAL a b)), such that one side (a or b) has as its top function symbol
; a symbol in lhs-fns and the other has as its top function symbol a symbol in
; rhs-fns.  Call term (a or b) with the lhs-fns symbol lhs and the other term
; rhs.  Replace lhs by rhs throughout cl and delete lit.  Return the singleton
; set of clauses containing the rewritten cl.  If no such lit is found, return
; the singleton set containing cl itself as a sign of inaction.

  (mv-let (lit bad good)
          (find-triggering-lit-for-rewrite-with-equalp preferences cl)
          (cond
           (lit
            (prog2$
             (cw "~%~%HIT!  Replaced ~x0 by ~x1.~%~%"
                 bad good)
             (list (my-subst-expr1 nil good bad cl))))
           (t (list cl)))))

; Example call:
#||
(rewrite-clause-with-equal
 '((not (hyp1 s n))
   (not (hyp2 (sem s n)))
   (not (equal (fn2 s n) (wr key val s)))
   (not (equal (wr key! val! s) (sem s n)))  ; triggering hyp -- note swap
   (conclp (foo (sem s n)) (bar (mum (sem s n)))))
 '(((sem) (wr))))                            ; ((bad-fns good-fns))
==>
(((NOT (HYP1 S N))                  ; list of clauses to prove
  (NOT (HYP2 (WR KEY! VAL! S)))
  (NOT (EQUAL (FN2 S N) (WR KEY VAL S)))
  (CONCLP (FOO (WR KEY! VAL! S))
          (BAR (MUM (WR KEY! VAL! S))))))
||#

; We should perhaps change the names of these evaluators to be less common
; ones.

(defevaluator eqev eqev-lst ((not x) (equal x y) (if x y z)))

(defthm my-subst-expr1-correct
  (and
   (implies (and (pseudo-termp term)
                 flg
                 (equal (eqev new alist)
                        (eqev old alist)))
            (equal (eqev (my-subst-expr1 flg new old term) alist)
                   (eqev term alist)))
   (implies (and (pseudo-term-listp term)
                 (not flg)
                 (equal (eqev new alist)
                        (eqev old alist)))
            (equal (eqev-lst (my-subst-expr1 flg new old term) alist)
                   (eqev-lst term alist))))
  :hints (("Goal" :induct (my-subst-expr1 flg new old term)
           :in-theory (enable EQEV-CONSTRAINT-0))))

(defthm correctness-of-rewrite-clause-with-equal-gen
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (equal (eqev good a)
                       (eqev bad a))
                (eqev (disjoin (my-subst-expr1 nil good bad cl))
                      a))
           (eqev (disjoin cl) a))
  :rule-classes nil)

(defthm find-triggering-lit-for-rewrite-with-equalp-finds-member
  (implies (and (pseudo-term-listp cl)
                (car (find-triggering-lit-for-rewrite-with-equalp hints cl)))
           (member-equal (car (find-triggering-lit-for-rewrite-with-equalp hints cl)) cl)))

(defthm member-of-false-clause-is-false
  (implies (and (pseudo-term-listp cl)
                (not (eqev (disjoin cl) a))
                (member-equal lit cl))
           (not (eqev lit a)))
  :rule-classes nil)

; Therefore, the two terms found by find-triggering-lit-for-rewrite-with-equalp
; are equivalent:

(defthm terms-found-by-find-triggering-lit-for-rewrite-with-equalp-are-equal
  (implies (and (pseudo-term-listp cl)
                (car (find-triggering-lit-for-rewrite-with-equalp hints cl))
                (not (eqev (disjoin cl) a)))
           (equal (eqev (mv-nth 1 (find-triggering-lit-for-rewrite-with-equalp hints cl)) a)
                  (eqev (mv-nth 2 (find-triggering-lit-for-rewrite-with-equalp hints cl)) a)))
  :hints (("Goal" :use (:instance member-of-false-clause-is-false
                                  (cl cl)
                                  (a a)
                                  (lit (car (find-triggering-lit-for-rewrite-with-equalp hints cl))))))
  :rule-classes nil)

(defthm correctness-of-rewrite-clause-with-equal
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (eqev (conjoin-clauses
                       (rewrite-clause-with-equal cl hints))
                      a))
           (eqev (disjoin cl) a))
  :hints (("Goal" :do-not-induct t
           :use ((:instance terms-found-by-find-triggering-lit-for-rewrite-with-equalp-are-equal)
                 (:instance correctness-of-rewrite-clause-with-equal-gen
                            (cl cl)
                            (a a)
                            (good (mv-nth 2 (find-triggering-lit-for-rewrite-with-equalp hints cl)))
                            (bad (mv-nth 1 (find-triggering-lit-for-rewrite-with-equalp hints cl)))))))
  :rule-classes :clause-processor)

; The following computed hint implements the replacement of bad terms by
; preferred good terms in clauses that are stable under simplification and
; which contain an explicit equality equating the good and bad terms.

(defun rewrite-with-equality-when-stable (id clause world stable-under-simplificationp)
  (declare (ignore id))
  (cond
   ((and stable-under-simplificationp
         (mv-let (lit bad good)
                 (find-triggering-lit-for-rewrite-with-equalp
                  (cdr (assoc-eq :preferences
                                 (table-alist 'rewrite-with-equality
                                              world)))
                  clause)
                 (declare (ignore bad good))
                 lit))
    `(:computed-hint-replacement t
                                 :clause-processor
                                 (rewrite-clause-with-equal
                                  clause
                                  ',(cdr (assoc-eq :preferences
                                                   (table-alist 'rewrite-with-equality
                                                                world))))))
   (t nil)))

#||
; =================================================================
; Here is an example.  The thm below will fail after reducing the goal
; to
; (IMPLIES (AND (HYP1 U V (GOOD1 U))
;               (HYP2 U V (GOOD2 V W)))
;          (CONCL (GOOD1 U) (GOOD2 V W)))

(defstub bad1 (a) t)
(defstub bad2 (b c) t)
(defstub good1 (u) t)
(defstub good2 (v w) t)

(defstub hyp1 (u v x) t)
(defstub hyp2 (u v x) t)
(defstub concl (x y) t)

(include-book
 "rewrite-with-equality")

(table rewrite-with-equality
       :preferences
       '(((bad1 bad2) (good1 good2))))

(thm (implies (and (hyp1 u v (bad1 a))
                   (equal (bad1 a) (good1 u))       ; orientation of equal hyps
                   (equal (good2 v w) (bad2 b c))   ; irrelevant
                   (hyp2 u v (bad2 b c)))
              (concl (bad1 a)
                     (bad2 b c)))
     :hints ((rewrite-with-equality-when-stable id clause world
                                                stable-under-simplificationp)))
||#

