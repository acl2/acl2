(in-package "ACL2")

(set-state-ok t)

;When we're rewriting a term, it may be one of the top-level literals in the goal, may be a subterm of a top-level
;literal, or may not even appear in the goal at all (because it arose during backchaining). This function tests
;whether the term is a top-level literal in the goal which has the "parity" of a hypothesis (or a negated
;conclusion, I guess).  Recall that a clause is the disjunction of the conclusion with the negations of all the
;hyps.  So a hypothesis H appears in the clause as (not H).
(defun hypothesis-parity (term mfc state)
  (declare (ignore state) (type t term mfc state) (xargs :guard-hints (("Goal" :in-theory (enable mfc-clause)))))
  (member-equal (list 'not term) (mfc-clause mfc)))

;This function tests whether the term is a top-level literal in the goal which has the "parity" of the conclusion
;(or a negated hypothesis, I guess).  Recall that a clause is the disjunction of the conclusion with the negations
;of all the hyps.  So a hypothesis H appears in the clause as just H.
(defun conclusion-parity (term mfc state)
  (declare (ignore state) (type t term mfc state) (xargs :guard-hints (("Goal" :in-theory (enable mfc-clause)))))
  (member-equal term (mfc-clause mfc)))

(defevaluator cons-ev cons-ev-list
  ((equal x y)
   (cons a b)
   (if test x y)))

;BOZO verify gaurds?
;returns a list of equalities equivalent to the claim (equal CONS-NEST1 CONS-NEST2)
;perhaps don't include equalities that are trivially true?
(defun cons-equal-meta-function-helper (cons-nest1 cons-nest2)
  (declare (type t cons-nest1 cons-nest2))
  (if (and (consp cons-nest1)
           (consp (cdr cons-nest1))
           (consp (cddr cons-nest1))
           (equal (car cons-nest1) 'cons)
           (consp cons-nest2)
           (consp (cdr cons-nest2))
           (consp (cddr cons-nest2))
           (equal (car cons-nest2) 'cons))
      (if (equal (cadr cons-nest1) (cadr cons-nest2))
          (cons-equal-meta-function-helper (caddr cons-nest1) (caddr cons-nest2)) ;skip syntactically equal stuff
        (list
         'if
         (list 'equal (cadr cons-nest1) (cadr cons-nest2))
         (cons-equal-meta-function-helper (caddr cons-nest1) (caddr cons-nest2))
         ''nil
         ))
    ;bozo if syntactically equal, take advantage of that fact
;    (if (equal cons-nest1 cons-nest2)
 ;       ''t
      (list 'equal cons-nest1 cons-nest2) ;at least one of them is not a cons
      ))


(defthm cons-equal-smart-meta-helper
  (equal (cons-ev (cons-equal-meta-function-helper nest1 nest2) a)
         (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defun cons-equal-meta-function (term mfc state)
  (declare (type t  mfc state) (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
          ; (consp (cdr term)) ;how was I able to comment this out?
           (consp (cadr term))  ;(cadr term) should be of the form (cons blah blah2)
           (equal (car (cadr term)) 'cons)
           (consp (cddr term))
           (consp (caddr term))
           (equal (car (caddr term)) 'cons)  ;(caddr term) should be of the form (cons blah3 blah4)

           (equal (car term) 'equal)

;           (consp (cdr (cadr term))) ;check the arities:
 ;          (consp (cddr (cadr term)))
  ;         (consp (cdr (caddr term)))
   ;        (consp (cddr (caddr term)))
           (not (conclusion-parity term mfc state))
           )
      (cons-equal-meta-function-helper (cadr term) (caddr term))
    term))

(in-theory (disable HYPothesis-PARITY MFC-CLAUSE))

(defthmd cons-equal-smart-meta
  (equal (cons-ev term a)
         (cons-ev (cons-equal-meta-function term mfc state) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))

#|
(defmacro V0 (x) `(mv-nth 0 ,x))
(defmacro V1 (x) `(mv-nth 1 ,x))
(defmacro V2 (x) `(mv-nth 2 ,x))

(defmacro met (binding &rest rst)
  (let ((bvar (car binding)))
    (let ((fn (cadr binding)))
      `(mv-let ,bvar ,fn ,@rst))))


;bozo this one should fire first?
;this one takes two cons nests which are claimed to be equal and removes corresponding items which are syntactically equal, yielding a two possibly-smaller cons nests
;for efficiency, before creating the new nests (which might be the same as the old ones), we check whether we will make any changes and save the creation of the cons cells if we don't
;or pass a flag indicating whether we've changed anything?
(defun cons-equal-meta-function-helper2 (cons-nest1 cons-nest2)
  (declare (type t cons-nest1 cons-nest2))
  (if (and (consp cons-nest1)
           (consp (cdr cons-nest1))
           (consp (cddr cons-nest1))
           (equal (car cons-nest1) 'cons)
           (consp cons-nest2)
           (consp (cdr cons-nest2))
           (consp (cddr cons-nest2))
           (equal (car cons-nest2) 'cons))
      (if (equal (cadr cons-nest1) (cadr cons-nest2))
          (cons-equal-meta-function-helper2 (caddr cons-nest1) (caddr cons-nest2)) ;skip syntactically equal stuff
        (met ((result1 result2) (cons-equal-meta-function-helper2 (caddr cons-nest1) (caddr cons-nest2)))
             (mv (list 'cons (cadr cons-nest1) result1)
                 (list 'cons (cadr cons-nest2) result2))))
    (mv cons-nest1 cons-nest2) ;at least one of them is not a cons
    ))

;things that might be slow
;checking every time we rewrite and equal that the rule should fire.
;consing up the new term even in the case where nothing changes..
;checking whether a change was made when we just return term.

(defun cons-equal-meta-function2 (term)
  (declare (type t term))
  (if (and (consp term)
           (consp (cdr term))
           (consp (cadr term))  ;(cadr term) should be of the form (cons blah blah2)
           (equal (car (cadr term)) 'cons)
           (consp (cddr term))
           (consp (caddr term))
           (equal (car (caddr term)) 'cons)  ;(caddr term) should be of the form (cons blah3 blah4)

           (equal (car term) 'equal)

;           (consp (cdr (cadr term))) ;check the arities:
 ;          (consp (cddr (cadr term)))
  ;         (consp (cdr (caddr term)))
   ;        (consp (cddr (caddr term)))
;           (hypothesis-parity term mfc state)  ;TERM appears as a hypothesis (or a negated conclusion)
           )
      (met ((result1 result2) (cons-equal-meta-function-helper2 (cadr term) (caddr term)))
           (list 'equal result1 result2))
    term))

(defthm cons-equal-smart-meta2-helper-one
  (implies (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                  (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a))
           (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-smart-meta2-helper-two
  (implies (cons-ev (list 'equal nest1 nest2) a)
           (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                  (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a)))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-smart-meta2-helper-three
  (equal (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a))
         (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable mv-nth))

(defthmd cons-equal-smart-meta2
  (equal (cons-ev term a)
         (cons-ev (cons-equal-meta-function2 term) a))
  :hints (("Goal" :in-theory (enable cons-equal)
           :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))

|#

#|

(in-theory (disable cons-equal))

(thm (implies (equal (cons x1 y1) (cons x2 y2))
              (equal x1 x2))
     :hints (("Goal" :in-theory (disable car-cons))))

(thm (implies blah
              (equal (cons x1 y1) (cons x2 y2)))
     :hints (("Goal" :in-theory (disable car-cons))))

|#

#|
new plan (Doug's idea):
 rewrite (equal (cons a b) (cons c d)) to (cons-equal-dummy a b c d) when we're rewriting a hyp with a normal rule.
 then rewrite (with a meta rule) (cons-equal-dummy a b c d) to a conjunction of equalities between corresponding pieces.
  will this second rewrite happen immediately?

how do we handle backchaining?
|#

#|
(defund cons-equal-dummy (a b c d)
  (equal (cons a b) (cons c d)))

(defthmd cons-equal-introduce-dummy
  (implies (syntaxp (hypothesis-parity (list 'equal (list 'cons a b) (list 'cons c d)) mfc state))
           (equal (equal (cons a b) (cons c d))
                  (cons-equal-dummy a b c d)))
  :hints (("Goal" :in-theory (enable cons-equal-dummy))))

(defun cons-equal-dummy-meta-function (term)
  (declare (type t term))
  (if (and; (hypothesis-parity term mfc state) ;TERM appears as a hypothesis (or a negated conclusion)
           (consp term)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (consp (cddddr term))
           (equal (car term) 'cons-equal-dummy)
           )
      (cons-equal-meta-function-helper (list 'cons (cadr term) (caddr term))
                                       (list 'cons (cadddr term) (car (cddddr term)))
                                       )
    term))

(defevaluator cons-ev2 cons-ev2-list
  (
   (equal x y)
   (cons a b)
   (cons-equal-dummy a b c d)
   (if test x y)
   ))

(defthm cons-equal-smart-meta-helper-2
  (equal (cons-ev2 (cons-equal-meta-function-helper nest1 nest2) a)
         (cons-ev2 (list 'equal nest1 nest2) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-dummy-meta
  (equal (cons-ev2 term a)
         (cons-ev2 (cons-equal-dummy-meta-function term) a))
  :hints (("Goal" :in-theory (enable cons-equal CONS-EQUAL-DUMMY)
           :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (cons-equal-dummy))))

(defthmd cons-equal-introduce-dummy-into-non-conclusion
  (implies (syntaxp (not (conclusion-parity (list 'equal (list 'cons a b) (list 'cons c d)) mfc state)))
           (equal (equal (cons a b) (cons c d))
                  (cons-equal-dummy a b c d)))
  :hints (("Goal" :in-theory (enable cons-equal-dummy))))

(in-theory (enable cons-equal-introduce-dummy-into-non-conclusion))
(in-theory (disable cons-equal)) ;we'll use our rule instead.
|#
;don't forget about the built-in axiom CONS-EQUAL

#|
(defthmd equal-cons-cases ;trying disabled...
  (implies (consp x)
           (equal (equal (cons y z) x)
                  (and (equal y (car x))
                       (equal z (cdr x))))))

;yuck!
;do i need both equal-cons-cases-2 and equal-true-list-cases?
(defthm equal-cons-cases-2
  (equal (equal x (cons y z))
         (and (consp x)
              (equal (car x) y)
              (equal (cdr x) z))))
|#

(defthmd cons-equal-rewrite ;trying disabled..
  (equal (equal (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (equal x (cdr y)))))

(defthm cons-onto-cdr-equals-all-rewrite
  (equal (equal (cons a (cdr x))
                x)
         (and (consp x)
              (equal a (car x)))))

(defthm list-car-equal-all-rewrite
  (equal (equal (list (car x)) x)
         (and (consp x)
              (equal nil (cdr x))))
  :hints (("Goal" :in-theory (enable cons-equal-rewrite))))

(defthm cons-equal-cons-same-rewrite-one
  (equal (equal (cons a x) (cons a y))
         (equal x y)))

(defthm cons-equal-cons-same-rewrite-two
  (equal (equal (cons a x) (cons b x))
         (equal a b)))


(in-theory (disable cons-equal))
(in-theory (enable cons-equal-smart-meta))

