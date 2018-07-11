; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains some basic tests of various hint mechanisms.

; Note that because of must-fail, REBUILD doesn't work for this book.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test override-hints.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rev (x)
  (if (atom x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defun my-tester1 (id state)
  (declare (xargs :stobjs state))
; Note that (parse-clause-id "Subgoal *1/3'5'") = ((0 1) (3) . 5).
  (value (and (equal id '((0 1) (3) . 5))
              (list :error
                    (msg "QUITTING.")))))

(add-default-hints '((my-tester1 id state)))

(must-fail
; Error after Subgoal *1/3'5', upon attempt to generalize.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))))

(must-succeed
; Succeeds because explicit hint takes priority over default hint.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'5'" :expand ((nth u v))))))

(add-override-hints '((append '(:no-thanks t) keyword-alist)))

(must-succeed
; Explicit hint fires just fine with override hint, but this time
; we do not see "Thanks".
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'5'" :expand ((nth u v))))))

(set-override-hints
; Basically the same as above, except that we will see a message printed for
; every attempt to select a hint.
 '((mv-let (col state)
           (fmx "**Applying override hints**")
           (declare (ignore col))
           (value (append '(:no-thanks t) keyword-alist)))))

(must-succeed
; As above, explicit hint fires just fine with override hint.
; But now we see a message printed for every attempt to select a hint.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'5'" :expand ((nth u v))))))

(must-fail
; Error after Subgoal *1/3'5'. still.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))))

(set-override-hints '((remove-keyword :error keyword-alist)))

(must-fail
; Still fails, because we't check for :error in computed hint results at every
; stage, not just at the end of applying override-hints.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))))

(set-override-hints nil)

(set-default-hints nil)

(must-fail
; Fails, of course.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/2" :in-theory (disable rev))
              ("Subgoal *1/1" :in-theory (disable rev))
              ("Subgoal *1/1'" :in-theory (disable true-listp rev (rev))))))

(set-override-hints '((remove-keyword :in-theory keyword-alist)))

(must-succeed
; Now, succeeds because of override-hints above.  Notice that we get no
; "Thanks", because there are no hint-settings left after removing the
; :in-theory hint-settings.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/2" :in-theory (disable rev))
              ("Subgoal *1/1" :in-theory (disable rev))
              ("Subgoal *1/1'" :in-theory (disable true-listp rev (rev))))))

(must-succeed
; Also succeeds because of override-hints above.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Goal" :in-theory (disable rev)))))

(must-fail
; Fails because computed hint fires, since "Goal" hint is not selected (because
; it becomes the empty hint).
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Goal" :in-theory (disable rev))
              (quote (:hands-off rev)))))

; Now, arrange that we never eliminate a hint entirely:
(set-override-hints '((let ((temp (remove-keyword :in-theory keyword-alist)))
                        (or temp
                            (and keyword-alist
                                 '(:no-op t))))))

(must-fail
; Fails even though "Goal" hint is replaced by ("Goal" (:no-op t)), which is
; selected, because preprocess-clause hits (but puts a hidden-clause note in
; the history, and nothing is printed) and hence the computed hint is applied
; to "Goal" on the second try; try (trace$ waterfall-step) to see that a HIT
; signal is returned by preprocess-clause.  Actually a HIT signal is then also
; returned for "Goal" on settled-down-clause.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Goal" :in-theory (disable rev))
              (and (equal id *initial-clause-id*)
                   (quote (:hands-off rev))))))

(must-succeed
; As just above, but we avoid the issue with "Goal" making extra trips through
; the waterfall.  Thus, succeeds because "Subgoal *1/3'" hint is replaced by
; ("Subgoal *1/3'" (:no-op t)), which is selected.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'" :in-theory (disable rev))
              (and (equal id (parse-clause-id "Subgoal *1/3'"))
                   (quote (:hands-off rev))))))

; Just to make sure that :in-theory and :hands-off would both have caused
; failures above:

(remove-override-hints '((let ((temp (remove-keyword :in-theory keyword-alist)))
                           (or temp
                               (and keyword-alist
                                    '(:no-op t))))))
(assert-event (null (override-hints (w state))))
(must-fail
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'" :in-theory (disable rev)))))
(must-fail
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints ((and (equal id (parse-clause-id "Subgoal *1/3'"))
                   (quote (:hands-off rev))))))

; Now we implement the feature requested by Peter Dillinger, where we can limit
; induction levels without printing "Thanks" for the hint when that is all we
; are doing.  First, we do this without worrying about "Thanks".

(set-override-hints '((if (and (>= (length (cdar id)) 2)
; Avoid bothering with children of top-level induction goals:
                               (null (cdr (access clause-id id :case-lst)))
                               (zerop (access clause-id id :primes)))
                          (list* :do-not-induct :otf keyword-alist)
                        keyword-alist)))

(must-fail
; We should see:
#||
  So we now return to *1.1.2, which is

  (IMPLIES (AND (NOT (CONSP L2))
                (EQUAL (APPEND BAD X2) (APPEND X2 BAD)))
           (EQUAL (LIST* L1 X1 X2)
                  (APPEND X2 (LIST* X1 L1 L2)))).

  Normally we would attempt to prove *1.1.2 by induction.  However, a
  :DO-NOT-INDUCT hint was supplied to abort the proof attempt.
||#
 (thm (equal (append (append x x) x)
             (append x x x))))

; As above, but no "Thanks" for the hints this time:
(set-override-hints '((if (and (>= (length (cdar id)) 2)
; Avoid bothering with children of top-level induction goals:
                               (null (cdr (access clause-id id :case-lst)))
                               (zerop (access clause-id id :primes)))
                          (list* :do-not-induct :otf
                                 (or keyword-alist
                                     '(:no-thanks t)))
                        keyword-alist)))
(must-fail
; Should see the same :DO-NOT-INDUCT failure message as above, but this time we
; should not see any "Thanks" messages for hints.
 (thm (equal (append (append x x) x)
             (append x x x))))

(must-fail
; As above, but we should see a "Thanks" message for (only) the indicated
; goal.
 (thm (equal (append (append x x) x)
             (append x x x))
      :hints (("Subgoal *1.1/2" :in-theory (enable car-cons)))))

; Now we test that add-override-hints does indeed add to the end.  First, we
; add to the beginning and see that we get the "Thanks" as just above, because
; the new override-hint is added before we see whether to add :no-thanks.

(encapsulate
 ()

 (add-override-hints '((if (equal (parse-clause-id "Subgoal *1.1/2")
                                  id)
                           (list* :in-theory '(enable car-cons) keyword-alist)
                         keyword-alist))
                     :at-end nil)

 (must-fail
; As above, with a "Thanks" message for "Subgoal *1.1/2".
  (thm (equal (append (append x x) x)
              (append x x x)))))

; Same as above, using no explicit :at-end but checking that default is nil.

(encapsulate
 ()

 (add-override-hints '((if (equal (parse-clause-id "Subgoal *1.1/2")
                                  id)
                           (list* :in-theory '(enable car-cons) keyword-alist)
                         keyword-alist)))

 (must-fail
; As above, with a "Thanks" message for"Subgoal *1.1/2".
  (thm (equal (append (append x x) x)
              (append x x x)))))

; Let's check that the add-override-hints was local to the above encapsulates.

(assert-event (equal (length (override-hints (w state))) 1))

; Now we add the new override-hint to the end, by which time we have already
; added the :no-thanks hint -- so we should see no "Thanks".

(encapsulate
 ()

 (add-override-hints '((if (equal (parse-clause-id "Subgoal *1.1/2")
                                  id)
                           (list* :in-theory '(enable car-cons) keyword-alist)
                         keyword-alist))
                     :at-end t)

 (must-fail
; As above, with no "Thanks" message for"Subgoal *1.1/2".
  (thm (equal (append (append x x) x)
              (append x x x)))))

; Same as above, but add-override-hints! is non-local.

(encapsulate
 ()

 (add-override-hints! '((if (equal (parse-clause-id "Subgoal *1.1/2")
                                   id)
                            (list* :in-theory '(enable car-cons) keyword-alist)
                          keyword-alist))
                     :at-end t)

 (must-fail
; As above, with no "Thanks" message for"Subgoal *1.1/2".
  (thm (equal (append (append x x) x)
              (append x x x)))))

; Let's check that the add-override-hints! was NOT local to the above
; encapsulates.

(assert-event (equal (length (override-hints (w state))) 2))

(set-default-hints nil)
(set-override-hints nil)

; The following does not produce a "Thanks" message, because we treat computed
; hints as nil when they produce only the :computed-hints-replacement keyword,
; even after applying override hints.  See the discussion of
; :computed-hint-replacement in :doc override-hints.
(encapsulate
 ()
 (add-override-hints '((remove-keyword :expand keyword-alist)))
 (must-succeed
  (thm (equal x x)
       :hints
       ((quote (:computed-hint-replacement t :expand ((nth u v))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test :backtrack hints.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parts of the following basic example correspond to the slides presentated at
; ACL2 Workshop 2011 for the paper "Integrating Testing and Interactive Theorem
; Proving" by Harsh Raju Chamarthi, Peter C. Dillinger, Matt Kaufmann, and
; Panagiotis Manolios.

; This basic example works equally well with default-hints and override-hints.
; The advantage in general of override-hints is that they fire even if the user
; has supplied an explicit hint.  The last part below shows a failure of
; default-hints, to illustrate why override-hints are preferable.

;;;;; basic definitions ;;;;;

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev0 (x) ; called rev0 to avoid name clash with earlier rev
  (if (consp x)
      (app (rev0 (cdr x)) (cons (car x) nil))
    nil))

(defthm app-assoc
  (equal (app (app x y) z)
         (app x (app y z))))

; Fails (bad generalization produces non-theorem, Subgoal *1/2''):
(must-fail
 (thm
  (equal (rev0 (app a b))
         (app (rev0 b) (rev0 a)))))

(defun test-clause (cl state)
  (declare (xargs :stobjs state :mode :program))
  (pprogn
   (fms "Test-clause:~|~x0~|"
        (list (cons #\0 cl))
        *standard-co* state nil)
   (er-let* ((term/val
              (simple-translate-and-eval
               (conjoin cl)
               (cons (cons 'rv 3) (pairlis$ (all-vars1-lst cl nil) nil))
               nil "" 'test-clause (w state) state t)))
            (value (not (cdr term/val))))))

;;;;; using override-hint ;;;;;

(defun test-gen-checkpoint (keyword-alist)
  `(:backtrack
    (cond
     ((eq processor 'generalize-clause)
      (er-let*
       ((res (test-clause (car clause-list) state)))
       (value (cond (res '(:do-not '(generalize)))
                    (t nil)))))
     (t (value nil)))
    ,@keyword-alist))

(add-override-hints
 '((test-gen-checkpoint keyword-alist)))

; Succeeds:
(must-succeed
 (thm
  (equal (rev0 (app a b))
         (app (rev0 b) (rev0 a)))))

(remove-override-hints
 '((test-gen-checkpoint keyword-alist)))

; Fails again (override-hint was removed)
(must-fail
 (thm
  (equal (rev0 (app a b))
         (app (rev0 b) (rev0 a)))))

(defun test-gen-checkpoint2 ()
  `(:backtrack
    (cond
     ((eq processor 'generalize-clause)
      (er-let*
       ((res (test-clause (car clause-list) state)))
       (value (cond (res '(:do-not '(generalize)))
                    (t nil)))))
     (t (value nil)))))

(add-default-hints
 '((test-gen-checkpoint2)))

; Succeeds:
(must-succeed
 (thm
  (equal (rev0 (app a b))
         (app (rev0 b) (rev0 a)))
  :hints (("Subgoal *1/2'" :in-theory (enable nth)))))

; The rest of this is to show the advantage of override-hints over
; default-hints.  (Technical point: It takes a bit of effort to defeat
; default-hints, because settled-down-clause hits and pops us up to the top of
; the waterfall for a second try.  So we actually need two hints in front of
; test-gen-checkpoint2 in order to keep it from firing.)

(defun silly-expand-hint ()
  `(:computed-hint-replacement t :expand ((nth u v))))

(add-default-hints
 '((silly-expand-hint)))

; Fails, because default-hint doesn't apply
(must-fail
 (thm
  (equal (rev0 (app a b))
         (app (rev0 b) (rev0 a)))
  :hints (("Subgoal *1/2'" :expand ((nth y z))))))

; End of basic example of the use of :backtrack hints.

(defconst *backtrack-failure*
  '(:backtrack
    (and (eq processor 'generalize-clause)
         (list :error
               (msg "ACL2 tried to generalize on a clause with function ~
                     symbols ~&0.  We are aborting with a :BACKTRACK hint."
                    (all-fnnames-lst clause))))))

(defun my-tester2 (state)
  (declare (xargs :stobjs state))
  (value *backtrack-failure*))

(set-default-hints '((my-tester2 state)))

(must-fail
; Error after Subgoal *1/3'5', upon attempt to generalize.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))))

(must-fail
; Fails as above even though explicit hints take priority over default hints,
; because the default :backtrack hint is incorporated into the running
; :hint-settings at "Goal".  The :backtrack computed hint is evaluated at every
; goal -- try (trace$ process-backtrack-hint) -- but returns (value nil) until
; it returns an error when we hit on generalization, when evaluation produces
; an :error hint.  Of course, this time we get a "Thanks" for the indicated
; subgoal.
 (thm (implies (true-listp x)
               (equal (rev (rev x)) x))
      :hints (("Subgoal *1/3'5'" :expand ((nth u v))))))

(encapsulate
 ()

; The following is a mistake, because PROCESSOR is not legal in ordinary
; computed hints, but only in :backtrack hints.
 (set-default-hints '((and (eq processor 'generalize-clause)
                           '(:in-theory (disable append)))))

 (must-fail
; The translation error message should say that PROCESSOR is only legal for
; :backtrack hints.
  (thm (equal (append (append x y) z)
              (append x y z))))
 )

; The following is just as above, but the error message should say that
; PROCESSOR, CLAUSE-LIST, and KEYWORD-ALIST are only legal for :backtrack hint
; or override-hints.
(encapsulate
 ()
 (set-default-hints '((and (eq processor 'generalize-clause)
                           (null clause-list)
                           keyword-alist
                           '(:in-theory (disable append)))))
 (must-fail
  (thm (equal (append (append x y) z)
              (append x y z)))))

; Translation error as above, but because of FOO there is no bother of
; mentioning :backtrack hints or override-hints.
(encapsulate
 ()
 (set-default-hints '((and (eq processor 'generalize-clause)
                           (null clause-list)
                           keyword-alist
                           foo
                           '(:in-theory (disable append)))))
 (must-fail
  (thm (equal (append (append x y) z)
              (append x y z)))))

; More interesting example suggesting an approach for testing:

(defun test-clause-list (processor clause-list state)
; Return (value t) if we find a counterexample, else (value nil).
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((term (conjoin-clauses clause-list))
         (vars (all-vars term)))
    (er-let* ((pair
               (simple-translate-and-eval term
                                          (pairlis$ vars nil)
                                          nil
                                          "The clause with values bound to nil"
                                          'my-tester
                                          (w state)
                                          state
                                          nil)))
             (cond ((cdr pair) (value nil))
                   (t (assert$
                       (null (cdr clause-list))
                       (pprogn
                        (io? prove nil state
                             (processor clause-list)
                             (fms "The attempt at ~x0 produced the ~
                                   clause~|~%~x1,~|~%which is false when the ~
                                   variables are bound to nil.  So we abandon ~
                                   that step.~|"
                                  (list (cons #\0 processor)
                                        (cons #\1
                                              (prettyify-clause
                                               (car clause-list)
                                               (let*-abstractionp state)
                                               (w state))))
                                  (proofs-co state)
                                  state
                                  (term-evisc-tuple nil state)))
                        (value t))))))))

(defun my-tester3 ()
  `(:computed-hint-replacement
    t
    :backtrack
    (cond ((eq processor 'fertilize-clause)
           (er-let* ((val (test-clause-list processor clause-list state)))
                    (value (cond (val '(:do-not '(fertilize)))
                                 (t nil)))))
          (t (value nil)))))

(set-default-hints '((my-tester3)))

; For the following, after Subgoal *1.2/2'4' we get:
#||
 The attempt at FERTILIZE-CLAUSE produced the clause

 (IMPLIES (NOT (CONSP Y)) (EQUAL (APPEND X2 (CONS X1 X2)) (APPEND X2 Y))),

 which is false when the variables are bound to nil.  So we abandon
 that step.

 [Note:  A hint was supplied for our processing of the goal above, because
 of a :backtrack hint that is preventing heuristic use of equalities.
 Thanks!]

 We generalize this conjecture, replacing (APPEND X2 X2) by BAD.  This
 produces

 Subgoal *1.2/2'5'
||#
(must-fail
 (thm (equal (append x y x) (append y x y))))

; The following behaves identically to the above, still thanking us for the
; hint on "Subgoal *1.2/2'4'", because the :no-thanks hint is applied to "Goal"
; and then removed from the lst of two computed hints but stored in the
; hint-settings, and then settled-down-clause hits on "Goal", which eliminates
; the :no-thanks hint-setting.
(encapsulate
 ()
 (add-default-hints '((quote (:no-thanks t))))
 (must-fail
  (thm (equal (append x y x) (append y x y)))))

; So to make sure that :no-thanks always applies, we use
; :computed-hint-replacement.  But then we always select that hint, since
; add-default-hints adds to the front (unless :at-end is supplied).  In
; particular, the :backtrack hint no longer fires at "Subgoal *1.2/2'4'" --
; instead, fertilization is applied.  So what we really want is an
; override-hint, which follows this test.
(encapsulate
 ()
 (add-default-hints '((quote (:computed-hint-replacement t :no-thanks t))))
 (must-fail
  (thm (equal (append x y x) (append y x y)))))

; So this time the :backtrack hint fires at "Subgoal *1.2/2'4'", and thus we
; avoid fertilization there.
(encapsulate
 ()
 (add-override-hints '((cond ((or (null keyword-alist)
                                  (assoc-keyword :no-thanks keyword-alist))
                              keyword-alist)
                             (t
                              (append '(:no-thanks t) keyword-alist)))))
 (must-fail
  (thm (equal (append x y x) (append y x y)))))

(set-default-hints nil)
(set-override-hints nil)

; Silly success:
(must-succeed
 (thm (equal (car (append x y))
             (if (consp x) (car x) (car y)))
      :hints
      (("Goal"
        :backtrack
        (quote (:expand ((nth u v))))))))

; Simple success, demonstrating backtrack hint:
(encapsulate
 ()
 (local (in-theory (disable append)))
 (must-succeed
  (thm (equal (car (append x y))
              (if (consp x) (car x) (car y)))
       :hints
       (("Goal"
         :backtrack
         (quote (:in-theory (enable append))))))))

; Success, demonstrating that backtrack hint allows the use of
; :computed-hint-replacement (but :computed-hint-replacement plays no
; interesting role in this case):
(encapsulate
 ()
 (local (in-theory (disable append)))
 (must-succeed
  (thm (equal (car (append x y))
              (if (consp x) (car x) (car y)))
       :hints
       (("Goal"
         :backtrack
         (quote (:computed-hint-replacement t :in-theory (enable append))))))))

; Success, demonstrating interaction of backtrack hint with
; computed-hint-replacement:
(encapsulate
 ()
 (local (in-theory (disable append)))
 (must-succeed
  (thm (equal (car (append x y))
              (if (consp x) (car x) (car y)))
       :hints
       (("Goal"
         :backtrack
         (quote (:computed-hint-replacement
                 ((quote (:in-theory (enable append))))
                 :no-op t)))))))

; Here is a test that combines backtrack hints and override-hints.

(defun my-computed-hint (state)
  (declare (xargs :mode :program :stobjs state))
  (pprogn (fms "*** HELLO ***~%" nil *standard-co* state nil)
          (value nil)))

(add-override-hints
 '((quote (:backtrack (if (member-eq processor '(apply-top-hints-clause
                                                 preprocess-clause
                                                 simplify-clause))
                          (value nil)
                        (my-computed-hint state))))))

; If you now do (thm (equal (append (append x x) x) (append x x x))), you'll see
; the string "*** HELLO ***" printed after every simplification checkpoint.
; Note that the member-eq test above rules out those processors in
; *preprocess-clause-ledge* that do not correspond to simplification
; checkpoints.

; Also note that the above call of add-override-hints arranges for all hints to
; be ignored!  That's because the application of this override-hint selects a
; hint of the form (:backtrack <expr>) where <expr> evaluates to (mv nil nil
; state) -- so any other hint is ignored (superseded by this :backtrack hint),
; but this :backtrack hint actually has no effect on the proof.

(set-override-hints nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test :or hints and custom hints.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub property (x) t)

(defstub constrp (x) t)

(encapsulate ((fff (x) t))
             (local (defun fff (x) x))
             (skip-proofs (defthm constrp-fff (constrp (fff x)))))

(skip-proofs (defthm property-fff (property (fff x))))

(encapsulate ((ggg (x) t))
             (local (defun ggg (x) x))
             (skip-proofs (defthm constrp-ggg (constrp (ggg x))
                            :rule-classes nil)))

(defstub ppp (x) t)

(must-not-prove
 (property (ggg aaa))

; This proof will fail but you will see 5 cases: 4 from the
; :cases and a constraint.

 :hints
 (("Goal" :use (:instance (:functional-instance property-fff (fff ggg))
                          (x bbb))
   :cases ((ppp 1) (ppp 2) (ppp 3))))
 :otf-flg t)

(must-prove
 (property (ggg aaa))

; This proof will succeed.

 :hints
 (("Goal" :use ((:instance (:functional-instance property-fff (fff ggg))
                           (x aaa))
                (:instance constrp-ggg (x x)))
   :cases ((ppp 1) (ppp 2) (ppp 3)))
  ("Goal'" :use ((:instance constrp-ggg (x x))))))


; These examples test :or

(defstub property (x) t)

(defaxiom bar
  (implies (property (fff x)) (property x))
  :rule-classes nil)

(defaxiom mum
  (implies (property (ggg x)) (property x))
  :rule-classes nil)

(defaxiom aaa (property (fff x)))
(defaxiom bbb (property (ggg x)))
(in-theory (disable aaa bbb))

; This is just to see the the io.  The proof will fail.

(must-not-prove
 (property ccc)

;;;   ------------ this will fail ---------------

 :hints
 (("Goal"
   :OR
   ((:use (:instance bar (x disj-case-1)) :do-not '(generalize))
    (:use (:instance bar (x disj-case-2)) :do-not '(fertilize)))))
 :otf-flg t)

(must-not-prove
 (property ccc)

;;;   ------------ this will fail ---------------


 :hints
 (("Goal"
   :OR
   ((:use (:instance bar (x disj-case-1)) :do-not '(generalize))
    (:use (:instance bar (x disj-case-2)) :do-not '(fertilize)))))
 :otf-flg nil)


(must-prove
 (property ccc)

;;; ------------ this will succeed on the first branch ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ccc)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(must-prove
 (property ccc)

;;; ------------ this will succeed on the second branch ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ddd)))
    (:in-theory (enable bbb) :use (:instance mum (x ccc)))))))

(must-not-prove
 (property ccc)

;;; ------------ this will fail ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ddd)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(must-prove
 (property ccc)

;;; ------------ this will succeed ---------

 :hints
 (("Goal"
   :OR
   ((                      :use (:instance bar (x ccc)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(must-not-prove
 (property ccc)

;;; ------------ this will fail ---------

 :hints
 (("Goal"
   :OR
   ((:induct (append ccc x))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

; These examples test custom keyword hints:

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (splice-keyword-alist
                            :syn-use
                            (list :use val)
                            keyword-alist))))

(must-not-prove
 (equal x y)

; This hint will expand at pre-process time.  You will be able to
; tell because it will print a message every time it is run.
; You will see one expansion message.  The proof will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))
         ("Goal'" :in-theory (enable car-cons))))

(must-not-prove
 (equal x y)

; This will cause an error because of an ill-formed common hint mixed
; with syn-use.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalized)) ; error!
         ("Goal'" :in-theory (enable car-cons))))

(remove-custom-keyword-hint :syn-use) ; Added by Matt K.

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (splice-keyword-alist
                            :syn-use
                            (list :use val)
                            keyword-alist)))
                         :checker
                         (pprogn
                          (fms "~%Expanding :syn-use checker~%"
                               nil *standard-co* state nil)
                          (cond ((eq val 'cdr-cons)
                                 (er soft ctx
                                     "Syn-use doesn't allow you to use ~
                                      ~x0!"
                                     val))
                                (t (value t)))))

(must-not-prove
 (equal x y)

; This hint will expand at pre-process time.  You will see the checker
; and then the generator.  The proof will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))
         ("Goal'" :in-theory (enable car-cons))))

(must-not-prove
 (equal x y)

; This will cause an error because of the syn-use checker will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use cdr-cons
          :do-not '(generalized)) ; error!
         ("Goal'" :in-theory (enable car-cons))))

(add-custom-keyword-hint :eror
                         (value
                          (splice-keyword-alist
                           :eror
                           `(:ERROR ,(msg "The value ~x0 is illegal!" val))
                           keyword-alist)))

(must-not-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; This will throw an error on translation.

 :hints (("Subgoal *1/1'" :eror (a b c))))

(remove-custom-keyword-hint :eror) ; added by Matt K.

(add-custom-keyword-hint :eror
                         (value
                          (if (equal clause clause)
                              (splice-keyword-alist
                               :eror
                               `(:ERROR ,(msg "The value ~x0 is illegal!" val))
                               keyword-alist)
                            nil)))

(must-not-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; This will throw an error when Subgoal 1.1' arises

 :hints (("Subgoal *1/1'" :eror (a b c))))

(remove-custom-keyword-hint :syn-use) ; added by Matt K.

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (if (equal clause clause)
                               (splice-keyword-alist
                                :syn-use
                                (list :use val)
                                keyword-alist)
                             nil)))
                         :checker
                         (pprogn
                          (fms "~%Expanding :syn-use checker~%"
                               nil *standard-co* state nil)
                          (cond ((eq val 'cdr-cons)
                                 (er soft ctx
                                     "Syn-use doesn't allow you to use ~
                                      ~x0!"
                                     val))
                                (t (value t)))))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; You will see the checker expanded TWICE in pre-processing.  The
; first expansion is when we are trying to eagerly eliminate the
; :syn-use hint.  That fails.  So then we just run the all the
; checkers and we see it again.  Then the checker and the generator
; are run again in Subgoal *1/1'.

 :hints (("Subgoal *1/1'" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))))

(add-custom-keyword-hint :count-down
                         (value
                          (if (zp val)
                              (splice-keyword-alist
                               :count-down
                               '(:NO-OP t)
                               keyword-alist)
                            (splice-keyword-alist
                             :count-down
                             `(:count-down ,(- val 1))
                             keyword-alist))))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))
 :hints (("Subgoal *1/1'" :count-down 7)))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; Proof succeeds after a no-op hint is added

 :hints (("Subgoal *1/1'" :count-down 2)))

(remove-custom-keyword-hint :count-down)

(must-not-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; Error: illegal keyword

 :hints (("Subgoal *1/1'" :count-down 2)))

(add-custom-keyword-hint :count-down
                         (value
                         (if (and (equal clause clause)
                                  (zp val))
                             (splice-keyword-alist
                              :count-down
                              '(:NO-OP t)
                              keyword-alist)
                           (splice-keyword-alist
                            :count-down
                            `(:count-down ,(- val 1))
                            keyword-alist)))
                         :checker
                         (if (natp val)
                             (value t)
                           (er soft ctx
                               ":count-down wants a nat and ~x0 ain't one."
                               val)))


(must-not-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; Error at pre-process

 :hints (("Subgoal *1/1'" :count-down t)))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))
 :hints (("Subgoal *1/1'" :count-down 7)))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))
; Success

 :hints (("Subgoal *1/1'" :count-down 2)))

(add-custom-keyword-hint :recurse
                         (er-progn
                          (value (cw "--- Here goes ---"))
                          (defthm append-right-id
                            (implies (true-listp x)
                                     (equal (append x nil) x)))
                          (value (cw "--- Done ---"))
                          (value (if (equal clause clause)
                                     (splice-keyword-alist
                                      :recurse
                                      '(:NO-OP t)
                                      keyword-alist)
                                   nil))))

(must-prove
 (equal (append (append a b) c)
        (append a (append b c)))

; Scary Success.  This was designed to test the ens tracking and we didn't find
; anything amiss.

; This was labeled as "scary" above because it seemed conceivable that we would
; be able to provoke a slow array warning.

 :hints (("Subgoal *1/2" :in-theory (disable cdr-cons
                                             CONS-CAR-CDR
                                             car-cdr-elim))
         ("Subgoal *1/2'" :no-op t
          :recurse t
          )
         ("Subgoal *1/2''" :in-theory (disable cdr-cons cons-car-cdr))
         ("Subgoal *1/2'4'" :in-theory (enable cdr-cons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Illustration of ideas in :doc hints-and-the-waterfall
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-hints nil)
(set-override-hints nil)

; The following example is for advanced users of computed hints, and assumes an
; understanding of documentation topic hints-and-the-waterfall.

; Below we find two versions of nonlinearp-default-hint.  The first is from
; books/arithmetic-5/lib/basic-ops/default-hint.lisp, with the comment slightly
; modified.  The second is the result of removing a test and winding up with an
; infinite loop.

; For each version, we attempt to prove a trivial theorem that requires
; induction.  The first attempt succeeds, while the second fails.  In fact, we
; impose a time limit because the second attempt goes into an infinite loop.

; We explain this example by first explaining what the two versions of
; nonlinearp-default-hint have in common.  Each is a function that can generate
; a computed hint in either of the following two situations:

; (A) If the goal is stable under simplification -- i.e., if the goal or an
;     ancestor of it has passed through the simplifier without being changed --
;     then assuming nonlinear arithmetic is currently off, a computed hint is
;     generated that turns on nonlinear arithmetic for the current goal and all
;     its descendents, at least until another hint turns nonlinear arithmetic
;     off.

; (B) If we are at the top of the waterfall, nonlinear arithmetic is currently
;     enabled, and at least one proof process has applied to the current goal
;     or an ancestor of it, then a computed hint MAY BE generated that turns
;     off nonlinear arithmetic.

; In (B), "MAY BE" can be replaced by "is" for the second version of
; nonlinearp-default-hint, which is the one that can cause an infinite loop.
; The first version of nonlinearp-default-hint restricts (B) by refusing to
; generate a computed hint if the most recently applied proof process is the
; "settled down" process.  As we now explain, this refusal is what prevents an
; infinite loop.

; Consider the second version of nonlinearp-default-hint below, in which the
; clause is allowed to have just settled down when generating a hint that
; re-disables nonlinear arithmetic.  The following sequence occurs.

; (1) The initial goal for theorem TEST1 passes unchanged through the
;     simplification process (induction is the first successful proof
;     activity).  Thus the "settled-down" proof process hits, sending the goal
;     back to the top of the waterfall.

; (2) The goal passes through the waterfall, again passing through the
;     simplifier unchanged.  This time it then passes through the
;     "settled-down" process without hitting, since it had already settled
;     down.  So it reaches the point where we look for a computed hint to
;     select with variable STABLE-UNDER-SIMPLIFICATIONP bound to T.
;     Nonlinearp-default-hint generates a computed hint to turn on nonlinear
;     arithmetic (situation (A) above) and sends the goal back to the top of
;     the waterfall, with this hint as the selected hint.

;     NOTE: the history of the goal is modified to remove the indication that
;     it has settled down.  Quoting from :doc hints-and-the-waterfall, about
;     computed hints being selected in the case that
;     STABLE-UNDER-SIMPLIFICATIONP is T:

;       A subtlety is that in this case, if the most recent hit had been from
;       settling down, then the prover ``changes its mind'' and considers that
;       the goal has not yet settled down after all as it continues through the
;       waterfall.

; (3) The hint is applied to enable nonlinear arithmetic, and the goal passes
;     through the waterfall.  Because its history says that it has not yet
;     reached the point of settling down (see the "NOTE" in (2) above), the
;     "settled-down" proof process hits, sending the goal back to the top of
;     the waterfall.

; (4) In the search for an applicable hint, we are in situation (B) above and
;     hence the nonlinearp-default-hint applies to disable nonlinear
;     arithmetic.  (Remember, we are considering the second version of
;     nonlinearp-default-hint below, which does not consider settling down.)
;     Then the goal passes through the waterfall, and exactly as in (2) above,
;     situation (A) above applies, so nonlinearp-default-hint generates a
;     computed hint to turn on nonlinear arithmetic and sends the goal back to
;     the top of the waterfall, with this hint as the selected hint.

; We now have a loop (3), (4), (3), (4), (3), (4), ....  So why does the first
; version of nonlinearp-default-hint break this loop?  At the start of (4),
; situation (B) no longer applies because the goal has just settled down from
; (3), and hence the first (most recent) element of the history is a
; 'SETTLED-DOWN-CLAUSE entry.  Indeed, we can see that the proof of TEST1 in
; the first encapsulate form below generates a comment that "We now enable
; non-linear arithmetic" but no such comment about disabling.

(encapsulate
 ()

 (local
  (defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)
    (declare
     (xargs
      :guard ; Guard change for tau after ACL2 Version 5.0 by J Moore:
      (and (consp pspv)
           (consp (car pspv))
           (consp (car (car pspv)))
           (consp (cdr (car (car pspv))))
           (consp (cdr (cdr (car (car pspv)))))
           (consp (cdr (cdr (cdr (car (car pspv))))))
           (consp (cdr (cdr (cdr (cdr (car (car pspv)))))))
           (consp (cdr (cdr (cdr (cdr (cdr (car (car pspv))))))))
           (consp (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))
           (consp (car (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))))))
    (cond (stable-under-simplificationp
           (if (not (access rewrite-constant
                            (access prove-spec-var pspv :rewrite-constant)
                            :nonlinearp))
               (prog2$
                (cw "~%~%[Note: We now enable non-linear arithmetic.]~%~%")
                '(:computed-hint-replacement t
                                             :nonlinearp t))
             nil))
          ((access rewrite-constant
                   (access prove-spec-var pspv :rewrite-constant)
                   :nonlinearp)
           (if (and (consp hist)
                    (consp (car hist))
                    ;; The following is discussed below:
                    (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
               (prog2$
                (cw "~%~%[Note: We now disable non-linear arithmetic.]~%~%")
                '(:computed-hint-replacement t
                                             :nonlinearp nil))
             nil))
          (t
           nil))))

 (local
  (add-default-hints
   '((nonlinearp-default-hint stable-under-simplificationp hist pspv))))

 (local
  (defthm test1
    (equal (len (append x nil))
           (len x))
    :rule-classes nil)))

(encapsulate
 ()

 (local
  (defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)
    (declare
     (xargs
      :guard ; Guard change for tau after ACL2 Version 5.0 by J Moore:
      (and (consp pspv)
           (consp (car pspv))
           (consp (car (car pspv)))
           (consp (cdr (car (car pspv))))
           (consp (cdr (cdr (car (car pspv)))))
           (consp (cdr (cdr (cdr (car (car pspv))))))
           (consp (cdr (cdr (cdr (cdr (car (car pspv)))))))
           (consp (cdr (cdr (cdr (cdr (cdr (car (car pspv))))))))
           (consp (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))
           (consp (car (cdr (cdr (cdr (cdr (cdr (cdr (car (car pspv)))))))))))))
    (cond (stable-under-simplificationp
           (if (not (access rewrite-constant
                            (access prove-spec-var pspv :rewrite-constant)
                            :nonlinearp))
               (prog2$
                (cw "~%~%[Note: We now enable non-linear arithmetic.]~%~%")
                '(:computed-hint-replacement t
                                             :nonlinearp t))
             nil))
          ((access rewrite-constant
                   (access prove-spec-var pspv :rewrite-constant)
                   :nonlinearp)
           (if (and (consp hist)
                    (consp (car hist))
                    ;; The extra test is removed this time:
                    ;; (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE))
                    )
               (prog2$
                (cw "~%~%[Note: We now disable non-linear arithmetic.]~%~%")
                '(:computed-hint-replacement t
                                             :nonlinearp nil))
             nil))
          (t
           nil))))

 (local
  (add-default-hints
   '((nonlinearp-default-hint stable-under-simplificationp hist pspv))))

 (must-fail
  (with-prover-time-limit
; The proof of the previous test1 has succeeded in Sept. 2009 on a 2.2GHz
; Opteron (tm) Processor 850 in under 1/20 seconds of real time.  So the time
; limit below seems generous.  It was still sufficient to see over 240 trips
; through the infinite loop.
   1/5
   (defthm test1
     (equal (len (append x nil))
            (len x))
     :rule-classes nil))))
