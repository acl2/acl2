;;
;; Copyright (C) 2020, David Greve
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;;
(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

;; The issue that we address with this macro, and that we illustrate
;; below, is that in the course of a proof, ACL2 appears to lose
;; information that *would* (in this case) have allowed it to complete
;; the proof.

;; J Moore made the following observations about this behavior:

;; Here we illustrate the source of the "problem" using purely
;; propositional simplification.
;; 
;; ACL2 !>(clausify '(IF A
;;                     B
;;                     (IF C
;;                         B
;;                         'T))
;;                 nil nil 500)
;; (((NOT A) B)   ; A --> B
;;  ((NOT C) B))  ; C --> B
;; 
;; The issue is this: Do you really want to focus on (~A & C) --> B
;; when you already have to prove A --> B?
;; 
;; This process is called ``subsumption-replacement'' which comes from
;; resolution.  It says that if you're adding a new clause, (~A B), to
;; a set of clauses to prove, e.g., {(A ~C B)}, and a resolvent of the
;; new clause and one of the old ones subsumes one of the parents,
;; replace the subsumed clause by the resolvent.  So the resolvent of
;; (~A B) and (A ~C B) is (~C B), which subsumes the second parent so
;; we replace it with the resolvent.
;; 
;; This example is really basic (being purely propositional).  Doing
;; away with this process would add a lot of ``junk'' to clauses.  I
;; can imagine for some A it might be useful, e.g., as in Dave's
;; example.  But I can imagine for other A, e.g., humongous terms,
;; you'd just as soon drop it.

;; Fortunately, using only existing mechanisms in ACL2, we were able
;; to inhibit this process on the challenge problem.  Curiously, it
;; requires the combination of two features, a quick-and-dirty-srs
;; attachment and a :case-split-limitation hint, because subsumption
;; takes place in multiple places during simplification.

(defmacro without-subsumption(form &key (cases 'nil))
  `(encapsulate
       ()

     (local (defun without-subsumption-disable-quick-and-dirty (x y)
              (declare (ignore x y) (xargs :guard t)) nil))
     (local (defattach-system quick-and-dirty-srs
              without-subsumption-disable-quick-and-dirty))
     (set-case-split-limitations '(0 ,cases))
     
     ,form

     ))

;; Below we illustrate the use of the without-subsumption macro to
;; prove the lemma that served as the original motivating example in
;; its development.  Along the way we document failing proofs that
;; demonstrate the symptoms we originally observed .. symptoms that
;; suggest situations in which this macro may prove handy.

(local
 (encapsulate
     ()

   ;; This example was derived from the k-induction book originally written
   ;; by Matt Kaufmann.
   ;;
   ;; Copyright (C) 2020, Matt Kaufmann
   ;; Written by Matt Kaufmann
   ;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(encapsulate
  ((pk (n params) t)
   (pk-k () t)
   (pk-badguy (n params) t))

  (local (defun pk (n params)
           (declare (ignore n params))
           t))

  (local (defun pk-k ()
           1))

  (local (defun pk-badguy (n params)
           (declare (ignore n params))
           0))

  (defthm posp-pk-k
    (posp (pk-k))
    :rule-classes :type-prescription)

  (defthm natp-pk-badguy
    (natp (pk-badguy n params))
    :rule-classes :type-prescription)

  (defthm pk-badguy-range
    (implies (and (natp n)
                  (not (pk n params)))
             (and (< (pk-badguy n params)
                     n)
                  (>= (pk-badguy n params)
                      (- n (pk-k)))))
    :rule-classes (:linear :rewrite))

  (defthm pk-badguy-is-counterexample
    (implies (and (natp n)
                  (not (pk n params)))
             (not (pk (pk-badguy n params) params)))))

(defun pk-induction (n params)
  (if (or (zp n) (pk n params))
      t
    (pk-induction (pk-badguy n params) params)))

(defthm pk-0
  (pk 0 params)
  :hints (("Goal" :use ((:instance pk-badguy-range (n 0))))))

(defthm pk-holds
  (implies (natp n)
           (pk n params))
  :hints (("Goal" :induct (pk-induction n params))))

(encapsulate
  ((q (n x y) t))
  (local (defun q (n x y)
           (declare (ignore n x y))
           t))
  (defthm q-3-properties
    (and (q 0 x y)
         (q 1 x y)
         (q 2 x y)
         (implies (and (natp n)
                       (<= 3 n)
                       (q (- n 3) x y)
                       (q (- n 2) x y)
                       (q (- n 1) x y))
                  (q n x y)))))

(defun q-params (n params)
  (q n (nth 0 params) (nth 1 params)))

(defun k-params-badguy (n k params)
  (if (zp k) n
    (if (zp n) 0
      (let ((n (1- n)))
        (if (not (q-params n params)) n
          (k-params-badguy n (- k 1) params))))))

(defthm open-k-params
  (implies
   (syntaxp (quotep k))
   (equal (k-params-badguy n k params)
          (if (zp k) n
            (if (zp n) 0
              (let ((n (1- n)))
                (if (not (q-params n params)) n
                  (k-params-badguy n (- k 1) params))))))))


(local (include-book "misc/eval" :dir :system))

;; As formulated, the following proof fails.  I'm turning off (zp)
;; related rules to help show what is happening.

(local
 (must-fail
  (defthmd q-params-holds-1
    (implies (natp n)
             (q-params n params))
    :otf-flg t
    :hints (("Goal" :use ((:functional-instance pk-holds
                                                (pk q-params)
                                                (pk-k (lambda () 3))
                                                (pk-badguy (lambda (n params) (k-params-badguy n 3 params)))))
             :in-theory (disable open-k-params ZP-COMPOUND-RECOGNIZER zp zp-open))
            ;; Open up K-PARAMS-BADGUY (but disable zp-related rules)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (open-k-params) (ZP-COMPOUND-RECOGNIZER zp zp-open))))
            ;; Re-enable zp rules
            (and stable-under-simplificationp
                 '(:in-theory (enable zp-open zp)))
            ))
  :with-output-off nil))

;; In Subgoal 4.2.4 (zp n) is true.  Here we see (zp n) in the
;; hypothesis.  This case proves without problems.

;; Subgoal 4.2.4
;; (IMPLIES (AND (INTEGERP N)
;;               (<= 0 N)
;;               (CONSP PARAMS)
;;               (NOT (Q N (CAR PARAMS) (NTH 1 PARAMS)))
;;               (ZP N))  ;; <<- This is the case we are considering
;;          (NOT (Q 0 (CAR PARAMS) (NTH 1 PARAMS)))).

;; Subgoal 4.2.2 is the case where (zp (1- n)) is true; but in
;; order to open up K-PARAMS-BADGUY to this point, (zp n)
;; must have been false.  However, (not (zp n)) is conspicuously
;; absent from the hypothesis .. and THIS IS WHY THE PROOF FAILS.

;; Subgoal 4.2.2
;; (IMPLIES (AND (INTEGERP N)
;;               (<= 0 N)
;;               (CONSP PARAMS)
;;               (NOT (Q N (CAR PARAMS) (NTH 1 PARAMS)))
;;               (Q (+ -1 N) (CAR PARAMS) (NTH 1 PARAMS))
;;               (ZP (+ -1 N)))  ;; <<- This is the case we are considering
;;                               ;; ?? Where is (not (zp n)) ??
;;          (NOT (Q 0 (CAR PARAMS) (NTH 1 PARAMS)))).


;; Beyond this point, lacking additional case splitting, the proof
;; just fails.

;; This time we try something different.  We run the proof in slow
;; motion .. note the :restrict hint applied to open-k-params .. this
;; ensures that we open up K-PARAMS-BADGUY one step at a time.

(local
 (encapsulate ()
   (local
    (defthm q-params-holds-2
      (implies (natp n)
               (q-params n params))
      :otf-flg t
      :hints (("Goal" :use ((:functional-instance pk-holds
                                                  (pk q-params)
                                                  (pk-k (lambda () 3))
                                                  (pk-badguy (lambda (n params) (k-params-badguy n 3 params)))))
               :in-theory (disable open-k-params))
              ;; Open K-PARAMS-BADGUY one step at a time (with zp-related rules disabled)
              (and stable-under-simplificationp
                   '(:in-theory (e/d (open-k-params) (ZP-COMPOUND-RECOGNIZER zp zp-open))
                                :restrict ((open-k-params ((k 3))))))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (open-k-params) (ZP-COMPOUND-RECOGNIZER zp zp-open))
                                :restrict ((open-k-params ((k 2))))))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (open-k-params) (ZP-COMPOUND-RECOGNIZER zp zp-open))
                                :restrict ((open-k-params ((k 1))))))
              ;; Re-enable zp rules
              (and stable-under-simplificationp
                   '(:in-theory (enable zp-open zp)))
              ))
    )))

;; Now Subgoal 4.2.2 is the case where (zp n) is true (Subgoal
;; 4.2.4 above) and this case proves without problems.

;; Subgoal 4.2.2
;; (IMPLIES (AND (INTEGERP N)
;;               (<= 0 N)
;;               (CONSP PARAMS)
;;               (NOT (Q N (CAR PARAMS) (NTH 1 PARAMS)))
;;               (ZP N)) ;; <<- This is the case we are considering
;;          (NOT (Q 0 (CAR PARAMS) (NTH 1 PARAMS)))).

;; This time we get a Subgoal 4.2.1 in which we explicitly know (not
;; (zp n)) ..

;; Subgoal 4.2.1
;; (IMPLIES (AND (INTEGERP N)
;;               (<= 0 N)
;;               (CONSP PARAMS)
;;               (NOT (Q N (CAR PARAMS) (NTH 1 PARAMS)))
;;               (NOT (ZP N)) ;; <<- Yay!
;;               (Q (+ -1 N)
;;                  (CAR PARAMS)
;;                  (NTH 1 PARAMS)))
;;          (NOT (Q (K-PARAMS-BADGUY (+ -1 N) 2 PARAMS)
;;                  (CAR PARAMS)
;;                  (NTH 1 PARAMS)))).

;; We continue expanding K-PARAMS-BADGUY and end up with Subgoal
;; 4.2.1.2 in which (ZP (+ -1 N)) is true (just like in Subgoal 4.2.2
;; from the failed proof above) but this time we also know (not
;; (zp n)).

;; Subgoal 4.2.1.2
;; (IMPLIES (AND (INTEGERP N)
;;               (<= 0 N)
;;               (CONSP PARAMS)
;;               (NOT (Q N (CAR PARAMS) (NTH 1 PARAMS)))
;;               (NOT (ZP N)) ;; <<- This was missing in the previous proof
;;               (Q (+ -1 N) (CAR PARAMS) (NTH 1 PARAMS))
;;               (ZP (+ -1 N))) ;; <<- This is the case we are considering
;;          (NOT (Q 0 (CAR PARAMS) (NTH 1 PARAMS)))).

;; With that information in hand we re-enable ZP and this case
;; proves without issue.

;; And, in fact, using the slow opening strategy, ACL2 is able to
;; complete the entire proof because it isn't losing information along
;; the way.

;; The lack of an essential hypothesis in a failing subgoal, a
;; hypothesis that "should have been generated" by the opening of
;; various definitions, is a possible indication that
;; without-subsumption might be useful.

;; Here the same proof that ultimately succeeds is shown failing
;; for lack of the without-subsumption macro.

(local
 (must-fail
 (defthm q-params-holds-3
   (implies (natp n)
            (q-params n params))
   :otf-flg t
   :hints (("Goal" :use
            ((:functional-instance
              pk-holds
              (pk q-params)
              (pk-k (lambda () 3))
              (pk-badguy (lambda (n params) (k-params-badguy n 3 params)))))
            )))
 :with-output-off nil)
 )

;; Finally, the successful proof using the without-subsumption macro.

(without-subsumption
 (defthmd q-params-holds-4
   (implies (natp n)
            (q-params n params))
   :otf-flg t
   :hints (("Goal" :use
            ((:functional-instance
              pk-holds
              (pk q-params)
              (pk-k (lambda () 3))
              (pk-badguy (lambda (n params) (k-params-badguy n 3 params)))))
            )))
 )
 
))

(defxdoc without-subsumption
  :short "Perform proofs without subsumption/replacement to preserve hypotheses that might otherwise be dropped."
  :parents (proof-automation)
  :long "
<p>
@('without-subsumption') is a simple macro that allows you to perform
proofs without subsumption/replacement to preserve hypotheses that
might otherwise be dropped during clausification.
</p>
<p>
In the course of a proof, ACL2 will sometimes drop hypotheses during
subsumption/replacement that would otherwise have allowed it to
complete the proof.
</p>
<p>
@('without-subsumption') uses both
@(tsee quick-and-dirty-subsumption-replacement-step) and
@(tsee case-split-limitations) to stop subsumption/replacement in various
stages of the ACL2 simplifier.  These hints can help preserve hypothesis
in a proof that the ACL2 simplifier might otherwise drop.  The
macro is defined as follows:
</p>
@({
 (defmacro without-subsumption(form &key (cases 'nil))
  `(encapsulate
       ()

     (local (defun without-subsumption-disable-quick-and-dirty (x y)
              (declare (ignore x y) (xargs :guard t)) nil))
     (local (defattach-system quick-and-dirty-srs
              without-subsumption-disable-quick-and-dirty))
     (set-case-split-limitations '(0 ,cases))
     
     ,form

     ))
})
<p>Usage:</p>
@({
 (include-book \"tools/without-subsumption\" :dir :system)
 (without-subsumption
   (defthm natp-implies-integerp
     (implies 
       (natp n)
       (integerp n)))
  )
 })

")
