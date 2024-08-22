; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Experiments with Geneqv
; Matt Kaufmann and J Moore
; June, 2024

; This book illustrates the ideas discussed in :DOC geneqv.  See that
; documentation for commentary.  This is a run-script-style file: i/o behavior
; during the certification is recorded and compared to the expected i/o.  If
; you want to read a transcript of the processing of these commands see
; geneqv-test-log.txt.

(in-package "ACL2")

; -----------------------------------------------------------------
; This section may be skipped.  This is part of the infrastructure of using
; run-script. It just arranges for the break-rewrite i/o to be recorded during
; the certification.

(defconst *old-standard-oi* *standard-oi*)
(redef+)
(make-event `(defconst *standard-oi* ',(standard-oi state)))
(make-event `(defconst *standard-co* ',(standard-co state)))
(f-put-global 'trace-co (standard-co state) state)

(defun set-ld-prompt (val state)
  (er-progn
   (chk-ld-prompt val 'set-ld-prompt state)
   (if (eq val 'brr-prompt)
       (set-ld-pre-eval-print t state)
     (value nil))
   (pprogn
    (f-put-global 'ld-prompt val state)
    (value val))))

(redef-)
; -----------------------------------------------------------------

(include-book "sorting/isort" :dir :system)

(defequiv perm) ; redundant

(defcong perm equal (len x) 1
  :hints (("Goal" :in-theory (disable CONVERT-PERM-TO-HOW-MANY))))

; Here is a rewrite rule that uses perm as the equivalence relation.
; Note that isort is an identity function with respect to perm.

(defthm perm-isort ; redundant
  (perm (isort x) x))

(defun pairwise-iff (x y)
  (cond ((atom x) (atom y))
        ((atom y) nil)
        (t (and (iff (car x) (car y))
                (pairwise-iff (cdr x) (cdr y))))))

(defequiv pairwise-iff)

(defcong pairwise-iff equal (len x) 1)

(defun norml (x)
  (cond ((atom x) nil)
        (t (cons (if (car x) t nil)
                 (norml (cdr x))))))

; Here is a rewrite rule that uses pairwise-iff as the equivalence
; relation.  Norml is an identity wrt pairwise-iff.

(defthm pairwise-iff-norml
  (pairwise-iff (norml x) x))

; We will install a monitor on the rule perm-isort (including breaks for
; refinement failures, though none occur in this script) and explore the
; failure in the resulting interactive break.

(brr t)
(monitor 'perm-isort '(:rf t))

; This theorem is trivial with equivalence/congruence reasoning: both isort and
; norml are identity functions wrt to congruences admited by len.  But our
; monitor will prompt a break and we can inspect the situation.  Preprocessing
; is avoided because we're trying to monitor a simple abbreviation rule, as
; mentioned in :doc monitor and :doc geneqv.

(defthm example-thm-1
  (equal (len (isort (norml x))) (len x))
  :hints (("Goal" :do-not '(preprocess)))
  :rule-classes nil)

; The break will prompt us for input, which we provide here:

:geneqv

(get-brr-local 'geneqv state)

:ok

; Here is what the break looks like and how we'd inspect geneqv in it.

; (1 Breaking (:REWRITE PERM-ISORT) on (ISORT (NORML X)):
; 1 ACL2 >:geneqv
;
; Geneqv:
; ((PAIRWISE-IFF PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;  (PERM PERM-IMPLIES-EQUAL-LEN-1))
;
; ==========
; Use (GET-BRR-LOCAL 'GENEQV STATE) to see actual geneqv data structure.
; 1 ACL2 >(get-brr-local 'geneqv state)
; ((5717 PAIRWISE-IFF
;        :CONGRUENCE PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;  (5710 PERM
;        :CONGRUENCE PERM-IMPLIES-EQUAL-LEN-1))
; 1 ACL2 >:ok
; 1)

; Now we'll experiment with a third equivalence relation.

(defun equal-nat-list (x y)
  (cond ((atom x) (atom y))
        (t (and (not (atom y))
                (equal (nfix (car x)) (nfix (car y)))
                (equal-nat-list (cdr x) (cdr y))))))

(defequiv equal-nat-list)

; We're going to ``forget'' to prove the necessary :congruence rule!

; (defcong equal-nat-list equal (len x) 1)

; But we will prove a :rewrite that will be crucial (but unavailable due to the
; refinement check) to the proof below.  Nfix-list is an identity function wrt
; equal-nat-list.

(defthm equal-nat-list-nfix-list
  (equal-nat-list (nfix-list x) x))

; The following fails, at least if we do not allow an inductive proof.  If we
; provoke a break via perm-isort, as above, we could inspect the :geneqv and
; we'd find it is exactly what it was above.  Our intended proof would have
; used equal-nat-list-nfix-list as a rewrite rule.  But equal-nat-list is not
; in the geneqv.  We need the geneqv to include that equivalence if we expect
; to use it!

(defthm example-thm-2
  (equal (len (isort (norml (nfix-list x)))) (len x))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t))
  :rule-classes nil)

:geneqv

:path+

:go

; If preprocessing is suppressed, the output from the break and a subsequent
; :go command is

; (1 Breaking (:REWRITE PERM-ISORT) on (ISORT (NORML (NFIX-LIST X))):
; 1 ACL2 >:geneqv
;
; Geneqv:
; ((PAIRWISE-IFF PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;  (PERM PERM-IMPLIES-EQUAL-LEN-1))
;
; ==========
; Use (GET-BRR-LOCAL 'GENEQV STATE) to see actual geneqv data structure.
; 1 ACL2 >:path+
; 1. Simplifying the clause
;      ((EQUAL (LEN (ISORT (NORML (NFIX-LIST X))))
;              (LEN X)))
; 2. Rewriting (to simplify) the atom of the first literal,
;      (EQUAL (LEN (ISORT (NORML (NFIX-LIST X))))
;             (LEN X)),
;    Geneqv: (IFF)
; 3. Rewriting (to simplify) the first argument,
;      (LEN (ISORT (NORML (NFIX-LIST X)))),
; 4. Rewriting (to simplify) the first argument,
;      (ISORT (NORML (NFIX-LIST X))),
;    Geneqv: ((PAIRWISE-IFF PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;             (PERM PERM-IMPLIES-EQUAL-LEN-1))
; 5. Attempting to apply (:REWRITE PERM-ISORT) to
;      (ISORT (NORML (NFIX-LIST X)))
;    Preserving: PERM
;    Geneqv: ((PAIRWISE-IFF PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;             (PERM PERM-IMPLIES-EQUAL-LEN-1))
; 1 ACL2 >:go
;
; 1 (:REWRITE PERM-ISORT) produced (NORML (NFIX-LIST X)).
; 1)

; Note that in frame 3 we are rewriting a call of LEN to preserve EQUAL.  (The
; EQUAL is not shown because it is the default equivalence that is almost
; always the only one being preserved.)  Note that in frame 4 we derive the
; geneqv consisting of (PAIRWISE-IFF PERM), using the congruence rules that
; they both preserve EQUAL on LEN.  We need the analogous congruence rule for
; EQUAL-NAT-LIST if we're to have the expanded geneqv allowing the rewrite we
; want.

; To fix this we need to prove the congruence rule we ``forgot.''

(defcong equal-nat-list equal (len x) 1)

; Now if you inspect geneqv in the perm-isort break you'll see it lists all
; three of our equivalence relations.

(defthm example-thm-2
  (equal (len (isort (norml (nfix-list x)))) (len x))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t))
  :rule-classes nil)

:geneqv
:go

; (1 Breaking (:REWRITE PERM-ISORT) on (ISORT (NORML (NFIX-LIST X))):
; 1 ACL2 >:geneqv

; Geneqv:
; ((EQUAL-NAT-LIST EQUAL-NAT-LIST-IMPLIES-EQUAL-LEN-1)
;  (PAIRWISE-IFF PAIRWISE-IFF-IMPLIES-EQUAL-LEN-1)
;  (PERM PERM-IMPLIES-EQUAL-LEN-1))

; ==========
; Use (GET-BRR-LOCAL 'GENEQV STATE) to see actual geneqv data structure.
; 1 ACL2 >:ok
; 1)

; The proof succeeds.

; -----------------------------------------------------------------
; This section can be skipped.  It just undoes the infrastructure changes
; made at the top of this file.

(redef+)
(defconst *standard-oi* *old-standard-oi*)
(redef-)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)

; -----------------------------------------------------------------
