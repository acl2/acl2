(princ$ ; wording required by DARPA:

"
This research was developed with funding from the Defense Advanced
Research Projects Agency (DARPA).  The views, opinions and/or findings
expressed are those of the authors and should not be interpreted as
representing the official views or policies of the Department of
Defense or the U.S. Government.  Released under Distribution Statement
``A'' (Approved for Public Release, Distribution Unlimited).
"

*standard-co* state)

; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; -----------------------------------------------------------------

; SKIP TO THE NEXT SECTION WHEN READING: This section contains some
; infrastructure to support book certification, which is not interesting from
; the perspective of the paper, "Advances in ACL2 Proof Debugging Tools".

; There are some calls of acl2-query that read from *standard-oi*.  So we
; redefine that input channel to be the current value of 'standard-oi.  There
; is also output printed to the comment window.  So we redirect that output to
; the current value of 'standard-co.

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

; Section 2

(deflabel start-section-2)

(include-book "std/lists/rev" :dir :system)

(with-brr-data
 (thm (implies (and (natp n)
                    (< n (len x)))
               (equal (nth n (revappend x y))
                      (nth n (reverse x))))
      :hints ; The second example shows what happens when we remove :hints.
      (("Goal" :do-not '(preprocess)))))

(cw-gstack-for-subterm (REV X))

(with-brr-data
 (thm (implies (and (natp n)
                    (< n (len x)))
               (equal (nth n (revappend x y))
                      (nth n (reverse x))))))

(cw-gstack-for-subterm (REV X))

(ubt 'start-section-2)

; -----------------------------------------------------------------

; Section 3

; Setup for all break-rewrite examples in Sections 3 and 6

(set-brr-evisc-tuple nil state)
(include-book "projects/apply/top" :dir :system)

(encapsulate ((p (x) t)
              (q (x) t)
              (r (x) t)
              (s (x) t)
              (f (x y) t))
  (local (defun p (x) (declare (ignore x)) t))
  (local (defun q (x) (declare (ignore x)) t))
  (local (defun r (x) (declare (ignore x)) t))
  (local (defun s (x) (declare (ignore x)) t))
  (local (defun f (x y) (declare (ignore x y)) t))
  (defthm p-rule (implies (q x)(p (f x y))))
  (defthm q-rule1 (implies (r x)(q x)))
  (defthm q-rule2 (implies (s x)(q x)))
  )

(defun nats (n)
  (if (zp n) '(0) (cons n (nats (- n 1)))))

(defstub foo (x) t)

; ----
; Example 1

; Relevant rules in this example
; (defthm p-rule (implies (q x)(p (f x y))))
; (defthm q-rule1 (implies (r x)(q x)))

(thm (implies (r v) (p (f u v))))
; fails

(brr t)
(monitor 'p-rule t)
(monitor 'q-rule1 t)
(thm (implies (r v) (p (f u v))))
:eval
:eval
:type-alist
"Normally we would execute :a! here, but to support book
 certification, we simply let the proof run to completion."
; :a!
:go!
:go!
:go!

(thm (implies (r u) (p (f u v))))
:go
:go
; Q.E.D.

; ----
; Example 2:

(defthm lemma-a
  (loop$ for e in (nats n) always (atom e)))

(defthm thm-a
  (loop$ for e in (nats (foo a)) always (atom e)))

(brr t)
(unmonitor :all)
(monitor 'lemma-a '(:lambda t))

(defthm thm-a
  (loop$ for e in (nats (foo a)) always (atom e)))
:target
:lhs
"Normally we would execute :a! here, but to support book
 certification, we simply let the proof run to completion."
; :a!
:go!
:go!
:go!

; This confirms the fix
(unmonitor :all)

(defthm lemma-a-revised
  (loop$ for e in (nats n) always (if (consp e) nil t)))

(thm ; thm-a
  (loop$ for e in (nats (foo a)) always (atom e)))

; -----------------------------------------------------------------
; Section 6, Example 1

(brr t)
(monitor 'p-rule ''(:go))
(monitor 'q-rule1 ''(:go))
(thm (implies (r u) (p (f u v))))

; [indentation added]

; ACL2 !>(thm (implies (r u) (p (f u v))))
;
;       (1 Breaking (:REWRITE P-RULE) on (P (F U V)):
;       1 ACL2 >:GO
;
;             (2 Breaking (:REWRITE Q-RULE1) on (Q U):
;             2 ACL2 >:GO
;
;             2 (:REWRITE Q-RULE1) produced 'T.
;             2)
;
;       1 (:REWRITE P-RULE) produced 'T.
;       1)
;
; Q.E.D.

(trace$ (brkpt1 :entry 'brkpt1 :exit 'brkpt1)
        (brkpt2 :entry 'brkpt2 :exit 'brkpt2))

(thm (implies (r u) (p (f u v))))

; ACL2 !>(thm (implies (r u) (p (f u v))))
; 1> BRKPT1 {p-rule}
;
;        (1 Breaking (:REWRITE P-RULE) on (P (F U V)):
;        1 ACL2 >:GO
; <1 BRKPT1 {p-rule}
; 1> BRKPT1 {q-rule2}
; <1 BRKPT1 {q-rule2}
; 1> BRKPT2 {q-rule2}
; <1 BRKPT2 {q-rule2}
; 1> BRKPT1 {q-rule1}
;
;              (2 Breaking (:REWRITE Q-RULE1) on (Q U):
;              2 ACL2 >:GO
; <1 BRKPT1 {q-rule1}
; 1> BRKPT2 {q-rule1}
;
;              2 (:REWRITE Q-RULE1) produced 'T.
;              2)
; <1 BRKPT2 {q-rule1}
; 1> BRKPT2 {p-rule1}
;
;        1 (:REWRITE P-RULE) produced 'T.
;        1)
; <1 BRKPT2 {p-rule1}
;
; Q.E.D.

; -----------------------------------------------------------------

; SKIP THIS WHEN READING: This is just some final support for book
; certification.

(redef+)
(defconst *standard-oi* *old-standard-oi*)
(redef-)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
