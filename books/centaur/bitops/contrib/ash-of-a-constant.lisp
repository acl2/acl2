; Matt Kaufmann
; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "log2")

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local (scatter-exponents))

 (local (defthm <-ash-reduction-lemma
          (implies (and (natp x)
                        (integerp shift-exp)
                        (natp constant-exp)
                        (<= shift-exp constant-exp))
                   (equal (< (ash x shift-exp) (expt 2 constant-exp))
                          (< x (expt 2 (- constant-exp shift-exp)))))
          :hints (("Goal"
                   :in-theory
                   (enable prefer-positive-exponents-scatter-exponents-<)))
          :rule-classes nil))

 (defthm <-ash-reduction
   (implies (and (syntaxp (and (quotep expt-2-constant-exp)
                               (posp (unquote expt-2-constant-exp))))
                 (equal constant-exp
; binding hypothesis; see (1) in :doc free-variables
                        (log2 expt-2-constant-exp))
                 (equal expt-2-constant-exp (expt 2 constant-exp))
                 (natp x)
                 (integerp shift-exp)
                 (natp constant-exp)
                 (<= shift-exp constant-exp))
            (equal (< (ash x shift-exp) expt-2-constant-exp)
                   (< x (expt 2 (- constant-exp shift-exp)))))
   :hints (("Goal" :use <-ash-reduction-lemma)))
)

; Examples

; Need to disable ash in order for <-ash-reduction to have a decent chance at
; firing:
(local (in-theory (disable ash)))

; Sadly, I got a stack overflow from calls of expt on large naturals.  The
; following trick restricts when we are willing to execute expt.  It's probably
; far from perfect, but good enough for demo purposes.  David, I suspect that
; you already have your own decent solution for this issue.

(defun expt-compute-fn (r i)
  (declare (xargs :guard ; same as for expt
                  (and (acl2-numberp r)
                       (integerp i)
                       (not (and (eql r 0) (< i 0))))))
  (expt r i))

(defthm expt-compute-lemma
  (implies (and (syntaxp (quotep i))
                (< (abs i) 10000))
           (equal (expt r i)
                  (expt-compute-fn r i))))

(in-theory (disable (expt)))

; Now for some testing.

(defmacro my-def-ash-lemma (shift-exp constant-exp)
  `(defthm ,(packn (list 'test- shift-exp '- constant-exp))
     (implies (natp x)
              (equal (< (ash x ,shift-exp) ,(expt 2 constant-exp))
                     (< x ,(expt 2 (- constant-exp shift-exp)))))
     :hints (("Goal" :in-theory (disable ash)))
     :rule-classes nil))

(my-def-ash-lemma 2 75)

; Is this what we expected?  Yes!
(encapsulate
 ()
 (set-enforce-redundancy t)

 (DEFTHM TEST-2-75
   (IMPLIES (NATP X)
            (EQUAL (< (ASH X 2) 37778931862957161709568)
                   (< X 9444732965739290427392)))
   :RULE-CLASSES NIL))

; More tests:

(my-def-ash-lemma 4 75)
(my-def-ash-lemma 6 75)
(my-def-ash-lemma 8 82)
(my-def-ash-lemma 1 82)
