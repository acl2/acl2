; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 61: type-alist-equality-loop1 (type-set-b.lisp:11843) reports a
; contradiction with (puffert ttree) at :11885 and DROPS ttree0, the tag-tree of
; the (EQUAL arg1 arg2) type-alist entry bound at :11867:
;
;   ((ts= int *ts-empty*)
;    (mv 'contradiction nil (puffert ttree)))            ; <- ttree0 dropped
;
; ttree0 is the SOLE licence for the contradiction -- disjoint argument types are
; not contradictory by themselves; it is the assumed equality that makes them so.
; So when ttree0 carries an 'assumption (a FORCEd hypothesis) or 'pt tags, they
; vanish, no forcing round is generated, and simplify-clause reports the clause
; proved.
;
; TWO IMPLEMENTATIONS OF ONE IDEA.  The next cond clause of the SAME function
; (:11899-11900) does (puffert (cons-tag-trees ttree0 ttree)), and so does the
; corresponding disjoint-types branch of assume-true-false (:10503-10507).
;
; Consumers: type-alist-clause (:12376-12378) and forward-chain-top
; (simplify.lisp:4664-4672) both hand that ttree onward as the only justification
; that the context is contradictory, and simplify-clause1 (simplify.lisp:8198)
; turns it into "simplify-clause proved this clause, with this ttree".
;
; Measured at the function level: HAS-ASSUMPTION = NO,
; ASSUMPTION-FREE-TTREEP = T, with the traced type-alist showing the clean
; (WAA X) binding shadowing the FORCE-tainted one.
;
; WHY IT IS RARE: reaching :11885 needs the disjointness to emerge only from the
; equality loop's milking pass -- hence conditional type-prescriptions for the
; "tighteners" and a nesting so their sort-fcds1-rating is below that of the two
; equalities.  In (mini-proveall) the function is entered 2305 times and reaches
; this branch 0 times.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour -- BOOM is false, since
; the local witness makes (wtrig x) = T.  RED while the defect is present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(encapsulate
 (((wtrig *) => *) ((waa *) => *) ((wbb *) => *) ((wcc *) => *)
  ((wbad *) => *)
  ((wpb *) => *) ((wqb *) => *) ((wrb *) => *)
  ((wpc *) => *) ((wqc *) => *) ((wrc *) => *))
 (local (defun wtrig (x) (declare (ignore x)) t))
 (local (defun waa (x) (declare (ignore x)) 0))
 (local (defun wbb (x) (declare (ignore x)) 0))
 (local (defun wcc (x) (declare (ignore x)) (cons 1 nil)))
 (local (defun wbad (x) (declare (ignore x)) nil))
 (local (defun wpb (x) (declare (ignore x)) t))
 (local (defun wqb (x) x))
 (local (defun wrb (x) x))
 (local (defun wpc (x) (declare (ignore x)) t))
 (local (defun wqc (x) x))
 (local (defun wrc (x) x))
 ; the two "tighteners": conditional, so both argument types are unknown when
 ; the equalities are assumed, and nested so their rating is the lower one.
 (defthm tp-b (implies (wpb (wqb (wrb x))) (integerp (wbb x)))
   :rule-classes :type-prescription)
 (defthm tp-c (implies (wpc (wqc (wrc x))) (consp (wcc x)))
   :rule-classes :type-prescription)
 ; the FORCEd equality: its ttree is the one that gets dropped.
 (defthm fc-e2 (implies (and (wtrig x) (force (wbad x)))
                        (equal (waa x) (wcc x)))
   :rule-classes ((:forward-chaining :trigger-terms ((wtrig x)))))
 (defthm fc-e1 (implies (wtrig x) (equal (waa x) (wbb x)))
   :rule-classes ((:forward-chaining :trigger-terms ((wtrig x)))))
 (defthm fc-tb (implies (wtrig x) (wpb (wqb (wrb x))))
   :rule-classes ((:forward-chaining :trigger-terms ((wtrig x)))))
 (defthm fc-tc (implies (wtrig x) (wpc (wqc (wrc x))))
   :rule-classes ((:forward-chaining :trigger-terms ((wtrig x))))))

; THE DEFECT.  (not (wtrig x)) is false -- the local witness makes (wtrig x) = T
; -- yet forward chaining "proves" it, because the contradiction it found rests
; on a FORCEd hypothesis whose assumption was dropped.  The summary names
; FC-E1, FC-TB, FC-TC, TP-B, TP-C and :FAKE-RUNE-FOR-TYPE-SET -- but NOT FC-E2,
; the rule that actually licensed it.
(must-fail
 (defthm boom (not (wtrig x)) :rule-classes nil))
