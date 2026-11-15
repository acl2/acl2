; xcheck-tests.lsp -- randomized cross-validation of OUR connectivity chain
; against THEIRS with ACL2s cgen.  Certify the books in this directory
; first, then run from this directory with
;   ACL2_SYSTEM_BOOKS=<books> <acl2> < xcheck-tests.lsp > xcheck-tests.out
; (the acl2s books cannot be included by a certified book in this fork:
; their certificates are stale, so the test? forms live in this script;
; the certified book xcheck-defs.lisp holds the definitions and the
; deterministic assert-event instances).
;
; Every property is a disabled predicate of xcheck-defs.lisp, so test? can
; only test it (the prover has nothing to expand).  Expected outcome: every
; test? succeeds except prop-b-naive, which exhibits the p = 1 flip
; convention difference (see xcheck-defs.lisp, to-x-move).

(include-book "xcheck-defs")
(include-book "acl2s/defdata/top" :dir :system :ttags :all)
(include-book "acl2s/cgen/top" :dir :system :ttags :all)

(acl2s::acl2s-defaults :set acl2s::num-trials 300)
;; cgen's default per-test timeout is 1/100 s and its per-goal budget 10 s;
;; the properties here run whole connectivity paths (up to ~1 s at n = 3),
;; so the timeouts are disabled and the overall test? budget raised.
(acl2s::acl2s-defaults :set acl2s::cgen-single-test-timeout 0)
(acl2s::acl2s-defaults :set acl2s::cgen-local-timeout 0)
(acl2s::acl2s-defaults :set acl2s::cgen-timeout 7200)
(acl2s::acl2s-defaults :set acl2s::print-cgen-summary t)
(acl2s::acl2s-defaults :set acl2s::num-witnesses 3)
(acl2s::acl2s-defaults :set acl2s::num-counterexamples 3)

(acl2s::defdata seed acl2s::nat)
(acl2s::defdata seed2 (list acl2s::nat acl2s::nat))

;;; How the random inputs are distributed: ranks of the random correct
;;; schemes, and how often the perturbed / random-triple schemes are correct
;;; (so that both branches of the iff in (a) are exercised).

(defun rank-histogram (i n acc)
  (declare (xargs :mode :program))
  (if (zp i) acc
    (rank-histogram (1- i) n
                    (let* ((r (len (rand-scheme (1- i) n)))
                           (e (assoc r acc)))
                      (put-assoc r (1+ (if e (cdr e) 0)) acc)))))
(defun count-correct-perturbed (i n acc)
  (declare (xargs :mode :program))
  (if (zp i) acc
    (count-correct-perturbed (1- i) n
      (if (correct-schemep (perturb (lcg-next (1- i)) (rand-scheme (1- i) n) n) n) (1+ acc) acc))))
(defun count-correct-triples (i n acc)
  (declare (xargs :mode :program))
  (if (zp i) acc
    (count-correct-triples (1- i) n
      (if (correct-schemep (insert-list (rand-triples (1- i) n) nil) n) (1+ acc) acc))))
(defun count-move-kinds (i n acc)
  (declare (xargs :mode :program))
  (if (zp i) acc
    (count-move-kinds (1- i) n
      (let* ((s (1- i)) (m (rand-move (lcg-next s) (rand-scheme s n)))
             (k (and m (list (car m) (cadr m)))) (e (assoc-equal k acc)))
        (put-assoc-equal k (1+ (if e (cdr e) 0)) acc)))))

(rank-histogram 300 2 nil)
(rank-histogram 100 3 nil)
(list :correct-among-300-perturbed-n2 (count-correct-perturbed 300 2 0))
(list :correct-among-300-random-triple-lists-n2 (count-correct-triples 300 2 0))
(list :move-kinds-of-300-random-moves-n2 (count-move-kinds 300 2 nil))

;;; ------------------------------------------------------------------ n = 2

;; (a) correct-schemep vs x-schemep
(acl2s::test? (implies (seedp s) (prop-a-triples-t s 2)))
(acl2s::test? (implies (seedp s) (prop-a-rand-t s 2)))
(acl2s::test? (implies (seedp s) (prop-a-perturbed-t s 2)))

;; (b) moves: validity and application agree
(acl2s::test? (implies (seedp s) (prop-b-t s 2)))
(acl2s::test? (implies (seedp s) (prop-b-conv-t s 2)))
(acl2s::test? (implies (seedp s) (prop-roundtrip-t s 2)))

;; (b) with the naive flip translation: EXPECTED TO FAIL (p = 1 flips)
(acl2s::test? (implies (seedp s) (prop-b-naive-t s 2)))

;; (c) THE MAIN CROSS-CHECK, both directions
(acl2s::test? (implies (seed2p sp) (prop-c-t (car sp) (cadr sp) 2)))
(acl2s::test? (implies (seed2p sp) (prop-c-conv-t (car sp) (cadr sp) 2)))

;;; ------------------------------------------------------------------ n = 3

(acl2s::test? (implies (seedp s) (prop-a-rand-t s 3)))
(acl2s::test? (implies (seedp s) (prop-a-perturbed-t s 3)))
(acl2s::test? (implies (seedp s) (prop-b-t s 3)))
(acl2s::test? (implies (seedp s) (prop-b-conv-t s 3)))
(acl2s::test? (implies (seedp s) (prop-roundtrip-t s 3)))
(acl2s::test? (implies (seed2p sp) (prop-c-t (car sp) (cadr sp) 3)))
(acl2s::test? (implies (seed2p sp) (prop-c-conv-t (car sp) (cadr sp) 3)))
