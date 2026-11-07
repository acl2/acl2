; The add-arbitrary lemma of the companion paper (lem:add-arbitrary,
; Lemma 4.6): from any correct scheme sch for n x n matrix multiplication
; over F2 (n >= 2) and any nonzero n x n matrices X, Y, Z, there is a valid
; path from sch to sch plus two copies of X (x) Y (x) Z.
;
; The three legs (A, B, C positions) and the path add-arbitrary-path are
; developed in arbitrary.lisp; this book composes them into the full
; theorem and validates the full path by execution at n = 2.

(in-package "ACL2")

(include-book "arbitrary")

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defrule add-arbitrary
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n)))
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n))))
           (let* ((path (add-arbitrary-path sch x y z n))
                  (s (summand x y z))
                  (sch3 (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal sch3
                         (obag::insert s (obag::insert s sch)))
                  (correct-schemep sch3 n))))
  :do-not-induct t
  :enable (add-arbitrary-path correct-schemep)
  :disable (add-arbitrary-a add-arbitrary-a-path
            arb-path-b arb-path-c
            apply-moves-of-append path-validp-of-append
            delete-pair-result delete-pair-move-validp)
  :use (add-arbitrary-a
        arb-s0-facts
        arb-path-b-step
        arb-path-c-step
        (:instance compose-path-steps
                   (p1 (arb-path-b sch x y n))
                   (p2 (arb-path-c sch x y z n))
                   (sch (obag::insert
                         (summand x
                                  (cadr (find-summand-a-neq sch x))
                                  (caddr (find-summand-a-neq sch x)))
                         (obag::insert
                          (summand x
                                   (cadr (find-summand-a-neq sch x))
                                   (caddr (find-summand-a-neq sch x)))
                          sch)))
                   (sch1 (obag::insert
                          (summand x y (caddr (find-summand-a-neq sch x)))
                          (obag::insert
                           (summand x y (caddr (find-summand-a-neq sch x)))
                           sch)))
                   (sch2 (obag::insert
                          (summand x y z)
                          (obag::insert (summand x y z) sch))))
        (:instance compose-path-steps
                   (p1 (add-arbitrary-a-path sch x n))
                   (p2 (append (arb-path-b sch x y n)
                               (arb-path-c sch x y z n)))
                   (sch sch)
                   (sch1 (obag::insert
                          (summand x
                                   (cadr (find-summand-a-neq sch x))
                                   (caddr (find-summand-a-neq sch x)))
                          (obag::insert
                           (summand x
                                    (cadr (find-summand-a-neq sch x))
                                    (caddr (find-summand-a-neq sch x)))
                           sch)))
                   (sch2 (obag::insert
                          (summand x y z)
                          (obag::insert (summand x y z) sch))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable validation of the full path at n = 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A generic case and a fully degenerate case (x = y = z, so both the B
;;; and C legs may be empty or not depending on the found summand).

(assert-event
 (and (let* ((x '((0 1) (1 0))) (y '((1 1) (1 1))) (z '((1 0) (0 1)))
             (path (add-arbitrary-path *arb-std2* x y z 2))
             (s (summand x y z)))
        (and (path-validp path *arb-std2* 2)
             (equal (apply-moves path *arb-std2* 2)
                    (obag::insert s (obag::insert s *arb-std2*)))))
      (let* ((x '((1 0) (0 0))) (y x) (z x)
             (path (add-arbitrary-path *arb-std2* x y z 2))
             (s (summand x y z)))
        (and (path-validp path *arb-std2* 2)
             (equal (apply-moves path *arb-std2* 2)
                    (obag::insert s (obag::insert s *arb-std2*)))))
      (let* ((x '((1 1) (0 0))) (y '((0 1) (0 0))) (z '((0 0) (1 1)))
             (path (add-arbitrary-path *arb-std2* x y z 2))
             (s (summand x y z)))
        (and (path-validp path *arb-std2* 2)
             (equal (apply-moves path *arb-std2* 2)
                    (obag::insert s (obag::insert s *arb-std2*)))))))
