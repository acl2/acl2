; Known-answer + collapse-by-expansion regression for the bare
; `loop { ... if k == N { break; } ... }` shape (de-vendoring roadmap item 3:
; the aes128_encrypt round loop).  Validates that
;   * the mid-body break extracts as an early (ok s) return, and
;   * the loop function collapses to its finite op chain by EXPLICIT :expand
;     at the concrete counter values -- the proof pattern the cipher book's
;     enc-collapse uses on the re-rolled round loop.
(in-package "ACL2")
(include-book "loop_break")

;; everything computes: a at k=1,3,5,7 (indices 1,3,1,3), b at k=2,4,6
;; (indices 2,0,2) starting from all-zeros.
(defthm run-known-answer
  (equal (loop-break-run 100 (list 0 0 0 0)) (ok (list 1 2 2 2))))

;; the loop at any fuel > 3 IS the 7-step chain (symbolic state: the error
;; propagation of the b* ok-binders matches the loop's own short-circuiting).
(defthm run-loop0-collapse
  (implies (and (natp n) (< 3 n))
           (equal (loop-break-run-loop0 n s 1)
                  (b* (((ok s1) (loop-break-step-a s 1))
                       ((ok s2) (loop-break-step-b s1 2))
                       ((ok s3) (loop-break-step-a s2 3))
                       ((ok s4) (loop-break-step-b s3 4))
                       ((ok s5) (loop-break-step-a s4 5))
                       ((ok s6) (loop-break-step-b s5 6))
                       ((ok s7) (loop-break-step-a s6 7)))
                    (ok s7))))
  :hints (("Goal" :do-not-induct t
           :expand ((loop-break-run-loop0 n s 1)
                    (:free (m ss) (loop-break-run-loop0 m ss 3))
                    (:free (m ss) (loop-break-run-loop0 m ss 5))
                    (:free (m ss) (loop-break-run-loop0 m ss 7)))
           :in-theory (disable loop-break-step-a loop-break-step-b
                               loop-break-run-loop0))))
