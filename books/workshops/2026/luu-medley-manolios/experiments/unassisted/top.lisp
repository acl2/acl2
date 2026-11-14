; top.lisp -- Everything in one book.
;
; ACL2 formalization of
;   "GPU-Accelerated Search for Fast Matrix Multiplication over F_2"
;   (ALENEX 2027).
;
; See README.md for the map from the paper to the books.

(in-package "ACL2")

(include-book "bitvec")            ; F_2 vectors
(include-book "outer")             ; rank-one tensors
(include-book "mmt")               ; M^(n), Lemma 4.1 (coordinate formula)
(include-book "mmt-def")           ; Definition 2.1 (existence and uniqueness)
(include-book "scheme")            ; Definitions 2.2, 2.3; moves preserve schemes
(include-book "span")              ; Lemma 4.2
(include-book "add-dup")           ; Observation 4.1, Lemma 4.3
(include-book "add-arbitrary")     ; Lemma 4.4
(include-book "zero-subset")       ; Lemma 4.5
(include-book "connectivity")      ; Theorem 4.1
(include-book "genflip")           ; Section 5.2, subset form of generalized flips
(include-book "genflip-basis")     ; Section 5.2, invertible-G form
(include-book "search-step")       ; Appendix C and __match_any_sync
(include-book "rank245")           ; Appendix A, the rank-245 scheme
(include-book "optimal-genflip")   ; Appendix B, parts 1-3
(include-book "optimal-genflip-final") ; Appendix B, Theorem B.1

;; Appendix A + Theorem 4.1: the rank-245 scheme is reachable from the
;; naive rank-343 scheme by flip and plus moves alone.
(defthm rank245-reachable-from-naive
  (and (path-ok-p (sq 7) (connect-path 7 (naive-scheme 7) *rank245-scheme*) (naive-scheme 7))
       (perm (apply-path (sq 7) (connect-path 7 (naive-scheme 7) *rank245-scheme*) (naive-scheme 7))
             *rank245-scheme*))
  ;; Pure instantiation: use a minimal theory so that ACL2 does not try to
  ;; evaluate connect-path on the concrete 343-term scheme.
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '((:executable-counterpart posp)
                                               (:executable-counterpart <)
                                               (:executable-counterpart not)))
                  :use ((:instance flip-graph-strongly-connected (n 7) (S (naive-scheme 7))
                                   (S2 *rank245-scheme*))
                        (:instance schemep-of-naive-scheme (n 7))
                        rank245-is-a-scheme))))
