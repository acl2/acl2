; Phase 4 -- key-schedule CORE SPEC: the byte-level AES key-expansion round
; recurrence kr-spec-bytes (RotWord, SubWord via the inlined S-box table, Rcon,
; the running column XOR), validated against Kestrel's keyexpansion.
;
; The correspondence between the extracted fixslice round and this recurrence
; is proven in aes_fixslice_keystep (step-star-c: GL over the pure window
; transform krw8 for each round constant, lifted to all inputs).
(in-package "ACL2")
(include-book "aes_fixslice_subbytes")

(defund xorw (x y) (list (logxor (nth 0 x)(nth 0 y)) (logxor (nth 1 x)(nth 1 y))
                         (logxor (nth 2 x)(nth 2 y)) (logxor (nth 3 x)(nth 3 y))))
(defund kr-spec-bytes (b rv)
  (b* ((w0 (list (nth 0 b)(nth 1 b)(nth 2 b)(nth 3 b)))
       (w1 (list (nth 4 b)(nth 5 b)(nth 6 b)(nth 7 b)))
       (w2 (list (nth 8 b)(nth 9 b)(nth 10 b)(nth 11 b)))
       (w3 (list (nth 12 b)(nth 13 b)(nth 14 b)(nth 15 b)))
       (rot (list (nth 1 w3)(nth 2 w3)(nth 3 w3)(nth 0 w3)))
       (sub (list (nth (nth 0 rot) *sbox*)(nth (nth 1 rot) *sbox*)
                  (nth (nth 2 rot) *sbox*)(nth (nth 3 rot) *sbox*)))
       (temp (list (logxor (nth 0 sub) rv)(nth 1 sub)(nth 2 sub)(nth 3 sub)))
       (n0 (xorw w0 temp)) (n1 (xorw w1 n0)) (n2 (xorw w2 n1)) (n3 (xorw w3 n2)))
    (append n0 n1 n2 n3)))

;; ---------------------------------------------------------------------------
;; Bridge validation: iterating kr-spec-bytes from the key reproduces Kestrel's
;; keyexpansion round keys (so the fixslice step, once equated to kr-spec-bytes
;; in keystep, computes the spec's key-expansion step).  Concrete check on the
;; FIPS-197 C.1 key; the all-inputs equality of kr-spec-bytes to Kestrel's
;; subword/rotword/rcon recurrence is proven in aes_fixslice_keybridge
;; (kk-iter-is-keyexpansion).
(local
 (progn
   (defun kc-xpow (c) (if (zp c) 1 (aes::xtime (kc-xpow (1- c)))))
   (defun kc-iter (key r)  ; r-th round key by iterating kr-spec-bytes
     (declare (xargs :measure (nfix r)))
     (if (zp r) key (kr-spec-bytes (kc-iter key (1- r)) (kc-xpow (1- r)))))
   (defun kc-kk (w r)
     (append (nth (* 4 r) w) (nth (+ 1 (* 4 r)) w) (nth (+ 2 (* 4 r)) w) (nth (+ 3 (* 4 r)) w)))
   (defconst *kc-key* '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))
   (defconst *kc-w*   (aes::keyexpansion *kc-key* 4))
   (defun kc-all (r)
     (declare (xargs :measure (nfix (- 11 r))))
     (if (or (not (natp r)) (> r 10)) t
       (and (equal (kc-iter *kc-key* r) (kc-kk *kc-w* r)) (kc-all (1+ r)))))
   ;; iterated recurrence == Kestrel keyexpansion, all 11 round keys:
   (assert-event (kc-all 0))))
