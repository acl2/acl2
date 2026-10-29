; Phase 6 -- DECRYPT SIDE, part 3a: wstatep closure for the inverse ops
; (8 u32 words in -> 8 u32 words out).
;
; This book lives on the SLIMMEST possible include chain
; (aes_fixslice_round = the generated book + wstatep + GL) because the
; inv_sub_bytes circuit blast leaves several GB of BDD/memo residue: in the
; full decipherops session (invops + invops2 + invops3 + cipherops +
; decipher all loaded) the next GL event after it went over the cgroup
; memory limit and was OOM-killed -- and hons-clear + clear-memoize-tables
; did not save it, since SBCL never returns the pages.  So:
;   - the four inv_mix_columns closures are proved by plain REWRITING
;     (the bodies are linear: xor / rotate / mask), from tiny local GL
;     type rules for u32-xor and the six rotate-rows wrappers (32/64-var
;     blasts, milliseconds each);
;   - only inv_sub_bytes, a genuine 256-var circuit, gets a big GL blast,
;     placed LAST so its memory peak is the session's final act.
; The derived (non-GL) push-in rules are in aes_fixslice_decipherops,
; which includes this book.
(in-package "ACL2")
(include-book "aes_fixslice_round")

;; ---- local GL type rules: u32-xor and the rotate-rows wrappers ----

(local (gl::def-gl-thm ubp32-of-u32-xor
  :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
  :concl (unsigned-byte-p 32 (u32-xor x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32)))))

(local (gl::def-gl-thm rr1-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-1 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-1 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))
(local (gl::def-gl-thm rr2-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-2 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-2 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))
(local (gl::def-gl-thm rc11-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-and-columns-1-1 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-and-columns-1-1 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))
(local (gl::def-gl-thm rc12-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-and-columns-1-2 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-and-columns-1-2 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))
(local (gl::def-gl-thm rc13-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-and-columns-1-3 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-and-columns-1-3 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))
(local (gl::def-gl-thm rc22-type-gl
  :hyp (unsigned-byte-p 32 x)
  :concl (and (equal (result-kind (aes-fixslice-encrypt-rotate-rows-and-columns-2-2 x)) :ok)
              (unsigned-byte-p 32 (result-ok->val (aes-fixslice-encrypt-rotate-rows-and-columns-2-2 x))))
  :g-bindings (gl::auto-bindings (:nat x 32))))

;; ---- inv-mix-columns 0..3: plain rewriting over the opened bodies ----

(defthm wstatep-of-imc0
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s))))
  :hints (("Goal" :in-theory (e/d (wstatep)
                                  (u32-xor
                                   aes-fixslice-encrypt-rotate-rows-1
                                   aes-fixslice-encrypt-rotate-rows-2
                                   unsigned-byte-p)))))
(defthm wstatep-of-imc1
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s))))
  :hints (("Goal" :in-theory (e/d (wstatep)
                                  (u32-xor
                                   aes-fixslice-encrypt-rotate-rows-and-columns-1-1
                                   aes-fixslice-encrypt-rotate-rows-and-columns-2-2
                                   unsigned-byte-p)))))
(defthm wstatep-of-imc2
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s))))
  :hints (("Goal" :in-theory (e/d (wstatep)
                                  (u32-xor
                                   aes-fixslice-encrypt-rotate-rows-2
                                   aes-fixslice-encrypt-rotate-rows-and-columns-1-2
                                   unsigned-byte-p)))))
(defthm wstatep-of-imc3
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s))))
  :hints (("Goal" :in-theory (e/d (wstatep)
                                  (u32-xor
                                   aes-fixslice-encrypt-rotate-rows-and-columns-1-3
                                   aes-fixslice-encrypt-rotate-rows-and-columns-2-2
                                   unsigned-byte-p)))))

;; ---- inv-sub-bytes: the one genuine circuit blast, last ----

(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

(local (gl::def-gl-thm wstatep-of-isb-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32))))
(defthm wstatep-of-isb
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-isb-gl aes-fixslice-encrypt-inv-sub-bytes nth))
           :use (:instance wstatep-of-isb-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
