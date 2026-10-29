; Phase 6 -- DECRYPT SIDE, part 3b: per-op push-in rules for the decrypt
; chain (mirror of aes_fixslice_cipherops).
;
; For each inverse op:
;   type    :  wstatep(op(S))                    (aes_fixslice_decoptypes)
;   push-in :  inv_bitslice(op(S)) = op-bytes(inv_bitslice(S))  (per lane)
; for ARBITRARY wstatep S -- the push-ins fold the aes_fixslice_invops{,2,3}
; through-packing facts with bitslice-of-inv-bitslice, exactly as the
; forward side does.  inv_shift_rows_2 is the extracted alias of
; shift_rows_2, so its rules reduce to the cipherops sr2 rules by opening
; the wrapper.  (The GL type blasts are in aes_fixslice_decoptypes, on a
; slim include chain -- in this book's heavy session the second blast was
; OOM-killed by the isb blast's BDD residue.)
(in-package "ACL2")
(include-book "aes_fixslice_decipher")
(include-book "aes_fixslice_cipherops")
(include-book "aes_fixslice_invops2")
(include-book "aes_fixslice_invops3")
(include-book "aes_fixslice_decoptypes")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))


;; ---- inv-sub-bytes ----

(defthm inv-bitslice-of-isb
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s))))
                  (list (map-invsbox16 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (map-invsbox16 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (inv-sub-bytes-general aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            map-invsbox16 nth))
           :use (:instance inv-sub-bytes-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ---- inv-mix-columns-0 ----

(defthm inv-bitslice-of-imc0
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s))))
                  (list (imc0-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (imc0-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (inv-mix-columns-0-general aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            imc0-bytes nth))
           :use (:instance inv-mix-columns-0-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ---- inv-mix-columns-1 ----

(defthm inv-bitslice-of-imc1
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s))))
                  (list (imc1-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (imc1-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (inv-mix-columns-1-general aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            imc1-bytes nth))
           :use (:instance inv-mix-columns-1-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ---- inv-mix-columns-2 ----

(defthm inv-bitslice-of-imc2
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s))))
                  (list (imc2-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (imc2-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (inv-mix-columns-2-general aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            imc2-bytes nth))
           :use (:instance inv-mix-columns-2-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ---- inv-mix-columns-3 ----

(defthm inv-bitslice-of-imc3
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s))))
                  (list (imc3-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (imc3-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (inv-mix-columns-3-general aes-fixslice-encrypt-inv-mix-columns-3 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            imc3-bytes nth))
           :use (:instance inv-mix-columns-3-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ---- inv_shift_rows_2 = shift_rows_2 (extracted alias), at fuel 100 ----
(defthm wstatep-of-isr2-w
  (implies (wstatep s)
           (wstatep (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2 wstatep)))))
(defthm inv-bitslice-of-isr2-w
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
                  (list (shift-rows-2-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (shift-rows-2-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2)
                                  (aes-fixslice-encrypt-shift-rows-2 wstatep
                                   aes-fixslice-encrypt-inv-bitslice shift-rows-2-bytes nth)))))
