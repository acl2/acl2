; Prove that blake2s-extended matches blake2 when no salt and no personalization
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "blake2s-extended")
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

;(local (in-theory (disable ceiling len)))

(local
 (encapsulate ()
   (local (include-book "kestrel/bv/rules3" :dir :system)) ;todo: reduce
   (defthm xor-lemma
     (implies (and (posp nn)
                   (<= nn 32))
              (equal (bvxor 32 16842752 nn)
                     (acl2::bvcat 16 257 16 (bvchop 8 nn)))))

   (defthm xor-lemma2
     (implies (and (posp nn)
                   (<= nn 32)
                   (<= (len key-bytes) 32))
              (equal (BVXOR 32 1779033703
                            (ACL2::BVCAT 16 257 16
                                         (ACL2::BVCAT 8 (LEN KEY-BYTES) 8 NN)))
                     (BVXOR 32 1795745383
                            (BVXOR 32 NN
                                   (ACL2::BVCAT 24 (LEN KEY-BYTES) 8 0)))))
     :hints (("Goal" :in-theory (enable ACL2::GETBIT-TOO-HIGH))))))

;; Shows that blake2s-extended, when called with no salt or personalization, is
;; identical to blake2s.
(defthmd blake2s-extended-when-no-salt-or-personalization
  (implies (and (posp nn)
                (<= nn 32)
                (<= (len key-bytes) 32))
           (equal (blake2s-extended data-bytes
                                    key-bytes
                                    nil
                                    nil
                                    nn)
                  (blake2s data-bytes key-bytes nn)))
  :hints (("Goal" :in-theory (enable blake2s-extended
                                     blake2s-extended-main
                                     parameter-block
                                     bytes-to-words
                                     bytes-to-word
                                     wordp
                                     wordxor
                                     xor-words
                                     acl2::bvshl
                                     blake2s
                                     blake2s-main))))

;; Shows that blake2s-extended, when called with zeros for the salt and
;; personalization, is identical to blake2s.
(defthmd blake2s-extended-when-zero-salt-and-personalization
  (implies (and (posp nn)
                (<= nn 32)
                (<= (len key-bytes) 32))
           (equal (blake2s-extended data-bytes
                                    key-bytes
                                    (repeat 8 0)
                                    (repeat 8 0)
                                    nn)
                  (blake2s data-bytes key-bytes nn)))
  :hints (("Goal" :in-theory (enable blake2s-extended
                                     blake2s-extended-main
                                     parameter-block
                                     bytes-to-words
                                     bytes-to-word
                                     wordp
                                     wordxor
                                     xor-words
                                     acl2::bvshl
                                     blake2s
                                     blake2s-main))))
