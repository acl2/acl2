; Semantic-preservation check for the vendored RustCrypto AES fixslice round
; core (aes_fixslice_core.lisp, extracted from the SHIPPED crate). The golden
; outputs were produced by RUNNING the vendored Rust on a fixed input; these
; assert-events confirm the extracted ACL2 computes bit-identically.
(in-package "ACL2")
(include-book "aes_fixslice_core")

;; the 113-gate bitsliced S-box, on a fixed bitsliced state
(assert-event
 (equal (aes-fixslice-core-just-sub-bytes
          (list #x00112233 #x44556677 #x8899aabb #xccddeeff
                #x0f0e0d0c #x0b0a0908 #x07060504 #x03020100))
        (ok (list #x8797a7b7 #x03020100 #xc7d7e7f7 #x8f8e8d8c
                  #x8495a6b7 #x03020100 #x07060504 #x8f8e8d8c))))

;; a full fixsliced round: sub_bytes ; mix_columns_1 ; add_round_key
;; (fuel 20 covers add_round_key's 8-iteration for-loop)
(assert-event
 (equal (aes-fixslice-core-aes-round 20
          (list #x00112233 #x44556677 #x8899aabb #xccddeeff
                #x0f0e0d0c #x0b0a0908 #x07060504 #x03020100)
          (list #x11111111 #x22222222 #x33333333 #x44444444
                #x55555555 #x66666666 #x77777777 #x88888888))
        (ok (list #x74787c70 #xfcfdfeff #xece0e4e8 #x13121110
                  #x8495a6b7 #x17161514 #x3d20170a #x4f526578))))
