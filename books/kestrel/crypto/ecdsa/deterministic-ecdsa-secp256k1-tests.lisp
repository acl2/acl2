; Tests of the RFC 6979 Deterministic ECDSA formalization.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "deterministic-ecdsa-secp256k1")
(include-book "deterministic-ecdsa-exposing-k-secp256k1")
(include-book "std/strings/hex" :dir :system)  ; for str::strval16

(include-book "kestrel/utilities/strings/hexstrings" :dir :system) ; for hexstring=>ubyte8s
(include-book "kestrel/utilities/bytes-as-digits" :dir :system) ; for bebytes=>nat


;;; ----------------------------------------------------------------
;;; Test utilities

(defun string=>bits (str)
  (bytes-to-bits (acl2::string=>nats str)))

(defun r-s-string-to-r-s-list (r-s-string)
  (if (and (stringp r-s-string)
           (equal (length r-s-string) 128))
      (list (str::strval16 (subseq r-s-string 0 64))
            (str::strval16 (subseq r-s-string 64 128)))
    nil))

;;; Test the routine that generates (r,s) given k.
(defun test--ecdsa-sign-given-k--sha-256 (testcase)
  ;; testcase is (<private-key> <message> <expected-k> <expected-signature>)
  (b* (((mv error? & & r s)
        ;; an enhancement would be to test the returned x-index and y-even? too
        (ecdsa-sign-given-k (acl2::bytes-to-bits
                             (sha2::sha-256-bytes
                              (acl2::string=>nats (second testcase))))
                            (first testcase)
                            (third testcase)))
       ;; adjust tests now that ECDSA-SIGN-GIVEN-K no longer keeps s < q/2:
       ((mv & & r s) (ecdsa-ensure-s-below-q/2 0 nil r s)))
    (and (eq error? nil)
         (equal (list r s)
                (r-s-string-to-r-s-list (fourth testcase))))))

;;; Test full signature generation
(defun test--ecdsa-sign-deterministic--sha-256 (testcase)
  (b* (((mv error? & & r s)
        ;; an enhancement would be to test the returned x-index and y-even? too
        (ecdsa-sign-deterministic-sha-256
         (string=>bits (second testcase))
         (first testcase)
         t
         t)))
    (and (eq error? nil)
         (equal (list r s)
                (r-s-string-to-r-s-list (fourth testcase))))))

;;; Test full signature generation while also checking k
(defun test--ecdsa-sign-deterministic-exposing-k--sha-256 (testcase)
  (b* (((mv error? & & r s k)
        ;; an enhancement would be to test the returned x-index and y-even? too
        (ecdsa-sign-deterministic-sha-256-exposing-k
         (string=>bits (second testcase))
         (first testcase)
         t)))
    (and (eq error? nil)
         (equal (list r s k)
                (append (r-s-string-to-r-s-list (fourth testcase))
                        (list (third testcase)))))))



;;; ----------------------------------------------------------------
;;; Test cases

;;; --------------------------------
;;; Group 1
;;; Using sha-256 for the message hash.
;;;
;;; This group tests deterministic-ecdsa, but these test cases
;;; are not directly usable for Ethereum, which
;;; hashes the message with keccak-256 before
;;; calling ECDSASIGN.

#||
From
https://bitcointalk.org/index.php?topic=285142.0;all

The first set of test vectors did not take into account the restriction
that s < q/2.

This is the corrected set of test vectors that are suitable for
the additional step of inverting s when s > q/2.

    # Test Vectors for RFC 6979 ECDSA, secp256k1, SHA-256
    # (private key, message, expected k, expected signature)
    test_vectors = [
    ..
    ]

Original content duplicated in below comments, above each test case.
||#

;;; (private key, message, expected k, expected signature)
;;; (0x1, "Satoshi Nakamoto", 0x8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15, "934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d82442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5"),
(defconst *test-1-1*
  (list #x1
        "Satoshi Nakamoto"
        #x8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15
        "934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d82442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5"))

;;; (private key, message, expected k, expected signature)
;;; (0x1, "All those moments will be lost in time, like tears in rain. Time to die...", 0x38AA22D72376B4DBC472E06C3BA403EE0A394DA63FC58D88686C611ABA98D6B3, "8600dbd41e348fe5c9465ab92d23e3db8b98b873beecd930736488696438cb6b547fe64427496db33bf66019dacbf0039c04199abb0122918601db38a72cfc21"),
(defconst *test-1-2*
  (list #x1
        "All those moments will be lost in time, like tears in rain. Time to die..."
        #x38AA22D72376B4DBC472E06C3BA403EE0A394DA63FC58D88686C611ABA98D6B3
        "8600dbd41e348fe5c9465ab92d23e3db8b98b873beecd930736488696438cb6b547fe64427496db33bf66019dacbf0039c04199abb0122918601db38a72cfc21"))

;;; (private key, message, expected k, expected signature)
;;; (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140, "Satoshi Nakamoto", 0x33A19B60E25FB6F4435AF53A3D42D493644827367E6453928554F43E49AA6F90, "fd567d121db66e382991534ada77a6bd3106f0a1098c231e47993447cd6af2d06b39cd0eb1bc8603e159ef5c20a5c8ad685a45b06ce9bebed3f153d10d93bed5"),
(defconst *test-1-3*
  (list #xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140
        "Satoshi Nakamoto"
        #x33A19B60E25FB6F4435AF53A3D42D493644827367E6453928554F43E49AA6F90
        "fd567d121db66e382991534ada77a6bd3106f0a1098c231e47993447cd6af2d06b39cd0eb1bc8603e159ef5c20a5c8ad685a45b06ce9bebed3f153d10d93bed5"))

;;; (private key, message, expected k, expected signature)
;;; (0xf8b8af8ce3c7cca5e300d33939540c10d45ce001b8f252bfbc57ba0342904181, "Alan Turing", 0x525A82B70E67874398067543FD84C83D30C175FDC45FDEEE082FE13B1D7CFDF1, "7063ae83e7f62bbb171798131b4a0564b956930092b33b07b395615d9ec7e15c58dfcc1e00a35e1572f366ffe34ba0fc47db1e7189759b9fb233c5b05ab388ea"),
(defconst *test-1-4*
  (list #xf8b8af8ce3c7cca5e300d33939540c10d45ce001b8f252bfbc57ba0342904181
        "Alan Turing"
        #x525A82B70E67874398067543FD84C83D30C175FDC45FDEEE082FE13B1D7CFDF1
        "7063ae83e7f62bbb171798131b4a0564b956930092b33b07b395615d9ec7e15c58dfcc1e00a35e1572f366ffe34ba0fc47db1e7189759b9fb233c5b05ab388ea"))

;;; (private key, message, expected k, expected signature)
;;; (0xe91671c46231f833a6406ccbea0e3e392c76c167bac1cb013f6f1013980455c2, "There is a computer disease that anybody who works with computers knows about. It's a very serious disease and it interferes completely with the work. The trouble with computers is that you 'play' with them!", 0x1F4B84C23A86A221D233F2521BE018D9318639D5B8BBD6374A8A59232D16AD3D, "b552edd27580141f3b2a5463048cb7cd3e047b97c9f98076c32dbdf85a68718b279fa72dd19bfae05577e06c7c0c1900c371fcd5893f7e1d56a37d30174671f6")
(defconst *test-1-5*
  (list #xe91671c46231f833a6406ccbea0e3e392c76c167bac1cb013f6f1013980455c2
        "There is a computer disease that anybody who works with computers knows about. It's a very serious disease and it interferes completely with the work. The trouble with computers is that you 'play' with them!"
        #x1F4B84C23A86A221D233F2521BE018D9318639D5B8BBD6374A8A59232D16AD3D
        "b552edd27580141f3b2a5463048cb7cd3e047b97c9f98076c32dbdf85a68718b279fa72dd19bfae05577e06c7c0c1900c371fcd5893f7e1d56a37d30174671f6"))


;;; ----------------------------------------------------------------
;;; Run tests

;;; Run tests of the core routine ECDSA-SIGN-GIVEN-K
;;;
(assert-event (test--ecdsa-sign-given-k--sha-256 *test-1-1*))
(assert-event (test--ecdsa-sign-given-k--sha-256 *test-1-2*))
(assert-event (test--ecdsa-sign-given-k--sha-256 *test-1-3*))
(assert-event (test--ecdsa-sign-given-k--sha-256 *test-1-4*))
(assert-event (test--ecdsa-sign-given-k--sha-256 *test-1-5*))

;;; Run tests of the main interface ECDSA-SIGN-DETERMINISTIC
;;;
(assert-event (test--ecdsa-sign-deterministic--sha-256 *test-1-1*))
(assert-event (test--ecdsa-sign-deterministic--sha-256 *test-1-2*))
(assert-event (test--ecdsa-sign-deterministic--sha-256 *test-1-3*))
(assert-event (test--ecdsa-sign-deterministic--sha-256 *test-1-4*))
(assert-event (test--ecdsa-sign-deterministic--sha-256 *test-1-5*))

;;; Run tests of ECDSA-SIGN-DETERMINISTIC-EXPOSING-K
;;; to make sure we generate k correctly.
;;;
(assert-event (test--ecdsa-sign-deterministic-exposing-k--sha-256 *test-1-1*))
(assert-event (test--ecdsa-sign-deterministic-exposing-k--sha-256 *test-1-2*))
(assert-event (test--ecdsa-sign-deterministic-exposing-k--sha-256 *test-1-3*))
(assert-event (test--ecdsa-sign-deterministic-exposing-k--sha-256 *test-1-4*))
(assert-event (test--ecdsa-sign-deterministic-exposing-k--sha-256 *test-1-5*))



;;; --------------------------------
;;; Group 2
;;; Also using sha-256 for the message hash.
;;;
;;; This group tests deterministic-ecdsa, but these test cases
;;; are not directly usable for Ethereum, which
;;; hashes the message with keccak-256 before
;;; calling ECDSASIGN.

#||
From
https://bitcointalk.org/index.php?topic=285142.msg3300992#msg3300992
Submitted by plaprade and double-checked by fpgaminer.

plaprade states:
"The test vectors are fully canonical signatures with S components <= order/2.
They contain both vectors were the S component had to be flipped and not
flipped."

EM: The original content had commas separating items in each tuple.
  I removed those and added the defconst.

"Haskoin test vectors for RFC 6979 ECDSA (secp256k1, SHA-256)"
"(PrvKey HEX, PrvKey WIF, message, R || S as HEX, sig as DER)"

||#

(defconst *haskoin-tests-rfc-6979-ecdsa-secp256k1-sha-256*
  '(
    ( "0000000000000000000000000000000000000000000000000000000000000001"
      "KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn"
      "Everything should be made as simple as possible, but not simpler."
      "33a69cd2065432a30f3d1ce4eb0d59b8ab58c74f27c41a7fdb5696ad4e6108c96f807982866f785d3f6418d24163ddae117b7db4d5fdf0071de069fa54342262"
      "3044022033a69cd2065432a30f3d1ce4eb0d59b8ab58c74f27c41a7fdb5696ad4e6108c902206f807982866f785d3f6418d24163ddae117b7db4d5fdf0071de069fa54342262"
    )
    ( "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140"
      "L5oLkpV3aqBjhki6LmvChTCV6odsp4SXM6FfU2Gppt5kFLaHLuZ9"
      "Equations are more important to me, because politics is for the present, but an equation is something for eternity."
      "54c4a33c6423d689378f160a7ff8b61330444abb58fb470f96ea16d99d4a2fed07082304410efa6b2943111b6a4e0aaa7b7db55a07e9861d1fb3cb1f421044a5"
      "3044022054c4a33c6423d689378f160a7ff8b61330444abb58fb470f96ea16d99d4a2fed022007082304410efa6b2943111b6a4e0aaa7b7db55a07e9861d1fb3cb1f421044a5"
    )
    ( "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140"
      "L5oLkpV3aqBjhki6LmvChTCV6odsp4SXM6FfU2Gppt5kFLaHLuZ9"
      "Not only is the Universe stranger than we think, it is stranger than we can think."
      "ff466a9f1b7b273e2f4c3ffe032eb2e814121ed18ef84665d0f515360dab3dd06fc95f5132e5ecfdc8e5e6e616cc77151455d46ed48f5589b7db7771a332b283"
      "3045022100ff466a9f1b7b273e2f4c3ffe032eb2e814121ed18ef84665d0f515360dab3dd002206fc95f5132e5ecfdc8e5e6e616cc77151455d46ed48f5589b7db7771a332b283"
    )
    ( "0000000000000000000000000000000000000000000000000000000000000001"
      "KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn"
      "How wonderful that we have met with a paradox. Now we have some hope of making progress."
      "c0dafec8251f1d5010289d210232220b03202cba34ec11fec58b3e93a85b91d375afdc06b7d6322a590955bf264e7aaa155847f614d80078a90292fe205064d3"
      "3045022100c0dafec8251f1d5010289d210232220b03202cba34ec11fec58b3e93a85b91d3022075afdc06b7d6322a590955bf264e7aaa155847f614d80078a90292fe205064d3"
    )
    ( "69ec59eaa1f4f2e36b639716b7c30ca86d9a5375c7b38d8918bd9c0ebc80ba64"
      "KzmcSTRmg8Gtoq8jbBCwsrvgiTKRrewQXniAHHTf7hsten8MZmBB"
      "Computer science is no more about computers than astronomy is about telescopes."
      "7186363571d65e084e7f02b0b77c3ec44fb1b257dee26274c38c928986fea45d0de0b38e06807e46bda1f1e293f4f6323e854c86d58abdd00c46c16441085df6"
      "304402207186363571d65e084e7f02b0b77c3ec44fb1b257dee26274c38c928986fea45d02200de0b38e06807e46bda1f1e293f4f6323e854c86d58abdd00c46c16441085df6"
    )
    ( "00000000000000000000000000007246174ab1e92e9149c6e446fe194d072637"
      "KwDiBf89QgGbjEhKnhXJwe1E2mCa8asowBrSKuCaBV6EsPYEAFZ8"
      "...if you aren't, at any given time, scandalized by code you wrote five or even three years ago, you're not learning anywhere near enough"
      "fbfe5076a15860ba8ed00e75e9bd22e05d230f02a936b653eb55b61c99dda4870e68880ebb0050fe4312b1b1eb0899e1b82da89baa5b895f612619edf34cbd37"
      "3045022100fbfe5076a15860ba8ed00e75e9bd22e05d230f02a936b653eb55b61c99dda48702200e68880ebb0050fe4312b1b1eb0899e1b82da89baa5b895f612619edf34cbd37"
    )
    ( "000000000000000000000000000000000000000000056916d0f9b31dc9b637f3"
      "KwDiBf89QgGbjEhKnhXJuH7LrciVrZiib5S9h4knkymNojPUVsWN"
      "The question of whether computers can think is like the question of whether submarines can swim."
      "cde1302d83f8dd835d89aef803c74a119f561fbaef3eb9129e45f30de86abbf906ce643f5049ee1f27890467b77a6a8e11ec4661cc38cd8badf90115fbd03cef"
      "3045022100cde1302d83f8dd835d89aef803c74a119f561fbaef3eb9129e45f30de86abbf9022006ce643f5049ee1f27890467b77a6a8e11ec4661cc38cd8badf90115fbd03cef"
  )
    ))

;; Originally: "(PrvKey HEX, PrvKey WIF, message, R || S as HEX, sig as DER)"
;; We ignore the "PrvKeyWIF HEX" and the "sig as DER".

(defun run-haskoin-testcase (testcase)
  (b* (((mv error? & & r s)
        (ecdsa-sign-deterministic-sha-256
         (string=>bits (third testcase)) ; message
         (acl2::bebytes=>nat (acl2::hexstring=>ubyte8s (first testcase))) ; private key
         t
         t)))
    (and (eq error? nil)
         (equal (list r s)
                (r-s-string-to-r-s-list (fourth testcase))))))

(defun run-haskoin-testcases (testcases)
  (if (null testcases) T
    (and (run-haskoin-testcase (car testcases))
         (run-haskoin-testcases (cdr testcases)))))

(acl2::assert!
 (run-haskoin-testcases *haskoin-tests-rfc-6979-ecdsa-secp256k1-sha-256*))
