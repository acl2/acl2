; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "transactions")

;; Attach the executable pieces needed to assemble and sign transactions.
(include-book "kestrel/crypto/attachments/keccak-256" :dir :system)
(include-book "kestrel/crypto/ecdsa/secp256k1-attachment" :dir :system)

(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test the example in
;; https://github.com/ethereum/EIPs/blob/master/EIPS/eip-155.md
;;
;; "Consider a transaction with nonce = 9, gasprice = 20 * 10**9, startgas = 21000, to = 0x3535353535353535353535353535353535353535, value = 10**18, data='' (empty)."

;; Note, defconst is a macro and doesn't work well with attachments.
;; Hence the make-event.  See :doc acl2::ignored-attachment
(make-event
`(defconst *eip-155-example-transaction*
  ',(mv-let (error? transaction)
      (make-signed-transaction
       9              ; nonce
       (* 20 (expt 10 9)) ; gasprice
       21000              ; startgas
       '(#x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35
              #x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35 #x35) ; to
       (expt 10 18)                                              ; value
       '()                                                       ; data
       1 ; chain ID 1 = mainnet
       #x4646464646464646464646464646464646464646464646464646464646464646 ; private key
       )
    (if error?
        nil
      transaction))))

(assert! (and (equal (transaction->sign-v *eip-155-example-transaction*) 37)
              (equal (transaction->sign-r *eip-155-example-transaction*)
                     #x28EF61340BD939BC2195FE537567866003E1A15D3C71FF63E1590620AA636276)
              (equal (transaction->sign-s *eip-155-example-transaction*)
                     #x67CBE9D8997F761AECB703304B3800CCF555C9F3DC64214B297FB1966A3B6D83)))
