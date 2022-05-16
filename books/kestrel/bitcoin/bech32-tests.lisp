; Bitcoin Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bech32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test Cases

;;;;;;;;;;;;;;;;;;;;

; Test cases from the Examples section of BIP-0173

(assert-event
 (valid-bech32
  "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4"))

(assert-event
 (valid-bech32
  "tb1qw508d6qejxtdg4y5r3zarvary0c5xw7kxpjzsx"))

(assert-event
 (valid-bech32
  "bc1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3qccfmv3"))

(assert-event
 (valid-bech32
  "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7"))

;;;;;;;;;;;;;;;;;;;;

; Test cases from the Appendix of BIP-0173

(assert-event
 (valid-bech32
  "A12UEL5L"))

(assert-event
 (valid-bech32
  "a12uel5l"))

(assert-event
 (valid-bech32
  "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs"))

(assert-event
 (valid-bech32
  "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw"))

(assert-event
 (valid-bech32
  "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j"))

(assert-event
 (valid-bech32
  "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w"))

(assert-event
 (valid-bech32
  "?1ezyfcl"))

;;;;;;;;;;;;;;;;;;;;

; Test cases for invalid Bech32 from the Appendix of BIP-0173

(assert-event
 (not (valid-bech32
       " 1nwldj5"))) ; space is #x20 = 32, out of valid range

(assert-event
 (not (valid-bech32
       (string-append (string (code-char #x7F)) "1axkwrx"))))

(assert-event
 (not (valid-bech32
       (string-append (string (code-char #x80)) "1eym55h"))))

(assert-event
 (not (valid-bech32
       "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx")))

(assert-event
 (not (valid-bech32
       "pzry9x0s0muk")))

(assert-event
 (not (valid-bech32
       "1pzry9x0s0muk")))

(assert-event
 (not (valid-bech32
       "x1b4n0q5v")))

(assert-event
 (not (valid-bech32
       "li1dgmt3")))

(assert-event
 (not (valid-bech32
       "de1lg7wt")))

(assert-event
 (not (valid-bech32
       "A1G7SGD8")))

(assert-event
 (not (valid-bech32
       "10a06t8")))

(assert-event
 (not (valid-bech32
       "1qzzfhee")))

;;;;;;;;;;;;;;;;;;;;

; Valid segwit addresses from the Appendix of BIP-0173

(assert-event
 (valid-bech32
  "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4"))

(assert-event
 (valid-bech32
  "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7"))

(assert-event
 (valid-bech32
  "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx"))

(assert-event
 (valid-bech32
  "BC1SW50QA3JX3S"))

(assert-event
 (valid-bech32
  "bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj"))

(assert-event
 (valid-bech32
  "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy"))

;;;;;;;;;;;;;;;;;;;;

; Invalid segwit addresses from the Appendix of BIP-0173,
; but only those for which the reason is that they are invalid Bech32.
; (The full list should be tested when checking segwit address validity)

(assert-event
 (not (valid-bech32
       "tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty:"))) ; Invalid human-readable part

(assert-event
 (not (valid-bech32
       "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5"))) ; Invalid checksum

; Omitted:
; BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2: Invalid witness version
; bc1rw5uspcuh: Invalid program length
; bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90: Invalid program length
; BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P: Invalid program length for witness version 0 (per BIP141)

(assert-event
 (not (valid-bech32
       "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7"))) ; Mixed case

; Omitted
; bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du: zero padding of more than 4 bits
; tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv: Non-zero padding in 8-to-5 conversion
; bc1gmk9yu: Empty data section

;;;;;;;;;;;;;;;;;;;;

; Test cases from the Test Vectors section of BIP-0350

(assert-event
 (valid-bech32m
  "A1LQFN3A"))

(assert-event
 (valid-bech32m
  "a1lqfn3a"))

(assert-event
 (valid-bech32m
  "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6"))

(assert-event
 (valid-bech32m
  "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx"))

(assert-event
 (valid-bech32m
  "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8"))

(assert-event
 (valid-bech32m
  "split1checkupstagehandshakeupstreamerranterredcaperredlc445v"))

(assert-event
 (valid-bech32m
  "?1v759aa"))

;;;;;;;;;;;;;;;;;;;;

; Invalid test vectors for Bech32, implied by them being valid Bech32m,
; mentioned in Test Vectors section of BIP-0350

(assert-event
 (not (valid-bech32
       "A1LQFN3A")))

(assert-event
 (not (valid-bech32
       "a1lqfn3a")))

(assert-event
 (not (valid-bech32
       "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6")))

(assert-event
 (not (valid-bech32
       "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx")))

(assert-event
 (not (valid-bech32
       "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8")))

(assert-event
 (not (valid-bech32
       "split1checkupstagehandshakeupstreamerranterredcaperredlc445v")))

(assert-event
 (not (valid-bech32
       "?1v759aa")))

;;;;;;;;;;;;;;;;;;;;

; Invalid test vectors for Bech32m from the Test Vectors section of BIP-0350.

(assert-event
 (not (valid-bech32m
       " 1xj0phk"))) ; HRP character out of range

(assert-event
 (not (valid-bech32m
       (string-append (string (code-char #x7F)) "1g6xzxy")))) ; HRP character out of range


(assert-event
 (not (valid-bech32m
       (string-append (string (code-char #x7F)) "1vctc34")))) ; HRP character out of range

(assert-event
 (not (valid-bech32m
       "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4"))) ; overall max length exceeded

(assert-event
 (not (valid-bech32m
       "qyrz8wqd2c9m"))) ; No separator character

(assert-event
 (not (valid-bech32m
       "1qyrz8wqd2c9m"))) ; Empty HRP

(assert-event
 (not (valid-bech32m
       "y1b0jsk6g"))) ; Invalid data character

(assert-event
 (not (valid-bech32m
       "lt1igcx5c0"))) ; Invalid data character

(assert-event
 (not (valid-bech32m
       "in1muywd"))) ; Too short checksum

(assert-event
 (not (valid-bech32m
       "mm1crxm3i"))) ; Invalid character in checksum

(assert-event
 (not (valid-bech32m
       "au1s5cgom"))) ; Invalid character in checksum

(assert-event
 (not (valid-bech32m
       "M1VUXWEZ"))) ; checksum calculated with uppercase form of HRP

(assert-event
 (not (valid-bech32m
       "16plkw9"))) ; empty HRP

(assert-event
 (not (valid-bech32m
       "1p2gdwpf"))) ; empty HRP

;;;;;;;;;;;;;;;;;;;;

; Valid segwit addresses from the Test Vectors section of BIP-0350
; Note that this section contains some Bech32-encoded addresses.

; Each test case is checked with Bech32 and Bech32m,
; one of which must pass and one of which must fail.
; The one that succeeds is listed first.

(assert-event
 (valid-bech32
  "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4"))

(assert-event
 (not (valid-bech32m
       "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4")))

(assert-event
 (valid-bech32
  "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7"))

(assert-event
 (not (valid-bech32m
  "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7")))

(assert-event
 (valid-bech32m
  "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y"))

(assert-event
 (not (valid-bech32
       "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y")))

(assert-event
 (valid-bech32m
  "BC1SW50QGDZ25J"))

(assert-event
 (not (valid-bech32
        "BC1SW50QGDZ25J")))

(assert-event
 (valid-bech32m
  "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs"))

(assert-event
 (not (valid-bech32
       "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs")))

(assert-event
 (valid-bech32
  "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy"))

(assert-event
 (not (valid-bech32m
       "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy")))

(assert-event
 (valid-bech32m
  "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c"))

(assert-event
 (not (valid-bech32
       "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c")))

(assert-event
 (valid-bech32m
  "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0"))

(assert-event
 (not (valid-bech32
       "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0")))

;;;;;;;;;;;;;;;;;;;;

; Invalid segwit addresses from the Test Vectors section of BIP-0350,
; but only those for which the reason is that they are invalid Bech32.
; (The full list should be tested when checking segwit address validity)

; segwit conformance not yet tested
;tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut: Invalid human-readable part

;bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd: Invalid checksum (Bech32 instead of Bech32m)
(assert-event
 (not (valid-bech32m
       "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd")))

;tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf: Invalid checksum (Bech32 instead of Bech32m)
(assert-event
 (not (valid-bech32m
       "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf")))

;BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL: Invalid checksum (Bech32 instead of Bech32m)
(assert-event
 (not (valid-bech32m
       "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL")))

; the invalidity of these is depenedent on the segwith content; segwit conformance not yet tested
;bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh: Invalid checksum (Bech32m instead of Bech32)
;tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47: Invalid checksum (Bech32m instead of Bech32)

;bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4: Invalid character in checksum
(assert-event
 (not (valid-bech32m
       "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4")))

; segwit conformance not yet tested
;BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R: Invalid witness version
;bc1pw5dgrnzv: Invalid program length (1 byte)
;bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav: Invalid program length (41 bytes)
;BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P: Invalid program length for witness version 0 (per BIP141)

;tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq: Mixed case
(assert-event
 (not (valid-bech32m
       "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq")))

; segwit conformance not yet tested
;bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf: zero padding of more than 4 bits
;tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j: Non-zero padding in 8-to-5 conversion

(assert-event
 (not (valid-bech32m
       "bc1gmk9yu")))
