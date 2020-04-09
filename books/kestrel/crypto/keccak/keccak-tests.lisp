; Keccak Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KECCAK")


;; ================================
;; Testing keccak
;; ================================


;; --------------------------------
;; include-book statements

(include-book "keccak")

; Leave this include-book here just in case it gets taken out of the spec.
(include-book "std/testing/assert-equal" :dir :system)

;; for parsing strings of space-separated byte values
(include-book "std/strings/strsplit" :dir :system)

(include-book "std/lists/flatten" :dir :system)

(include-book "std/strings/hex" :dir :system)


;; --------------------------------
;; Converting an ACL2 string to an equivalent list of bits for
;; the purpose of testing keccak/sha-3.
;; We represent the spec's "strings of bits" as lists of bits.

(defun string-to-bits-little (str)
  (bytes-to-bits-little (string=>nats str)))


;; --------------------------------
;; Utilities for parsing test results

;; The test result oracles give us a sequence of hex byte values,
;; with or without whitespace.
;; To make it easy to compare hash outputs, let's parse strings
;; of hex byte values into lists of byte values.

;; A hexstring is a string of length 2 that is the hex representation
;; of a byte.

(defun hexstring-to-num (hexstring)
  (if (not (= (length hexstring) 2))
      nil
    (let ((nibble0 (str::hex-digit-val (char hexstring 0)))
          (nibble1 (str::hex-digit-val (char hexstring 1))))
      (if (or (null nibble0) (null nibble1))
          nil
        (+ (* nibble0 16)
           nibble1)))))

(defun map-hexstring-to-num (x)
  (if (atom x)
      nil
    (cons (hexstring-to-num (car x))
          (map-hexstring-to-num (cdr x)))))

;; Example: " 6B 0E " ==> (107 14)
;; Extra spaces are ignored.
(defun hexes-string-to-list (str)
  (let ((hex-value-strings (str::strsplit str #\Space )))
    (map-hexstring-to-num hex-value-strings)))


;; ----------------------------
;; Test cases for sha3 / keccak

;; For sha3, there are 6 bitstrings each given as input
;; to each of the sha3 variants on the site
;;    http://csrc.nist.gov/groups/ST/toolkit/examples.html#aHashing :
;; The bitstrings are:
;; 1. "" (0 bits)
;; 2. " 1 1 0 0 1 " (5 bits)
;; 3. " 1 1 0 0 1 0 1 0 0 0 0 1 1 0 1 0 1 1 0 1 1 1 1 0 1 0 0 1 1 0 " (30 bits)
;; 4. " 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 "*50)
;;   (i.e., 50 appended copies of that bit string for a total of 1600 bits)
;; 5. " 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 "*50
;;      1 1 0 0 0"
;;   (i.e., "1 1 0 0 0" appended to the previous case for a total of 1605 bits)
;; 6. " 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 "*50
;;      1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 "
;;   (i.e., 2 bits short of 51 copies of that bit string for a total of 1630 bits)
;; In addition, we will run test case #1 (the empty string input)
;; and test case #4 (200 repetitions of #xA3)
;; (we have to use the "checksum" tool and upload a file,
;; not the "hash" tool where you yank in a text string)
;; and one more test case on the site
;;   http://emn178.github.io/online-tools/
;;   (for author info and other test cases, see https://www.npmjs.com/package/js-sha3):
;; 7. "testing"

(defconst *k-test-input-1* '())
(defconst *k-test-input-1-string* "")

(defconst *k-test-input-2* '( 1 1 0 0 1 ))
(defconst *k-test-input-3* '( 1 1 0 0 1 0 1 0 0 0 0 1 1 0 1 0 1 1 0 1 1 1 1 0 1 0 0 1 1 0 ))
(defconst *k-test-input-4* (flatten (repeat 50
  '( 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 ))))
(defconst *k-test-input-5* (append *k-test-input-4* '( 1 1 0 0 0 )))
(defconst *k-test-input-6* (append *k-test-input-4*
  '( 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0 1 )))

(defconst *k-test-input-7-string* "testing")
(defconst *k-test-input-7* (string-to-bits-little *k-test-input-7-string*))


;; -----------
;; theta tests

;; There are no tests in the spec for theta.
;; Here is a hand-checked test.
(assert-equal (k-theta 2 '(1 0 2 1 0 1 3 0 1 2 0 1 1 3 3 0 0 1 2 2 1 1 1 0 0 ))
              '(1 1 0 1 3 1 2 2 1 1 0 0 3  3 0 0 1 3 2 1 1 0 3 0 3 ))


;; -----------
;; rho tests

;; There is not much in the spec to test rho.
;; One could add tests for the two examples given for the b=200 diagram.


;; --------
;; Test: make sure the 24 standard RC values for w=64 match the literature.

(defconst *k-RC-64-values*
  (list (K-RC 64 0) (K-RC 64 1) (K-RC 64 2) (K-RC 64 3)
        (K-RC 64 4) (K-RC 64 5) (K-RC 64 6) (K-RC 64 7)
        (K-RC 64 8) (K-RC 64 9) (K-RC 64 10) (K-RC 64 11)
        (K-RC 64 12) (K-RC 64 13) (K-RC 64 14) (K-RC 64 15)
        (K-RC 64 16) (K-RC 64 17) (K-RC 64 18) (K-RC 64 19)
        (K-RC 64 20) (K-RC 64 21) (K-RC 64 22) (K-RC 64 23)))

;; These are grabbed out of
;;   ethereumj-core/src/main/java/org/ethereum/crypto/cryptohash/KeccakCore.java
;; and massaged to fit lisp syntax.
(defconst *keccakcore-java-rc-constants*
  (list #x0000000000000001 #x0000000000008082
        #x800000000000808A #x8000000080008000
        #x000000000000808B #x0000000080000001
        #x8000000080008081 #x8000000000008009
        #x000000000000008A #x0000000000000088
        #x0000000080008009 #x000000008000000A
        #x000000008000808B #x800000000000008B
        #x8000000000008089 #x8000000000008003
        #x8000000000008002 #x8000000000000080
        #x000000000000800A #x800000008000000A
        #x8000000080008081 #x8000000000008080
        #x0000000080000001 #x8000000080008008))

(assert-equal *k-RC-64-values* *keccakcore-java-rc-constants*)

;; Note on the above test: we have also checked these constants against
;; Table 1 in the keccak.team spec summary:
;; https://keccak.team/keccak_specs_summary.html#roundConstants


;; ----------------
;; keccak-xxx tests

;; For keccak, we only use
;;   http://emn178.git hub.io/online-tools/.
;; However, that tool does not handle inputs that are not a multiple of 8 bits.
;; So for test cases 1, 4, 7 we have independent results;
;; for test cases 2, 3, 5 and 6 we use our own results as regression tests.
;; Number 1 is the empty string.
;; Number 4 is 200 repetitions of #xA3 (we have to use the "checksum" tool and
;; upload a file, not the "hash" tool where you yank in a text string)
;; Number 7 is "testing"
;; Let's add one item that exceeds 1600 bits.
;; 8. "(defun setbit (width n val bv) (declare (type (integer 0 *) n) (type (integer 0 *) width) (type integer bv) (type integer val) (xargs :guard (< n width))) (setbits width n n val bv)) (defthm unsigned-byte-p-of-setbit (equal (unsigned-byte-p width (setbit width n val bv)) (natp width)))"  (2288 bits).

(defconst *k-test-input-8-string* "(defun setbit (width n val bv) (declare (type (integer 0 *) n) (type (integer 0 *) width) (type integer bv) (type integer val) (xargs :guard (< n width))) (setbits width n n val bv)) (defthm unsigned-byte-p-of-setbit (equal (unsigned-byte-p width (setbit width n val bv)) (natp width)))")
(defconst *k-test-input-8* (string-to-bits-little *k-test-input-8-string*))


;; keccak-224
;; ----------
;; results from the external site mentioned:
;; 1. f71837502ba8e10837bdd8d365adb85591895602fc552b48b7390abd
;; 4. 42cc3f045bb950fcee6cba87ac0880296a1133936d620549901adbb7
;; 7. 7b77b0b01d9b669ec7637ae75fd2f0ce234c8c8c835723b6715f4b59
;; 8. a9c19f886273c1dd74459267a96aed6d038ffcfe1d7aedba5970fba9
;; The other results are what we got when we ran it, and are here for regression testing.

(defconst *k-test-224-result-1*
  (hexes-string-to-list
   "f7 18 37 50 2b a8 e1 08 37 bd d8 d3 65 ad b8 55 91 89 56 02 fc 55 2b 48 b7 39 0a bd"))
(defconst *k-test-224-result-2*
  (hexes-string-to-list
   "A4 7E BC B4 F7 B1 F6 FF 7B F8 BE 4F FC 8F A4 01 39 1F DD 9F B1 1C B1 EF 04 18 A9 B0"))
(defconst *k-test-224-result-3*
  (hexes-string-to-list
   "D2 C6 95 1E EC 96 99 42 B5 D4 06 C2 59 72 03 45 BC 8E 60 9A E8 76 6D 34 F2 A0 EE EF"))
(defconst *k-test-224-result-4*
  (hexes-string-to-list
   "42 cc 3f 04 5b b9 50 fc ee 6c ba 87 ac 08 80 29 6a 11 33 93 6d 62 05 49 90 1a db b7"))
(defconst *k-test-224-result-5*
  (hexes-string-to-list
   "6A 2E 5D D4 D7 D9 B7 84 A1 A8 0C 7F 2E EE B2 87 19 75 19 06 10 6A 9B 23 03 4B 59 91"))
(defconst *k-test-224-result-6*
  (hexes-string-to-list
   "DD D5 79 2B E2 68 D5 21 AD CB 79 F3 91 3D E4 19 5E EF E6 34 8F 02 B4 51 1A 02 83 00"))
(defconst *k-test-224-result-7*
  (hexes-string-to-list
   "7b 77 b0 b0 1d 9b 66 9e c7 63 7a e7 5f d2 f0 ce 23 4c 8c 8c 83 57 23 b6 71 5f 4b 59"))
(defconst *k-test-224-result-8*
  (hexes-string-to-list
   "a9 c1 9f 88 62 73 c1 dd 74 45 92 67 a9 6a ed 6d 03 8f fc fe 1d 7a ed ba 59 70 fb a9"))

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-1*))
 *k-test-224-result-1*)
(assert-equal
 (keccak-224-bytes *k-test-input-1*)
 *k-test-224-result-1*)
(assert-equal
 (keccak-224-string-to-bytes *k-test-input-1-string*)
 *k-test-224-result-1*)

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-2*))
 *k-test-224-result-2*)
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-3*))
 *k-test-224-result-3*)

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-4*))
 *k-test-224-result-4*)
(assert-equal
 (keccak-224-bytes (bits-to-bytes-little *k-test-input-4*))
 *k-test-224-result-4*)

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-5*))
 *k-test-224-result-5*)
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-6*))
 *k-test-224-result-6*)

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-7*))
 *k-test-224-result-7*)
(assert-equal
 (keccak-224-bytes (bits-to-bytes-little *k-test-input-7*))
 *k-test-224-result-7*)

;; test input 8 is 2288 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-224 *k-test-input-8*))
 *k-test-224-result-8*)
(assert-equal
 (keccak-224-bytes (bits-to-bytes-little *k-test-input-8*))
 *k-test-224-result-8*)



;; keccak-256
;; --------
;; results from the external site mentioned:
;; 1. c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
;; 4. 3a57666b048777f2c953dc4456f45a2588e1cb6f2da760122d530ac2ce607d4a
;; 7. 5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02
;; 8. e1d6df0db23d1fc6c92ef0da79e5970eb8ef7f99e4a23d716cc26ed0b89a5598
;; The other results are what we got when we ran it, and are here for regression testing.

(defconst *k-test-256-result-1*
  (hexes-string-to-list
   "c5 d2 46 01 86 f7 23 3c 92 7e 7d b2 dc c7 03 c0 e5 00 b6 53 ca 82 27 3b 7b fa d8 04 5d 85 a4 70"))
(defconst *k-test-256-result-2*
  (hexes-string-to-list
   "FF 0E 29 4F 7C 9E B0 E3 D9 C6 03 52 18 57 BF CA E9 82 BE C1 31 C5 E1 9E 51 00 44 EA FB 1D 1E AD"))
(defconst *k-test-256-result-3*
  (hexes-string-to-list
   "E2 3C D9 08 2A 62 39 20 8A AE 8F 41 03 F2 31 0F 13 6F 96 A4 44 DE 5A CE 34 B1 7A 75 4D 6D 9F BF"))
(defconst *k-test-256-result-4*
  (hexes-string-to-list
   "3a 57 66 6b 04 87 77 f2 c9 53 dc 44 56 f4 5a 25 88 e1 cb 6f 2d a7 60 12 2d 53 0a c2 ce 60 7d 4a"))
(defconst *k-test-256-result-5*
  (hexes-string-to-list
   "4C 35 7A AC 43 EC A3 D5 AD F1 82 50 91 9C 11 81 6B D2 4C 00 95 54 62 AB E0 43 06 28 76 BF 19 59"))
(defconst *k-test-256-result-6*
  (hexes-string-to-list
   "3B D5 1A EE 81 7E AA F4 2C 9A AA 6F 41 FF 54 2C 04 B8 48 B2 DA 50 44 76 52 FF A6 FB 09 64 D9 9E"))
(defconst *k-test-256-result-7*
  (hexes-string-to-list
   "5f 16 f4 c7 f1 49 ac 4f 95 10 d9 cf 8c f3 84 03 8a d3 48 b3 bc dc 01 91 5f 95 de 12 df 9d 1b 02"))
(defconst *k-test-256-result-8*
  (hexes-string-to-list
   "e1 d6 df 0d b2 3d 1f c6 c9 2e f0 da 79 e5 97 0e b8 ef 7f 99 e4 a2 3d 71 6c c2 6e d0 b8 9a 55 98"))

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-1*))
 *k-test-256-result-1*)
(assert-equal
 (keccak-256-bytes *k-test-input-1*)
 *k-test-256-result-1*)
(assert-equal
 (keccak-256-string-to-bytes *k-test-input-1-string*)
 *k-test-256-result-1*)

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-2*))
 *k-test-256-result-2*)
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-3*))
 *k-test-256-result-3*)

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-4*))
 *k-test-256-result-4*)
(assert-equal
 (keccak-256-bytes (bits-to-bytes-little *k-test-input-4*))
 *k-test-256-result-4*)

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-5*))
 *k-test-256-result-5*)
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-6*))
 *k-test-256-result-6*)

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-7*))
 *k-test-256-result-7*)
(assert-equal
 (keccak-256-bytes (bits-to-bytes-little *k-test-input-7*))
 *k-test-256-result-7*)

;; test input 8 is 2288 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-256 *k-test-input-8*))
 *k-test-256-result-8*)
(assert-equal
 (keccak-256-bytes (bits-to-bytes-little *k-test-input-8*))
 *k-test-256-result-8*)


;; keccak-384
;; ---------
;; results from the external site mentioned:
;; 1. 2c23146a63a29acf99e73b88f8c24eaa7dc60aa771780ccc006afbfa8fe2479b2dd2b21362337441ac12b515911957ff
;; 4. 94026c78412d4739a463ec02ef157216ba9001e18d870c3575d69f17c77b21646e8dbc4e6436d207cec1785159bb7897
;; 7. 1020b1c91956efe79b89c387b54de4f7a9c187c3970552f9f48c0da176f6326b7aa694795d2c9adcf2bdd20aec605588
;; 8. 6ce5624807fbf971695e62e613e3ba380be996151b553fc217ec0c8fef4a23632f3f63846297289be7f8b1d7e528da4f
;; The other results are what we got when we ran it, and are here for regression testing.

(defconst *k-test-384-result-1*
 (hexes-string-to-list
  "2c 23 14 6a 63 a2 9a cf 99 e7 3b 88 f8 c2 4e aa 7d c6 0a a7 71 78 0c cc 00 6a fb fa 8f e2 47 9b 2d d2 b2 13 62 33 74 41 ac 12 b5 15 91 19 57 ff"))

(defconst *k-test-384-result-2*
 (hexes-string-to-list
  "F6 3C 26 49 9F C1 89 4E 14 87 07 19 23 85 F5 5D D4 78 F3 52 E9 85 44 95 8F CA EF A5 0F 63 2C FB F2 91 34 58 08 DA 4D 9B 40 5B 6E C5 C9 75 69 72"))

(defconst *k-test-384-result-3*
 (hexes-string-to-list
  "5A 94 EC 2C 9D C7 D4 95 A1 A2 C2 27 72 5A 18 6E 14 08 3C 2C E1 4A 7A 9B BA 82 70 36 49 17 27 14 CD ED 21 6D EF AA 58 FE 01 B2 E7 0C E7 E1 2C 61"))

(defconst *k-test-384-result-4*
 (hexes-string-to-list
  "94 02 6c 78 41 2d 47 39 a4 63 ec 02 ef 15 72 16 ba 90 01 e1 8d 87 0c 35 75 d6 9f 17 c7 7b 21 64 6e 8d bc 4e 64 36 d2 07 ce c1 78 51 59 bb 78 97"))

(defconst *k-test-384-result-5*
 (hexes-string-to-list
  "8B E4 A4 41 4F 4C BA C2 9F 04 65 E8 AD AF 75 59 3E F3 F5 48 8A EF 4F 62 CD 50 20 B9 A5 96 E1 BE 9E C7 9C FE 62 F4 06 9A 4B 63 25 17 09 45 AB 5F"))

(defconst *k-test-384-result-6*
 (hexes-string-to-list
  "34 1D E5 2B E5 F3 E9 95 FA 54 66 E2 32 30 D6 29 BE 16 EB C1 81 E6 5B E7 FD 25 58 1F 2F 06 54 D8 CE 5A 65 C0 74 F0 D9 48 09 94 8D 1E 7D 5D F4 90"))

(defconst *k-test-384-result-7*
 (hexes-string-to-list
  "10 20 b1 c9 19 56 ef e7 9b 89 c3 87 b5 4d e4 f7 a9 c1 87 c3 97 05 52 f9 f4 8c 0d a1 76 f6 32 6b 7a a6 94 79 5d 2c 9a dc f2 bd d2 0a ec 60 55 88"))

(defconst *k-test-384-result-8*
 (hexes-string-to-list
  "6c e5 62 48 07 fb f9 71 69 5e 62 e6 13 e3 ba 38 0b e9 96 15 1b 55 3f c2 17 ec 0c 8f ef 4a 23 63 2f 3f 63 84 62 97 28 9b e7 f8 b1 d7 e5 28 da 4f"))

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-1*))
 *k-test-384-result-1*)
(assert-equal
 (keccak-384-bytes *k-test-input-1*)
 *k-test-384-result-1*)
(assert-equal
 (keccak-384-string-to-bytes *k-test-input-1-string*)
 *k-test-384-result-1*)

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-2*))
 *k-test-384-result-2*)
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-3*))
 *k-test-384-result-3*)

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-4*))
 *k-test-384-result-4*)
(assert-equal
 (keccak-384-bytes (bits-to-bytes-little *k-test-input-4*))
 *k-test-384-result-4*)

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-5*))
 *k-test-384-result-5*)
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-6*))
 *k-test-384-result-6*)

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-7*))
 *k-test-384-result-7*)
(assert-equal
 (keccak-384-bytes (bits-to-bytes-little *k-test-input-7*))
 *k-test-384-result-7*)

;; test input 8 is 2288 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-384 *k-test-input-8*))
 *k-test-384-result-8*)
(assert-equal
 (keccak-384-bytes (bits-to-bytes-little *k-test-input-8*))
 *k-test-384-result-8*)


;; keccak-512
;; --------
;; results from the external site mentioned:
;; 1. 0eab42de4c3ceb9235fc91acffe746b29c29a8c366b7c60e4e67c466f36a4304c00fa9caf9d87976ba469bcbe06713b435f091ef2769fb160cdab33d3670680e
;; 4. f4f846d140847539f53c3f082cc4e6810e143a5b4fc62a20597b5d76043246b86bd7149b906140bb9665a6ce83d991f032f2291d2fae80eedfc6f845cc16d5ae
;; 7. 9558a7ba9ac74b33b347703ffe33f8d561d86d9fcad1cfd63225fb55dfea50a0953a0efafd6072377f4c396e806d5bda0294cba28762740d8446fee45a276e4a
;; 8. 656c09573cfd6d17bf0048702c0eedbec30e8d3cfd2077c7df9ba973592d75c3b5658c3e1943b328badc5ffe2fe1c51754a56259e117b1afad5a2a9e3f503ea1
;; The other results are what we got when we ran it, and are here for regression testing.

(defconst *k-test-512-result-1*
 (hexes-string-to-list
  "0e ab 42 de 4c 3c eb 92 35 fc 91 ac ff e7 46 b2 9c 29 a8 c3 66 b7 c6 0e 4e 67 c4 66 f3 6a 43 04 c0 0f a9 ca f9 d8 79 76 ba 46 9b cb e0 67 13 b4 35 f0 91 ef 27 69 fb 16 0c da b3 3d 36 70 68 0e"))

(defconst *k-test-512-result-2*
 (hexes-string-to-list
  "63 1B 34 13 63 89 C7 FD 28 5A 4F 50 E2 0A 95 8E F1 8A 53 D3 57 64 81 7E 11 D3 75 FF 2D C3 2C 0F FD 6E 19 DA 7D 2B 86 B3 DD F4 61 D4 4F 88 46 6C CB FD E8 41 89 60 9C 18 03 8E ED DC 69 16 F6 C4"))

(defconst *k-test-512-result-3*
 (hexes-string-to-list
  "E8 73 13 5D 6C 24 BA 7A 55 82 B6 E4 19 78 B7 E9 38 B5 A5 1E 17 61 9F 21 C7 29 90 D3 47 47 A9 23 B1 98 37 3A 63 C6 B4 59 7D 3E E5 A9 29 1C 8B BB 6F 9B D6 5E 01 F1 8F A9 00 30 42 E5 85 97 D5 CA"))

(defconst *k-test-512-result-4*
 (hexes-string-to-list
  "f4 f8 46 d1 40 84 75 39 f5 3c 3f 08 2c c4 e6 81 0e 14 3a 5b 4f c6 2a 20 59 7b 5d 76 04 32 46 b8 6b d7 14 9b 90 61 40 bb 96 65 a6 ce 83 d9 91 f0 32 f2 29 1d 2f ae 80 ee df c6 f8 45 cc 16 d5 ae"))

(defconst *k-test-512-result-5*
 (hexes-string-to-list
  "02 BE 89 A7 D4 72 1E FB 94 0C 93 79 EA F7 6D 71 96 30 E5 58 81 CD AA AA 77 73 20 E4 A1 FA 39 BA F6 8A 20 A2 9C A5 B6 01 C9 A6 C7 79 7C BA C7 E9 7B 81 85 84 03 70 4D B8 D3 D9 72 52 80 3D 73 FB"))

(defconst *k-test-512-result-6*
 (hexes-string-to-list
  "3A FC 3D 40 41 E0 10 D6 FE 94 00 51 0F B6 BF D7 E0 D9 2C F3 F0 43 9E 2E 14 E8 4E A9 E4 D4 15 02 75 85 5F A1 8F 0E 12 39 AA 15 35 0B F5 BA 00 24 B4 8A B7 5F D2 48 5C 37 39 E6 79 0D D0 21 85 9B"))

(defconst *k-test-512-result-7*
 (hexes-string-to-list
  "95 58 a7 ba 9a c7 4b 33 b3 47 70 3f fe 33 f8 d5 61 d8 6d 9f ca d1 cf d6 32 25 fb 55 df ea 50 a0 95 3a 0e fa fd 60 72 37 7f 4c 39 6e 80 6d 5b da 02 94 cb a2 87 62 74 0d 84 46 fe e4 5a 27 6e 4a"))

(defconst *k-test-512-result-8*
 (hexes-string-to-list
  "65 6c 09 57 3c fd 6d 17 bf 00 48 70 2c 0e ed be c3 0e 8d 3c fd 20 77 c7 df 9b a9 73 59 2d 75 c3 b5 65 8c 3e 19 43 b3 28 ba dc 5f fe 2f e1 c5 17 54 a5 62 59 e1 17 b1 af ad 5a 2a 9e 3f 50 3e a1"))

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-1*))
 *k-test-512-result-1*)
(assert-equal
 (keccak-512-bytes *k-test-input-1*)
 *k-test-512-result-1*)
(assert-equal
 (keccak-512-string-to-bytes *k-test-input-1-string*)
 *k-test-512-result-1*)

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-2*))
 *k-test-512-result-2*)
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-3*))
 *k-test-512-result-3*)

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-4*))
 *k-test-512-result-4*)
(assert-equal
 (keccak-512-bytes (bits-to-bytes-little *k-test-input-4*))
 *k-test-512-result-4*)

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-5*))
 *k-test-512-result-5*)
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-6*))
 *k-test-512-result-6*)

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-7*))
 *k-test-512-result-7*)
(assert-equal
 (keccak-512-bytes (bits-to-bytes-little *k-test-input-7*))
 *k-test-512-result-7*)

;; test input 8 is 2288 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (keccak-512 *k-test-input-8*))
 *k-test-512-result-8*)
(assert-equal
 (keccak-512-bytes (bits-to-bytes-little *k-test-input-8*))
 *k-test-512-result-8*)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ================================
;; Testing sha3
;; ================================


;; -----------------------------------------
;; See the above section titled "Test cases for sha3 / keccak"
;; for the definition of these tests.
;; The comments below are the expected results in
;; http://csrc.nist.gov/groups/ST/toolkit/examples.html#aHashing


;; sha3-224 and sha3-224-bytes
;; --------
;; 1. 6B 4E 03 42 36 67 DB B7 3B 6E 15 45 4F 0E B1 AB
;;    D4 59 7F 9A 1B 07 8E 3F 5B 5A 6B C7
;; 2. FF BA D5 DA 96 BA D7 17 89 33 02 06 DC 67 68 EC
;;    AE B1 B3 2D CA 6B 33 01 48 96 74 AB
;; 3. D6 66 A5 14 CC 9D BA 25 AC 1B A6 9E D3 93 04 60
;;    DE AA C9 85 1B 5F 0B AA B0 07 DF 3B
;; 4. 93 76 81 6A BA 50 3F 72 F9 6C E7 EB 65 AC 09 5D
;;    EE E3 BE 4B F9 BB C2 A1 CB 7E 11 E0
;; 5. 22 D2 F7 BB 0B 17 3F D8 C1 96 86 F9 17 31 66 E3
;;    EE 62 73 80 47 D7 EA DD 69 EF B2 28
;; 6. 4E 90 7B B1 05 78 61 F2 00 A5 99 E9 D4 F8 5B 02
;;    D8 84 53 BF 5B 8A CE 9A C5 89 13 4C
;; 7. 04eaf0c175aa45299155aca3f97e41c2d684eb0978c9af6cd88c5a51

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-1*))
 (hexes-string-to-list
  "6B 4E 03 42 36 67 DB B7 3B 6E 15 45 4F 0E B1 AB D4 59 7F 9A 1B 07 8E 3F 5B 5A 6B C7"))
(assert-equal
 (sha3-224-bytes (bits-to-bytes-little *k-test-input-1*))
 (hexes-string-to-list
  "6B 4E 03 42 36 67 DB B7 3B 6E 15 45 4F 0E B1 AB D4 59 7F 9A 1B 07 8E 3F 5B 5A 6B C7"))

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-2*))
 (hexes-string-to-list
  "FF BA D5 DA 96 BA D7 17 89 33 02 06 DC 67 68 EC AE B1 B3 2D CA 6B 33 01 48 96 74 AB"))
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-3*))
 (hexes-string-to-list
  "D6 66 A5 14 CC 9D BA 25 AC 1B A6 9E D3 93 04 60 DE AA C9 85 1B 5F 0B AA B0 07 DF 3B"))

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-4*))
 (hexes-string-to-list
  "93 76 81 6A BA 50 3F 72 F9 6C E7 EB 65 AC 09 5D EE E3 BE 4B F9 BB C2 A1 CB 7E 11 E0"))
(assert-equal
 (sha3-224-bytes (bits-to-bytes-little *k-test-input-4*))
 (hexes-string-to-list
  "93 76 81 6A BA 50 3F 72 F9 6C E7 EB 65 AC 09 5D EE E3 BE 4B F9 BB C2 A1 CB 7E 11 E0"))

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-5*))
 (hexes-string-to-list
  "22 D2 F7 BB 0B 17 3F D8 C1 96 86 F9 17 31 66 E3 EE 62 73 80 47 D7 EA DD 69 EF B2 28"))
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-6*))
 (hexes-string-to-list
  "4E 90 7B B1 05 78 61 F2 00 A5 99 E9 D4 F8 5B 02 D8 84 53 BF 5B 8A CE 9A C5 89 13 4C"))

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-224 *k-test-input-7*))
 (hexes-string-to-list
  "04 ea f0 c1 75 aa 45 29 91 55 ac a3 f9 7e 41 c2 d6 84 eb 09 78 c9 af 6c d8 8c 5a 51"))
(assert-equal
 (sha3-224-bytes (bits-to-bytes-little *k-test-input-7*))
 (hexes-string-to-list
  "04 ea f0 c1 75 aa 45 29 91 55 ac a3 f9 7e 41 c2 d6 84 eb 09 78 c9 af 6c d8 8c 5a 51"))


;; sha3-256 and sha3-256-bytes
;; --------
;; 1. A7 FF C6 F8 BF 1E D7 66 51 C1 47 56 A0 61 D6 62
;;    F5 80 FF 4D E4 3B 49 FA 82 D8 0A 4B 80 F8 43 4A
;; 2. 7B 00 47 CF 5A 45 68 82 36 3C BF 0F B0 53 22 CF
;;    65 F4 B7 05 9A 46 36 5E 83 01 32 E3 B5 D9 57 AF
;; 3. C8 24 2F EF 40 9E 5A E9 D1 F1 C8 57 AE 4D C6 24
;;    B9 2B 19 80 9F 62 AA 8C 07 41 1C 54 A0 78 B1 D0
;; 4. 79 F3 8A DE C5 C2 03 07 A9 8E F7 6E 83 24 AF BF
;;    D4 6C FD 81 B2 2E 39 73 C6 5F A1 BD 9D E3 17 87
;; 5. 81 EE 76 9B ED 09 50 86 2B 1D DD ED 2E 84 AA A6
;;    AB 7B FD D3 CE AA 47 1B E3 11 63 D4 03 36 36 3C
;; 6. 52 86 0A A3 01 21 4C 61 0D 92 2A 6B 6C AB 98 1C
;;    CD 06 01 2E 54 EF 68 9D 74 40 21 E7 38 B9 ED 20
;; 7. 7f5979fb78f082e8b1c676635db8795c4ac6faba03525fb708cb5fd68fd40c5e

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-1*))
 (hexes-string-to-list
  "A7 FF C6 F8 BF 1E D7 66 51 C1 47 56 A0 61 D6 62 F5 80 FF 4D E4 3B 49 FA 82 D8 0A 4B 80 F8 43 4A"))
(assert-equal
 (sha3-256-bytes *k-test-input-1*)
 (hexes-string-to-list
  "A7 FF C6 F8 BF 1E D7 66 51 C1 47 56 A0 61 D6 62 F5 80 FF 4D E4 3B 49 FA 82 D8 0A 4B 80 F8 43 4A"))

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-2*))
 (hexes-string-to-list
  "7B 00 47 CF 5A 45 68 82 36 3C BF 0F B0 53 22 CF 65 F4 B7 05 9A 46 36 5E 83 01 32 E3 B5 D9 57 AF"))
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-3*))
 (hexes-string-to-list
  "C8 24 2F EF 40 9E 5A E9 D1 F1 C8 57 AE 4D C6 24 B9 2B 19 80 9F 62 AA 8C 07 41 1C 54 A0 78 B1 D0"))

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-4*))
 (hexes-string-to-list
  "79 F3 8A DE C5 C2 03 07 A9 8E F7 6E 83 24 AF BF D4 6C FD 81 B2 2E 39 73 C6 5F A1 BD 9D E3 17 87"))
(assert-equal
 (sha3-256-bytes (bits-to-bytes-little *k-test-input-4*))
 (hexes-string-to-list
  "79 F3 8A DE C5 C2 03 07 A9 8E F7 6E 83 24 AF BF D4 6C FD 81 B2 2E 39 73 C6 5F A1 BD 9D E3 17 87"))

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-5*))
 (hexes-string-to-list
  "81 EE 76 9B ED 09 50 86 2B 1D DD ED 2E 84 AA A6 AB 7B FD D3 CE AA 47 1B E3 11 63 D4 03 36 36 3C"))
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-6*))
 (hexes-string-to-list
  "52 86 0A A3 01 21 4C 61 0D 92 2A 6B 6C AB 98 1C CD 06 01 2E 54 EF 68 9D 74 40 21 E7 38 B9 ED 20"))

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-256 *k-test-input-7*))
 (hexes-string-to-list
  "7f 59 79 fb 78 f0 82 e8 b1 c6 76 63 5d b8 79 5c 4a c6 fa ba 03 52 5f b7 08 cb 5f d6 8f d4 0c 5e"))
(assert-equal
 (sha3-256-bytes (bits-to-bytes-little *k-test-input-7*))
 (hexes-string-to-list
  "7f 59 79 fb 78 f0 82 e8 b1 c6 76 63 5d b8 79 5c 4a c6 fa ba 03 52 5f b7 08 cb 5f d6 8f d4 0c 5e"))


;; sha3-384 and sha3-384-bytes
;; --------
;; 1. 0C 63 A7 5B 84 5E 4F 7D 01 10 7D 85 2E 4C 24 85
;;    C5 1A 50 AA AA 94 FC 61 99 5E 71 BB EE 98 3A 2A
;;    C3 71 38 31 26 4A DB 47 FB 6B D1 E0 58 D5 F0 04
;; 2. 73 7C 9B 49 18 85 E9 BF 74 28 E7 92 74 1A 7B F8
;;    DC A9 65 34 71 C3 E1 48 47 3F 2C 23 6B 6A 0A 64
;;    55 EB 1D CE 9F 77 9B 4B 6B 23 7F EF 17 1B 1C 64
;; 3. 95 5B 4D D1 BE 03 26 1B D7 6F 80 7A 7E FD 43 24
;;    35 C4 17 36 28 11 B8 A5 0C 56 4E 7E E9 58 5E 1A
;;    C7 62 6D DE 2F DC 03 0F 87 61 96 EA 26 7F 08 C3
;; 4. 18 81 DE 2C A7 E4 1E F9 5D C4 73 2B 8F 5F 00 2B
;;    18 9C C1 E4 2B 74 16 8E D1 73 26 49 CE 1D BC DD
;;    76 19 7A 31 FD 55 EE 98 9F 2D 70 50 DD 47 3E 8F
;; 5. A3 1F DB D8 D5 76 55 1C 21 FB 11 91 B5 4B DA 65
;;    B6 C5 FE 97 F0 F4 A6 91 03 42 4B 43 F7 FD B8 35
;;    97 9F DB EA E8 B3 FE 16 CB 82 E5 87 38 1E B6 24
;; 6. 34 85 D3 B2 80 BD 38 4C F4 A7 77 84 4E 94 67 81
;;    73 05 5D 1C BC 40 C7 C2 C3 83 3D 9E F1 23 45 17
;;    2D 6F CD 31 92 3B B8 79 5A C8 18 47 D3 D8 85 5C
;; 7. e15a44d4e12ac138db4b8d77e954d78d94de4391ec2d1d8b2b8ace1a2f4b3d2fb9efd0546d6fcafacbe5b1640639b005

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-1*))
 (hexes-string-to-list
  "0C 63 A7 5B 84 5E 4F 7D 01 10 7D 85 2E 4C 24 85 C5 1A 50 AA AA 94 FC 61 99 5E 71 BB EE 98 3A 2A C3 71 38 31 26 4A DB 47 FB 6B D1 E0 58 D5 F0 04"))
(assert-equal
 (sha3-384-bytes (bits-to-bytes-little *k-test-input-1*))
 (hexes-string-to-list
  "0C 63 A7 5B 84 5E 4F 7D 01 10 7D 85 2E 4C 24 85 C5 1A 50 AA AA 94 FC 61 99 5E 71 BB EE 98 3A 2A C3 71 38 31 26 4A DB 47 FB 6B D1 E0 58 D5 F0 04"))

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-2*))
 (hexes-string-to-list
  "73 7C 9B 49 18 85 E9 BF 74 28 E7 92 74 1A 7B F8 DC A9 65 34 71 C3 E1 48 47 3F 2C 23 6B 6A 0A 64 55 EB 1D CE 9F 77 9B 4B 6B 23 7F EF 17 1B 1C 64"))
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-3*))
 (hexes-string-to-list
  "95 5B 4D D1 BE 03 26 1B D7 6F 80 7A 7E FD 43 24 35 C4 17 36 28 11 B8 A5 0C 56 4E 7E E9 58 5E 1A C7 62 6D DE 2F DC 03 0F 87 61 96 EA 26 7F 08 C3"))

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-4*))
 (hexes-string-to-list
  "18 81 DE 2C A7 E4 1E F9 5D C4 73 2B 8F 5F 00 2B 18 9C C1 E4 2B 74 16 8E D1 73 26 49 CE 1D BC DD 76 19 7A 31 FD 55 EE 98 9F 2D 70 50 DD 47 3E 8F"))
(assert-equal
 (sha3-384-bytes (bits-to-bytes-little *k-test-input-4*))
 (hexes-string-to-list
  "18 81 DE 2C A7 E4 1E F9 5D C4 73 2B 8F 5F 00 2B 18 9C C1 E4 2B 74 16 8E D1 73 26 49 CE 1D BC DD 76 19 7A 31 FD 55 EE 98 9F 2D 70 50 DD 47 3E 8F"))

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-5*))
 (hexes-string-to-list
  "A3 1F DB D8 D5 76 55 1C 21 FB 11 91 B5 4B DA 65 B6 C5 FE 97 F0 F4 A6 91 03 42 4B 43 F7 FD B8 35 97 9F DB EA E8 B3 FE 16 CB 82 E5 87 38 1E B6 24"))
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-6*))
 (hexes-string-to-list
  "34 85 D3 B2 80 BD 38 4C F4 A7 77 84 4E 94 67 81 73 05 5D 1C BC 40 C7 C2 C3 83 3D 9E F1 23 45 17 2D 6F CD 31 92 3B B8 79 5A C8 18 47 D3 D8 85 5C"))

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-384 *k-test-input-7*))
 (hexes-string-to-list
  "e1 5a 44 d4 e1 2a c1 38 db 4b 8d 77 e9 54 d7 8d 94 de 43 91 ec 2d 1d 8b 2b 8a ce 1a 2f 4b 3d 2f b9 ef d0 54 6d 6f ca fa cb e5 b1 64 06 39 b0 05"))
(assert-equal
 (sha3-384-bytes (bits-to-bytes-little *k-test-input-7*))
 (hexes-string-to-list
  "e1 5a 44 d4 e1 2a c1 38 db 4b 8d 77 e9 54 d7 8d 94 de 43 91 ec 2d 1d 8b 2b 8a ce 1a 2f 4b 3d 2f b9 ef d0 54 6d 6f ca fa cb e5 b1 64 06 39 b0 05"))




;; sha3-512 and sha3-512-bytes
;; --------
;; 1. A6 9F 73 CC A2 3A 9A C5 C8 B5 67 DC 18 5A 75 6E
;;    97 C9 82 16 4F E2 58 59 E0 D1 DC C1 47 5C 80 A6
;;    15 B2 12 3A F1 F5 F9 4C 11 E3 E9 40 2C 3A C5 58
;;    F5 00 19 9D 95 B6 D3 E3 01 75 85 86 28 1D CD 26
;; 2. A1 3E 01 49 41 14 C0 98 00 62 2A 70 28 8C 43 21
;;    21 CE 70 03 9D 75 3C AD D2 E0 06 E4 D9 61 CB 27
;;    54 4C 14 81 E5 81 4B DC EB 53 BE 67 33 D5 E0 99
;;    79 5E 5E 81 91 8A DD B0 58 E2 2A 9F 24 88 3F 37
;; 3. 98 34 C0 5A 11 E1 C5 D3 DA 9C 74 0E 1C 10 6D 9E
;;    59 0A 0E 53 0B 6F 6A AA 78 30 52 5D 07 5C A5 DB
;;    1B D8 A6 AA 98 1A 28 61 3A C3 34 93 4A 01 82 3C
;;    D4 5F 45 E4 9B 6D 7E 69 17 F2 F1 67 78 06 7B AB
;; 4. E7 6D FA D2 20 84 A8 B1 46 7F CF 2F FA 58 36 1B
;;    EC 76 28 ED F5 F3 FD C0 E4 80 5D C4 8C AE EC A8
;;    1B 7C 13 C3 0A DF 52 A3 65 95 84 73 9A 2D F4 6B
;;    E5 89 C5 1C A1 A4 A8 41 6D F6 54 5A 1C E8 BA 00
;; 5. FC 4A 16 7C CB 31 A9 37 D6 98 FD E8 2B 04 34 8C
;;    95 39 B2 8F 0C 9D 3B 45 05 70 9C 03 81 23 50 E4
;;    99 0E 96 22 97 4F 6E 57 5C 47 86 1C 0D 2E 63 8C
;;    CF C2 02 3C 36 5B B6 0A 93 F5 28 55 06 98 78 6B
;; 6. CF 9A 30 AC 1F 1F 6A C0 91 6F 9F EF 19 19 C5 95
;;    DE BE 2E E8 0C 85 42 12 10 FD F0 5F 1C 6A F7 3A
;;    A9 CA C8 81 D0 F9 1D B6 D0 34 A2 BB AD C1 CF 7F
;;    BC B2 EC FA 9D 19 1D 3A 50 16 FB 3F AD 87 09 C9
;; 7. 881c7d6ba98678bcd96e253086c4048c3ea15306d0d13ff48341c6285ee71102a47b6f16e20e4d65c0c3d677be689dfda6d326695609cbadfafa1800e9eb7fc1

;; *k-test-input-1* is the empty list, so can be used as a list of bits or a
;; list of bytes.
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-1*))
 (hexes-string-to-list
  "A6 9F 73 CC A2 3A 9A C5 C8 B5 67 DC 18 5A 75 6E 97 C9 82 16 4F E2 58 59 E0 D1 DC C1 47 5C 80 A6 15 B2 12 3A F1 F5 F9 4C 11 E3 E9 40 2C 3A C5 58 F5 00 19 9D 95 B6 D3 E3 01 75 85 86 28 1D CD 26"))
(assert-equal
 (sha3-512-bytes (bits-to-bytes-little *k-test-input-1*))
 (hexes-string-to-list
  "A6 9F 73 CC A2 3A 9A C5 C8 B5 67 DC 18 5A 75 6E 97 C9 82 16 4F E2 58 59 E0 D1 DC C1 47 5C 80 A6 15 B2 12 3A F1 F5 F9 4C 11 E3 E9 40 2C 3A C5 58 F5 00 19 9D 95 B6 D3 E3 01 75 85 86 28 1D CD 26"))

;; test inputs 2 and 3 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-2*))
 (hexes-string-to-list
  "A1 3E 01 49 41 14 C0 98 00 62 2A 70 28 8C 43 21 21 CE 70 03 9D 75 3C AD D2 E0 06 E4 D9 61 CB 27 54 4C 14 81 E5 81 4B DC EB 53 BE 67 33 D5 E0 99 79 5E 5E 81 91 8A DD B0 58 E2 2A 9F 24 88 3F 37"))
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-3*))
 (hexes-string-to-list
  "98 34 C0 5A 11 E1 C5 D3 DA 9C 74 0E 1C 10 6D 9E 59 0A 0E 53 0B 6F 6A AA 78 30 52 5D 07 5C A5 DB 1B D8 A6 AA 98 1A 28 61 3A C3 34 93 4A 01 82 3C D4 5F 45 E4 9B 6D 7E 69 17 F2 F1 67 78 06 7B AB"))

;; *k-test-input-4* is 200 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-4*))
 (hexes-string-to-list
  "E7 6D FA D2 20 84 A8 B1 46 7F CF 2F FA 58 36 1B EC 76 28 ED F5 F3 FD C0 E4 80 5D C4 8C AE EC A8 1B 7C 13 C3 0A DF 52 A3 65 95 84 73 9A 2D F4 6B E5 89 C5 1C A1 A4 A8 41 6D F6 54 5A 1C E8 BA 00"))
(assert-equal
 (sha3-512-bytes (bits-to-bytes-little *k-test-input-4*))
 (hexes-string-to-list
  "E7 6D FA D2 20 84 A8 B1 46 7F CF 2F FA 58 36 1B EC 76 28 ED F5 F3 FD C0 E4 80 5D C4 8C AE EC A8 1B 7C 13 C3 0A DF 52 A3 65 95 84 73 9A 2D F4 6B E5 89 C5 1C A1 A4 A8 41 6D F6 54 5A 1C E8 BA 00"))

;; test inputs 5 and 6 are not a multiple of 8 bits, so just use the
;; bit-oriented tests
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-5*))
 (hexes-string-to-list
  "FC 4A 16 7C CB 31 A9 37 D6 98 FD E8 2B 04 34 8C 95 39 B2 8F 0C 9D 3B 45 05 70 9C 03 81 23 50 E4 99 0E 96 22 97 4F 6E 57 5C 47 86 1C 0D 2E 63 8C CF C2 02 3C 36 5B B6 0A 93 F5 28 55 06 98 78 6B"))
(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-6*))
 (hexes-string-to-list
  "CF 9A 30 AC 1F 1F 6A C0 91 6F 9F EF 19 19 C5 95 DE BE 2E E8 0C 85 42 12 10 FD F0 5F 1C 6A F7 3A A9 CA C8 81 D0 F9 1D B6 D0 34 A2 BB AD C1 CF 7F BC B2 EC FA 9D 19 1D 3A 50 16 FB 3F AD 87 09 C9"))

;; test input 7 is 56 bits, which is divisible by 8, so test both
;; bit-oriented and byte-oriented functions

(assert-equal
 (bits-to-bytes-little (sha3-512 *k-test-input-7*))
 (hexes-string-to-list
  "88 1c 7d 6b a9 86 78 bc d9 6e 25 30 86 c4 04 8c 3e a1 53 06 d0 d1 3f f4 83 41 c6 28 5e e7 11 02 a4 7b 6f 16 e2 0e 4d 65 c0 c3 d6 77 be 68 9d fd a6 d3 26 69 56 09 cb ad fa fa 18 00 e9 eb 7f c1"))
(assert-equal
 (sha3-512-bytes (bits-to-bytes-little *k-test-input-7*))
 (hexes-string-to-list
  "88 1c 7d 6b a9 86 78 bc d9 6e 25 30 86 c4 04 8c 3e a1 53 06 d0 d1 3f f4 83 41 c6 28 5e e7 11 02 a4 7b 6f 16 e2 0e 4d 65 c0 c3 d6 77 be 68 9d fd a6 d3 26 69 56 09 cb ad fa fa 18 00 e9 eb 7f c1"))
