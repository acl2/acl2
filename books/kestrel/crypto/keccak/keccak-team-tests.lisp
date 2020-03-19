; Keccak Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KECCAK")

;; --------------------------------
;; The following tests are from the Keccak team as of the round 3 submission
;; for the SHA-3 contest.
;; They precede the extra 2-bit padding '01' added for FIPS 202.
;;
;; We think these tests were originally at:
;;   http://keccak.noekeon.org/KeccakKAT-3.zip
;; but as of 2019-07-11 they are available at:
;;   https://keccak.team/obsolete/KeccakKAT-3.zip
;; which is findable from
;;   https://keccak.team/archives.html
;; following the link at
;;   Known-answer and Monte Carlo test results
;;   * As of round 3 of the SHA-3 competition

;; From this zip file, we take tests from
;;   ShortMsgKAT_NNN.txt
;; and
;;   LongMsgKAT_NNN.txt
;; for NNN in {224, 256, 384, 512}.

;; Note that there are additional tests in this zip file that can be considered.

;; ----
;; Format of the tests.
;; Each of the .txt files above has a number of tests, each of which
;; looks like this:
;;   Len = <decimal number of bits>
;;   Msg = <hex string>
;;   MD = <hex string>

;; Msg is converted to a bit string from left to right one byte at a time.
;; Each byte is converted to bits in little-endian.
;; If rembits = Len mod 8 <> 0, the last (Len mod 8) bits are the
;; highest-order bits of the last byte, written in little endian.
;; For example, if Len = 10 and Msg = 9D40,
;; the first byte is x9D, little endian 10111001
;; the two most significant bits of the next byte are 0 (for x80) and 1 (for
;; x40), which are written in little endian order: 10,
;; so the full bitstring is 1011100110.


;; --------------------------------
;; include-book statements

(include-book "keccak")

(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; big defconsts
(include-book "keccak-team-test-data")

(include-book "std/testing/assert-equal" :dir :system)


;; --------------------------------
;; Test automation
;;
;; Each test has 3 parts:
;; Len: the length of the input in bits.
;; Msg: the input message in hex.  See above for the rule on converting
;;      this to a bit string when Len mod 8 is not 0.
;; MD: the output in hex.
;;     This is also a sequence of hex digits taken two at a time to get a sequence
;;     of bytes.


;; Define a function for the guard of hexstring=>ubyte8s
(define hexstringp (str)
  :returns (yes/no booleanp)
  (and (stringp str)
       (str::hex-digit-string-p str)
       (evenp (length str))))


;; Convert the input hexstring with Len, the length in bits,
;; to the appropriate list of bits.
(define kat-msg-to-bits ((Len natp)
                         (Msg hexstringp))
  :returns (bits bit-listp
                 :hints (("Goal" :in-theory (disable bit-listp-alt-def))))
  :guard-hints (("Goal" :in-theory (enable
                                    acl2::byte-listp-rewrite-unsigned-byte-listp
                                    hexstringp
                                    verify-guards-lemma)))
  (b* ((available-bytes (acl2::hexstring=>ubyte8s Msg))
       (num-needed-full-bytes (floor Len 8))
       (num-needed-extra-bits (mod Len 8))
       ;; If Len is requesting more bytes than available, output an error message
       ;; and return an empty list.
       ((when (< (len available-bytes)
                 (+ num-needed-full-bytes (if (equal num-needed-extra-bits 0) 0 1))))
        (prog2$ (cw "ERROR: kat-msg-to-bits Msg hexstring too short for Len bits")
                '()))
       (bits-from-needed-bytes
        (acl2::lebytes=>bits (firstn num-needed-full-bytes available-bytes)))
       (extra-bits (if (equal num-needed-extra-bits 0)
                       '()
                     ;; If the last byte is partial, the tests take the number of
                     ;; needed high-order bits from the next byte,
                     ;; returned in little-endian order.
                     ;; See "Format of the tests." above.
                     (nthcdr (- 8 num-needed-extra-bits)
                             (acl2::nat=>lebits
                              8 (nth num-needed-full-bytes available-bytes))))))
    (append bits-from-needed-bytes extra-bits))
  :prepwork
  ((local
    (defthmd verify-guards-lemma
      (implies (unsigned-byte-p 8 x)
               (and (integerp x)
                    (<= 0 x)
                    (< x 256)))))))


(define call-keccak ((input-bits bit-listp) (num-output-bits natp))
  :returns (hash bit-listp)
  (case num-output-bits
    (224 (keccak-224 input-bits))
    (256 (keccak-256 input-bits))
    (384 (keccak-384 input-bits))
    (512 (keccak-512 input-bits))
    (otherwise
     (prog2$ (cw "ERROR: unsupported number of output bits for Keccak")
             '()))))


;; A test case is a triple (Len, Msg, MD) as explained above.
(define test-case-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 3)
       (natp (first x)) ; Len
       (hexstringp (second x)) ; Msg
       (hexstringp (third x)))) ; MD


;; Lists of test cases.
(std::deflist test-case-listp (x)
  (test-case-p x)
  :true-listp t
  :elementp-of-nil nil)


;; T means passed, NIL means failed
(define run-kat-test ((num-output-bits natp) (triple test-case-p))
  :returns (yes/no booleanp)
  (let ((Len (first triple))
        (Msg (second triple))
        (MD (third triple)))
    (let ((input-bits (kat-msg-to-bits Len Msg))
          (desired-output-bits (acl2::lebytes=>bits
                                (acl2::hexstring=>ubyte8s MD))))
      (if (not (equal (len desired-output-bits)
                      num-output-bits))
          (prog2$ (cw "ERROR: inconsistent MD for given number of output bits")
                  nil)
        (equal (call-keccak input-bits num-output-bits)
               desired-output-bits))))
  :guard-hints
  (("Goal" :in-theory (enable test-case-p
                              hexstringp
                              acl2::byte-listp-rewrite-unsigned-byte-listp))))


;; T means all passed; NIL means at least one failed
(define run-kat-tests ((num-output-bits natp) (triples test-case-listp))
  :returns (yes/no booleanp)
  (b* (((when (atom triples))
        T)
       (this-passed? (run-kat-test num-output-bits (car triples)))
       (- (if (null this-passed?)
              (cw "KAT test failed: keccak-~x0 on ~x1 bits of ~x2~%"
                  num-output-bits
                  (first (car triples)) (second (car triples)))
            nil))
       (rest-passed? (run-kat-tests num-output-bits (cdr triples))))
    (and this-passed? rest-passed?))
  :guard-hints (("Goal" :in-theory (enable test-case-listp test-case-p))))


;; Output success message if all tests succeeded.
;; TYPE describes which bunch of tests, for now just "short" or "long"
(define run-kat-tests-and-report (type
                                  (num-output-bits natp)
                                  (triples test-case-listp))
  :returns (yes/no booleanp)
  (if (run-kat-tests num-output-bits triples)
      (prog2$ (cw "All ~x0 keccak-~x1 tests succeeded!~%" type num-output-bits)
              t)
    nil))


;; --------------------------------
;; Test data

;; The test data is defined in
;;   keccak-team-test-data.lisp
;; in the form of defconsts.


;; --------------------------------
;; Run abridged tests

(acl2::assert! (run-kat-tests 224 *abridged-short-224-tests*))
(acl2::assert! (run-kat-tests 256 *abridged-short-256-tests*))
(acl2::assert! (run-kat-tests 384 *abridged-short-384-tests*))
(acl2::assert! (run-kat-tests 512 *abridged-short-512-tests*))

(acl2::assert! (run-kat-tests 224 *abridged-long-224-tests*))
(acl2::assert! (run-kat-tests 256 *abridged-long-256-tests*))
(acl2::assert! (run-kat-tests 384 *abridged-long-384-tests*))
(acl2::assert! (run-kat-tests 512 *abridged-long-512-tests*))


;; --------------------------------
;; Run unabridged tests

#||
;; easy form to paste into ACL2 listener, but it could take over an hour to run
(in-package "KECCAK")
(time$ (acl2::assert! (and (run-kat-tests-and-report "short" 224 *short-224-tests*)
                           (run-kat-tests-and-report "short" 256 *short-256-tests*)
                           (run-kat-tests-and-report "short" 384 *short-384-tests*)
                           (run-kat-tests-and-report "short" 512 *short-512-tests*)
                           (run-kat-tests-and-report "long" 224 *long-224-tests*)
                           (run-kat-tests-and-report "long" 256 *long-256-tests*)
                           (run-kat-tests-and-report "long" 384 *long-384-tests*)
                           (run-kat-tests-and-report "long" 512 *long-512-tests*)
                           )))
||#
