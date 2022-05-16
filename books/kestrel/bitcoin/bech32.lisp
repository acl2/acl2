; Bitcoin Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "projects/apply/top" :dir :system) ; needed for defwarrant
(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bech32
  :parents (bitcoin)
  :short "A library for Bech32 encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Bech32 and Bech32m are used to encode a sequence of bytes
    in a checksummed base32 format.")
   (xdoc::p
    "The following executable formal specifications follow the
    specifications in "
    (xdoc::ahref
     "https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki"
     "BIP 173")
    "and"
    (xdoc::ahref
     "https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki"
     "BIP 350")
    ".")
   (xdoc::p
    "Bech32 and Bech32m differ only in the value xored into the
     checksum at the end of the computation.  When we describe Bech32,
     we are usually referring to both Bech32 and Bech32m."))
  :order-subtopics t
  :default-parent t)

(defxdoc bip-173
  :parents (bitcoin)
  :short "BIP-173"
  :long (xdoc::topstring (xdoc::p "See @(see bech32).")))

(defxdoc bip-350
  :parents (bitcoin)
  :short "BIP-350"
  :long (xdoc::topstring (xdoc::p "See @(see bech32).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Human-readable portion validity.

(define hrp-valid-char-code-p (x)
  :returns (y/n booleanp)
  (and (integerp x)
       (<= 33 x)
       (<= x 126)))

(define hrp-valid-string-length-p ((s stringp))
  :returns (y/n booleanp)
  (let ((slen (length s)))
    (and (<= 1 slen)
         (<= slen 83))))

(defwarrant hrp-valid-char-code-p)

(define hrp-valid-p ((s stringp))
  :returns (y/n booleanp)
  :short "Check if a Bech32 human-readable portion is valid."
  (and (hrp-valid-string-length-p s)
       (loop$ for x in (explode s) always (and (characterp x) (hrp-valid-char-code-p (char-code x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *bech32m-const*
  :short "Bech32m constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Value xored into the checksum at the end of computing Bech32m.")
   (xdoc::p
    "The equivalent value for Bech32 is @('1')."))
  #x2bc830a3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Data portion conversion and validity

(defval *bech32-char-vals*
  :short "Map from 5-bit nonnegative integer to Bech32 character."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of 32 characters representing a map from the index in @('[0..32)')
     to the bech32 or bech32m character that represents that number,
     used to encode the @('data part')."))
  (explode "qpzry9x8gf2tvdw0s3jn54khce6mua7l"))

; If any one of the data-chars is not in *bech32-char-vals*,
; then the returned list will contain a nil, and callers should check for that.
; Note, callers of this might have an easier time if the return type
; were byte-option-listp.
(define bech32-chars-to-octets ((data-chars character-listp))
  :returns (ret-val true-listp)
  (if (endp data-chars)
      nil
    (cons (position (first data-chars) *bech32-char-vals*)
          (bech32-chars-to-octets (rest data-chars)))))

; Valid data bytes are from 0 to 31.
; A predicate for that is (unsigned-byte-listp 5 data-octets-or-nils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Checksum Verification

(defconst *bech32-GEN*
  '(#x3b6a57b2 #x26508e6d #x1ea119fa #x3d4233dd #x2a1462b3))

(define bech32-polymod-aux ((values (unsigned-byte-listp 8 values))
                            (chk (unsigned-byte-p 48 chk)))
  :returns (checksum (unsigned-byte-p 48 checksum))
  (if (not (mbt (unsigned-byte-p 48 chk))) ; for return type theorem
      0
    (if (endp values)
        chk
      (b* ((v (first values))
           (b (bvshr 48 chk 25))
           (chk (bvxor 48 (bvshl 48 (bvand 48 chk #x1ffffff) 5) v))
           ;; Unroll the loop of i in range(5).
           ;; Mostly leaving it unoptimized for clarity.
           ;; Replaced `.. & 1` by `(oddp ..)`.
           (chk (bvxor 48 chk (if (oddp (bvshr 48 b 0))
                                  (nth 0 *bech32-GEN*)
                                0)))
           (chk (bvxor 48 chk (if (oddp (bvshr 48 b 1))
                                  (nth 1 *bech32-GEN*)
                                0)))
           (chk (bvxor 48 chk (if (oddp (bvshr 48 b 2))
                                  (nth 2 *bech32-GEN*)
                                0)))
           (chk (bvxor 48 chk (if (oddp (bvshr 48 b 3))
                                  (nth 3 *bech32-GEN*)
                                0)))
           (chk (bvxor 48 chk (if (oddp (bvshr 48 b 4))
                                  (nth 4 *bech32-GEN*)
                                0))))
        (bech32-polymod-aux (rest values) chk))))
  :guard-hints (("Goal" :in-theory (disable oddp))))

(define bech32-polymod ((values (unsigned-byte-listp 8 values)))
  :returns (checksum (unsigned-byte-p 48 checksum))
  :short "The polymod checksum for both Bech32 and Bech32m."
  (bech32-polymod-aux values 1))

(defwarrant bvshr)
(defwarrant bvand)

(define bech32-collect-high-3-bits ((codes (unsigned-byte-listp 8 codes)))
  :returns (high-bits-codes (unsigned-byte-listp 8 high-bits-codes)
                            :hyp (warrant bvshr))
  (loop$ for code of-type (integer 0 255) in codes collect (bvshr 8 code 5))
 :guard-hints (("Goal" :in-theory (enable unsigned-byte-p))))

(define bech32-collect-low-5-bits ((codes (unsigned-byte-listp 8 codes)))
  :returns (low-bits-codes (unsigned-byte-listp 8 low-bits-codes)
                           :hyp (warrant bvand))
  (loop$ for code of-type (integer 0 255) in codes collect (bvand 8 code 31))
  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p))))

(define bech32-hrp-expand ((s stringp))
  :returns (expanded-hrp (unsigned-byte-listp 8 expanded-hrp)
                         :hyp (and (warrant bvshr) (warrant bvand)))
  :short "The stretching of the human-readable portion."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('hrp') is converted to a list of ascii codes (octets)
     and then copied to make two lists.  The first list
     shifts out all 5 low bits, leaving the 3 high bits
     of each code.  The second list masks out the 3 high bits,
     leaving the low five bits of each code.  Then the two lists
     are appended with a zero byte in between."))
  (b* ((char-codes (string=>nats s))
       (high-bit-codes (bech32-collect-high-3-bits char-codes))
       (low-bit-codes (bech32-collect-low-5-bits char-codes)))
    (append high-bit-codes
            '(0)
            low-bit-codes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Splitting an address into the hrp and data portions

(define bech32-index-of-last-1 ((s stringp))
  :returns (idx) ; an exercise would be show this returns acl2::nat-optionp
  ;; It is too bad acl2::position doesn't support the :from-end keyword argument
  ;; like cl-user::position does and like acl2::search does.
  (search "1" s :from-end t))

; An alternative implementation could be to convert the address up front to a
; list of chars, process it, and convert the hrp part back to a string at the end.
(define bech32-split-address ((address stringp))
  :returns (mv (erp booleanp)
               (ret-hrp stringp
                        :hyp (stringp address))
               (data-octets
                (unsigned-byte-listp 5 data-octets)))
  :short "Split Bech32 address into hrp and data."
  :long
  (xdoc::topstring
   (xdoc::p
    "Splits the Bech32 or Bech32m address into the <b>human-readable portion</b>
     (@('hrp')) as a string and the <b>data portion</b> as a list of 5-bit bytes.")
    (xdoc::p
     "Also performs some validity checks."
     (xdoc::ul
      (xdoc::li "The overall string must not exceed 90 characters.  Since
                 none of the characters is allowed to be encoded using multiple
                 bytes, this means the string does not exceed 90 bytes.")
      (xdoc::li "There must be a @('#\\1' character) in the string.
                 The last @('#\\1') in the string separates the @('hrp') from
                 the data.")
      (xdoc::li "@('hrp-valid-p') makes sure the @('hrp') has at least one
                 character and no more than 83 characters, and the ASCII codes
                 of the characters must be in the range [33,126] inclusive.")
      (xdoc::li "The @('data') part must have at least 6 characters.")
      (xdoc::li "The characters in the @('data') part must be drawn from
                 @('qpzry9x8gf2tvdw0s3jn54khce6mua7l').")))
    (xdoc::p
     "There are three values returned: an error flag, the @('hrp') as a string
     or the empty string in the case of an error, and the @('data') as
     a list of 5-bit bytes or the empty list in the case of an error."))
  (b* (((unless (<= (length address) 90))
        (mv t "" nil))
       (separator-1 (bech32-index-of-last-1 address))
       ((unless (natp separator-1))
        (mv t "" nil))
       ;; There must be at least 6 characters in the data part,
       ;; but for proving the guards we just need at least 1 character after the #\1.
       ((unless (< separator-1 (- (length address) 1)))
        (mv t "" nil))
       (hrp (subseq address 0 separator-1))
       ((unless (hrp-valid-p hrp))
        (mv t "" nil))
       (data-string (subseq address (+ separator-1 1) (length address)))
       ((unless (<= 6 (length data-string)))
        (mv t "" nil))
       (data-chars (explode data-string))
       (data-octets-or-nils (bech32-chars-to-octets data-chars))
       ((unless (unsigned-byte-listp 5 data-octets-or-nils))
        (mv t "" nil)))
    (mv nil hrp data-octets-or-nils)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bech32-verify-checksum ((hrp stringp) (data (unsigned-byte-listp 8 data)))
  :returns (y/n booleanp)
  :short "Verifies a Bech32 checksum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that the last 6 bytes of @('data') are a correct Bech32 checksum
     of a string that is split into @('hrp') and @('data')."))
  (and (hrp-valid-p hrp)
       (<= 6 (len data))
       (warrant bvshr)
       (warrant bvand)
       (equal (bech32-polymod (append (bech32-hrp-expand hrp) data))
              1)))

(define bech32m-verify-checksum ((hrp stringp) (data (unsigned-byte-listp 8 data)))
  :returns (y/n booleanp)
  :short "Verifies a Bech32 checksum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that the last 6 bytes of @('data') are a correct Bech32m checksum
     of a string that is split into @('hrp') and @('data')."))
  (and (hrp-valid-p hrp)
       (<= 6 (len data))
       (warrant bvshr)
       (warrant bvand)
       (equal (bech32-polymod (append (bech32-hrp-expand hrp) data))
              *bech32m-const*)))

(define bech32-or-bech32m-verify-checksum ((hrp stringp)
                                           (data (unsigned-byte-listp 8 data)))
  :returns (y/n booleanp)
  :short "Verifies a Bech32 checksum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that the last 6 bytes of @('data') are a correct Bech32 or Bech32m
     checksum of a string that is split into @('hrp') and @('data').")
   (xdoc::p
    "Does not tell you whether a Bech32 or Bech32m checksum was found."))
  (and (hrp-valid-p hrp)
       (<= 6 (len data))
       (warrant bvshr)
       (warrant bvand)
       (let ((cksum (bech32-polymod (append (bech32-hrp-expand hrp) data))))
         (or (= cksum 1)
             (= cksum *bech32m-const*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A good addition to this book
; would be bech32-create-checksum and bech32m-create-checksum.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simple widening rule, so that return values from bech32-split-address can be
; used as arguments to bech32-verify-checksum and bech32m-verify-checksum.

(std::defrule unsigned-byte-list-5-is-8
  (implies (unsigned-byte-listp 5 x)
           (unsigned-byte-listp 8 x))
  :enable (unsigned-byte-listp unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test if address string is mixed case, which is explicitly disallowed.
; In this context "case" means only the letters a-z and A-Z.

(define mixed-case-stringp ((s stringp))
  :returns (y/n booleanp)
  ;; A mixed case string has at least one upper case letter
  ;; and at least one lower case letter.  That means the string
  ;; will change if you upcase it and it will change if you
  ;; downcase it.  If it doesn't change one or the other of those,
  ;; then it must not be mixed.
  (and (not (equal (str::upcase-string s) s))
       (not (equal (str::downcase-string s) s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top-level API to verify address checksum.

(define valid-bech32 ((address stringp))
  :returns (y/n booleanp)
  :short "Check if address is valid Bech32."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that @('address') is a valid Bech32 string.")
   (xdoc::p
    "Disallows a mixed-case string; then downcases the string before
     converting the data characters to bytes and verifying the checksum."))
  (b* (((when (mixed-case-stringp address)) nil)
       (address (str::downcase-string address))
       ((mv erp hrp data) (bech32-split-address address))
       ((when erp) nil))
    (bech32-verify-checksum hrp data)))

(define valid-bech32m ((address stringp))
  :returns (y/n booleanp)
  :short "Check if address is valid Bech32m."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that @('address') is a valid Bech32m string.")
   (xdoc::p
    "Disallows a mixed-case string; then downcases the string before
     converting the data characters to bytes and verifying the checksum."))
  (b* (((when (mixed-case-stringp address)) nil)
       (address (str::downcase-string address))
       ((mv erp hrp data) (bech32-split-address address))
       ((when erp) nil))
    (bech32m-verify-checksum hrp data)))

(define valid-bech32-or-bech32m ((address stringp))
  :returns (y/n booleanp)
  :short "Check if address is valid Bech32 or Bech32m."
  :long
  (xdoc::topstring
   (xdoc::p
    "Verifies that @('address') is a valid Bech32 or Bech32m string.
     Does not indicate which kind it is.")
   (xdoc::p
    "Disallows a mixed-case string; then downcases the string before
     converting the data characters to bytes and verifying the checksum."))
  (b* (((when (mixed-case-stringp address)) nil)
       (address (str::downcase-string address))
       ((mv erp hrp data) (bech32-split-address address))
       ((when erp) nil))
    (bech32-or-bech32m-verify-checksum hrp data)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
