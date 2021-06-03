; Keccak Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KECCAK")


;; ================================
;; Formal spec for Keccak hash functions.


;; --------------------------------
;; Introduction.

;; This file defines the Keccak family of permutations and sponge functions,
;; as well as 4 hash functions that were described in "The Keccak
;; SHA-3 submission", Version 3 [1], and defined in "The Keccak specification"
;; [2], before SHA-3 was finalized.

;; These functions are:
;;   KECCAK-224, KECCAK-256, KECCAK-384, KECCAK-512.

;; These correspond, respectively, to
;;   KECCAK-224: first 224 bits of Keccak[r = 1152, c = 448]
;;   KECCAK-256: first 256 bits of Keccak[r = 1088, c = 512]
;;   KECCAK-384: first 384 bits of Keccak[r = 832, c = 768]
;;   KECCAK-512: first 512 bits of Keccak[r = 576, c = 1024]
;; in the notation of the Keccak submission.

;; The finalized functions SHA-3-224, SHA-3-256, SHA-3-384, SHA-3-512
;; in FIPS 202, "SHA-3 Standard" [3] differ from these functions
;; only by appending the bits 01 to the message before calling Keccak.
;; For example, from FIPS 202 section 6.1:
;;   SHA3-256(M) = KECCAK[512] (M || 01, 256);

;; Since this difference is external to the Keccak routines,
;; and since FIPS 202 is the standard reference, we refer to
;; sections of FIPS 202 in this file.

;; In JavaScript-land [4] they call these pre-finalized functions
;; Keccak-224, Keccak-256, Keccak-384, and Keccak-512,
;; so we use the same names.
;; Keccak-256 became an integral part of Ethereum.

;; [1] The Keccak SHA-3 submission, version 3, January 14, 2011
;;     https://keccak.team/files/Keccak-submission-3.pdf
;; [2] The Keccak reference, version 3.0, January 14, 2011
;;     https://keccak.team/files/Keccak-reference-3.0.pdf
;; [3] SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions,
;;     NIST, http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
;; [4] http://emn178.github.io/online-tools/

;; As mentioned above, the SHA-3 hash functions are only slightly modified
;; from these functions.  They are formalized at the end of this file.


;; --------------------------------
;; Interfaces to the Keccak hash functions
;;
;; These hash functions come in the following varieties.
;;
;; 1. Each default function accepts and returns "bit strings",
;;    which we model by lists of bits.  Note that these
;;    functions allow inputs whose length is not a multiple of 8.
;;    The default bit-oriented functions are:
;;
;;      KECCAK-224, KECCAK-256, KECCAK-384, KECCAK-512.
;;
;; 2. Each byte-oriented function accepts and returns
;;    "hexadecimal strings with an even number of digits",
;;    which we model by lists of bytes.
;;    The byte-oriented functions are:
;;
;;      KECCAK-224-BYTES, KECCAK-256-BYTES, KECCAK-384-BYTES, KECCAK-512-BYTES
;;
;;    See these definitions for more details on endianness and the FIP 202
;;    specification.
;;
;; 3. Internally, the functions take a list of bits and return a bitvector
;;    represented as a large integer.  Those functions are exposed as:
;;
;;      KECCAK-224-BITS-TO-BV, KECCAK-256-BITS-TO-BV,
;;      KECCAK-384-BITS-TO-BV, KECCAK-512-BITS-TO-BV
;;
;; 4. In the keccak-tests.lisp file, we define string-oriented functions.


;; --------------------------------
;; Note on other Keccak-related functions.

;; There are other functions based on Keccak
;; (in addition to SHA-3) which are not defined here:
;;
;;   SHAKE128, SHAKE256 (in FIPS 202)
;;   cSHAKE, KMAC, TupleHash, ParallelHash, (in NIST SP 800-185)
;;   KangarooTwelve, (in http://keccak.noekeon.org/KangarooTwelve.pdf)
;;   Keyak, (in http://keyak.noekeon.org/Keyakv2-doc2.2.pdf)
;;   or Ketje (in http://ketje.noekeon.org/Ketjev2-doc2.0.pdf).
;;
;; Most but not all of these are hash functions.


;; --------------------------------
;; References

;; http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
;;  - Section 6 is where the standardized SHA3 functions
;;    are defined in terms of the Keccak algorithms.
;; http://keccak.noekeon.org/Keccak-reference-3.0.pdf [K-REF-3-0]
;;  - for more on keccak.

;; Ethereum currently (2017-07-15) uses Keccak-256, although
;; there are EIPs (Ethereum Improvement Proposal) to change this.
;; Note that the EVM's SHA3 instruction actually calls Keccak-256.
;; Ethereum also uses Keccak-512 for the Ethash proof-of-work algorithm.

;; http://emn178.github.io/online-tools
;;  - This is a site that computes all 8 variants of SHA3 hashes
;;    defined here and in sha-3.lisp, on byte-multiple inputs.
;;    You can enter the input interactively or by uploading a file.


;; --------------------------------
;; include-book statements

;; Note :
;; We model a Keccak "state string" (which we call k-string)
;; by a bitvector integer,
;; and a Keccak "state array" by a list of bitvector integers.
;; We convert between Keccak "state strings" and "state arrays"
;; using code from bvseq/packbv.lisp
;; This book also brings in other things we use like getbit.

(include-book "kestrel/bv-lists/packbv-def" :dir :system)
(include-book "kestrel/bv-lists/unpackbv-def" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits-little" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)

(include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system)

(include-book "kestrel/bv/defs-bitwise" :dir :system)
(include-book "kestrel/bv/bvshr-def" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)

(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)

(include-book "std/basic/two-nats-measure" :dir :system)

;; for string=>nats
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (include-book "kestrel/bv-lists/packbv-and-unpackbv" :dir :system)) ;for unpackbv-of-packbv


;; --------
;; Library theorems

; TODO: move
(defthm all-unsigned-byte-p-of-chars=>nats
  (all-unsigned-byte-p 8 (chars=>nats str))
  :hints (("Goal" :in-theory (enable chars=>nats))))

; TODO: move
(defthm all-unsigned-byte-p-of-string=>nats
  (all-unsigned-byte-p 8 (string=>nats str))
  :hints (("Goal" :in-theory (enable string=>nats))))


;; --------
;; Bit lists

;; For compatiblity with the bit vector library we introduce the following rule,
;; which turns bit-listp into the true-listp and all-unsigned-byte-p,
;; which is the form used by the bit vector library.

(defthm bit-listp-alt-def
  (equal (bit-listp x)
         (and (true-listp x)
              (all-unsigned-byte-p 1 x)))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable bit-listp))))


;; --------------------------------
;; Parameters of the hashing algorithms.

;; The Keccak algorithms have a number of parameters.
;; Here is some information about where they are used
;; and their allowed values.

;; b - the width of the data in the Keccak-f permutation.
;;     b in {25, 50, 100, 200, 400, 800, 1600}.
;; Variables dependent on b:
;;   * w = b / 25, the width of a "lane", so
;;     w in {1, 2, 4, 8, 16, 32, 64}
;;   * l = log2(w), so
;;     l in {0, 1, 2, 3, 4, 5, 6}
;;   * nr = 12 + 2l, the number of rounds, so
;;     nr in {12, 14, 16, 18, 20, 22, 24}
;; See Table 1 in Section 3.1 of FIPS 202 for the range of b,
;; and for the definition and ranges of w and l;
;; the definition of nr is in Section 3.4.
;; All of the top-level hashing functions defined here
;; use b = 1600, w = 64, l = 6, nr = 24.
;; We have attempted to leave b as a parameter as much as possible
;; so that later keccak-based functions using a different b will
;; be easier to define.

;; r - the "bitrate".  r < b.
;; Variables dependent on r:
;;   * c, the "capacity": c = b - r.
;; This varies with the top-level hashing function.
;; From http://keccak.noekeon.org/specs_summary.html :
;; hash fn                r    c  output #bits
;; --------             ---- ---- ------------
;; SHA3-224/Keccak-224  1152  448    224
;; SHA3-256/Keccak-256  1088  512    256
;; SHA3-384/Keccak-384   832  768    384
;; SHA3-512/Keccak-512   576 1024    512

;; Here are some constants with the relations between
;; b, w, l, and nr.

;; Allowable values of b.
(defconst *k-b-vals* '(25 50 100 200 400 800 1600))

;; Allowable values of w
(defconst *k-w-vals* '(1 2 4 8 16 32 64))

(defund k-w-val-p (w)
  (declare (xargs :guard t))
  (member w *k-w-vals*))

(defthm k-w-val-p-forward-to-posp
  (implies (k-w-val-p w)
           (posp w))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-w-val-p))))

;; These constants are not used, but are shown here for reference.
;;
;; (defconst *k-b-to-w*
;;   '((25 . 1) (50 . 2) (100 . 4) (200 . 8) (400 . 16) (800 . 32) (1600 . 64)))
;;
;; (defconst *k-b-to-nr*
;;   '((25 . 12) (50 . 14) (100 . 16) (200 . 18) (400 . 20) (800 . 22) (1600 . 24)))

(defconst *k-w-to-l*
  '((1 . 0) (2 . 1) (4 . 2) (8 . 3) (16 . 4) (32 . 5) (64 . 6)))


;; ================================
;; Section-by-section implementation of spec.

;; Naming:
;; "k-" prefix means "Keccak", the algorithm underlying SHA-3.
;; "bitstring" is a list of bits used as input to the main
;;   hash functions
;; "k-string" is an integer bitvector used to represent a Keccak state string

;; "k-w-" prefix means "w-bit lane", for w in {1,2,4,8,16,32,64}. (spec: 3.1)
;; There are 25 lanes, so the whole state is b = 25w bits;
;;   b in {25,50,100,200,400,800,1600}.
;; l = log2(w), so l in {0,1,2,3,4,5,6}  (spec: 3.1)


;; ----------------
;; Quoting from spec:
;; 3. KECCAK-p PERMUTATIONS
;;
;; In this section, the KECCAK-p permutations are specified, with two
;; parameters: 1) the fixed length of the strings that are permuted, called the
;; width of the permutation, and 2) the number of iterations of an internal
;; transformation, called a round. The width is denoted by b, and the number of
;; rounds is denoted by nr. The KECCAK-p permutation with nr rounds and width b
;; is denoted by KECCAK-p[b, nr]; the permutation is defined for any b in {25,
;; 50, 100, 200, 400, 800, 1600} and any positive integer nr.

;; A round of a KECCAK-p permutation, denoted by Rnd, consists of a sequence of
;; five transformations, which are called the step mappings. The permutation is
;; specified in terms of an array of values for b bits that is repeatedly
;; updated, called the state; the state is initially set to the input values of
;; the permutation.
;;
;; The notation and terminology for the state are described in Sec. 3.1. The
;; step mappings are specified in Sec. 3.2. The KECCAK-p permutations,
;; including the round function Rnd, are specified in Sec. 3.3. The
;; relationship of the KECCAK-p permutations to the KECCAK-f permutations that
;; were defined for KECCAK in [8] is described in Sec. 3.4.


;; ----------------
;; (spec 3.1)
;; There are two representations of the state for the KECCAK-p[b,nr]
;; permutation: b-bit strings and 5-by-5-by-w arrays of bits.
;; We call these k-strings and state-arrays.
;; For k-strings:
;;    We use a big integer (unsigned-byte).
;;    We index into the state string using getbit.
;;    This means the #b form shows the bits in opposite order than
;;    you get from listing the bits with increasing index.
;;    I.e., #b1100 is equivalent bit vector [0,0,1,1].
;; For state-arrays:
;;    Since we use (unpackbv ..) to convert a Keccak state string (integer)
;;    to a Keccak state array (list of integers), the indexing into
;;    the list is backwards from what one might think.
;;    Instead of the lane index being (+ x (* y 5)), it is (- 24 (+ x (* y 5))).

;; Answers the question:
;;   Is k-string the string representation of a Keccak state (of b bits)?
(defund k-string-p (b k-string)
  (declare (type (integer 0 *) b))
  (unsigned-byte-p b k-string))

(defthm k-string-p-forward-to-integerp
  (implies (k-string-p b k-string)
           (integerp k-string))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-string-p))))

;; Returns the bit at position i of the k-string representation of a Keccak state.
(defun k-S (b k-string i)
  (declare (type (integer 1 *) b)
           (type (integer 0 *) i)
           (xargs :guard (k-string-p b k-string)))
  (if (>= i b)
      nil
    (getbit i k-string)))

;; Answers the question:
;;   Is k-lane a valid representation of a w-wide lane?
;; Note that this is the same definition as k-string-p as we currently represent
;; k-string and k-lane.
(defund k-lane-p (w k-lane)
  (declare (xargs :guard (k-w-val-p w)))
  (unsigned-byte-p w k-lane))

(defthm k-lane-p-forward-to-integerp
  (implies (k-lane-p w k-lane)
           (integerp k-lane))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-lane-p))))

;; Justifies using 0 as an accumulator for a k-lane.
(defthm k-lane-p-of-0
  (implies (natp w)
           (k-lane-p w 0))
  :hints (("Goal" :in-theory (enable k-lane-p))))

;; Check that LANES is a true-list of k-lanes, each of width W.
(defun k-lane-list-p (w lanes)
  (declare (xargs :guard (k-w-val-p w)))
  (if (not (consp lanes))
      (equal nil lanes)
    (and (k-lane-p w (first lanes))
         (k-lane-list-p w (rest lanes)))))

(defthm k-lane-list-p-forward-to-true-listp
  (implies (k-lane-list-p w lanes)
           (true-listp lanes))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-lane-list-p))))

(defthm k-lane-list-p-forward-to-all-integerp
  (implies (k-lane-list-p w lanes)
           (all-integerp lanes))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-lane-list-p k-lane-p))))

(defthm k-lane-list-p-forward-to-all-unsigned-byte-p
  (implies (k-lane-list-p w lanes)
           (all-unsigned-byte-p w lanes))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable k-lane-list-p k-lane-p))))

(defthm integerp-of-nth-when-k-lane-list-p
  (implies (and (k-lane-list-p w lanes) ;w is a free var
                (< n (len lanes))
                (natp n))
           (integerp (nth n lanes)))
  :hints (("Goal" :in-theory (enable k-lane-p))))

(defthm k-lane-p-of-nth-when-k-lane-list-p
  (implies (k-lane-list-p w lanes)
           (equal (k-lane-p w (nth n lanes))
                  (< (nfix n) (len lanes))))
  :hints (("Goal" :in-theory (e/d (nth) (acl2::nth-of-cdr)))))

(defthm k-lane-list-p-of-reverse-list
  (equal (k-lane-list-p w (reverse-list x))
         (k-lane-list-p w (true-list-fix x)))
  :hints (("Goal" :in-theory (enable reverse-list))))

;; We represent the Keccak "state array" as a list of 25 lanes.
;; w is the "width", i.e., the number of bits in a lane.
(defund k-state-array-p (w state-array)
  (declare (xargs :guard (k-w-val-p w)))
  (and (k-lane-list-p w state-array)
       (= 25 (len state-array))))

(defthm integerp-of-nth-when-k-state-array-p
  (implies (and (k-state-array-p w lanes) ;w is a free var
                (< n (len lanes))
                (natp n))
           (integerp (nth n lanes)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

(defthm len-when-k-state-array-p
  (implies (k-state-array-p w lanes) ;w is a free var
           (equal (len lanes)
                  25))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

(defthm k-state-array-p-of-reverse-list
  (equal (k-state-array-p w (reverse-list x))
         (k-state-array-p w (true-list-fix x)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

(defun k-lane (w state-array x y)
  (declare (type (integer 0 4) x y)
           (type (integer 1 *) w)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))
                  :guard-hints (("Goal" :in-theory (enable k-state-array-p))))
           (ignore w))
  ;; As explained above, the list of lanes is in reverse order.
  (nth (- 24 (+ x (* y 5))) state-array))

(defthm k-lane-p-of-k-lane
  (implies (and (natp x)
                (natp y)
                (<= 0 x)
                (<= 0 y)
                (k-state-array-p w state-array))
           (k-lane-p w (k-lane w state-array x y)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

;; Returns the bit at A(x,y,z), where z is the index into the lane.
(defun k-A (w state-array x y z)
  (declare (type (integer 0 4) x y)
           (type (integer 0 *) w z)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))
                  :guard-hints (("Goal" :in-theory (enable k-state-array-p)))))
  (let ((lane (k-lane w state-array x y)))
    (getbit z lane)))

(defthm k-A-returns-bit
  (bitp (k-A w state-array x y z)))


;; ----------------
;; (spec 3.1.1) Parts of the state array.

;; Lane is defined above.
;; Plane is defined here.

;; As needed: add definitions of slice, sheet, row, column.

;; Note, as with the Keccak state array, we have the larger indexes on the left.
;; It doesn't look like planes are used for much in the Keccak algorithm.
;; Let's pack it into a bitvector so that it is easier to test in 3.1.3.
(defun k-plane (w state-array y)
  (declare (type (integer 0 4) y)
           (type (integer 1 *) w)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))
                  :guard-hints (("Goal" :in-theory (enable k-state-array-p)))))
  (packbv 5 w (list (k-lane w state-array 4 y)
                    (k-lane w state-array 3 y)
                    (k-lane w state-array 2 y)
                    (k-lane w state-array 1 y)
                    (k-lane w state-array 0 y))))


;; ----------------
;; (spec 3.1.2)
;; Converting (Keccak state) Strings to Arrays

;; Turns a Keccak state string (a big integer bitvector) into an array of lanes
;; (the array is implemented as a list, and each lane is an integer bitvector).
;; Reminder: b=25*w is the total number of bits in the string or 3d matrix;
;;   w is the width of a single lane.  There are always 25 lanes.
(defund k-string-to-state-array (w k-string)
  (declare (type (integer 1 *) w)
           (xargs :guard (k-string-p (* 25 w) k-string)))
  (unpackbv 25 w k-string))

(defthm k-state-array-p-of-k-string-to-state-array
  (implies (and (k-string-p (* 25 w) k-string)
                (natp w))
           (k-state-array-p w (k-string-to-state-array w k-string)))
  :hints (("Goal" :in-theory (enable k-state-array-p
                                     k-lane-p
                                     k-string-to-state-array
                                     acl2::unpackbv-opener))))

(defthm len-of-k-string-to-state-array
  (equal (len (k-string-to-state-array w k-string))
         25)
  :hints (("Goal" :in-theory (enable k-string-to-state-array))))

;; Consistency theorem.
;; Show that our conversion from state string to state array
;; preserves the contents.
;; For every valid x,y,z, w, and k-string (state string), we show that
;; finding the value at a position in the k-string
;; yields the same result as finding the value at the corresponding
;; position in the state array computed from the k-string.
;; I.e., A[x, y, z] = S[w(5y+x)+z].

(defthmd k-spec-3-1-2-consistency
  (implies (and (natp x) (natp y) (natp z)
                (< x 5) (< y 5) (< z w) (k-w-val-p w)
                (k-string-p b k-string))
           (= (k-A w (k-string-to-state-array w k-string)
                   x y z)
              (k-S (* 25 w)
                   k-string
                   (+ (* w (+ x (* 5 y))) z))))
  :hints (("Goal" :in-theory (enable packbv unpackbv
                                     k-string-to-state-array k-w-val-p))))


;; ----------------
;; (spec 3.1.3)
;; Converting (Keccak state) Arrays to Strings

(defund k-state-array-to-string (w state-array)
  (declare (type (integer 1 *) w)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))
                  :guard-hints (("Goal" :in-theory (enable k-state-array-p)))))
  (packbv 25 w state-array))

(defthm k-string-p-of-k-state-array-to-string
  (implies (and (equal b (* 25 w))
                (natp w)
                (k-state-array-p w state-array))
           (k-string-p b (k-state-array-to-string w state-array)))
  :hints (("Goal" :in-theory (enable k-state-array-to-string k-string-p))))

;; Note: k-lane and k-plane defined above in 3.1.1

;; (k-plane ..) is defined on state-array.
;; Define an equivalent function on k-string.
(defun k-plane-from-k-string (b k-string w y)
  (declare (type (integer 1 *) b w)
           (type (integer 0 4) y)
           (xargs :guard (k-string-p b k-string))
           (ignore b))
  (slice (- (* (* 5 w) (+ y 1)) 1)
         (* (* 5 w) y)
         k-string))

;; Prove k-plane and k-plane-from-k-string get the same result.
(defthm k-plane-of-state-array-is-k-plane-from-k-string
  (implies (and (k-w-val-p w)
                (natp y) (< y 5)  ;; y is the plane number
                (k-string-p (* 25 w) k-string))
           (let ((state-array (k-string-to-state-array w k-string)))
             (equal (k-plane-from-k-string (* 25 w) k-string w y)
                    (k-plane w state-array y))))
  :hints (("Goal" :in-theory (enable packbv unpackbv
                                     k-string-to-state-array k-w-val-p))))

;; Prove this assertion from the spec:
;;   S = Plane (0) || Plane (1) || Plane (2) || Plane (3) || Plane (4)
;; Again, we index backwards because that's how bitvector packing works.
(defthmd k-string-is-concatenation-of-planes
  (implies (and (k-w-val-p w)
                (natp y) (< y 5)  ;; y is the plane number
                (k-string-p (* 25 w) k-string))
           (let ((state-array (k-string-to-state-array w k-string)))
             (equal (packbv 5 (* 5 w)
                            (list (k-plane w state-array 4)
                                  (k-plane w state-array 3)
                                  (k-plane w state-array 2)
                                  (k-plane w state-array 1)
                                  (k-plane w state-array 0)))
                    k-string)))
  :hints (("Goal" :in-theory (enable packbv unpackbv
                                     k-string-to-state-array
                                     k-w-val-p k-string-p))))

;; ----------------
;; Extra (not in spec) theorems relating (Keccak state) strings and arrays.

(defthmd k-string-to-array-and-back
  (implies (and (k-w-val-p w)
                (k-string-p (* 25 w) k-string))
           (equal (k-state-array-to-string
                   w
                   (k-string-to-state-array w k-string))
                  k-string))
  :hints (("Goal" :in-theory (enable packbv unpackbv
                                     k-string-to-state-array
                                     k-state-array-to-string
                                     k-string-p
                                     acl2::unpackbv-opener))))

(defthmd k-state-array-to-string-and-back
  (implies (and (k-w-val-p w)
                (k-state-array-p w state-array))
           (equal (k-string-to-state-array
                   w (k-state-array-to-string w state-array))
                  state-array))
  :hints (("Goal"
           :in-theory (enable packbv unpackbv
                              k-state-array-p
                              k-string-to-state-array
                              k-state-array-to-string))))


;; ----------------
;; (spec: 3.1.4)
;; This section basically says that the x and y indexes are permuted in
;; the following diagrams.
;; Above, x and y were in numerical order [0,1,2,3,4] (or backwards,
;;   depending on which way you look.)
;; Here, it shows x and y in this order: [3,4,0,1,2]
;; This only a diagrammatic and visualization issue ---
;; it is not a definitional part of the spec, since the spec
;; deals with indices and
;; does not define an "adjacent lane" concept.



;; ----------------
;; (spec: 3.2)
;; Step Mappings

;; Quoting from spec:

;; The five step mappings that comprise a round of KECCAK-p[b, nr] are denoted by
;; theta, rho, pi, chi, and iota. Specifications for these functions are given in
;; Secs. 3.2.1-3.2.5.

;; The algorithm for each step mapping takes a state array, denoted by A, as an
;; input and returns an updated state array, denoted by A', as the output. The
;; size of the state is a parameter that is omitted from the notation, because b
;; is always specified when the step mappings are invoked.

;; The iota step mapping has a second input: an integer called the round index,
;; denoted by ir, which is defined within Algorithm 7 for KECCAK-p[b, nr], in
;; Sec. 3.3. The other step mappings do not depend on the round index.


;; ----------------
;; (spec: 3.2.1)
;; Specification of theta

;; A C-array is a list (indexed by x coordinates) of 5 k-lanes. Each lane has
;; width w, with individual bits in a lane indexed by z coordinates.
;; This is the type of C in Step 1; note that C is a plane.
(defund C-array-p (w c-array)
  (declare (xargs :guard (k-w-val-p w)))
  (and (k-lane-list-p w c-array)
       (= 5 (len c-array))))

;; Finds the parity of the column at (x, ..., z).
;; This calculates C[x,z] in Step 1.
(defund k-theta-C-column-parity (w state-array x z)
  (declare (type (integer 0 4) x)
           (type (integer 0 *) z)
           (type (integer 1 *) w)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (bitxor (k-A w state-array x 0 z)
          (bitxor (k-A w state-array x 1 z)
                  (bitxor (k-A w state-array x 2 z)
                          (bitxor (k-A w state-array x 3 z)
                                  (k-A w state-array x 4 z))))))

(defthm k-theta-C-column-parity-returns-bit
  (implies (k-state-array-p w state-array)
           (bitp (k-theta-C-column-parity w state-array x z)))
  :hints (("Goal" :in-theory (enable k-theta-C-column-parity))))

;; Update bits z through w-1 of LANE-ACC (which is initially zero),
;; yielding lane x of C, in Step 1.
;; This function is called with z = 0 to update the whole lane.
(defund make-k-theta-c-lane-aux (z x w state-array lane-acc)
  (declare (type (integer 0 *) z)
           (type (integer 0 4) x)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array)
                              (<= z w)
                              (k-lane-p w lane-acc))
                  :guard-hints (("Goal" :in-theory (enable k-lane-p)))
                  :measure (nfix (- w z))))
  (if (or (not (mbt (and (natp z)
                         (natp w))))
          (<= w z))
      lane-acc
    (let ((lane-acc
           (putbit w z (k-theta-C-column-parity w state-array x z) lane-acc)))
      (make-k-theta-c-lane-aux (+ 1 z) x w state-array lane-acc))))

(defthm k-lane-p-of-make-k-theta-c-lane-aux
  (implies (k-lane-p w lane-acc)
           (k-lane-p w (make-k-theta-c-lane-aux z x w state-array lane-acc)))
  :hints (("Goal" :in-theory (enable make-k-theta-c-lane-aux k-lane-p))))

;; Make lane x of C, in Step 1.
(defund make-k-theta-c-lane (x w state-array)
  (declare (type (integer 0 4) x)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (make-k-theta-c-lane-aux 0 x w state-array 0))

(defthm k-lane-p-of-make-k-theta-c-lane
  (implies (natp w)
           (k-lane-p w (make-k-theta-c-lane x w state-array)))
  :hints (("Goal" :in-theory (enable make-k-theta-c-lane))))

;; Make the suffix of C containing lanes x through 4, in Step 1.
;; This function is called with x = 0 to make the whole C.
(defun k-theta-make-c-aux (x w state-array)
  (declare (type (integer 0 5) x)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))
                  :measure (nfix (- 5 x))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (make-k-theta-c-lane x w state-array)
          (k-theta-make-c-aux (+ 1 x) w state-array))))

(defthm k-lane-list-p-of-k-theta-make-c-aux
  (implies (natp w)
           (k-lane-list-p w (k-theta-make-c-aux x w state-array))))

(defthm len-of-k-theta-make-c-aux
  (implies (and (natp x)
                (<= x 5))
           (equal (len (k-theta-make-c-aux x w state-array))
                  (- 5 x))))

(defthm C-array-p-of-k-theta-make-c-aux
  (implies (natp w)
           (C-array-p w (k-theta-make-c-aux 0 w state-array)))
  :hints (("Goal" :in-theory (enable C-array-p))))

;; Make C, in Step 1.
(defund k-theta-make-c (w state-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (k-theta-make-c-aux 0 w state-array))

(defthm C-array-p-of-k-theta-make-c
  (implies (natp w)
           (C-array-p w (k-theta-make-c w state-array)))
  :hints (("Goal" :in-theory (enable k-theta-make-c))))

;; Return C[x,z] from C.
(defund k-theta-C (w C-array x z)
  (declare (type (integer 0 4) x)
           (type (integer 0 *) z)
           (type (integer 1 *) w)
           (xargs :guard (and (k-w-val-p w)
                              (C-array-p w C-array))
                  :guard-hints (("Goal" :in-theory (enable C-ARRAY-P))))
           (ignore w))
  (let ((lane (nth x C-array)))
    (getbit z lane)))

(defthm k-theta-C-returns-bit
  (bitp (k-theta-C w C-array x z)))

;; A D-array is a list (indexed by x coordinates) of 5 k-lanes. Each lane has
;; width w, with individual bits in a lane indexed by z coordinates.
;; This is the type of D in Step 2; note that D is a plane.
(defund D-array-p (w d-array)
  (declare (xargs :guard (k-w-val-p w)))
  (and (k-lane-list-p w d-array)
       (= 5 (len d-array))))

;; Update bits z through w-1 of LANE-ACC (which is initially zero),
;; yielding lane x of D, in Step 2.
;; This function is called with z = 0 to update the whole lane.
(defund make-k-theta-d-lane-aux (z x w C-array lane-acc)
  (declare (type (integer 0 *) z)
           (type (integer 0 4) x)
           (xargs :guard (and (k-w-val-p w)
                              (c-array-p w C-array)
                              (<= z w)
                              (unsigned-byte-p w lane-acc))
                  :measure (nfix (- w z))))
  (if (or (not (mbt (and (natp z)
                         (natp w))))
          (<= w z))
      lane-acc
    (let* ((val (bitxor (k-theta-C w C-array (mod (- x 1) 5) z)
                        (k-theta-C w C-array (mod (+ x 1) 5) (mod (- z 1) w))))
           (lane-acc (putbit w z val lane-acc)))
      (make-k-theta-d-lane-aux (+ 1 z) x w C-array lane-acc))))

(defthm k-lane-p-of-make-k-theta-d-lane-aux
  (implies (k-lane-p w lane-acc)
           (k-lane-p w (make-k-theta-d-lane-aux z x w c-array lane-acc)))
  :hints (("Goal" :in-theory (enable make-k-theta-d-lane-aux k-lane-p))))

;; Make lane x of D, in Step 2.
(defund make-k-theta-d-lane (x w c-array)
  (declare (type (integer 0 4) x)
           (xargs :guard (and (k-w-val-p w)
                              (c-array-p w c-array))))
  (make-k-theta-d-lane-aux 0 x w c-array 0))

(defthm k-lane-p-of-make-k-theta-d-lane
  (implies (natp w)
           (k-lane-p w (make-k-theta-d-lane x w c-array)))
  :hints (("Goal" :in-theory (e/d (make-k-theta-d-lane) ()))))

;; Make the suffix of D containing lanes x through 4, in Step 2.
;; This function is called with x = 0 to make the whole D.
(defun k-theta-make-d-aux (x w c-array)
  (declare (type (integer 0 5) x)
           (xargs :guard (and (k-w-val-p w)
                              (c-array-p w c-array))
                  :measure (nfix (- 5 x))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (make-k-theta-d-lane x w c-array)
          (k-theta-make-d-aux (+ 1 x) w c-array))))

(defthm k-lane-list-p-of-k-theta-make-d-aux
  (implies (natp w)
           (k-lane-list-p w (k-theta-make-d-aux x w c-array))))

(defthm len-of-k-theta-make-d-aux
  (implies (and (natp x)
                (<= x 5))
           (equal (len (k-theta-make-d-aux x w c-array))
                  (- 5 x))))

(defthm d-array-p-of-k-theta-make-d-aux
  (implies (natp w)
           (d-array-p w (k-theta-make-d-aux 0 w c-array)))
  :hints (("Goal" :in-theory (enable d-array-p))))

;; Make D, in Step 2.
(defund k-theta-make-d (w c-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (c-array-p w c-array))))
  (k-theta-make-d-aux 0 w c-array))

(defthm d-array-p-of-k-theta-make-d
  (implies (natp w)
           (d-array-p w (k-theta-make-d w c-array)))
  :hints (("Goal" :in-theory (enable k-theta-make-d))))

;; Get lane x of D (a bit vector indexed by z values).
(defund k-theta-D-lane (w D-array x)
  (declare (type (integer 0 4) x)
           (xargs :guard (and (k-w-val-p w)
                              (D-array-p w D-array))
                  :guard-hints (("Goal" :in-theory (enable D-array-p))))
           (ignore w))
  (nth x D-array))

(defthm k-lane-p-of-k-theta-D-lane
  (implies (and (natp x)
                (< x 5)
                (natp w)
                (D-array-p w d-array))
           (k-lane-p w (k-theta-D-lane w d-array x)))
  :hints (("Goal" :in-theory (enable k-theta-D-lane D-array-p))))

(defthm integerp-of-k-theta-D-lane
  (implies (and (natp x)
                (< x 5)
                (natp w)
                (D-array-p w d-array))
           (integerp (k-theta-D-lane w d-array x)))
  :hints (("Goal" :in-theory (enable k-theta-D-lane D-array-p))))

;; Returns the lane for A' at (x,y), in Step 3.
;; From the spec:  A'[x,y,z] = A[x,y,z] XOR D[x,z].
;; If we fix x and y, then we see that the new lane for A'[x,y] is
;; the old lane for A[x,y] XOR'ed with the lane for D[x].
(defund k-theta-combine-lanes (w state-array D-array x y)
  (declare (type (integer 0 4) x)
           (type (integer 0 4) y)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array)
                              (D-array-p w D-array))
                  :guard-hints (("Goal" :in-theory (enable D-array-p)))))
  (let ((A-lane (k-lane w state-array x y))
        (D-lane (k-theta-D-lane w D-array x)))
    (bvxor w A-lane D-lane)))

(defthm k-lane-p-of-k-theta-combine-lanes
  (implies (natp w)
           (k-lane-p w (k-theta-combine-lanes w state-array D-array x y)))
  :hints (("Goal" :in-theory (enable k-theta-combine-lanes k-lane-p))))

;; Iterates through x and y (y-major) to calculate the lanes of
;; the A' state array in Step 3.  This is called with x = y = 0.
(defun k-theta-aux (w state-array D-array x y)
  (declare (type (integer 0 4) x)
           (type (integer 0 5) y)
           (xargs :measure (two-nats-measure (- 5 y) (- 5 x))
                  :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array)
                              (D-array-p w D-array))))
  (if (not (and (natp w)
                (natp x) (< x 5)
                (natp y) (< y 5)))
      nil
    ;; y-major
    (let ((new-x (if (= (+ x 1) 5) 0 (+ x 1)))
          (new-y (if (= (+ x 1) 5) (+ y 1) y)))
      (cons (k-theta-combine-lanes w state-array D-array x y)
            (k-theta-aux w
                         state-array
                         D-array
                         new-x
                         new-y)))))

(defthm k-lane-list-p-of-k-theta-aux
  (implies (natp w)
           (k-lane-list-p w (k-theta-aux w state-array D-array x y))))

(defthm len-of-k-theta-aux
  (implies (and (natp x)
                (natp y)
                (<= y 5)
                (<= x 4)
                (natp w))
           (equal (len (k-theta-aux w state-array D-array x y))
                  (if (equal y 5)
                      0
                    (+ (* 5 (- 4 y))
                       (- 5 x)))))
  :hints (("Goal" :induct (k-theta-aux w state-array D-array x y))))

(defthm k-state-array-p-of-k-theta-aux
  (implies (natp w)
           (k-state-array-p w (k-theta-aux w state-array D-array 0 0)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

;; Returns the A' Keccak state array that is the output of theta.
(defun k-theta (w state-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (let* ((C-array (k-theta-make-C w state-array)) ; Step 1
         (D-array (k-theta-make-D w C-array))) ; Step 2
    ;; Because we want index (0,0) on the right, we need to reverse this.
    ;; (The alternative is to make the indexes go the other way in k-theta-aux.)
    (reverse-list (k-theta-aux w state-array D-array 0 0)))) ; Step 3

(defthm k-state-array-p-of-k-theta
  (implies (natp w)
           (k-state-array-p w (k-theta w state-array))))


;; ----------------
;; (spec: 3.2.2)
;; Specification of rho

;; The procedural description using assignments to A' is not
;; straightforward to implement in ACL2.
;; More straightforward is to use the offsets in Table 2
;; to construct the new Keccak state array in order of
;; the indexes.

;; Store the constants in Table 2, but in the
;; same (x,y) order as the lanes in a state-array.
;; In other words, starting at the right and
;; incrementing leftward, y-major.
(defconst *offsets-of-rho*
  ;;        x
  ;;  4   3   2   1   0
  ;;  -   -   -   -   -
  '( 78 120 253  66 210   ; 4
    136  21  15  45 105   ; 3
    231 153 171  10   3   ; 2  y
    276  55   6 300  36   ; 1
    91   28 190   1   0)) ; 0

(defund k-rho-offset (x y)
  (declare (type (integer 0 4) x y))
  (nth (- 24 (+ x (* y 5))) *offsets-of-rho*))

(defthm natp-of-k-rho-offset
  (implies (and (natp x)
                (natp y)
                (<= x 4)
                (<= y 4))
           (natp (k-rho-offset x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable k-rho-offset acl2::nth-of-cons))))

;; Iterates through x and y (y-major) to rotate each lane
;; by the offset in Table 2.  This is called with x = y = 0.
(defun k-rho-aux (w state-array x y)
  (declare (type (integer 0 4) x)
           (type (integer 0 5) y)
           (xargs :measure (two-nats-measure (- 5 y) (- 5 x))
                  :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (if (not (and (natp x) (< x 5)
                (natp y) (< y 5)))
      nil
    ;; y-major
    (let ((new-x (if (= (+ x 1) 5) 0 (+ x 1)))
          (new-y (if (= (+ x 1) 5) (+ y 1) y)))
      (cons (leftrotate w (mod (k-rho-offset x y) w) (k-lane w state-array x y))
            (k-rho-aux w state-array new-x new-y)))))

(defthm k-lane-list-p-of-k-rho-aux
  (implies (natp w)
           (k-lane-list-p w (k-rho-aux w state-array x y)))
  :hints (("Goal" :in-theory (enable k-lane-p))))

(defthm len-of-k-rho-aux
  (implies (and (natp x)
                (natp y)
                (<= y 5)
                (<= x 4)
                (natp w))
           (equal (len (k-rho-aux w state-array x y))
                  (if (equal y 5)
                      0
                    (+ (* 5 (- 4 y))
                       (- 5 x)))))
  :hints (("Goal" :induct (k-rho-aux w state-array x y))))

(defthm k-state-array-p-of-k-rho-aux
  (implies (natp w)
           (k-state-array-p w (k-rho-aux w state-array 0 0)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

;; Returns the A' Keccak state array that is the output of rho.
(defund k-rho (w state-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  ;; See comment on k-theta.  The reverse is here for the same reason.
  (reverse-list (k-rho-aux w state-array 0 0)))

(defthm k-state-array-p-of-k-rho
  (implies (natp w)
           (k-state-array-p w (k-rho w state-array)))
  :hints (("Goal" :in-theory (enable k-rho))))


;; ----------------
;; (spec: 3.2.3)
;; Specification of pi

;; From the spec:
;;   A'[x, y, z] = A[(x + 3y) mod 5, x, z]
;; Note that z is unchanged.  Therefore we can
;; move lanes around; we don't need to index into any lane.

;; Iterates through x and y (y-major) to calculate the lanes of
;; the A' state array in Step 1.  This is called with x = y = 0.
(defun k-pi-aux (w state-array x y)
  (declare (xargs :measure (two-nats-measure (- 5 y) (- 5 x))
                  :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (if (not (and (natp x) (< x 5)
                (natp y) (< y 5)))
      nil
    ;; y-major
    (let ((new-x (if (= (+ x 1) 5) 0 (+ x 1)))
          (new-y (if (= (+ x 1) 5) (+ y 1) y)))
      (cons (k-lane w state-array (mod (+ x (* 3 y)) 5) x)
            (k-pi-aux w state-array new-x new-y)))))

(defthm k-lane-list-p-of-k-pi-aux
  (implies (and (natp w)
                (k-state-array-p w state-array))
           (k-lane-list-p w (k-pi-aux w state-array x y)))
  :hints (("Goal" :in-theory (disable k-lane))))

(defthm len-of-k-pi-aux
  (implies (and (natp x)
                (natp y)
                (<= y 5)
                (<= x 4)
                (natp w))
           (equal (len (k-pi-aux w state-array x y))
                  (if (equal y 5)
                      0
                    (+ (* 5 (- 4 y))
                       (- 5 x)))))
  :hints (("Goal" :induct (k-pi-aux w state-array x y))))

(defthm k-state-array-p-of-k-pi-aux
  (implies (and (natp w)
                (k-state-array-p w state-array))
           (k-state-array-p w (k-pi-aux w state-array 0 0)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

;; Returns the A' Keccak state array that is the output of pi.
(defund k-pi (w state-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  ;; See comment on k-theta.  The reverse is here for the same reason.
  (reverse-list (k-pi-aux w state-array 0 0)))

(defthm k-state-array-p-of-k-pi
  (implies (and (natp w)
                (k-state-array-p w state-array))
           (k-state-array-p w (k-pi w state-array)))
  :hints (("Goal" :in-theory (enable k-pi))))


;; ----------------
;; (spec: 3.2.4)
;; Specification of chi

;; From the spec:
;;   A'[x,y,z] = A[x,y,z] XOR
;;              ((A[(x+1) mod 5, y, z] XOR 1) AND A[(x+2) mod 5, y, z])
;; Note that each bit in a given lane is processed in the same way, so we
;; can do bitvector operations on lanes rather than going down to bits.

;; Calculates lane (x,y) of A' in Step 1.
;; Note that (b XOR 1) = (NOT b), so we use BVNOT below.
(defun k-chi-combine-lanes (w state-array x y)
  (declare (type (integer 0 4) x y)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (bvxor w
         (k-lane w state-array x y)
         (bvand w
                (bvnot w (k-lane w state-array (mod (+ x 1) 5) y))
                (k-lane w state-array (mod (+ x 2) 5) y))))

;; Iterates through x and y (y-major) to calculate the lanes of
;; the A' state array in Step 1.  This is called with x = y = 0.
(defun k-chi-aux (w state-array x y)
  (declare (xargs :measure (two-nats-measure (- 5 y) (- 5 x))
                  :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (if (not (and (natp x) (< x 5)
                (natp y) (< y 5)))
      nil
    ;; y-major
    (let ((new-x (if (= (+ x 1) 5) 0 (+ x 1)))
          (new-y (if (= (+ x 1) 5) (+ y 1) y)))
      (cons (k-chi-combine-lanes w state-array x y)
            (k-chi-aux w state-array new-x new-y)))))

(defthm k-lane-list-p-of-k-chi-aux
  (implies (natp w)
           (k-lane-list-p w (k-chi-aux w state-array x y)))
  :hints (("Goal" :in-theory (enable k-lane-p))))

(defthm len-of-k-chi-aux
  (implies (and (natp x)
                (natp y)
                (<= y 5)
                (<= x 4)
                (natp w))
           (equal (len (k-chi-aux w state-array x y))
                  (if (equal y 5)
                      0
                    (+ (* 5 (- 4 y))
                       (- 5 x)))))
  :hints (("Goal" :induct (k-chi-aux w state-array x y))))

(defthm k-state-array-p-of-k-chi-aux
  (implies (natp w)
           (k-state-array-p w (k-chi-aux w state-array 0 0)))
  :hints (("Goal" :in-theory (enable k-state-array-p))))

;; Returns the A' Keccak state array that is the output of chi.
;; [ Note: because the next function (iota) modifies only lane (0,0),
;;   it would be more efficient to leave this A' reversed
;;   and replace only the car of the list.
;;   We may do this in the future, perhaps via a transformation. ]
(defund k-chi (w state-array)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  ;; See comment on k-theta.  The reverse is here for the same reason.
  (reverse-list (k-chi-aux w state-array 0 0)))

(defthm k-state-array-p-of-k-chi
  (implies (natp w)
           (k-state-array-p w (k-chi w state-array)))
  :hints (("Goal" :in-theory (enable k-chi))))


;; ----------------
;; (spec: 3.2.5)
;; Specification of iota

;; nr = 12 + 2l, where l is log2(w).
;; (Note that this definition of nr, given in spec 3.4,
;; specializes KECCAK-p[b,nr] to the KECCAK-f[b].)
;; So, for w in {1,   2,   4,   8,  16,  32,  64},  <- width of lane
;;         l in {0,   1,   2,   3,   4,   5,   6},  <- log2(w)
;;        nr in {12, 14,  16,  18,  20,  22,  24},  <- number of rounds
;; (spec 3.3): "round index" goes from ir = (12 + 2l - nr) to (12 + 2l - 1)
;; For these examples, ir goes from 0 to nr-1, inclusive.

;; Specifically for SHA3,
;; w=64, l=6, b=1600, and nr=24, and ir goes from 0 to 23, inclusive


;; ----
;; define rc(t)
;; Because ACL2 is not case-sensitive,
;; let's call rc rcbit, and call RC RC.

;; META-NOTE:
;; An implementation can pre-compute rc(t) and RC[r]
;; If we just use a table of RC values it is probably sufficient.
;; Quoting from spec:
;;   Let RC=0^w.
;;   3. For j from 0 to l, let RC[2^j - 1]=rc(j+7ir).
;; OK, but there is no table of RC values in the spec.


;; The spec definition of rc indexes into a bit string
;; from the left.
;; We leave the bits in the same display order,
;; but represent them as integer bitvectors,
;; and convert the indexes to our own indexes.
;; Note that R is either 8 bits wide at the recursive call,
;; or 9 bits wide while it is being operated on.
;; This function captures the loop in Step 3 of Algorithm 5.
(defun k-rcbit-aux (R num-iters)
  (declare (type integer r)
           (xargs :guard (natp num-iters)))
  (if (zp num-iters)
      R
    ;; Each step in the loop has a letter from a to f.
    (let* (;; a. R=0||R;
           ;; Adding an extra 0 on the left doesn't change our bv representation.
           (R-a R) ;; We now think of R-a as being 9 bits long
           ;; b.  their (spec) R[0] is our (getbit 8 ..)
           ;; and their R[8] is our (getbit 0 ..).
           ;; Create a new 9-bit byte that has bit 8 replaced by bit 8 xor bit 0
           (R-b (putbit 9 8 (bitxor (getbit 8 R-a) (getbit 0 R-a)) R-a))
           ;; c. their R[4] is also our (getbit 4 ..)
           (R-c (putbit 9 4 (bitxor (getbit 4 R-b) (getbit 0 R-b)) R-b))
           ;; d. their R[5] is our (getbit 3 ..)
           (R-d (putbit 9 3 (bitxor (getbit 3 R-c) (getbit 0 R-c)) R-c))
           ;; e. their R[6] is our (getbit 2 ..)
           (R-e (putbit 9 2 (bitxor (getbit 2 R-d) (getbit 0 R-d)) R-d))
           ;; f. trunc8[R] is their R[0..7] which is
           ;; our (getbit 8 ..) down to (getbit 1 ..).
           ;; We could do it as a slice or as a right shift by 1
           (R-f (bvshr 9 R-e 1)))
      (k-rcbit-aux R-f (- num-iters 1)))))

;; This function might easily become more efficient if memoized.
;; This function captures Algorithm 5.
(defun k-rcbit (tt)
  (declare (type integer tt))
  (let ((num-iters (mod tt 255)))
    (if (zp num-iters)
        1 ; return val
      (let ((R #b10000000))
        (let ((final-R (k-rcbit-aux R num-iters)))
          ;; their (spec) R[0] is now our (getbit 7 ..)
          (getbit 7 final-R))))))

;; Computing RC.
;; RC has the same width w as a lane.
;; spec 3.2.4,
;; Algorithm 6: iota(A,ir)
;; Step 2:  RC is initialized to all zeros
;; Step 3:  For j from 0 to l, RC[2^j-1] = rc(j + 7*ir)

;; This function captures the loop in Step 3.
(defun k-RC-aux (w round-idx RC-so-far j max-j)
  (declare (xargs :measure (nfix (+ 1 (- max-j j)))
                  :guard (and (k-w-val-p w)
                              (integerp RC-so-far)
                              (integerp round-idx)
                              (natp j)
                              (natp max-j)
                              (<= j (+ 1 max-j))
                              (equal max-j (cdr (assoc w *k-w-to-l*))))))
  (if (or (not (mbt (natp j)))
          (not (mbt (natp max-j)))
          (> j max-j))
      RC-so-far
    (k-RC-aux w
              round-idx
              (putbit w
                       (- (expt 2 j) 1)
                       (k-rcbit (+ j (* 7 round-idx)))
                       RC-so-far)
              (+ j 1)
              max-j)))

;; Part of iota function.
;; The RC values for w=64 and round-idx in [0 .. 23]
;; are usually defined in an array of constants
;; in code in the wild.
(defun k-RC (w round-idx)
  (declare (type integer round-idx)
           (xargs :guard (k-w-val-p w)
                  :guard-hints (("Goal" :in-theory (enable k-w-val-p)))))
  (k-RC-aux w round-idx 0 0 (cdr (assoc w *k-w-to-l*))))

;; Returns the A' keccak state array that is the output of iota.
(defund k-iota (w state-array round-idx)
  (declare (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array)
                              (integerp round-idx))
                  :guard-hints (("Goal" :in-theory (enable k-state-array-p)))
                  ))
  ;; The previous array is increasing from right-to-left,
  ;; so lane(0,0) is at the end.
  ;; Reverse it to put lane(0,0) at the beginning.
  (let* ((reversed-state-array (reverse-list state-array))
         (new-lane-0-0 (bvxor w (car reversed-state-array) (k-RC w round-idx))))
    ;; after adding the new lane(0,0),
    ;; put state-array back in right-to-left order
    (reverse-list (cons new-lane-0-0 (cdr reversed-state-array)))))

(defthm k-lane-list-p-of-append
  (equal (k-lane-list-p w (append x y))
         (and (k-lane-list-p w (true-list-fix x))
              (k-lane-list-p w y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm k-lane-list-p-of-cons
  (implies (and (k-lane-p w lane)
                (k-lane-list-p w lanes))
           (k-lane-list-p w (cons lane lanes))))

(defthm k-lane-list-p-of-take
  (implies (and (k-lane-list-p w lanes)
                (natp n)
                (< n (len lanes)))
           (k-lane-list-p w (take n lanes)))
  :hints (("Goal" :in-theory (enable take))))

(defthm k-state-array-p-of-k-iota
  (implies (k-state-array-p w state-array)
           (k-state-array-p w (k-iota w state-array round-idx)))
  :hints (("Goal" :in-theory (enable k-state-array-p k-lane-p k-iota))))


;; ----------------
;; (spec: 3.3)
;; KECCAK-p[b,nr]

;; Note:
;; (spec: 3.4) states that the the rounds of KECCAK-f[b] have round-index
;; going from 0 to 11+2l; these are nr = 12+2l rounds.
;; If KECCAK-p[b,nr] has more rounds than 12+2l, then
;; the round index should start with the appropriate negative value.
;; The example given in the spec is KECCAK-p[1600,30].
;; In that case, the last round index should be 23, so the first round index is -6.
;; We have tested this informally, but it would be good to have some
;; official test vectors for this example.

;; Rnd(A, ir) = iota (chi (pi (rho (theta (A)))), ir).
(defund k-rnd (w state-array round-idx)
  (declare (type integer round-idx)
           (xargs :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (k-iota w (k-chi w (k-pi w (k-rho w (k-theta w state-array)))) round-idx))

(defthm k-state-array-p-of-k-rnd
  (implies (and (k-state-array-p w state-array)
                (natp w))
           (k-state-array-p w (k-rnd w state-array round-idx)))
  :hints (("Goal" :in-theory (enable k-rnd))))

;; Iterate from i to max-i to repeatedly apply Rnd, with i as the ir argument.
(defund k-do-rounds (w state-array i max-i)
  (declare (type integer i max-i)
           (xargs :measure (nfix (+ 1 (- max-i i)))
                  :guard (and (k-w-val-p w)
                              (k-state-array-p w state-array))))
  (if (or (not (mbt (integerp i)))
          (not (mbt (integerp max-i)))
          (> i max-i))
      state-array
    (k-do-rounds w (k-rnd w state-array i) (+ i 1) max-i)))

(defthm k-state-array-p-of-k-do-rounds
  (implies (and (k-state-array-p w state-array)
                (natp w))
           (k-state-array-p w (k-do-rounds w state-array i max-i)))
  :hints (("Goal" :in-theory (enable k-do-rounds))))

(defthm k-lane-p-of-slice
  (implies (and (< (- high low) w)
                (natp high)
                (natp low)
                (<= low high)
                (natp w))
           (k-lane-p w (slice high low k-string)))
  :hints (("Goal" :in-theory (enable k-lane-p))))

(defthm k-lane-p-of-getbit
  (implies (and (< 0 w)
                (natp n)
                (natp w))
           (k-lane-p w (getbit n k-string)))
  :hints (("Goal" :in-theory (enable k-lane-p))))

(defun keccak-p (b nrounds k-string)
  (declare (type integer nrounds)
           (xargs :guard (and (member b *k-b-vals*)
                              (k-string-p b k-string))))
  (let* ((w (/ b 25))
         (ell (- (integer-length w) 1))) ; l = log2(w), where w is a power of 2
    (let ((state-array (k-string-to-state-array w k-string)))
      (let* ((last-round-index (if (<= nrounds (+ 12 (* 2 ell)))
                                   (- nrounds 1)
                                 (+ 11 (* 2 ell))))
             (first-round-index (- last-round-index (- nrounds 1))))
        (let ((final-state-array
               (k-do-rounds w state-array first-round-index last-round-index)))
          (k-state-array-to-string w final-state-array))))))

(defthm k-string-p-of-keccak-p
  (implies (and (k-string-p b k-string)
                (natp w)
                (equal b (* 25 w)))
           (k-string-p b (keccak-p b nrounds k-string)))
  :hints (("Goal" :in-theory (disable k-string-p))))


;; ----------------
;; (spec: 4)
;; SPONGE CONSTRUCTION

;; r is the rate; r < b
;; c is the capacity; c = b - r

;; See below for a continuation of (spec: 4) after pad() is defined.


;; ----------------
;; (spec: 5)
;; KECCAK family of sponge functions.


;; ----------------
;; (spec 5.1)
;; Specification of pad10*1

;; Use this for a bitstring represented as a list of bits
(defund k-pad10*1 (x m)
  (declare (type (integer 1 *) x)
           (type (integer 0 *) m))
  (let ((j (mod (- (- m) 2) x)))
    (cons '1
          (append (repeat j '0)
                  '(1)))))

(defthm all-unsigned-byte-p-1-of-k-pad10*1
  (all-unsigned-byte-p 1 (k-pad10*1 x m))
  :hints (("Goal" :in-theory (enable k-pad10*1))))


;; --------------------------------
;; Conversions between bit vectors and bit strings.

(defun bitstring-to-bv (list-of-bits)
  (declare (xargs :guard (bit-listp list-of-bits)))
  (packbv (len list-of-bits) 1 (reverse-list list-of-bits)))

;; The inverse of bitstring-to-bv.
(defun k-string-to-bitstring (d k-string)
  (declare (xargs :guard (and (posp d)
                              (k-string-p d k-string))))
  (reverse-list (unpackbv d 1 k-string)))

(defthm len-of-k-string-bitstring
  (implies (and (posp d)
                (k-string-p d k-string))
           (equal (len (k-string-to-bitstring d k-string))
                  d)))


;; ----------------
;; continuation of (spec: 4)

;; Although the sponge construction is more general than Keccak,
;; we will assume it is being defined for KECCAK-p[b,nr] and that
;; it uses pad10*1.
;; Leaving b (bit width) and r (rate) and nrounds as parameters.
;; (For SHA-3 and Keccak-256, b=1600, c=512, r=1088, d=256, nrounds=24).

;; The input message N is a "bitstring", which we represent as
;; a list of bits.

;; However, as a practical matter, nobody wants to hash bitstrings,
;; they want to hash strings of bytes.
;; On the other hand, the spec allows any number of bits, so we support that.

;; There are other possible representations that would be more efficient,
;; such as N = (cons N' nmod8),
;; where N' is a string of bytes, but only the nmod8 bits of the last byte
;; are the last nmod8 bits of N.

;; As another practical matter, implementations typically stream the input
;; bytes and just add the padding, etc. at the end when the end is known.
;; We do not handle this use case at this time.

;; NOTE: The bitvector we use internally treats the list of bits
;; as little-endian.  Therefore we must reverse the list when converting
;; between list-of-bits and the bitvector.  See also the note on k-sponge.

;; Does the absorbing (spec: Figure 7)
;; This is the loop in Step 6 of Algorithm 8.
(defun k-sponge-aux (i max-i b r nrounds s-so-far rest-of-p)
  (declare (type integer nrounds s-so-far)
           (type (integer 0 *) r b)
           (xargs :measure (nfix (+ 1 (- max-i i)))
                  :guard (and (member b *k-b-vals*)
                              (bit-listp rest-of-p))
                  :guard-hints (("Goal" :in-theory (enable k-string-p)))))
  (if (or (not (natp i))
          (not (natp max-i))
          (> i max-i))
      s-so-far
    (k-sponge-aux
     (+ i 1)
     max-i
     b
     r
     nrounds
     (keccak-p b nrounds (bvxor b s-so-far (bitstring-to-bv (firstn r rest-of-p))))
     (nthcdr r rest-of-p))))

;; Does the squeezing (spec: Figure 7)
;; (spec: Algorithm 8 steps 8 to 10)
;;   8.  Let Z = Z || Trunc_r(S)
;;   9.  If d <= |Z|, then return Trunc_d(Z); else continue.
;;   10. Let S=f(S), and continue with Step 8.
;; f is keccak-p()
;; Z is a bitstring, S is a bitvector (unsigned integer).
;; It would be more consistent to have S be a bitstring, too,
;; but for now keccak-p expects a bitvector.
;;
;; Future code (not needed for now):
;; (defun k-sponge-squeeze (b r nrounds d Z S)
;;  (let ((new-Z (append Z (firstn r (k-string-to-bitstring d S)))))
;;    (if (<= d (len new-Z))
;;        (firstn d new-Z)
;;      (let ((new-S (keccak-p b nrounds S)))
;;        (k-sponge-squeeze b r nrounds d new-Z new-S)))))
;;
;; NOTE: k-sponge returns the bitvector (a nat) we use internally.
;; If you convert this to a list of bits, you should reverse the bits
;; if you want to match FIPS 202.
(defund k-sponge (b r nrounds N d)
  (declare (type integer nrounds)
           (type (integer 0 *) b d)
           (type (integer 1 *) r)
           (xargs :guard (and (member b *k-b-vals*)
                              (bit-listp n))))
  (let ((P (append N (k-pad10*1 r (len N))))) ; Step 1
    (let ((num-chunks (/ (len P) r))) ; Step 2
      (let ((c (- b r))) ; Step 3
        ;; Because higher-order bits in a bitvector are implicitly zero,
        ;; and because the only use of c in the spec is to pad with
        ;; higher-order zeros, we can ignore c.
        (declare (ignorable c))
        ;; Step 4 is implicitly performed by the recursion in k-sponge-aux.
        ;; Represent S (of width b) as a bitvector.
        ;; S starts out as 0 (Step 5),
        ;; which is the second '0' in the call to k-sponge-aux.
        (let ((S (k-sponge-aux 0 (- num-chunks 1) b r nrounds 0 P)))
          ;; Future code (commented out for now):
          ;; (bitstring-to-bv (k-sponge-squeeze b r nrounds d '() S))
          ;; Replace the next form by the previous line when
          ;; k-sponge-squeeze is defined.
          ;; The following is adequate for f = KECCAK-p[1600, 24]
          ;; since |Z| = 1088 and d is 256.
          ;; That is, for now the loop in Steps 8-10 is executed only once.
          (let ((Z (slice (- r 1) 0 S)))
            (slice (- d 1) 0 Z)))))))

;; For reference:
;; keccak-256 does (keccak-c 512 M 256)
;; c = 512, d = 256
;; (k-sponge 1600 (- 1600 c) 24 N d) = (k-sponge 1600 1088 24 N 256)
;; b = 1600, r = 1088, nrounds = 24, d = 256

(defthm k-string-p-of-k-sponge
  (implies (posp d)
           (k-string-p d (k-sponge b r nrounds n d)))
  :hints (("Goal" :in-theory (enable k-sponge k-string-p))))

(defthm unsigned-byte-p-of-k-sponge
  (implies (posp d)
           (unsigned-byte-p d (k-sponge b r nrounds n d)))
  :hints (("Goal" :in-theory (enable k-sponge))))


;; ----------------
;; (spec 5.2)
;; Specification of KECCAK[c]
;; KECCAK[c] = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 - c]

;; Note that our definition of k-sponge implements
;; SPONGE and KECCAK-p and pad10*1,
;; with the b and nrounds exposed as parameters.

;; NOTE: keccak-c returns the bitvector (a nat) we use internally.
;; If you convert this to a list of bits, you should reverse the bits
;; if you want to match FIPS 202.

;; N is input bit string (as a list of bits), d is output size in bits
(defun keccak-c (c N d)
  (declare (type (integer 0 *) d)
           (type (integer 0 1599) c)
           (xargs :guard (bit-listp n)))
  (k-sponge 1600 (- 1600 c) 24 N d))

(defthm k-string-p-of-keccak-c
  (implies (posp d)
           (k-string-p d (keccak-c c N d)))
  :hints (("Goal" :in-theory (disable K-STRING-P))))

(defthm return-size-of-keccak-c
  (implies (and (posp d)
                (bit-listp N))
           (unsigned-byte-p d (keccak-c c N d))))


;; --------------------------------
;; Lowest-level interface for Keccak hash functions.
;; Takes a list of bits, and returns the bitvector
;; represented as a large integer that we use internally.
;; If you convert this to a list of bits to match FIPS 202,
;; you should do it little-endian.  This is because
;; of how we represent the bits internally.
;; For example, if the bitvector is 129, a standard base two
;; representation is #b10000010, but to match FIPS 202
;; you would return (0 1 0 0 0 0 0 1)

(defun keccak-224-bits-to-bv (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-c 448 M 224))

(defun keccak-256-bits-to-bv (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-c 512 M 256))

(defun keccak-384-bits-to-bv (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-c 768 M 384))

(defun keccak-512-bits-to-bv (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-c 1024 M 512))


;; --------------------------------
;; Main bit-oriented hash functions.

;; These are the functions that are closest to IFIPS 202
;; in terms of the input and output data types.

(defund keccak-224 (M)
  (declare (xargs :guard (bit-listp M)))
  (k-string-to-bitstring 224 (keccak-224-bits-to-bv M)))

(defthm all-unsigned-byte-p-1-of-keccak-224
  (all-unsigned-byte-p 1 (keccak-224 M))
  :hints (("Goal" :in-theory (enable keccak-224))))

(defthm len-of-keccak-224
  (equal (len (keccak-224 M)) 224)
  :hints (("Goal" :in-theory (enable keccak-224))))

(defund keccak-256 (M)
  (declare (xargs :guard (bit-listp M)))
  (k-string-to-bitstring 256 (keccak-256-bits-to-bv M)))

(defthm all-unsigned-byte-p-1-of-keccak-256
  (all-unsigned-byte-p 1 (keccak-256 M))
  :hints (("Goal" :in-theory (enable keccak-256))))

(defthm len-of-keccak-256
  (equal (len (keccak-256 M)) 256)
  :hints (("Goal" :in-theory (enable keccak-256))))

(defund keccak-384 (M)
  (declare (xargs :guard (bit-listp M)))
  (k-string-to-bitstring 384 (keccak-384-bits-to-bv M)))

(defthm all-unsigned-byte-p-1-of-keccak-384
  (all-unsigned-byte-p 1 (keccak-384 M))
  :hints (("Goal" :in-theory (enable keccak-384))))

(defthm len-of-keccak-384
  (equal (len (keccak-384 M)) 384)
  :hints (("Goal" :in-theory (enable keccak-384))))

(defund keccak-512 (M)
  (declare (xargs :guard (bit-listp M)))
  (k-string-to-bitstring 512 (keccak-512-bits-to-bv M)))

(defthm all-unsigned-byte-p-1-of-keccak-512
  (all-unsigned-byte-p 1 (keccak-512 M))
  :hints (("Goal" :in-theory (enable keccak-512))))

(defthm len-of-keccak-512
  (equal (len (keccak-512 M)) 512)
  :hints (("Goal" :in-theory (enable keccak-512))))


;; --------------------------------
;; Converting to and from bytes for the byte-oriented interface.

;; From FIPS 202, Appendix B.1,
;; see
;;   Algorithm 10: h2b(H, n).
;;   Algorithm 11: b2h(S).


;; ----------------
;; h2b(H)

;; Used for converting a sequence of bytes into a sequence of bits
;; prior to computing the hash function.

;; "Input: hexadecimal string H consisting of 2m digits for some
;;  positive integer m; positive integer n such that n <= 8m."
;;
;; Without loss of generality, we omit the argument n:
;;   "If the length n of the output string S is not specified explicitly
;;    as an input, then h2b(H) is defined to be h2b(H, 8m),
;;    i.e., n is given the maximum possible value."
;; The caller can truncate if they want fewer bits.

(defun h2b (H)
  (declare (xargs :guard (and (true-listp H)
                              (all-unsigned-byte-p 8 H))))
  (bytes-to-bits-little H))

(defthm all-unsigned-byte-p-1-of-h2b
  (all-unsigned-byte-p 1 (h2b S)))


;; ----------------
;; b2h(S)

;; Used for converting the sequence of bits output from a hash function
;; to a sequence of bytes.

;; "Input: bit string S consisting of n bits for a positive integer n."

;; Notes:
;; "The formal bit-reordering function that was specified in [12]-for the
;;  KECCAK submission to the SHA-3 competition-gives equivalent conversions when
;;  the message is byte-aligned, i.e., when n is a multiple of 8."
;;
;; [12] G. Bertoni, J. Daemen, M. Peeters, G. Van Assche, and R. Van Keer,
;;      KECCAK implementation overview, January 2011,
;;      http://keccak.noekeon.org/Keccak-implementation-3.0.pdf.
;; Note, this pdf is here as of 2019-03-21:
;;   https://keccak.team/obsolete/Keccak-implementation-3.0.pdf

(defun b2h (S)
  (declare (xargs :guard (bit-listp S)
                  :guard-hints (("Goal" :in-theory (enable len-mult-of-8p)))))
  (let ((bits-multiple-of-8 (if (len-mult-of-8p S)
                                S
                              (append S (repeat (- 8 (mod (len S) 8)) 0)))))
    (bits-to-bytes-little bits-multiple-of-8)))

(defthm all-unsigned-byte-p-8-of-b2h
  (all-unsigned-byte-p 8 (b2h S)))

;; --------------------------------
;; Main byte-oriented hash functions.
;; These are also implied by FIPS 2012.

(defund keccak-224-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-224 (h2b bytes))))

(defthm all-unsigned-byte-p-8-of-keccak-224-bytes
  (all-unsigned-byte-p 8 (keccak-224-bytes bytes))
  :hints (("Goal" :in-theory (enable keccak-224-bytes))))

(defthm len-of-keccak-224-bytes
  (equal (len (keccak-224-bytes bytes)) 28)
  :hints (("Goal" :in-theory (enable keccak-224-bytes len-mult-of-8p))))

(defund keccak-256-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-256 (h2b bytes))))

(defthm all-unsigned-byte-p-8-of-keccak-256-bytes
  (all-unsigned-byte-p 8 (keccak-256-bytes bytes))
  :hints (("Goal" :in-theory (enable keccak-256-bytes))))

(defthm len-of-keccak-256-bytes
  (equal (len (keccak-256-bytes bytes)) 32)
  :hints (("Goal" :in-theory (enable keccak-256-bytes len-mult-of-8p))))

(defund keccak-384-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-384 (h2b bytes))))

(defthm all-unsigned-byte-p-8-of-keccak-384-bytes
  (all-unsigned-byte-p 8 (keccak-384-bytes bytes))
  :hints (("Goal" :in-theory (enable keccak-384-bytes))))

(defthm len-of-keccak-384-bytes
  (equal (len (keccak-384-bytes bytes)) 48)
  :hints (("Goal" :in-theory (enable keccak-384-bytes len-mult-of-8p))))

(defund keccak-512-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-512 (h2b bytes))))

(defthm all-unsigned-byte-p-8-of-keccak-512-bytes
  (all-unsigned-byte-p 8 (keccak-512-bytes bytes))
  :hints (("Goal" :in-theory (enable keccak-512-bytes))))

(defthm len-of-keccak-512-bytes
  (equal (len (keccak-512-bytes bytes)) 64)
  :hints (("Goal" :in-theory (enable keccak-512-bytes len-mult-of-8p))))


;; --------------------------------
;; Hash functions that take string input.
;; Returns a list of bytes.

;; An ACL2 string is isomorphic to a vector of 8-bit unisgned bytes,
;; since an ACL2 string is an array of characters, each of which
;; has a char-code from 0 to 255 and no other information.

(defun keccak-224-string-to-bytes (str)
  (declare (xargs :guard (stringp str)))
  (keccak-224-bytes (string=>nats str)))

(defun keccak-256-string-to-bytes (str)
  (declare (xargs :guard (stringp str)))
  (keccak-256-bytes (string=>nats str)))

(defun keccak-384-string-to-bytes (str)
  (declare (xargs :guard (stringp str)))
  (keccak-384-bytes (string=>nats str)))

(defun keccak-512-string-to-bytes (str)
  (declare (xargs :guard (stringp str)))
  (keccak-512-bytes (string=>nats str)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ================================
;; Formal spec for SHA-3 hash functions.


;; ----------------
;; Introduction.

;; SHA-3 is based on the Keccak family of permutations and
;; sponge functions.

;; Below we define 4 varieties of standard SHA-3 hash functions:
;;
;;   SHA3-224, SHA3-256, SHA3-384, SHA3-512
;;
;; References to "spec" are to:
;;   SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions
;;   NIST, http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf


;; ----------------
;; (spec 6.1)
;; SHA-3 hash functions

;; These hash functions come in the following varieties.
;;
;; 1. Each default function accepts and returns "bit strings",
;;    which we model by lists of bits.  Note that these
;;    functions allow inputs whose length is not a multiple of 8.
;;    The default bit-oriented functions are:
;;
;;      SHA3-224, SHA3-256, SHA3-384, SHA3-512.
;;
;; 2. Each default function accepts and returns "byte strings".
;;    which we model by lists of bytes.  These are:
;;      SHA3-224-BYTES, SHA3-256-BYTES, SHA3-384-BYTES, SHA3-512-BYTES.


;; --------
;; Bit-oriented SHA-3 functions

;; For each of these functions:
;; M is a list of bits.
;; It returns a list of bits.

(defun sha3-224 (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-224 (append M '(0 1))))

(defun sha3-256 (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-256 (append M '(0 1))))

(defun sha3-384 (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-384 (append M '(0 1))))

(defun sha3-512 (M)
  (declare (xargs :guard (bit-listp M)))
  (keccak-512 (append M '(0 1))))


;; --------
;; Byte-oriented SHA-3 functions

;; For each of these functions:
;; M is a list of bytes
;; It returns a list of bits.

(defun sha3-224-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-224 (append (h2b bytes) '(0 1)))))

(defun sha3-256-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-256 (append (h2b bytes) '(0 1)))))

(defun sha3-384-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-384 (append (h2b bytes) '(0 1)))))

(defun sha3-512-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b2h (keccak-512 (append (h2b bytes) '(0 1)))))
