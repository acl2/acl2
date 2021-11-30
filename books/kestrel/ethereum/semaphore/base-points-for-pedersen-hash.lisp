; Ethereum Semaphore Library
; Pedersen Hash base point calculation
;
; Copyright (C) 2020,2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "baby-jubjub")

(include-book "kestrel/crypto/blake/blake-256" :dir :system)

(include-book "kestrel/utilities/digits-any-base/core" :dir :system)

(include-book "kestrel/number-theory/quadratic-residue" :dir :system)
(include-book "kestrel/number-theory/tonelli-shanks" :dir :system)

(include-book "std/strings/top" :dir :system)

(include-book "kestrel/bv-lists/string-to-bits" :dir :system) ; for string-to-bytes

(include-book "kestrel/bv-lists/bits-to-byte" :dir :system) ; for bits-to-byte

(include-book "kestrel/prime-fields/prime-fields" :dir :system)

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defxdoc+ pedersen-hash-base-points
  :parents (semaphore-specification)
  :short "Calculation of the ten base points used for the Pedersen hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ten base points used for Semaphore's Pedersen hash were chosen in a
  pseudorandom fashion.  In [Sema-Spec:5.3.2] these are called
  <i>generators</i> and are denoted @($g_s$) for @($s$) in the set
  @($\\{0,..,9\\}$).")
    (xdoc::p
    "The description in [Sema-Spec:5.3.2] of how the base points were chosen
  is not quite correct.  The input to @($\\mathsf{Blake256}$) contains some
  additional punctuation, and the padding function pads a decimal string
  version of the number with the digit `0' (ascii 48).  We believe the correct
  specification, checked against the
  Javascript source and also independently duplicated in Python, is as follows.")
    (xdoc::blockquote
    "For each @($s$), the generator @($g_s$) is computed as the first
  successful attempt, when incrementally trying indices from @($i = 0$),
  at finding a @($\\mathsf{BabyJubjub}$) point from a possible @($x$) coordinate calculated as "
   (xdoc::@[] "\\mathsf{Blake256(}\\mathtt{\"PedersenGenerator\\_\"}
   \\ || \\ \\mathsf{decimalStringPadLeftZeros}(s,32)
   \\ || \\ \\mathtt{\"\\_\"}
   \\ || \\ \\mathsf{decimalStringPadLeftZeros}(i,32))")
   "with the 255th bit set to 0.")
 ))



;; adds the byte PAD-VALUE to the left of STARTING-BYTE-LIST until it has length GOAL-LENGTH
(defun bytes-pad-left (goal-length pad-value starting-byte-list)
  (if (or (not (natp goal-length))
          (not (natp pad-value))
          (not (< pad-value 256))
          (not (true-listp starting-byte-list))
          (< goal-length (length starting-byte-list)))
      nil
    (append (repeat (- goal-length (length starting-byte-list))
                    (char-code #\0))
              starting-byte-list)))

(verify-guards bytes-pad-left)

(defund pedersen-base-point-seed-string ()
  "PedersenGenerator_")

(verify-guards pedersen-base-point-seed-string)

(defun pedersen-base-point-seed (s i)
  (declare (type (integer 0 255) s))
  (declare (type (integer 0 255) i))
  (append
   (acl2::string-to-bytes (pedersen-base-point-seed-string))
   (bytes-pad-left 32
                   (char-code #\0)
                   (acl2::string-to-bytes (str::int-to-dec-string s)))
   (acl2::string-to-bytes "_")
   (bytes-pad-left 32
                   (char-code #\0)
                   (acl2::string-to-bytes (str::int-to-dec-string i)))))


(defun pedersen-base-calculate-y (s i)
  (let ((hash (blake::blake-256-bytes (pedersen-base-point-seed s i))))
    ;; hash is a little-endian list of bytes,
    ;; but with two refinements: bit 256 should be returned as the sign,
    ;; and both bits 255 and 256 should be cleared from the returned y value.
    ;; Since it is easier to modify the head of the list,
    ;; reverse the list, and after twiddling the bits,
    ;; construct the integer with bendian=>nat, not lendian=>nat.
    (let* ((rhash (reverse hash))
           (first-byte (car rhash))
           (bits-of-first-byte (acl2::byte-to-bits first-byte))
           ;; returned a big-endian list of bits for the byte
           (sign? (equal 1 (first bits-of-first-byte)))
           ;; replace highest order two bits by 0
           (new-first-byte (acl2::bits-to-byte (cons 0 (cons 0 (cddr bits-of-first-byte)))))
           (y-val (acl2::bendian=>nat 256 (cons new-first-byte (cdr rhash)))))
      (mv y-val sign?))))



;; The Twisted Edwards curve is 168700.x^2 + y^2 = 1 + 168696.x^2.y^2
;; Solving for x^2:  x^2 * (168700 - 168696.y^2) = 1 - y^2
;;   x^2 = (1 - y^2)/(168700 - 168696.y^2)
;;   As long as y^2 is not 168700/168696, we can calculate x^2.

(assert! (not (primes::has-square-root? (pfield::div 168700
                                                     168696
                                                     (baby-jubjub-prime))
                                        (baby-jubjub-prime))))

;; We first find y from the hash, then we see if the RHS has a square root.

(defun pedersen-base-point-aux (s i)
  (declare (type (integer 0  99999999999999999999999999999999) s)
           ;; allow 1 more for i to signal failure
           (type (integer 0 100000000000000000000000000000000) i))
  (declare (xargs :verify-guards nil))
  (declare (xargs :measure (nfix (- 100000000000000000000000000000000 i))))
  (if (or (not (mbt (natp i)))
          (> i 99999999999999999999999999999999))
      nil
    (mv-let (y sign?)
        (pedersen-base-calculate-y s i)
      ;; move this calculation to baby-jubjub.lisp (it is probably already there)
      (if (<= (baby-jubjub-prime) y) ; can happen, even when both are 254 bits
          (pedersen-base-point-aux s (+ i 1))
        (let* ((y^2 (pfield::mul y y (baby-jubjub-prime)))
               (numerator (pfield::sub 1 y^2 (baby-jubjub-prime)))
               (denominator (pfield::sub 168700
                                         (pfield::mul 168696
                                                      y^2
                                                      (baby-jubjub-prime))
                                         (baby-jubjub-prime)))
               ;; the assert! above prevents the next expression from dividing by zero
               (x^2 (pfield::div numerator denominator (baby-jubjub-prime)))
               (has-root? (primes::has-square-root? x^2 (baby-jubjub-prime))))
          (if has-root?
              (let ((x (primes::tonelli-shanks-sqrt x^2 (baby-jubjub-prime) 5)))
                ;; x will be the lesser square root
                ;; (of the two in [0..(baby-jubjub-prime)))
                (if sign?
                    (cons (pfield::neg x (baby-jubjub-prime)) y)
                  (cons x y)))
            (pedersen-base-point-aux s (+ i 1))))))))


(defun pedersen-base-point (s)
  ;; pedersen-base-point-aux Iterates i until a valid point is found
  ;; or until no 32-decimal-digit value works
  (let ((bpoint (pedersen-base-point-aux s 0)))
    (if (not bpoint) nil ; extremely unlikely
      ;; multiply point by 8
      (baby-jubjub-mul 8 bpoint))))

;; Base points copied from pedersen.circom
;; Below we will see if they are the same as the calculated ones.

(defconst *pedersen-base-points-for-semaphore*
  '(
        (10457101036533406547632367118273992217979173478358440826365724437999023779287 . 19824078218392094440610104313265183977899662750282163392862422243483260492317)
        (2671756056509184035029146175565761955751135805354291559563293617232983272177 . 2663205510731142763556352975002641716101654201788071096152948830924149045094)
        (5802099305472655231388284418920769829666717045250560929368476121199858275951 . 5980429700218124965372158798884772646841287887664001482443826541541529227896)
        (7107336197374528537877327281242680114152313102022415488494307685842428166594 . 2857869773864086953506483169737724679646433914307247183624878062391496185654)
        (20265828622013100949498132415626198973119240347465898028410217039057588424236 . 1160461593266035632937973507065134938065359936056410650153315956301179689506)
        (1487999857809287756929114517587739322941449154962237464737694709326309567994 . 14017256862867289575056460215526364897734808720610101650676790868051368668003)
        (14618644331049802168996997831720384953259095788558646464435263343433563860015 . 13115243279999696210147231297848654998887864576952244320558158620692603342236)
        (6814338563135591367010655964669793483652536871717891893032616415581401894627 . 13660303521961041205824633772157003587453809761793065294055279768121314853695)
        (3571615583211663069428808372184817973703476260057504149923239576077102575715 . 11981351099832644138306422070127357074117642951423551606012551622164230222506)
        (18597552580465440374022635246985743886550544261632147935254624835147509493269 . 6753322320275422086923032033899357299485124665258735666995435957890214041481)
    ))


;; Make sure the points are on the curve.

(define bjj-point-listp ((l true-listp))
;;  "Recognizes true lists of points on the baby jubjub curve"
  :returns (y/n booleanp)
  (or (endp l)
      (and (baby-jubjub-pointp (car l))
           (bjj-point-listp (cdr l)))))

(assert! (bjj-point-listp *pedersen-base-points-for-semaphore*))


;; Make sure the formal spec above computes the points
;; in the constant in pedersen.circom.

(defun nth-pedersen-matches? (i)
  (equal (nth i *pedersen-base-points-for-semaphore*)
         (pedersen-base-point i)))

(assert! (and (nth-pedersen-matches? 0)
              (nth-pedersen-matches? 1)
              (nth-pedersen-matches? 2)
              (nth-pedersen-matches? 3)
              (nth-pedersen-matches? 4)
              (nth-pedersen-matches? 5)
              (nth-pedersen-matches? 6)
              (nth-pedersen-matches? 7)
              (nth-pedersen-matches? 8)
              (nth-pedersen-matches? 9)))
