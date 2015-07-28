; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "GACC")

;; [Jared] reordered include-books so non-local includes come first
(include-book "../lists/repeat")
(include-book "list-ops-fast")
;;(include-book "list-ops")
(include-book "wrap")
(include-book "../super-ihs/fast")
(include-book "../lists/mixed")

(local (include-book "../util/iff"))
; (Matt K., 10/2013: Changed rel8 to rel9.)
(local (include-book "rtl/rel9/arithmetic/fl" :dir :system))

;(local (include-book "../super-ihs/loglist")) ;bzo
(local (include-book "../super-ihs/super-ihs")) ;bzo

;; This books includes support for reading and writing to a memory with the following characteristics:
;; Addresses are 32-bit signed integers.
;; The memory is byte-addressable (each address corresponds to a single byte).
;; A data read or write is of a 2-byte of word at an even byte address (generated from a 31-bit word address).
;; A code fetch is of a single byte at a 32-bit byte address.
;; Data reads and writes are done with respect to a data environment, indicated by a 15-bit denvr.
;; Code reads and writes are done with respect to a code environment, indicated by a 16-bit cenvr.
;; Things are done in a little endian fashion.  bzo expand.


;; Perhaps someday someone will generalize the functionality of this book.

;; We hope that read-data-word, read-data-words, write-data-word, and
;; write-data-words can usually be treated as primitives.  That is, you should
;; rarely need to look inside those functions.  But if you do need to blow
;; such things open and talk about the lists of addresses that are getting
;; read and written, that information is easiliy available, since these
;; functions are defined directly as calls to rd-list and wr-list.

;; RBK: I added a bunch of apparently missing rules to the end of this
;; book on May 15th 2007.  These should be integrated properly with the
;; rest of the book and put in the proper place.

;; [Jared] dumb speed hacking
(local (in-theory (disable list::memberp
                           acl2::ash-0
                           (:t acl2::loghead-type)
                           acl2::zip-open
                           acl2::BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P
                           gacc::wr-list-of-what-was-already-there
                           acl2::loghead-identity
                           gacc::wr-list-of-cons-one
                           RD-OF-WR-LIST-DIFF
                           ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                           )))


(local (in-theory (disable list::memberp-of-cons
                           bag::subbagp-of-cons)))


;bbzo move this stuff:


;bzo add guards to these...
(defun gather-constant-factors (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;e.g., a variable
      (list 1)
    (if (and (equal 'quote (car term))
             (integerp (cadr term)))
        (list (cadr term))
      (if (equal 'binary-+ (car term))
          (append (gather-constant-factors (cadr term))
                  (gather-constant-factors (caddr term)))
        (if (equal 'unary-- (car term))
            (gather-constant-factors (cadr term))
          (if (equal 'binary-* (car term)) ;assumes the constant (if any) has been brought to the front of the product
              (if (and (quotep (cadr term))
                       (integerp (cadadr term)))
                  (list (cadr (cadr term)))
                (list 1))
            (list 1)))))))

;only works for positive numbers?
(defun gcd-aux (i j)
  (declare (xargs :measure (nfix j)
                  :guard (and (integerp i) (integerp j) (<= 0 j))))
  (if (zp j)
      1
    (let ((r (mod i j)))
      (if (zp r)
          j
        (gcd-aux j r)))))

;what should this do for negative numbers?
(defun greatest-common-divisor (i j)
  (declare (xargs :guard (and (integerp i) (integerp j))))
  (gcd-aux (max (abs i) (abs j)) (min (abs i) (abs j))))

(defun gcd-many (lst)
  (declare (xargs :guard (integer-listp lst) :verify-guards nil))
  (if (endp lst)
      1
    (if (endp (cdr lst))
        (car lst)
      (greatest-common-divisor (car lst)
                               (gcd-many (cdr lst))))))

(defthm integerp-of-gcd-many
  (implies (integer-listp lst)
           (integerp (gcd-many lst))))

(verify-guards gcd-many)

(defthm integer-listp-of-gather-constant-factors
  (integer-listp (gather-constant-factors term)))

(defun greatest-common-constant-factor (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (greatest-common-divisor (gcd-many (gather-constant-factors term1))
                           (gcd-many (gather-constant-factors term2))))

(defun bind-x-to-greatest-common-constant-factor (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (acons 'x `(quote ,(greatest-common-constant-factor term1 term2)) nil))


;what about multiplying by constant factor in denominator?
(defthm cancel-common-constant-factor-from-<
  (implies (and (BIND-FREE (bind-x-to-greatest-common-constant-factor LHS RHS) (X))
                (< 1 x) ;otherwise, this rule might loop
                (integerp x)
                (rationalp lhs)
                (rationalp rhs))
           (equal (< lhs rhs)
                  (< (/ lhs x) (/ rhs x)))))

(defthm cancel-common-constant-factor-from-=
  (implies (and (BIND-FREE (bind-x-to-greatest-common-constant-factor LHS RHS) (X))
                (< 1 x) ;otherwise, this rule might loop
                (integerp x)
                (rationalp lhs)
                (rationalp rhs))
           (equal (equal lhs rhs)
                  (equal (/ lhs x) (/ rhs x)))))



;bzo allow denvrs to differ everywhere appropriate?


(local (in-theory (enable zp)))


(defthm wr-same-rd-non-cheap
  (implies (equal val (rd ad ram))
           (equal (wr ad val ram)
                  ram)))

;; [Jared] speed hack
(local (in-theory (disable wr-same-rd-non-cheap)))

;bzo can loop
(defthm wr-of-0-becomes-clr
  (equal (wr ad 0 ram)
         (memory-clr ad ram))
  :hints (("Goal" :in-theory (enable))))

(theory-invariant (incompatible (:rewrite wr-of-0-becomes-clr) (:rewrite clr)))

#+joe
(defthm clr-of-wr-diff
  (implies (not (equal ad1 ad2))
           (equal (memory-CLR ad1 (WR ad2 value ram))
                  (wr ad2 value (memory-CLR ad1 ram))))
  :hints (("Goal" :in-theory (e/d (CLR) (wr-of-0-becomes-clr)))))

#+joe
(defthm clr-of-wr-same
  (equal (clr ad (wr ad value ram))
         (clr ad ram))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))


;add loop-stopper?
#+joe
(defthm clr-of-clr-diff
  (implies (not (equal ad1 ad2))
           (equal (clr ad1 (clr ad2 ram))
                  (clr ad2 (clr ad1 ram))))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))

#+joe
(DEFTHM RD-OF-clr-both
  (EQUAL (RD ACL2::A (clr ACL2::B ACL2::R))
         (IF (EQUAL ACL2::B ACL2::A)
             0
             (RD ACL2::A ACL2::R)))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))


(local (include-book "../bags/pick-a-point")) ;bzo make non-local? ;drop?

;bzo dup
;move
(defthm unsigned-byte-p-list-of-offset-range-wrap
  (implies (natp n)
           (unsigned-byte-p-list n (offset-range-wrap n ad numbytes)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-list offset-range-wrap))))

;; (defthm unsigned-byte-p-list-of-offset-range-wrap
;;   (unsigned-byte-p-list 31 (offset-range-wrap 31 base ads))
;;   :hints (("Goal" :in-theory (enable offset-range-wrap unsigned-byte-p-list))))



;;
;; Converting word addresses to byte addresses.
;;



;; Convert the word address WORD-AD to a list of its two corresponding byte
;; addresses.
;;
(defun word-ad-to-byte-ads (word-ad)
  (declare (type integer word-ad))
  (list (logapp 1 0 word-ad)
        (logapp 1 1 word-ad)))

(defthm consp-of-word-ad-to-byte-ads
  (consp (word-ad-to-byte-ads word-ad)))

(defthm len-of-word-ad-to-byte-ads
  (equal (len (word-ad-to-byte-ads word-ad))
         2)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm consp-cdr-word-ad-to-byte-ads
  (equal (consp (cdr (word-ad-to-byte-ads word-ad)))
         t)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))


(defthm integer-listp-of-word-ad-to-byte-ads
  (implies (integerp word-ad)
           (integer-listp (word-ad-to-byte-ads word-ad)))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm memberp-of-word-ad-to-byte-ads
  (equal (memberp b (word-ad-to-byte-ads a))
         (and (integerp b)
              (equal (ifix a) (acl2::logcdr b))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable word-ad-to-byte-ads
                              list::memberp-of-cons))))

;; [Jared] dumb speed hack
(local (in-theory (disable gacc::memberp-of-word-ad-to-byte-ads)))

(defthm integerp-of-cadr-of-word-ad-to-byte-ads
  (integerp (car (cdr (word-ad-to-byte-ads word-ad))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm integerp-of-car-of-word-ad-to-byte-ads
  (integerp (car (word-ad-to-byte-ads word-ad)))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm disjoint-of-two-word-ad-to-byte-ads
  (equal (disjoint (word-ad-to-byte-ads ad1)
                   (word-ad-to-byte-ads ad2))
         (not (equal (ifix ad1) (ifix ad2))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads
                                     list::memberp-of-cons))))

(defthm logext-list-32-of-word-ad-to-byte-ads
  (equal (logext-list 32 (word-ad-to-byte-ads word-ad))
         (word-ad-to-byte-ads (logext 31 word-ad)))
  :hints (("Goal" :in-theory (enable logext-list word-ad-to-byte-ads))))

(defthm disjoint-of-WORD-AD-TO-BYTE-ADS
  (implies (integer-listp x)
           (equal (DISJOINT X (WORD-AD-TO-BYTE-ADS a))
                  (not (memberp (ifix a) (logcdr-list x)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable list::memberp WORD-AD-TO-BYTE-ADS))))

(defthm cdr-cdr-word-ad-to-byte-ads
  (equal (cdr (cdr (word-ad-to-byte-ads word-ad)))
         nil)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm unique-of-word-ad-to-byte-ads
  (bag::unique (word-ad-to-byte-ads word-ad))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads
                                     acl2::equal-to-ash-1-rewrite))))
;misc:


(defthm loghead-list-of-offset-range-wrap
  (equal (loghead-list '16 (offset-range-wrap 16 base size))
         (offset-range-wrap 16 base size))
  :hints (("Goal" :in-theory (enable loghead-list offset-range-wrap))))

;;
;; syntactic stuff
;;



;Offsets look like this:
; (BINARY-+ '1 (NTH '4 ST))
; (BINARY-+ '2 (NTH '3 ST))
(defun offset-has-expected-form (term)
  (declare (type t term))
  (and (equal 3 (len term))
       (SYMBOLP (CAR TERM))
       (equal (symbol-name (car term)) "BINARY-+")
       (quotep (cadr term))
       (let ((nth-call (caddr term)))
         (and (equal 3 (len nth-call))
              (symbolp (car nth-call))
              (equal "NTH" (symbol-name (car nth-call)))
              (symbolp (caddr nth-call))
              (equal "ST" (symbol-name (caddr nth-call)))
              (or (equal (cadr nth-call) ''4)
                  (equal (cadr nth-call) ''3))))))


(defun smaller-offset-term-aux (term1 term2)
  (declare (type t term1 term2)
           (xargs :mode :program))
  (if (and (offset-has-expected-form term1)
           (offset-has-expected-form term2))
      (let ((nth-call1 (caddr term1))
            (nth-call2 (caddr term2)))
        ;stack ones come befores locals ones
        (if (and (equal ''3 (cadr nth-call1))
                 (equal ''4 (cadr nth-call2)))
            t
          (if (and (equal ''3 (cadr nth-call2))
                   (equal ''4 (cadr nth-call1)))
              nil
            ;;we must be dealing with two locals ones or two stack ones,
            ;;so we just compare the offsets numerically
            ;; lexorder is like <=, but what we want is like <, so we use
            ;; the not of the lexorder of the arguments in reverse order
            (not (lexorder (cadr term2) (cadr term1))))))
    (acl2::smaller-term term1 term2)))

;Terms like (NTH '3 ST) don't match the '(BINARY-+ <constant> (NTH '3 ST)) pattern,
;so we forge an equivalent term that matches the pattern.
(defun convert-term-to-plus-form (term)
  (declare (type t term)
           (xargs :mode :program))
  (if (and (equal 3 (len term))
           (symbolp (car term))
           (equal "NTH" (symbol-name (car term)))
           (symbolp (caddr term))
           (equal "ST" (symbol-name (caddr term)))
           (or (equal (cadr term) ''4)
               (equal (cadr term) ''3)))
      `(binary-+ '0 ,term)
    term))

;;(smaller-offset-term '(BINARY-+ '2 (NTH '3 ST)) '(BINARY-+ '2 (NTH '4 ST)))
(defun smaller-offset-term (term1 term2)
  (declare (xargs :mode :program))
  (smaller-offset-term-aux (convert-term-to-plus-form term1) (convert-term-to-plus-form term2)))

;The arguments to this function are terms
(defun smaller-params (denvr1 offset1 denvr2 offset2)
  (declare (xargs :mode :program))
  (if (acl2::smaller-term denvr1 denvr2)
      t
    (if (acl2::smaller-term denvr2 denvr1)
        nil
      (smaller-offset-term offset1 offset2))))


;;
;; NTHWORD (where should this go?)
;;

(defund nthword (n value)
  (if (zp n)
      (loghead 16 value)
    (nthword (+ -1 n) (logtail 16 value))))

(defthm nthword-of-0
  (equal (nthword 0 value)
         (loghead 16 value))
  :hints (("Goal" :in-theory (enable nthword))))

(defthmd nthword-rewrite
  (implies (natp n)
           (equal (nthword n x)
                  (loghead 16 (logtail (* 16 n) x))))
  :hints (("Goal" :in-theory (enable nthword))))

;loops with LOGTAIL-16-LOGHEAD-32
(defthmd nthword-constant-opener
  (equal (nthword n value)
         (if (zp n)
             (loghead 16 value)
             (nthword (+ -1 n)
                            (logtail 16 value))))
  :hints (("Goal" :in-theory (enable nthword))))

;gen to any size >= 16
(defthm usb16-nthword
  (unsigned-byte-p 16 (nthword n value))
  :hints (("Goal" :in-theory (enable nthword))) )

;gen
(defthm nthword-1-of-logapp
  (equal (nthword 1 (logapp 16 x y))
         (nthword 0 y))
  :hints (("Goal" :in-theory (e/d (nthword-constant-opener) (;logtail-16-loghead-32
                                                             )))))

(defthm logapp-nthword-self-hack
  (equal (logapp 16 x (nthword 1 x))
         (loghead 32 x))
  :hints (("Goal" :in-theory (e/d (nthword-constant-opener) (;logtail-16-loghead-32
                                                             )))))


;;
;; READ-DATA-WORD
;;

;bzo don't mention aamp?
(defun aamp-ramp (ram)
  (declare (type t ram))
  (and (ramp ram)
       (equal (mem::size ram) (expt 2 32))))

;; For execution only.
;; bzo still makes fixnums to pass into RD.
;; Inline the call to acl2::logext-31-exec?
;bzo denv is now a 15 bit quantity in the stobj...
(defund read-data-word-exec (denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p (:executable-counterpart expt) ;yuck?
                                                           ))))
           )
  (the-usb 16 (let ((word-ad (the (unsigned-byte 31) (+ offset (the-usb 31 (* 65536 denvr)))))) ;Bbzo loghead 15 okay?
                (declare (type (unsigned-byte 31) word-ad))
                (let ;((ad0 (the-sb 32 (ash (the-sb 31 (acl2::logext-31-exec word-ad)) 1))))
                    ((ad0 (the-usb 32 (ash word-ad 1))))
;                  (declare (type (signed-byte 32) ad0)) ;ad0 is a byte address
                  (declare (type (unsigned-byte 32) ad0)) ;ad0 is a byte address
                  (let ;((ad1 (the-sb 32 (+ 1 ad0)))) ;ad1 is a byte address
                      ((ad1 (the-usb 32 (+ 1 ad0)))) ;ad1 is a byte address
                    ;(declare (type (signed-byte 32) ad1))
                    (declare (type (unsigned-byte 32) ad1))
                    (the-usb 16
                             (+ (the-usb 8 (rd ad0 ram))
                                (the-usb 16 (* 256 (the-usb 8 (rd ad1 ram)))))))))))

;I'm intending to leave this open in this file
;logext 15 of denv?
(defun addresses-of-data-word (denvr offset)
  (word-ad-to-byte-ads (logapp 16
                               offset
                               (loghead 15 denvr) ;;(logext 15 denvr) ;bzo drop this?
                               )))

;; Read the 2-byte word of data at offset OFFSET in data environment DENVR in
;; RAM.  The byte at the lower address goes into the least significant bits of
;; the result.
;;
(defund read-data-word (denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                                         acl2::loghead-identity
                                                         read-data-word-exec
                                                         acl2::ash-as-logapp
                                                         word-ad-to-byte-ads
                                                         acl2::sum-with-shift-becomes-logapp-constant-version)
                                                        (acl2::logapp-0-part-2-better))))))
  (mbe :exec (read-data-word-exec denvr offset ram)
       :logic (wintlist (rd-list (addresses-of-data-word denvr offset)
                                 ram))))

;bzo rewrite and/or linear rules too?
(defthm read-data-word-non-negative-integerp-type
  (and (<= 0 (read-data-word denvr offset ram))
       (integerp (read-data-word denvr offset ram)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-data-word))))

;our rule is better:
(in-theory (disable (:type-prescription read-data-word)))

(defthmd usb16-of-read-data-word
  (unsigned-byte-p 16 (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm unsigned-byte-p-of-read-data-word
  (implies (<= 16 n)
           (equal (unsigned-byte-p n (read-data-word denvr offset ram))
                  (integerp n)))
  :hints (("Goal" :use (:instance usb16-of-read-data-word)
           :in-theory (disable usb16-of-read-data-word))))

(defthm usb16-of-read-data-word-fw
  (unsigned-byte-p 16 (read-data-word denvr offset ram))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-word denvr offset ram)))))

(defthm read-data-word-of-loghead15
  (equal (read-data-word (loghead 15 denvr) offset ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word
                                     ACL2::LOGEXT-LOGAPP
                                     WORD-AD-TO-BYTE-ADS))))

(defthm read-data-word-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (read-data-word denvr offset ram)
                  (read-data-word denvr 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm read-data-word-of-loghead16-2
  (equal (read-data-word denvr (loghead 16 offset) ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm read-data-word-subst-alt
  (implies (and (equal (loghead 16 offset1) offset2)
                (syntaxp (and (term-order offset2 offset1)
                              (not (equal offset1 offset2))))
                )
           (equal (read-data-word denvr offset1 ram)
                  (read-data-word denvr offset2 ram))))

(defthm read-data-word-subst
  (implies (and (equal (loghead 16 offset1) (loghead 16 offset2))
                (syntaxp (and (term-order offset2 offset1)
                              (not (equal offset1 offset2))))
                )
           (equal (read-data-word denvr offset1 ram)
                  (read-data-word denvr offset2 ram)))
  :hints (("Goal" :use ((:instance read-data-word-of-loghead16-2 (offset offset1))
                        (:instance read-data-word-of-loghead16-2 (offset offset2)))
           :in-theory (disable read-data-word-of-loghead16-2))))

;bzo bad name
(defthm read-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                )
           (equal (read-data-word denvr k ram)
                  (read-data-word denvr (acl2::loghead 16 k) ram)))
  :hints (("Goal" :in-theory (disable read-data-word-of-loghead16-2)
           :use ((:instance read-data-word-of-loghead16-2 (offset (acl2::loghead 16 k)))
                 (:instance read-data-word-of-loghead16-2 (offset k))))))

(defthm read-data-word-subst-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (and (term-order denvr2 denvr1)
                              (not (equal denvr1 denvr2)))))
           (equal (read-data-word denvr1 offset ram)
                  (read-data-word denvr2 offset ram)))
  :hints
  (("Goal" :use ((:instance read-data-word-of-loghead15
                            (denvr denvr1))
                 (:instance read-data-word-of-loghead15
                            (denvr denvr2)))
    :in-theory (disable read-data-word-of-loghead15))))


(defthm read-data-word-of-sum-of-loghead
  (implies (integerp offset2)
           (equal (read-data-word denvr (+ offset1 (loghead 16 offset2)) ram)
                  (read-data-word denvr (+ offset1 offset2) ram)))
  :hints (("Goal" :use ((:instance read-data-word-of-loghead16-2 (offset  (+ offset1 (loghead 16 offset2))))
                        (:instance read-data-word-of-loghead16-2 (offset  (+ offset1 offset2))))
           :in-theory (disable read-data-word-of-loghead16-2))))

(defthm read-data-word-of-sum-of-loghead-alt
  (implies (integerp offset2)
           (equal (read-data-word denvr (+ (loghead 16 offset2) offset1) ram)
                  (read-data-word denvr (+ offset1 offset2) ram)))
  :hints (("Goal" :use (:instance read-data-word-of-sum-of-loghead)
           :in-theory (disable read-data-word-of-sum-of-loghead))))

;;
;; WRITE-DATA-WORD
;;


;; For execution only.
;bzo speed this up?

(defund write-data-word-exec (denvr offset value ram)
  (declare; (type t ram)
           (type integer denvr offset value)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable ash)))
                  )
           )
  (let* ((word-ad (logapp 16 offset denvr))
;;         (ad0 (acl2::logext 32 (ash word-ad 1))) ;ad0 is a byte address
         (ad0 (acl2::loghead 32 (ash word-ad 1))) ;ad0 is a byte address
         (ad1 (+ 1 ad0)) ;ad1 is a byte address
         (byte0 (loghead 8 value))
         (byte1 (loghead 8 (logtail 8 value)))
         )
    (wr ad0 byte0
        (wr ad1 byte1 ram))))


;; Write the 2-byte word VALUE into RAM at offset OFFSET in data environment
;; DENVR in RAM.  The byte at the lower address comes from the least
;; significant bits of VALUE.
;;
(defund write-data-word (denvr offset value ram)
  (declare (type integer denvr offset value)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable write-data-word-exec
                                                           ACL2::LOGEXT-LOGAPP)))))
  ;;  (wx 16 (ash (makeaddr denvr offset) 1) value ram)
  (mbe :exec (write-data-word-exec denvr offset value ram)
       :logic (wr-list (addresses-of-data-word denvr offset)
                       (enlistw 2 value)
                       ram)))

(defthm write-data-word-of-write-data-word-same-simple
  (equal (write-data-word denvr offset val1 (write-data-word denvr offset val2 ram))
         (write-data-word denvr offset val1 ram))
  :hints (("Goal" :in-theory (enable write-data-word))))

;trying disabled, since the offsets should get normalized...
(defthmd write-data-word-of-write-data-word-same-offs
  (implies (equal (loghead 16 offset1) (loghead 16 offset2))
           (equal (write-data-word denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                  (write-data-word denvr offset1 val1 ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-diff-offs
;;   (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
;;                 (not (equal (loghead 16 offset1) (loghead 16 offset2))))
;;            (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
;;                   (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
;;   :rule-classes ((:rewrite :loop-stopper nil))
;;   :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-same-denv-both
;;   (implies (syntaxp (smaller-offset-term offset2 offset1))
;;            (equal (write-data-word denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
;;                   (if (equal (loghead 16 offset1) (loghead 16 offset2))
;;                       (write-data-word denvr offset1 val1 ram)
;;                     (write-data-word denvr offset2 val2 (write-data-word denvr offset1 val1 ram)))))
;;   :rule-classes ((:rewrite :loop-stopper nil))
;;     :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-diff-denvrs
;;   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;            (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
;;                   (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
;;   :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
;;   :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-write-data-word-both
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (if (and (equal (loghead 15 denvr1)
                                  (loghead 15 denvr2))
                           (equal (loghead 16 offset1)
                                  (loghead 16 offset2)))
                      (write-data-word denvr1 offset1 val1 ram)
                    (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram)))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (write-data-word
                                   gacc::wr-list-of-cons-one
                                   )
                                  (disjoint-of-two-word-ad-to-byte-ads)))))

;improve?
(defthm write-data-word-of-write-data-word-diff-bag-phrasing
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1)) ;we sort using a complicated scheme.
                (bag::disjoint (addresses-of-data-word denvr1 offset1)
                               (addresses-of-data-word denvr2 offset2)))
           (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (write-data-word) (disjoint-of-two-word-ad-to-byte-ads)))))

(defthm write-data-word-replace-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (write-data-word denvr1 offset value ram)
                  (write-data-word denvr2 offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-loghead
  (equal (write-data-word denvr offset (loghead 16 value) ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-loghead-16
  (equal (write-data-word denvr (loghead 16 offset) value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word))))


(defthm write-data-word-of-logext-16
  (equal (write-data-word denvr (acl2::logext 16 offset) value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word
                                     gacc::wr-list-of-cons-one
                                     WORD-AD-TO-BYTE-ADS))))

(defthm write-data-word-subst-in-offset-alt
  (implies (and (equal (loghead 16 free) (loghead 16 offset))
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr free value ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word) ()))))

(defthm write-data-word-of-write-data-word-same-val
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (write-data-word denvr1 offset1 val (write-data-word denvr2 offset2 val ram))
                  (write-data-word denvr2 offset2 val (write-data-word denvr1 offset1 val ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))


;; ;bzo gen
;; (defthm write-data-word-of-sum-of-loghead
;;   (implies (integerp offset)
;;            (equal (write-data-word denvr (+ 1 (loghead 16 offset)) val ram)
;;                   (write-data-word denvr (+ 1 offset) val ram)))
;;   :hints (("Goal" :in-theory (enable write-data-word))))


(defthm write-data-word-of-sum-of-loghead
  (implies (and (integerp x)
                (integerp a)
                )
           (equal (write-data-word denvr (+ a (loghead 16 x)) val ram)
                  (write-data-word denvr (+ a x) val ram)
                  ))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-word denvr (+ k offset) value ram)
                  (write-data-word denvr (+ (loghead 16 k) offset) value ram)))
  :hints (("Goal" :use ((:instance write-data-word-of-loghead-16 (offset (+ k offset)))
                        (:instance write-data-word-of-loghead-16 (offset (+ (loghead 16 k) offset))))
           :in-theory (e/d () (write-data-word-of-loghead-16
                               ;write-data-word-equal-rewrite
                               )))))

;bzo prove WRITE-DATA-WORD-WITH-VALUE-OUT-OF-BOUNDS from WRITE-DATA-WORD-OF-LOGHEAD?
;analogue for write-data-words?
(defthm write-data-word-of-sum-normalize-constant-addend-in-value
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-word denvr offset (+ k value) ram)
                  (write-data-word denvr offset (+ (loghead 16 k) value) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORD-of-loghead
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (value (+ (loghead 16 k) value)))
                        (:instance WRITE-DATA-WORD-of-loghead
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (value (+ k value))))
           :in-theory (e/d () (WRITE-DATA-WORD-of-loghead
                               ;write-data-word-equal-rewrite
                               )))))

;zzz


;move?
(defthm helper-for-subst-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (logext-list 32 (word-ad-to-byte-ads (logapp 16 offset denvr1)))
                  (logext-list 32 (word-ad-to-byte-ads (logapp 16 offset denvr2)))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))



(defthm write-data-word-with-offset-out-of-bounds
  (implies (and (syntaxp (quotep offset))
                (not (acl2::unsigned-byte-p 16 offset)))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr (acl2::loghead 16 offset) value ram))))

;make a non syntaxp version
(defthm write-data-word-with-value-out-of-bounds
  (implies (and (syntaxp (quotep value))
                (not (acl2::unsigned-byte-p 16 value)))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr offset (acl2::loghead 16 value) ram)))
  :hints (("Goal" :in-theory (enable write-data-word word-ad-to-byte-ads))))

(defthm write-data-word-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr 0 value ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-subst-in-sum-offset
  (implies (and (equal (loghead 16 off2) free)
                (syntaxp (acl2::smaller-term free off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (write-data-word denvr (+ off1 off2) value ram)
                  (write-data-word denvr (+ off1 free) value ram))))




;;
;; Theorems about the single word ops.
;;

;Can these "already" there rules cause problems?  (I've seen a case with two
;nests of clear that were hard to normalize to the same thing, and I think the
;problem arose because of an "already-there" rule).  Maybe the "write equal
;rewrite" rules should be sufficient?

(defthm write-data-word-of-what-was-already-there-weak
  (equal (write-data-word denvr offset (read-data-word denvr offset ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable acl2::logext-logapp write-data-word read-data-word))))

;too expensive?
(defthm write-data-word-of-what-was-already-there-strong
  (implies (equal val (read-data-word denvr offset ram))
           (equal (write-data-word denvr offset val ram)
                  ram)))

;; Can cause case splits; perhaps keep it turned off until the simulation is done?
;; If so, maybe non-case splitting versions of the -diff rules are needed?
(defthm read-data-word-of-write-data-word-all-cases
  (equal (read-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
         (if (and (equal (loghead 16 offset1) (loghead 16 offset2))
                  (equal (loghead 15 denvr1) (loghead 15 denvr2)))
             (loghead 16 val)
           (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory
           (enable read-data-word
                   write-data-word
                   gacc::wr-list-of-cons-one
                   ))))

;Subsumed by read-data-word-of-write-data-word-all-cases, but this should be a "simple" rule.
(defthm read-data-word-of-write-data-word-same-simple
  (equal (read-data-word denvr offset (write-data-word denvr offset val ram))
         (loghead 16 val)))

(defthmd read-data-word-of-write-data-word-diff-bag-phrasing
  (implies (bag::disjoint (addresses-of-data-word denvr1 offset1)
                          (addresses-of-data-word denvr2 offset2))
           (equal (read-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable read-data-word write-data-word))))

;;
;; CLEAR-DATA-WORD
;;

;bzo add guard?
(defund clear-data-word (denvr offset ram1)
  (write-data-word denvr offset 0 ram1))

;see theorems about wr-bytes and copy them?

(defthm write-data-word-equal-rewrite
  (equal (equal (write-data-word denvr offset value ram1) ram2)
         (and (equal (loghead 16 value) (read-data-word denvr offset ram2))
              (equal (clear-data-word denvr offset ram1)
                     (clear-data-word denvr offset ram2))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (WRITE-DATA-WORD READ-DATA-WORD
                                                   WORD-AD-TO-BYTE-ADS
                                                   ACL2::EQUAL-LOGAPP-X-Y-Z
                                                   WR==R!
                                                   clear-data-word
                                                   )
                                  ()))))

(theory-invariant (incompatible (:rewrite write-data-word-equal-rewrite) (:definition clear-data-word)))

(defthm read-data-word-of-clear-data-word-both
  (equal (read-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
         (if (and (equal (loghead 16 offset1) (loghead 16 offset2))
                  (equal (loghead 15 denvr1) (loghead 15 denvr2)))
             0
           (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

;Subsumed by read-data-word-of-clear-data-word-both, but this should be a "simple" rule.
(defthm read-data-word-of-clear-data-word-same-simple
  (equal (read-data-word denvr offset (clear-data-word denvr offset ram))
         0))

;use the bag phrasing on the -both lemmas?
(defthmd read-data-word-of-clear-data-word-diff-bag-phrasing
  (implies (bag::disjoint (addresses-of-data-word denvr1 offset1)
                          (addresses-of-data-word denvr2 offset2))
           (equal (read-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word
                                   list::memberp-of-cons)
                                  (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-clear-data-word-same-simple
  (equal (clear-data-word denvr offset (clear-data-word denvr offset ram))
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

; ===




;; (defthm clear-data-word-of-write-data-word-diff-denvrs
;;   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;            (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (write-data-word denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
;;   :hints (("Goal" :in-theory (e/d (clear-data-word
;;                                    acl2::logext-logapp)
;;                                   (write-data-word-equal-rewrite)))))


;; (defthm clear-data-word-of-write-data-word-diff-offsets
;;   (implies (not (equal (loghead 16 offset1)
;;                        (loghead 16 offset2)))
;;            (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (write-data-word denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
;;   :hints (("Goal" :in-theory (e/d (
;;                                    clear-data-word
;;                                    acl2::logext-logapp)
;;                                   (write-data-word-equal-rewrite)))))

(defthm clear-data-word-subst-in-offset
  (implies (and (equal (loghead 16 offset) free)
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (clear-data-word denvr offset ram)
                  (clear-data-word denvr free ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-write-data-word-same-simple
  (equal (clear-data-word denvr offset (write-data-word denvr offset value ram))
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-write-data-word-all-cases
  (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
         (if (and (equal (loghead 15 denvr1) (loghead 15 denvr2))
                  (equal (loghead 16 offset1) (loghead 16 offset2)))
             (clear-data-word denvr1 offset1 ram)
           (write-data-word denvr2 offset2 val (clear-data-word denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (clear-data-word
                                   acl2::logext-logapp)
                                  (write-data-word-equal-rewrite)))))

(defthm write-data-word-subst-in-offset
  (implies (and (equal free (loghead 16 offset))
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr free value ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-sum-of-loghead
  (implies (and (integerp x)
                (integerp a)
                )
           (equal (clear-data-word denvr (+ a (loghead 16 x)) ram)
                  (clear-data-word denvr (+ a x) ram)
                  ))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-loghead-16
  (equal (clear-data-word denvr (loghead 16 offset) ram)
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp offset)
                (not (unsigned-byte-p 16 k)))
           (equal (clear-data-word denvr (+ k offset) ram)
                  (clear-data-word denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-when-already-zero
  (implies (equal (read-data-word denvr offset ram) 0)
           (equal (clear-data-word denvr offset ram)
                  ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word
                                   write-data-word-of-what-was-already-there-strong)
                                  (write-data-word-equal-rewrite)))))

(defthm clear-data-word-when-already-zero-cheap
  (implies (equal (read-data-word denvr offset ram) 0)
           (equal (clear-data-word denvr offset ram)
                  ram))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable clear-data-word-when-already-zero))))

(defthm clear-data-word-normalize-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (clear-data-word denvr offset ram)
                  (clear-data-word denvr (loghead 16 offset) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-clear-data-word-diff
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (clear-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (clear-data-word denvr1 offset1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

;dup with unforced?
;analogue for write?
(defthm clear-data-word-loghead
  (implies (and (force (integerp n))
                (force (integerp a))
                (force (integerp b)))
           (equal (clear-data-word denvr (+ a (loghead 16 (+ b n))) ram)
                  (clear-data-word denvr (+ a b n) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))




;;
;;
;; Multi-word operations
;;
;;



;;
;; WORD-ADS-TO-BYTE-ADS
;;

;;word-ads-to-byte-ads implicitly takes word-aligned input...
;; Convert a list of word addresses to a list of twice the length, containing
;; their corresponding byte addresses
;;

(defun word-ads-to-byte-ads (word-ads)
  (declare (xargs :guard (integer-listp word-ads)))
  (if (consp word-ads)
      (append (word-ad-to-byte-ads (car word-ads)) (word-ads-to-byte-ads (cdr word-ads)))
    nil))

(defthm integer-listp-of-word-ads-to-byte-ads
  (implies (integer-listp word-ads)
           (integer-listp (word-ads-to-byte-ads word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-cons
  (equal (word-ads-to-byte-ads (cons ad word-ads))
         (append (word-ad-to-byte-ads ad) (word-ads-to-byte-ads word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-append
  (equal (gacc::word-ads-to-byte-ads (append x y))
         (append (gacc::word-ads-to-byte-ads x)
                 (gacc::word-ads-to-byte-ads y))))

(defthm consp-of-word-ads-to-byte-ads
  (equal (consp (word-ads-to-byte-ads word-ads))
         (consp word-ads))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-iff
  (iff (gacc::word-ads-to-byte-ads gacc::word-ads)
       (consp gacc::word-ads))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm car-of-word-ads-to-byte-ads
  (equal (car (word-ads-to-byte-ads word-ads))
         (if (consp word-ads)
             (car (word-ad-to-byte-ads (car word-ads)))
           nil))
  :hints (("Goal" :expand (word-ads-to-byte-ads word-ads)
           :in-theory (enable word-ads-to-byte-ads))))

(defthm cdr-of-word-ads-to-byte-ads
  (equal (cdr (word-ads-to-byte-ads word-ads))
         (if (consp word-ads)
             (cons (cadr (word-ad-to-byte-ads (car word-ads)))
                   (word-ads-to-byte-ads (cdr word-ads)))
           nil))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads
                                     word-ad-to-byte-ads))))

(defthm len-of-word-ads-to-byte-ads
  (equal (len (word-ads-to-byte-ads word-ads))
         (* 2 (len word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-when-word-ads-is-not-a-consp
  (implies (not (consp word-ads))
           (equal (word-ads-to-byte-ads word-ads)
                  nil))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthmd loghead-list-of-word-ads-to-byte-ads-hack
  (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (loghead-list 31 word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads word-ad-to-byte-ads))))

(defthm memberp-of-logapp-and-word-ads-to-byte-ads
  (implies (integer-listp word-ads)
           (equal (list::memberp (logapp 17 (logapp 1 b offset) denvr) (word-ads-to-byte-ads word-ads))
                  (list::memberp (logapp 16 offset denvr) word-ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable list::memberp
                              word-ads-to-byte-ads
                              WORD-AD-TO-BYTE-ADS
                              ACL2::EQUAL-LOGAPP-X-Y-Z))))

(defthm memberp-of-word-ads-to-byte-ads
  (equal (memberp ad (word-ads-to-byte-ads ads))
         (and (integerp ad)
              (memberp (acl2::logcdr ad) (ifix-list ads))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (word-ads-to-byte-ads
                            list::memberp-of-cons)
                           ()))))

(defthm word-ads-to-byte-ads-of-loghead-list
  (implies (and (integerp size)
                (<= 0 size))
           (equal (word-ads-to-byte-ads (loghead-list size ads))
                  (loghead-list (+ 1 size) (word-ads-to-byte-ads ads))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads
                                     word-ads-to-byte-ads))))

(theory-invariant (incompatible (:rewrite loghead-list-of-word-ads-to-byte-ads-hack)
                                (:rewrite word-ads-to-byte-ads-of-loghead-list)))

(defthm logext-list-32-of-word-ads-to-byte-ads
  (equal (logext-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (logext-list 31 word-ads)))
  :hints (("Goal" :in-theory (enable logext-list word-ads-to-byte-ads))))

(defthm disjoint-of-word-ad-to-byte-ads-and-word-ads-to-byte-ads
  (equal (disjoint (word-ad-to-byte-ads ad)
                   (word-ads-to-byte-ads word-ads))
         (not (bag::memberp (ifix ad) (ifix-list word-ads))))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm disjoint-of-two-calls-to-word-ads-to-byte-ads
  (equal (disjoint (word-ads-to-byte-ads word-ads1) (word-ads-to-byte-ads word-ads2))
         (or (endp word-ads1)
             (endp word-ads2)
             (disjoint (ifix-list word-ads1) (ifix-list word-ads2))
             ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable word-ads-to-byte-ads))))

(defthm count-in-word-ads-to-byte-ads
  (implies (integer-listp ads) ;bzo
           (equal (bag::count bag::arbitrary-element (word-ads-to-byte-ads ads))
                  (if (integerp bag::arbitrary-element)
                      (bag::count (acl2::logcdr bag::arbitrary-element) ads)
                    0)))
  :hints (("Goal" :in-theory (e/d (word-ads-to-byte-ads
                                   acl2::equal-logapp-x-y-z
                                   acl2::ash-as-logapp
                                   word-ad-to-byte-ads)
                                  (acl2::logapp-0-part-2-better)))))



(defthm subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads
  (implies (and (bag::subbagp ads1 ads2)
                (integer-listp ads1)
                (integer-listp ads2))
           (bag::subbagp (word-ads-to-byte-ads ads1)
                         (word-ads-to-byte-ads ads2)))
  :hints (("Goal" ; :induct (double-cdr-induct ads1 ads2)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable len word-ads-to-byte-ads))))

;; (implies (bag::unique (loghead-list 16 word-ads))
;;          (bag::unique word-ads))

;drop?
(defthm unique-of-word-ads-to-byte-ads
  (implies (and (bag::unique (loghead-list 16 word-ads))
                (integer-listp word-ads) ;bzo
                )
           (bag::unique (word-ads-to-byte-ads word-ads)))
  :hints(("Goal" :in-theory (enable list::memberp-of-cons))))


(defthm unique-of-word-ads-to-byte-ads-better
  (implies (integer-listp word-ads)
           (equal (unique (word-ads-to-byte-ads word-ads))
                  (unique word-ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable list::memberp-of-cons)
           :expand ((unique word-ads)
                    (word-ads-to-byte-ads word-ads)))))

(defthm firstn-of-word-ads-to-byte-ads-helper
  (implies (integerp n)
           (equal (firstn (* 2 n) (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (firstn n word-ads))))
  :hints (("Goal" :expand (WORD-ADS-TO-BYTE-ADS (FIRSTN N WORD-ADS))
           :in-theory (enable word-ads-to-byte-ads (:induction firstn)))))

(defthm firstn-of-word-ads-to-byte-ads
  (implies (evenp n)
           (equal (firstn n (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (firstn (/ n 2) word-ads))))
  :hints (("Goal" :use (:instance firstn-of-word-ads-to-byte-ads-helper (n (/ n 2)))
           :in-theory (disable firstn-of-word-ads-to-byte-ads-helper))))

(defthm nthcdr-of-word-ads-to-byte-ads-helper
  (implies (integerp n)
           (equal (nthcdr (* 2 n) (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (nthcdr n word-ads))))
  :hints (("Goal" :expand (WORD-ADS-TO-BYTE-ADS (NTHCDR N WORD-ADS))
           :in-theory (enable word-ads-to-byte-ads (:induction nthcdr)))))

(defthm nthcdr-of-word-ads-to-byte-ads
  (implies (evenp n)
           (equal (nthcdr n (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (nthcdr (/ n 2) word-ads))))
  :hints (("Goal" :use (:instance nthcdr-of-word-ads-to-byte-ads-helper (n (/ n 2)))
           :in-theory (disable nthcdr-of-word-ads-to-byte-ads-helper))))

;;
;; READ-DATA-WORDS
;;

;; For execution only:
;; bzo think more about how to make this fast
;; drop the loghead in (loghead 16 value)?
;put in a case for 1?
;bzo should we restrict numwords to be a fixnum? ask hardin? will mean read-data-words has the same restriction...
(defund read-data-words-exec (numwords denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (type (unsigned-byte 31) numwords) ;trying...;(type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram))
           )
  (if (equal 2 numwords) ;any other special cases?
      (let ((word-ad0 (logapp 16 offset denvr)))
        (declare (type (unsigned-byte 31) word-ad0))
        (let ((word-ad1 (logapp 16 (+ 1 offset) denvr)))
          (declare (type (unsigned-byte 31) word-ad1))
          (let ;;((ad0 (the-sb 32 (ash (the-sb 31 (acl2::logext 31 word-ad0)) 1)))) ;ad0 is a byte address
              ((ad0 (the-usb 32 (ash (the-usb 31 (acl2::loghead 31 word-ad0)) 1)))) ;ad0 is a byte address
            ;;(declare (type (signed-byte 32) ad0))
            (declare (type (unsigned-byte 32) ad0))
            (let ((ad1 (+ 1 ad0))) ;;ad1 is a byte address
              (let ;((ad2 (acl2::logext 32 (ash word-ad1 1)))) ;ad2 is a byte address
                  ((ad2 (acl2::loghead 32 (ash word-ad1 1)))) ;ad2 is a byte address
                (let ((ad3 (+ 1 ad2))) ;ad3 is a byte address
                  (logapp 24 (logapp 16 (logapp 8 (rd ad0 ram) (rd ad1 ram)) (rd ad2 ram)) (rd ad3 ram))))))))
    (if (equal 1 numwords)
        (read-data-word-exec denvr offset ram)
      (if (zp numwords)
          0
        (logapp 16
                (read-data-word-exec denvr offset ram)
                (read-data-words-exec (+ -1 numwords) denvr (loghead 16 (+ 1 offset)) ram))))))

;;
;; ADDRESSES-OF-DATA-WORDS
;;

(defun addresses-of-data-words (numwords denvr offset)
  (word-ads-to-byte-ads (logapp-list 16
                                     (offset-range-wrap 16 offset numwords)
                                     (loghead 15 denvr) ;(logext 15 denvr)
                                     )))


(defthm consp-of-addresses-of-data-words
  (equal (consp (gacc::addresses-of-data-words numwords denvr offset))
         (not (zp numwords)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))


(defund read-data-words (numwords denvr offset ram)
  (declare (type (unsigned-byte 31) numwords) ;trying...;(type (integer 0 *) numwords); (type (integer 0 *) numwords)
           (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs  :guard (aamp-ramp ram)
                   :guard-hints (("Goal" :expand  ((offset-range-wrap 16 offset 2)
                                                   (offset-range-wrap 16 offset numwords))
                                  :induct t
                                  :do-not '(generalize eliminate-destructors)
                                  :in-theory (e/d (word-ad-to-byte-ads
                                                   ACL2::SUM-WITH-SHIFT-BECOMES-LOGAPP-CONSTANT-VERSION
                                                   read-data-word-exec
                                                   acl2::logext-logapp
                                                   acl2::ash-as-logapp
                                                   read-data-words-exec
                                                   acl2::loghead-identity
                                                   )
                                                  (acl2::logapp-0-part-2-better
                                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant))))))
  (mbe :exec (read-data-words-exec numwords denvr offset ram)
       :logic (wintlist (rd-list (addresses-of-data-words numwords denvr offset)
                                 ram))))

;bzo rewrite and/or linear rules too?
(defthm read-data-words-non-negative-integerp-type
  (and (<= 0 (read-data-words numwords denvr offset ram))
       (integerp (read-data-words numwords denvr offset ram)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-data-words))))

;our rule is better:
(in-theory (disable (:type-prescription read-data-words)))


(defthm read-data-words-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (read-data-words numwords denvr offset ram)
                  (read-data-words numwords denvr 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthmd read-data-words-opener
  (implies (and (syntaxp (and (quotep numwords)
                              (<= (cadr numwords) 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                              ))
                (not (zp numwords)))
           (equal (read-data-words numwords denvr offset ram)
                  (logapp 16
                          (read-data-word denvr offset ram)
                          (read-data-words (+ -1 numwords)
                                           denvr (+ 1 (ifix offset))
                                           ram))))
  :hints
  (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS)
                    (OFFSET-RANGE-WRAP 16 0 NUMWORDS))
    :in-theory
    (e/d (READ-DATA-WORD
          read-data-words
          WORD-AD-TO-BYTE-ADS
          OFFSET-RANGE-WRAP-CONST-OPENER
          ACL2::ASH-AS-LOGAPP
          ACL2::LOGEXT-LOGAPP)
         ( ;makeaddr-of-+-loghead
          ACL2::LOGAPP-0-PART-2-BETTER
          ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
          )))))

(defthmd read-data-words-alt-def
  (equal (read-data-words numwords denvr offset ram)
         (if (zp numwords)
             0
           (logapp 16
                   (read-data-word denvr offset ram)
                   (read-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))))
  :rule-classes :definition
  :hints (("Goal" :use (:instance read-data-words-opener)
           :in-theory (disable read-data-words-opener))))

(defthm read-data-words-of-1
  (equal (read-data-words 1 denvr offset ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words-opener))))

(defthm read-data-words-of-loghead-around-denvr
  (equal (read-data-words numwords (loghead 16 denvr) offset ram)
         (read-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-of-loghead-around-offset
  (equal (read-data-words numwords denvr (loghead 16 offset) ram)
         (read-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-subst
  (implies (and (equal (loghead 16 offset) (loghead 16 free))
                (syntaxp (acl2::smaller-term free offset))
                (integerp offset)
                (integerp free))
           (equal (read-data-words numwords denvr offset ram)
                  (read-data-words numwords denvr free ram)))
  :hints (("Goal" :in-theory (enable read-data-words))))

(DEFTHM LEN-OF-LOGHEAD-LIST
  (EQUAL (LEN (LOGHEAD-LIST SIZE I-LIST))
         (LEN I-LIST))
  :HINTS (("Goal" :IN-THEORY (ENABLE LOGHEAD-LIST))))

;rewrite too?
(defthm unsigned-byte-p-of-read-data-words
  (implies (acl2::natp numwords)
           (unsigned-byte-p (* 16 numwords) (read-data-words numwords denvr offset ram)))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-words numwords denvr offset ram))))
  :hints (("Goal" :in-theory (enable read-data-words))))


(defthm unsigned-byte-p-of-read-data-words-gen
  (implies (<= (* 16 numwords) n)
           (equal (unsigned-byte-p n (read-data-words numwords denvr offset ram))
                  (and (integerp n)
                       (<= 0 n))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-of-read-data-words)
           :use (:instance  unsigned-byte-p-of-read-data-words))))



;;
;;
;; WRITE-DATA-WORDS
;;
;;

;bzo think more about how to make this fast
;drop the loghead in (loghead 16 value)?
(defund write-data-words-exec (numwords denvr offset value ram)
  (declare (type integer denvr offset value)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram)
                  :verify-guards nil ;we do it below
                  )
           )
  (if (zp numwords)
      ram
    (if (equal 2 numwords) ;any other special cases?
        (let* ((word-ad0 (logapp 16 offset denvr))
               (word-ad1 (logapp 16 (+ 1 offset) denvr))
;;               (ad0 (acl2::logext 32 (ash word-ad0 1))) ;ad0 is a byte address
               (ad0 (acl2::loghead 32 (ash word-ad0 1))) ;ad0 is a byte address
               (ad1 (+ 1 ad0)) ;;ad1 is a byte address
;;               (ad2 (acl2::logext 32 (ash word-ad1 1))) ;ad2 is a byte address
               (ad2 (acl2::loghead 32 (ash word-ad1 1))) ;ad2 is a byte address
               (ad3 (+ 1 ad2)) ;ad3 is a byte address
;bzo use masks here?
               (byte0 (loghead 8 value))
               (byte1 (loghead 8 (logtail 8 value)))
               (byte2 (loghead 8 (logtail 16 value)))
               (byte3 (loghead 8 (logtail 24 value)))
               )
          (wr ad0 byte0 (wr ad1 byte1 (wr ad2 byte2 (wr ad3 byte3 ram)))))
      (write-data-word-exec
       denvr offset value ;(loghead 16 value)
       (write-data-words-exec (+ -1 numwords) denvr (+ 1 offset) (logtail 16 value) ram)))))

(defthm memory-p-of-write-data-word-exec
  (implies (mem::memory-p ram)
           (mem::memory-p (write-data-word-exec denvr offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-word-exec))))

(defthm memory-p-of-write-data-words-exec
  (implies (MEM::MEMORY-P ram)
           (MEM::MEMORY-P (write-data-words-exec numwords denvr offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-words-exec))))

(defthm size-of-write-data-word-exec
  (implies (mem::memory-p ram)
           (equal (mem::size (write-data-word-exec denvr offset value ram))
                  (mem::size ram)))
  :hints (("Goal" :in-theory (enable write-data-word-exec))))

(defthm size-of-write-data-words-exec
  (implies (mem::memory-p ram)
           (equal (mem::size (write-data-words-exec numwords denvr offset value ram))
                  (mem::size ram)))
  :hints (("Goal" :in-theory (enable write-data-words-exec))))

(verify-guards write-data-words-exec)


(in-theory (disable WORD-AD-TO-BYTE-ADS
                    WORD-ADs-TO-BYTE-ADS
                    write-data-word-exec))

;handle wr-list of append?

;; Write (the low NUMWORDS words of) VALUE at offset OFFSET in data environment DENV in ram RAM.
;order of word-ads-to-byte-ads and append-denv-list?
;we intend to keep this closed up, but we can open it if we have to...
;maybe we don't even need the call to offset-range-wrap, since logapp-list chops its args?
;16 or 15???
;; Wraps around if we reach the end of DENVR.
;; The low-order bits of VALUE go into the lower addresses in DENV (unless wrapping occurs).

(defund write-data-words (numwords denvr offset value ram)
  (declare (type (integer 0 *) numwords)
           (type integer offset value denvr)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :expand  (offset-range-wrap 16 offset numwords)
                                 :induct t
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d (WORD-AD-TO-BYTE-ADS
                                                  OFFSET-RANGE-WRAP-CONST-OPENER
                                                  WRITE-DATA-WORD-EXEC
                                                  ACL2::LOGEXT-LOGAPP
                                                  write-data-words-exec
                                                  gacc::wr-list-of-cons-one)
                                                 (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT))))))
  (mbe :exec (write-data-words-exec numwords denvr offset value ram)
       :logic (wr-list (addresses-of-data-words numwords denvr offset)
;           (word-list-to-byte-list (split-into-words numwords value))
                       (enlistw (* 2 numwords) value)
                       ram)))

(defthm write-data-words-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (write-data-words numwords denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (write-data-words numwords denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (write-data-words numwords
                                    denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthmd write-data-words-opener
  (implies (and (syntaxp (and (quotep numwords)
                              (<= (cadr numwords) 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                              ))
                (not (zp numwords)))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-word denvr offset (loghead 16 value)
                                   (write-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) (logtail 16 value)
                                                     ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS))
           :in-theory (e/d (write-data-words write-data-word
                                             acl2::logext-logapp
                                             gacc::wr-list-of-cons-one
                                             WORD-AD-TO-BYTE-ADS)
                           ()))))

(defthmd write-data-words-alt-def
  (equal (write-data-words numwords denvr offset value ram)
         (if (zp numwords)
             ram
           (write-data-word denvr offset
                            (loghead 16 value)
                            (write-data-words (+ -1 numwords)
                                              denvr
                                              (+ 1 (ifix offset))
                                              (logtail 16 value)
                                              ram))))
  :rule-classes :definition
  :hints (("Goal" :use (:instance write-data-words-opener)
           :in-theory (e/d ()
                           (write-data-word-equal-rewrite
                            write-data-words-opener
                            )))))

(defthm write-data-words-of-sum-of-loghead
  (equal (write-data-words numwords denvr (+ i (loghead 16 j)) val ram)
         (write-data-words numwords denvr (+ i (ifix j)) val ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

;; ex: (write-data-words 3 #x0001 #x0001 #xffffffffffff nil)


;; zz
;; (thm
;;  (implies (and (unique i-list)
;;                (unsigned-byte-p-list size i-list))
;;           (unique (logext-list size i-list)))
;;  :hints (("Goal" :in-theory (enable logext-list))))

;; zzz
;; (defthm read-data-words-of-write-data-word-diff-offsets
;;   (implies (and (not (bag::memberp (loghead 16 offset2) (offset-range-wrap offset1 numwords))) ;rephrase?
;;                 (integerp offset1)
;;                 (integerp offset2)
;;                 )
;;            (equal (read-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (read-data-words numwords denvr1 offset1 ram)))
;; )

;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct t
;;            :in-theory (enable read-data-words write-data-words ACL2::LOGHEAD-OF-ONE-LESS-THAN-X))))


(defthm write-data-words-of-1
  (equal (write-data-words 1 denvr offset value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :expand (write-data-words 1 denvr offset value ram)
           :in-theory (enable write-data-words write-data-word acl2::logext-logapp))))

;rename
(defthm write-data-words-replace-offset
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                (integerp offset1)
                (integerp offset2)
                )
           (equal (write-data-words numwords denvr offset1 value ram)
                  (write-data-words numwords denvr offset2 value ram)))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-of-loghead-16
  (implies (integerp offset)
           (equal (write-data-words numwords denvr (loghead 16 offset) value ram)
                  (write-data-words numwords denvr offset value ram)))
  :hints (("Goal" :use (:instance write-data-words-replace-offset
                                  (offset1 offset) (offset2  (loghead 16 offset)))
           :in-theory (disable write-data-words-replace-offset))))


(defun write-data-words-induct (numwords offset value)
  (if (zp numwords)
      (list numwords offset value)
    (write-data-words-induct (+ -1 numwords) (+ 1 offset) (logtail 16 value))))

(defthm write-data-words-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-words numwords denvr 0 value ram)))
  :hints (("subgoal *1/2" :in-theory (disable write-data-word-equal-rewrite
                                              write-data-words-opener)
           :use ((:instance write-data-words-opener
                            (numwords numwords)
                            (denvr denvr)
                            (offset offset)
                            (ram ram)
                            )
                 (:instance write-data-words-opener
                            (numwords numwords)
                            (denvr denvr)
                            (offset 0)
                            (ram ram)
                            )))
          ("Goal" :in-theory (e/d (zp) ())
           :do-not '(generalize eliminate-destructors)
           :induct (write-data-words-induct numwords offset value))))

(defthm write-data-words-simplify-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (acl2::unsigned-byte-p 16 offset))
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-words numwords denvr (acl2::loghead 16 offset) value ram)))
  :hints (("Goal" :use (:instance write-data-words-replace-offset (offset1 (ifix offset)) (offset2 (acl2::loghead 16 offset)))
           :in-theory (disable write-data-words-replace-offset))))

;rename
(defthm write-data-words-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (acl2::unsigned-byte-p 16 a))
                (integerp a)
                (integerp b))
           (equal (write-data-words numwords denvr (+ a b) value ram)
                  (write-data-words numwords denvr (+ (acl2::loghead 16 a) b) value ram)))
  :hints (("Goal" :use ((:instance write-data-words-of-loghead-16 (offset (+ a b)))
                        (:instance write-data-words-of-loghead-16 (offset (+ (acl2::loghead 16 a) b)))
                        )
           :in-theory (disable))))



;; ;bzo gen the 2
;; (defthm read-data-word-of-write-data-words2-same
;;   (equal (read-data-word denvr offset (write-data-words 2 denvr offset val ram))
;;          (loghead 16 val))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener ;bzo
;; ;write-data-words read-data-word
;; ;offset-range-wrap-const-opener ;bzo
;;                                      ))))

(defthm write-data-words-replace-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (write-data-words numwords denvr1 offset value ram)
                  (write-data-words numwords denvr2 offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthmd loghead-list-32-of-word-ads-to-byte-ads
  (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (loghead-list 31 word-ads)))
  :hints
  (("Goal"
    :in-theory (enable loghead-list word-ads-to-byte-ads))))

(theory-invariant (incompatible (:rewrite WORD-ADS-TO-BYTE-ADS-OF-LOGHEAD-LIST) (:rewrite loghead-list-32-of-word-ads-to-byte-ads )))

(local
 (defthm read-data-word-of-write-data-words-diff-denvrs
   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
            (equal (read-data-word denvr1 offset1 (write-data-words numwords denvr2 offset2 value ram))
                   (read-data-word denvr1 offset1 ram)))
   :hints (("Goal" :in-theory (e/d (read-data-word write-data-words
                                      loghead-list-32-of-word-ads-to-byte-ads
                                      LOGHEAD-LIST-OF-LOGAPP-LIST
                                      acl2::logext-logapp)
                                   (WORD-ADS-TO-BYTE-ADS-OF-LOGHEAD-LIST
                                    LOGAPP-LIST-OF-LOGHEAD))))))

(encapsulate
 ()
 (local (defthm read-data-word-of-write-data-words-diff
          (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
                   (equal (read-data-word denvr offset1 (write-data-words numwords denvr offset2 val ram))
                          (read-data-word denvr offset1 ram)))
          :hints (("Goal" :cases ((zp numwords) (integerp offset1))
                   :in-theory (e/d (write-data-words
                                    acl2::logext-logapp
                                    read-data-word WORD-AD-TO-BYTE-ADS zp write-data-word
                                    acl2::loghead-0-hack
                                    ACL2::ASH-AS-LOGAPP
                                    zp
                                    LOGHEAD-LIST-of-LOGAPP-LIST
                                    loghead-list-of-word-ads-to-byte-ads-hack)
                                   (MEMBERP-OF-OFFSET-RANGE
                                    WORD-ADS-TO-BYTE-ADS-OF-LOGHEAD-LIST
                                    LOGAPP-LIST-OF-LOGHEAD
                                    ACL2::LOGAPP-0-PART-2-BETTER))))))

 ;put -bag-phrasing in the name? make a -both version?
 (defthmd read-data-word-of-write-data-words-diff-better
   (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
            (equal (read-data-word denvr offset1 (write-data-words numwords denvr2 offset2 val ram))
                   (read-data-word denvr offset1 ram)))
   :hints (("Goal" :cases ((equal (loghead 15 denvr) (loghead 15 denvr2)))))))


;; (defthm read-data-word-of-write-data-words-hack
;;   (implies (integerp offset)
;;            (equal (read-data-word denvr offset (write-data-words 2 denvr (+ -1 offset) value ram))
;;                   (loghead 16 (logtail 16 value))))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener))))




;; (defthm read-data-word-of-write-data-words-special-case
;;   (implies (and (equal offset1 (+ 1 offset2))
;;                 (integerp offset2))
;;            (equal (read-data-word denvr offset1 (write-data-words 2 denvr offset2 value ram))
;;                   (loghead 16 (logtail 16 value))))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener))))

;bzo is there a non-2 version?
(DEFUN WRITE-DATA-WORDS-INDUCT-wrap2
  (NUMWORDS OFFSET VALUE)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE)
      (WRITE-DATA-WORDS-INDUCT-wrap2 (+ -1 NUMWORDS)
                                     (loghead 16 (+ 1 OFFSET))
                                     (LOGTAIL 16 VALUE))))

(encapsulate
 ()

 ;; The disable of the executable-counterpart of expt, below, was added in
 ;; order to avoid the following error in Allegro CL:
 ;; Error: Attempt to create an integer which is too large to represent.
 ;; The defthm just above it was then necessary.

 (local (defthm expt-2-16 (equal (expt 2 16) 65536)))
 (local (in-theory (disable (expt))))

 ;; requires denvrs to match
 (local (defthm read-data-word-of-write-data-words-same
          (implies (and (< (loghead 16 (- offset offset2)) numwords)
                        (integerp offset)
                        (integerp offset2)
                        (integerp numwords)
                        )
                   (equal (read-data-word denvr offset (write-data-words numwords denvr offset2 value ram))
                          (nthword (loghead 16 (- offset offset2)) value)))
          :hints (("subgoal *1/2" :use ((:instance WRITE-DATA-WORDS-OF-LOGHEAD-16
                                                   (offset (+ 1 offset2)))
                                        (:instance write-data-words-opener
                                                   (numwords numwords)
                                                   (denvr denvr)
                                                   (offset offset2)
                                                   (ram ram))))
                  ("Goal" :in-theory (e/d (zp nthword-rewrite
                                              acl2::loghead-of-minus
                                              acl2::loghead-sum-split-into-2-cases
                                              )
                                          (WRITE-DATA-WORDS-OF-LOGHEAD-16
;WRITE-DATA-WORDS-EQUAL-REWRITE
                                           WRITE-DATA-WORD-EQUAL-REWRITE))
                   :do-not '(generalize eliminate-destructors)
                   :induct (write-data-words-induct-wrap2 numwords offset2 value)))))

 (local (defthm read-data-word-of-write-data-words-diff-better-better
          (implies(and (<= numwords (loghead 16 (- offset1 offset2)))
                       (integerp offset1)
                       (integerp offset2)
                       (integerp numwords)
                       )
                  (equal (read-data-word denvr offset1 (write-data-words numwords denvr2 offset2 value ram))
                         (read-data-word denvr offset1 ram)))
          :hints (("Goal" :in-theory (e/d (memberp-of-offset-range
                                           read-data-word-of-write-data-words-diff-better)
                                          ()))) ))


;make a vesion for clear?
 (defthm read-data-word-of-write-data-words-all-cases
   (implies (and (integerp offset1)
                 (integerp offset2)
                 )
            (equal (read-data-word denvr1 offset1 (write-data-words numwords denvr2 offset2 value ram))
                   (if (and (equal (loghead 15 denvr1) (loghead 15 denvr2))
                            (< (loghead 16 (- offset1 offset2)) (nfix numwords)))
                       (nthword (loghead 16 (- offset1 offset2)) value)
                     (read-data-word denvr1 offset1 ram))))))


;zzz


;bzo allow the denvrs to differ here and elsewhere
(defthm read-data-words-of-write-data-word-diff
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (write-data-word denvr offset2 val ram))
                  (read-data-words size denvr offset1 ram)))
  :otf-flg t
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 0 SIZE))
           :cases ((EQUAL (LOGHEAD '16 (ifix OFFSET2)) (LOGHEAD '16 (ifix OFFSET1)))
;                          (and (not (integerp offset1)) (integerp offset2))
;                          (and (not (integerp offset1)) (integerp offset2))
 ;                         (not (integerp offset2))
                          )
           :in-theory (e/d (read-data-words
                            loghead-list-of-logapp-list
                            WORD-AD-TO-BYTE-ADS
                            write-data-word
                            acl2::logext-logapp
                            ACL2::ASH-AS-LOGAPP
                            list::memberp-of-cons
                            RD-OF-WR-LIST-DIFF
                            )
                           (LOGAPP-LIST-OF-LOGHEAD
                            ;ACL2::EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                            ACL2::LOGAPP-0-PART-2-BETTER
                            MEMBERP-OF-OFFSET-RANGE)))))

(defthm read-data-word-gets-the-second-word
  (implies (integerp x)
           (equal (read-data-word denvr (+ -1 x) (write-data-words 2 denvr (+ -2 x) val ram))
                  (loghead 16 (logtail 16 val))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORDS-OPENER))))


;gen or drop?
(defthm read-data-words-of-write-data-words2
  (equal (read-data-words 2 denvr offset (write-data-words 2 denvr offset val ram))
         (loghead 32 val))
  :hints (("Goal" :in-theory (enable READ-DATA-WORDS-OPENER
                                     write-DATA-WORDS-OPENER))))

(defthm read-data-words-of-write-data-words
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (read-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (read-data-words
                                   ACL2::LOGEXT-LOGAPP ;possible loops?

                                   ACL2::LOGHEAD-LOGAPP
                                   LOGHEAD-LIST-OF-LOGAPP-LIST

                                   ACL2::ASH-AS-LOGAPP
                                   write-data-words)
                                  (LOGAPP-LIST-OF-LOGHEAD

                                   READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   ACL2::LOGAPP-0-PART-2-BETTER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS)))))

(defthm write-data-words-of-write-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))
                  (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))))
  :hints (("Goal" :in-theory (e/d (write-data-words
                                   LOGHEAD-LIST-OF-LOGAPP-LIST)
                                  (LOGAPP-LIST-OF-LOGHEAD
                                   READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   ACL2::PLUS-OF-LOGAPP-SUCK-IN)))))

(defthm write-data-words-of-write-data-words-same
  (implies (and (equal denvr1 denvr2) ;bzo gen
                (equal offset1 offset2)
                (equal numwords1 numwords2)
                )
           (equal (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 ram)))
  :hints (("Goal" :in-theory (e/d (write-data-words)
                                  (READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   ACL2::PLUS-OF-LOGAPP-SUCK-IN)))))

;move
(defthm disjoint-of-word-ads-to-byte-ads
  (implies (and (integer-listp x)
                (integer-listp y))
           (equal (disjoint x (word-ads-to-byte-ads y))
                  (disjoint (logcdr-list x) y)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm subbagp-of-word-ad-to-byte-ads-and-word-ads-to-byte-ads
  (implies (list::memberp ad ads)
           (bag::subbagp (word-ad-to-byte-ads ad)
                         (word-ads-to-byte-ads ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(local (in-theory (disable MEMBERP-OF-OFFSET-RANGE)))

(encapsulate
 ()

 (local (defthmd write-data-words-of-write-data-word-cover-helper
          (implies (and (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
                        (integerp numwords)
                        (< 0 numwords))
                   (equal (write-data-words numwords denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                          (write-data-words numwords denvr offset1 val1 ram)))
          :hints (("Goal" ; :cases (zp numwords)
                   :in-theory (e/d (loghead-list-of-logapp-list
                                    zp write-data-word write-data-words acl2::logext-logapp)
                                   (LOGAPP-LIST-OF-LOGHEAD
                                    ACL2::LOGAPP-0-PART-2-BETTER))
                   ))))

 (defthm write-data-words-of-write-data-word-cover
   (implies (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
            (equal (write-data-words numwords denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                   (write-data-words numwords denvr offset1 val1 ram)))
   :hints (("Goal" :use (:instance write-data-words-of-write-data-word-cover-helper)))))

(defthmd write-data-words-of-write-data-words-cover
  (implies (bag::subbagp (offset-range-wrap 16 offset2 numwords2)
                         (offset-range-wrap 16 offset1 numwords1) )
           (equal (write-data-words numwords1 denvr offset1 val1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (write-data-words numwords1 denvr offset1 val1 ram)))
  :hints (("Goal" :cases (zp numwords)
           :in-theory (e/d (LOGHEAD-LIST-OF-LOGAPP-LIST
                              zp write-data-word write-data-words acl2::logext-logapp)
                           (LOGAPP-LIST-OF-LOGHEAD)))))


;; (thm
;;  (equal (logcdr-list (word-ads-to-byte-ads ads))
;;         need a way to state this...)
;;  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm write-data-word-of-write-data-words-diff-denvrs
  (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
           (equal (write-data-word denvr1 offset1 val1 (write-data-words numwords denvr2 offset2 val2 ram))
                  (write-data-words numwords denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
  :hints (("Goal" ;:cases ((equal (loghead 15 denvr1) (loghead 15 denvr2)))
           :in-theory (e/d (write-data-words
                            write-data-word
                            acl2::logext-logapp
                            LOGHEAD-LIST-OF-LOGAPP-LIST
                            )
                           (
                            disjoint-of-WORD-AD-TO-BYTE-ADS
                            LOGAPP-LIST-OF-LOGHEAD
                            disjoint-of-word-ads-to-byte-ads)))))



(encapsulate
 ()
 (local (defthm write-data-word-of-write-data-words-diff-same-denvr
          (implies (and ;(integerp offset2) ;bzo failed *with* this hyp
;                     (syntaxp (smaller-params denvr offset2 denvr offset1))
                    (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords))))
                   (equal (write-data-word denvr offset1 val1 (write-data-words numwords denvr offset2 val2 ram))
                          (write-data-words numwords denvr offset2 val2 (write-data-word denvr offset1 val1 ram))))

          :hints (("Goal" ;:cases ((equal (loghead 15 denvr1) (loghead 15 denvr2)))
                   :in-theory (e/d (write-data-words
                                    write-data-word
                                    acl2::logext-logapp
                                    LOGHEAD-LIST-OF-LOGAPP-LIST

                                    )
                                   (disjoint-of-WORD-AD-TO-BYTE-ADS
                                    LOGAPP-LIST-OF-LOGHEAD
                                    disjoint-of-word-ads-to-byte-ads))))))

 (defthm write-data-word-of-write-data-words-diff
   (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                 (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords))))
            (equal (write-data-word denvr1 offset1 val1 (write-data-words numwords denvr2 offset2 val2 ram))
                   (write-data-words numwords denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal"  :use (:instance WRITE-DATA-WORD-OF-WRITE-DATA-WORDS-DIFF-DENVRS)
            :in-theory (disable WRITE-DATA-WORD-OF-WRITE-DATA-WORDS-DIFF-DENVRS
                                WRITE-DATA-WORD-EQUAL-REWRITE)))))


(local (in-theory (disable disjoint-of-WORD-AD-TO-BYTE-ADS
                           disjoint-of-word-ads-to-byte-ads)))

;;
;; CLEAR-DATA-WORDS
;;

;bzo add guard?
(defund clear-data-words (numwords denvr offset ram1)
  (write-data-words numwords denvr offset 0 ram1))

(defthm clear-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (clear-data-words numwords denvr offset ram)
                  ram))
  :hints (("Goal" :in-theory (e/d (clear-data-words clear-data-word)
                                  (write-data-word-equal-rewrite  write-data-words-opener)))))

;;
;; theorems about write-data-words, etc.
;;

(defthm write-data-words-equal-rewrite
  (implies (<= numwords 65536)
           (equal (equal (write-data-words numwords denvr offset value ram1) ram2)
                  (and (equal (loghead (* 16 (ifix numwords)) value) (read-data-words numwords denvr offset ram2))
                       (equal (clear-data-words numwords denvr offset ram1)
                              (clear-data-words numwords denvr offset ram2)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (WRITE-DATA-WORD READ-DATA-WORD
                                                   WORD-AD-TO-BYTE-ADS
                                                   ACL2::EQUAL-LOGAPP-X-Y-Z
                                                   WR==R!
                                                   CLEAR-DATA-WORDS
                                                   READ-DATA-WORDS
                                                   WRITE-DATA-WORDS
                                                   LOGHEAD-LIST-OF-LOGAPP-LIST
                                                   )
                                  (LOGAPP-LIST-OF-LOGHEAD
                                   UNIQUE-OF-WORD-ADS-TO-BYTE-ADS-better)))))

(defthm write-data-words-of-write-data-word-diff-denvrs
  (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
           (equal (write-data-words numwords denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-words numwords denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
  :hints (("Goal" :in-theory (e/d (write-data-words
                                     write-data-word
                                     acl2::logext-logapp
                                     LOGHEAD-LIST-OF-LOGAPP-LIST
                                     )
                                  (LOGAPP-LIST-OF-LOGHEAD)))))

;(local (in-theory (disable LOGAPP-LIST-OF-LOGHEAD)))
(local (in-theory (enable LOGHEAD-LIST-OF-LOGAPP-LIST)))

(encapsulate
 ()
 (local (defthm write-data-words-of-write-data-word-diff-same-denv
          (implies (and (syntaxp (smaller-params denvr offset2 denvr offset1))
                        (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))))
                   (equal (write-data-words numwords denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                          (write-data-word denvr offset2 val2 (write-data-words numwords denvr offset1 val1 ram))))
          :rule-classes ((:rewrite :loop-stopper nil))
          :hints (("Goal" :in-theory (enable write-data-words
                                             write-data-word
                                             acl2::logext-logapp
                                             )))))

 (defthm write-data-words-of-write-data-word-diff
   (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                 (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))))
            (equal (write-data-words numwords denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                   (write-data-word denvr2 offset2 val2 (write-data-words numwords denvr1 offset1 val1 ram))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :cases ((not (equal (loghead 15 denvr1) (loghead 15 denvr2))))))))

(defthm clear-data-words-of-write-data-word
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords)))
           (equal (clear-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
                  (write-data-word denvr2 offset2 value (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm clear-data-words-of-write-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (clear-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 value ram))
                  (write-data-words numwords2 denvr2 offset2 value (clear-data-words numwords1 denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (enable clear-data-words write-data-words))))




(encapsulate
 ()

 (local (defthm helper
          (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
                   (equal (read-data-word denvr offset1 (write-data-words numwords denvr offset2 value ram))
                          (read-data-word denvr offset1 ram)))
          :hints (("Goal" :in-theory (enable read-data-word write-data-words
                                             acl2::logext-logapp)))))

 (defthm read-data-word-of-clear-data-words-diff
   (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
            (equal (read-data-word denvr1 offset1 (clear-data-words numwords denvr2 offset2 ram))
                   (read-data-word denvr1 offset1 ram)))
   :hints (("Goal"  :in-theory (enable clear-data-words ;bzo
                                       read-data-word-of-write-data-words-diff-better)
            :cases ((not (equal (loghead 15 denvr1) (loghead 15 denvr2))))))))

;bzo really necessary?
(theory-invariant (incompatible (:definition clear-data-word ) (:rewrite WRITE-DATA-WORD-EQUAL-REWRITE)))

(defthm clear-data-word-of-write-data-words-diff-denvrs
  (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
           (equal (CLEAR-DATA-WORD denvr1 offset1 (WRITE-DATA-WORDS numwords denvr2 offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr2 offset2 value (CLEAR-DATA-WORD denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (
                                   clear-data-word
                                   acl2::logext-logapp)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-write-data-words-diff-offsets
  (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
           (equal (clear-data-word denvr1 offset1 (write-data-words numwords denvr2 offset2 value ram))
                  (write-data-words numwords denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (
                                   clear-data-word
                                   acl2::logext-logapp)
                                  (write-data-word-equal-rewrite)))))










;gen!
(defthm loghead-16-of-read-data-words
  (equal (loghead 16 (read-data-words numwords denvr offset ram))
         (if (zp numwords)
             0
           (read-data-word denvr offset ram)))
  :hints (("Goal" :in-theory (enable read-data-words read-data-word acl2::logext-logapp))))

;move
;gen!
(defthm logtail-16-of-read-data-words
  (equal (logtail 16 (read-data-words numwords denvr offset ram))
         (read-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS)
                           (OFFSET-RANGE-WRAP 16 0 NUMWORDS))
           :in-theory (enable read-data-words))))




;drop?
(defthm clear-data-word-of-write-data-words-special-case
  (implies (and (equal (loghead 16 offset1) (loghead 16 (+ -1 numwords offset2)))
                (equal numwords 2) ;bbzo get rid of this and remove -special case from the theorem name
                (integerp offset2)
                (<= numwords 65536))
           (equal (clear-data-word denvr offset1 (write-data-words numwords denvr offset2 value ram))
                  (write-data-words (+ -1 numwords) denvr offset2 value (clear-data-word denvr offset1 ram))))
  :hints (("Goal" :in-theory (e/d (;offset-range-wrap-const-opener
;                                  clear-data-word write-data-word
;write-data-words
                                   write-data-words-opener
                                   )
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                   write-data-word-equal-rewrite)))))

(defthm clear-data-words-of-write-data-words-same
  (equal (clear-data-words numwords denvr offset (write-data-words numwords denvr offset value ram))
         (clear-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;bzo
(defthm write-data-words-of-what-was-already-there
  (implies (equal val (read-data-words numwords denvr offset ram))
           (equal (write-data-words numwords denvr offset val ram)
                  ram))
  :hints (("Goal" :cases ((and (integerp numwords)
                               (<= 0 numwords)))
           :in-theory (enable write-data-words read-data-words))))

;bzo
(defthm write-data-words-of-what-was-already-there-cheap
  (equal (write-data-words numwords denvr offset (read-data-words numwords denvr offset ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable write-data-words read-data-words))))

(defthm clear-data-word-of-write-data-words-special-case-2
  (implies (and (equal numwords 2) ;bbzo get rid of this and remove -special case from the theorem name
;                (integerp offset)
                (<= numwords 65536))
           (equal (clear-data-word denvr offset (write-data-words numwords denvr offset value ram))
                  (write-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) (logtail 16 value) (clear-data-word denvr offset ram))))
  :hints (("Goal" :in-theory (e/d (;offset-range-wrap-const-opener
;                                  clear-data-word write-data-word
;write-data-words
                                   write-data-words-opener
                                   )
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                   write-data-word-equal-rewrite)))))

(defthm read-data-words-sum-loghead-hack
  (equal (read-data-words numwords denvr (+ i (loghead 16 j)) ram)
         (read-data-words numwords denvr (+ i (ifix j)) ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm write-data-words-of-loghead-hack
  (equal (write-data-words 2 denvr offset (loghead 32 val) ram)
         (write-data-words 2 denvr offset val ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

;bzo gen!
(defthm write-data-words2-of-logext
  (equal (write-data-words 2 denvr offset (logext 32 x) ram)
         (write-data-words 2 denvr offset x ram))
  :hints (("Goal" :in-theory (enable write-data-words))))


;bzo allow denvrs to differ
(defthm read-data-words-of-clear-data-word-diff
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (clear-data-word denvr offset2 ram))
                  (read-data-words size denvr offset1 ram)))
  :hints (("Goal" :cases ((EQUAL (LOGHEAD '16 OFFSET2) (LOGHEAD '16 OFFSET1)))
           :in-theory (e/d (clear-data-word)
                           (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm read-data-words-of-clear-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (read-data-words numwords1 denvr1 offset1 (clear-data-words numwords2 denvr2 offset2 ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-words)
                                  ()))))

(defthm clear-data-words-of-write-data-word-cover
   (implies (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
            (equal (clear-data-words numwords denvr offset1 (write-data-word denvr offset2 value ram))
                   (clear-data-words numwords denvr offset1 ram)))
   :hints (("Goal" :in-theory (enable clear-data-words))))



(defthm clear-data-words-of-sum-of-loghead
  (equal (clear-data-words numwords denvr (+ i (loghead 16 j)) ram)
         (clear-data-words numwords denvr (+ i (ifix j)) ram))
  :hints (("Goal" :in-theory (enable clear-data-words
                                     ))))


(defthm CLEAR-DATA-WORDS-of-WRITE-DATA-WORDS-partial-overlap-2
  (implies (and (equal (loghead 16 offset1) (loghead 16 (+ 1 (ifix offset2))))
                (integerp offset2)
                (integerp offset1))
           (equal (CLEAR-DATA-WORDS 2 denvr offset2 (WRITE-DATA-WORDS 2 denvr offset1 value ram))
                  (WRITE-DATA-WORD denvr (+ 1 offset1) (logtail 16 value) (CLEAR-DATA-WORDS 2 denvr offset2 ram))))
  :hints (("Goal" :in-theory (e/d (CLEAR-DATA-WORDS
;DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   READ-DATA-WORDS-OPENER
                                   WRITE-DATA-WORDS-OPENER

                                   )
                                  (;READ-DATA-WORDS-RECOLLAPSE
                                   acl2::LOGHEAD-SUM-SUBST-ALT ;bzo looped
                                   WRITE-DATA-WORDS-EQUAL-REWRITE ;bzo loops!
                                   )))))




;; (defthm
;; (WRITE-DATA-WORD DENVR2 OFFSET1 VALUE
;;                               (WRITE-DATA-WORD DENVR1 OFFSET1 VALUE RAM))


;; (thm
;;  (equal (CLEAR-DATA-WORD DENVR1 OFFSET1 (WRITE-DATA-WORD DENVR2 OFFSET1 VALUE RAM))

;; (defthm write-data-word-of-write-data-word-same-value
;;   (equal (write-data-word denvr1 offset1 value (write-data-word denvr2 offset2 value ram))
;;          (write-data-word denvr2 offset2 value (write-data-word denvr1 offset1 value ram)))
;;   :hints (("Goal" :cases ((equal (loghead 16 offset1) (loghead 16 offset2))))))

;; (defthmd clear-data-words-constant-opener2
;;   (equal (clear-data-words 2 denvr offset ram1)
;;          (clear-data-word denvr offset (clear-data-word denvr (+ 1 (ifix offset)) ram1))
;;          )
;;   :hints (("Goal" :in-theory (e/d (clear-data-words
;;                                    WRITE-DATA-WORDS-OPENER)
;;                                   (WRITE-DATA-WORDS-EQUAL-REWRITE ;bzo
;;                                    )))))




;(in-theory (disable READ-DATA-WORDS-OPENER))

(defthm read-data-words-of-write-data-word-hack
  (implies (integerp offset)
           (equal (read-data-words 2 denvr (+ -1 offset) (write-data-word denvr offset value ram))
                  (logapp 16
                          (read-data-word denvr (+ -1 offset) ram)
                          (loghead 16 value))))
  :hints (("Goal" :in-theory (enable read-data-words-opener))))


;this loops with the splitting up rules?
;move
(defthmd read-data-words-recollapse
  (implies (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
           (equal (logapp 16
                          (read-data-word denvr offset1 ram)
                          (read-data-word denvr offset2 ram))
                  (read-data-words 2 denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (read-data-words-opener)
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))))

(theory-invariant (incompatible (:rewrite READ-DATA-WORDS-RECOLLAPSE) (:definition READ-DATA-WORDS)))
(theory-invariant (incompatible (:rewrite READ-DATA-WORDS-RECOLLAPSE) (:rewrite READ-DATA-WORDS-OPENER)))


(defthm write-data-words-of-write-data-words-diff-new
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                               (offset-range-wrap 16 offset2 numwords2)))
           (equal (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(in-theory (disable write-data-words-of-write-data-words-diff))







;more like this?
;bzo bad name?
(defthm clear-data-words-of-write-data-words-partial-overlap-1
  (implies (and (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
                (integerp offset2)
                (integerp offset1))
           (equal (clear-data-words 2 denvr offset2 (write-data-words 2 denvr offset1 value ram))
                  (write-data-word denvr offset1 value (clear-data-words 2 denvr offset2 ram))))
  :hints (("Goal" :in-theory (e/d (clear-data-words
;disjoint-of-two-offset-range-wraps
                                   read-data-words-opener
                                   write-data-words-opener
                                   )
                                  (read-data-words-recollapse
                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant
                                   write-data-words-equal-rewrite ;bzo loops!
                                   )))))



;;
;; These use the bag phrasing...
;;











;move this up?
(defthm read-data-words-of-write-data-word-diff-denvrs
  (implies (not (equal (loghead 15 denvr1)
                       (loghead 15 denvr2)))
           (equal (read-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
                  (read-data-words numwords denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable write-data-word
                                     word-ad-to-byte-ads
                                     read-data-words
                                     acl2::logext-logapp))))


(defthm read-data-words-of-write-data-word-diff-better
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-words size denvr offset1 ram)))
  :otf-flg t
  :hints (("Goal" :cases ((equal (loghead 15 denvr) (loghead 15 denvr2)))))
  )

(in-theory (disable READ-DATA-WORDS-OF-WRITE-DATA-WORD-DIFF))

(DEFTHM READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT-addend
  (IMPLIES (AND (SYNTAXP (QUOTEP K))
                (NOT (UNSIGNED-BYTE-P 16 K))
                (integerp x)
                (integerp k)
                )
           (EQUAL (READ-DATA-WORD DENVR (+ K x) RAM)
                  (READ-DATA-WORD DENVR (+ (LOGHEAD 16 K) x)
                                  RAM)))
  :HINTS
  (("Goal"
    :IN-THEORY (DISABLE READ-DATA-WORD-OF-LOGHEAD16-2
                        )
    :USE ((:INSTANCE READ-DATA-WORD-OF-LOGHEAD16-2
                     (OFFSET (+ x (LOGHEAD 16 K))))
          (:INSTANCE READ-DATA-WORD-OF-LOGHEAD16-2
                     (OFFSET (+ x K)))))))

;bzo make a -better version?
(defthm clear-data-words-of-write-data-words-cover
  (implies (bag::subbagp (offset-range-wrap 16 offset2 numwords2)
                         (offset-range-wrap 16 offset1 numwords1))
           (equal (clear-data-words
                   numwords1
                   denvr offset1
                   (write-data-words
                    numwords2 denvr
                    offset2 val2 ram))
                  (clear-data-words
                   numwords1 denvr
                   offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words
                                     write-data-words-of-write-data-words-cover
                                     ))))



(defthm clear-data-words-of-clear-data-word-cover
  (implies (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
           (equal (clear-data-words numwords denvr offset1 (clear-data-word denvr offset2 ram))
                  (clear-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-words
                                     clear-data-word)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-words-of-clear-data-word-cover-hack
  (implies (and (< (loghead 16 offset2) numwords)
                (integerp numwords))
           (equal (clear-data-words numwords denvr 0 (clear-data-word denvr offset2 ram))
                  (clear-data-words numwords denvr 0 ram)))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range
                                     acl2::loghead-sum-split-into-2-cases
                                     acl2::loghead-of-minus))))






;prove from the multi-word version?
(defthm write-data-words-of-write-data-word-cover-better
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                  (write-data-words numwords denvr offset1 val1 ram)))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range))))

;what about the non-better lemma?
(defthm clear-data-words-of-write-data-word-cover-better
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr offset1 (write-data-word denvr offset2 value ram))
                  (clear-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;every theorem about clear-data-words should be proved easily from an analogous theorem about write-data-words!
;make sure analogues exist for each theorem about either function.
;likewise for the single-word ops

(defthm write-data-words-of-write-data-word-diff-better
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-words numwords denvr1 offset1 val1 ram))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :in-theory (e/d (memberp-of-offset-range)
                                  (write-data-word-equal-rewrite
                                   write-data-words-equal-rewrite)))))

;three "clear" variations of write-data-words-of-write-data-word-diff
(defthm clear-data-words-of-write-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 val ram))
                  (write-data-word denvr2 offset2 val (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 val) (val1 0))
           :in-theory (e/d (clear-data-words) (write-data-words-of-write-data-word-diff
                                                     write-data-word-equal-rewrite
                                                     write-data-words-equal-rewrite)))))

(defthm clear-data-words-of-clear-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 0) (val1 0))
           :in-theory (e/d (clear-data-words
                            clear-data-word)
                           (write-data-words-of-write-data-word-diff
                            write-data-word-equal-rewrite
                            write-data-words-equal-rewrite)))))

;Disabled because it goes against our convention of pushing clears inside of writes.
(defthmd write-data-words-of-clear-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr1 offset1 val (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (write-data-words numwords denvr1 offset1 val ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 0) (val1 val))
           :in-theory (e/d (clear-data-word) (write-data-words-of-write-data-word-diff
                                                    write-data-word-equal-rewrite
                                                    write-data-words-equal-rewrite)))))



(defthm read-data-word-of-clear-data-words-diff-better-better
  (implies(and (<= numwords (loghead 16 (- offset1 offset2)))
               (integerp offset1)
               (integerp offset2)
               (integerp numwords)
               )
          (equal (read-data-word denvr offset1 (clear-data-words numwords denvr2 offset2 ram))
                 (read-data-word denvr offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm write-data-words-of-write-data-words-cover-better
  (implies (and (<= (+ numwords2 (loghead 16 (+ offset2 (- offset1)))) numwords1)
                (<= numwords2 (expt 2 16)) ;bzo can probably drop stuff like this?
                (integerp numwords1)
                (integerp numwords2)
                (integerp offset1)
                (integerp offset2))
           (equal (write-data-words numwords1 denvr offset1 val1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (write-data-words numwords1 denvr offset1 val1 ram)))
  :hints (("Goal" :cases ((<= 0 numwords2))
           :in-theory (enable write-data-words-of-write-data-words-cover))))

;analogue with clear of clear?
(defthm clear-data-words-of-write-data-words-cover-better
  (implies (and (<= (+ numwords2 (loghead 16 (+ offset2 (- offset1)))) numwords1)
                (<= numwords2 (expt 2 16))
                (integerp numwords1)
                (integerp numwords2)
                (integerp offset1)
                (integerp offset2))
           (equal (clear-data-words numwords1 denvr offset1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (clear-data-words numwords1 denvr offset1 ram)))
  :hints (("Goal" :cases ((<= 0 numwords2))
           :in-theory (enable write-data-words-of-write-data-words-cover))))


(defthm write-data-words-of-write-data-words-diff-new-better
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                     (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
                )
           (equal (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm clear-data-words-of-write-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (clear-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (write-data-words numwords2 denvr2 offset2 val (clear-data-words numwords1 denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (disable write-data-words-equal-rewrite)))) ;why the disable?

;clear-data-words of clear-data-words doesn't need any same or diff hyps since writing same values.
;same for single word and single/multi word cases.

;prove the single word lemmas from the multi-word lemmas?
;kill READ-DATA-WORDS-OF-WRITE-DATA-WORDS?
(defthm read-data-words-of-write-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (read-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (read-data-words numwords1 denvr1 offset1 ram))))

(defthm read-data-words-of-clear-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (read-data-words numwords1 denvr1 offset1 (clear-data-words numwords2 denvr2 offset2 ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm read-data-words-of-write-data-word-diff-better-better
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (read-data-words numwords denvr offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (memberp-of-offset-range)
                                  ())))  )

(defthm read-data-words-of-clear-data-word-diff-better-better
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (read-data-words numwords denvr offset1 (clear-data-word denvr2 offset2 ram))
                  (read-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))






(defthmd clear-data-words-opener
  (implies (and (syntaxp (quotep numwords))
                (<= numwords 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                (not (zp numwords)))
           (equal (clear-data-words numwords denvr offset ram)
                  (clear-data-word denvr offset (clear-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))))
  :hints (("Goal" :use (:instance  write-data-words-opener (value 0))
           :in-theory (e/d (clear-data-words clear-data-word)
                                  (write-data-word-equal-rewrite  write-data-words-opener)))))



(defthm read-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                )
           (equal (read-data-words numwords denvr k ram)
                  (read-data-words numwords denvr (acl2::loghead 16 k) ram)))
  :hints (("Goal" :in-theory (disable READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET)
           :use ((:instance READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET (offset (acl2::loghead 16 k)))
                 (:instance READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET (offset k))))))

(defthm read-data-words-of-sum-normalize-constant-addend
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp x)
                (integerp k)
                )
           (equal (read-data-words numwords denvr (+ k x) ram)
                  (read-data-words numwords denvr (+ (loghead 16 k) x)
                                  ram)))
  :hints (("Goal" :in-theory (disable read-data-words-of-loghead-around-offset)
           :use ((:instance read-data-words-of-loghead-around-offset (offset (+ x (loghead 16 k))))
                 (:instance read-data-words-of-loghead-around-offset (offset (+ x k)))))))


;oo





;;
;;
;; MAKE-CODE-ADDR
;;
;;

;; Create a byte-address by concatenating a 16-bit code environment, CENVR,
;; onto a 16 bit offset, OFFSET.  CENVR forms the more signficiant
;; bits of the result.  See "Section 2.1 MEMORY ADDRESSING" in the AAMP
;; manual.
;;
;; Note that after logapp computes a 32-bit unsigned result, we sign-extend
;; that result to a signed 32-bit number.  This is because addresses in the
;; AAMP RAM are signed numbers (though perhaps we'll change that fact
;; later?). -ews
;;
;; bzo add a guard and give this a fast body?
(defund make-code-addr (cenvr offset)
  (declare (type integer cenvr offset))
;;  (logext 32 (logapp 16 offset cenvr))
    (loghead 32 (logapp 16 offset cenvr))
    )

;; (defthm signed-byte-p-of-make-code-addr
;;   (signed-byte-p 32 (make-code-addr env offset))
;;   :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm unsigned-byte-p-of-make-code-addr
  (unsigned-byte-p 32 (make-code-addr env offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm make-code-addr-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr cenvr 0)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm make-code-addr-when-cenvr-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr 0 offset)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;generalize the 16?
(defthm make-code-addr-of-loghead-1
  (equal (make-code-addr (loghead 16 cenvr) offset)
         (make-code-addr cenvr offset))
  :hints (("Goal" :in-theory (enable make-code-addr acl2::logext-logapp))))

;generalize the 16?
(defthm make-code-addr-of-loghead-2
  (equal (make-code-addr cenvr (loghead 16 offset))
         (make-code-addr cenvr offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))


;linear rule for makeaddr?

(defthm make-code-addr-of-logext-gen
  (implies (and (integerp n)
                (<= 16 n))
           (equal (make-code-addr cenvr (logext n offset))
                  (make-code-addr cenvr offset)))
  :hints (("Goal" :use ((:instance make-code-addr-of-loghead-2)
                        (:instance make-code-addr-of-loghead-2 (offset (logext n offset))))
           :in-theory (disable make-code-addr-of-loghead-2))))

(defthm make-code-addr-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (unsigned-byte-p 16 a))
                (integerp a)
                (integerp b)
                )
           (equal (make-code-addr cenvr (+ a b))
                  (make-code-addr cenvr (+ (loghead 16 a) b))))
  :hints (("Goal" :use ((:instance make-code-addr-of-loghead-2 (offset (+ a b)))
                        (:instance make-code-addr-of-loghead-2 (offset (+ (loghead 16 a) b)))
                        )
           :in-theory (disable make-code-addr-of-loghead-2))))

;;;;;

;do we want this?
;this may have looped...
(defthm make-code-addr-of-+-loghead
  (implies (and (integerp y1)
                (integerp y2))
           (equal (make-code-addr x (+ y1 (loghead 16 y2)))
                  (make-code-addr x (loghead 16 (+ y1 y2))) ;further simplify this?
                  ))
  :hints (("Goal" :in-theory (enable make-code-addr logapp))))

;bzo
;weird.  do we still need this?
(defthm make-code-addr-of-make-code-addr
  (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
           (equal (make-code-addr x (make-code-addr x2 y))
                  (make-code-addr x y)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;weird.  do we still need this?
(defthm make-code-addr-plus-hack
  (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
           (equal (make-code-addr x (+ k (make-code-addr x2 y)))
                  (make-code-addr x (+ k y))))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm make-code-addr-cong16
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-code-addr cenvr offset1)
                  (make-code-addr cenvr offset2)))
  :hints (("Goal" :in-theory (enable make-code-addr
                                     logapp ;bzo
                                     ))))

(defthm make-code-addr-cong16-lemma
  (implies (and (equal (loghead 16 offset1)
                       offset2)
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-code-addr cenvr offset1)
                  (make-code-addr cenvr offset2)))
  :hints (("Goal" :in-theory (enable make-code-addr
                                     logapp ;bzo
                                     ))))

;kill the other
(defthm make-code-addr-of-+-loghead-better
  (implies (and (integerp y1) (integerp y2))
           (equal (make-code-addr x (+ y1 (loghead 16 y2)))
                  (make-code-addr x (+ y1 y2))))
  :hints
  (("Goal" :in-theory (enable make-code-addr logapp))))

(defthm make-code-addr-subst-in-for-offset
  (implies (and (equal (loghead 16 y) z)
                (syntaxp (acl2::smaller-term z y))
                (integerp x)
                (integerp y)
                )
           (equal (MAKE-CODE-ADDR cenvr (+ x y))
                  (MAKE-CODE-ADDR cenvr (+ x z)))))

;bzo even if we prove this by closing things up, opening things may reveal good lemmas
(defthmd plus-make-code-addr
  (implies (and (unsigned-byte-p 16 (+ x pc))
                (unsigned-byte-p 16 pc)
                (unsigned-byte-p 16 ccenvr))
           (equal (+ x (make-code-addr ccenvr pc))
                  (make-code-addr ccenvr (+ x pc))))
  :hints (("Goal" :cases ((acl2-numberp x)) ;why suddenly needed?
           :in-theory (e/d (make-code-addr
                            acl2::logext-logapp
;         ACL2::LOGAPP-0-PART-2-BETTER
                            acl2::ASH-AS-LOGAPP ;think about this
                            )
                           (ACL2::LOGAPP-0-PART-2-BETTER)))))

;enable?
(defthmd ash-plus-make-code-addr2
  (implies (and (unsigned-byte-p 16 base)
                (unsigned-byte-p 16 offset)
                (integerp k)
                (unsigned-byte-p 16 (+ k offset)))
           (equal (+ (* 2 k) (ash (make-code-addr base offset) 1))
                  (ash (make-code-addr base (+ k offset)) 1)))
  :hints (("Goal" :use (:instance acl2::ash-plus-addr2 (acl2::k k) (acl2::addr (make-code-addr base offset)))
           :in-theory (enable plus-make-code-addr))))

;;;;xx
(encapsulate
 ()
 (local (defthm bk
          (implies (and (equal (loghead 16 x) (loghead 16 offset))
                        (unsigned-byte-p 32 x) ;;(signed-byte-p 32 x)
                        (equal (logtail 16 x) (loghead 16 cenvr) ;(logext 16 cenvr)
                               ))
                   (EQUAL x (MAKE-CODE-ADDR CENVR OFFSET)))
          :rule-classes nil
          :hints (("Goal" :in-theory (enable make-code-addr ifix ACL2::LOGEXT-LOGAPP)))))

 (local (defthm fw
          (implies (EQUAL x (MAKE-CODE-ADDR CENVR OFFSET))
                   (and (equal (loghead 16 x) (loghead 16 offset))
                        (unsigned-byte-p 32 x) ;(signed-byte-p 32 x)
                        (equal (logtail 16 x) (loghead 16 cenvr) ;(logext 16 cenvr)
                               )))
          :rule-classes nil
          :hints (("Goal" :in-theory (enable make-code-addr ifix ACL2::LOGEXT-LOGAPP)))))

;do we want this on?
 (defthmd make-code-addr-equal-rewrite
   (equal (equal x (make-code-addr cenvr offset))
          (and (equal (loghead 16 x) (loghead 16 offset))
               (unsigned-byte-p 32 x) ;(signed-byte-p 32 x)
               (equal (logtail 16 x) (loghead 16 cenvr) ;(logext 16 cenvr)
                      )))
   :hints (("Goal" :use (fw bk)))))

(defthm logtail-16-of-make-code-addr
  (equal (logtail 16 (make-code-addr x y))
         (loghead 16 x) ;;(logext 16 x)
         )
  :hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                   make-code-addr)
                                  (
                                   acl2::logtail-logapp)))))

(defthm loghead-16-of-make-code-addr
  (equal (loghead 16 (make-code-addr x y))
         (loghead 16 y))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm equal-of-two-make-code-addrs-rewrite
  (equal (equal (make-code-addr cenvr2 offset2)
                (make-code-addr cenvr1 offset1))
         (and (equal (loghead 16 cenvr1) ;we could also talk about logexts here?
                     (loghead 16 cenvr2))
              (equal (loghead 16 offset1)
                     (loghead 16 offset2))))
  :hints (("Goal" :in-theory (enable make-code-addr-equal-rewrite))))

(defthm logtail-of-make-code-addr-hack
  (equal (logtail 17 (make-code-addr ccenvr offset1))
         ;;(logext 15 (acl2::logcdr ccenvr))
         (loghead 15 (acl2::logcdr ccenvr))
         )
  :hints (("Goal" :in-theory (enable make-code-addr ACL2::LOGEXT-LOGAPP))))

(defthm logtail15-of-make-code-addr
  (equal (logtail 15 (make-code-addr cenvr offset))
         ;; (logapp 1 (acl2::logbit 15 offset) (logext 16 cenvr))
         (logapp 1 (acl2::logbit 15 offset) (loghead 16 cenvr))
         )
  :hints (("Goal" :in-theory (e/d (make-code-addr ifix ACL2::LOGEXT-LOGAPP)
                                  (acl2::logext-logtail)))))

;; (defthm <-of-make-code-addr
;;   (implies (and (integerp x)
;;                 (integerp offset) ;drop?
;;                 )
;;            (equal (< (make-code-addr cenvr offset) x)
;;                   (if (logbitp 15 cenvr)
;;                       (or (< -1 (logtail 31 x))
;;                           (and (equal -1 (logtail 31 x))
;;                                (< (logapp 16 offset (loghead 15 cenvr))
;;                                   (loghead 31 x))))
;;                     (< (loghead 31 (logapp 16 offset cenvr)) x))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (make-code-addr logext acl2::logtail-loghead-better
;;                                             )
;;                                   (;equal-of-if
;;                                    acl2::loghead-logtail
;;                                    acl2::logext-logapp ;why?
;;                                    )))))

(defthm <-of-make-code-addr
  (implies (and (integerp x)
                (integerp offset) ;drop?
                )
           (equal (< (make-code-addr cenvr offset) x)
                  (< (loghead 32 (logapp 16 offset cenvr)) x)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (make-code-addr logext acl2::logtail-loghead-better
                                            )
                                  (;equal-of-if
                                   acl2::loghead-logtail
                                   acl2::logext-logapp ;why?
                                   )))))


(defthm make-code-addr-chop-second-arg-when-constant
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr cenvr (loghead 16 offset)))))

(defthm loghead-15-make-code-addr
  (implies (and (integerp y)
                (integerp x))
           (equal (loghead 15 (make-code-addr x y))
                  (loghead 15 y)))
  :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm make-code-addr-plus-mult-16
  (implies  (and (syntaxp (not (quotep offset))) ;prevents loops
                 (integerp offset)
                 (integerp cenvr))
            (equal (MAKE-CODE-ADDR cenvr (+ 65536 offset))
                   (MAKE-CODE-ADDR cenvr offset)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(in-theory (disable MAKE-code-ADDR-OF-+-LOGHEAD)) ;looped!

(defthm make-code-addr-equal-same-env-rewrite
  (implies (and (integerp cenvr)
                (integerp offset1)
                (integerp offset2))
           (equal (EQUAL (MAKE-CODE-ADDR CENVR OFFSET2)
                         (MAKE-CODE-ADDR CENVR OFFSET1))
                  (EQUAL (LOGHEAD 16 OFFSET1)
                         (LOGHEAD 16 OFFSET2))))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm logcar-of-make-code-addr
  (equal (acl2::logcar (make-code-addr cenvr offset))
         (acl2::logcar offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;; (defthm signed-byte-p-of-make-code-addr-fw
;;   (signed-byte-p 32 (make-code-addr cenvr offset))
;;   :rule-classes ((:forward-chaining :trigger-terms ((make-code-addr cenvr offset)))))

(defthm unsigned-byte-p-of-make-code-addr-fw
  (unsigned-byte-p 32 (make-code-addr cenvr offset))
  :rule-classes ((:forward-chaining :trigger-terms ((make-code-addr cenvr offset)))))

;; (defthm signed-byte-p-of-make-code-addr-better
;;   (implies (and (integerp n)
;;                 (<= 32 n))
;;            (signed-byte-p n (make-code-addr cenvr offset)))
;;   :hints (("Goal" :use (:instance signed-byte-p-of-make-code-addr)
;;            :in-theory (disable signed-byte-p-of-make-code-addr))))

(defthm unsigned-byte-p-of-make-code-addr-better
  (implies (and (integerp n)
                (<= 32 n))
           (unsigned-byte-p n (make-code-addr cenvr offset)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-make-code-addr)
           :in-theory (disable unsigned-byte-p-of-make-code-addr))))

;can this (or the other one?) loop?
(defthm make-code-addr-cong16-cenvr
  (implies (and (equal (loghead 16 env1)
                       (loghead 16 env2))
                (syntaxp (acl2::smaller-term env2 env1)))
           (equal (make-code-addr env1 offset)
                  (make-code-addr env2 offset)))
  :hints (("Goal" :use ((:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV1)))
                        (:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV2))))
           :in-theory (e/d (make-code-addr logapp) (ACL2::LOGEXT-LOGHEAD)))))



;;
;;
;; MAKE-DATA-ADDR
;;
;;

;; Create a byte-address by concatenating a 15-bit data environment, DENVR,
;; onto a 16 bit offset, OFFSET, and then shifting the result one bit to the
;; left.  DENVR forms the most signficiant bits of the result.  See "Section
;; 2.1 MEMORY ADDRESSING" in the AAMP manual.
;;
;; Note that after logapp computes a 32-bit unsigned result, we sign-extend
;; that result to a signed 32-bit number.  This is because addresses in the
;; AAMP RAM are signed numbers (though perhaps we'll change that fact
;; later?). -ews
;;
;; we expect denvr to be a 15-bit value...
;; bzo add a guard and give this a fast body?
;;
;bzo could move the logext in?
(defund make-data-addr (denvr offset)
  (declare (type integer denvr offset))
  ;;(logext 32 (ash (logapp 16 offset denvr) 1))
  (loghead 32 (ash (logapp 16 offset denvr) 1))
  )

;; (defthm signed-byte-p-of-make-data-addr
;;   (signed-byte-p 32 (make-data-addr denvr offset))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm unsigned-byte-p-of-make-data-addr
  (unsigned-byte-p 32 (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (make-data-addr denvr offset)
                  (make-data-addr denvr 0)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-when-denvr-is-not-an-integerp
  (implies (not (integerp denvr))
           (equal (make-data-addr denvr offset)
                  (make-data-addr 0 offset)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;generalize the 16?
(defthm make-data-addr-of-loghead-1
  (equal (make-data-addr (loghead 15 denvr) offset)
         (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr acl2::logext-logapp))))

;generalize the 16?
(defthm make-data-addr-of-loghead-2
  (equal (make-data-addr denvr (loghead 16 offset))
         (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))




;do we want this?
;this may have looped...
(defthm make-data-addr-of-+-loghead
  (implies (and (integerp y1)
                (integerp y2))
           (equal (make-data-addr x (+ y1 (loghead 16 y2)))
                  (make-data-addr x (loghead 16 (+ y1 y2))) ;further simplify this?
                  ))
  :hints (("Goal" :in-theory (enable make-data-addr logapp))))

;bzo
;weird.  do we still need this?
;; (defthm make-data-addr-of-make-data-addr
;;   (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
;;            (equal (make-data-addr x (make-data-addr x2 y))
;;                   (make-data-addr x y)))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

;weird.  do we still need this?
;; (defthm make-data-addr-plus-hack
;;   (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
;;            (equal (make-data-addr x (+ k (make-data-addr x2 y)))
;;                   (make-data-addr x (+ k y))))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-cong16
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-data-addr denvr offset1)
                  (make-data-addr denvr offset2)))
  :hints (("Goal" :in-theory (enable make-data-addr
                                     logapp ;bzo
                                     ))))

(defthm make-data-addr-cong16-lemma
  (implies (and (equal (loghead 16 offset1)
                       offset2)
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-data-addr denvr offset1)
                  (make-data-addr denvr offset2)))
  :hints (("Goal" :in-theory (enable make-data-addr
                                     logapp ;bzo
                                     ))))

;kill the other
(defthm make-data-addr-of-+-loghead-better
  (implies (and (integerp y1) (integerp y2))
           (equal (make-data-addr x (+ y1 (loghead 16 y2)))
                  (make-data-addr x (+ y1 y2))))
  :hints
  (("Goal" :in-theory (enable make-data-addr logapp))))

(defthm make-data-addr-subst-in-for-offset
  (implies (and (equal (loghead 16 y) z)
                (syntaxp (acl2::smaller-term z y))
                (integerp x)
                (integerp y)
                )
           (equal (MAKE-DATA-ADDR denvr (+ x y))
                  (MAKE-DATA-ADDR denvr (+ x z)))))

;bzo even if we prove this by closing things up, opening things may reveal good lemmas
;; (defthmd plus-make-data-addr
;;   (implies (and (unsigned-byte-p 16 (+ x pc))
;;                 (unsigned-byte-p 16 pc)
;;                 (unsigned-byte-p 16 cdenvr))
;;            (equal (+ x (make-data-addr cdenvr pc))
;;                   (make-data-addr cdenvr (+ x pc))))
;;   :hints (("Goal" :cases ((acl2-numberp x)) ;why suddenly needed?
;;            :in-theory (e/d (make-data-addr add32 lshl32 lshu
;;                                    ;         ACL2::LOGAPP-0-PART-2-BETTER
;;                                             acl2::ASH-AS-LOGAPP ;think about this
;;                                             )
;;                                   (ACL2::LOGAPP-0-PART-2-BETTER)))))

;enable?
;; (defthmd ash-plus-make-data-addr2
;;   (implies (and (unsigned-byte-p 16 base)
;;                 (unsigned-byte-p 16 offset)
;;                 (integerp k)
;;                 (unsigned-byte-p 16 (+ k offset)))
;;            (equal (+ (* 2 k) (ash (make-data-addr base offset) 1))
;;                   (ash (make-data-addr base (+ k offset)) 1)))
;;   :hints (("Goal" :use (:instance acl2::ash-plus-addr2 (acl2::k k) (acl2::addr (make-data-addr base offset)))
;;            :in-theory (enable plus-make-data-addr))))

(defthm make-data-addr-of-logext-gen
  (implies (and (integerp n)
                (<= 16 n))
           (equal (make-data-addr denvr (logext n offset))
                  (make-data-addr denvr offset)))
  :hints (("Goal" :use ((:instance make-data-addr-of-loghead-2)
                        (:instance make-data-addr-of-loghead-2 (offset (logext n offset))))
           :in-theory (disable make-data-addr-of-loghead-2))))

(defthm make-data-addr-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (unsigned-byte-p 16 a))
                (integerp a)
                (integerp b)
                )
           (equal (make-data-addr denvr (+ a b))
                  (make-data-addr denvr (+ (loghead 16 a) b))))
  :hints (("Goal" :use ((:instance make-data-addr-of-loghead-2 (offset (+ a b)))
                        (:instance make-data-addr-of-loghead-2 (offset (+ (loghead 16 a) b)))
                        )
           :in-theory (disable make-data-addr-of-loghead-2))))

(defthm make-data-addr-chop-second-arg-when-constant
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (make-data-addr denvr offset)
                  (make-data-addr denvr (loghead 16 offset)))))

(defthm loghead-15-make-data-addr
  (implies (and (integerp y) (integerp x))
           (equal (loghead 15 (make-data-addr x y))
                  (ash (loghead 14 y) 1)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-plus-mult-16
  (implies  (and (syntaxp (not (quotep offset))) ;prevents loops
                 (integerp offset)
                 (integerp denvr))
            (equal (MAKE-DATA-ADDR denvr (+ 65536 offset))
                   (MAKE-DATA-ADDR denvr offset)))
  :hints (("Goal" :in-theory (enable make-data-addr))))




(in-theory (disable make-data-addr-OF-+-LOGHEAD)) ;looped!

(defthm make-data-addr-equal-same-env-rewrite
  (implies (and (integerp denvr)
                (integerp offset1)
                (integerp offset2))
           (equal (EQUAL (MAKE-DATA-ADDR DENVR OFFSET2)
                         (MAKE-DATA-ADDR DENVR OFFSET1))
                  (EQUAL (LOGHEAD 16 OFFSET1)
                         (LOGHEAD 16 OFFSET2))))
  :hints (("Goal" :in-theory (enable make-data-addr))))


(defthm logcar-of-make-data-addr
  (equal (acl2::logcar (make-data-addr denvr offset))
         0)
  :hints (("Goal" :in-theory (enable make-data-addr))))

;; (defthm signed-byte-p-of-make-data-addr-fw
;;   (signed-byte-p 32 (make-data-addr denvr offset))
;;   :rule-classes ((:forward-chaining :trigger-terms ((make-data-addr denvr offset)))))

(defthm unsigned-byte-p-of-make-data-addr-fw
  (unsigned-byte-p 32 (make-data-addr denvr offset))
  :rule-classes ((:forward-chaining :trigger-terms ((make-data-addr denvr offset)))))

(defthm unsigned-byte-p-of-make-data-addr-better
  (implies (and (integerp n)
                (<= 32 n))
           (unsigned-byte-p n (make-data-addr denvr offset)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-make-data-addr)
           :in-theory (disable unsigned-byte-p-of-make-data-addr))))

(defthm evenp-of-make-data-addr
  (evenp (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;bzo
(DEFTHM ODD-<-EVEN-TIGHTEN-alt
  (IMPLIES (AND; (INTEGERP ACL2::I)
               ; (INTEGERP ACL2::J)
                (evenp i)
                (evenp j)
                )
           (EQUAL (< (+ 1 j) i)
                  (< j i)))
  :hints (("Goal" :use (:instance acl2::ODD-<-EVEN-TIGHTEN (acl2::j (/ j 2)) (acl2::i (/ i 2)))
           :in-theory (disable acl2::ODD-<-EVEN-TIGHTEN))))


(encapsulate
 ()
 (local (defthm bk
          (implies (and (equal (loghead 16 (acl2::logcdr x)) (loghead 16 offset))
                        (unsigned-byte-p 32 x) ;;(signed-byte-p 32 x)
                        (equal (acl2::logcar x) 0)
                        (equal (logtail 17 x) (loghead 15 denvr) ;(logext 15 denvr)
                               ))
                   (EQUAL x (MAKE-DATA-ADDR DENVR OFFSET)))
          :rule-classes nil
          :hints (("Goal" :in-theory (enable make-data-addr ifix ACL2::LOGEXT-LOGAPP)))))

 (local (defthm fw
          (implies (EQUAL x (MAKE-DATA-ADDR DENVR OFFSET))
                   (and (equal (loghead 16 (acl2::logcdr x)) (loghead 16 offset))
                        (unsigned-byte-p 32 x) ;(signed-byte-p 32 x)
                        (equal (acl2::logcar x) 0)
                        (equal (logtail 17 x) (loghead 15 denvr) ;(logext 15 denvr)
                               )))
          :rule-classes nil
          :hints (("Goal" :in-theory (enable make-data-addr ifix ACL2::LOGEXT-LOGAPP)))))

;do we want this on?
 (defthmd make-data-addr-equal-rewrite
   (equal (equal x (make-data-addr denvr offset))
          (and (equal (loghead 16 (acl2::logcdr x)) (loghead 16 offset))
               (unsigned-byte-p 32 x) ;;(signed-byte-p 32 x)
               (equal (acl2::logcar x) 0)
               (equal (logtail 17 x) (loghead 15 denvr) ;(logext 15 denvr)
                      )))
   :hints (("Goal" :use (fw bk)))))


;can this (or the other one?) loop?
(defthm make-data-addr-cong16-denvr
  (implies (and (equal (loghead 15 env1)
                       (loghead 15 env2))
                (syntaxp (acl2::smaller-term env2 env1)))
           (equal (make-data-addr env1 offset)
                  (make-data-addr env2 offset)))
  :hints (("Goal" :use ((:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV1)))
                        (:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV2))))
           :in-theory (e/d (make-data-addr logapp) (ACL2::LOGEXT-LOGHEAD)))))

;; (if (logbitp 15 denvr)
;;                       (or (< -1 (logtail 31 x))
;;                           (and (equal -1 (logtail 31 x))
;;                                (< (logapp 16 offset (loghead 15 denvr))
;;                                   (loghead 31 x))))
;;                     (< (loghead 31 (logapp 16 offset denvr)) x))

;simplify more?
;; (defthm <-of-make-data-addr
;;   (implies (and (integerp x)
;;                 (integerp offset) ;drop?
;;                 )
;;            (equal (< (make-data-addr denvr offset) x)
;;                   (if (ACL2::LOGBITP 14 DENVR)
;;                       (< (ASH (LOGAPP 30 (LOGAPP 16 OFFSET DENVR) -1)
;;                               1)
;;                          X)
;;                     (< (ASH (LOGAPP 16 OFFSET (LOGHEAD 14 DENVR))
;;                             1)
;;                        X)
;;                     )))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (make-data-addr logext acl2::logtail-loghead-better
;;                                                   )
;;                                   ( ;equal-of-if
;;                                    acl2::loghead-logtail
;;                                    acl2::logext-logapp ;why?
;;                                    )))))

(defthm <-of-make-data-addr
  (implies (and (integerp x)
                (integerp offset) ;drop?
                )
           (equal (< (make-data-addr denvr offset) x)
                  (< (ASH (LOGAPP 16 OFFSET (LOGHEAD 15 DENVR))
                            1)
                       X)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (make-data-addr logext acl2::logtail-loghead-better
                                                  )
                                  ( ;equal-of-if
                                   acl2::loghead-logtail
                                   acl2::logext-logapp ;why?
                                   )))))

(defthm logtail-16-of-make-data-addr
  (equal (logtail 16 (make-data-addr x y))
         (logapp 1 (acl2::logbit 15 y) (loghead 15 x) ;(logext 15 x)
                 ))
  :hints (("Goal" :cases ((integerp x))
                          :in-theory (e/d (make-data-addr acl2::logext-logapp)
                                  (acl2::logtail-logapp)))))


(defthm loghead-16-of-make-data-addr
  (equal (loghead 16 (make-data-addr x y))
         (ash (loghead 15 y) 1))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;; (defthm equal-of-two-make-data-addrs-rewrite
;;   (equal (equal (make-data-addr ddenvr2 offset2)
;;                 (make-data-addr ddenvr1 offset1))
;;          (and (equal (loghead 16 ddenvr1) ;we could also talk about logexts here?
;;                      (loghead 16 ddenvr2))
;;               (equal (loghead 16 offset1)
;;                      (loghead 16 offset2))))
;;   :hints (("Goal" :in-theory (enable make-data-addr-equal-rewrite))))

(defthm logtail-of-make-data-addr-hack
  (equal (logtail 17 (make-data-addr denvr offset1))
         (loghead 15 denvr); (logext 15 denvr)
         )
  :hints (("Goal" :in-theory (enable make-data-addr ACL2::LOGEXT-LOGAPP))))

;; (defthm logtail15-of-make-data-addr
;;   (equal (logtail 15 (make-data-addr denvr offset))
;;          (logapp 1 (acl2::logbit 15 offset) (logext 16 denvr)))
;;   :hints (("Goal" :in-theory (e/d (make-data-addr ifix ACL2::LOGEXT-LOGAPP)
;;                                   (acl2::logext-logtail)))))

(defthm loghead16-logcdr-make-data-addr
  (equal (loghead 16 (acl2::logcdr (make-data-addr denvr offset)))
         (loghead 16 offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;zz4









;;
;; FETCH-CODE-BYTE
;;

;; bzo have Hardin check this.

;;Fetch the byte at offset OFFSET in code environment CENVR in ram RAM.
(defund fetch-code-byte (cenvr offset ram)
  (declare (type integer cenvr offset)
           (xargs :guard (aamp-ramp ram))
           )
  (rd (make-code-addr cenvr offset) ram) ;old: (rx 8 (make-code-addr cenvr offset) ram)
  )

(defthm fetch-code-byte-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (fetch-code-byte cenvr offset ram)
                  (fetch-code-byte cenvr 0 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-when-cenv-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (fetch-code-byte cenvr offset ram)
                  (fetch-code-byte 0 offset ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

;bzo improve in the usual way -ews
(defthm usb8-of-fetch-code-byte
  (unsigned-byte-p 8 (fetch-code-byte cenvr offset ram))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fetch-code-byte cenvr offset ram))))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-of-loghead
  (equal (fetch-code-byte cenvr (loghead 16 offset) ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-of-loghead-2
  (equal (fetch-code-byte (loghead 16 cenvr) offset ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))


;;
;; FETCH-CODE-BYTES
;;

(defthm address-listp-of-loghead-list-32
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (address-listp (loghead-list 32 vals) ram)))

;bzo handle this better. ADDRESS-LISTP is basically usb-list?
(defthm address-listp-of-logapp-list-of-loghead
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (ADDRESS-LISTP (LOGAPP-LIST 16
                                       (OFFSET-RANGE-WRAP 16 OFFSET NUMBYTES)
                                       (LOGHEAD 16 CENVR))
                          RAM))
  :hints (("Goal" :in-theory (e/d (LOGAPP-LIST-OF-LOGHEAD) (LOGHEAD-LIST-OF-LOGAPP-LIST)))))

;;Fetch NUMBYTES bytes, starting at offset OFFSET in code environment CENVR in ram RAM.
;;This returns a bit vector (that is, a big number).

;;Note that the behavior of this function involves wrapping around; that is,
;;if we reach the end of the code environment, we start reading from the
;;begining of that same environment, not from the next environment.

;;All the calls to loghead and fix below could make this slow, so we could use
;;mbe to give this a fast body. -ews

;; bzo have Hardin check this.

;; Bbzo redo this to call RD-LIST?

;;bzo make this tail recursive?  or redo things to prevent 3 calls when numbytes is 2.

;bzo make a fast executable body..
;recently reordered the params on this

;bzo fast body
;think about guard
;bzo wrap the list of addresses up into a nice function?
;bzo could move the logext-list in?
(defun fetch-code-bytes (numbytes cenvr offset ram)
  (declare (type integer cenvr offset)
           (type (integer 0 *) numbytes)
           (xargs :guard (aamp-ramp ram)))
  (wintlist
   (rd-list ;;(logext-list 32 (logapp-list 16 (offset-range-wrap 16 offset numbytes) cenvr))
    (loghead-list 32 (logapp-list 16 (offset-range-wrap 16 offset numbytes) cenvr))
    ram)))

(defthm fetch-code-bytes-when-numbytes-is-non-positive
  (implies (<= numbytes 0)
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable fetch-code-bytes))))

(defthm fetch-code-bytes-when-numbytes-is-1
  (equal (fetch-code-bytes 1 cenvr offset ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :expand (fetch-code-bytes 1 cenvr offset ram)
           :in-theory (enable fetch-code-bytes fetch-code-byte make-code-addr))))

;bzo fix this! - huh?
(defthm fetch-code-bytes-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes cenvr (ifix offset) ram)))
  :hints (("Goal" :in-theory (e/d (fetch-code-bytes ifix) (FETCH-CODE-BYTE)))))

(defthm fetch-code-bytes-when-cenv-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes 0 offset ram)))
  :hints (("Goal" :in-theory
           (e/d (fetch-code-bytes ifix)
                (fetch-code-byte)))))

;bzo put a limit on this to prevent huge expansions (like the limit on read-data-words-opener)?
(defthmd fetch-code-bytes-opener
  (implies (and (syntaxp (quotep numbytes))
                (not (zp numbytes)))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (logapp 8
                          (fetch-code-byte cenvr (loghead 16 offset) ram)
                          (fetch-code-bytes (+ -1 (ifix numbytes))
                                            cenvr
                                            (loghead 16 (+ 1 (ifix offset)))
                                            ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMBYTES) ;bzo
                           (OFFSET-RANGE-WRAP 16 0 NUMBYTES))
           :in-theory (enable fetch-code-bytes
                                     fetch-code-byte
                                     make-code-addr))))




;bzo will the multiplication get done during forward-chaining?
(defthm unsigned-byte-p-of-fetch-code-bytes
  (implies (and (integerp numbytes)
                (<= 0 numbytes))
           (unsigned-byte-p (* 8 numbytes) (fetch-code-bytes numbytes cenvr offset ram)))
  :rule-classes ((:forward-chaining :trigger-terms ((fetch-code-bytes numbytes cenvr offset ram))))
  :hints (("Goal" :in-theory (enable fetch-code-bytes))))

(defthm unsigned-byte-p-of-fetch-code-bytes-gen
  (implies (and (<= (* 8 numbytes) n)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (equal (unsigned-byte-p n (fetch-code-bytes numbytes cenvr offset ram))
                  (integerp n))))

(defthm fetch-code-bytes-of-loghead
  (equal (fetch-code-bytes numbytes cenvr (loghead 16 offset) ram)
         (fetch-code-bytes numbytes cenvr offset ram))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable fetch-code-bytes zp))))

(defthm fetch-code-bytes-of-loghead-2
  (equal (fetch-code-bytes numbytes (loghead 16 cenvr) offset ram)
         (fetch-code-bytes numbytes cenvr offset ram))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (fetch-code-bytes zp LOGAPP-LIST-OF-LOGHEAD) (LOGHEAD-LIST-OF-LOGAPP-LIST)))))

(defthm loghead-8-of-fetch-code-bytes-better
  (equal (loghead 8 (fetch-code-bytes numbytes cenvr offset ram))
         (if (zp numbytes)
             0
           (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes fetch-code-byte make-code-addr ;firstn
                                     ))))

(defthm fetch-code-bytes-simp-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes cenvr (loghead 16 offset) ram)))
  :hints (("Goal" :use ((:instance FETCH-CODE-BYTES-OF-LOGHEAD (offset (logext 16 offset)))
                        (:instance FETCH-CODE-BYTES-OF-LOGHEAD))
           :in-theory (disable FETCH-CODE-BYTES-OF-LOGHEAD))))

;helps us prove fetch-code-bytes of loghead lemmas
(defthm fetch-code-bytes-agree-when-logheads-agree
  (implies (and (equal (loghead 16 offset1) (loghead 16 offset2))
                (integerp offset1)
                (integerp offset2))
           (equal (equal (gacc::fetch-code-bytes numbytes cenvr offset1 ram)
                         (gacc::fetch-code-bytes numbytes cenvr offset2 ram))
                  t))
  :hints (("Goal" :use ((:instance gacc::fetch-code-bytes-of-loghead
                                   (gacc::offset offset1)
                                   (gacc::numbytes numbytes)
                                   (gacc::cenvr cenvr)
                                   (gacc::ram ram)
                                   )
                        (:instance gacc::fetch-code-bytes-of-loghead
                                   (gacc::offset offset2)
                                   (gacc::numbytes numbytes)
                                   (gacc::cenvr cenvr)
                                   (gacc::ram ram)))
           :in-theory (disable gacc::fetch-code-bytes-of-loghead))))

;bzo
(defthm fetch-code-bytes-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k) (not (unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (gacc::fetch-code-bytes numbytes cenvr (+ k offset) ram)
                  (gacc::fetch-code-bytes numbytes cenvr (+ (loghead 16 k) offset) ram))))

(defthm fetch-code-bytes-sum-subst
  (implies (and (equal (loghead 16 x) y)
                (syntaxp (acl2::smaller-term y x))
                (integerp x)
                (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ x n) ram)
                  (fetch-code-bytes numbytes cenvr (+ y n) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 x))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n x)))))))

(defthm fetch-code-bytes-sum-subst-alt
  (implies (and (equal (loghead 16 x) y)
                (syntaxp (acl2::smaller-term y x))
                (integerp x)
                (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ n x) ram)
                  (fetch-code-bytes numbytes cenvr (+ n y) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 x))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n x)))))))

(defthm fetch-code-bytes-sum-lemma
  (implies (and (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ n (loghead 16 y)) ram)
                  (fetch-code-bytes numbytes cenvr (+ n y) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 y))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n y)))))))


(defun fetch-code-bytes-n-induct (numbytes offset n)
  (if (zp numbytes)
      (+ n offset)
    (fetch-code-bytes-n-induct (1- numbytes)  (+ 1 (loghead 16 offset))  (1- n))))







;will the (* 8 n) in the LHS sometimes prevent this from firing?
(defthm logtail-8n-fetch-code-bytes
  (implies (and (< n numbytes) ;gen?
                (<= 0 n)
                (integerp n)
                )
           (equal (logtail (* 8 n) (fetch-code-bytes numbytes cenvr offset ram))
                  (fetch-code-bytes (- numbytes n) cenvr (+ n (ifix offset)) ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (fetch-code-bytes numbytes cenvr offset ram)
           :induct (fetch-code-bytes-n-induct numbytes offset n)
           :in-theory (enable fetch-code-bytes
                              FETCH-CODE-BYTE))))


;;
;; NO-CODE-DATA-CLASH
;;

;;says that the 15-bit data environment pointer DENVR doesn't equal the high 15
;;bits of the code environment pointer CENV.  Eric hopes to make this the key
;;fact that lets us conclude that code and data accesses don't interfere.
;bzo make a code-data-clash... instead of no-code-data-clash ?
(defund no-code-data-clash (cenvr denvr)
  (declare (type integer cenvr denvr))
  (not (equal (acl2::logcdr (loghead 16 cenvr)) ;add a loghead here?
              (loghead 15 denvr))))



;;
;; FETCH-CODE-BYTES-LIST
;;

;bzo add guard
(defund fetch-code-bytes-list (numbytes cenvr offset ram)
  (enlistw numbytes (fetch-code-bytes numbytes cenvr offset ram)))

(defthm fetch-code-bytes-list-of-loghead16
  (equal (fetch-code-bytes-list len cenvr (loghead 16 offset) ram)
         (fetch-code-bytes-list len cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list))))

;bzo redo this...
;i expect off-offset to be a small integer.
(defthm use-fetch-code-bytes-list-1
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (unsigned-byte-p 16 offset) ;drop?
;                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (rd (make-code-addr cenvr ad) ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable fetch-code-byte fetch-code-bytes-list make-code-addr))))

(defthm use-fetch-code-bytes-list-2
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (rd (make-code-addr cenvr ad) ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :in-theory (e/d (ifix fetch-code-bytes-list) (use-fetch-code-bytes-list-1))
           :use (:instance use-fetch-code-bytes-list-1 (offset (loghead 16 offset))))))

(defthm use-fetch-code-bytes-list-4
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (fetch-code-byte cenvr ad ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :in-theory (e/d (ifix fetch-code-byte
                                        ;rx-to-rd
                                        fetch-code-bytes-list)
                                  (use-fetch-code-bytes-list-1))
           :use (:instance use-fetch-code-bytes-list-1 (offset (loghead 16 offset))))))

;eventually don't go to addr range?
;gen
;bzo remove the stuff that mentions addr-range?
;; (defthm disjoint-of-addr-ranges-of-make-data-addrs
;;   (implies (and (integerp denvr)
;;                 (integerp offset1)
;;                 (integerp offset2))
;;            (equal (bag::disjoint (addr-range (make-data-addr denvr offset1) 2)
;;                                  (addr-range (make-data-addr denvr offset2) 2))
;;                   (not (equal (loghead 16 offset1) (loghead 16 offset2)))))
;;   :hints (("Goal" :in-theory (e/d (disjoint-of-two-addr-ranges
;;                                    logext ;bzo disable and get lemmas!
;;                                    ash
;;                                    ;makeaddr
;;                                    ACL2::LOGTAIL-LOGHEAD-BETTER
;;                                    MAKE-data-ADDR
;;                                    )
;;                                   ( ;acl2::<-of-ash
;;                                    acl2::loghead-logtail
;;                                    acl2::extend-<
;;                                    MAKE-data-ADDR-CONG16
;;                                    )))))

(defthm code-addr-isnt-one-plus-data-addr
  (implies (no-code-data-clash cenvr denvr)
           (not (equal (make-code-addr cenvr offset)
                       (+ 1 (make-data-addr denvr offset2)))))
  :hints (("Goal" :in-theory (enable no-code-data-clash
                                     make-code-addr-equal-rewrite
                                     ;make-data-addr
                                     ))))

(defthm logcdr-of-code-addr-isnt-data-addr
  (implies (no-code-data-clash cenvr denvr)
           (not (equal (make-code-addr cenvr offset)
                       (make-data-addr denvr offset2))))
  :hints (("Goal" :in-theory (enable no-code-data-clash
                                     make-code-addr-equal-rewrite
                                     ))))



(defthm not-equal-code-addr-data-addr
  (implies (and (no-code-data-clash cenvr denvr)
;                (integerp offset)
                (integerp cenvr)
                (integerp offset2)
                (integerp denvr)
                )
           (not (equal (make-code-addr cenvr offset)
                       (make-data-addr denvr offset2))))
  :hints (("Goal" :in-theory (enable acl2::equal-to-ash-1-rewrite
                                     NO-CODE-DATA-CLASH
                                     ))))

(defthm fetch-code-byte-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-byte cenvr offset (write-data-word ;write-data-word
                                                denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable RD-OF-WR-LIST-DIFF
                                     list::memberp-of-cons
                                     write-data-word
;                                     rx-to-rd
                                     make-code-addr
                                     WORD-AD-TO-BYTE-ADS
                                     fetch-code-byte no-code-data-clash))))



;; (defthm fetch-code-byte-of-write-data-words
;;   (implies (no-code-data-clash cenvr denvr)
;;            (equal (fetch-code-byte cenvr offset (write-data-words ;write-data-words
;;                                                 numwords denvr offset2 val ram))
;;                   (fetch-code-byte cenvr offset ram)))
;;   :hints (("Goal" :in-theory (enable write-data-words
;;                                      WORD-AD-TO-BYTE-ADS
;;                                      make-code-addr
;;                                      fetch-code-byte
;;                                      rx-to-rd
;;                                      ))))

;bzo gen this!  see above
(defthm fetch-code-byte-of-write-data-words
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-byte cenvr offset (write-data-words ;write-data-words
                                                 2 ;numwords
                                                 denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (RD-OF-WR-LIST-DIFF
                                   write-data-words
                                   acl2::logext-logapp
                                   WORD-AD-TO-BYTE-ADS
                                   make-code-addr
                                   fetch-code-byte
;                                     rx-to-rd
                                   OFFSET-RANGE-WRAP-CONST-OPENER
                                   NO-CODE-DATA-CLASH
                                   list::memberp-of-cons
                                   )
                                  (WRITE-DATA-WORDS-OPENER)))))


;; (encapsulate
;;  ()
;; ;bzo why so many enables?
;;  (local (defthm disjoint-of-data-addr-ranges-when-offs-differ-helper
;;           (implies (and (not (equal (loghead 16 offset1) (loghead 16 offset2)))
;;                         (integerp offset1)
;;                         (integerp offset2)
;;                         (integerp denvr1)
;;                         (integerp denvr2)
;;                         )
;;                    (BAG::DISJOINT (ADDR-RANGE (MAKE-data-ADDR DENVR1 OFFSET1)
;;                                                     '2)
;;                                   (ADDR-RANGE (MAKE-data-ADDR DENVR2 OFFSET2)
;;                                                     '2)))
;;           :otf-flg t
;;           :hints ( ;("goal'4'" :in-theory (e/d (LOGEXT-LOGAPP-HACK) (LOGAPP-OF-LOGEXT))) ;gross!
;;                   ("Goal" :in-theory (e/d (;acl2::LOGEXT-LOGAPP-HACK
;;                                            acl2::LOGEXT-LOGAPP
;;                                            DISJOINT-OF-TWO-ADDR-RANGES
;;                                            ACL2::LOGHEAD-OF-ONE-MORE-THAN-X
;;                                            logext
;;                                            make-data-addr
;;                                            )
;;                                           (acl2::LOGAPP-OF-LOGEXT
;;                                            ))))))



;;  (defthm disjoint-of-data-addr-ranges-when-offs-differ
;;    (implies (not (equal (loghead 16 offset1) (loghead 16 offset2)))
;;             (BAG::DISJOINT (ADDR-RANGE (MAKE-data-ADDR DENVR1 OFFSET1) 2)
;;                            (ADDR-RANGE (MAKE-data-ADDR DENVR2 OFFSET2) 2)))
;;    :hints (("Goal" :use (:instance disjoint-of-data-addr-ranges-when-offs-differ-helper (denvr2 (ifix denvr2)) (denvr1 (ifix denvr1)) (offset1 (ifix offset1)) (offset2 (ifix offset2)))
;;             :in-theory (disable disjoint-of-data-addr-ranges-when-offs-differ-helper
;;                                 DISJOINT-OF-TWO-ADDR-RANGES)))))



;; (defthm disjoint-of-data-addr-ranges-when-denvrs-differ
;;   (implies (and (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;                 )
;;            (bag::disjoint (addr-range (make-data-addr denvr1 offset1)
;;                                             2)
;;                           (addr-range (make-data-addr denvr2 offset2)
;;                                             2)))
;;   :hints (("Goal" :in-theory (e/d (MAKE-DATA-ADDR-EQUAL-REWRITE
;;                                    disjoint-of-two-addr-ranges)
;;                                   (<-OF-MAKE-DATA-ADDR)))))

;bzo improve these?







;; (defthm loghead-list-of-word-ads-to-byte-ads-hack
;;   (implies (unsigned-byte-p-list 31 word-ads)
;;            (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
;;                   (word-ads-to-byte-ads word-ads)))
;;   :hints (("Goal" :in-theory (enable word-ads-to-byte-ads
;;                                      word-ad-to-byte-ads
;;                                      ))))



;The :instance hints were needed because of stuff like this:
;; 2x (:REWRITE HACK-FOR-CODE-DATA-CLASH) failed because :HYP 1 is judged
;; more complicated than its ancestors (type :ANCESTORS to see the ancestors
;; and :PATH to see how we got to this point).
;; 2)
;; -ews
(defthm fetch-code-bytes-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes numbytes cenvr offset1 (write-data-word denvr offset2 val ram))
                  (fetch-code-bytes numbytes cenvr offset1 ram)))
  :hints (("Goal" :use ((:instance hack-for-code-data-clash (denvr ;(LOGEXT '31 (LOGAPP '16 OFFSET2 DENVR))
                                                             (LOGhead '31 (LOGAPP '16 OFFSET2 DENVR))
                                                             )
                                   (cenvs (LOGAPP-LIST '16
                                                       (OFFSET-RANGE-WRAP 16 OFFSET1 NUMBYTES)
                                                       (LOGhead '16 CENVR) ;(LOGEXT '16 CENVR)
                                                       )
                                          ))
                        (:instance hack-for-code-data-clash2 (denvr ;(LOGEXT '31 (LOGAPP '16 OFFSET2 DENVR))
                                                              (LOGhead '31 (LOGAPP '16 OFFSET2 DENVR))
                                                              )
                                   (cenvs (LOGAPP-LIST '16
                                                       (OFFSET-RANGE-WRAP 16 OFFSET1 NUMBYTES)
                                                       (LOGhead '16 CENVR) ;(LOGEXT '16 CENVR)
                                                       )
                                          )))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (fetch-code-bytes write-data-word WORD-AD-TO-BYTE-ADS
                                             NO-CODE-DATA-CLASH
                                             )
                           (hack-for-code-data-clash
                            hack-for-code-data-clash2
                            ;ACL2::ASSOCIATIVITY-OF-LOGAPP-BETTER
                            ACL2::LOGAPP-0-PART-2-BETTER)))))

(defthm fetch-code-bytes-list-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes-list numbytes cenvr offset1 (write-data-word denvr offset2 val ram))
                  (fetch-code-bytes-list numbytes cenvr offset1 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list))))

(defthm fetch-code-bytes-list-of-write-data-words-irrel
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes-list numbytes cenvr offset1 (write-data-words numwords denvr offset2 val ram))
                  (fetch-code-bytes-list numbytes cenvr offset1 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list
                                     fetch-code-bytes ;bzo
                                     write-data-words
                                     no-code-data-clash
                                     disjoint-of-WORD-AD-TO-BYTE-ADS
                                     disjoint-of-word-ads-to-byte-ads
                                     ))))

;(in-theory (disable BAG::SUBBAG-BY-MULTIPLICITY))

(defthm fetch-code-byte-of-sum-of-loghead-two
  (implies (and (integerp off1)
                (integerp off2))
           (equal (fetch-code-byte cenvr (+ off1 (loghead 16 off2)) ram)
                  (fetch-code-byte cenvr (+ off1 off2) ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte
                                     MAKE-CODE-ADDR ;bzo
                                     ))))

(defthm fetch-code-byte-of-sum-of-loghead-one
  (implies (and (integerp off1)
                (integerp off2))
           (equal (fetch-code-byte cenvr (+ (loghead 16 off2) off1) ram)
                  (fetch-code-byte cenvr (+ off1 off2) ram)))
  :hints (("Goal" :use (:instance  fetch-code-byte-of-sum-of-loghead-two)
           :in-theory (disable  fetch-code-byte-of-sum-of-loghead-two))))


(local (in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))


(defthm fetch-code-byte-of-write-data-word-bag-phrasing
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word denvr offset2)))
           (equal (fetch-code-byte cenvr offset (write-data-word denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word
                                   fetch-code-byte
                                   RD-OF-WR-LIST-DIFF
                                   )
                                  (ADDRESSES-OF-DATA-WORD)))))

(defthm fetch-code-byte-of-clear-data-word-bag-phrasing
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word denvr offset2)))
           (equal (fetch-code-byte cenvr offset (clear-data-word denvr offset2 ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))









(encapsulate
 ()

;this doesn't open up write-data-words but rather uses write-data-words-opener
 (local (defthm FETCH-CODE-BYTE-of-WRITE-DATA-WORDS-helper
          (implies (and (NO-CODE-DATA-CLASH cenvr denvr)
                        (integerp offset2)
                        )
                   (equal (FETCH-CODE-BYTE cenvr offset (WRITE-DATA-WORDS numwords denvr offset2 value ram))
                          (FETCH-CODE-BYTE cenvr offset ram)))
          :hints (("subgoal *1/2" :in-theory (disable WRITE-DATA-WORD-EQUAL-REWRITE
                                                      WRITE-DATA-WORDS-OPENER)
                   :use (:instance WRITE-DATA-WORDS-OPENER
                                   (numwords numwords)
                                   (denvr denvr)
                                   (offset offset2)
                                   (ram ram)
                                   ))

                  ("Goal" :in-theory (e/d (zp ) (WRITE-DATA-WORD-EQUAL-REWRITE))
                   :do-not '(generalize eliminate-destructors)
                   :induct (write-data-words-induct numwords offset2 value)))))

;need this because the numwords argument to WRITE-DATA-WORDS might not be a
;constant (e.g., when we talk about writing the whole call stack)
;

;bzo kill the non-gen
 (defthm fetch-code-byte-of-write-data-words-gen
   (implies (no-code-data-clash cenvr denvr)
            (equal (fetch-code-byte cenvr offset (write-data-words numwords denvr offset2 value ram))
                   (fetch-code-byte cenvr offset ram)))
   :otf-flg t
   :hints (("Goal" :cases ((integerp offset2))))
   ))







(defun read-data-words-induct (numwords offset)
  (if (zp numwords)
      (list numwords offset)
    (read-data-words-induct (+ -1 numwords) (+ 1 (ifix offset)))))



;; (encapsulate
;;  ()
;;  (local (defthm read-data-word-of-write-data-words-same
;;           (implies (and (< offset (+ numwords offset2))
;;                         (<= offset2 offset)
;;                         (unsigned-byte-p 16 offset)
;;                         (unsigned-byte-p 16 offset2)
;;                         (integerp numwords)
;;                         )
;;                    (equal (READ-DATA-WORD denvr offset (WRITE-DATA-WORDS numwords denvr offset2 value ram))
;;                           (nthword (- offset offset2) value)))
;;           :hints (("subgoal *1/2" :in-theory (disable WRITE-DATA-WORD-EQUAL-REWRITE
;;                                                       WRITE-DATA-WORDS-OPENER)
;;                    :expand (NTHWORD (+ OFFSET (- OFFSET2))
;;                                     VALUE)
;;                    :use (:instance WRITE-DATA-WORDS-OPENER (numwords numwords)
;;                                    (denvr denvr)
;;                                    (offset offset2)
;;                                    (ram ram)))
;;                   ("Goal" :in-theory (enable zp)
;; ;          :expand (WRITE-DATA-WORDS NUMWORDS DENVR OFFSET VALUE RAM)
;;                    :do-not '(generalize eliminate-destructors)
;;                    :induct (write-data-words-induct numwords offset2 value)))
;;           ))

;; ;bzo make this local !
;;  (defthm read-data-word-of-write-data-words-same-gen
;;    (implies (and (< (loghead 16 offset) (+ numwords (loghead 16 offset2)))
;;                  (<= (loghead 16 offset2) (loghead 16 offset)) ;bzo drop?
;;                  (integerp offset2)
;;                  (integerp numwords)
;;                  )
;;             (equal (read-data-word denvr offset (write-data-words numwords denvr offset2 value ram))
;;                    (nthword (- (loghead 16 offset) (loghead 16 offset2)) value)))
;;    :hints (("Goal" :in-theory (disable read-data-word-of-write-data-words-same )
;;             :use (:instance  read-data-word-of-write-data-words-same
;;                              (offset (loghead 16 offset))
;;                              (offset2 (loghead 16 offset2)))))))

(defthm loghead-16-of-diff-equals-0
  (implies (and (EQUAL (LOGHEAD 16 OFFSET) (LOGHEAD 16 OFFSET2))
                (integerp OFFSET)
                (integerp OFFSEt2))
           (equal (LOGHEAD 16 (+ OFFSET (- OFFSET2)))
                  0))
  :hints (("Goal" :in-theory (enable acl2::loghead-of-minus
                                     ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))



(defun read-data-words-induct-with-n (numwords offset n)
  (if (zp numwords)
      (list numwords offset n)
      (read-data-words-induct-with-n (+ -1 numwords)
                                     (+ 1 (ifix offset))
                                     (+ -1 n)
                                     )))

;make a both version?
;rename to have a same including same?
(defthm nthword-of-read-data-words
  (implies (and (<= 0 n)
                (< n numwords)
                (integerp n)
                (integerp offset2)
                (integerp offset)
                (integerp numwords)
                )
           (equal (NTHWORD n (READ-DATA-WORDS numwords denvr offset ram))
                  (read-data-word denvr (+ n offset) ram)))
  :hints (("subgoal *1/2"
           :expand (NTHWORD N
                            (READ-DATA-WORDS NUMWORDS DENVR OFFSET RAM))
           :in-theory (disable WRITE-DATA-WORDS-OPENER))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read-data-words-induct-with-n numwords offset n))))






;;
;; WRITE-NTH-WORD
;;

;move to super-ihs? (along with nth-word)
;value is a big bit vector
;0 means the least significant word of VALUE
(defund write-nth-word (n word value)
  (if (zp n)
      (logapp 16 word (logtail 16 value))
    (logapp 16 (loghead 16 value) (write-nth-word (+ -1 n) word (logtail 16 value)))))

(defthm write-nth-word-when-n-is-zp
  (implies (zp n)
           (equal (write-nth-word n word value)
                  (logapp 16 word (logtail 16 value))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm write-nth-word-when-value-it-not-an-integerp
  (implies (not (integerp value))
           (equal (write-nth-word n word value)
                  (write-nth-word n word 0)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(DEFUN WRITE-DATA-WORDS-INDUCT-with-n (NUMWORDS OFFSET VALUE n)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE n)
      (WRITE-DATA-WORDS-INDUCT-with-n (+ -1 NUMWORDS)
                                            (+ 1 OFFSET)
                                            (LOGTAIL 16 VALUE)
                                            (+ -1 n)
                                            )))






(defun read-data-words-induct-wrap
  (numwords offset)
  (if (zp numwords)
      (list numwords offset)
    (read-data-words-induct-wrap (+ -1 numwords)
                                 (loghead 16 (+ 1 offset)))))

(defthm logtail-16-of-write-nth-word
  (equal (logtail 16 (write-nth-word n word value))
         (if (zp n)
             (logtail 16 value)
           (write-nth-word (+ -1 n) word (logtail 16 value))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm loghead-16-of-write-nth-word
  (equal (loghead 16 (write-nth-word n word value))
         (if (zp n)
             (loghead 16 word)
           (loghead 16 value)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm read-data-words-of-write-data-word-same-E
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                ;(unsigned-byte-p 16 numwords)
                (integerp numwords)
                (<= 0 numwords)
                (<= numwords 65536)
                (integerp offset1)
                (integerp offset2)
                )
           (equal (read-data-words numwords denvr offset1 (write-data-word denvr offset2 word ram))
                  (write-nth-word (loghead 16 (- offset2 offset1)) word (read-data-words numwords denvr offset1 ram))))
  :hints (("subgoal *1/2"
           :expand ((WRITE-NTH-WORD 0 WORD
                                    (READ-DATA-WORDS NUMWORDS DENVR 65535 RAM))
                    (WRITE-NTH-WORD 0 WORD
                                    (READ-DATA-WORDS NUMWORDS DENVR OFFSET1 RAM))
                    (write-nth-word (+ (- offset1) offset2)
                                    word
                                    (read-data-words numwords denvr offset1 ram)))

           :in-theory (e/d (zp ;write-nth-word
                            MEMBERP-OF-OFFSET-RANGE
                            acl2::loghead-sum-split-into-2-cases
                            acl2::loghead-of-minus
                            read-data-words-alt-def
                            ) (read-data-words-opener)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable zp ;write-nth-word
                              )
           :induct (read-data-words-induct-wrap numwords offset1))))

(DEFUN WRITE-DATA-WORDS-INDUCT-wrap
  (NUMWORDS OFFSET VALUE)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE)
      (WRITE-DATA-WORDS-INDUCT-wrap (+ -1 NUMWORDS)
                                          (loghead 16 (+ 1 OFFSET))
                                          (LOGTAIL 16 VALUE))))



;gen the 0?
(defthm write-nth-word-0-logapp
  (equal (write-nth-word 0 value (logapp 16 lowbits highbits))
         (logapp 16 value highbits))
  :hints (("Goal" :in-theory (enable write-nth-word))))


;move?
(encapsulate
 ()


 (local (defthm read-data-words-of-write-data-words-same-helper
          (implies (and (unsigned-byte-p 16 numwords)
                        (integerp offset)
                        )
                   (equal (read-data-words numwords denvr offset (write-data-words numwords denvr offset value ram))
                          (loghead (* 16 numwords) value)))
          :hints (("subgoal *1/2"
                   :in-theory (e/d (;(expt)
                                    READ-DATA-WORDS-alt-def
                                    ;WRITE-DATA-WORDS-recollapse
                                    WRITE-DATA-WORDS-alt-def)
                                   (WRITE-DATA-WORDS-opener
                                    WRITE-DATA-WORDS-EQUAL-REWRITE))
                   :use (:instance WRITE-DATA-WORDS-opener
                                   (offset offset)
                                   (denvr denvr)
                                   (numwords numwords)
                                   (value value)
                                   (ram ram)))
                  ("Goal" :do-not '(generalize eliminate-destructors)
                   :induct (WRITE-DATA-WORDS-INDUCT-wrap numwords offset value)))))

     ;allow offsets to differ?
 (defthm read-data-words-of-write-data-words-same
   (implies (unsigned-byte-p 16 numwords)
            (equal (read-data-words numwords denvr offset (write-data-words numwords denvr offset value ram))
                   (loghead (* 16 numwords) value)))
   :hints (("Goal" :in-theory (disable read-data-words-of-write-data-words-same-helper)
            :use (:instance read-data-words-of-write-data-words-same-helper
                            (offset (ifix offset)))))))




(defun induct-by-sub1-and-sub16 (n m)
  (if (zp n)
      (list n m)
    (induct-by-sub1-and-sub16 (+ -1 n) (+ -16 m))))

(defun induct-by-sub1-and-sub1 (n m)
  (if (zp n)
      (list n m)
    (induct-by-sub1-and-sub1 (+ -1 n) (+ -1 m))))

(defun induct-by-sub1-and-sub1-and-logtail16 (n m value)
  (if (zp n)
      (list n m value)
    (induct-by-sub1-and-sub1-and-logtail16 (+ -1 n) (+ -1 m) (logtail 16 value))))


;bzo can loop
(defthmd logtail-16-of-WRITE-NTH-WORD-back
  (implies (and (integerp n)
                (<= 0 n))
           (equal (WRITE-NTH-WORD n word (logtail 16 value))
                  (logtail 16 (WRITE-NTH-WORD (+ 1 n) word value))))
  :hints (("Goal" :in-theory (enable ;WRITE-NTH-WORD
                              ))))

(defthm loghead-of-WRITE-NTH-WORD
  (implies (and (< n m)
                (integerp m)
                (integerp n)
                (<= 0 n)
                (<= 0 m)
                )
           (equal (loghead (* 16 m) (WRITE-NTH-WORD N WORD VALUE))
                  (WRITE-NTH-WORD N WORD (loghead (* 16 m) VALUE))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct ( induct-by-sub1-and-sub1-and-logtail16 n m value)
           :expand (WRITE-NTH-WORD N WORD (LOGHEAD (* 16 M) VALUE))
           :in-theory (e/d (WRITE-NTH-WORD
     ;                           logtail-16-of-WRITE-NTH-WORD-back
                            )
                           ( logtail-16-of-WRITE-NTH-WORD)))))

(defthm write-data-word-of-write-data-words-same
  (implies (and (< (loghead 16 (- offset1 offset2)) numwords)
                (integerp offset1)
                (integerp offset2)
                (unsigned-byte-p 16 numwords)
                (integerp word)
                )
           (equal (write-DATA-WORD denvr offset1 word (WRITE-DATA-WORDS numwords denvr offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr offset2
                                          (write-nth-word (loghead 16 (- offset1 offset2)) word value) ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;usb-of-sum-with-two-other-addends-hack
                              MEMBERP-OF-OFFSET-RANGE
                              acl2::loghead-sum-split-into-2-cases
                              acl2::loghead-of-minus
                              )
     ;:induct (WRITE-DATA-WORDS-INDUCT-wrap numwords offset2 value)
           )))

(defthm clear-data-word-of-write-data-words-same
  (implies (and (< (loghead 16 (- offset1 offset2)) numwords)
                (integerp offset1)
                (integerp offset2)
                (unsigned-byte-p 16 numwords)
                (integerp word)
                )
           (equal (clear-DATA-WORD denvr offset1 (WRITE-DATA-WORDS numwords denvr offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr offset2
                                          (write-nth-word (loghead 16 (- offset1 offset2)) 0 value) ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (clear-DATA-WORD
                              ) (WRITE-DATA-WORD-EQUAL-REWRITE))
     ;:induct (WRITE-DATA-WORDS-INDUCT-wrap numwords offset2 value)
           )))


(defthm WRITE-NTH-WORD-of-logapp
  (equal (WRITE-NTH-WORD n word (LOGAPP 16 x y))
         (if (zp n)
             (LOGAPP 16 word y)
           (LOGAPP 16 x (WRITE-NTH-WORD (+ -1 n) word y))))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD))))


(defthm write-nth-word-0-when-usb16
  (implies (unsigned-byte-p 16 value)
           (equal (write-nth-word 0 word value)
                  (loghead 16 word)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm nthword-of-write-nth-word-same
  (equal (NTHWORD n (WRITE-NTH-WORD n word value))
         (loghead 16 word))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

;make a both?
(defthm nthword-of-write-nth-word-diff
  (implies (and (natp n1)
                (natp n2)
                (not (equal n1 n2))
                )
           (equal (NTHWORD n1 (WRITE-NTH-WORD n2 word value))
                  (NTHWORD n1 value)))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

(defthm write-nth-word-constant-opener
  (implies (syntaxp (quotep n))
           (equal (write-nth-word n word value)
                  (if (zp n)
                      (logapp 16 word (logtail 16 value))
                    (logapp 16 (loghead 16 value) (write-nth-word (+ -1 n) word (logtail 16 value))))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm write-nth-word-of-write-nth-word-diff
  (implies (and (natp n1)
                (natp n2)
                (not (equal n1 n2)))
           (equal (write-nth-WORD n1 word1 (WRITE-NTH-WORD n2 word2 value))
                  (write-nth-WORD n2 word2 (WRITE-NTH-WORD n1 word1 value))))
  :rule-classes ((:rewrite :loop-stopper ((n1 n2))))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

(defthm write-nth-word-of-write-nth-word-same
  (equal (write-nth-word n word1 (write-nth-word n word2 value))
         (write-nth-word n word1 value))
  :hints (("Goal" :in-theory (enable write-nth-word nthword))))






;could make a bound about the second word?
(defthm read-data-words-bound
  (implies (and (integerp n)
                (< 0 n))
           (<= (read-data-word denvr offset ram)
               (read-data-words n denvr offset ram)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance read-data-words-alt-def
                                  (denvr denvr)
                                  (offset offset)
                                  (ram ram)
                                  (numwords n)
                                  )
           :in-theory (e/d (acl2::loghead-identity)
                           (loghead-16-of-read-data-words
;                               loghead-times-16-of-read-data-words
                               read-data-words-alt-def)))))

(defthm read-data-words-when-high-word-is-zero-cheap
  (implies (and (equal 0 (read-data-word denvr (+ 1 offset) ram))
                (integerp offset))
           (equal (read-data-words 2 denvr offset ram)
                  (read-data-word denvr offset ram)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  :hints (("Goal" :in-theory (enable read-data-words-alt-def))))


;bzo generalize this sequence?
(defthm read-data-word-when-read-data-words-equals-constant
  (implies (and (equal k (read-data-words numwords denvr offset ram))
                (syntaxp (quotep k)) ;consider relaxing this?
                (< 0 numwords)
                (integerp numwords)
                )
           (equal (read-data-word denvr offset ram)
                  (loghead 16 k))))

(defthm read-data-word-when-read-data-words-equals-constant-2
  (implies (and (equal k (read-data-words numwords denvr offset ram))
                (syntaxp (quotep k)) ;consider relaxing this?
                (< 1 numwords)
                (integerp numwords)
                (integerp offset)
                )
           (equal (read-data-word denvr (+ 1 offset) ram)
                  (loghead 16 (logtail 16 k)))))



(defthm fetch-code-bytes-list-of-sum-normalize-constant
  (implies (and (syntaxp (quotep z))
                (not (acl2::unsigned-byte-p 16 z))
                (integerp z)
                )
           (equal (fetch-code-bytes-list numbytes cenvr (+ z offset) ram)
                  (fetch-code-bytes-list numbytes cenvr (+ (loghead 16 z) offset) ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list fetch-code-bytes))))

;dup?
(defthm write-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr (+ k offset) value ram)
                  (write-data-words numwords denvr (+ (loghead 16 k) offset) value ram)))
  :hints (("Goal" :use ((:instance write-data-words-of-loghead-16 (offset (+ k offset)))
                        (:instance write-data-words-of-loghead-16 (offset (+ (loghead 16 k) offset))))
           :in-theory (e/d () (write-data-word-of-loghead-16
                               write-data-word-equal-rewrite)))))

;dup?
(defthm clear-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (clear-data-words numwords denvr (+ k offset) ram)
                  (clear-data-words numwords denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;dup?
(defthm read-data-word-of-sum-normalize-constant-2
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp offset)
                (not (unsigned-byte-p 16 k)))
           (equal (read-data-word denvr (+ k offset) ram)
                  (read-data-word denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :use ((:instance READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT (k (+ k offset)))
                        (:instance READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT (k (+ (loghead 16 k) offset))))
           :in-theory (e/d () (READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT)))))

;bzo move this series
(defthmd write-data-words-opener-hack
  (implies (and (syntaxp (equal numwords 'numwords)) ;note this
                (not (zp numwords)))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-word
                   denvr
                   offset (loghead 16 value)
                   (write-data-words (+ -1 numwords)
                                     denvr (+ 1 (ifix offset))
                                     (logtail 16 value)
                                     ram))))
  :hints (("Goal" :use (:instance write-data-words-opener
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (numwords numwords)
                                   (value value)
                                  )
           :in-theory (disable write-data-words))))



(defthm write-data-words-of-loghead
  (implies (and (acl2::natp numwords)
                (INTEGERP OFFSET))
           (equal (write-data-words numwords denvr offset (loghead (* 16 numwords) value) ram)
                  (write-data-words numwords denvr offset value ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write-data-words-induct numwords offset value)
           :in-theory (e/d ( WRITE-DATA-WORDS-opener-hack
                           ;  WRITE-DATA-WORDS-alt-def
                             )
                           (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm write-data-words-of-sum-normalize-constant-addend-in-value
  (implies (and (syntaxp (and (quotep k)
                              (not (unsigned-byte-p (* 16 (cadr numwords)) (cadr k)))))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset (+ k value) ram)
                  (write-data-words numwords denvr offset (+ (loghead (* 16 numwords) k) value) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (+ (loghead (* 16 numwords) k) value)))
                        (:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (+ k value))))
           :in-theory (e/d () (WRITE-DATA-WORDs-of-loghead
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-of-sum-normalize-constant-value
  (implies (and (syntaxp (and (quotep k)
                              (quotep numwords)
                              (<= 0 (cadr numwords))
                              (not (unsigned-byte-p (* 16 (cadr numwords)) (cadr k)))))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset k ram)
                  (write-data-words numwords denvr offset (loghead (* 16 numwords) k) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (loghead (* 16 numwords) k)))
                        (:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value k)))
           :in-theory (e/d () (WRITE-DATA-WORDs-of-loghead
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-hack
  (implies (and (integerp y)
                (integerp x)
                (integerp offset)
                (equal n (* 16 numwords))
                (< 0 numwords) ;bzo gen
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset (+ (LOGEXT n x) y) ram)
                  (write-data-words numwords denvr offset (+ x y) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
                                   ;;                                    (denvr denvr)
                                   ;;                                    (offset offset)
                                   ;;                                    (ram ram)
                                   (value (+ (LOGEXT n x) y)))
                        (:instance WRITE-DATA-WORDs-of-loghead
                                   ;;                                    (denvr denvr)
                                   ;;                                    (offset offset)
                                   ;;                                    (ram ram)
                                   (value (+ x y))))
           :in-theory (e/d () (
                               WRITE-DATA-WORDS-OF-LOGHEAD
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-hack-alt
  (implies (and (integerp y)
                (integerp x)
                (integerp offset)
                (equal n (* 16 numwords))
                (< 0 numwords) ;bzo gen
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset (+ y (LOGEXT n x)) ram)
                  (write-data-words numwords denvr offset (+ x y) ram)))
  :hints (("Goal" :use (:instance write-data-words-hack)
           :in-theory (disable write-data-words-hack))))



;bzo gen and add theory invar with opener
(defthmd fetch-code-bytes-recollect
  (implies (and (equal (loghead 16 (+ 2 offset1)) (loghead 16 offset2))
                (integerp offset1))
           (equal (logapp 16
                          (gacc::fetch-code-bytes 2 cenvr offset1 ram)
                          (gacc::fetch-code-byte cenvr offset2 ram))
                  (gacc::fetch-code-bytes 3 cenvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (GACC::FETCH-CODE-BYTES-OPENER) (fetch-code-bytes)))))

(theory-invariant (incompatible (:rewrite fetch-code-bytes-recollect) (:rewrite fetch-code-bytes-opener)))

(defthmd addresses-of-data-words-constant-opener
  (implies (and (syntaxp (quotep numwords))
                (integerp numwords)
                (< 0 numwords)
                (integerp offset))
           (equal (gacc::addresses-of-data-words numwords denvr offset)
                  (append (gacc::addresses-of-data-word denvr offset)
                          (gacc::addresses-of-data-words (+ -1 numwords) denvr (+ 1 offset)))))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm addresses-of-data-words-of-0
  (equal (gacc::addresses-of-data-words 0 denvr offset)
         nil))

(defthm addresses-of-data-word-of-sum-loghead
  (implies (and (integerp a)
                (integerp b))
           (equal (gacc::addresses-of-data-word denvr (+ a (loghead 16 b)))
                  (gacc::addresses-of-data-word denvr (+ a b)))))

(defthm cadr-of-word-ad-to-byte-ads
  (equal (cadr (gacc::word-ad-to-byte-ads word-ad))
         (acl2::logapp 1 1 word-ad))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defthm car-of-word-ad-to-byte-ads
  (equal (car (gacc::word-ad-to-byte-ads word-ad))
         (acl2::logapp 1 0 word-ad))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defthm logcdr-list-of-word-ad-to-byte-ads
  (equal (gacc::logcdr-list (gacc::word-ad-to-byte-ads ad))
         (list (ifix ad) (ifix ad)))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defun dup-and-ifix-all (lst)
  (if (endp lst)
      nil
    (cons (ifix (car lst)) (cons (ifix (car lst)) (dup-and-ifix-all (cdr lst))))))

(defthm logcdr-list-of-word-ads-to-byte-ads
  (equal (gacc::logcdr-list (gacc::word-ads-to-byte-ads word-ads))
         (dup-and-ifix-all word-ads))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads gacc::logcdr-list))))

(defthm dup-and-ifix-perm
  (implies (integer-listp lst)
           (bag::perm (dup-and-ifix-all lst)
                      (append lst lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm nthword-of-0-value
  (equal (nthword n 0)
         0)
  :hints (("Goal" :in-theory (enable gacc::nthword))))

(defthm nthword-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (gacc::nthword n value)
                  0))
  :hints (("Goal" :in-theory (enable gacc::nthword ;-rewrite
                                     ))))

;move to gacc/ram3
(defthm loghead-times-16-of-read-data-words
  (implies (and (integerp numwords1)
                (integerp numwords2)
                )
           (equal (loghead (* 16 numwords1) (gacc::read-data-words numwords2 denvr offset ram))
                  (if (<= numwords1 numwords2)
                      (gacc::read-data-words numwords1 denvr offset ram)
                    (gacc::read-data-words numwords2 denvr offset ram))))

  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::read-data-words-alt-def
                       )
           :induct (gacc::read-data-words-induct-with-n numwords2 offset numwords1))))

;ram3
(defthm logtail-times-16-of-read-data-words
  (implies  (and (integerp numwords1)
                 (integerp numwords2)
;                 (<= 0 numwords2)
                 (<= 0 numwords1)
                 (integerp offset)
                 )
            (equal (LOGTAIL (* 16 NUMWORDS1) (GACC::READ-DATA-WORDS NUMWORDS2 DENVR offset ram))
                   (GACC::READ-DATA-WORDS (- NUMWORDS2 numwords1) DENVR (+ offset numwords1) ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::read-data-words-alt-def
                       )
           :induct (gacc::read-data-words-induct-with-n numwords2 offset numwords1)))
  )






;add to ram3
(defthm write-data-word-of-write-data-words-diff-better
  (implies (and (syntaxp (gacc::smaller-params denvr2 offset2
                                               denvr1 offset1))
                (<= numwords (loghead 16 (- offset1 offset2)))
                (integerp offset2)
                (integerp offset1)
                )
           (equal (gacc::write-data-word denvr1 offset1 val1 (gacc::write-data-words numwords denvr2 offset2 val2 ram))
                  (gacc::write-data-words numwords denvr2 offset2 val2 (gacc::write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (gacc::memberp-of-offset-range) (gacc::write-data-word-of-write-data-words-diff
                                                                   gacc::write-data-words-equal-rewrite))
           :use (:instance gacc::write-data-word-of-write-data-words-diff))))

;add to ram3!
(defthm gacc::write-data-word-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (gacc::write-data-word denvr offset value ram)
                  (gacc::write-data-word denvr offset 0 ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-word))))


;bzo make an alt version?
;ram3
(defthmd gacc::write-data-words-recollapse
  (implies (and (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
;(integerp val2)
                )
           (equal (gacc::write-data-word denvr offset1 val1 (gacc::write-data-word denvr offset2 val2 ram))
                  (gacc::write-data-words 2 denvr offset1 (logapp 16 val1 (ifix val2)) ram)))
  :hints (("Goal" :in-theory (e/d (gacc::write-data-words-opener)
                                  (acl2::loghead-sum-split-into-2-when-i-is-a-constant)))))

(theory-invariant (incompatible (:rewrite write-data-words-recollapse) (:rewrite gacc::write-data-words-opener)))


;(defthm DATA-WRITE-ALLOWED-when-offset-is-not-an-UNSIGNED-BYTE-P
;  (IMPLIES (NOT (UNSIGNED-BYTE-P 16 AAMP::OFFSET))
;           (equal (AAMP::DATA-WRITE-ALLOWED AAMP::DENVR AAMP::OFFSET AAMP::PMU)
;                  (AAMP::DATA-WRITE-ALLOWED AAMP::DENVR (loghead 16 AAMP::OFFSET) AAMP::PMU)))
;  :hints (("Goal" :in-theory (e/d (AAMP::DATA-WRITE-ALLOWED
;                                   GACC::MAKE-DATA-ADDR)
;                                  (AAMP::ACCESS-CHECK-BECOMES-DATA-WRITE-ALLOWED)))))




;(defthm GACC::READ-DATA-WORD-smaller-than-big-constant
;  (implies (and (syntaxp (quotep k))
;                (<= 65536 k))
;           (equal (< (GACC::READ-DATA-WORD denvr offset ram) k)
;                  t)))
;ram3
(defthm fetch-code-bytes-list-when-offset-is-not-a-usb16
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (gacc::fetch-code-bytes-list numbytes cenvr offset ram)
                  (gacc::fetch-code-bytes-list numbytes cenvr (loghead 16 offset) ram))))

;bzo gen
;bzo or should we just open up nthword?
(defthm nthword-1-of-loghead8
  (equal (gacc::nthword 1 (loghead 8 x))
         0)
  :hints (("Goal" :in-theory (enable gacc::nthword))))


(defthm nthword-1-of-ash-16
  (equal (gacc::nthword 1 (ash x 16))
         (loghead 16 x))
  :hints (("Goal" :in-theory (enable gacc::nthword))))


;scary?
(defthmd logtail-16-loghead-32
  (equal (logtail 16 (loghead 32 x))
         (gacc::nthword 1 x))
  :hints (("Goal" :expand ((gacc::nthword 1 x)))))


;gen?
(defthm gacc::write-nth-word-0-0
  (equal (gacc::write-nth-word n 0 0)
         0)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-nth-word-non-negative
  (implies (and (<= 0 word)
                (integerp value) ;bzo
                (<= 0 value))
           (<= 0 (gacc::write-nth-word n word value)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-nth-word-logapp32-hack
  (implies (and (integerp n)
                (integerp x)
                (integerp y))
           (equal (gacc::write-nth-word n word (logapp 32 x y))
                  (if (< n 2)
                      (logapp 32 (gacc::write-nth-word n word x) y)
                    (logapp 32 x (gacc::write-nth-word (+ -2 n) word y)))))
  :hints (("Goal" :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-data-words-opener-2
  (implies (and (syntaxp (and (quotep gacc::numwords)
                              (<= (cadr gacc::numwords) 20)))
                (not (zp gacc::numwords)))
           (equal (gacc::write-data-words gacc::numwords gacc::denvr gacc::offset value gacc::ram)
                  (gacc::write-data-word
                   gacc::denvr
                   gacc::offset (loghead 16 value)
                   (gacc::write-data-words
                    (+ -1 gacc::numwords)
                    gacc::denvr (+ 1 (ifix gacc::offset))
                    (logtail 16 value)
                    gacc::ram))))
  :hints
  (("Goal"
    :expand
    ((gacc::offset-range-wrap 16 gacc::offset gacc::numwords))
    :in-theory
    (e/d (gacc::write-data-words
          gacc::write-data-word
          gacc::wr-list-of-cons-one
          acl2::logext-logapp gacc::word-ad-to-byte-ads)
         nil))))

(theory-invariant (incompatible (:rewrite write-data-words-recollapse) (:rewrite gacc::write-data-words-opener-2)))

;bzo push this change back?
(in-theory (disable list::nthcdr-of-firstn))
(in-theory (enable list::firstn-of-nthcdr))

(defthmd gacc::write-data-words-opener-n
  (implies (and (integerp nwords) (> nwords 2) (< nwords 20) (integerp offset1))
           (equal (gacc::write-data-words nwords denvr offset1 val ram)
                  (gacc::write-data-words 2 denvr offset1 (loghead 32 val)
                                          (gacc::write-data-words (- nwords 2) denvr
                                                                  (loghead 16 (+ 2 offset1))
                                                                  (logtail 32 val) ram))))
  :hints (("Goal" :in-theory (e/d (gacc::write-data-words-opener-2)
                                  (gacc::write-data-words-opener)))))

;bzo gen
(defthm logapp-of-READ-DATA-WORDS
  (equal (LOGAPP 64 (GACC::READ-DATA-WORDS 5 denvr offset ram)
                 1)
         (LOGAPP 64 (GACC::READ-DATA-WORDS 4 denvr offset ram)
                 1)))

;bzo gen
(defthm nthword-2-ash-32-hack
  (equal (gacc::nthword 2 (ash x 32))
         (loghead 16 x))
  :hints (("Goal" :in-theory (e/d (gacc::nthword-rewrite) (gacc::logtail-16-loghead-32)))))

;bzo gen
(defthm nthword-3-ash-32-hack
  (equal (gacc::nthword 3 (ash x 32))
         (gacc::nthword 1 x))
  :hints (("Goal" :in-theory (e/d (gacc::nthword-rewrite) (gacc::logtail-16-loghead-32)))))

(defthm nthword-of-READ-DATA-WORDS-too-far
  (implies (and (<= numwords n)
                (<= 0 numwords)
                (integerp numwords)
                (integerp n))
           (equal (GACC::NTHWORD n (GACC::READ-DATA-WORDS numwords denvr offset ram))
                  0))
 :hints (("Goal" :in-theory (e/d (GACC::NTHWORD-rewrite
                                  acl2::loghead-identity)
                                 (gacc::LOGTAIL-16-LOGHEAD-32)))))

(defthm loghead-times-16-of-read-data-words-special
  (implies (and (integerp numwords1)
                (integerp numwords2)
                )
           (equal (loghead (+ -64 (* 16 NUMWORDS1)) (gacc::read-data-words numwords2 denvr offset ram))
                  (if (<= (+ -4 NUMWORDS1) numwords2)
                      (gacc::read-data-words (+ -4 NUMWORDS1) denvr offset ram)
                    (gacc::read-data-words numwords2 denvr offset ram))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable loghead-times-16-of-read-data-words)
           :use (:instance loghead-times-16-of-read-data-words (numwords1 (+ -4 NUMWORDS1)))))
  )

;bzo gen
(defthm hack1
  (implies (integerp numwords)
           (equal (loghead (+ -64 (* 16 numwords)) (gacc::wintlist byte-list))
                  (gacc::wintlist (firstn (+ -8 (* 2 numwords)) byte-list))))
  :hints (("Goal" :in-theory (disable gacc::loghead-times-8-of-wintlist)
           :use (:instance gacc::loghead-times-8-of-wintlist
                           (gacc::byte-list byte-list)
                           (gacc::numbytes (+ -8 (* 2 numwords)))))
          ))

(defthm logtail-times-16-of-read-data-words-hack
  (implies  (and (integerp numwords1)
                 (integerp numwords2)
                 (<= 0 numwords2)
                 (<= 4 numwords1)
                 (integerp offset)
                 )
            (equal (LOGTAIL (+ -64 (* 16 NUMWORDS1)) (GACC::READ-DATA-WORDS NUMWORDS2 DENVR offset ram))
                   (GACC::READ-DATA-WORDS (+ 4 (- NUMWORDS2 numwords1)) DENVR (+ -4 offset numwords1) ram)))
  :hints (("Goal" :use (:instance gacc::logtail-times-16-of-read-data-words
                                  (numwords1 (+ -4 numwords1))
                                  )

           :in-theory (disable gacc::logtail-times-16-of-read-data-words)))

  )

;bzo remove the -hack version?
;matches better
(defthm logtail-times-16-of-read-data-words-alt
  (implies (and (integerp (/ n 16))
;                (integerp n)
                (<= 0 n) ;drop?
                (integerp numwords2)
;                (<= 0 numwords1)
                (integerp offset))
           (equal (logtail n (gacc::read-data-words numwords2 denvr offset ram))
                  (gacc::read-data-words (- numwords2 (/ n 16))
                                         denvr (+ offset (/ n 16))
                                         ram)))
  :hints (("Goal" :in-theory (disable logtail-times-16-of-read-data-words)
           :use (:instance logtail-times-16-of-read-data-words (numwords1 (/ n 16))))))

(defthm consp-of-cdr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (consp (cdr (gacc::addresses-of-data-words numwords denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cdr-of-cdr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords)
                (integerp offset) ;this may cause problems
                )
           (equal (cdr (cdr (gacc::addresses-of-data-words numwords denvr offset)))
                  (gacc::addresses-of-data-words (+ -1 numwords) denvr (acl2::loghead 16 (+ 1 offset)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm car-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (equal (car (gacc::addresses-of-data-words numwords denvr offset))
                  (car (gacc::addresses-of-data-word denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cadr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (equal (cadr (gacc::addresses-of-data-words numwords denvr offset))
                  (cadr (gacc::addresses-of-data-word denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm car-of-addresses-of-data-word
  (equal (car (gacc::addresses-of-data-word denvr offset))
         (acl2::logapp 1 0 (acl2::logapp 16 offset (acl2::loghead 15 denvr)))
         )
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cadr-of-addresses-of-data-word
  (equal (cadr (gacc::addresses-of-data-word denvr offset))
         (acl2::logapp 1 1 (acl2::logapp 16 offset (acl2::loghead 15 denvr)))
         )
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(in-theory (disable gacc::cadr-when-offset-rangep)) ;bzo move up?

(defthm consp-of-cdr-of-addresses-of-data-word
  (consp (cdr (gacc::addresses-of-data-word denvr offset)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm cdr-of-cdr-of-addresses-of-data-word
  (equal (cdr (cdr (gacc::addresses-of-data-word denvr offset)))
         nil)
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm addresses-of-data-words-of-1
  (equal (gacc::addresses-of-data-words 1 denvr offset)
         (gacc::addresses-of-data-word denvr offset))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))


;disable?
;gen?
;add backchain limit?
(defthmd loghead-15-not-equal-hack
  (implies (not (acl2::unsigned-byte-p 15 x))
           (not (equal x (acl2::loghead 15 y)))))

(defthm memberp-of-addresses-of-data-words
  (implies (and (integerp offset)
                (integerp numwords))
           (equal (memberp ad (gacc::addresses-of-data-words numwords denvr offset))
                  (and (acl2::unsigned-byte-p 32 ad)
                       (equal (acl2::logtail 17 ad) (acl2::loghead 15 denvr))
                       (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad))
                                               offset))
                          numwords))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::addresses-of-data-words
                              loghead-15-not-equal-hack
                              gacc::memberp-of-offset-range))))

(defthm memberp-of-addresses-of-data-word
  (implies (integerp offset)
           (equal (memberp ad (gacc::addresses-of-data-word denvr offset))
                  (and (acl2::unsigned-byte-p 32 ad)
                       (equal (acl2::logtail 17 ad) (acl2::loghead 15 denvr))
                       (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad)) offset)) 1)
                       )))
  :hints (("Goal" :use (:instance memberp-of-addresses-of-data-words
                                  (numwords 1))
           :in-theory (disable memberp-of-addresses-of-data-words))))

(defthm addresses-of-data-word-simp-leading-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset))
           (equal (gacc::addresses-of-data-word denvr (+ k offset))
                  (gacc::addresses-of-data-word denvr (+ (acl2::loghead 16 k) offset)))))

(defthm word-ads-to-byte-ads-of-fix
  (equal (gacc::word-ads-to-byte-ads (list::fix ads))
         (gacc::word-ads-to-byte-ads ads))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-remove-1
  (implies (and (gacc::unsigned-byte-p-list 31 ads)
                (acl2::unsigned-byte-p 31 x))
           (equal (gacc::word-ads-to-byte-ads (bag::remove-1 x ads))
                  (bag::remove-bag (gacc::word-ad-to-byte-ads x)
                                   (gacc::word-ads-to-byte-ads ads))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads
                              WORD-AD-TO-BYTE-ADS
                              bag::remove-1))))

(defthm addresses-of-data-word-of-loghead-around-offset
  (equal (gacc::addresses-of-data-word denvr (acl2::loghead 16 offset))
         (gacc::addresses-of-data-word denvr offset))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm len-of-addresses-of-data-words
  (equal (len (gacc::addresses-of-data-words numwords denvr offset))
         (* 2 (nfix numwords)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(local
 (defun 2-list-induct (l1 l2)
   (if (endp l1)
       (list l1 l2)
     (2-list-induct (cdr l1) (bag::remove-1 (car l1) l2)))))

;make this and the forward rule local?
(defthm gacc::subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads-back
  (implies (and (bag::subbagp (gacc::word-ads-to-byte-ads ads1)
                              (gacc::word-ads-to-byte-ads ads2))
                (gacc::unsigned-byte-p-list 31 ads1)
                (gacc::unsigned-byte-p-list 31 ads2))
           (bag::subbagp ads1 ads2))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
               :induct (2-list-induct ads1 ads2)
    :in-theory (e/d (len gacc::word-ads-to-byte-ads
                         WORD-AD-TO-BYTE-ADS
                         bag::subbagp-of-cons)
                    (list::len-cdr-equal-len-cdr-rewrite
                     BAG::SUBBAG-BY-MULTIPLICITY
                     ;GACC::WORD-AD-TO-BYTE-ADS

                     )))))

;bzo improve GACC::SUBBAGP-OF-WORD-ADS-TO-BYTE-ADS-AND-WORD-ADS-TO-BYTE-ADS to not use integer-listp but rather the better one
(defthm gacc::subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads-both
  (implies (and (gacc::unsigned-byte-p-list 31 ads1)
                (gacc::unsigned-byte-p-list 31 ads2)
                (true-listp ads1) ;yuck
                (true-listp ads2) ;yuck
                )
           (equal (bag::subbagp (gacc::word-ads-to-byte-ads ads1)
                                (gacc::word-ads-to-byte-ads ads2))
                  (bag::subbagp ads1 ads2))))



;make GACC::UNIQUE-OF-OFFSET-RANGE-WRAP into an equal rule?

;(set-default-hints nil)

;bzo gen?
;bzo prove single word versions
(defthm subbagp-of-addresses-of-data-words-and-addresses-of-data-words
  (implies (and (natp numwords1)
                (natp numwords2)
                (< 0 numwords1)
                (<= NUMWORDS2 (EXPT 2 16))
                (<= NUMWORDS1 (EXPT 2 16))
                (ACL2::UNSIGNED-BYTE-P 16 NUMWORDS2)
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-words numwords1 denvr offset1)
                                (gacc::addresses-of-data-words numwords2 denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) numwords2)
                       (<= (+ numwords1 (acl2::loghead 16 (- offset1 offset2))) numwords2))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words
                                     GACC::SUBBAGP-OF-TWO-OFFSET-RANGE-wraps))))

(defthm subbagp-of-addresses-of-data-words-and-addresses-of-data-word
  (implies (and (natp numwords1)
                (< 0 numwords1)
                (<= NUMWORDS1 (EXPT 2 16))
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-words numwords1 denvr offset1)
                                (gacc::addresses-of-data-word denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) 1)
                       (<= (+ numwords1 (acl2::loghead 16 (- offset1 offset2))) 1))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords2 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))

(defthm subbagp-of-addresses-of-data-word-and-addresses-of-data-words
  (implies (and (natp numwords2)
                (<= NUMWORDS2 (EXPT 2 16))
                (ACL2::UNSIGNED-BYTE-P 16 NUMWORDS2)
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-word denvr offset1)
                                (gacc::addresses-of-data-words numwords2 denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) numwords2)
                       (<= (+ 1 (acl2::loghead 16 (- offset1 offset2))) numwords2))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords1 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))

(defthm subbagp-of-addresses-of-data-word-and-addresses-of-data-word
  (implies (and (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-word denvr offset1)
                                (gacc::addresses-of-data-word denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) 1)
                       (<= (+ 1 (acl2::loghead 16 (- offset1 offset2))) 1))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords1 1) (numwords2 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))


;one is even and the other odd
(defthm cadr-of-addresses-of-data-word-not-equal-car-of-addresses-of-data-word
  (not (equal (cadr (gacc::addresses-of-data-word denvr1 offset1))
              (car (gacc::addresses-of-data-word denvr2 offset2))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-words-not-equal-car-of-addresses-of-data-word
  (implies (and (integerp numwords)
                (< 0 numwords))
           (not (equal (cadr (gacc::addresses-of-data-words numwords denvr1 offset1))
                       (car (gacc::addresses-of-data-word denvr2 offset2)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CADR-OF-ADDRESSES-OF-DATA-WORDS))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-word-not-equal-car-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (not (equal (cadr (gacc::addresses-of-data-word denvr2 offset2))
                       (car (gacc::addresses-of-data-words numwords denvr1 offset1)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CAR-OF-ADDRESSES-OF-DATA-WORDS))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-words-not-equal-car-of-addresses-of-data-words
  (implies (and (integerp numwords1)
                (< 0 numwords1)
                (integerp numwords2)
                (< 0 numwords2))
           (not (equal (cadr (gacc::addresses-of-data-words numwords2 denvr2 offset2))
                       (car (gacc::addresses-of-data-words numwords1 denvr1 offset1)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CAR-OF-ADDRESSES-OF-DATA-WORDS CADR-OF-ADDRESSES-OF-DATA-WORDS))))

(defthm rd-of-write-data-word-diff-denvr
  (implies (and (not (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad)))
                (integerp offset) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable RD-OF-WR-LIST-DIFF
                                     gacc::write-data-word
                                     gacc::memberp-of-word-ad-to-byte-ads))))

(defthm rd-of-write-data-word-diff-offset
  (implies (and (not (equal (acl2::loghead 16 offset) (acl2::loghead 16 (acl2::logtail 1 ad))))
                (integerp offset) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable RD-OF-WR-LIST-DIFF
                                     gacc::write-data-word
                                     gacc::memberp-of-word-ad-to-byte-ads))))

(defthm rd-of-write-data-word-same
  (implies (and (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad))
                (equal (acl2::loghead 16 offset) (acl2::loghead 16 (acl2::logtail 1 ad)))
                (integerp offset) ;drop?
                (ACL2::UNSIGNED-BYTE-P '32 AD) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (acl2::loghead 8 (acl2::logtail
                                    (* 8 (acl2::logcar ad)) ;if ad is even, take word 0, else take word 1
                                    value))
                  ))
  :hints (("Goal" :in-theory (enable gacc::write-data-word
                                     WORD-AD-TO-BYTE-ADS
                                     GACC::ADDRESSES-OF-DATA-WORD
                                     gacc::wr-list-of-cons-one
                                     ACL2::EQUAL-LOGAPP-X-Y-Z))))

(defthm rd-of-write-data-words-diff-denvr
  (implies (and (not (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad)))
                (integerp offset) ;drop?
                (integerp numwords)
                )
           (equal (gacc::rd ad (gacc::write-data-words numwords denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-words
                                     RD-OF-WR-LIST-DIFF))))

(defthm rd-of-write-data-words-diff-offset
  (implies (and (not (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad)) offset)) numwords))
                (integerp offset) ;drop?
                (integerp numwords)
;                (integerp ad) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-words numwords denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::write-data-words
                              RD-OF-WR-LIST-DIFF
                              MEMBERP-OF-OFFSET-RANGE))))

(defthm find-index-of-word-ads-to-byte-ads
  (implies (and (integerp ad)
                (acl2::integer-listp word-ads)
                (list::memberp (acl2::logcdr ad) word-ads))
           (equal (list::find-index ad (gacc::word-ads-to-byte-ads word-ads))
                  (+ (acl2::logcar ad)
                     (* 2 (list::find-index (acl2::logcdr ad) word-ads)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads
                              WORD-AD-TO-BYTE-ADS
                              (:definition list::find-index)
                              acl2::equal-logapp-x-y-z
                              MEMBERP-OF-OFFSET-RANGE
                              LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR
                              ))))


;;; RBK: Additions begin here.  Integrate these with the rest of the book,
;;; and put them in the proper palces.

(defthm addresses-of-data-word-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (GACC::ADDRESSES-OF-DATA-WORD cenvr (+ k offset))
                  (GACC::ADDRESSES-OF-DATA-WORD cenvr (+ (acl2::loghead 16 k) offset)))))

(defthm addresses-of-data-words-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n cenvr (+ k offset))
                  (GACC::ADDRESSES-OF-DATA-WORDS n cenvr (+ (acl2::loghead 16 k) offset)))))

(defthm fetch-code-byte-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (gacc::fetch-code-byte cenvr (+ k offset) ram)
                  (gacc::fetch-code-byte cenvr (+ (acl2::loghead 16 k) offset) ram))))

(defthm addresses-of-data-words-loghead-normalization
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (acl2::LOGHEAD 16 x))
                  (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 x)))

(defthm addresses-of-data-words-loghead-normalization-a
  (implies (and (integerp x)
                (integerp y))
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (+ y (acl2::LOGHEAD 16 x)))
                  (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (+ y x))))
  :hints (("Goal" :use (:instance addresses-of-data-words-loghead-normalization
                                  (x (+ y (acl2::LOGHEAD 16 x))))
                  :in-theory (disable addresses-of-data-words-loghead-normalization
                                      GACC::OFFSET-RANGE-WRAP-OF-LOGHEAD))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-3-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 3 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 3 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-3-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 3)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-2-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 2 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 2 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-2-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 2 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 2 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 2)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-1-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 1 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 1 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-1-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 1 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 1 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 1)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN))))

;;; RBK: Generalize?
(defthm size-of-fetch-code-bytes-3
  (acl2::unsigned-byte-p 31 (GACC::FETCH-CODE-BYTES 3 X0
                                              x
                                              X23)))

;;; RBK: Generalize?
(defthm size-of-fetch-code-bytes-3-a
  (acl2::unsigned-byte-p 31 (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                                   x
                                                   X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 3)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
           :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))
