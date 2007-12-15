;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.



;; utf8.lisp
;;
;; We introduce functions to process UTF-8 encoding.
;;
;; There is a fair amount of description in the Unicode Specification about the
;; UTF-8 encoding form.  Here are the parts of the 4.0.1 specification which
;; deal with UTF-8 directly.  This is all really quite straightforward.
;;
;;    D36: UTF-8 Encoding Form: The Unicode encoding form which assigns each
;;    Unicode scalar value to an unsigned byte sequence of one to four bytes in
;;    length, as specified in Table 3-5.
;;
;;      1.  In UTF-8, the code point sequence <004D 0430 4E8C 10302> is
;;      represented as <4D D0 B0 D4 BA 8C F0 90 8C 82>, where <4D> corresponds to
;;      U+004D, <D0 B0> corresponds to U+0430, <E4 BA 8C> corresponds to U+4E8C, 
;;      and <F0 90 8C 82> corresponds to U+10302.
;;
;;      2.  Any UTF-8 byte sequence that does not match the patterns listed in
;;      Table 3-6 is ill formed.
;;
;;      3.  Before the Unicode Standard, Version 3.1, the problematic "non-
;;      shortest form" byte sequences in UTF-8 were those where BMP characters
;;      could be represented in more than one way.  These sequences are ill
;;      formed, because they are not allowed by Table 3-6.
;;
;;      4.  Because surrogate code points are not Unicode scalar values, any
;;      UTF-8 byte sequence that would otherwise map to code points D800..DFFF is
;;      ill formed.
;;
;;    Table 3-5 Specifies the bit distribution for the UTF-8 encoding form,
;;    showing the ranges of Unicode scalar values corresponding to one-, two-,
;;    three-, and four-byte sequences.
;;
;;                     Table 3-5.  UTF-8 Bit Distribution
;;
;;     Scalar Value                1st Byte  2nd Byte  3rd Byte  4th Byte
;;     00000000 0xxxxxxx           0xxxxxxx
;;     00000yyy yyxxxxxx           110yyyyy  10xxxxxx
;;     zzzzyyyy yyxxxxxx           1110zzzz  10yyyyyy  10xxxxxx
;;     000uuuuu zzzzyyyy yyxxxxx   11110uuu  10uuzzzz  10yyyyyy  10xxxxxx
;;
;;
;;    Table 3-6 lists all of the byte sequences that are well formed in UTF-8.
;;    A range of byte values such as A0..BF indicates that any byte from A0 to 
;;    BF, inclusive, is well formed in that position.  Any byte value outside 
;;    the ranges listed is ill formed.  For example:
;;
;;      1.  The byte sequence <C0 AF> is ill fomred because C0 is not well formed
;;      in the "1st Byte" column.
;;
;;      2.  The byte sequence <E0 9F 80> is ill formed, because in the row where
;;      E0 is well formed as a first byte, 9F is not well formed as a second
;;      byte.
;;
;;      3.  The byte sequence <F4 80 83 92> is well formed, because every byte in
;;      that sequence matches a byte range in the row of the table (the last
;;      row).
;;
;;                Table 3-6:  Well-Formed UTF-8 Byte Sequences
;;
;;     Code Points          1st Byte    2nd Byte    3rd Byte    4th Byte
;;     U+0000..U+007F       00..7F
;;     U+0080..U+07FF       C2..DF      80..BF
;;     U+0800..U+0FFF       E0          A0..BF      80..BF
;;     U+1000..U+CFFF       E1..EC      80..BF      80..BF
;;     U+D000..U+D7FF       ED          80..9F      80..BF
;;     U+E000..U+FFFF       EE..EF      80..BF      80..BF
;;     U+10000..U+3FFFF     F0          90..BF      80..BF      80..BF
;;     U+40000..U+FFFFF     F1..F3      80..BF      80..BF      80..BF
;;     U+100000..U+10FFFF   F4          80..8F      80..BF      80..BF
;;
;;    As a consequence of the well formedness conditions specified in Table 
;;    3-6, the following byte values are disallowed in UTF-8: C0-C1, F5-FF.
;;
;;    D39: UTF-8 Encoding Scheme: The Unicode encoding scheme that serializes
;;    a UTF-8 code unit sequence in exactly the same order as the code unit 
;;    sequence itself.
;;
;;      1.  In the UTF-8 encoding scheme, the UTF-8 code unit sequence <4D D0 B0
;;      E4 BA 8C F0 90 8C 82> is serialized as <4D D0 B0 E4 BA 8C F0 90 8C 82>
;;
;;      2.  Because the UTF-8 encoding form already deals in ordered byte
;;      sequences, the UTF-8 encoding scheme is trivial.  The byre ordering is
;;      already obvious and completely defined by the UTF-8 code unit sequence
;;      itself.  The UTF-8 encoding scheme is defined merely for completeness of
;;      the Unicode character encoding model.
;;
;;      3.  While there is no need for a byte order signature when using UTF-8,
;;      there are occasions when processes convert UTF-16 or UTF-32 data
;;      containing a byte order mark into UTF-8.  When represented in UTF-8, the
;;      byte order mark turns into the byte sequence <EF BB BF>.  Its usage at
;;      the beginning of a UTF-8 data stream is neither required nor recommended
;;      by the Unicode Standard, but its presence does not affect conformance to
;;      the UTF-8 encoding scheme.  Identification of the <EF BB BF> byte
;;      sequence at the beginning of a data stream can, however, be taken as a
;;      near certain indication that the data stream is using the UTF-8 encoding
;;      scheme.

(in-package "ACL2")
(include-book "uchar")
(include-book "utf8-table35")
(include-book "utf8-table36")
(set-verify-guards-eagerness 2)
(set-state-ok t)





(in-theory (disable nthcdr take))

(include-book "acl2-basics")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm nat-listp-of-cdr-when-nat-listp
  (implies (nat-listp x)
           (nat-listp (cdr x))))

;; (defthm nthcdr-of-cons
;;   (equal (nthcdr n (cons a x))
;;          (if (and (integerp n)
;;                   (< 0 n))
;;              (nthcdr (+ -1 n) x)
;;            (cons a x)))
;;   :hints(("Goal" :in-theory (enable nthcdr))))

(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (if (natp n)
             (max 0 (- (len l) n))
           (len l)))
  :hints (("Goal" 
           :in-theory (enable nthcdr)
           :induct (nthcdr n l))))

(defthm list-fix-of-nthcdr
  (equal (list-fix (nthcdr n l))
         (nthcdr n (list-fix l)))
  :hints(("Goal" :in-theory (enable nthcdr))))


(defthm partition-list-identity
  (implies (and (nat-listp sizes)
                (equal (sum-list sizes) (len x)))
           (equal (flatten-cons-list 
                   (partition-list sizes x))
                  (list-fix x)))
  :hints(("Goal" 
          :induct (partition-list sizes x)
          :in-theory (enable partition-list))))










;; I first claim (and prove) that the Table 3-5 1st Byte entries are distinct.
;; That is, given any x as input, x either matches none of the acceptable 1st
;; Byte patterns, or it matches exactly one of them.  Because of this, we can
;; use the 1st Byte to determine how many bytes we need to read total.

(defthm utf8-table35-byte-1/x-distinct
  (and (implies (utf8-table35-byte-1/1? x)
                (and (not (utf8-table35-byte-1/2? x))
                     (not (utf8-table35-byte-1/3? x))
                     (not (utf8-table35-byte-1/4? x))
                     (not (utf8-table35-trailing-byte? x))))
       (implies (utf8-table35-byte-1/2? x)
                (and (not (utf8-table35-byte-1/1? x))
                     (not (utf8-table35-byte-1/3? x))
                     (not (utf8-table35-byte-1/4? x))
                     (not (utf8-table35-trailing-byte? x))))
       (implies (utf8-table35-byte-1/3? x)
                (and (not (utf8-table35-byte-1/1? x))
                     (not (utf8-table35-byte-1/2? x))
                     (not (utf8-table35-byte-1/4? x))
                     (not (utf8-table35-trailing-byte? x))))
       (implies (utf8-table35-byte-1/4? x)
                (and (not (utf8-table35-byte-1/1? x))
                     (not (utf8-table35-byte-1/2? x))
                     (not (utf8-table35-byte-1/3? x))
                     (not (utf8-table35-trailing-byte? x))))
       (implies (utf8-table35-trailing-byte? x)
                (and (not (utf8-table35-byte-1/1? x))
                     (not (utf8-table35-byte-1/2? x))
                     (not (utf8-table35-byte-1/3? x))
                     (not (utf8-table35-byte-1/4? x)))))
  :rule-classes nil
  :hints(("Goal" :in-theory (enable utf8-table35-byte-1/1?
                                    utf8-table35-byte-1/2?
                                    utf8-table35-byte-1/3?
                                    utf8-table35-byte-1/4?
                                    utf8-table35-trailing-byte?))))

;; Since the first bytes are all distinct, we can simply examine the first 
;; byte of a purported UTF-8 sequence in order to determine how long the
;; sequence will have to be in order to be acceptable.

(defun utf8-table35-expected-length (x)
  "Given that x is allegedly the first byte of a UTF-8 sequence, use Table 3-5
   to determine how long this sequence is expected to be."
  (declare (type (unsigned-byte 8) x))
  (cond ((utf8-table35-byte-1/1? x) 1)
        ((utf8-table35-byte-1/2? x) 2)
        ((utf8-table35-byte-1/3? x) 3)
        ((utf8-table35-byte-1/4? x) 4)
        (t nil)))

;; As a result, we can wee that UTF-8 byte sequences can only be acceptable
;; under Tables 3-5 and 3-6 if they have the length which is predicted by
;; utf8-table35-expected-length.

(defthm utf8-table35-ok?-when-not-expected-length
  (implies (not (equal (utf8-table35-expected-length (first x))
                       (len x)))
           (not (utf8-table35-ok? cp x)))
  :hints(("Goal" :in-theory (enable utf8-table35-ok?
                                    utf8-table35-row-1?
                                    utf8-table35-row-2?
                                    utf8-table35-row-3?
                                    utf8-table35-row-4?
                                    utf8-table35-byte-1/1?
                                    utf8-table35-byte-1/2?
                                    utf8-table35-byte-1/3?
                                    utf8-table35-byte-1/4?
                                    utf8-table35-trailing-byte?
                                    utf8-table35-expected-length))))

(defthm utf8-table35-expected-length-when-utf8-table35-ok?
  (implies (utf8-table35-ok? cp x)
           (equal (utf8-table35-expected-length (first x))
                  (len x))))

(defthm utf8-table36-okp-when-not-expected-length
  (implies (not (equal (utf8-table35-expected-length (first x))
                       (len x)))
           (not (utf8-table36-ok? cp x)))
  :hints(("Goal" :in-theory (enable utf8-table36-ok?
                                    utf8-table35-byte-1/1?
                                    utf8-table35-byte-1/2?
                                    utf8-table35-byte-1/3?
                                    utf8-table35-byte-1/4?
                                    utf8-table35-trailing-byte?
                                    utf8-table36-rows
                                    utf8-table36-codepoint-1?
                                    utf8-table36-codepoint-2?
                                    utf8-table36-codepoint-3?
                                    utf8-table36-codepoint-4?
                                    utf8-table36-codepoint-5?
                                    utf8-table36-codepoint-6?
                                    utf8-table36-codepoint-7?
                                    utf8-table36-codepoint-8?
                                    utf8-table36-codepoint-9?
                                    utf8-table36-bytes-1?
                                    utf8-table36-bytes-2?
                                    utf8-table36-bytes-3?
                                    utf8-table36-bytes-4?
                                    utf8-table36-bytes-5?
                                    utf8-table36-bytes-6?
                                    utf8-table36-bytes-7?
                                    utf8-table36-bytes-8?
                                    utf8-table36-bytes-9?
                                    utf8-table35-expected-length))))

(defthm utf8-table35-expected-length-when-utf8-table36-ok?
  (implies (utf8-table36-ok? cp x)
           (equal (utf8-table35-expected-length (first x))
                  (len x))))


;; Suppose we have a list of bytes which are a UTF8 encoded string or file.  We
;; want to convert these bytes into a list of atomic code points.  The most
;; straightforward thing to do would be the following:
;;
;;   1. Consider the bytes which make up the first codepoint.  Extract
;;      the codepoint they represent.
;;
;;   2. Repeat 























(defun read-utf8-codepoint (channel state)
  "Read the next codepoint from a UTF-8 encoded file."
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))))
  (mv-let (x1 state) (read-byte$ channel state)
    (if (eq x1 nil)
        (mv nil state)
      (case (utf8-table35-expected-length x1)
        (1 (mv x1 state))
        (2 (mv-let (x2 state) (read-byte$ channel state)
            (mv (if (and x2 (utf8-combine2-guard x1 x2))
                    (utf8-combine2 x1 x2)
                  'fail)
                state)))
        (3 (mv-let (x2 state) (read-byte$ channel state)
            (mv-let (x3 state) (read-byte$ channel state)
             (mv (if (and x2 x3 (utf8-combine3-guard x1 x2 x3))
                     (utf8-combine3 x1 x2 x3)
                   'fail)
                 state))))
        (4 (mv-let (x2 state) (read-byte$ channel state)
            (mv-let (x3 state) (read-byte$ channel state)
             (mv-let (x4 state) (read-byte$ channel state)
              (mv (if (and x2 x3 x4 (utf8-combine4-guard x1 x2 x3 x4))
                      (utf8-combine4 x1 x2 x3 x4) 
                    'fail)
                  state)))))
        (otherwise (mv 'fail state))))))

(defun read-utf8-codepoints (n channel state acc)
  "Read the next n codepoints from a UTF-8 encoded file."
  (declare (xargs :guard (and (natp n)
                              (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state)
                              (true-listp acc))))
  (if (zp n)
      (mv (reverse acc) state)
    (mv-let (codepoint state) 
            (read-utf8-codepoint channel state)
            (if (or (eq codepoint nil)
                    (eq codepoint 'fail))
                (mv (reverse acc) state)
              (read-utf8-codepoints (1- n) channel state 
                                    (cons codepoint acc))))))

(defun read-utf8-file (n filename state)
  (declare (xargs :mode :program))
  (mv-let (channel state)
          (open-input-channel filename :byte state)
          (mv-let (data state)
                  (read-utf8-codepoints n channel state nil)
                  (let ((state (close-input-channel channel state)))
                    (mv data state)))))









#|





(defun read-utf8-char (channel state)
  "Read the next codepoint from a UTF-8 encoded file."
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))))
  (mv-let (x1 state) 
          (read-byte$ channel state)
          (cond ((eq x1 nil)
                 (mv nil state))
                
                ((utf8-table35-expected-length 

              
    (cond ((eq x1 nil)
           (mv nil state))

          ((< (the-fixnum x1) #b01111111)
           (mv x1 state))
          
          ((= (logand (the-fixnum x1) #b11100000) #b11000000)
           (mv-let (x2 state) 
                   (read-byte$ channel state)
            (if (eq x2 nil)
                (mv 'fail state)
              (mv (mbe :logic (read-utf8-combine2 x1 x2)
                       :exec (let ((000yyyyy (logand (the-fixnum x1) #b00011111))
                                   (00xxxxxx (logand (the-fixnum x2) #b00111111)))
                               (logior (the-fixnum (ash (the-fixnum 000yyyyy) 6))
                                       (the-fixnum 00xxxxxx))))
                  state))))
          
          ((= (logand (the-fixnum x1) #b11110000) #b11100000)
           (mv-let (x2 state) (read-byte$ channel state)
            (mv-let (x3 state) (read-byte$ channel state)
             (if (or (eq x2 nil) (eq x3 nil))
                 (mv 'fail state)
               (mv (mbe :logic (read-utf8-combine3 x1 x2 x3)
                        :exec (let ((0000zzzz (logand (the-fixnum x1) #b00001111))
                                    (00yyyyyy (logand (the-fixnum x2) #b00111111))
                                    (00xxxxxx (logand (the-fixnum x3) #b00111111)))
                                (logior (the-fixnum (ash (the-fixnum 0000zzzz) 12))
                                        (the-fixnum (ash (the-fixnum 00yyyyyy) 6))
                                        (the-fixnum 00xxxxxx))))
                   state)))))

          ((= (logand (the-fixnum x1) #b11111000) #b11110000)
           (mv-let (x2 state) (read-byte$ channel state)
            (mv-let (x3 state) (read-byte$ channel state)
             (mv-let (x4 state) (read-byte$ channel state)
              (if (or (eq x2 nil) (eq x3 nil) (eq x4 nil))
                  (mv 'fail state)
                (mv (mbe :logic (read-utf8-combine4 x1 x2 x3 x4)
                         :exec (let ((00000uuu (logand (the-fixnum x1) #b00000111))
                                     (00uuzzzz (logand (the-fixnum x2) #b00111111))
                                     (00yyyyyy (logand (the-fixnum x3) #b00111111))
                                     (00xxxxxx (logand (the-fixnum x4) #b00111111)))
                                 (logior (the-fixnum (ash (the-fixnum 00000uuu) 18))
                                         (the-fixnum (ash (the-fixnum 00uuzzzz) 12))
                                         (the-fixnum (ash (the-fixnum 00yyyyyy) 6))
                                         (the-fixnum 00xxxxxx))))
                    state))))))

          (t (mv 'fail state)))))




          





(defthm read-utf8-state
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (state-p1 (mv-nth 1 (read-utf8-char channel state)))))

(defthm read-utf8-open-input-channel
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (open-input-channel-p1 channel 
                                  :byte 
                                  (mv-nth 1 (read-utf8-char channel state)))))

(i-am-here)

;; first we would like to show that reading from a utf8 stream gives us a
;; unicode scalar value

(defthm read-utf8-uchar
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state))
                (car (read-utf8-char channel state))
                (not (equal (car (read-utf8-char channel state)) 'fail)))
           (uchar? (car (read-utf8-char channel state)))))

;; we would also like to show that this value is not in any of the forbidden
;; ranges, as indicated by the table.  actually, a good way to do this might
;; be to simply do exhaustive testing.  that is, write something like
;; combine16u and use mbe to put its definition into the logical definition
;; for read-utf8-char.  then, we can exhaustively show that as long as you 
;; feed it good values, it never produces a bad output.
;;
;; right now, i think this conjecture is false, and we will have to add some
;; extra cases to discard the bad ranges and so forth.








(encapsulate nil

 (local (in-theory (disable read-utf8-combine2)))

 (local (defun test-x2 (x1 i)
   (declare (type (unsigned-byte 8) x1)
            (type (unsigned-byte 8) i))
   (and (uchar? (read-utf8-combine2 x1 i))
        (or (zp i)
            (test-x2 x1 (1- i))))))

 (local (defun test-x1 (i)
   (declare (type (unsigned-byte 8) i))
   (and (test-x2 i 255)
        (or (zp i)
            (test-x1 (1- i))))))
           
 (local (defthm test-x2-lemma
          (implies (and (test-x2 x1 x2)
                        (integerp x2)
                        (integerp j) 
                        (<= 0 j) 
                        (<= j x2))
                   (uchar? (read-utf8-combine2 x1 j)))))

 (local (defthm test-x1-lemma
          (implies (and (test-x1 x1) 
                        (integerp x1)
                        (integerp i) 
                        (<= 0 i) 
                        (<= i x1)
                        (integerp j) 
                        (<= 0 j) 
                        (<= j 255))
                   (uchar? (read-utf8-combine2 i j)))
          :hints(("Subgoal *1/1"
                  :use (:instance test-x2-lemma
                                  (x1 i)
                                  (x2 255)
                                  (j j))))))

 (defthm read-utf8-combine2-uchar
   (implies (and (force (unsigned-byte-p 8 x1))
                 (force (unsigned-byte-p 8 x2)))
            (uchar? (read-utf8-combine2 x1 x2)))
   :hints(("Goal" :in-theory (enable unsigned-byte-p)
           :use (:instance test-x1-lemma 
                           (x1 255)
                           (i x1)
                           (j x2)))))
)



       
           



(= (logand (the-fixnum x1) #b11110000) #b11100000)

(local (defun test-x3 (x1 x2 i)
         (declare (type (unsigned-byte 8) x1)
                  (type (unsigned-byte 8) x2)
                  (type (unsigned-byte 8) i))
         (and (or (implies (and (= (logand x1 #b11110000) #b11100000)
                                (= (logand x2 #b11000000) #b10000000)
                                (= (logand i #b11000000) #b10000000))
                           (uchar? (read-utf8-combine3 x1 x2 i)))
                  (cw "test-x3 fails for ~x0 ~x1 ~x2.~%" x1 x2 i))
              (or (zp i)
                  (test-x3 x1 x2 (1- i))))))

(local (defun test-x2 (x1 i)
         (declare (type (unsigned-byte 8) x1)
                  (type (unsigned-byte 8) i))
         (and (test-x3 x1 i 255)
              (or (zp i)
                  (test-x2 x1 (1- i))))))

(local (defun test-x1 (i)
         (declare (type (unsigned-byte 8) i))
         (and (test-x2 i 255)
              (or (zp i)
                  (test-x1 (1- i))))))

           



(i-am-here)

(set-state-ok t)































; =============================================================================
;
;   D43: UTF-32BE Encoding Scheme: The Unicode encoding scheme that serializes
;   a UTF-32 code sequence as a byte sequence in big-endian format.
;
;     - In UTF-32BE, the UTF-32 code sequence <0000004D, 00000430, 00004E8C,
;       00010302> is serialized as <00 00 00 4D 00 00 04 30 00 00 4E 8C 00 01
;       03 02>
;
;     - In UTF-32BE, an initial byte sequence <00 00 FE FF> is interpreted as
;       U+FEFF, ZERO WIDTH NO-BREAK SPACE.
;
; =============================================================================

; Well, this is all very simple.  All we have to do is read four-byte big
; endian quantities from the stream.

(defun read-utf32be-char (channel state) 
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))))
  (mv-let (uchar state)
          (read-bytes$ channel :bytes 4 :signed nil :end big)
          (mv (cond ((eq uchar nil) nil)
                    ((eq uchar 'fail) 'fail)
                    ((uchar? uchar) uchar)
                    (t 'fail))
              state)))







(defun utf-channel? (x)
  (and (listn x 2)
       (or (eq (first x) 'UTF-32BE)
           (eq (first x) 'UTF-32LE)
           (eq (first x) 'UTF-16BE)
           (eq (first x) 'UTF-16LE)
           (eq (first x) 'UTF-8))
       (symbolp (second x))))



(defun read-utf-channel (utfc state)
  (declare (xargs :guard (and (utf-channel? utfc)
                              (state-p state)
                              (open-input-channel-p (cadr utfc) :byte state))))
  (let ((type (car utfc))
        (channel (cadr utfc)))
    (case type
      ('UTF-8    (read-utf-8-char channel state))
      ('UTF-16BE (read-utf-16be-char channel state))
      ('UTF-16LE (read-utf-16le-char channel state))
      ('UTF-32BE (read-utf-32be-char channel state))
      (t (read-utf-32le-char channel state)))))

  




















; =============================================================================
; From Section 3.9
; 
;   D31: UTF-32 Encoding FORM: The Unicode encoding form which assigns each
;   Unicode scalar value to a single unsigned 32-bit code unit with the same
;   numeric value as the Unicode scalar value.
;
;     - In UTF-32, the code sequence <004D, 0430, 4E8C, 10302> is represented
;     as <0000004D, 00000430, 00004E8C, 00010302>.
;
;     - Because surrogate code points are not included in the set of Unicode
;     scalar values, UTF-32 code units in the range 0000D800..0000DFFF(16) are
;     ill formed.
;
;     - Any UTF-32 code unit greater than 0010FFFF(16) is ill formed.
;
;
;   D38: Unicode Encoding SCHEME: A specified byte serialization for a Unicode
;   encoding form, including the specification of the handling of a byte order
;   mark (BOM), if allowed.
;
;     - For historical reasons, the Unicode encoding schemes are also referred
;     to as Unicode (or UCS) transformation formats (UTF).  That term is,
;     however, ambiguous between its usage for encoding forms and encoding 
;     schemes. 
;
; =============================================================================


|#






;; Formalization of Valid UTF-8 Sequences =====================================
;;
;; We say that the valid utf8-sequence are those objects, x, for which there
;; exists some unicode scalar value, cp, which can be used so that <cp, x>
;; matches with tables 3-5 and 3-6.  We use quantifiers to capture this idea.

(set-verify-guards-eagerness 0)

(defun-sk utf8-sequence? (x)
  (exists cp
          (and (utf8-table35-ok? cp x)
               (utf8-table36-ok? cp x))))

(set-verify-guards-eagerness 2)

;; The following theorems show that when x is a valid utf8 sequence, we can
;; choose (using utf8-sequence?-witness) an object which is a Unicode scalar
;; value, and meets our table requirements.

(defthm uchar?-of-utf8-sequence?-witness
  (implies (utf8-sequence? x)
           (uchar? (utf8-sequence?-witness x))))

(defthm utf8-table35-ok?-of-utf8-sequence?-witness
  (implies (utf8-sequence? x)
           (utf8-table35-ok? (utf8-sequence?-witness x) x))
  :hints(("Goal" :in-theory (disable utf8-table35-ok?))))

(defthm utf8-table36-ok?-of-utf8-sequence?-witness
  (implies (utf8-sequence? x)
           (utf8-table36-ok? (utf8-sequence?-witness x) x))
  :hints(("Goal" :in-theory (disable utf8-table36-ok?))))

