; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Regarding authorship of ACL2 in general:

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; serialize-raw.lisp -- a scheme for serializing ACL2 objects to disk.

; This file was initially developed and contributed by Jared Davis on behalf of
; Centaur Technology.  Comments referring to "I" or "my" are from Jared.  This
; file is now maintained by the ACL2 authors (see above).

(in-package "ACL2")

; INTRODUCTION
;
; We now develop a serialization scheme that allows ACL2 objects to be saved to
; disk using a compact, structure-shared, binary encoding.
;
; We configure ACL2's print-object$ function so that it writes objects with our
; encoding scheme when writing certificate files.  This allows large objects
; produced by make-event to be read and written efficiently.
;
; We extend the ACL2 readtable so that serialized objects can be read at any
; time, using the extended reader macros #Y[...] and #Z[...].  These macros are
; almost identical, but
;
;    #Y rebuilds the object entirely with CONS and does not restore any
;       fast alists, whereas
;
;    #Z uses HONS for the parts of the structure that were originally normed,
;       and rebuilds the hash tables for fast alists.
;
; We provide routines for reading and writing ACL2 objects as individual files,
; typically with a ".sao" extension for "Serialized ACL2 Object".  For
; bootstrapping reasons, these are introduced in hons.lisp and hons-raw.lisp
; instead of here in serialize-raw.lisp.

; Essay on Bad Objects and Serialize
;
; When we decode serialized objects, must we ensure that the object returned is
; a valid ACL2 object, i.e., not something that BAD-LISP-OBJECTP would reject?
;
; Matt and Jared think the answer is "no" for the reader macros.  Why?  These
; macros are just extensions of certain readtables like the *acl2-readtable*,
; which are used by READ to interpret input.  But there are already any number
; of other ways for READ to produce bad objects, for instance it might produce a
; floating point numbers, symbols in a foreign package, vectors, structures,
; etc.  The "Remarks on *acl2-readtable*" in acl2.lisp has more discussion of
; these matters.  At any rate, whenever ACL2 is using READ, it already needs to
; be defending against bad objects, so it should be okay if the serialize reader
; macros generate bad objects.
;
; However, Jared thinks that the serialize-read-fn function *is* responsible for
; ensuring that only good objects are read, because it is a "new" way for input
; to enter the system.
;
; Well, the serialized object format is considerably more restrictive than the
; Common Lisp reader, and does not provide any way to encode floats, circular
; objects, etc.  Jared thinks the only bad objects that can be produced from
; serialized reading are symbols in unknown packages.  So, in
; serialize-read-file we pass in a flag that makes sure we check whether
; packages are known.  We think this is sufficient to justify not checking
; BAD-LISP-OBJECTP explicitly.

; Essay on the Serialize Object Format
;
; Our scheme involves encoding ACL2 objects into a fairly simple, byte-based,
; binary format.
;
; There are actually three different formats of serialized objects, named V1,
; V2 and V3.  For compatibility with previously written files, we support
; reading from all three file formats.  But we always write files using the
; newest, V3 format.
;
; Why these different versions?
;
;    V1.  We originally developed our serialization scheme as a ttag-based
;         library in :dir :system, but this left us with no way to tightly
;         integrate it into ACL2's certificate printing/reading routines.
;
;    V2. When we moved serialization into ACL2 proper, we noticed a few things
;        that we could improve, and tweaked the serialization scheme.  The new
;        scheme, V2, wasn't compatible with community book books/serialize, but
;        we already had many files written in the old V1 format.
;
;    V3. Later, we realized that it would be easy to restore fast alists within
;        serialized objects, and that this would allow the fast alists defined
;        in a book to still be fast after including the book.  The new format,
;        V3, added this feature, but again we had lots of V2 files that we
;        still wanted to be able to read.
;
; Eventually we should be able to drop support for the old versions, but the
; formats are all very similar so supporting them is not that much work.  Since
; all of the versions are very similar, we begin with the V1 format.  A
; sequence of objects is encoded by OBJECT: first MAGIC, then LEN, then the
; indicated homogeneous sequences of objects, and then MAGIC.
;
;   OBJECT ::= MAGIC                       ; marker for sanity checking
;              LEN                         ; total number of objects
;              NATS RATS COMPLEXES CHARS   ; object data
;              STRS PACKAGES CONSES        ;
;              MAGIC                       ; marker for sanity checking
;
;   NATS      ::= LEN NAT*        ; number of nats, followed by that many nats
;   RATS      ::= LEN RAT*        ; number of rats, followed by that many rats
;   COMPLEXES ::= LEN COMPLEX*    ; etc.
;   CHARS     ::= LEN CHAR*
;   STRS      ::= LEN STR*
;   PACKAGES  ::= LEN PACKAGE*
;   CONSES    ::= LEN CONS*
;
;   RAT ::= NAT NAT NAT           ; sign (0 or 1), numerator, denominator
;   COMPLEX ::= RAT RAT           ; real, imaginary parts
;   CHAR ::= byte                 ; the character code for this character
;   STR ::= LEN CHAR*             ; length and then its characters
;   PACKAGE ::= STR LEN STR*      ; package name, number of symbols, symbol names
;   CONS ::= NAT NAT              ; "index" of its car and cdr (see below)
;
;   LEN ::= NAT                   ; just to show when we're referring to a length
;
;   MAGIC ::= #xAC120BC7          ; also see the discussion below
;
;   NAT ::= [see below]
;
; You can experiment with these formats, for example as follows in raw Lisp.
;
;   (let ((str (with-output-to-string (s) (ser-encode-to-stream 5/2 s))))
;        (loop for i from 0 to (1- (length str))
;              collect (char-code (char str i))))
;
;
; Magic Numbers.  The magic number, #xAC120BC7, is a 32-bit integer that sort
; of looks like "ACL2 OBCT", i.e., "ACL2 Object."  This use of magic numbers is
; probably silly, but may have some advantages:
;
;   (1) It lets us do a basic sanity check.
;
;   (2) When serialize is used to write out whole files, helps to ensure the
;       file doesn't start with valid ASCII characters.  This *might* help
;       protect these files from tampering by programs that convert newline
;       characters in text files (e.g., FTP programs).
;
;   (3) It gives us the option of tweaking our encoding.  Today we use distinct
;       magic numbers to identify V1, V2, and V3 files, and in the future we
;       could add additional encodings by adding other magic numbers.
;
;
; Naturals.  Our representation of NAT is slightly involved since we need to
; support arbitrary-sized natural numbers.  We use a variable-length encoding
; where the most significant bit of each byte is 0 if this is the last piece of
; the number, or 1 if there are additional bytes, and the other 7 bits are data
; bits.  The bytes are kept in little-endian order.  For example:
;
;      0 is encoded as   #x00       (continue bit: 0, data: 0)
;      2 is encoded as   #x02       (continue bit: 0, data: 2)
;       ...
;      127 is encoded as #x7F       (continue bit: 0, data: 127)
;      128 is encoded as #x80 #x01  [(c: 1, d: 0) = 0] + 128*[(c: 0, d: 1) = 1]
;      129 is encoded as #x81 #x01  [(c: 1, d: 1) = 1] + 128*[(c: 0, d: 1) = 1]
;      519 is encoded as #x87 #x04  [(c: 1, d: 7) = 7] + 128*[(c: 0, d: 4) = 4]
;    16383 is encoded as #xFF #x7F
;          [(c: 1, d: 127) = 127] + 128 * [(c: 0, d: 127) = 127]
;    16384 is encoded as #x80 #x80 #x01
;          [(c: 1, d:   0) =   0] + 128 * [(c: 0, d:   0) =   0]
;                                 + 128^2*[(c: 0, d:   1) =   1]
;    16387 is encoded as #x83 #x80 #x01
;          [(c: 1, d:   3) =   3] + 128 * [(c: 0, d:   0) =   0]
;                                 + 128^2*[(c: 0, d:   1) =   1]
;       ...
;
;
; Negative Integers.  Negative integers aren't mentioned in the file format
; because we encode them as rationals with denominator 1.  This only requires 2
; bytes of overhead (for the sign and denominator) beyond the magnitude of the
; integer, which seems acceptable since negative integers aren't especially
; frequent.
;
;
; Conses.  Every object in the file has an (implicit) index, determined by its
; position in the file.  The naturals are given the smallest indices 0, 1, 2,
; and so on.  Supposing there are N naturals, the rationals will have indices
; N, N+1, etc.  After that we have the complexes, then the characters, strings,
; symbols, and finally the conses.
;
; We encode conses using these indices.  For instance, suppose the first two
; natural numbers in our file are 37 and 55.  Since we start our indexing with
; the naturals, 37 will have index 0 and 55 will have index 1.  Then, we can
; encode the cons (37 . 55) by just writing down these two indices, e.g., #x00
; #x01.
;
; We insist that sub-trees of conses come first in the file, so as we are
; decoding the file, whenever we construct a cons we can make sure its indices
; refer to already-constructed conses.
;
; The object with the maximal index is "the object" that has been saved,
; and is returned by the #Y and #Z readers, or by the whole-file reader,
; serialize-read.
;
;
; The V2 Format.  The V2 format is almost the same as the V1 format, but with
; the following changes that allow us to restore the normedness of conses.
;
;   (1) The magic number changes to #xAC120BC8, so we know which format is
;       being used,
;
;   (2) We tweak the way indices are handled so that NIL and T are implicitly
;       given index 0 and 1, respectively (i.e., we do not actually write out
;       those symbols), which can sometimes slightly improve compression for
;       cons structures that have lots of NILs and Ts within them (since
;       without this tweak, NIL and T might have large indices that are
;       represented using many bytes).
;
;   (3) We change the way conses are represented so we can mark which conses
;       were normed.  Instead of recording a cons by writing down its car-index
;       and cdr-index verbatim, we now instead write down:
;
;           (car-index << 1) | (if honsp 1 0), cdr-index
;
;       Because of the way we encode naturals, this neatly only costs an extra
;       byte if the car-index happens to have an integer length that is a
;       multiple of 7.  (To see this, note that our encoding is essentially a
;       base-128 encoding, so we need an extra "digit" only when the top 7-bit
;       "digit" has its top bit set to 1.)
;
;   (4) Instead of the total number of objects, we replace LEN with the maximum
;       index of the object to be read.  Usually this just means that instead
;       of LEN we record LEN - 1.  But it allows us to detect the special case
;       of NIL where the object being encoded is not necessarily at LEN - 1.
;
;
; The V3 format.  The V3 format is almost the same as the V2 format, but with
; the following changes that allow us to restore fast alists.
;
;   (1) The magic number changes to #xAC120BC9, and
;
;   (2) We extend the OBJECT format with an extra FALS field, that comes
;       after the conses.  Note that LEN is unchanged and does not count
;       the FALS.
;
;         OBJECT ::= MAGIC                       ; marker for sanity checking
;                    LEN                         ; total number of objects
;                    NATS RATS COMPLEXES CHARS   ; object data
;                    STRS PACKAGES CONSES        ;
;                    FALS
;                    MAGIC                       ; marker for sanity checking
;
;         FALS ::= FAL* 0                        ; zero-terminated list
;
;         FAL ::= NAT NAT                        ; index and hash-table-count
;
;   (3) We change the encoding of STR so that we can mark which strings were
;       normed.  In place of recording the string's LEN, we instead record:
;          (len << 1) | (if honsp 1 0)

; -----------------------------------------------------------------------------
;
;                              PRELIMINARIES
;
; -----------------------------------------------------------------------------

(defparameter *ser-verbose* nil)

(defmacro ser-time? (form)
  `(if *ser-verbose*
       (time ,form)
     ,form))

(defmacro ser-print? (msg &rest args)
  `(when *ser-verbose*
     (format t ,msg . ,args)))

; To make it easy to switch the kind of input/output stream being used, all of
; our stream reading/writing is done with the following macros.
;
; In previous versions of serialize we used binary streams and wrote/read from
; them with write/read-byte on most Lisps; on CCL we used memory-mapped files
; for better performance while reading.  But we had to switch to using ordinary
; character streams to get compatibility with the Common Lisp reader (where we
; use #Y and #Z), which reads character streams.

(defmacro ser-write-char (x stream)
  `(write-char (the character ,x) ,stream))

(defmacro ser-write-byte (x stream)
  `(ser-write-char (code-char (the (unsigned-byte 8) ,x)) ,stream))

(defmacro ser-read-char (stream)

; Note that Lisp's read-char causes an end-of-file error (HyperSpec says that
; it "is signaled") if EOF is reached, so we don't have to detect unexpected
; EOFs in our decoding routines.

  `(the character (read-char ,stream)))

(defmacro ser-read-byte (stream)

; How do we know that the char-code is 8 bits when reading a file stream?  We
; try to enforce this in acl2-set-character-encoding.  The magic number might
; save us if this changes, since its first byte is #xAC = 172 > 127 and will
; presumably be misread if we are using a file character encoding other than
; iso-8859-1.

  `(the (unsigned-byte 8) (char-code (ser-read-char ,stream))))

(defun ser-encode-magic (stream)
  ;; We only write V3 files now, so we write AC120BC9 instead of C8 or C7.
  (ser-write-byte #xAC stream)
  (ser-write-byte #x12 stream)
  (ser-write-byte #x0B stream)
  (ser-write-byte #xC9 stream))

(defun ser-decode-magic (stream)
  ;; Returns :V1, :V2, or :V3, or causes an error.
  (let* ((magic-1 (ser-read-byte stream))
         (magic-2 (ser-read-byte stream))
         (magic-3 (ser-read-byte stream))
         (magic-4 (ser-read-byte stream)))
    (declare (type (unsigned-byte 8) magic-1 magic-2 magic-3 magic-4))
    (let ((version (and (= magic-1 #xAC)
                        (= magic-2 #x12)
                        (= magic-3 #x0B)
                        (cond ((= magic-4 #xC7) :v1)
                              ((= magic-4 #xC8) :v2)
                              ((= magic-4 #xC9) :v3)
                              (t nil)))))
      (unless version
        (error "Invalid serialized object, magic number incorrect: ~X ~X ~X ~X"
               magic-1 magic-2 magic-3 magic-4))
      version)))

; -----------------------------------------------------------------------------
;
;                      ENCODING AND DECODING NATURALS
;
; -----------------------------------------------------------------------------

; WHY DO WE USE 8-BIT BLOCKS?
;
; Originally I tried using 64-bit blocks.  I thought this would mean only 1/64
; of the bits would be "overhead" for continue-bits, and surely this would be
; better than using 8-bit blocks, where 1/8 of the bits would be continue-bit
; overhead.
;
; This thinking is totally wrong.  It ignores another important source of
; overhead: the unnecessary data-bits in the final block.  To make this very
; concrete, think about encoding the number 5.  We only "need" 3 bits.  In an
; 8-bit encoding, we use 8 bits so the overhead is 5/8 = 62%.  But in a 64-bit
; encoding we would need 64 bits for an overhead of 61/64 = 95%.  So the 8-bit
; encoding is much more efficient for small integers.
;
; Another potential disadvantage of 64-bit blocks may seem to be that 64-bit
; numbers are not fixnums in CCL (or perhaps any Lisp circa 2014 or for years
; to come).  However, that issue is probably actually quite minor; 8 8-bit
; fixnums quite possibly use more memory than one 64-bit bignum.
;
; Of course, there are cases where 64-bit blocks win.  For instance, 2^62
; nicely fits into a single 64-bit block, but requires 9 8-bit blocks (at 7
; data bits apiece), i.e., 72 bits.  But on some other larger numbers, 8-bit
; blocks can still be more efficient.  Take 2^64.  Here, we need either 2
; 64-bit blocks (at 63 data bits apiece) for 128 bits, or 10 8-bit blocks for
; 80 bits.  In short, the wider encoding only wins when the numbers are very
; long, or when there aren't very many unnecessary data bits in the final
; block.

; WHY ALL THESE OPTIMIZATIONS?
;
; The performance of natural number encoding/decoding is especially important
; because we have to (1) encode/decode two naturals for every cons, and (2)
; encode/decode naturals all over the place for string lengths, symbol name
; lengths, and the representation of any number.  These optimizations are a big
; deal: on one example benchmark, they improve CCL's decoding performance by
; almost 20% (as opposed to using just ser-encode-nat-large to encode
; naturals).

(defun ser-encode-nat-fixnum (n stream)

; Optimized encoder that assumes N is a fixnum.

  (declare (type fixnum n))
  (loop while (>= n 128)
        do
        (ser-write-byte (logior
                         ;; The 7 low data bits
                         (the fixnum (logand n #x7F))
                         ;; A continue bit
                         #x80)
                        stream)
        (setq n (the fixnum (ash n -7))))
  (ser-write-byte n stream))

(defun ser-encode-nat-large (n stream)

; Safe encoder that doesn't assume how large N is.

  (declare (type (integer 0 *) n))
  (loop until (typep n 'fixnum)
        do
        ;; Fixnums are at least (signed-byte 16) in Common Lisp, so we must
        ;; be in the large case, i.e., n > 128.
        (ser-write-byte (logior
                         ;; The 7 low data bits
                         (the fixnum (logand (the integer n) #x7F))
                         ;; A continue bit
                         #x80)
                        stream)
        (setq n (the integer (ash n -7))))
  (ser-encode-nat-fixnum n stream))

(defmacro ser-encode-nat (n stream)

; This is kind of silly, but it lets us avoid the function overhead of calling
; ser-encode-nat-large in the very common case that N is a fixnum.

  (when (eq stream 'n)
    (error "~s called with stream = N, which would cause capture!"
           'ser-encode-nat))
  `(let ((n ,n))
     (if (typep n 'fixnum)
         (ser-encode-nat-fixnum n ,stream)
       (ser-encode-nat-large n ,stream))))

(defun ser-decode-nat-large (shift value stream)

; Simple (but unoptimized) natural number decoder that doesn't assume anything
; is a fixnum.  Shift is 7 times the current block number we are reading, and
; represents how much we need to shift over the next 7 bits we read.  Value is
; the already-summed value of the previous blocks we have read.

  (declare (type integer value shift))
  (let ((x1 (ser-read-byte stream)))
    (declare (type fixnum x1))
    (loop while (>= x1 128)
          do
          (incf value (ash (- x1 128) shift))
          (incf shift 7)
          (setf x1 (ser-read-byte stream)))
    (incf value (ash x1 shift))
    value))

(defmacro ser-decode-nat-body (shift)

; See SER-NAT-DECODE; this is accounting for different fixnum sizes across Lisps
; by unrolling the loop with a recursive macro.  SHIFT is a constant that is
; being incremented by 7 on each "iteration".  An invariant that is important to
; the fixnum optimizations is that VALUE is always less than 2^SHIFT.

  (if (> (expt 2 (+ 7 shift)) most-positive-fixnum)
      ;; Can't unroll any further because we've reached the fixnum size, so fall
      ;; back to using the large decoder.
      `(ser-decode-nat-large ,shift value stream)

    `(progn
       (setq x1 (ser-read-byte stream))

       ;; Reusing X1 is kind of goofy, but seems to result in better code on
       ;; CCL.
       (cond
        ((< x1 128)
         ;; The returned VALUE + (X1 << SHIFT) is a fixnum since it is less than
         ;; 2^(7+SHIFT), which above we checked is a fixnum.
         (setq x1 (the fixnum (ash x1 ,shift)))
         (the fixnum (+ value x1)))

        (t
         ;; Else, we increment value by (x1 - 128) << SHIFT.  This is still a
         ;; fixnum because (x1 - 128) < 2^7, so the sum is under 2^(7+SHIFT).
         ;; To see this let x2=x1-128, s=SHIFT, and v=value; then since v<2^s
         ;; and x2 <= 2^7-1, we have:
         ;; value + (x1-128)<<s = v + x2*2^s < 2^s + (2^7-1)*2^s = 2^(7+s).
         (setq x1 (the fixnum (- x1 128)))
         (setq x1 (the fixnum (ash x1 ,shift)))
         (setq value (the fixnum (+ value x1)))

         ;; Recursive macro expansion to unroll further.
         (ser-decode-nat-body ,(+ 7 shift)))))))

(defun ser-decode-nat (stream)

; Optimized natural-number decoder.  For small enough integers (under 128) we
; don't need any shifting nonsense or even an accumulator.  For anything larger,
; we set up the initial VALUE accumulator and use our macro to write an
; unrolled, fixnum-optimized loop for us.

  (let ((x1 (ser-read-byte stream)))
    (declare (type fixnum x1))
    (when (< (the fixnum x1) 128)
      (return-from ser-decode-nat x1))
    (setq x1 (the fixnum (- x1 128)))
    (let ((value x1))
      (declare (type fixnum value))
      (ser-decode-nat-body 7))))

; -----------------------------------------------------------------------------
;
;                 ENCODING AND DECODING OTHER BASIC OBJECTS
;
; -----------------------------------------------------------------------------

; RAT ::= NAT NAT NAT           ; sign (0 or 1), numerator, denominator

(declaim (inline ser-encode-rat ser-decode-rat))

(defun ser-encode-rat (x stream)
  (declare (type rational x))
  (ser-encode-nat (if (< x 0) 1 0) stream)
  (ser-encode-nat (abs (numerator x)) stream)
  (ser-encode-nat (denominator x) stream))

(defun ser-decode-rat (stream)
  (let* ((sign        (ser-decode-nat stream))
         (numerator   (ser-decode-nat stream))
         (denominator (ser-decode-nat stream)))
    (declare (type integer sign numerator denominator))

    (cond ((= sign 1)
           (setq numerator (- numerator)))
          ((= sign 0)
           ;; Fine, but there is nothing to do.
           nil)
          (t
           ;; This check probably isn't necessary; we could just assume that the
           ;; sign is zero.  But it seems cheap enough and basically reasonable.
           (error "Trying to decode rational, but the sign is invalid.")))

    (when (= denominator 0)
      ;; This check probably isn't necessary since the Lisp should probably
      ;; signal an error if we try to divide by zero, but it seems cheap enough
      ;; and is probably basically reasonable.
      (error "Trying to decode rational, but the denominator is zero."))

    (the rational (/ numerator denominator))))

; COMPLEX ::= RAT RAT           ; real, imaginary parts

(declaim (inline ser-encode-complex ser-decode-complex))

(defun ser-encode-complex (x stream)
  (declare (type complex x))
  (ser-encode-rat (realpart x) stream)
  (ser-encode-rat (imagpart x) stream))

(defun ser-decode-complex (stream)
  (let* ((realpart (ser-decode-rat stream))
         (imagpart (ser-decode-rat stream)))
    (declare (type rational realpart imagpart))
    (when (= imagpart 0)
      ;; Hrmn.  This check is probably unnecessary.  (complex 3 0) is just 3.
      ;; Our encoder should never encode natural numbers as complexes, but it
      ;; wouldn't necessarily be wrong to do so.
      (error "Trying to decode complex, but the imagpart is zero."))
    (complex realpart imagpart)))

; (v1/v2): STR ::= LEN CHAR*             ; length and then its characters
; (v3):    STR ::= [(LEN << 1) | (if normedp 1 0)] CHAR*

; Note that our symbol encoding/decoding stuff piggy-backs on our string stuff,
; so we care about string encoding/decoding performance a bit.
;
; A very minor note is that in Common Lisp, the length of a string must be a
; fixnum (a string is a vector, which is a one-dimensional array, and hence its
; size must be less than the array-dimension-limit, which is a fixnum.)

(declaim (inline ser-encode-str ser-decode-str))

(defun ser-encode-str (x stream)
  (declare (type string x))
  (let* ((len     (length x))
         (normedp (hl-hspace-normedp-wrapper x))
         (header  (logior (ash len 1) (if normedp 1 0))))
    (ser-encode-nat header stream)
    (loop for n fixnum from 0 below (the fixnum len) do
          (ser-write-char (char x n) stream))))

(defun ser-decode-str (version hons-mode stream)
  (let* ((header (ser-decode-nat stream))
         (len    (if (eq version :v3)
                     (ash header -1)
                   header))
         (normp  (and (eq version :v3)
                      (= (the bit (logand header 1)) 1)
                      (not (eq hons-mode :never)))))
    (unless (and (typep len 'fixnum)
                 (< (the fixnum len) array-dimension-limit))

; Sanity check: shouldn't normally happen if we encoded with ser-encode-str,
; though could perhaps happen if that was done with a different Lisp
; implementation.

      (error "Trying to decode a string, but the length is too long."))
    (let ((str (make-string (the fixnum len))))
      (declare (type vector str))
      (loop for i fixnum from 0 below (the fixnum len) do
            (setf (schar str i) (ser-read-char stream)))
      (if normp
          (hons-copy str)
        str))))

; -----------------------------------------------------------------------------
;
;                    ENCODING AND DECODING BASIC OBJECT LISTS
;
; -----------------------------------------------------------------------------

; We now build upon our encoders/decoders for individual elements, and write
; versions to deal with lists of naturals, rationals, etc.

(defstruct ser-decoder

; The decoder's state mainly consists of an ARRAY and a FREE index.  As the file
; is decoded, ARRAY gets populated from zero on up, with FREE always pointing to
; the next available slot.  Since array sizes are always fixnums, we know that
; FREE is always a fixnum.

  (array (make-array 0) :type simple-vector)
  (free  0              :type fixnum)

; The decoder also knows which file format we are decoding (i.e., :v1, :v2,
; :v3).  This is set based on the magic number from the start of the file.

  (version nil))

; NATS ::= LEN NAT*        ; number of nats, followed by that many nats

(defun ser-encode-nats (x stream)
  (let ((len (length x)))
    (ser-print? "; Encoding ~a naturals.~%" len)
    (ser-encode-nat len stream)
    (dolist (elem x)
      (ser-encode-nat elem stream))))

(defun ser-decode-and-load-nats (decoder stream)
  (declare (type ser-decoder decoder))
  (let* ((len  (ser-decode-nat stream))
         (arr  (ser-decoder-array decoder))
         (free (ser-decoder-free decoder))
         (stop (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a naturals.~%" len)
    (unless (<= stop (length arr))
      ;; Note that we need just one bounds check for the whole list of naturals.
      (error "Invalid serialized object, too many naturals."))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free) (ser-decode-nat stream))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; RATS ::= LEN RAT*        ; number of rats, followed by that many rats

(defun ser-encode-rats (x stream)
  (let ((len (length x)))
    (ser-print? "; Encoding ~a rationals.~%" len)
    (ser-encode-nat len stream)
    (dolist (elem x)
      (ser-encode-rat elem stream))))

(defun ser-decode-and-load-rats (decoder stream)
  (declare (type ser-decoder decoder))
  (let* ((len  (ser-decode-nat stream))
         (arr  (ser-decoder-array decoder))
         (free (ser-decoder-free decoder))
         (stop (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a rationals.~%" len)
    (unless (<= stop (length arr))
      (error "Invalid serialized object, too many rationals."))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free) (ser-decode-rat stream))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; COMPLEXES ::= LEN COMPLEX*   ; number of complexes, followed by that many complexes

(defun ser-encode-complexes (x stream)
  (let ((len (length x)))
    (ser-print? "; Encoding ~a complexes.~%" len)
    (ser-encode-nat len stream)
    (dolist (elem x)
      (ser-encode-complex elem stream))))

(defun ser-decode-and-load-complexes (decoder stream)
  (declare (type ser-decoder decoder))
  (let* ((len  (ser-decode-nat stream))
         (arr  (ser-decoder-array decoder))
         (free (ser-decoder-free decoder))
         (stop (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a complexes.~%" len)
    (unless (<= stop (length arr))
      (error "Invalid serialized object, too many complexes."))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free) (ser-decode-complex stream))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; CHARS ::= LEN CHAR*     ; number of characters, followed by that many chars

(defun ser-encode-chars (x stream)
  (let ((len (length x)))
    (ser-print? "; Encoding ~a characters.~%" len)
    (ser-encode-nat len stream)
    (dolist (elem x)
      (ser-write-char elem stream))))

(defun ser-decode-and-load-chars (decoder stream)
  (declare (type ser-decoder decoder))
  (let* ((len  (ser-decode-nat stream))
         (arr  (ser-decoder-array decoder))
         (free (ser-decoder-free decoder))
         (stop (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a characters.~%" len)
    (unless (<= stop (length arr))
      (error "Invalid serialized object, too many characters."))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free) (ser-read-char stream))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; STRS ::= LEN STR*      ; number of strings, followed by that many strs

(defun ser-encode-strs (x stream)
  (let ((len (length x)))
    (ser-print? "; Encoding ~a strings.~%" len)
    (ser-encode-nat len stream)
    (dolist (elem x)
      (ser-encode-str elem stream))))

(defun ser-decode-and-load-strs (hons-mode decoder stream)
  (declare (type ser-decoder decoder))
  (let* ((len     (ser-decode-nat stream))
         (arr     (ser-decoder-array decoder))
         (free    (ser-decoder-free decoder))
         (version (ser-decoder-version decoder))
         (stop    (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a strings.~%" len)
    (unless (<= stop (length arr))
      (error "Invalid serialized object, too many strings."))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free) (ser-decode-str version hons-mode stream))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; -----------------------------------------------------------------------------
;
;                      ENCODING AND DECODING SYMBOLS
;
; -----------------------------------------------------------------------------

; We don't want to pay the price of writing down the package for every symbol
; individually, since most of the time an object will probably contain lots of
; symbols from the same package.  So, our basic approach is to organize the
; symbols into groups by their package names, and then for each package we write
; out: the name of the package, and the list of symbol names.
;
; See also the Essay on Bad Objects and Serialize.  When we are decoding, we
; optionally check that packages are known to ACL2 by calling pkg-witness, which
; causes an error if it the package isn't known.  Note that we only have to do
; this once per package, so this is a very low-cost check.
;
; If checking packages is so cheap, why not just check packages all the time?
; We tried that originally, but sometimes ACL2 actually DOES read in bad
; objects, e.g., foo@expansion.lsp may have *1* symbols in it, etc.  So we need
; to avoid complaining if ACL2 is using the #Y or #Z reader when reading these
; files.

; PACKAGE ::= STR LEN STR*      ; package name, number of symbols, symbol names

(defun ser-encode-package (pkg x stream)
  (declare (type string pkg))
  (let ((len (length x)))
    (ser-print? "; Encoding ~a symbols for ~a package.~%" len pkg)
    (ser-encode-str pkg stream)
    (ser-encode-nat (length x) stream)
    (dolist (elem x)
      (ser-encode-str (symbol-name elem) stream))))

(defun ser-decode-and-load-package (check-packagesp decoder stream)

; We always use hons-mode :never below, because there's no need to norm the
; package or symbol names since we're going to intern them and not return them.
; The point here is that it is difficult to control norming of symbol-names;
; imagine for example reading FOO::X and then later (defconst *a* (intern
; (hons-copy "X") "FOO")).  Then (symbol-name 'foo::x) will not be normed.

  (declare (type ser-decoder decoder))
  (let* ((version  (ser-decoder-version decoder))
         (arr      (ser-decoder-array decoder))
         (free     (ser-decoder-free decoder))
         (pkg-name (ser-decode-str version :never stream))
         (len      (ser-decode-nat stream))
         (stop     (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a symbols for ~a package.~%" len pkg-name)
    (unless (<= stop (length arr))
      (error "Invalid serialized object, too many symbols."))
    (when check-packagesp
      (pkg-witness pkg-name))
    (loop until (= (the fixnum stop) free) do
          (setf (svref arr free)
                (let ((temp (ser-decode-str version :never stream)))

; We use *read-suppress* to avoid trying to handle symbols in contexts like
; #+sbcl (sb-ext:inhibit-warnings 3)
; where the feature is false (as in CCL for the example above).

                  (if *read-suppress* nil (intern temp pkg-name))))
          (incf free))
    (setf (ser-decoder-free decoder) stop)))

; PACKAGES ::= LEN PACKAGE*    ; number of packages, followed by that many packages

(defun ser-encode-packages (alist stream)

; Alist maps package-names to the lists of their symbols.

  (let ((len (length alist)))
    (ser-print? "; Encoding symbols for ~a packages.~%" len)
    (ser-encode-nat len stream)
    (dolist (entry alist)
      (ser-encode-package (car entry) (cdr entry) stream))))

(defun ser-decode-and-load-packages (check-packagesp decoder stream)
  (declare (type ser-decoder decoder))
  (let ((len (ser-decode-nat stream)))
    (ser-print? "; Decoding symbols for ~a packages.~%" len)
    (loop for i from 1 to len do
          (ser-decode-and-load-package check-packagesp decoder stream))))

; -----------------------------------------------------------------------------
;
;                      PREPARING OBJECTS FOR ENCODING
;
; -----------------------------------------------------------------------------

(defun ser-hashtable-init (size test)

; For good performance, it is critical that we aggressively resize the hash
; tables that are used in the atom-gathering phase of encoding.  This is just a
; wrapper for making hash tables with more aggressive rehash sizes.

  (make-hash-table :size size
                   :test test
                   :rehash-size 2.2
                   #+ccl :shared #+ccl nil
                   ))

(defstruct ser-encoder

; This object bundles the state of the encoder.
;
; The first phase of encoding is SER-GATHER-ATOMS.  The goal is to quickly
; collect all of the atoms in the object, without duplication, and partition
; them into lists by their types.
;
; To avoid repeatedly collecting the same atoms, we use four "seen" tables that
; keep track of which objects we have explored.  As we gather atoms, we mark the
; objects we have seen by binding them to T in the appropriate hash table.
;
; Every symbol we have seen is in the SYM hash table, and every
; number/character we have seen is in the EQL hash table.  But the string and
; cons tables are only EQ hash tables.  Because of this, EQUAL-but-not-EQ
; strings and conses may be bound in their seen tables.
;
; We make no effort to avoid "redundantly" writing EQUAL-but-not-EQ conses or
; strings.  Of course, a HONS user could first hons-copy their object to
; achieve full structure sharing.  This would perhaps improve read time at the
; cost of write time.

  (seen-sym  (ser-hashtable-init 1000 'eq)  :type hash-table)
  (seen-eql  (ser-hashtable-init 1000 'eql) :type hash-table)
  (seen-str  (ser-hashtable-init 1000 'eq)  :type hash-table)
  (seen-cons (ser-hashtable-init 2000 'eq)  :type hash-table)

; In addition to the above seen tables, the encoder has several accumulators
; which collect the atoms it finds during the GATHER-ATOMS phase.  The basic
; idea here is to separate these objects by their types, so that we can then
; write them out using our encoders for lists of naturals, rationals, etc.
;
; The accumulators for naturals, rationals, complexes, strings, and characters
; are simple lists that we push new values into.  Because of our seen-tables, we
; can guarantee that the accumulators for naturals, rationals, complexes, and
; characters have no duplicates.  However, the strings accumulator may contain
; duplicates in the sense that two members might be equal but not eq.

  (naturals     nil :type list)
  (rationals    nil :type list)
  (complexes    nil :type list)
  (chars        nil :type list)
  (strings      nil :type list)

; The symbol accumulator is more complex.  The SYMBOL-HT is a hash table that
; associates packages with the lists of symbols found in that package.  Once we
; are done gathering atoms, we map over this hash table to convert it into an
; alist (SYMBOL-AL).  This conversion is cheap; it only requires one cons per
; package.

  (symbol-ht    (ser-hashtable-init 60 'eq) :type hash-table)
  (symbol-al    nil :type list)

; The free-index here is only used in ser-encode-conses.  Bundling it with the
; encoder's state is beneficial in two ways for ser-encode-conses: it reduces
; stack size requirements by eliminating a parameter, and simplifies the flow
; because we don't need to return multiple values.

  (free-index  0 :type fixnum)

; The stream that we are writing into.  Bundling this into the encoder instead
; of passing it as an extra argument helps to reduce the stack size
; requirements for ser-encode-conses.

  (stream nil)

)

(defmacro ser-see-obj (x table)

; Mark X as seen, and return T/NIL based on whether it was previously seen.

  `(let ((x   ,x)
         (tbl ,table))
     (cond ((gethash x tbl) t)
           (t (setf (gethash x tbl) t)
              nil))))

(defun ser-gather-atoms (x encoder)

; Gathering atoms is particularly performance critical, so we have looked into
; making it faster.  We assume X is a valid ACL2 object.  We do some typep
; checks in a few cases where using ordinary recognizers seems to be slower.
; But this does not gain us much, because almost all of the time seems to be
; spent on hashing.
;
; Sol Swords uses a destructive hashing scheme in his AIGER writer which we
; could probably adapt for use here, and it would probably lead to significant
; performance gains.  However, anything destructive is scary with respect to
; multithreaded code, and we don't want to use it unless we really have no
; other choice.

  (declare (type ser-encoder encoder))
  (cond ((consp x)
         (unless (ser-see-obj x (ser-encoder-seen-cons encoder))
           (ser-gather-atoms (car x) encoder)
           (ser-gather-atoms (cdr x) encoder)))

        ((symbolp x)
         ;; V2 change: do not gather T and NIL into the accumulator for
         ;; symbols.  They are implicit in the v2 format.
         (unless (or (eq x t)
                     (eq x nil)
                     (ser-see-obj x (ser-encoder-seen-sym encoder)))
           (push x (gethash (symbol-package x)
                            (ser-encoder-symbol-ht encoder)))))

        ((typep x 'fixnum)
         ;; This case is probably common enough to add explicitly, since this
         ;; fixnum check is so fast.
         (unless (ser-see-obj x (ser-encoder-seen-eql encoder))
           (if (< (the fixnum x) 0)
               (push x (ser-encoder-rationals encoder))
             (push x (ser-encoder-naturals encoder)))))

        ((typep x 'array) ; <-- (stringp x), but twice as fast in CCL.
         (unless (ser-see-obj x (ser-encoder-seen-str encoder))
           (push x (ser-encoder-strings encoder))))

        ;; Performance is probably already pretty bad at this point, because of
        ;; all the typep checks above.
        (t
         (unless (ser-see-obj x (ser-encoder-seen-eql encoder))
           (cond ((typep x 'character)
                  (push x (ser-encoder-chars encoder)))
                 ((typep x 'integer)
                  (if (< x 0)
                      (push x (ser-encoder-rationals encoder))
                    (push x (ser-encoder-naturals encoder))))
                 ((rationalp x)
                  (push x (ser-encoder-rationals encoder)))
                 ((complex-rationalp x)
                  (push x (ser-encoder-complexes encoder)))
                 (t
                  (error "ser-gather-atoms-types given non-ACL2 object.")))))))

; Essay on How We Handle Equal-but-not-eq Strings
;
; A subtle change in V3 is that we no longer make any effort to avoid
; redundantly encoding EQUAL-but-not-EQ or strings.
;
; When I first developed serialize, I wanted to use it to save the models of
; our processor.  My Verilog translator produced objects with lots of strings,
; and in many cases these strings could be different, e.g., if you parsed a
; module with:
;
;     module m ( ..., foo, ... );
;        input foo;
;        assign ... = foo;
;        ...
;     endmodule
;
; then you could end up with lots of different strings that all said "foo".
; Note also that in this context, I really wanted to optimize for read time
; instead of write time (a script made the processor models at night, where
; time is irrelevant, but I needed to read them in while developing proofs.)
; At any rate, for these reasons, I really wanted to avoid writing out
; redundant strings.
;
; My first idea was to just use an EQUAL hash table for seen-str, but this
; turned out to be far too slow.
;
; Instead, I developed a fancy scheme.  First, the seen-str was only an EQ hash
; table.  But when encoding the collected strings, I (1) sorted them using
; Lisp's SORT function, which is a stable sort, and (2) assigned their indices
; using a tricky function that looked for adjacent EQUAL strings, and reused
; the index in this case.  The net effect was that all strings would be
; canonicalized to some representative.  This was probably a performance win
; because, instead of having to EQUAL-hash at each occurrence of the string, we
; only have to EQ hash and then do one global sort at the end.  (It probably
; would have worked just as well to use separate EQ and EQUAL hash tables.)
;
; This scheme was used in V1 and V2.  However, in V3, where we started to
; record whether strings were normed, and restore them to their normed status,
; we ran into a problem.
;
; Suppose there are two EQUAL-but-not-EQ strings,
;    - X (which is normed) and
;    - Y (which is not).
;
; Under our canonicalization scheme, we would choose one of these as the
; canonical form "at random."  (Actually the winner just depended on which we
; first encountered, but you can think of that as basically random.)  At any
; rate, this could two bad outcomes:
;
;    (1) Y could be canonicalized to X, and hence become normed.  This seems
;        basically fine and is probably nothing to be worried about unless some
;        TTAG code is depending on it being different from Y, which wouldn't be
;        sound anyway).
;
;    (2) X could be canonicalized to Y, and hence lose its normed status.  This
;        is bad because if X is being used as a fast alist key, we will have
;        trouble restoring that alist.
;
; It seems easy enough to fix this by norming the string whenever ANY of its
; EQUAL-but-not-EQ partners are normed.  But instead, we now just do not try to
; avoid writing out redundant strings.  Why not?
;
;   - It was somewhat complicated and ugly, and the fix seems kind of gross.
;
;   - Sorting the strings slows down writing, and write speed is now more
;     important than it used to be.  We used to only write out our processor
;     models with an automated script.  But now serialize is used to print
;     certificates, etc., and while write speed is certainly still less
;     important than read speed, it is at least somewhat important.
;
;   - EQUAL-but-not-EQ strings don't seem that prevalent anyway, e.g., we now
;     judiciously use HONS-COPY to normalize strings in the Verilog parser,
;     etc., and other users can do the same if they think EQUAL-but-not-EQ
;     copies of a string are likely to occur.

(defun ser-make-atom-map (encoder)

; After the atoms have been gathered we want to assign them unique indices.
; These indices will need to agree with the implicit order of the indices in
; the serialized file.  So, we need to assign indices to the naturals first,
; then the rationals, etc.
;
; In earlier versions of serialize, we constructed "atom map" structures that
; were hash tables binding atoms to their indices.  These atom maps were new
; structures that were unrelated to the seen-tables above.
;
; But now, for considerably better performance and memory efficiency, we
; instead smash the seen-tables and convert them into index mappings.  That is,
; during SER-GATHER-ATOMS above, the seen tables just bound the objects we had
; seen to T.  Now we are going to smash these bindings and replace them with
; their indices.  This is especially efficient because their hash tables have
; already been grown to the proper sizes.
;
; Before we this smashing process, we check that the maximum index we will ever
; need is going to be a fixnum.  Because of this, throughout this code we can
; assume that all indices are always fixnums.
;
; Future optimization potential.  It might be possible to do the index
; assignment inline with atom gathering, by keeping separate track of how many
; naturals we have seen, how many characters, etc., and storing only
; type-relative offsets into the atom maps instead of absolute indices.  This
; might be worthwhile: it should significantly reduce the amount of hashing we
; need to do.

  ;; Note: this order must agree with ser-encode-atoms.

  (let ((free-index 2)
        ;; In v2, the first free index is 2 (nil and t are implicitly 0 and 1)
        (seen-sym (ser-encoder-seen-sym encoder))
        (seen-eql (ser-encoder-seen-eql encoder))
        (seen-str (ser-encoder-seen-str encoder)))
    (declare (type fixnum free-index)
             (type hash-table seen-sym seen-eql seen-str))

    (dolist (elem (ser-encoder-naturals encoder))
      (setf (gethash elem seen-eql) free-index)
      (incf free-index))

    (dolist (elem (ser-encoder-rationals encoder))
      (setf (gethash elem seen-eql) free-index)
      (incf free-index))

    (dolist (elem (ser-encoder-complexes encoder))
      (setf (gethash elem seen-eql) free-index)
      (incf free-index))

    (dolist (elem (ser-encoder-chars encoder))
      (setf (gethash elem seen-eql) free-index)
      (incf free-index))

    (dolist (elem (ser-encoder-strings encoder))
      (setf (gethash elem seen-str) free-index)
      (incf free-index))

    ;; Turn the hash table of symbols into an alist so that they're in the same
    ;; order now and when we encode.  This might not be necessary, but it's
    ;; probably very cheap in practice because there's only one entry per
    ;; package.
    (let ((al nil))
      (maphash (lambda (key val)
                 (push (cons (package-name key) val) al))
               (ser-encoder-symbol-ht encoder))
      (setf (ser-encoder-symbol-al encoder) al))

    (dolist (elem (ser-encoder-symbol-al encoder))
      (dolist (sym (cdr elem))
        ;; We don't have to check for T and NIL because we didn't accumulate
        ;; them into the symbol table.
        (setf (gethash sym seen-sym) free-index)
        (incf free-index)))

    ;; V2 change: explicitly assign nil and t indices 0 and 1
    (setf (gethash nil seen-sym) 0)
    (setf (gethash t seen-sym) 1)

    ;; Finally, update the encoder with the free index we've arrived at.
    (setf (ser-encoder-free-index encoder) free-index)))

; -----------------------------------------------------------------------------
;
;                      ENCODING AND DECODING CONSES
;
; -----------------------------------------------------------------------------

; After the atoms have been assigned their indices as above, we are going to
; write out a list of instructions for reassembling the conses in the object.
; We keep incrementing the free-index as we go so that the atoms and conses end
; up in a shared index-space.  Just as we smashed the seen-tables for the
; atoms, we also smash the seen-cons table to reuse its space for the indices.
;
; In earlier versions of serialize, we separated the act of generating
; instructions from writing them.  But now for greater efficiency we fuse the
; two operations so that we never need to record the instructions anywhere
; except in the stream.
;
; We call ser-encode-conses only after generating all of the atom maps,
; writing out all the atoms in the file, and writing the number of conses that
; we are about to build (which is available as the count of the seen-cons
; table.)

(defun ser-encode-conses
  (x          ; the object we are encoding, which we are recurring through
   encoder    ; the encoder's state (so we can look at all the tables)
   )
  "Returns X-INDEX"
  (declare (type ser-encoder encoder))
  (if (atom x)
      ;; Atoms already have their indices assigned, so there's nothing
      ;; to do but look them up.
      (cond ((symbolp x)
             (gethash x (ser-encoder-seen-sym encoder)))
            ((stringp x)
             (gethash x (ser-encoder-seen-str encoder)))
            (t
             (gethash x (ser-encoder-seen-eql encoder))))

    (let* ((seen-cons (ser-encoder-seen-cons encoder))
           (idx       (gethash x seen-cons)))

      ;; At this point you might expect to see something like, "(if idx ...)".
      ;; But since we are reusing the seen-cons table, every cons that does not
      ;; already have its index assigned is bound to T, not unbound.  To see if
      ;; an index has been assigned, then, we have to check if it is a number.
      ;; Since all indices are fixnums, I check whether it's a fixnum, which is
      ;; very fast (just looking at type bits), at least on CCL.
      (if (typep idx 'fixnum)
          idx
        (let* ((car-index (ser-encode-conses (car x) encoder))
               (cdr-index (ser-encode-conses (cdr x) encoder))

               ;; At this point, we've assigned indices to the car and cdr.
               ;; We've also written out all of the instructions needed to
               ;; generate them in the stream.  We can now assign an index to X
               ;; and write the instruction for rebuilding it:
               (free-index (ser-encoder-free-index encoder))
               (stream     (ser-encoder-stream encoder))

               ;; V2 change: we now write (car-index << 1) | (if honsp 1 0)
               ;; instead of just car-index.  Note that these fixnum
               ;; declarations are justified by the checking we do in
               ;; ser-encode-to-stream.
               (v2-car-index
                (if (hl-hspace-honsp-wrapper x)
                    (the fixnum (logior (the fixnum (ash car-index 1)) 1))
                  (the fixnum (ash car-index 1)))))
          (declare (type fixnum car-index cdr-index v2-car-index free-index))
          (setf (gethash x seen-cons) free-index)
          (ser-encode-nat v2-car-index stream)
          (ser-encode-nat cdr-index stream)
          (setf (ser-encoder-free-index encoder) (the fixnum (+ 1 free-index)))
          free-index)))))

(defmacro ser-decode-loop (version hons-mode)

  `(loop until (= (the fixnum stop) free) do

         (let ((first-index (ser-decode-nat stream)))
           (unless (typep first-index 'fixnum)
             (error "Consing instruction has non-fixnum first-index."))

           (let ((car-index ,(if (eq version :v1)
                                 'first-index
                               '(the fixnum (ash (the fixnum first-index) -1))))

                 (honsp     ,(cond ((eq hons-mode :always)
                                    't)
                                   ((and (eq hons-mode :smart)
                                         (not (eq version :v1)))
                                    '(logbitp 0 (the fixnum first-index)))
                                   (t
                                    nil)))

                 (cdr-index (ser-decode-nat stream)))

              ;; Performance testing suggests these bounds checks are
              ;; almost free.
              (unless (and (typep cdr-index 'fixnum)
                           (< (the fixnum car-index) free)
                           (< (the fixnum cdr-index) free))
                (error "Consing instruction has index out of bounds."))
              (let ((car-obj (svref arr (the fixnum car-index)))
                    (cdr-obj (svref arr (the fixnum cdr-index))))
                (setf (svref arr free)
                      (if honsp
                          (hons car-obj cdr-obj)
                        (cons car-obj cdr-obj)))
                (incf free))))))

(defun ser-decode-and-load-conses (hons-mode decoder stream)

  ;; The valid hons modes are:
  ;;   :always  - always hons regardless of hons bits
  ;;   :never   - never hons regardless of hons bits
  ;;   :smart   - hons only when hons bits are set (v2/3 only)
  ;;              smart does no honsing for v1 files

  (declare (type ser-decoder decoder))
  (let* ((len          (ser-decode-nat stream))
         (arr          (ser-decoder-array decoder))
         (free         (ser-decoder-free decoder))
         (version      (ser-decoder-version decoder))
         (stop         (+ free len)))
    (declare (type fixnum free))
    (ser-print? "; Decoding ~a consing instructions.~%" len)

    (unless (<= stop (length arr))
      ;; Like our other decoders, we only need a single bounds check to make
      ;; sure we won't overflow the array as we decode the conses.
      (error "Invalid serialized object, too many conses."))

    ;; This is a gross hack so that we have five different loops, optimized for
    ;; the different cases of hons-mode and file version.
    (if (eq version :v1)
        (if (eq hons-mode :always)
            (ser-decode-loop :v1 :always)
          (ser-decode-loop :v1 :never))
      ;; v2/3 are the same here
      (cond ((eq hons-mode :always)
             (ser-decode-loop :v2 :always))
            ((eq hons-mode :never)
             (ser-decode-loop :v2 :never))
            (t
             (ser-decode-loop :v2 :smart))))

    (setf (ser-decoder-free decoder) stop)))


; -----------------------------------------------------------------------------
;
;                              FAST ALISTS
;
; -----------------------------------------------------------------------------

; See also the Essay on Fast Alists in hons-raw.lisp.  The FAL-HT binds some
; alists to hash tables.  Some of these alists might be conses that we've just
; written out.  For each such alist, we just want to record its index.
;
; Our basic approach to restoring fast alists is as follows.  First, we encode
; the whole object -- we gather its atoms, assign indices to them, and write
; out all the consing instructions -- without any regard to which alists inside
; of it are fast.  Then we tack on some fast-alist information.
;
; Once the whole object has been encoded, we look at the FALTABLE from the Hons
; Space.  Recall that the FALTABLE binds alists to their backing hash tables.
; For each entry in the FALTABLE, we check whether the alist has been assigned
; an index in the encoder's SEEN-CONS table.  I.e., we check whether the alist
; was part of the object we just encoded.  If so, we write down a FAL
; instruction that describes how to rebuild the hash table.
;
; This seems pretty efficient: each FAL instruction is only two natural
; numbers, so the real added cost to encoding is just N hash table lookups,
; where N is the size of the FALTABLE, and the cost of encoding 2M naturals
; where M is the number of fast alists actually in the object.
;
; An encoded FAL instruction is a pair of natural numbers, INDEX and COUNT.
; The INDEX is just the looked up index of the alist, itself.  The COUNT is the
; hash-table-count of the backing hash table, so that when we recreate the hash
; table we can initialize it with approximately the correct size.
;
; So how does decoding work?  Since the FAL instructions come at the end of the
; object, we already have restored the whole object by the time we get to them.
; In other words, the INDEX that we read tells us where, in the decode array,
; we can find the alist that was fast.  Assuming we are using smart honsing or
; always honsing, then the keys of the ALIST should already be honsed, because
; it was a fast alist and so its keys had to be honses.  So all we need to do
; is rebuild the hash table for this alist and install it into the FAL table,
; which is very easy.
;
; We zero-terminate the FALS instead of writing down the number of FALS first.
; This is legitimate because 0 is always the index of NIL, and NIL cannot be
; bound in the FALTABLE, so there is no ambiguity.  It is desirable because as
; we encode, we do not know how many FAL instructions we will actually need to
; write out.  Likewise, as we decode we do not need to know how many FAL
; instructions will be processed.

(defun ser-encode-fals (encoder)
  (declare (type ser-encoder encoder))

; Q: Why include the hash table's count, when the decoder could just take the
; length of the alist instead?
;
; A: Since the alist can have shadowed pairs, so its length may not be a very
; good indication of the size we should use.  We could end up with a much
; larger hash table than we really need.
;
; Q: Why use the hash-table-count instead of the hash-table-size?
;
; A: If a fast alist has been saved in a book, we think it is relatively
; unlikely that it is going to be modified by a sub-book.  It seems more likely
; that it is some kind of lookup table that you intend to refer to over and
; over.

  (let* ((stream    (ser-encoder-stream encoder))
         (seen-cons (ser-encoder-seen-cons encoder))
         (fn
          (lambda (alist backing-hash-table)
            (let ((idx (gethash alist seen-cons)))
              (when idx
                (ser-encode-nat idx stream)
                (ser-encode-nat (hash-table-count backing-hash-table)
                                stream))))))
    (hl-faltable-maphash fn (hl-hspace-faltable-wrapper))
    (ser-encode-nat 0 stream)))

(defun ser-decode-and-restore-fals (decoder hons-mode stream)
  (declare (type ser-decoder decoder))

; Q: Why don't we restore when hons-mode is :never?
;
; A: The keys of a fast alist need to be honsed.  If we didn't smartly (or
; dumbly) make them honses when we built the conses, then we may not be able to
; convert the alist into a fast alist.  Sure, we could build a new alist that
; is EQUAL to the alist and make it fast, but then how would we install it?  It
; wouldn't work to smash the entry in the decoder array -- the other conses
; that rely on it have already been built.  The only way would be to walk
; through the object and replace all uses of the alist with the new alist, and
; that seems horribly slow.  At any rate, it doesn't seem unreasonable to say,
; if you're reading the file with no honses, you get no fast alists either.

  (let* ((array (ser-decoder-array decoder))
         (max   (length array))
         (index (ser-decode-nat stream)))
    (loop until (= index 0) do
          (unless (< index max)
            (error "FAL index to restore is too large!"))
          (unless (eq hons-mode :never)
            (let ((alist (svref array index))
                  (count (ser-decode-nat stream)))
              (hl-restore-fal-for-serialize alist count)))

; Notice that we make progress reading nats from stream even if hons-mode is
; :never; we just ignore those nats!

          (setq index (ser-decode-nat stream)))))

(defun ser-encode-atoms (encoder)
  (declare (type ser-encoder encoder))

; It's sort of silly for this to be its own function, but it makes a convenient
; target for timing.

  (let ((stream (ser-encoder-stream encoder)))
    (ser-encode-nats      (ser-encoder-naturals encoder)  stream)
    (ser-encode-rats      (ser-encoder-rationals encoder) stream)
    (ser-encode-complexes (ser-encoder-complexes encoder) stream)
    (ser-encode-chars     (ser-encoder-chars encoder)     stream)
    (ser-encode-strs      (ser-encoder-strings encoder)   stream)
    (ser-encode-packages  (ser-encoder-symbol-al encoder) stream)))

(defun ser-encode-to-stream (obj stream)

; Serialize the OBJ and write it to the stream.  This writes "everything from
; magic number to magic number."  Note that it does NOT include the #Z prefix,
; which is needed if you're going to read the object back in.

  (let ((encoder (make-ser-encoder :stream stream))
        starting-free-index-for-conses
        total-number-of-objects
        max-index
        nconses)
    (declare (dynamic-extent encoder))

    ;; Make sure the hons space is initialized
    (hl-maybe-initialize-default-hs-wrapper)
    (ser-time? (ser-gather-atoms obj encoder))

    (setq nconses (hash-table-count (ser-encoder-seen-cons encoder)))

    (unless (typep (ash (+ 2 ;; to account for T and NIL
                           (hash-table-count (ser-encoder-seen-sym encoder))
                           (hash-table-count (ser-encoder-seen-eql encoder))
                           (hash-table-count (ser-encoder-seen-str encoder))
                           nconses)
                        1)
                   'fixnum)
      ;; This check ensures that all indices will be fixnums.  The sum above
      ;; may actually exceed the actual maximum index we will have, because
      ;; EQUAL-but-not-EQ strings will be removed.  But it is at least as large
      ;; as the maximum index, so if it is a fixnum then all indices are
      ;; fixnums.  In V1 we just checked if the sum was a fixnum.  In V2 we
      ;; need to shift it since indices get shifted in the file.  Note that we
      ;; rely on this check in ser-encode-conses.
      (error "Maximum index exceeded."))

    (ser-time? (ser-make-atom-map encoder))
    (setq starting-free-index-for-conses (ser-encoder-free-index encoder))

    (ser-encode-magic stream)

    (setq total-number-of-objects
          (the fixnum (+ starting-free-index-for-conses nconses)))

    (ser-encode-nat (cond ((eq obj nil)
                           0)
                          (t
                           (- total-number-of-objects 1)))
                    stream)

    (ser-time? (ser-encode-atoms encoder))
    (ser-encode-nat nconses stream)
    (setq max-index (ser-time? (ser-encode-conses obj encoder)))
    (ser-time? (ser-encode-fals encoder))

    (unless (and (equal (ser-encoder-free-index encoder)
                        total-number-of-objects)
                 (or (equal max-index (- (ser-encoder-free-index encoder) 1))
                     ;; in v2, max-index can be 0 and 1 also, for nil or t.
                     ;; if it happens to be t, then it's still going to be one
                     ;; less than the max free index.
                     (equal max-index 0)))
      (error "Sanity check failed in ser-encode-to-stream!~% ~
                - final-free-index is ~a~% ~
                - total-number-of-objects is ~a~% ~
                - max-index is ~a~%"
             (ser-encoder-free-index encoder)
             total-number-of-objects
             max-index))

    (ser-encode-magic stream)))

(defun ser-decode-and-load-atoms (check-packagesp hons-mode decoder stream)
  (declare (type ser-decoder decoder))
  (ser-decode-and-load-nats decoder stream)
  (ser-decode-and-load-rats decoder stream)
  (ser-decode-and-load-complexes decoder stream)
  (ser-decode-and-load-chars decoder stream)
  (ser-decode-and-load-strs hons-mode decoder stream)
  (ser-decode-and-load-packages check-packagesp decoder stream))

(defun ser-make-array-wrapper (size)

; Sol Swords reported in July 2017 that with SBCL, he has provided the
; following safety-3 wrapper to avoid some crashes in ser-decode-from-stream.

  #+sbcl (declare (optimize (safety 3)))
  (make-array size))

(defun ser-decode-from-stream (check-packagesp hons-mode stream)

; Warning: If you change the input or output signature of this function, change
; its (declaim (ftype ...)) form in acl2-fns.lisp.

; Read a serialized object from the stream.  This reads "everything from magic
; number to magic number."  Note that it does NOT expect there to be a #Z
; prefix.

  (let* ((version  (ser-decode-magic stream))
         (size/idx (ser-decode-nat stream))
         (arr-size (if (or (eq version :v2)
                           (eq version :v3))
                       (cond ((eq size/idx 0)
                              2)
                             (t
                              (+ size/idx 1)))
                     size/idx))
         (final-obj (if (or (eq version :v2)
                            (eq version :v3))
                        size/idx
                      (- arr-size 1))))

    (unless (typep arr-size 'fixnum)
      (error "Serialized object is too large."))

    (let* ((arr     (ser-make-array-wrapper arr-size))
           (decoder (make-ser-decoder :array arr
                                      :free 0
                                      :version version)))
      (declare (dynamic-extent arr decoder)
               (type ser-decoder decoder))

      (when (or (eq version :v2)
                (eq version :v3))
        (setf (aref arr 0) nil)
        (setf (aref arr 1) t)
        (setf (ser-decoder-free decoder) 2))

      (ser-print? "; Decoding serialized object of size ~a.~%" arr-size)
      (ser-time? (ser-decode-and-load-atoms check-packagesp hons-mode decoder
                                            stream))
      (ser-time? (ser-decode-and-load-conses hons-mode decoder stream))

      (when (eq version :v3)
        (ser-decode-and-restore-fals decoder hons-mode stream))

      (unless (eq (ser-decode-magic stream) version)
        (error "Invalid serialized object, magic number mismatch."))

      (unless (= (ser-decoder-free decoder) arr-size)
        (error "Invalid serialized object.~% ~
                 - Decode-free is ~a~%
                 - Arr-size is ~a."
               (ser-decoder-free decoder) arr-size))

      ;; Return the top object.
      (svref arr final-obj))))
