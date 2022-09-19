; Fastnumio - Efficient hex string I/O ops for Common Lisp streams
; Copyright (C) 2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "FASTNUMIO")

;(declaim (optimize (safety 3) (speed 0) (space 0)))
(declaim (optimize (speed 3) (space 1) (safety 0)))

; ----------------------------------------------------------------------------
;
;                          Supporting Utilities
;
; ----------------------------------------------------------------------------

(assert (< (char-code #\0) (char-code #\A)))
(assert (< (char-code #\A) (char-code #\a)))

(declaim (inline hex-digit-val))
(defun hex-digit-val (x)
  (declare (type character x))
  (let ((code (char-code x)))
    (declare (type fixnum code))
    (cond ((<= code #.(char-code #\9))
           (and (<= #.(char-code #\0) code)
                (the fixnum (- code #.(char-code #\0)))))
          ((<= code #.(char-code #\F))
           (and (<= #.(char-code #\A) code)
                (the fixnum (- code #.(- (char-code #\A) 10)))))
          (t
           (and (<= code #.(char-code #\f))
                (<= #.(char-code #\a) code)
                (the fixnum (- code #.(- (char-code #\a) 10))))))))



; ----------------------------------------------------------------------------
;
;                            Fast Hex Reading
;
; ----------------------------------------------------------------------------

; (read-hex stream) reads a hex value (e.g., FF9900) from stream and returns it
; as an integer, or returns NIL to indicate the stream does not start with a
; hex value.  More details:
;
;   - We accept digits in either case, e.g., 37ff or 37FF or 37Ff are all fine.
;
;   - Any leading zeroes are accepted and ignored.
;
;   - No hex prefixes are expected or accepted, e.g., if your stream contains
;     things like #FF9900, 0xFF9900, or #xFF9900, then you will need to do
;     something else to strip these leading #, 0x, or #x prefixes first.
;
;   - No underscores or whitespace within the number are accepted.
;
; Internally we read things using read-char.
;
;   - Although read-sequence is faster, it seems difficult to provide a nice
;     interface if we use it since it may read past the number we're parsing
;
;   - Read-line seems to be using a lot of memory.  CCL's read-line also seems
;     very slow, i.e., ~6x slower than SBCL's.  So it seems better to read the
;     stream directly instead of parse a string.  (Well, we could provide
;     functions for both, of course.)
;
; We also prefer to use unread-char instead of peek-char.  This appears to be
; quite a bit faster on both CCL and SBCL.


; The general idea behind our generic read-hex function is:
;
;   (1) read in as many hex characters (nibbles) as we can into an
;       (ideally stack-allocated) array,
;   (2) merge the nibbles in this array into a fixnum/bignum.
;
; To optimize for Lisps where we have 60+-bit fixnums, we merge the nibbles
; into contiguous, 60-bit chunks.  We then merge those chunks together, using
; something like;
;
;   finalans |= chunk << n*60
;
; This merging results in ephemeral/garbage bignums, which is unfortunate.
; However, it requires only one ephemeral bignum for each 60-bits of data,
; whereas merging the nibbles naively would require a bignum for each 4-bit
; chunk of data.

(defun assemble-nibbles-60 (pos nibarr)
  (declare (type (array (unsigned-byte 4) *) nibarr)
           (type fixnum pos))
  ;; POS is initially how many valid nibbles we have.  I.e., nibarr[pos-1]
  ;; is the last valid nibble.
  (let ((finalans 0)  ;; Accumulator for the answer (perhaps a bignum)
        (chunkidx 0)  ;; Offset into finalans for this chunk (0, 60, ...)
        (chunk    0)  ;; Value of the current chunk we're assembling
        (chunkpos 0)  ;; Nibble offset into the current chunk (0, 4, ...)
        )
    (declare (type (unsigned-byte 60) chunk)
             (type (unsigned-byte 8) chunkpos)
             (type fixnum chunkidx)
             (type unsigned-byte finalans))
    (loop do
          ;(format t "FINAL ~x, CHUNK ~x, CP ~d, CIDX ~d, POS ~d~%"
          ;        finalans chunk chunkpos chunkidx pos)
          (when (eql pos 0)
            (loop-finish))
          (when (eql chunkpos 60)
            ;; Merge the chunk we've gotten into the final answer.   -- ephemeral bignums :(
            ;; finalans |= (chunk << chunkidx * 60)
            (setf finalans
                  (the unsigned-byte
                       (logior (the unsigned-byte finalans)
                               (the unsigned-byte (ash chunk (the fixnum chunkidx))))))
            ;; Start a new chunk.
            (incf chunkidx 60)
            (setq chunk 0)
            (setq chunkpos 0))
          (decf pos)
          ;(format t "This nibble: ~x~%" (aref nibarr pos))
          (setq chunk ;; chunk |= nibarr[pos] << chunkpos        -- fixnum on 60+-bit impls
                (the (unsigned-byte 60)
                     (logior (the (unsigned-byte 60) chunk)
                             (the (unsigned-byte 60)
                                  (ash (the (unsigned-byte 4) (aref nibarr pos))
                                       (the (unsigned-byte 8) chunkpos))))))
          (incf chunkpos 4))
    ;(format t "Final assembly.  FINAL ~x, CHUNK ~x, CIDX ~d~%" finalans chunk chunkidx)
    (let ((ans (the unsigned-byte
                    (logior (the unsigned-byte finalans)
                            (the unsigned-byte (ash chunk (the fixnum chunkidx)))))))
      ;(format t "ANS: ~x~%" ans)
      ans)))

(defmacro nib-array-init-size () 128)

(declaim (inline read-nibbles))
(defun read-nibbles (nibarr stream)
  ;; Returns (values some-nibble-p end nibarr)
  ;;   some-nibble-p: were there any valid hex chars, including leading zeroes?
  ;;   end:           end of the valid area of the nibble array
  ;;                    counts how many nibbles we found, omitting leading nibbles
  ;;   nibarr:        updated nibble array
  (declare (type (array (unsigned-byte 4) *) nibarr))
  (let* ((end 0)
         (char)
         (nibble)
         (nibarrlen (nib-array-init-size))
         (some-nibble-p nil))
    (declare (type fixnum end nibarrlen)
             (type (array (unsigned-byte 4) *) nibarr))
    ;; Begin by skipping any leading 0 digits.  (They screw up length-based
    ;; computations.)
    (loop do
          (setq char   (read-char stream nil))
          (setq nibble (and char (hex-digit-val char)))
          (unless nibble
            (loop-finish))
          (setq some-nibble-p t)
          (unless (eql nibble 0)
            (loop-finish)))

    ;; Read as many hex digits as are available into the nibble array.  We
    ;; don't know how many digits we will need, so grow the array if necessary.
    (loop do
          (unless nibble
            (loop-finish))
          (when (eql end nibarrlen)
            ;; Need more space, grow the array.  This will generally ruin stack
            ;; allocation.  However, we can at least get the benefit of a stack
            ;; allocation for the initial array, which will be sufficient for
            ;; numbers up to some reasonable size.
            (setq nibarrlen (ash nibarrlen 1))
            ;(format t "Growing array to ~s~%" nibarrlen)
            (setq nibarr (adjust-array nibarr nibarrlen)))
          (setf (aref nibarr end) nibble)
          ;; advance to next character
          (incf end)
          (setq char   (read-char stream nil))
          (setq nibble (and char (hex-digit-val char))))

    ;; Unread the last (non-hex) character.  Special case: char is NIL exactly
    ;; when we're at EOF, in which case we don't need to unread anything.
    (when char (unread-char char stream))
    (values some-nibble-p end nibarr)))

(defun read-hex (stream)
  (let ((nibarr (make-array (nib-array-init-size)
                            :element-type '(unsigned-byte 4))))
    (declare (dynamic-extent nibarr)
             (type (array (unsigned-byte 4) *) nibarr))
    (multiple-value-bind
     (some-nibble-p end nibarr)
     (read-nibbles nibarr stream)
     (declare (type fixnum end)
              (type (array (unsigned-byte 4) *) nibarr))
     (when (eql end 0)
       (return-from read-hex
                    (if some-nibble-p
                        ;; No real digits but at least some zero digits,
                        ;; so the number is 0.
                        0
                      ;; Failed to read any hex digits.  Just fail.
                      nil)))
     ;; Found hex digits and already decoded their nibbles into nibarr.  The
     ;; nibble in nibarr[0] is the most significant.  I now want to chunk them
     ;; up into fixnum-sized blobs.
     (assemble-nibbles-60 end nibarr))))





; ----------------------------------------------------------------------------
;
;                      Scary Unsafe Hex Reading
;
; ----------------------------------------------------------------------------

; To try to get better performance, we go under the hood and create bignums
; from whole cloth.  We can reuse the nibble array stuff from above and just
; write a custom function to combine the nibbles.
;
; We start with some supporting code for chunking nibbles into u32s.  This
; code will be useful on both CCL (where bignums are made up out of 32-bit
; chunks) and on SBCL (where they are made of 64-bit chunks).
;
; Our starting point is the nibble array, which is populated from [0...END)
; with valid hex nibbles, with the most significant nibble at nibarr[0].  It
; is easy to see how many 64/32-bit chunks we will need: we can fit 16/8
; nibbles into such a chunk.  The only trickiness is that we will need to
; construct the least significant 32-bit chunks from the END of the nibble
; array.
;
; Example: suppose we found 11 nibbles.  Then there are nibbles in nibarr[0]
; through nibarr[10].  In this case, the least significant u32 is found in
; nibarr[3]...nibarr[10], with its most significant nibble in nibarr[3] and its
; least significant nibble in nibarr[10].

(defun u32-from-nibarr (end nibarr)
  ;; This extracts up to 8 nibbles (32 bits) from the nibble array, reading
  ;; backwards from index END-1.  END should not be zero but may be the
  ;; array length.
  (declare (type fixnum end)
           (type (array (unsigned-byte 4) *) nibarr))
  (let ((ans 0)
        (start (max 0 (- end 8))))
    (declare (type (unsigned-byte 32) ans)
             (type fixnum start))
    (loop do
          (setq ans (the (unsigned-byte 32)
                         (logior (the (unsigned-byte 32) (ash ans 4))
                                 (aref nibarr start))))
          (incf start)
          (when (eql start end)
            (loop-finish)))
    ans))

;; Basic demo/test
(let ((nibarr (make-array 16 :element-type '(unsigned-byte 4))))
  ;; Populate nibarr with FEDCBA98765
  (setf (aref nibarr 0)  #xf)
  (setf (aref nibarr 1)  #xe)
  (setf (aref nibarr 2)  #xd)
  (setf (aref nibarr 3)  #xc)
  (setf (aref nibarr 4)  #xb)
  (setf (aref nibarr 5)  #xa)
  (setf (aref nibarr 6)  #x9)
  (setf (aref nibarr 7)  #x8)
  (setf (aref nibarr 8)  #x7)
  (setf (aref nibarr 9)  #x6)
  (setf (aref nibarr 10) #x5)
  (assert (equal (u32-from-nibarr 11 nibarr) #xCBA98765))
  (assert (equal (u32-from-nibarr 10 nibarr) #xDCBA9876))
  (assert (equal (u32-from-nibarr 9 nibarr)  #xEDCBA987))
  (assert (equal (u32-from-nibarr 8 nibarr)  #xFEDCBA98))
  (assert (equal (u32-from-nibarr 7 nibarr)  #xFEDCBA9))
  (assert (equal (u32-from-nibarr 6 nibarr)  #xFEDCBA))
  (assert (equal (u32-from-nibarr 5 nibarr)  #xFEDCB))
  (assert (equal (u32-from-nibarr 4 nibarr)  #xFEDC))
  (assert (equal (u32-from-nibarr 3 nibarr)  #xFED))
  (assert (equal (u32-from-nibarr 2 nibarr)  #xFE))
  (assert (equal (u32-from-nibarr 1 nibarr)  #xF))
  )

#+(and sbcl 64-bit)
(progn
  ;; Basic sanity checking to see if we still understand the internal API.
  (assert (equal sb-bignum::digit-size 64))
  (assert (equal (sb-bignum::%bignum-ref (1- (expt 2 80)) 0) (1- (expt 2 64))))
  (assert (equal (sb-bignum::%bignum-ref (1- (expt 2 80)) 1) (1- (expt 2 16))))
  (assert (typep (1- (expt 2 64)) 'sb-bignum::bignum-element-type))
  (let* ((x      #xfeedf00ddeadd00ddeadbeef99998888)
         (digit  (sb-bignum::%bignum-ref x 0))
         (high32 (sb-bignum::%digit-logical-shift-right digit 32))
         (low32  (logand digit #xFFFFFFFF)))
    (assert (typep high32 'fixnum))
    (assert (typep low32 'fixnum))
    (assert (typep high32 '(unsigned-byte 32)))
    (assert (typep low32 '(unsigned-byte 32)))
    (assert (equal high32 #xdeadbeef))
    (assert (equal low32 #x99998888))))

#||

;; This is just scratchwork that may be useful when trying to understand SBCL's
;; bignum representation.

#+(and sbcl 64-bit)
(defun construct-u64-from-u32s (high low)
  (declare (type (unsigned-byte 32) high low))
  (if (logbitp 31 high)
      ;; Top bit is 1, so we need an extra digit to avoid treating this as unsigned.
      (let ((ans   (sb-bignum:%allocate-bignum 2))
            (digit (sb-bignum::bignum-logical-ior (sb-bignum::bignum-ashift-left high 32) low)))
        (setf (sb-bignum::%bignum-ref ans 0) digit)
        (setf (sb-bignum::%bignum-ref ans 1) 0)
        ans)
    ;; The top bit is 0, so we don't need an extra digit.
    (let ((ans   (sb-bignum:%allocate-bignum 1))
          (digit (sb-bignum::bignum-logical-ior (sb-bignum::bignum-ashift-left high 32) low)))
      (setf (sb-bignum::%bignum-ref ans 0) digit))))

(defun my-test (n)
  (declare (type (unsigned-byte 64) n))
  (let* ((high (ash n -32))
         (low  (logand n (1- (expt 2 32))))
         (ans  (construct-u64-from-u32s high low)))
    (assert (typep ans '(unsigned-byte 64)))
    (assert (equal ans n))
    (if (typep ans 'fixnum)
        (format t "Fixnum~%")
      (format t "Bignum~%"))))

(my-test (1- (expt 2 64)))
(my-test #x1000000000000000)

(loop for i from 1 to 10000 do (my-test i))
(loop for i from (- (expt 2 62) 1000) to (+ (expt 2 62) 1000) do (my-test i))
(loop for i from (- (expt 2 63) 1000) to (+ (expt 2 63) 1000) do (my-test i))
(loop for i from (- (expt 2 64) 1000) to (1- (expt 2 64)) do (my-test i))


||#

#+(and sbcl 64-bit)
(defun bignum-from-nibarr (end nibarr)
  (declare (type (array (unsigned-byte 4) *) nibarr)
           (type fixnum end))
  (let* ((bits-needed (* 4 end))
         (u64s-needed (+ 1 (ash (1- bits-needed) -6)))
         (u64s-for-normalize u64s-needed)
         (low32 0)
         (high32 0)
         (u64pos 0)
         (ans))
    (declare (type (unsigned-byte 32) low32 high32)
             (type fixnum u64pos))
;    (format t "~d nibbles, so ~d bits needed, so alloc ~d u64s~%" end bits-needed u64s-needed)
;    (format t "End mod 16 is ~d~%" (logand end #xF))
;    (format t "Most significant nibble is ~d~%" (aref nibarr 0))

    (cond ((and (eql (the (unsigned-byte 4) (logand end #xF)) 0)
                (> (the (unsigned-byte 4) (aref nibarr 0)) 7))
           ;; The number of nibbles we have is a multiple of 16, and the most
           ;; significant nibble (nibarr[0]) is large enough that its most
           ;; significant bit is set.  We need an extra, leading zero bignum
           ;; digit because otherwise this will look like a signed number.

;           (format t "Need extra digit to avoid signed result.~%")
           (setq ans (sb-bignum:%allocate-bignum (+ 1 u64s-needed)))
           (setf (sb-bignum::%bignum-ref ans u64s-needed) 0)
           (incf u64s-for-normalize))
          (t
           ;; Otherwise, we don't need an extra digit, so just allocate the
           ;; number of digits that we actually do need.

;           (format t "No extra digit is necessary to avoid signedness.~%")
           (setq ans (sb-bignum:%allocate-bignum u64s-needed))))

    (loop do
;          (format t "looping, end = ~d~%" end)
          (when (eql end 0)
            (loop-finish))
;          (format t "reading low~%")
          (setq low32 (u32-from-nibarr end nibarr))
          (setq end (max 0 (- end 8)))
;          (format t "got low = #x~x, end is now ~d~%" low32 end)
          (setq high32 (if (eql end 0)
                           0
                         (u32-from-nibarr end nibarr)))
          (setq end (max 0 (- end 8)))
;          (format t "got high = #x~x, end is now ~d~%" high32 end)
;          (format t "Installing chunk ~d <-- #x~x,#x~x~%" u64pos high32 low32)
          (setf (sb-bignum::%bignum-ref ans u64pos)
                (logior (sb-bignum::%ashl high32 32)
                        low32))
          (incf u64pos))

    ;; This normalization apparently handles the case where the bignum we are
    ;; constructing isn't necessary and we can just coerce it into a fixnum.
    (setq ans (sb-bignum::%normalize-bignum ans u64s-for-normalize))
    ;;(assert (equal u64pos u64s-needed))
;    (format t "Ans is #x~x~%" ans)
;    (format t "Type-of ans is ~s~%" (type-of ans))
    ans))

(defun scary-unsafe-read-hex (stream)
  (let ((nibarr (make-array (nib-array-init-size)
                            :element-type '(unsigned-byte 4))))
    (declare (dynamic-extent nibarr)
             (type (array (unsigned-byte 4) *) nibarr))
    (multiple-value-bind
     (some-nibble-p end nibarr)
     (read-nibbles nibarr stream)
     (declare (type fixnum end)
              (type (array (unsigned-byte 4) *) nibarr))
     (when (eql end 0)
       (return-from scary-unsafe-read-hex
                    (if some-nibble-p
                        ;; No real digits but at least some zero digits,
                        ;; so the number is 0.
                        0
                      ;; Failed to read any hex digits.  Just fail.
                      nil)))
     #+(not (and sbcl 64-bit))
     (assemble-nibbles-60 end nibarr)
     #+(and sbcl 64-bit)
     (if (< end 16)
         ;; Don't bother with any bignum nonsense
         (assemble-nibbles-60 end nibarr)
       (bignum-from-nibarr end nibarr)))))

;; (defun single-test (n)
;;   (let* ((str (let ((stream (make-string-output-stream)))
;;                 (format stream "~x" n)
;;                 (get-output-stream-string stream)))
;;          (ans (let ((stream (make-string-input-stream str)))
;;                 (scary-unsafe-read-hex stream))))
;;     (equal n ans)))





; ----------------------------------------------------------------------------
;
;                        Basic Correctness Tests
;
; ----------------------------------------------------------------------------



(let ((tests (append
              (list #xbeef
                    #x1beef
                    #x12beef
                    #x123beef
                    #xdeadbeef
                    #x1deadbeef
                    #x12deadbeef
                    #x123deadbeef
                    #x1234deadbeef
                    #x12345deadbeef
                    #x123456deadbeef
                    #x1234567deadbeef
                    (- (expt 2 60) 3)
                    (- (expt 2 60) 2)
                    (- (expt 2 60) 1)

                    #x5544FEDCBA9876543210

                    (expt 2 60)
                    (+ (expt 2 60) 1)
                    (+ (expt 2 60) 2)
                    (+ (expt 2 60) 3)
                    (+ (expt 2 60) 4)
                    (+ (expt 2 60) 15)
                    (+ (expt 2 60) 16)
                    (+ (expt 2 60) #xf0)
                    (expt 2 64)
                    (1- (expt 2 64))
                    (expt 2 80)
                    (1- (expt 2 80)))
              (loop for i from 0 to 100 collect i)
              (loop for i from 0 to 200 collect (ash 1 i))
              (loop for i from 0 to 200 collect (1- (ash 1 i)))
              (loop for n from 1 to 200 append  ;; borders near powers of 2
                    (loop for i from (max 0 (- (expt 2 n) 10))
                                  to        (+ (expt 2 n) 10)
                                  collect i))
              (loop for i from 1 to 100 collect (random (expt 2 1024)))
              )))
  (loop for test in tests do
        ;(format t "Testing ~x~%" test)
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (read-hex stream)))
               (v2 (let ((stream (make-string-input-stream str)))
                     (scary-unsafe-read-hex stream))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1))
          (or (equal test v2)
              (error "V2 Failure: ~x --> str ~s, v2 ~x" test str v2)))

        ;; Test leading zero
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "0~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (read-hex stream)))
               (v2 (let ((stream (make-string-input-stream str)))
                     (scary-unsafe-read-hex stream))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1))
          (or (equal test v2)
              (error "V2 Failure: ~x --> str ~s, v2 ~x" test str v2)))

        ;; Two leading zeroes
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "00~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (read-hex stream)))
               (v2 (let ((stream (make-string-input-stream str)))
                     (scary-unsafe-read-hex stream))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1))
          (or (equal test v2)
              (error "V2 Failure: ~x --> str ~s, v2 ~x" test str v2))))

  :ok)




#||

; I believe that we could do much better if there were some way to directly
; construct a bignum.  Below is a fledgling attempt to write a function to
; do this for X86-64 CCL, but I don't think it's working quite yet, and
; it is certainly scary and fragile to do this.

#+(and Clozure x86-64)
(progn
  ;; Make sure we still properly understand the fixnum/bignum boundary.
  (assert (typep (1- (expt 2 60)) 'fixnum))
  (assert (not (typep (expt 2 60) 'fixnum))))


;; #+(and Clozure x86-64)
;; (defun assemble-nibbles-ccl64 (pos nibarr)
;;   (declare (type (array (unsigned-byte 4) *) nibarr)
;;            (type fixnum pos))
;;   (if (<= pos 15)
;;       ;; Not going to need a bignum anyway, so no need for anything fancy.
;;       (progn
;;         (format t "Falling back to assemble-nibbles-60 because there are only ~d chars.~%" pos)
;;         (assemble-nibbles-60 pos nibarr))

;;     (let ((finalans
;;            ;; Create a bignum of the appropriate length.  We'll smash its
;;            ;; bits in a moment.  We need room for 4*pos nibbles.
;;            (ccl::%allocate-bignum the unsigned-byte (ash 1 (1- (the fixnum (ash pos 2))))))
;;           (chunkidx 0)  ;; Offset into finalans for this chunk (0, 1, ...)
;;           (chunk    0)  ;; Value of the current chunk we're assembling
;;           (chunkpos 0)  ;; Nibble offset into the current chunk (0, 4, ...)
;;           )
;;       (declare (type (unsigned-byte 32) chunk)
;;                (type (unsigned-byte 8) chunkpos)
;;                (type fixnum chunkidx)
;;                (type unsigned-byte finalans))
;;       (format t "Shift thing is ~x~%" finalans)
;;       (format t "VECSIZE is ~d~%" (ccl::uvsize finalans))
;;       (loop do
;;             (format t "FINAL ~x, CHUNK ~x, CP ~d, CIDX ~d, POS ~d~%"
;;                     finalans chunk chunkpos chunkidx pos)
;;             (when (eql pos 0)
;;               (loop-finish))
;;             (when (eql chunkpos 32)
;;               ;; Merge the chunk we've gotten into the final answer.
;;               (setf (ccl::uvref finalans chunkidx) chunk)
;;               ;; Start a new chunk.
;;               (incf chunkidx 1)
;;               (setq chunk 0)
;;               (setq chunkpos 0))
;;             (decf pos)
;;             (format t "This nibble: ~x~%" (aref nibarr pos))
;;             (setq chunk ;; chunk |= nibarr[pos] << chunkpos
;;                   (the (unsigned-byte 32)
;;                        (logior (the (unsigned-byte 32) chunk)
;;                                (the (unsigned-byte 32)
;;                                     (ash (the (unsigned-byte 4) (aref nibarr pos))
;;                                          (the (unsigned-byte 8) chunkpos))))))
;;             (incf chunkpos 4))

;;     (format t "Final assembly.  FINAL ~x, CHUNK ~x, CIDX ~d~%" finalans chunk chunkidx)
;;     (setf (ccl::uvref finalans chunkidx) chunk)
;;     (format t "After final installation: ~x~%" finalans)
;;     finalans)))


||#












