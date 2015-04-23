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

(declaim (optimize (speed 3) (space 1) (safety 0)))

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
; Internally we read things using read-char...
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

; General idea:
;  - Read in up to 60 bits at a time.
;  - Turn that 60 bits into a fixnum.
;  - Merge the 60-bit chunks together.

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

(defun assemble-nibbles-60 (pos nibarr)
  (declare (type (array (unsigned-byte 4) *) nibarr)
           (type fixnum pos))
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
            ;; Merge the chunk we've gotten into the final answer.
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
          (setq chunk ;; chunk |= nibarr[pos] << chunkpos
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

(defun read-hex (stream)
  (let* ((pos    0)
         (char)
         (nibble)
         (nibarrlen 128)
         (some-nibble-p nil)
         (nibarr (make-array nibarrlen :element-type '(unsigned-byte 4))))
    (declare (dynamic-extent nibarr)
             (type fixnum pos)
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
          (when (eql pos (length nibarr))
            ;; Need more space, grow the array.  Unfortunately I don't think
            ;; CCL can stack-allocate the resized array.  However, we will at
            ;; least get the benefit of a stack allocation for the initial
            ;; array, which is sufficient for numbers up to 512 bits.  It would
            ;; be nice to instead just use a global array, but that wouldn't be
            ;; thread-safe.
            (setq nibarrlen (ash nibarrlen 1))
            ;(format t "Growing array to ~s~%" nibarrlen)
            (setq nibarr (adjust-array nibarr nibarrlen)))
          (setf (aref nibarr pos) nibble)
          ;; advance to next character
          (incf pos)
          (setq char   (read-char stream nil))
          (setq nibble (and char (hex-digit-val char))))

    ;; Unread the last (non-hex) character.  Special case: char is NIL exactly
    ;; when we're at EOF, in which case we don't need to unread anything.
    (when char (unread-char char stream))

    (when (eql pos 0)
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
    ;;    #-(and Clozure x86-64)
    (assemble-nibbles-60 pos nibarr)
    ;; #+(and Clozure x86-64)
    ;; (assemble-nibbles-ccl64 pos nibarr)))
    ))


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
              (loop for i from 1 to 100 collect (random (expt 2 64)))
              (loop for i from 1 to 100 collect (random (expt 2 1024))))))
  (loop for test in tests do
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (progn ;; (format t "Testing ~s~%" str)
                            (read-hex stream)))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1)))
        ;; Test leading zero
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "0~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (read-hex stream))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1)))
        ;; Two leading zeroes
        (let* ((str (let ((stream (make-string-output-stream)))
                      (format stream "00~x" test)
                      (get-output-stream-string stream)))
               (v1 (let ((stream (make-string-input-stream str)))
                     (read-hex stream))))
          (or (equal test v1)
              (error "V1 Failure: ~x --> str ~s, v1 ~x" test str v1))))

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
