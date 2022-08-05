(in-package 3bz)

#++(ql:quickload '3bz)
(defstruct-cached (deflate-state (:conc-name ds-))
  ;; current state machine state
  (current-state :start-of-block)

  ;; set when reading last block in stream
  (last-block-flag nil :type (or nil t))

  ;; storage for dynamic huffman tree, modified for each dynamic block
  (dynamic-huffman-tree (cons (make-huffman-tree) (make-huffman-tree))
                        :type (cons huffman-tree huffman-tree))
  ;; reference to either dynamic-huffman-tree or *static-huffman-tree*
  ;; depending on curret block
  (current-huffman-tree +static-huffman-trees+
                        :type (cons huffman-tree huffman-tree))
  ;; dynamic huffman tree parameters being read
  (dht-hlit 0 :type  (unsigned-byte 10))
  (dht-hlit+hdist 0 :type (unsigned-byte 10))
  (dht-hclen 0 :type (unsigned-byte 4))
  (dht-len-codes (make-array 19 :element-type '(unsigned-byte 4)
                                :initial-element 0)
                 :type (simple-array (unsigned-byte 4) (19)))

  (dht-len-tree (make-huffman-tree)) ;; fixme: reduce size
  (dht-lit/len/dist (make-array (+ 288 32) :element-type '(unsigned-byte 4)
                                           :initial-element 0)
                    :type code-table-type)
  (dht-lit/len/dist-index 0 :type (mod 320))
  (dht-last-len #xff :type octet)

  ;; number of bytes left to copy (for uncompressed block, or from
  ;; history in compressed block)
  (bytes-to-copy 0 :type (unsigned-byte 16))
  (copy-offset 0 :type (unsigned-byte 16))

  ;; bitstream state: we read up to 64bits at a time to try to
  ;; minimize time spent interacting with input source relative to
  ;; decoding time.
  (partial-bits 0 :type (unsigned-byte 64))
  ;; # of valid bits remaining in partial-bits (0 = none)
  (bits-remaining 0 :type (unsigned-byte 7))

  ;; output state
  (output-offset 0 :type fixnum) ;; next octet to write
  (output-buffer (make-array 0 :element-type 'octet)
                 :type octet-vector)
  ;; window (only used if output buffer is filled mid-decode,
  ;; otherwise output buffer is used directly)
  (window nil :type (or null octet-vector))

;;; status for caller:

  ;; true if reached end of final block, and 'output' contains all
  ;; decompressed data
  (finished nil :type (or nil t))
  ;; true if there isn't enough space in 'output' to finish
  (output-overflow nil :type (or nil t))
  ;; true if input is empty (or incomplete) without reaching end of
  ;; final block
  (input-underrun nil :type (or nil t)))


(defmacro state-machine ((state) &body tagbody)
  (let ((tags (loop for form in tagbody when (atom form) collect form)))
    `(symbol-macrolet ((.current-state ,(list nil)))
       (macrolet ((next-state (next-state)
                    `(progn
                       (setf current-state ',next-state)
                       (go ,next-state)))
                  (%enter-state (s &environment env)
                    (setf (car (macroexpand '.current-state env)) s)
                    `(progn #++(format t "~s~%" ',s)))
                  (restart-state (&environment env)
                    `(go ,(car (macroexpand '.current-state env)))))
         (tagbody
            ;; possibly could do better than a linear search here, but
            ;; if state machine is being interrupted often enough to
            ;; matter, it probably won't matter anyway :/ at most,
            ;; maybe define more commonly interrupted states earlier
            (ecase (ds-current-state ,state)
              ,@(loop for i in tags
                      collect `(,i (go ,i))))
            ,@(loop for f in tagbody
                    collect f
                    when (atom f)
                      collect `(%enter-state ,f)))))))


(defparameter *stats* (make-hash-table))
(defun-with-reader-contexts decompress-deflate (read-context state)
    (read-context)
  (declare (optimize speed))
  (with-cached-state (state deflate-state save-state
                       partial-bits bits-remaining
                       current-huffman-tree
                       output-offset
                       current-state
                       bytes-to-copy
                       output-buffer)
    (setf output-overflow nil
          input-underrun nil)
    (macrolet ((bits* (&rest sizes)
                 ;; only valid for fixed sizes, but possibly should
                 ;; allow passing +constants+ and try to eval them
                 ;; at macroexpansion instead of requiring numbers?
                 (let ((n (reduce '+ sizes)))
                   `(let ((b (bits ,n)))
                      (declare (type (unsigned-byte ,n) b))
                      (values ,@(loop for o = 0 then (+ o s)
                                      for s in sizes
                                      collect `(ldb (byte ,s ,o) b))))))
               (eoi () ;; end of input
                 #++ (error "eoi")
                 #++ (go :eoi)
                 `(progn
                    (setf input-underrun t)
                    (save-state)
                    (throw :exit-loop :eoi)))
               (eoo () ;; end of output
                 `(let ((window-size (expt 2 15)))
                    (declare (optimize (speed 1)))
                    (unless (ds-window state)
                      (setf (ds-window state)
                            ;; extra few bytes so we can use word-size
                            ;; copies
                            (make-array (+ window-size 8)
                                        :element-type 'octet)))
                    (when (< output-offset window-size)
                      (replace (ds-window state) (ds-window state)
                               :start2  output-offset))
                    (replace (ds-window state) output-buffer
                             :start1 (max 0 (- window-size output-offset))
                             :start2 (max 0 (- output-offset window-size)))
                    (save-state)
                    (throw :exit-loop :eoo))))

      (let ((ht-scratch (make-huffman-tree)))
        (labels ((bits-avail (n)
                   (<= n bits-remaining))
                 (byte-align ()
                   (let ((r (mod bits-remaining 8)))
                     (unless (zerop r)
                       (setf partial-bits (ash partial-bits (- r)))
                       (decf bits-remaining r))))

                 ;; called when temp is empty, read bits and update
                 ;; remaining
                 (%fill-bits ()
                   #+#.(3bz::use-ub64)
                   (multiple-value-bind (input octets)
                       (word64)
                     (declare (type (mod 9) octets)
                              (type (unsigned-byte 64) input))
                     (setf bits-remaining (* 8 octets)
                           partial-bits input))
                   #-#.(3bz::use-ub64)
                   (multiple-value-bind (input octets)
                       (word32)
                     (declare (type (mod 5) octets)
                              (type (unsigned-byte 32) input))
                     (setf bits-remaining (* 4 octets)
                           partial-bits input)))
                 (%fill-bits32 (n)
                   (multiple-value-bind (input octets)
                       (word32)
                     (declare (type (mod 5) octets)
                              (type (unsigned-byte 32) input))
                     (setf partial-bits
                           (logior
                            (ash (ldb (byte 32 0) input)
                                 (min 32 bits-remaining))
                            partial-bits))

                     (incf bits-remaining (* 8 octets))
                     (>= bits-remaining n)))
                 ;; internals of bit reader, only call after
                 ;; ensuring there are enough bits available
                 (%bits (n)
                   (prog1 (ldb (byte n 0) partial-bits)
                     (setf partial-bits (ash partial-bits (- n)))
                     (decf bits-remaining n)))
                 ;; fast path for bit reader, inlined
                 (bits (n)
                   (if (<= n bits-remaining)
                       (%bits n)
                       (bits-full n)))
                 ;; slow path for bit reader, not inlined (should
                 ;; only be called if we know there aren't enough
                 ;; bits in temp. usually called from BITS)
                 (bits-full (n)
                   ;; we could handle 64 bits, but we limit it to
                   ;; make it more likely to fit in a fixnum
                   (declare (type (mod 56) n))
                   ;; try to read (up to) 64 bits from input
                   ;; (returns 0 in OCTETS if no more input)
                   (multiple-value-bind (input octets)
                       ;; some callers need more than 32 bits at once,
                       ;; so no use-ub64 here for now
                       (word64)
                     (declare (type (mod 9) octets)
                              (type (unsigned-byte 6) bits-remaining)
                              (type (unsigned-byte 64) input))
                     (let* ((bits (* octets 8))
                            (total (+ bits-remaining bits)))
                       ;; didn't read enough bits, save any bits we
                       ;; did get for later, then fail
                       (when (> n total)
                         (assert (<= total 64))
                         (setf partial-bits
                               (ldb (byte 64 0)
                                    (logior (ash input bits-remaining)
                                            partial-bits)))
                         (setf bits-remaining total)
                         (eoi))
                       ;; if we get here, we have enough bits now,
                       ;; so combine them and store any leftovers
                       ;; for later
                       (let* ((n2 (- n bits-remaining))
                              (r (ldb (byte n 0)
                                      (logior (ash (ldb (byte n2 0) input)
                                                   bits-remaining)
                                              (ldb (byte bits-remaining 0)
                                                   partial-bits))))
                              (bits2 (- bits n2)))
                         (declare (type (unsigned-byte 6) n2)
                                  (type (unsigned-byte 64) r))
                         (setf partial-bits (ash input (- n2))
                               bits-remaining bits2)
                         r))))

                 (out-byte (b)
                   (setf (aref output-buffer output-offset) b)
                   (setf output-offset (wrap-fixnum (1+ output-offset)))
                   nil)

                 (copy-byte-or-fail ()
                   (out-byte (bits 8)))

                 (%copy-history (from to s d e count total-count offset)
                   (declare (type non-negative-fixnum d e)
                            (type fixnum s)
                            (type non-negative-fixnum count offset total-count))
                   (cond
                     ;; if copy won't fit (or oversized copy below
                     ;; might overrun buffer), use slow path for
                     ;; now
                     ((> (+ d count 8)
                         e)
                      (loop while (< d e)
                            while (plusp count)
                            do (setf (aref to d)
                                     (aref from s))
                               (setf d (1+ d))
                               (setf s (1+ s))
                               (decf count)
                               (decf total-count))
                      ;; todo: store state so it can continue
                      (when (plusp count)
                        (setf bytes-to-copy total-count)
                        (setf copy-offset offset)
                        (setf current-state :continue-copy-history)
                        (setf output-offset d)
                        (setf output-overflow t)
                        (eoo)))
                     ;; to speed things up, we allow writing past
                     ;; current output index (but not past end of
                     ;; buffer), and read/write as many bytes at a
                     ;; time as possible.
                     #+#.(3bz::use-ub64)
                     ((> offset 8)
                      (loop repeat (ceiling count 8)
                            do (setf (ub64ref/le to d)
                                     (ub64ref/le from s))
                               (setf d (wrap-fixnum (+ d 8)))
                               (setf s (wrap-fixnum (+ s 8)))))
                     ((= offset 1)
                      ;; if offset is 1, we are just repeating a
                      ;; single byte...
                      (loop with x of-type octet = (aref from s)
                            repeat count
                            do (setf (aref to d) x)
                               (setf d (wrap-fixnum (1+ d)))))
                     #+#.(3bz::use-ub64)
                     ((= offset 8)
                      (loop with x of-type ub64 = (ub64ref/le from s)
                            repeat (ceiling count 8)
                            do (setf (ub64ref/le to d)
                                     x)
                               (setf d (wrap-fixnum (+ d 8)))))
                     ((> offset 4)
                      (loop repeat (ceiling count 4)
                            do (setf (ub32ref/le to d)
                                     (ub32ref/le from s))
                               (setf d (wrap-fixnum (+ d 4)))
                               (setf s (wrap-fixnum (+ s 4)))))
                     #+#.(3bz::use-ub64)
                     ((= offset 4)
                      (loop with x of-type ub32 = (ub32ref/le from s)
                            with xx of-type ub64 = (dpb x (byte 32 32) x)
                            repeat (ceiling count 8)
                            do (setf (ub64ref/le to d) xx)
                               (setf d (wrap-fixnum (+ d 8)))))
                     #-#.(3bz::use-ub64)
                     ((= offset 4)
                      (loop with x of-type ub32 = (ub32ref/le from s)
                            repeat (ceiling count 4)
                            do (setf (ub32ref/le to d) x)
                               (setf d (wrap-fixnum (+ d 4)))))
                     ((= offset 3)
                      (loop repeat (ceiling count 2)
                            do (setf (ub16ref/le to d)
                                     (ub16ref/le from s))
                               (setf d (wrap-fixnum (+ d 2)))
                               (setf s (wrap-fixnum (+ s 2)))))
                     #+#.(3bz::use-ub64)
                     ((= offset 2)
                      (loop with x of-type ub16 = (ub16ref/le from s)
                            with xx of-type ub32 = (dpb x (byte 16 16) x)
                            with xxxx of-type ub64 = (dpb xx (byte 32 32) xx)
                            repeat (ceiling count 8)
                            do (setf (ub64ref/le to d) xxxx)
                               (setf d (wrap-fixnum (+ d 8)))))
                     #-#.(3bz::use-ub64)
                     ((= offset 2)
                      (loop with x of-type ub16 = (ub16ref/le from s)
                            with xx of-type ub32 = (dpb x (byte 16 16) x)
                            repeat (ceiling count 4)
                            do (setf (ub32ref/le to d) xx)
                               (setf d (wrap-fixnum (+ d 4)))))
                     (t (error "?"))))

                 (copy-history (count offset)
                   (declare (type non-negative-fixnum count offset))
                   (let* ((d output-offset)
                          (s (- d offset))
                          (e (length output-buffer))
                          (n count))
                     (when (< s 0)
                       (unless window
                         (error "no window?"))
                       (let ((c (min count (abs s))))
                         (%copy-history window output-buffer
                                        (+ 32768 s) d e
                                        c count offset)
                         (decf n c)
                         (setf d (wrap-fixnum (+ d c))))
                       (setf s 0))
                     (when (plusp n)
                       (%copy-history output-buffer output-buffer
                                      s d e n n offset))
                     ;; D may be a bit past actual value, so calculate
                     ;; correct offset
                     (setf output-offset
                           (wrap-fixnum (+ output-offset count)))))

                 (decode-huffman-full (ht old-bits old-count)
                   (declare (type huffman-tree ht)
                            (type (unsigned-byte 32) old-bits)
                            (type (or null (unsigned-byte 6)) old-count))
                   (let ((ht-bits (ht-start-bits ht))
                         (bits partial-bits)
                         ;; # of valid bits left in BITS
                         (avail bits-remaining)
                         ;; offset of next unused bit in BITS
                         (offset 0)
                         ;; if we had to refill bits, # we had before refill
                         (old 0)
                         (extra-bits nil)
                         (node 0)
                         (nodes (ht-nodes ht)))
                     (declare (type (unsigned-byte 64) bits)
                              (type (unsigned-byte 7) avail)
                              (type (unsigned-byte 7) old)
                              (type ht-bit-count-type ht-bits))
                     (loop
                       ;; if we don't have enough bits, add some
                       when (> ht-bits avail)
                         do (incf old bits-remaining)
                            (%fill-bits)
                            ;; dist + extra is max 28 bits, so just
                            ;; grab enough for that from new input
                            ;; if available
                            (assert (< old 32))
                            (setf bits
                                  (logior bits
                                          (ash
                                           (ldb (byte (min 30 bits-remaining)
                                                      0)
                                                partial-bits)
                                           old)))
                            (setf avail
                                  (min 64
                                       (+ avail (min 30 bits-remaining))))
                            (when (> ht-bits avail)
                              ;; still not enough bits, push bits back
                              ;; onto tmp if we read more, and EOI
                              (assert (< old 64))
                              (assert (< (+ bits-remaining old) 64))

                              (setf partial-bits
                                    (ldb (byte 64 0)
                                         (ash partial-bits old)))
                              (setf (ldb (byte old 0) partial-bits)
                                    (ldb (byte old 0) bits))
                              (incf bits-remaining old)
                              ;; if we are reading a dist, put bits
                              ;; from len back too so we don't need
                              ;; separate states for lit/len and dist
                              (locally
                                  (declare #+sbcl (sb-ext:muffle-conditions
                                                   sb-ext:code-deletion-note))
                                (when old-count
                                  ;; (lit/len + dist + extras is max 48
                                  ;; bits, so just
                                  (assert (< (+ old-count bits-remaining) 64))
                                  (setf partial-bits
                                        (ldb (byte 64 0)
                                             (ash partial-bits old-count)))
                                  (setf (ldb (byte old-count 0) partial-bits)
                                        (ldb (byte old-count 0) old-bits))
                                  (incf bits-remaining old-count)))
                              (eoi))
                       if extra-bits
                         do (setf extra-bits (ldb (byte ht-bits offset) bits))
                            (incf offset ht-bits)
                            (decf avail ht-bits)
                            (loop-finish)
                       else
                         do (let* ((b (ldb (byte ht-bits offset) bits)))
                              (setf node (aref nodes (+ node b)))
                              (incf offset ht-bits)
                              (decf avail ht-bits)
                              (ecase (ht-node-type node)
                                (#.+ht-link/end+
                                 (when (ht-endp node)
                                   (loop-finish))
                                 (setf ht-bits (ht-link-bits node))
                                 (setf node (ht-link-offset node)))
                                (#.+ht-literal+
                                 (loop-finish))
                                (#.+ht-len/dist+
                                 (let ((x (ht-extra-bits node)))
                                   (when (zerop x)
                                     (loop-finish))
                                   (setf ht-bits x
                                         extra-bits x))))))
                     (let ((s (- offset old)))
                       (assert (< 0 s 64))
                       (setf partial-bits (ash partial-bits (- s)))
                       (decf bits-remaining s))
                     (assert (< offset 32))
                     (values (ht-value node)
                             (or extra-bits 0)
                             (ht-node-type node)
                             (ldb (byte offset 0) bits)
                             offset)))

                 ;; specialized version when we know we have enough bits
                 ;; (up to 28 depending on tree)
                 (%decode-huffman-fast (ht)
                   (declare (type huffman-tree ht))
                   (let ((ht-bits (ht-start-bits ht))
                         (bits partial-bits)
                         ;; offset of next unused bit in BITS
                         (offset 0)
                         (extra-bits nil)
                         (node 0)
                         (nodes (ht-nodes ht)))
                     (declare (type (unsigned-byte 64) bits)
                              (type ht-bit-count-type ht-bits)
                              (type (unsigned-byte 5) offset))
                     (loop
                       for b = (ldb (byte ht-bits offset) bits)
                       do (setf node (aref nodes (+ node b)))
                          (incf offset ht-bits)
                          (ecase (ht-node-type node)
                            (#.+ht-link/end+
                             (when (ht-endp node)
                               (loop-finish))
                             (setf ht-bits (ht-link-bits node)
                                   node (ht-link-offset node)))
                            (#.+ht-len/dist+
                             (let ((x (ht-extra-bits node)))
                               (when (plusp x)
                                 (setf extra-bits (ldb (byte x offset) bits))
                                 (incf offset x))
                               (loop-finish)))
                            (#.+ht-literal+
                             (loop-finish))))
                     (setf partial-bits (ash partial-bits (- offset)))
                     (decf bits-remaining offset)
                     (values (ht-value node)            ;; code
                             (or extra-bits 0)          ;; extra
                             (ht-node-type node)        ;; type
                             (ldb (byte offset 0) bits) ;; old-bits
                             offset)))                  ;; old-count

                 (decode-huffman (ht old-bits old-count)
                   ;; seems to be faster to just use constant than
                   ;; try to optimize for specific table?
                   (if (or (bits-avail +ht-max-bits+)
                           (%fill-bits32 +ht-max-bits+))
                       (%decode-huffman-fast ht)
                       (decode-huffman-full ht old-bits old-count))))
          (declare (inline bits-avail byte-align %fill-bits %bits bits
                           out-byte copy-byte-or-fail
                           decode-huffman %decode-huffman-fast
                           %fill-bits32 copy-history
                           %copy-history)
                   (ignorable #'bits-avail))
          (catch :exit-loop
            (state-machine (state)
              :start-of-block
              (multiple-value-bind (final type) (bits* 1 2)
                (setf last-block-flag (plusp final))
                (ecase type
                  (0 (next-state :uncompressed-block))
                  (1 ;; static huffman tree
                   (setf current-huffman-tree +static-huffman-trees+)
                   (next-state :decode-compressed-data))
                  (2
                   (setf current-huffman-tree dynamic-huffman-tree)
                   (next-state :dynamic-huffman-block))))

;;; uncompressed block

              :uncompressed-block
              (byte-align)
              (multiple-value-bind (s n) (bits* 16 16)
                (assert (= n (ldb (byte 16 0) (lognot s))))
                (setf bytes-to-copy s)
                (next-state :copy-block))
              :copy-block
              (loop while (and (plusp bits-remaining)
                               (plusp bytes-to-copy))
                    do (out-byte (bits 8))
                       (decf bytes-to-copy))
              (loop with e = (- (length output-buffer) 8)
                    while (and (> bytes-to-copy 8)
                               (< output-offset e))
                    do (multiple-value-bind (w c) #+#.(3bz::use-ub64) (word64) #-#.(3bz::use-ub64) (word32)
                         (declare (type #+#.(3bz::use-ub64) ub64
                                        #-#.(3bz::use-ub64) ub32))
                         (cond
                           #+#.(3bz::use-ub64)
                           ((= 8 c)
                            (setf (ub64ref/le output-buffer output-offset)
                                  w)
                            (setf output-offset
                                  (wrap-fixnum (+ output-offset 8)))
                            (decf bytes-to-copy 8))
                           #-#.(3bz::use-ub64)
                           ((= 4 c)
                            (setf (ub32ref/le output-buffer
                                              output-offset)
                                  w)
                            (setf output-offset
                                  (wrap-fixnum (+ output-offset 4)))
                            (decf bytes-to-copy 4))
                           ((plusp c)
                            (loop for i below c
                                  do (out-byte (ldb (byte 8 (* i 8)) w))
                                     (decf bytes-to-copy)))
                           (t (eoo)))))
              (loop while (plusp bytes-to-copy)
                    do (copy-byte-or-fail)
                       (decf bytes-to-copy))
              (next-state :block-end)

;;; dynamic huffman table block, huffman table

              :dynamic-huffman-block
              ;; we have at least 26 bits of fixed data, 3 length
              ;; fields, and first 4 code lengths, so try to read
              ;; those at once
              (multiple-value-bind (hlit hdist hclen l16 l17 l18 l0)
                  (bits* 5 5 4 3 3 3 3)
                (let ((dlc dht-len-codes))
                  (fill dlc 0)
                  (setf (aref dlc 16) l16)
                  (setf (aref dlc 17) l17)
                  (setf (aref dlc 18) l18)
                  (setf (aref dlc 0) l0))
                ;; possibly could optimize this a bit more, but
                ;; should be fairly small part of any normal file
                (setf dht-hlit (+ hlit 257)
                      dht-hlit+hdist (+ dht-hlit hdist 1)
                      dht-hclen hclen
                      dht-lit/len/dist-index 0)
                (next-state :dht-len-table))

              :dht-len-table
              ;; we read 4 entries with header, so max 15 left = 45
              ;; bits. wait until we have at least that much
              ;; available and extract all at once
              (let* ((bitcount (* dht-hclen 3))
                     (bits (bits bitcount))
                     (permute +len-code-order+)
                     (lc dht-len-codes))
                (declare (type (unsigned-byte 48) bits))
                ;; extract length codes into proper elements of
                ;; len-codes
                (loop for i from 4
                      for o from 0 by 3 ;downfrom (- bitcount 3) by 3
                      repeat dht-hclen
                      do (setf (aref lc (aref permute i))
                               (ldb (byte 3 o) bits)))
                ;; and build a huffman tree out of them
                (multiple-value-bind (count bits max)
                    (build-tree-part dht-len-tree 0
                                     dht-len-codes
                                     :dht-len 0 19
                                     ht-scratch
                                     +len-code-extra+)
                  (declare (ignore count))
                  (setf (ht-start-bits dht-len-tree) bits)
                  (setf (ht-max-bits dht-len-tree) max))
                (setf dht-last-len #xff)
                (next-state :dht-len-table-data))

              :dht-len-table-data
              (let ((ht dht-len-tree)
                    (end dht-hlit+hdist)
                    (lld dht-lit/len/dist))
                ;; decode-huffman will EOI if not enough bits
                ;; available, so we need to track state in loop to
                ;; be able to continue
                (loop while (< dht-lit/len/dist-index end)
                      do (multiple-value-bind (code extra)
                             (decode-huffman ht 0 nil)
                           (cond
                             ((< code 16)
                              (setf (aref lld dht-lit/len/dist-index)
                                    (setf dht-last-len code))
                              (incf dht-lit/len/dist-index))
                             ((= code 16)
                              (unless (< dht-last-len 16)
                                (error "tried to repeat length without previous length"))
                              (let ((e (+ dht-lit/len/dist-index extra 3)))
                                (assert (<= e dht-hlit+hdist))
                                (loop for i from dht-lit/len/dist-index
                                      repeat (+ extra 3)
                                      do (setf (aref lld i) dht-last-len))
                                #++(fill lld dht-last-len
                                         :start dht-lit/len/dist-index
                                         :end e)
                                (setf dht-lit/len/dist-index e)))
                             (t
                              (let* ((c (if (= code 17) 3 11))
                                     (e (+ dht-lit/len/dist-index extra c)))
                                (assert (<= e dht-hlit+hdist))
                                (fill lld 0
                                      :start dht-lit/len/dist-index
                                      :end e)
                                (setf dht-lit/len/dist-index e)
                                (setf dht-last-len 0)))))))
              ;; if we get here, we have read whole table, build tree
              (build-trees* (car dynamic-huffman-tree)
                            (cdr dynamic-huffman-tree)
                            dht-lit/len/dist
                            dht-hlit
                            dht-lit/len/dist-index
                            ht-scratch)
              (next-state :decode-compressed-data)

;;; dynamic or static huffman block, compressed data

              :decode-compressed-data
              (symbol-macrolet ((bases +len/dist-bases+)
                                (ht current-huffman-tree))
                (loop
                  (multiple-value-bind (code extra type old-bits old-count)
                      (decode-huffman (car ht) 0 nil)
                    (ecase type
                      (#.+ht-len/dist+
                       ;; got a length code, read dist and copy
                       (let ((octets (+ extra (aref bases code))))
                         ;; try to read dist. decode-huffman* will
                         ;; push BITS back onto temp before calling
                         ;; EOI if it fails, so we can restart state
                         ;; at len code
                         (multiple-value-bind (dist extra)
                             (decode-huffman (cdr ht)
                                             old-bits old-count)
                           ;; got dist code
                           (copy-history octets (+ (aref bases dist) extra)))))
                      (#.+ht-literal+
                       (when (>= output-offset (length output-buffer))
                         (setf current-state :out-byte)
                         (setf bytes-to-copy code)
                         (setf output-overflow t)
                         (eoo))
                       (out-byte code))
                      (#.+ht-link/end+
                       (assert (= code 0))
                       (assert (= extra 0))
                       (next-state :block-end))))))

              ;; continue copy if output filled up in the middle
              :continue-copy-history
              (copy-history bytes-to-copy copy-offset)
              (next-state :decode-compressed-data)

              :out-byte
              (when (> output-offset (length output-buffer))
                (when (> output-offset (length output-buffer))
                  (error "tried to continue from overflow without providing more space in output"))
                (setf output-overflow t)
                (eoo))
              (out-byte bytes-to-copy)
              (next-state :decode-compressed-data)

;;; end of a block, see if we are done with deflate stream
              :block-end
              (if last-block-flag
                  (next-state :done)
                  (next-state :start-of-block))

;;; normal exit from state machine
              :done
              (setf finished t)
;;; any exit from state machine (should set flags first)
              :exit-loop)))))
    (save-state)
    output-offset))
