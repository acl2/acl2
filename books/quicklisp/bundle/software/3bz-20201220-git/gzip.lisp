(in-package 3bz)

(defstruct (gzip-state (:conc-name gs-)
                       (:include deflate-state))

  ;; A compliant decompressor must check ID1, ID2, and CM, and provide
  ;; an error indication if any of these have incorrect values.  It
  ;; must examine FEXTRA/XLEN, FNAME, FCOMMENT and FHCRC at least so
  ;; it can skip over the optional fields if they are present.  It
  ;; need not examine any other part of the header or trailer; in
  ;; particular, a decompressor may ignore FTEXT and OS and always
  ;; produce binary output, and still be compliant.  A compliant
  ;; decompressor must give an error indication if any reserved bit is
  ;; non-zero, since such a bit could indicate the presence of a new
  ;; field that would cause subsequent data to be interpreted
  ;; incorrectly.
  (gzip-state :header)
  (compression-method nil)
  (flags nil)
  (extra nil)
  (name nil)
  (comment nil)
  (operating-system nil)
  (mtime/unix nil)
  (mtime/universal nil)
  (compression-level :default)
  (header-bytes (make-array 16 :adjustable t :fill-pointer 0))
  (crc32 0 :type (unsigned-byte 32)))

(defun decompress-gzip (read-context state)
  (check-type state gzip-state)
  ;; fixme: avoid duplication with these from deflate/zlib
  (with-reader-contexts (read-context)
    (with-accessors ((input-underrun gs-input-underrun)
                     (gzip-state gs-gzip-state)
                     (partial-bits gs-partial-bits)
                     (bits-remaining gs-bits-remaining)
                     (finished gs-finished)
                     (flags gs-flags)
                     (compression-level gs-compression-level)
                     (compression-method gs-compression-method)
                     (output-buffer gs-output-buffer)
                     (output-offset gs-output-offset)
                     (output-overflow gs-output-overflow)
                     (header-bytes gs-header-bytes)
                     (mtime/unix gs-mtime/unix)
                     (mtime/universal gs-mtime/universal)
                     (extra gs-extra)
                     (name gs-name)
                     (comment gs-comment)
                     (operating-system gs-operating-system)
                     (crc32 gs-crc32))
        state
      (labels ((%fill-bits32 (n)
                 (multiple-value-bind (input octets)
                     (word32)
                   (declare (type (mod 5) octets))
                   (setf partial-bits
                         (logior
                          (ash (ldb (byte 32 0) input)
                               (min 32 bits-remaining))
                          partial-bits))
                   (incf bits-remaining (* 8 octets))
                   (>= bits-remaining n)))
               (%bits (n)
                 (prog1 (ldb (byte n 0) partial-bits)
                   (setf partial-bits (ash partial-bits (- n)))
                   (decf bits-remaining n)))
               (header-byte ()
                 (let ((b (%bits 8)))
                   ;; might need to crc header, so store a copy
                   (when header-bytes
                     (vector-push-extend b header-bytes))
                   b))
               (byte-align ()
                 (let ((r (mod bits-remaining 8)))
                   (unless (zerop r)
                     (setf partial-bits (ash partial-bits (- r)))
                     (decf bits-remaining r))))
               (update-checksum ()
                 (setf crc32 (crc32/table output-buffer output-offset crc32)))
               (crc ()
                 (when (and (< bits-remaining 32)
                            (not (%fill-bits32 32)))
                   (setf input-underrun t)
                   (return-from decompress-gzip 0))
                 (let ((crc (logior (ash (header-byte) 0)
                                    (ash (header-byte) 8)
                                    (ash (header-byte) 16)
                                    (ash (header-byte) 24))))
                   #++(format t "crc = ~8,'0x ?= ~8,'0x~%"
                              crc crc32)
                   (assert (= crc crc32))
                   (setf gzip-state :final-len)))
               (len ()
                 (when (and (< bits-remaining 32)
                            (not (%fill-bits32 32)))
                   (setf input-underrun t)
                   (return-from decompress-gzip 0))
                 (let ((len (logior (ash (header-byte) 0)
                                    (ash (header-byte) 8)
                                    (ash (header-byte) 16)
                                    (ash (header-byte) 24))))
                   len
                   #++(format t "len = ~8,'0x ?= ~8,'0x~%"
                              len output-offset)
                   (setf gzip-state nil))))
        (declare (inline %fill-bits32 %bits byte-align)
                 (optimize (speed 1)))
        (setf input-underrun nil)
        (loop
          while gzip-state
          do (case gzip-state
               (:header ;; magic #
                (when (and (< bits-remaining 16)
                           (not (%fill-bits32 16)))
                  (setf input-underrun t)
                  (return-from decompress-gzip 0))
                (let ((id1 (header-byte))
                      (id2 (header-byte)))
                  (assert (= id1 #x1f))
                  (assert (= id2 #x8b))
                  (setf gzip-state :header2)))
               (:header2 ;; compression method, flags
                (when (and (< bits-remaining 16)
                           (not (%fill-bits32 16)))
                  (setf input-underrun t)
                  (return-from decompress-gzip 0))
                (let ((cm (header-byte))
                      (flg (header-byte)))
                  (if (= cm 8)
                      (setf compression-method :deflate)
                      (error "unknown compression method ~s~%" cm))
                  (when (plusp (ldb (byte 3 5) flg))
                    (error "reserved flag bits set in ~8,'0b" flg))
                  (when (logbitp 0 flg) (push :text flags))
                  (if (logbitp 1 flg)
                      (push :header-crc flags)
                      ;; no crc, stop remembering header contents
                      (setf header-bytes nil))
                  (when (logbitp 2 flg) (push :extra flags))
                  (when (logbitp 3 flg) (push :name flags))
                  (when (logbitp 4 flg) (push :comment flags))
                  (setf gzip-state :header-mtime)))
               (:header-mtime
                (when (and (< bits-remaining 32)
                           (not (%fill-bits32 32)))
                  (setf input-underrun t)
                  (return-from decompress-gzip 0))
                (let ((mtime (logior (ash (header-byte) 0)
                                     (ash (header-byte) 8)
                                     (ash (header-byte) 16)
                                     (ash (header-byte) 24))))
                  (unless (zerop mtime)
                    (setf mtime/unix mtime)
                    (setf mtime/universal
                          (+ mtime (encode-universal-time 0 0 0 1 1 1970 0))))
                  (setf gzip-state :header3)))

               (:header3 ;; extra flags, os
                (when (and (< bits-remaining 16)
                           (not (%fill-bits32 16)))
                  (setf input-underrun t)
                  (return-from decompress-gzip 0))
                (let ((xfl (header-byte))
                      (os (header-byte)))
                  (setf compression-level
                        (or (case xfl (2 :maximum) (4 :fastest))
                            xfl))
                  (setf operating-system
                        (if (<= 0 os 13)
                            (aref #(:fat :amiga :vms :unix :vm/cms
                                    :atari-tos :hpfs :macintosh
                                    :z-system :cp/m :tops-20
                                    :ntfs :qdos :acorn-riscos)
                                  os)
                            (list :unknown os)))
                  (setf gzip-state :header-extra)))
               (:header-extra
                (when (member :extra flags)
                  (unless extra
                    (when (and (< bits-remaining 16)
                               (not (%fill-bits32 16)))
                      (setf input-underrun t)
                      (return-from decompress-gzip 0))
                    (let ((xlen (logior (ash (header-byte) 0)
                                        (ash (header-byte) 8))))
                      (setf extra (make-array xlen :element-type 'octet
                                                   :fill-pointer 0))))
                  (loop while (< (fill-pointer extra)
                                 (length extra))
                        do (when (and (< bits-remaining 8)
                                      (not (%fill-bits32 8)))
                             (setf input-underrun t)
                             (return-from decompress-gzip 0))
                           (vector-push (header-byte) extra))
                  (setf extra (coerce extra '(simple-array octet 1))))
                (setf gzip-state :header-name))
               (:header-name
                (when  (member :name flags)
                  (unless name
                    (setf name (make-array 16 :adjustable t :fill-pointer 0
                                              :element-type 'octet)))
                  (loop do (when (and (< bits-remaining 8)
                                      (not (%fill-bits32 8)))
                             (setf input-underrun t)
                             (return-from decompress-gzip 0))
                           (let ((b (header-byte)))
                             (cond
                               ((not (zerop b))
                                (vector-push-extend b name))
                               (t
                                (setf name
                                      ;; rfc says 8859-1, but try utf8 anyway
                                      (or (babel:octets-to-string
                                           name :encoding :utf-8 :errorp nil)
                                          (babel:octets-to-string
                                           name :encoding :iso8859-1)))
                                (loop-finish))))))
                (setf gzip-state :header-comment))
               (:header-comment
                (when  (member :comment flags)
                  (unless comment
                    (setf comment (make-array 16 :adjustable t :fill-pointer 0
                                                 :element-type 'octet)))
                  (loop do (when (and (< bits-remaining 8)
                                      (not (%fill-bits32 8)))
                             (setf input-underrun t)
                             (return-from decompress-gzip 0))
                           (let ((b (header-byte)))
                             (cond
                               ((not (zerop b))
                                (vector-push-extend b comment))
                               (t
                                (setf comment
                                      ;; rfc says 8859-1, but try utf8 anyway
                                      (or (babel:octets-to-string
                                           comment :encoding :utf-8 :errorp nil)
                                          (babel:octets-to-string
                                           comment :encoding :iso8859-1)))
                                (loop-finish))))))
                (setf gzip-state :header-crc))
               (:header-crc
                ;; check hcrc if present
                (when (member :header-crc flags)
                  (when (and (< bits-remaining 16)
                             (not (%fill-bits32 16)))
                    (setf input-underrun t)
                    (return-from decompress-gzip 0))
                  (let* ((hb (coerce header-bytes 'octet-vector))
                         (crc (logior (ash (%bits 8) 0)
                                      (ash (%bits 8) 8)))
                         (crc32 (crc32/table hb (length hb) 0)))
                    (format t "got header crc ~4,'0x, expected ~8,'0x~%"
                            crc crc32)
                    (assert (= crc (ldb (byte 16 0) crc32)))))
                #++(format t "gzip header: method ~s, level ~s, os ~s, flags ~s~%"
                           compression-method compression-level
                           operating-system flags)
                #++(when mtime/universal
                     (format t "  mtime: ~s~%"
                             (reverse (multiple-value-list
                                       (decode-universal-time mtime/universal)))))
                #++(format t "  name: ~s~%" name)
                #++(format t "  comment: ~s~%" comment)
                #++(format t "  extra: ~s~%" extra)
                (setf gzip-state nil))
               (:final-crc
                (crc))
               (:final-len
                (len)
                (return-from decompress-gzip output-offset)))
             (unless gzip-state
               (decompress-deflate read-context state)
               (when (or finished output-overflow)
                 (update-checksum))
               (when finished
                 (byte-align)
                 (setf gzip-state :final-crc)
                 (setf finished nil))))
        (when (eql :final-crc gzip-state)
          (crc))
        (when (eql :final-len gzip-state)
          (len))
        output-offset))))
