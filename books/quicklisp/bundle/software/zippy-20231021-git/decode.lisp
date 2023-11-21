(in-package #:org.shirakumo.zippy)

(define-condition archive-file-required (error)
  ((disk :initarg :disk :initform (error "DISK required.") :reader disk))
  (:report (lambda (c s) (format s "Disk ~a is required to continue reading the Zip file."
                                 (disk c)))))

(defun decode-extra-fields (vector)
  (let ((fields ()))
    (loop with index = 0
          while (< index (length vector))
          do (let* ((sig (nibbles:ub16ref/le vector index))
                    (dec (gethash sig *structures*)))
               (incf index 2)
               (when dec
                 (push (funcall (first dec) vector index) fields))
               (if (< index (length vector))
                   (incf index (+ 2 (nibbles:ub16ref/le vector index)))
                   (return))))
    (nreverse fields)))

(defun process-extra-field (entry field)
  (typecase field
    (zip64-extended-information
     (setf (size entry) (zip64-extended-information-compressed-size field))
     (setf (uncompressed-size entry) (zip64-extended-information-original-size field))
     (setf (offset entry) (zip64-extended-information-header-offset field))
     (setf (disk entry) (zip64-extended-information-starting-disk field)))
    (encryption-header
     (setf (encryption-method entry)
           (list (encryption-method-name (encryption-header-encryption-algorithm field))
                 :bit-length (encryption-header-bit-length field))))
    (aes-extra-data
     (setf (encryption-method entry) (list (ecase (aes-extra-data-version field)
                                             (1 :AE-1)
                                             (2 :AE-2))
                                           :bit-length (ecase (aes-extra-data-encryption-strength field)
                                                         (1 128)
                                                         (2 192)
                                                         (3 256))))
     (setf (compression-method entry) (compression-method-name (aes-extra-data-compression-method field))))))

(defun lf-to-entry (lf entry)
  (macrolet ((maybe-set (field value)
               `(let ((value ,value))
                  (cond ((null (,field entry))
                         (setf (,field entry) value))
                        ((not (equal value (,field entry)))
                         (warn "Mismatch in ~a:~%  Central directory: ~a~%  Local file header: ~a"
                               ',field (,field entry) value))))))
    (maybe-set version (decode-version (local-file-version lf)))
    (setf (crc-32 entry) (local-file-crc-32 lf))
    ;; Ignore if size is not contained or in zip64
    (unless (or (logbitp 3 (local-file-flags lf))
                (= #xFFFFFFFF (local-file-compressed-size lf)))
      (maybe-set size (local-file-compressed-size lf))
      (maybe-set uncompressed-size (local-file-uncompressed-size lf)))
    (maybe-set compression-method (compression-method-name (local-file-compression-method lf)))
    (maybe-set encryption-method (cond ((logbitp 6 (local-file-flags lf)) '(:unknown))
                                       ((logbitp 0 (local-file-flags lf)) '(:pkware))))
    (maybe-set file-name (decode-string (local-file-file-name lf) (local-file-flags lf)))
    (setf (extra-fields entry) (append (extra-fields entry) (decode-extra-fields (local-file-extra lf))))
    (loop for field in (extra-fields entry)
          do (process-extra-field entry field))))

(defun cde-to-entry (cde entry)
  (setf (version entry) (decode-version (central-directory-entry-version-needed cde)))
  (setf (attributes entry) (decode-file-attribute (ldb (byte 8 8) (central-directory-entry-version-made cde))
                                                  (central-directory-entry-external-file-attributes cde)))
  (setf (crc-32 entry) (central-directory-entry-crc-32 cde))
  (setf (size entry) (central-directory-entry-compressed-size cde))
  (setf (uncompressed-size entry) (central-directory-entry-uncompressed-size cde))
  (setf (offset entry) (central-directory-entry-local-header-offset cde))
  (setf (disk entry) (central-directory-entry-disk-number-start cde))
  (setf (last-modified entry) (decode-msdos-timestamp (central-directory-entry-last-modified-date cde)
                                                      (central-directory-entry-last-modified-time cde)))
  (setf (compression-method entry) (compression-method-name (central-directory-entry-compression-method cde)))
  (setf (encryption-method entry) (cond ((logbitp 6 (central-directory-entry-flags cde)) '(:strong))
                                        ((logbitp 0 (central-directory-entry-flags cde)) '(:pkware))))
  (setf (comment entry) (decode-string (central-directory-entry-file-comment cde)
                                       (central-directory-entry-flags cde)))
  (setf (file-name entry) (decode-string (central-directory-entry-file-name cde)
                                         (central-directory-entry-flags cde)))
  (setf (extra-fields entry) (decode-extra-fields (central-directory-entry-extra cde)))
  (loop for field in (extra-fields entry)
        do (process-extra-field entry field)))

(defun decode-central-directory (input entries entry-offset)
  (let ((i entry-offset))
    (loop for structure = (parse-structure* input)
          for entry = (make-instance 'zip-entry)
          do (cde-to-entry structure entry)
             (setf (aref entries i) entry)
             (incf i)
          while (and (has-more input)
                     (< i (length entries))))
    i))

(defun decode-file (input)
  (let (entries disks)
    ;; First seek to end of file, then backtrack to find the end-of-central-directory signature.
    ;; We skip the bytes that are guaranteed to be part of the structure anyway. Thus, if the
    ;; comment is empty, we should immediately end up at the signature.
    (seek input (- (end input) (+ 4 2 2 2 2 4 4 2)))
    (loop for byte = (ub32 input)
          until (= #x06054B50 byte)
          ;; Seek back the 4 bytes we read +1 extra byte.
          ;; TODO: This could be sped up by trying to match parts of the signature against what we
          ;;       read and then speculatively back up more bytes.
          do (if (<= (start input) (- (index input) 5))
                 (seek input (- (index input) 5))
                 (error 'malformed-file :message "No end of central directory marker could be found.")))
    ;; We should now be at the beginning (after the signature) of the end-of-central-directory.
    (let* ((eocd (parse-structure end-of-central-directory input))
           (cd-offset (end-of-central-directory-central-directory-start eocd))
           (cd-start-disk (end-of-central-directory-central-directory-disk eocd))
           (cd-end-disk (end-of-central-directory-number-of-disk eocd)))
      ;; OK, next we look for end-of-central-directory-locator/64, which should be
      ;; input - 4 (eocd sig) - 16 (ecod64 payload) - 4 (eocd64 sig)
      (seek input (- (index input) 4 16 4))
      (when (= #x07064B50 (ub32 input))
        (let ((eocd-locator (parse-structure end-of-central-directory-locator/64 input))
              (eocd64-input input))
          (when (/= (end-of-central-directory-number-of-disk eocd)
                    (end-of-central-directory-locator/64-central-directory-disk eocd-locator))
            (restart-case (error 'archive-file-required :disk (end-of-central-directory-locator/64-central-directory-disk eocd-locator))
              (use-value (new-input)
                (setf eocd64-input new-input))))
          (setf disks (make-array (end-of-central-directory-locator/64-number-of-disks eocd-locator) :initial-element NIL))
          (setf (aref disks (end-of-central-directory-locator/64-central-directory-disk eocd-locator)) eocd64-input)
          ;; Okey, header is on here, let's check it.
          (seek eocd64-input (end-of-central-directory-locator/64-central-directory-start eocd-locator))
          (if (= #x06064B50 (ub32 eocd64-input))
              (let ((eocd (parse-structure end-of-central-directory/64 eocd64-input)))
                (setf cd-offset (end-of-central-directory/64-central-directory-start eocd))
                (setf cd-start-disk (end-of-central-directory/64-central-directory-disk eocd))
                (setf cd-end-disk (end-of-central-directory/64-number-of-disk eocd))
                (setf entries (make-array (end-of-central-directory/64-central-directory-entries eocd)
                                          :initial-element NIL :adjustable T :fill-pointer T)))
              (warn "File appears corrupted: 

Zip64 End of Central Directory Record was not at indicated position.
Will attempt to continue with 32 bit standard central directory."))))
      (cond ((and (null entries) (= #xFFFFFFFF (end-of-central-directory-central-directory-start eocd)))
             (error 'malformed-file :message "No Zip64 End of Central Directory record found, but End of Central
Directory contains a start marker that indicates there should be
one."))
            (T
             (let ((i 0))
               (unless entries
                 (setf entries (make-array (end-of-central-directory-central-directory-entries eocd)
                                           :initial-element NIL :adjustable T :fill-pointer T)))
               (unless disks
                 (setf disks (make-array (1+ (end-of-central-directory-number-of-disk eocd)) :initial-element NIL)))
               (unless (= #xFFFF (end-of-central-directory-number-of-disk eocd))
                 (setf (aref disks (end-of-central-directory-number-of-disk eocd)) input))
               (loop for disk from cd-start-disk to cd-end-disk
                     for input = (or (aref disks disk)
                                     (restart-case (error 'archive-file-required :disk disk)
                                       (use-value (new-input)
                                         (setf (aref disks disk) new-input))))
                     do (seek input cd-offset)
                        (setf cd-offset 0)
                        (setf i (decode-central-directory input entries i))))))
      (let ((zip-file (make-instance 'zip-file :comment (decode-string (end-of-central-directory-file-comment eocd) #b10000000000)
                                               :entries entries :disks disks)))
        (loop for entry across entries
              do (setf (zip-file entry) zip-file))
        zip-file))))

(defun open-zip-file (input &key (start 0) end)
  (etypecase input
    ((or pathname string)
     (let ((streams (list (open input :element-type '(unsigned-byte 8))))
           (success NIL))
       (handler-bind ((archive-file-required
                        (lambda (c)
                          (let ((id (disk c)))
                            (let ((stream (open (make-pathname :type (format NIL "z~2,'0d" (1+ id)) :defaults input)
                                                :element-type '(unsigned-byte 8))))
                              (push stream streams)
                              (use-value stream))))))
         (unwind-protect
              (let ((file (decode-file (first streams))))
                (setf success T)
                (values file streams))
           (unless success
             (mapc #'close streams))))))
    (stream
     (decode-file input))
    ((vector (unsigned-byte 8))
     (decode-file (make-vector-input input start start (or end (length input)))))))

(defun call-with-input-zip-file (function input &key (start 0) end)
  (multiple-value-bind (file streams) (open-zip-file input :start start :end end)
    (unwind-protect (funcall function file)
      (mapc #'close streams))))

(defun prepare-reading (entry)
  (let* ((disks (disks (zip-file entry)))
         (disk (disk entry))
         (input (or (aref disks disk)
                    (restart-case (error 'archive-file-required :disk disk)
                      (use-value (new-input)
                        (setf (aref disks disk) new-input))))))
    (seek input (offset entry))
    (lf-to-entry (parse-structure* input) entry)
    input))

(defun entry-raw-bytes (function entry)
  (let ((input (prepare-reading entry))
        (length (size entry)))
    (etypecase input
      (stream
       (loop with buffer = (ensure-buffer NIL)
             while (< 0 length)
             for read = (read-sequence buffer input :end (min (length buffer) length))
             do (funcall function buffer 0 read)
                (decf length read)))
      (vector-input
       (let ((start (vector-input-index input)))
         (funcall function (vector-input-vector input) start (+ start length))))
      (directory-input))))

(defun decode-entry (function entry &key password)
  (let* ((input (prepare-reading entry))
         (decryption-state (apply #'make-decryption-state (first (encryption-method entry)) input password (rest (encryption-method entry))))
         (decompression-state (make-decompression-state (compression-method entry))))
    (flet ((decompress (buffer start end)
             (call-with-decompressed-buffer function buffer start end decompression-state)))
      (call-with-decrypted-buffer #'decompress input (size entry) decryption-state))))

(defstruct (chunk-decoder
            (:constructor %make-chunk-decoder (input size decryption-state decompression-state buffer start end)))
  input
  size
  decryption-state
  decompression-state
  buffer
  start
  end)

(defun make-chunk-decoder (entry &key password)
  (let* ((input (prepare-reading entry))
         (decryption-state (apply #'make-decryption-state (first (encryption-method entry)) input password (rest (encryption-method entry))))
         (decompression-state (make-decompression-state (compression-method entry))))
    (%make-chunk-decoder input (size entry) decryption-state decompression-state NIL 0 0)))

(defun decode-chunk (decoder output start end)
  (let ((decompression-state (chunk-decoder-decompression-state decoder))
        (decryption-state (chunk-decoder-decryption-state decoder))
        (input (chunk-decoder-input decoder))
        (size (chunk-decoder-size decoder)))
    (labels ((decode (buffer bstart bend)
               (let ((copyable (min (- end start) (- bend bstart))))
                 (loop for i from 0 below copyable
                       do (setf (aref output (+ start i)) (aref buffer (+ bstart i))))
                 (incf start copyable)
                 (+ bstart copyable)))
             (decompress (buffer start end)
               (call-with-decompressed-buffer #'decode buffer start end decompression-state)))
      (loop until (= 0 (call-with-decrypted-buffer #'decompress input size decryption-state))))
    (min start end)))
