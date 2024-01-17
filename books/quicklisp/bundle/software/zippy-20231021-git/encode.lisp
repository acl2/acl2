(in-package #:org.shirakumo.zippy)

(defvar *zip64-needed*)

(defun n-bit-and-note-zip64-p (bits &rest integers)
  (cond ((apply #'n-bit-p bits integers))
        (T
         (setf *zip64-needed* T)
         nil)))

(defun cap-and-note-zip64 (value bits)
  (let ((max (1- (ash 1 bits))))
    (cond ((< value max)
           value)
          (T
           (setf *zip64-needed* T)
           max))))

(defun entry-flags (entry)
  (bitfield (encryption-method entry)
            NIL
            NIL
            T ;; FIXME: Should only set this to T if the /output/ is non-seekable
            NIL
            NIL
            (and (encryption-method entry)
                 (not (eql :pkware (encryption-method entry))))
            NIL NIL NIL NIL T NIL NIL NIL NIL))

(defun backfill-from-content (entry)
  (let ((content (content entry)))
    (etypecase content
      ((or string pathname file-stream)
       (setf (last-modified entry) (file-write-date content))
       (unless (file-name entry)
         (setf (file-name entry) (file-namestring content)))
       (unless (attributes entry)
         (setf (attributes entry) (list `(,(if (pathname-utils:directory-p content)
                                               :directory
                                               :normal)
                                          T)
                                        *compatibility*
                                        (file-attributes:attributes content))))
       (unless (pathname-utils:directory-p content)
         (typecase content
           (file-stream (setf (uncompressed-size entry) (file-length content)))
           (T
            (with-open-file (stream content :direction :input :element-type '(unsigned-byte 8))
              (setf (uncompressed-size entry) (file-length stream)))))))
      (stream)
      (vector-input
       (setf (uncompressed-size entry) (size content)))
      (vector
       (setf (uncompressed-size entry) (length content)))
      (null
       (unless (attributes entry) ;; Assume directory.
         (setf (attributes entry) (list '(:directory T) *compatibility* (default-attributes-for *compatibility*))))))
    (unless (attributes entry)
      (setf (attributes entry) (list '(:normal T) *compatibility* (default-attributes-for *compatibility*))))
    (when (and content
               (null (compression-method entry)))
      (if (< 1024 (or (uncompressed-size entry) 1025))
          (setf (compression-method entry) :deflate)
          (setf (compression-method entry) :store)))))

(defun entry-version (entry)
  (encode-version (or (version entry) *default-version-needed*)
                  (if (consp (attributes entry))
                      (second (attributes entry))
                      *compatibility*)))

(defun entry-compression-id (entry)
  (compression-method-id
   (if (and (consp (encryption-method entry))
            (find (first (encryption-method entry)) '(:ae-1 :ae-2)))
       :ae-x
       (or (compression-method entry)
           :store))))

(defun add-extra-entry (extra entry)
  (let ((end (length extra)))
    (setf extra (adjust-array extra (+ end 4 (zip64-extended-information-size entry))))
    (encode-structure entry extra end)
    extra))

(defun entry-to-lf (entry)
  (let ((file-name (babel:string-to-octets (file-name entry) :encoding :utf-8))
        (extra (make-array 0 :adjustable T :element-type '(unsigned-byte 8)))
        (size (or (size entry) 0))
        (uncompressed-size (or (uncompressed-size entry) 0)))
    (when (not (n-bit-and-note-zip64-p 32 size))
      (add-extra-entry extra (make-zip64-extended-information
                              28 size uncompressed-size
                              (offset entry) 0)))
    (destructuring-bind (&optional method bittage) (enlist (encryption-method entry))
      (case method
        (:ae-1
         (add-extra-entry extra (make-aes-extra-data
                                 7 17729 1
                                 (ecase bittage
                                   (128 1)
                                   (192 2)
                                   (256 3))
                                 (compression-method-id (compression-method entry)))))
        (:ae-2
         (add-extra-entry extra (make-aes-extra-data
                                 7 17729 2
                                 (ecase bittage
                                   (128 1)
                                   (192 2)
                                   (256 3))
                                 (compression-method-id (compression-method entry)))))
        ((:pkware NIL))
        (T
         (add-extra-entry extra (make-encryption-header
                                 8 2 (encryption-method-id method)
                                 bittage 1 #())))))
    (multiple-value-bind (date time) (encode-msdos-timestamp (last-modified entry))
      (make-local-file (entry-version entry)
                       (entry-flags entry)
                       (entry-compression-id entry)
                       time date (or (crc-32 entry) 0)
                       (cap size 32) (cap uncompressed-size 32)
                       (length file-name) (length extra) file-name extra))))

(defun entry-to-dd (entry)
  (let ((uncompressed-size (uncompressed-size entry)))
    (if (n-bit-and-note-zip64-p 32 uncompressed-size)
        (make-data-descriptor (crc-32 entry) (size entry) uncompressed-size)
        (make-data-descriptor/64 (crc-32 entry) (size entry) uncompressed-size))))

(defun entry-to-cd (entry)
  (let ((file-name (babel:string-to-octets (file-name entry) :encoding :utf-8))
        (comment (encode-string (comment entry)))
        (extra (make-array 0 :adjustable T :element-type '(unsigned-byte 8)))
        (size (or (size entry) 0))
        (uncompressed-size (or (uncompressed-size entry) 0))
        (offset (offset entry)))
    (when (not (n-bit-and-note-zip64-p 32 size offset))
      (add-extra-entry extra (make-zip64-extended-information
                              28 size uncompressed-size
                              offset 0)))
    (multiple-value-bind (date time) (encode-msdos-timestamp (last-modified entry))
      (make-central-directory-entry
       (entry-version entry)
       (entry-version entry)
       (entry-flags entry)
       (entry-compression-id entry)
       time date (or (crc-32 entry) 0)
       (cap size 32) (cap uncompressed-size 32)
       (length file-name) (length extra) (length comment)
       0 0 (or (encode-file-attribute (attributes entry)) 0) (cap offset 32)
       file-name extra comment))))

(defun encode-entry-payload (entry output password)
  (cond ((content entry)
         (with-io (input (content entry))
           (let ((read 0)
                 (written 0)
                 (crc #xFFFFFFFF)
                 (encryption-state (make-encryption-state (encryption-method entry) password))
                 (compression-state (make-compression-state (compression-method entry))))
             (labels ((write-out (buffer start end)
                        (incf written (- end start))
                        (output output buffer start end))
                      (encrypt (buffer start end)
                        (call-with-encrypted-buffer #'write-out buffer start end encryption-state))
                      (compress (buffer start end)
                        (incf read (- end start))
                        (loop for i from start below end
                              do (setf crc (crc32-rotate crc (aref buffer i))))
                        (call-with-compressed-buffer #'encrypt buffer start end compression-state)))
               (etypecase input
                 (stream
                  (when (or (not (typep input 'file-stream))
                            (not (pathname-utils:directory-p input)))
                    (loop with buffer = (make-array 4096 :element-type '(unsigned-byte 8))
                          for read = (read-sequence buffer input)
                          while (< 0 read)
                          do (compress buffer 0 read))))
                 (vector-input
                  (compress (vector-input-vector input) (vector-input-index input) (vector-input-end input)))
                 (directory-input))
               (call-with-completed-compressed-buffer #'encrypt compression-state)
               (call-with-completed-encrypted-buffer #'write-out encryption-state))
             (setf (crc-32 entry) (logxor #xFFFFFFFF crc))
             (setf (size entry) written)
             (setf (uncompressed-size entry) read))))
        ((and (offset entry) (size entry))
         ;; We are copying from source archive. Just transfer the bytes.
         (labels ((write-out (buffer start end)
                    (output output buffer start end)))
           (entry-raw-bytes #'write-out entry)))
        (T
         (setf (crc-32 entry) #xFFFFFFFF)
         (setf (size entry) 0)
         (setf (uncompressed-size entry) 0))))

(defun determine-min-version (zip64-used)
  ;; FIXME: be smarter about noting the min version based on other used features.
  (if zip64-used
      '(4 5)
      '(2 0)))

(defun encode-file (zip-file output &key password
                                         (version-made *default-version-made*)
                                         version-needed
                                         (zip64 :when-needed))
  (check-type zip64 (member NIL T :when-needed))
  (let ((*zip64-needed* NIL))
    (loop for i from 0
          for entry across (entries zip-file)
          for orig-offset = (offset entry)
          for offset = (index output)
          do (setf (offset entry) offset)
             (backfill-from-content entry)
             (write-structure* (entry-to-lf entry) output)
             ;; TODO: Decryption header and all that guff
             ;; KLUDGE: We temporarily reset the offset of the entry to
             ;;         ensure we can read it from the source archive should
             ;;         the entry be copyable from there.
             (progn
               (setf (offset entry) orig-offset)
               (encode-entry-payload entry output password)
               (setf (offset entry) offset))
             (write-structure* (entry-to-dd entry) output)
             ;; FIXME: If writing to a file-stream or vector, backtrack and
             ;;        Fixup the LF entry with size/crc/flag
          )
    (let* ((cd-start (index output))
           (entries (entries zip-file))
           (entry-count (length entries)))
      (loop for entry across entries
            do (write-structure* (entry-to-cd entry) output))
      (let* ((cd-end (index output))
             (comment (encode-string (comment zip-file)))
             ;; Create EOCD structure here and note overflows, so we
             ;; know whether to write the ZIP64 structures prior to
             ;; writing the EOCD structure.
             (eocd (make-end-of-central-directory
                    0 0
                    (cap-and-note-zip64 entry-count 16)
                    (cap-and-note-zip64 entry-count 16)
                    (cap (- cd-end cd-start) 32)
                    (cap cd-start 32)
                    (length comment) comment))
             (use-zip64-p (or (eq zip64 T)
                              (and (eq zip64 :when-needed) *zip64-needed*)))
             (min-version (determine-min-version use-zip64-p)))
        (cond ((not version-needed)
               (setf version-needed min-version))
              ((version< version-needed min-version)
               (error 'required-version-mismatched
                      :specified-version version-needed :required-version min-version)))
        (cond (use-zip64-p
               (write-structure* (make-end-of-central-directory/64
                                  44
                                  (encode-version version-made)
                                  (encode-version version-needed)
                                  0 0 entry-count entry-count
                                  (- cd-end cd-start) cd-start #())
                                 output)
               (write-structure* (make-end-of-central-directory-locator/64
                                  0 cd-end 1)
                                 output))
              (*zip64-needed*
               (error 'zip64-required :parameter zip64)))
        (write-structure* eocd output)))))
