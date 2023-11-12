; Utilities to extract data from zip files
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Working (needs more testing)

;; TODO: Consider using read-file-into-string to avoid reading the whole file
;; when only a part of it needs to be extracted.

(include-book "decompress-bytes")
(include-book "kestrel/file-io-light/read-file-into-byte-array-stobj" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(local (in-theory (disable mv-nth natp true-listp
                           ;assoc-equal
                           )))

(local (in-theory (enable true-listp-when-string-listp)))

;; ;move
(defund byte-list-listp (vals)
  (declare (xargs :guard t))
  (if (atom vals)
      (null vals)
    (and (byte-listp (first vals))
         (byte-list-listp (rest vals)))))

(defthm byte-list-listp-of-revappend
  (equal (byte-list-listp (revappend x y))
         (and (byte-list-listp (true-list-fix x))
              (byte-list-listp y)))
  :hints (("Goal" :in-theory (enable byte-list-listp revappend))))

(defthm byte-list-listp-of-cons
  (equal (byte-list-listp (cons a x))
         (and (byte-listp a)
              (byte-list-listp x)))
  :hints (("Goal" :in-theory (enable byte-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;move
;; (defund unsigned-byte-list-listp (size vals)
;;   (declare (xargs :guard t))
;;   (if (atom vals)
;;       (null vals)
;;     (and (unsigned-byte-listp size (first vals))
;;          (unsigned-byte-list-listp size (rest vals)))))

;; (defthm unsigned-byte-list-listp-of-revappend
;;   (equal (unsigned-byte-list-listp size (revappend x y))
;;          (and (unsigned-byte-list-listp size (true-list-fix x))
;;               (unsigned-byte-list-listp size y)))
;;   :hints (("Goal" :in-theory (enable unsigned-byte-list-listp revappend))))

;; (defthm unsigned-byte-list-listp-of-cons
;;   (equal (unsigned-byte-list-listp size (cons a x))
;;          (and (unsigned-byte-listp size a)
;;               (unsigned-byte-list-listp size x)))
;;   :hints (("Goal" :in-theory (enable unsigned-byte-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;move
;; (local
;;  (defthm unsigned-byte-listp-8-becomes-byte-listp
;;    (equal (unsigned-byte-listp 8 x)
;;           (byte-listp x))))

;; (defthm unsigned-byte-p-8-of-nth-when-bytesp
;;   (implies (and (bytesp bytes)
;;                 (natp index)
;;                 (< index (len bytes)))
;;            (unsigned-byte-p 8 (nth index bytes)))
;;   :hints (("Goal" :in-theory (enable nth bytesp))))

(defthm bytep-of-bytesi
  (implies (and (byte-array-stobjp byte-array-stobj)
                (natp index)
                (< index (bytes-length byte-array-stobj)))
           (bytep (bytesi index byte-array-stobj)))
  :hints (("Goal" :in-theory (enable byte-array-stobjp bytesi bytes-length))))

(defthm natp-of-bytesi-type
  (implies (and (byte-array-stobjp byte-array-stobj)
                (natp index)
                (< index (bytes-length byte-array-stobj)))
           (natp (bytesi index byte-array-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance bytep-of-bytesi)
           :in-theory (disable bytep-of-bytesi))))

;;almost a dup
(defun map-code-char3 (codes)
  (declare (xargs :guard (byte-listp codes)
                  :guard-hints (("Goal" :in-theory (enable bytep)))
                  ))
  (if (endp codes)
      nil
    (cons (code-char (first codes))
          (map-code-char3 (rest codes)))))

(defun bytelist-to-string3 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (coerce (map-code-char3 bytes) 'string))

;; Returns (mv val index) where val is an unsigned-byte-p 16.
(defund read2little (index byte-array-stobj)
  (declare (xargs :guard (and (natp index)
                              (<= (+ index 2)
                                  (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj))
  (mv (bvcat 8
             (bytesi (+ 1 index) byte-array-stobj) ;last byte is most significant
             8
             (bytesi index byte-array-stobj))
      (+ 2 index)))

(defthm natp-of-mv-nth-0-of-read2little-type
  (natp (mv-nth 0 (read2little index byte-array-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read2little))))

(defthm mv-nth-1-of-read2little
  (equal (mv-nth 1 (read2little index byte-array-stobj))
         (+ 2 index))
  :hints (("Goal" :in-theory (enable read2little))))


;; Returns (mv val index) where val an unsigned-byte-p 32.
(defund read4little (index byte-array-stobj)
  (declare (xargs :guard (and (natp index)
                              (<= (+ index 4)
                                  (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj))
  (mv (bvcat2 8
              (bytesi (+ 3 index) byte-array-stobj) ; most significany byte comes last
              8
              (bytesi (+ 2 index) byte-array-stobj)
              8
              (bytesi (+ 1 index) byte-array-stobj)
              8
              (bytesi index byte-array-stobj))
      (+ 4 index)))

(defthm mv-nth-1-of-read4little
  (equal (mv-nth 1 (read4little index byte-array-stobj))
         (+ 4 index))
  :hints (("Goal" :in-theory (enable read4little))))

(defthm natp-of-mv-nth-0-of-read4little-type
  (natp (mv-nth 0 (read4little index byte-array-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read4little))))

;; Returns a list of bytes.
;; TODO: Add fixnum declares (maybe bound the file length).
(defund readnbytes-from-byte-array-stobj-aux (n index byte-array-stobj acc)
  (declare (xargs :guard (and (natp index)
                              (natp n)
                              (true-listp acc)
                              (<= (+ n index) (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj))
  (if (zp n)
      (reverse acc)
    (readnbytes-from-byte-array-stobj-aux (+ -1 n) (+ 1 index) byte-array-stobj (cons (bytesi index byte-array-stobj) acc))))

(defthm byte-listp-of-readnbytes-from-byte-array-stobj-aux
  (implies (and (byte-listp acc)
                (<= (+ n index) (bytes-length byte-array-stobj))
                (natp index)
                (natp n)
                (byte-array-stobjp byte-array-stobj))
           (byte-listp (readnbytes-from-byte-array-stobj-aux n index byte-array-stobj acc)))
  :hints (("Goal" :in-theory (enable readnbytes-from-byte-array-stobj-aux))))

(defthm byte-listp-of-readnbytes-from-byte-array-stobj-aux
  (implies (and (byte-listp acc)
                (<= (+ n index) (bytes-length byte-array-stobj))
                (natp index)
                (natp n)
                (byte-array-stobjp byte-array-stobj))
           (byte-listp (readnbytes-from-byte-array-stobj-aux n index byte-array-stobj acc)))
  :hints (("Goal" :in-theory (enable readnbytes-from-byte-array-stobj-aux))))

;; Returns (mv erp bytes index) where bytes is a list of bytes.
;; TODO: Why return the new index?
(defund readnbytes-from-byte-array-stobj (n index byte-array-stobj)
  (declare (xargs :guard (and (natp index)
                              (natp n))
                  :stobjs byte-array-stobj))
  (if (<= (bytes-length byte-array-stobj) (+ index n))
      (mv :not-enough-bytes nil
          (+ n index) ; irrelevant, for uniformity
          )
    (let ((bytes (readnbytes-from-byte-array-stobj-aux n index byte-array-stobj nil)))
      (mv nil bytes (+ n index)))))

(defthm mv-nth-0-of-readnbytes-from-byte-array-stobj
  (equal (mv-nth 0 (readnbytes-from-byte-array-stobj n index byte-array-stobj))
         (if (<= (bytes-length byte-array-stobj) (+ index n))
             :not-enough-bytes
           nil))
  :hints (("Goal" :in-theory (enable readnbytes-from-byte-array-stobj))))

(defthm byte-listp-of-mv-nth-1-of-readnbytes-from-byte-array-stobj
  (implies (and; (<= (+ n index) (bytes-length byte-array-stobj))
                (natp index)
                (natp n)
                (byte-array-stobjp byte-array-stobj))
           (byte-listp (mv-nth 1 (readnbytes-from-byte-array-stobj n index byte-array-stobj))))
  :hints (("Goal" :in-theory (enable readnbytes-from-byte-array-stobj))))

(defthm natp-of-mv-nth-1-of-readnbytes-from-byte-array-stobj
  (implies (and (natp index)
                (natp n))
           (natp (mv-nth 2 (readnbytes-from-byte-array-stobj n index byte-array-stobj))))
  :hints (("Goal" :in-theory (enable readnbytes-from-byte-array-stobj))))

;; TODO: Add more
(defconst *compression-method-alist*
  '((0 . :no-compression)
    (8 . :deflate)))

;todo: handle multiple "disks"
(defund read-end-of-central-directory-record (index byte-array-stobj)
  (declare (xargs :guard (and (natp index)
                              (<= (+ index 22)
                                  (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj))
  (b* (((mv end-of-central-dir-signature                  index) (read4little index byte-array-stobj))
       ((mv number-of-this-disk                           index) (read2little index byte-array-stobj))
       ((mv number-of-disk-with-start-of-central-dir      index) (read2little index byte-array-stobj))
       ((mv number-of-entries-in-central-dir-of-this-disk index) (read2little index byte-array-stobj))
       ((mv number-of-entries-in-central-dir              index) (read2little index byte-array-stobj))
       ((mv size-of-central-dir                           index) (read4little index byte-array-stobj))
       ((mv offset-of-start-of-central-dir                index) (read4little index byte-array-stobj))
       ((mv comment-length                                &) (read2little index byte-array-stobj))
       ;; todo: comment (if room)
       )
       `((:end-of-central-dir-signature . ,end-of-central-dir-signature)
         (:number-of-this-disk . ,number-of-this-disk)
         (:number-of-disk-with-start-of-central-dir . ,number-of-disk-with-start-of-central-dir)
         (:number-of-entries-in-central-dir-of-this-disk . ,number-of-entries-in-central-dir-of-this-disk)
         (:number-of-entries-in-central-dir . ,number-of-entries-in-central-dir)
         (:size-of-central-dir . ,size-of-central-dir)
         (:offset-of-start-of-central-dir . ,offset-of-start-of-central-dir)
         (:comment-length . ,comment-length))))

(local
 (defthm alistp-of-read-end-of-central-directory-record
  (alistp (read-end-of-central-directory-record index byte-array-stobj))
  :hints (("Goal" :in-theory (enable read-end-of-central-directory-record)))))

;; Read and parse the central directory header at the INDEXth byte (0-based) in the BYTE-ARRAY-STOBJ.
;; The central directory contains a sequence of these headers, one for each path in the zipfile.
;; Returns (mv erp parsed-header index) where INDEX is the start of the next central directory header.
(defund read-central-directory-header (index byte-array-stobj)
  (declare (xargs :guard (natp index)
                  :stobjs byte-array-stobj))
  (b* (((when (> (+ index 46) ; size of required part
                 (bytes-length byte-array-stobj)))
        (mv :not-enough-bytes nil index))
       ((mv central-file-header-signature index) (read4little index byte-array-stobj))
       ((mv version-made-by               index) (read2little index byte-array-stobj))
       ((mv version-needed-to-extract index) (read2little index byte-array-stobj))
       ((mv general-purpose-bit-flag index) (read2little index byte-array-stobj))
       ((mv compression-method index) (read2little index byte-array-stobj))
       ((mv last-mod-file-time index) (read2little index byte-array-stobj))
       ((mv last-mod-file-date index) (read2little index byte-array-stobj))
       ((mv crc-32 index) (read4little index byte-array-stobj))
       ((mv compressed-size index) (read4little index byte-array-stobj))
       ((mv uncompressed-size index) (read4little index byte-array-stobj))
       ((mv file-name-length index) (read2little index byte-array-stobj))
       ((mv extra-field-length index) (read2little index byte-array-stobj))
       ((mv file-comment-length index) (read2little index byte-array-stobj))
       ((mv disk-number-start index) (read2little index byte-array-stobj))
       ((mv internal-file-attributes index) (read2little index byte-array-stobj))
       ((mv external-file-attributes index) (read4little index byte-array-stobj))
       ((mv relative-offset-of-local-header index) (read4little index byte-array-stobj))
       ((mv erp file-name-bytes index) (readnbytes-from-byte-array-stobj file-name-length index byte-array-stobj))
       ((when erp) (mv :not-enough-bytes nil index))
       (file-name (bytelist-to-string3 file-name-bytes)) ;todo: unicode?  odd char sets?
       ((mv erp extra-field-bytes index) (readnbytes-from-byte-array-stobj extra-field-length index byte-array-stobj))
       ((when erp) (mv :not-enough-bytes nil index))
       ((mv erp file-comment-bytes index) (readnbytes-from-byte-array-stobj file-comment-length index byte-array-stobj))
       ((when erp) (mv :not-enough-bytes nil index))
       (file-comment (bytelist-to-string3 file-comment-bytes)) ;todo: unicode?  odd char sets?
       )
    (mv nil ; no error
        `((:central-file-header-signature . ,central-file-header-signature)
          (:version-made-by . ,version-made-by)
          (:version-needed-to-extract . ,version-needed-to-extract)
          (:general-purpose-bit-flag . ,general-purpose-bit-flag)
          (:compression-method . ,compression-method)
          (:last-mod-file-time . ,last-mod-file-time)
          (:last-mod-file-date . ,last-mod-file-date)
          (:crc-32 . ,crc-32)
          (:compressed-size . ,compressed-size)
          (:uncompressed-size . ,uncompressed-size)
          ;; (:file-name-length . ,file-name-length)
          ;; (:extra-field-length . ,extra-field-length)
          ;; (:file-comment-length . ,file-comment-length)
          (:disk-number-start . ,disk-number-start)
          (:internal-file-attributes . ,internal-file-attributes)
          (:external-file-attributes . ,external-file-attributes)
          (:relative-offset-of-local-header . ,relative-offset-of-local-header)
          (:file-name . ,file-name)
          (:extra-field . ,extra-field-bytes)
          (:file-comment . ,file-comment))
        index)))

(defthm alistp-of-mv-nth-1-of-read-central-directory-header
  (alistp (mv-nth 1 (read-central-directory-header index byte-array-stobj)))
  :hints (("Goal" :in-theory (enable read-central-directory-header))))

;; needs more hyps
;; (defthm natp-of-lookup-equal-of-compress-size-of-mv-nth-1-of-read-central-directory-header
;;   (implies (and (<= (+ 46 index)
;;                     (bytes-length byte-array-stobj))
;;                 (byte-array-stobjp byte-array-stobj))
;;            (natp (lookup-equal :compressed-size (mv-nth 1 (read-central-directory-header index byte-array-stobj)))))
;;   :hints (("Goal" :in-theory (enable read-central-directory-header))))

(defthm natp-of-mv-nth-2-of-read-central-directory-header
  (implies (natp index)
           (natp (mv-nth 2 (read-central-directory-header index byte-array-stobj))))
  :hints (("Goal" :in-theory (enable read-central-directory-header))))

;; Returns (mv erp header index)
;; TODO: Read less of this?
(defund read-local-file-header (index byte-array-stobj)
  (declare (xargs :guard (natp index)
                  :stobjs byte-array-stobj))
  (b* (((when (> (+ index 30) ; size of required part
                 (bytes-length byte-array-stobj)))
        (mv :not-enough-bytes-for-local-file-header nil index))
       ((mv local-file-header-signature index) (read4little index byte-array-stobj))
       ((mv version-needed-to-extract index) (read2little index byte-array-stobj))
       ((mv general-purpose-bit-flag index) (read2little index byte-array-stobj))
       ((mv compression-method index) (read2little index byte-array-stobj))
       ((mv last-mod-file-time index) (read2little index byte-array-stobj))
       ((mv last-mod-file-date index) (read2little index byte-array-stobj))
       ((mv crc-32 index) (read4little index byte-array-stobj))
       ((mv compressed-size index) (read4little index byte-array-stobj))
       ((mv uncompressed-size index) (read4little index byte-array-stobj))
       ((mv file-name-length index) (read2little index byte-array-stobj))
       ((mv extra-field-length index) (read2little index byte-array-stobj))
       ((mv erp file-name-bytes index) (readnbytes-from-byte-array-stobj file-name-length index byte-array-stobj))
       ((when erp) (mv :not-enough-bytes nil index))
       (file-name (bytelist-to-string3 file-name-bytes))
       ((mv erp extra-field-bytes index) (readnbytes-from-byte-array-stobj extra-field-length index byte-array-stobj))
       ((when erp) (mv :not-enough-bytes nil index)))
    (mv (erp-nil)
        `((:local-file-header-signature . ,local-file-header-signature)
          (:version-needed-to-extract . ,version-needed-to-extract)
          (:general-purpose-bit-flag . ,general-purpose-bit-flag)
          (:compression-method . ,compression-method)
          (:last-mod-file-time . ,last-mod-file-time)
          (:last-mod-file-date . ,last-mod-file-date)
          (:crc-32 . ,crc-32)
          (:compressed-size . ,compressed-size)
          (:uncompressed-size . ,uncompressed-size)
          ;; file-name-length
          ;; extra-field-length
          (:file-name . ,file-name)
          (:extra-field . ,extra-field-bytes))
        index)))

(local
 (defthm natp-of-mv-nth-2-of-read-local-file-header
   (implies (natp index)
            (natp (mv-nth 2 (read-local-file-header index byte-array-stobj))))
   :hints (("Goal" :in-theory (enable read-local-file-header)))))

;; Check whether the BYTES are present in BYTE-ARRAY-STOBJ's byte array, starting at
;; position INDEX.
(defun bytes-present-at-indexp (bytes index byte-array-stobj)
  (declare (xargs :guard (and (byte-listp bytes)
                              (natp index)
                              (<= (+ index (len bytes))
                                  (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj))
  (if (endp bytes)
      t
    (and (equal (first bytes)
                (bytesi index byte-array-stobj))
         (bytes-present-at-indexp (rest bytes) (+ 1 index) byte-array-stobj))))

;; Return the highest index <= INDEX at which the BYTES are present in
;; BYTE-ARRAY-STOBJ's byte array, or nil if they cannot be found.
(defun search-backward-for-byte-sequence (bytes index byte-array-stobj)
  (declare (xargs :guard (and (byte-listp bytes)
                              (or (natp index)
                                  (equal -1 index))
                              (<= (+ index (len bytes))
                                  (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj
                  :measure (nfix (+ 1 index))
                  ))
  (if (not (natp index))
      nil ; not found
    (if (bytes-present-at-indexp bytes index byte-array-stobj)
        index
      (search-backward-for-byte-sequence bytes (+ -1 index) byte-array-stobj))))

(defthm <=-of-search-backward-for-byte-sequence-linear
  (implies (and (search-backward-for-byte-sequence bytes index byte-array-stobj)
                (natp index))
           (<= (search-backward-for-byte-sequence bytes index byte-array-stobj) index))
  :rule-classes :linear
  :hints (("Goal" :expand (search-backward-for-byte-sequence bytes 0 byte-array-stobj)
           :in-theory (enable search-backward-for-byte-sequence))))

;; Returns (mv erp end-of-central-directory-record byte-array-stobj state), where
;; BYTE-ARRAY-STOBJ has been populated with the contents of FILENAME.
(defund read-file-and-locate-end-of-central-directory-record (filename byte-array-stobj state)
  (declare (xargs :guard (stringp filename)
                  :stobjs (byte-array-stobj state)))
  (b* (;; Read in the whole file (TODO: Can we read in less?):
       ((mv erp byte-array-stobj state) (read-file-into-byte-array-stobj filename byte-array-stobj state))
       ((when erp)
        (er hard? 'read-file-and-locate-end-of-central-directory-record "Failed to read file ~x0." filename)
        (mv :error-reading-file-into-stobj nil byte-array-stobj state))
       (len (bytes-length byte-array-stobj))
       ((when (< len 22))
        (mv :not-enough-bytes nil byte-array-stobj state))
       ;;((mv erp file-infos bytes) (read-file-infos bytes nil))
       (maybe-end-of-central-directory-record
        (search-backward-for-byte-sequence '(#x50 #x4b #x05 #x06)
                                           ;; must be enough room for the end of central directory record:
                                           (+ -22 len)
                                           byte-array-stobj))
       ((when (not maybe-end-of-central-directory-record))
        (mv :cant-find-end-of-central-directory-record nil byte-array-stobj state))
       ;; TODO: Allow for spurious matches of the above step with bytes in the signature
       (end-of-central-directory-record (read-end-of-central-directory-record maybe-end-of-central-directory-record byte-array-stobj)))
    (mv (erp-nil)
        end-of-central-directory-record byte-array-stobj state)))

(local
 (defthm alistp-of-mv-nth-1-of-read-file-and-locate-end-of-central-directory-record
   (alistp (mv-nth 1 (read-file-and-locate-end-of-central-directory-record filename byte-array-stobj state)))
   :hints (("Goal" :in-theory (enable read-file-and-locate-end-of-central-directory-record)))))

;; Go through the central-directory-headers.  For each, add the file name and size to the result
;; Returns (mv erp file-infos index)
(defun read-stored-file-info (num-headers index byte-array-stobj acc)
  (declare (xargs :guard (and (natp num-headers)
                              (natp index)
                              (true-listp acc))
                  :stobjs byte-array-stobj))
  (if (zp num-headers)
      (mv (erp-nil) (reverse acc) index)
    (b* (((mv erp header index) (read-central-directory-header index byte-array-stobj))
         ((when erp) (mv erp nil index))
         ;; (relative-offset-of-local-header (nfix (lookup-eq :RELATIVE-OFFSET-OF-LOCAL-HEADER header)))
         ;; ((mv erp local-file-header index2) (read-local-file-header relative-offset-of-local-header byte-array-stobj))
         ;; ((when erp) (mv erp nil index))
         ;; ;; TODO: allow an encryption header to appear here
         ;; (compressed-size (nfix (lookup-eq :compressed-size local-file-header)))
         ;; ((mv erp file-data &) (readnbytes-from-byte-array-stobj compressed-size index2 byte-array-stobj))
         ;; ((when erp) (mv erp nil index))
         ;; (compression-method (nfix (lookup-eq :compression-method local-file-header)))
         ;; ((when (not (or (equal 8 compression-method)
         ;;                 (equal 0 compression-method))))
         ;;  (mv :unknown-compression-method nil index))
         )
      (read-stored-file-info (+ -1 num-headers)
                             index
                             byte-array-stobj
                             (cons `((:file-name . ,(lookup-eq :file-name header))
                                     (:uncompressed-size ,(lookup-eq :uncompressed-size header))
                                     (:compressed-size ,(lookup-eq :compressed-size header))
                                     (:compression-method ,(lookup-eq :compression-method header)))
                                   acc)))))

;; Returns information about the contents of the zipfile.
;; Returns (mv erp contents-list byte-array-stobj state).
;; Example call (describe-zipfile-contents "hello.zip" byte-array-stobj state).
(defun describe-zipfile-contents (zip-filename byte-array-stobj state)
  (declare (xargs :guard (stringp zip-filename)
                  :stobjs (byte-array-stobj state)))
  (b* (((mv erp end-of-central-directory-record byte-array-stobj state)
        (read-file-and-locate-end-of-central-directory-record zip-filename byte-array-stobj state))
       ((when erp) (mv erp nil byte-array-stobj state))
       (num-entries (nfix (lookup-eq :number-of-entries-in-central-dir end-of-central-directory-record)))
       (central-dir-offset (nfix (lookup-eq :offset-of-start-of-central-dir end-of-central-directory-record))) ; todo: drop the nfix
       ((mv erp stored-file-info &) (read-stored-file-info num-entries central-dir-offset byte-array-stobj nil))
       ((when erp) (mv erp nil byte-array-stobj state))
       )
    (mv (erp-nil)
        stored-file-info
        byte-array-stobj
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp path-to-decompressed-bytes-alist).
;; Go through the central-directory-headers.  For each, if it'sin the target-paths, read its and decompress corresponding file, including its local-file-header.
;; TODO: What if the same path appears multiple times in the .zip?  There are security issues related that that (e.g., in Android).
;; Is index really more of an offset?
(defund unzip-files (target-paths
                     num-headers
                     index ; location of the next central directory header to read, an index in the byte-array-stobj
                     verbosep
                     byte-array-stobj
                     acc)
  (declare (xargs :guard (and (or (string-listp target-paths)
                                  (eq target-paths :all))
                              (natp num-headers)
                              (natp index)
                              (booleanp verbosep)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable read-central-directory-header)))
                  :stobjs byte-array-stobj))
  (if (zp num-headers)
      (mv (erp-nil) (reverse acc)) ; could skip the reverse if desired
    (b* (                            ;; Read the next central directory header:
         ((mv erp header index) (read-central-directory-header index byte-array-stobj)) ; todo: we could proces less than the whole header, but they are variable size
         ((when erp) (mv erp nil))
         ;; Get the file path:
         (filename (lookup-eq :file-name header)) ; really a whole path
         ((when (not (stringp filename))) ; can this happen?
          (mv `(:bad-filename ,filename) nil))
         ;; Add an entry for this path, if it is one we want to extract:
         ((mv erp acc)
          (if (or (eq target-paths :all)
                  (member-equal filename target-paths))
              (b* ((- (and verbosep (cw "Exracting ~s0.~%" filename))) ; todo: option to suppress this and other printing
                   (compressed-size (lookup-eq :compressed-size header))
                   (- (and verbosep (cw "  Size: ~x0.~%" compressed-size)))
                   (compression-method (lookup-eq :compression-method header))
                   (- (and verbosep (cw "  Compression method: ~x0.~%" compression-method)))
                   (relative-offset-of-local-header (nfix (lookup-eq :relative-offset-of-local-header header)))
                   ((mv erp & ; local-file-header
                        index2) (read-local-file-header relative-offset-of-local-header byte-array-stobj))
                   ((when erp) (mv erp nil))
                   ;; TODO: allow an encryption header to appear here
                   ;; (compressed-size (nfix (lookup-eq :compressed-size local-file-header))) ;; TODO: I've seen the compressed size in the local file header be zero.
                   ((mv erp file-data &) (readnbytes-from-byte-array-stobj compressed-size index2 byte-array-stobj))
                   ((when erp) (mv erp nil))
                   (decoded-compression-method (cdr (assoc compression-method *compression-method-alist*)))
                   ((when (not decoded-compression-method))
                    (mv :unknown-compression-method nil))
                   ;; todo: pull out this pattern:
                   (decompressed-file-bytes (if (= 0 compressed-size) ; might be a directory
                                                nil
                                              (if (eq decoded-compression-method :no-compression)
                                                  file-data
                                                ;; must be :deflate, at least for now:
                                                (decompress-bytes file-data decoded-compression-method))))
                   ((when (not (byte-listp decompressed-file-bytes))) ; todo: optimize! needed for byte-list-listp-of-strip-cdrs-of-mv-nth-1-of-unzip-files below
                    (mv :bad-bytes nil))
                   )
                (mv (erp-nil) (acons filename decompressed-file-bytes acc)))
            (mv (erp-nil) acc)))
         ((when erp) (mv erp nil)))
      (unzip-files target-paths (+ -1 num-headers) index verbosep byte-array-stobj acc))))

(defthm alist-of-mv-nth-1-of-unzip-files
  (implies (alistp acc)
           (alistp (mv-nth 1 (unzip-files target-paths num-headers index verbosep byte-array-stobj acc))))
  :hints (("Goal" :in-theory (enable unzip-files))))

(defthm string-listp-of-strip-cars-of-mv-nth-1-of-unzip-files
  (implies (string-listp (strip-cars acc))
           (string-listp (strip-cars (mv-nth 1 (unzip-files target-paths num-headers index verbosep byte-array-stobj acc)))))
  :hints (("Goal" :in-theory (enable unzip-files))))

(defthm byte-list-listp-of-strip-cdrs-of-mv-nth-1-of-unzip-files
  (implies (and (byte-list-listp (strip-cdrs acc))
                (true-listp acc))
           (byte-list-listp (strip-cdrs (mv-nth 1 (unzip-files target-paths num-headers index verbosep byte-array-stobj acc)))))
  :hints (("Goal" :in-theory (enable unzip-files))))


;; Returns (mv erp path-to-decompressed-bytes-alist byte-array-stobj state).
;; The path-to-decompressed-bytes-alist maps paths in the zipfile to byte
;; lists (directories map to empty byte lists).
;; Example calls:
;; (unzip "hello.zip" '("hello.txt") byte-array-stobj state)
;; (unzip "hello.zip" :all byte-array-stobj state)
;; (unzip "../derivations/monitor/cp-2.4/rosjava/AIJ.jar" :all byte-array-stobj state)
(defund unzip (zip-filename
               paths ; paths within the zipfile to be extracted, or :all
               verbosep
               byte-array-stobj state)
  (declare (xargs :guard (and (stringp zip-filename)
                              (or (eq :all paths)
                                  (string-listp paths))
                              (booleanp verbosep))
                  :stobjs (byte-array-stobj state)))
  (b* (((mv erp end-of-central-directory-record byte-array-stobj state)
        (read-file-and-locate-end-of-central-directory-record zip-filename byte-array-stobj state))
       ((when erp) (mv erp nil byte-array-stobj state))
       (num-entries (nfix (lookup-eq :number-of-entries-in-central-dir end-of-central-directory-record))) ; todo: drop the nfix
       (central-dir-offset (nfix (lookup-eq :offset-of-start-of-central-dir end-of-central-directory-record)))
       ;; Decompress the desired files:
       ((mv erp path-to-decompressed-bytes-alist) (unzip-files paths num-entries central-dir-offset verbosep byte-array-stobj nil))
       ((when erp) (mv erp nil byte-array-stobj state))
       ;; Check whether any of the desired files were missing:
       (missing-paths (if (eq :all paths)
                          nil
                        (let ((found-paths (strip-cars path-to-decompressed-bytes-alist)))
                          (set-difference-equal paths found-paths))))
       ((when missing-paths)
        (er hard? 'unzip "Missing paths in ~x0: ~X12." zip-filename missing-paths nil)
        (mv `(:missing-paths-in-zip ,@missing-paths) nil byte-array-stobj state)))
    (mv (erp-nil) path-to-decompressed-bytes-alist byte-array-stobj state)))

(defthm alistp-of-mv-nth-1-of-unzip
  (alistp (mv-nth 1 (unzip zip-filename paths verbosep byte-array-stobj state)))
  :hints (("Goal" :in-theory (enable unzip))))

(defthm string-listp-of-strip-cars-of-mv-nth-1-of-unzip
  (string-listp (strip-cars (mv-nth 1 (unzip zip-filename paths verbosep byte-array-stobj state))))
  :hints (("Goal" :in-theory (enable unzip))))

(defthm byte-list-listp-of-strip-cdrs-of-mv-nth-1-of-unzip
  (byte-list-listp (strip-cdrs (mv-nth 1 (unzip zip-filename paths verbosep byte-array-stobj state))))
  :hints (("Goal" :in-theory (enable unzip))))
