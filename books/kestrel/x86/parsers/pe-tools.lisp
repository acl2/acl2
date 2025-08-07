; Tools for processing the alists that represent parsed PE files.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Should these be in a PE package?

(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system) ; todo: replace uses of this with proper error returns
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/memory/memory-regions" :dir :system)
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(in-theory (disable mv-nth))

(local (in-theory (e/d (rationalp-when-natp
                        acl2-numberp-when-natp)
                       (natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm alistp-when-symbol-alistp
    (implies (symbol-alistp x)
             (alistp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pe-section-headerp (h)
  (declare (xargs :guard t))
  (and (symbol-alistp h)
       (natp (lookup-equal :virtual-address h))
       (natp (lookup-equal :virtual-size h))))

(local
  (defthm alistp-when-pe-section-headerp
    (implies (pe-section-headerp h)
             (alistp h))
    :hints (("Goal" :in-theory (enable pe-section-headerp)))))

(local
  (defthm natp-of-lookup-equal-of-virtual-address
      (implies (pe-section-headerp h)
               (natp (lookup-equal :virtual-address h)))
    :hints (("Goal" :in-theory (enable pe-section-headerp)))))

(local
  (defthm natp-of-lookup-equal-of-virtual-size
      (implies (pe-section-headerp h)
               (natp (lookup-equal :virtual-size h)))
    :hints (("Goal" :in-theory (enable pe-section-headerp)))))

(defund pe-section-infop (info)
  (declare (xargs :guard t))
  (and (symbol-alistp info)
       (let ((header (lookup-eq :header info))
             (bytes (lookup-eq :raw-data info)))
         (and (pe-section-headerp header)
              (byte-listp bytes)))))

(defund pe-sectionp (section)
  (declare (xargs :guard t))
  (and (consp section)
       (let ((name (first section))
             (info (rest section)))
         (and (stringp name)
              (pe-section-infop info)))))

(local
  (defthm pe-section-infop-of-cdr
    (implies (pe-sectionp sec)
             (pe-section-infop (cdr sec)))
    :hints (("Goal" :in-theory (enable pe-sectionp)))))

(defthmd pe-sectionp-consequences
  (implies (pe-section-infop sec)
           (and (symbol-alistp sec)
                (byte-listp (lookup-equal :raw-data sec))
                (pe-section-headerp (lookup-equal :header sec))))
  :hints (("Goal" :in-theory (enable pe-section-infop
                                     pe-section-headerp))))

(local (in-theory (enable pe-sectionp-consequences)))

(defund pe-section-listp (sections)
  (declare (xargs :guard t))
  (if (not (consp sections))
      (null sections)
    (and (pe-sectionp (first sections))
         (pe-section-listp (rest sections)))))

(local
  (defthm consp-of-nth-when-pe-section-listp-iff
    (implies (pe-section-listp sections)
             (iff (consp (nth n sections))
                  (nth n sections)))
    :hints (("Goal" :in-theory (enable pe-section-listp pe-sectionp nth)))))

(local
  (defthm pe-sectionp-of-nth
    (implies (and (pe-section-listp sections)
                  (natp n)
                  (< n (len sections)))
             (pe-sectionp (nth n sections)))
    :hints (("Goal" :in-theory (enable pe-section-listp nth)))))

(defun pe-symbol-table-entryp (entry)
  (declare (xargs :guard t))
  (symbol-alistp entry))

(defun pe-symbol-tablep (entries)
  (declare (xargs :guard t))
  (if (not (consp entries))
      (null entries)
    (and (pe-symbol-table-entryp (first entries))
         (pe-symbol-tablep (rest entries)))))

(defund parsed-pe-p (pe)
  (declare (xargs :guard t))
  (and (symbol-alistp pe)
       (pe-section-listp (lookup-eq :sections pe))
       (pe-symbol-tablep (lookup-eq :symbol-table pe))
       (symbol-alistp (lookup-eq :optional-header-standard-fields pe))
       (symbol-alistp (lookup-eq :coff-file-header pe))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund get-pe-sections (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (acl2::lookup-eq-safe :sections parsed-pe))

(defthm pe-section-listp-of-get-pe-sections
  (implies (parsed-pe-p parsed-pe)
           (pe-section-listp (get-pe-sections parsed-pe)))
  :hints (("Goal" :in-theory (enable get-pe-sections parsed-pe-p))))

(local
  (defthm true-listp-when-pe-section-listp
    (implies (pe-section-listp sections)
             (true-listp sections))
    :hints (("Goal" :in-theory (enable pe-section-listp)))))

;; Returns (mv erp info) where INFO is the section-info (an alist).
(defund get-pe-section-info-aux (name sections)
  (declare (xargs :guard (and (stringp name)
                              (pe-section-listp sections))
                  :guard-hints (("Goal" :in-theory (enable pe-section-listp
                                                           pe-sectionp)))))
  (if (endp sections)
      ;(er hard? 'get-pe-section-info-aux "Can't find section named ~x0." name)
      (mv :section-not-found nil)
    (let* ((entry (first sections))
           (this-name (car entry)))
      (if (equal this-name name)
          (mv nil (cdr entry))
        (get-pe-section-info-aux name (rest sections))))))

(local
  (defthm pe-section-infop-of-mv-nth-1-of-get-pe-section-info-aux
    (implies (and (not (mv-nth 0 (get-pe-section-info-aux section-name sections))) ; no error
                  (pe-section-listp sections))
             (pe-section-infop (mv-nth 1 (get-pe-section-info-aux section-name sections))))
    :hints (("Goal" :in-theory (enable get-pe-section-info-aux pe-section-listp)))))

;; Returns (mv erp info) where INFO is the section-info (an alist).
(defund get-pe-section-info (section-name parsed-pe)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-pe-p parsed-pe))))
  (get-pe-section-info-aux section-name (get-pe-sections parsed-pe)))

(defthm pe-section-infop-of-mv-nth-1-of-get-pe-section-info
  (implies (and (not (mv-nth 0 (get-pe-section-info section-name parsed-pe)))
                (parsed-pe-p parsed-pe))
           (pe-section-infop (mv-nth 1 (get-pe-section-info section-name parsed-pe))))
  :hints (("Goal" :in-theory (enable get-pe-section-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp info) where INFO is the section-info (an alist).
;; numbering starts at 1
(defund get-numbered-pe-section-info (section-num parsed-pe)
  (declare (xargs :guard (and (posp section-num)
                              (parsed-pe-p parsed-pe))
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (let* ((sections (get-pe-sections parsed-pe))
         (n (+ -1 section-num)) ; n is 0-based
         )
    (if (>= n (len sections))
        (mv :no-such-section nil)
      (mv nil (cdr (nth n sections))))))

(defthm pe-section-infop-of-mv-nth-1-of-get-numbered-pe-section-info
  (implies (and (not (mv-nth 0 (get-numbered-pe-section-info section-num parsed-pe))) ; no error
                (posp section-num)
                (parsed-pe-p parsed-pe))
           (pe-section-infop (mv-nth 1 (get-numbered-pe-section-info section-num parsed-pe))))
  :hints (("Goal"
           :in-theory (enable get-numbered-pe-section-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp info) where INFO is the section-info (an alist).
(defund get-pe-text-section-info (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)))
  (get-pe-section-info ".text" parsed-pe))

(defthm pe-section-infop-mv-nth-1-of-get-pe-text-section-info
  (implies (and (not (mv-nth 0 (get-pe-text-section-info parsed-pe))) ; no error
                (parsed-pe-p parsed-pe))
           (pe-section-infop (mv-nth 1 (get-pe-text-section-info parsed-pe))))
  :hints (("Goal" :in-theory (enable get-pe-text-section-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund get-pe-section-info-bytes (section-info)
  (declare (xargs :guard (pe-section-infop section-info)))
  (acl2::lookup-eq-safe :raw-data section-info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp bytes)
(defund get-pe-text-section-bytes (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p pe-section-listp)))
                  ))
  (b* (((mv erp info) (get-pe-text-section-info parsed-pe))
       ((when erp) (mv erp nil)))
    (mv nil (get-pe-section-info-bytes info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return (mv erp rva).
(defund get-pe-section-rva (section-name parsed-pe)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-pe-p parsed-pe))))
  (b* (((mv erp section-info) (get-pe-section-info section-name parsed-pe))
       ((when erp) (mv erp 0))
       (header (lookup-eq-safe :header section-info))
       (section-rva (lookup-eq-safe :virtual-address header)))
    (mv nil section-rva)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rva)
(defund get-numbered-pe-section-rva (section-num parsed-pe)
  (declare (xargs :guard (and (posp section-num)
                              (parsed-pe-p parsed-pe))))
  (b* (((mv erp section-info) (get-numbered-pe-section-info section-num parsed-pe))
       ((when erp) (mv erp 0))
       (header (lookup-eq-safe :header section-info))
       (section-rva (lookup-eq-safe :virtual-address header)))
    (mv nil section-rva)))

(defthm natp-of-mv-nth-1-of-get-numbered-pe-section-rva
  (implies (and (posp section-num)
                (parsed-pe-p parsed-pe))
           (natp (mv-nth 1 (get-numbered-pe-section-rva section-num parsed-pe))))
  :hints (("Goal" :in-theory (enable get-numbered-pe-section-rva))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun section-containing-rva (sections rva)
  (declare (xargs :guard (and (pe-section-listp sections)
                              (natp rva))
                  :guard-hints (("Goal" :expand (pe-section-listp sections)
                                 :in-theory (enable pe-section-listp pe-sectionp
                                                    pe-section-infop)))))
  (if (endp sections)
      (er hard? 'section-containing-rva "No more sections.  Did not find RVA ~x0." rva)
    (let* ((section (first sections))
           (section-name (car section))
           (section-info (cdr section))
           (header (lookup-eq-safe :header section-info))
           (section-rva (lookup-eq-safe :virtual-address header))
           (section-size (lookup-eq-safe :virtual-size header)))
      (if (and (<= section-rva rva)
               (< rva (+ section-rva section-size)))
          section-name
        ;; RVA is not in this section, so keep looking
        (section-containing-rva (rest sections) rva)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Relative to the base of the image
(defund get-pe-entry-point (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (let* ((optional-header-standard-fields (lookup-eq-safe :optional-header-standard-fields parsed-pe)))
    (lookup-eq-safe :address-of-entry-point optional-header-standard-fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Relative to the base of the image
(defund get-pe-base-of-code (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (let* ((optional-header-standard-fields (lookup-eq-safe :optional-header-standard-fields parsed-pe)))
    (lookup-eq-safe :base-of-code optional-header-standard-fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lookup-pe-symbol (name symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (pe-symbol-tablep symbol-table))))
  (if (endp symbol-table)
      nil
    (if (equal name (acl2::lookup-eq-safe :name (first symbol-table)))
        (first symbol-table)
      (lookup-pe-symbol name (rest symbol-table)))))

(defthm alistp-of-lookup-pe-symbol
  (implies (pe-symbol-tablep symbol-table)
           (alistp (lookup-pe-symbol name symbol-table)))
  :hints (("Goal" :in-theory (enable pe-symbol-tablep lookup-pe-symbol))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This assumes we have a symbol table to find the address of the subroutine
(defun subroutine-address-within-text-section-pe-64 (subroutine-name
                                                     parsed-pe)
  (declare (xargs :guard (and (stringp subroutine-name)
                              (parsed-pe-p parsed-pe))
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-address-within-text-section-pe-64 "No symbol table present."))
       (symbol-record (acl2::lookup-pe-symbol subroutine-name symbol-table))
       ((when (not symbol-record))
        (er hard? 'subroutine-address-within-text-section-pe-64 "Can't find ~x0 in symbol table." subroutine-name))
       (subroutine-address-within-text-section (acl2::lookup-eq-safe :value symbol-record)))
    subroutine-address-within-text-section))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv offset-to-subroutine section-number).  Throws an error if not found
(defun subroutine-offset-and-section-number-pe-32 (target parsed-pe)
  (declare (xargs :guard (and (stringp target)
                              (parsed-pe-p parsed-pe))
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-offset-pe-32 "No symbol table present.")
        (mv nil nil))
       (symbol-record (acl2::lookup-pe-symbol target symbol-table))
       (offset-to-subroutine (acl2::lookup-eq-safe :value symbol-record)) ;relative to the base of the section?
       (section-number (acl2::lookup-eq-safe :section-number symbol-record)))
    (mv offset-to-subroutine section-number)))

(defun subroutine-offset-pe-32 (target parsed-pe)
  (declare (xargs :guard (and (stringp target)
                              (parsed-pe-p parsed-pe))))
  (mv-let (offset-to-subroutine section-number)
    (subroutine-offset-and-section-number-pe-32 target parsed-pe)
    (declare (ignore section-number))
    offset-to-subroutine))

(defun pe-cpu-type (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (lookup-eq-safe :machine (lookup-eq-safe :coff-file-header parsed-pe)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp address).
(defund subroutine-address-pe-64 (subroutine-name parsed-pe)
  (declare (xargs :guard (and (stringp subroutine-name)
                              (parsed-pe-p parsed-pe))
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))
                  ))
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-address-pe-64 "No symbol table present.")
        (mv :no-symbol-table nil))
       (symbol-record (acl2::lookup-pe-symbol subroutine-name symbol-table))
       ((when (not symbol-record))
        (er hard? 'subroutine-address-pe-64 "Can't find ~x0 in symbol table." subroutine-name)
        (mv `(:cant-find-symbol ,subroutine-name) nil))
       (value (lookup-eq-safe :value symbol-record))
       ((when (not (natp value)))
        (mv :bad-value 0))
       (section-number (lookup-eq-safe :section-number symbol-record))
       ((when (not (posp section-number)))
        (mv :bad-section-number 0))
       ((mv erp section-address) (get-numbered-pe-section-rva section-number parsed-pe))
       ((when erp) (mv erp 0)))
    (mv nil (+ section-address value))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-all-symbols-from-pe-symbol-table (symbol-table acc)
  (declare (xargs :guard (and (pe-symbol-tablep symbol-table)
                              (true-listp acc))))
  (if (endp symbol-table)
      (reverse acc)
    (let ((entry (first symbol-table)))
      (get-all-symbols-from-pe-symbol-table (rest symbol-table)
                                            (cons (acl2::lookup-eq-safe :name entry)
                                                  acc)))))

(defun get-all-pe-symbols (parsed-pe)
  (declare (xargs :guard (parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable parsed-pe-p)))))
  (get-all-symbols-from-pe-symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pe64-regions-to-load-aux (sections acc)
  (declare (xargs :guard (and (acl2::pe-section-listp sections)
;                              (acl2::byte-listp all-bytes)
;                              (equal all-bytes-len (len all-bytes))
                              (true-listp acc))
                  :guard-hints (("Goal" :expand (acl2::pe-section-listp sections)
                                 :in-theory (enable acl2::pe-section-listp
                                                    acl2::pe-sectionp
                                                    acl2::pe-section-infop
                                                    acl2::pe-section-headerp)))))
  (if (endp sections)
      (mv nil (reverse acc))
    (b* ((section (first sections)) ; todo: do all section types get loaded?
         ;; (name (first section))
         (info (rest section))
         (header (lookup-eq :header info))
         (vaddr (lookup-eq :virtual-address header)) ; var names here match what we do for ELF
         (memsz (lookup-eq :virtual-size header))
         ;; (offset (lookup-eq :pointer-to-raw-data section)) ; todo: this is rel to what?
         ;; (filesz (lookup-eq :filesize section))
         (bytes (lookup-eq :raw-data info))
         (len-bytes (len bytes))
         ((when (not (and ;; (natp offset)
                       ;; (natp filesz)
                       (natp vaddr)
                       (natp memsz)
                       ;; The data length can't be larger than the memory size:
                       (<= len-bytes memsz) ;; the size of the raw data may be rounded up, but that should all be handled by the parser
                       )))
          (er hard? 'pe64-regions-to-load-aux "Bad section: vaddr=~x0, memsz=~x1, len-bytes=~x2." vaddr memsz len-bytes)
          (mv :bad-load-section nil))
         ((when (not (equal memsz len-bytes)))
          (er hard? 'pe64-regions-to-load-aux "Bad section length: memsz=~x0, bytes=~x1." memsz bytes)
          (mv :bad-load-section nil))
         ;; ttodo: do we ever need to pad with zeros?
         ;; (last-byte-num (+ -1 filesz))
         ;; ((when (not (< last-byte-num len-bytes)))
         ;;  (mv :not-enough-bytes nil))
         ;; ;; If the file size is smaller than the memory size, we fill with zeros (todo: what if there are too many?):
         ;; (numzeros (- memsz filesz))
         ;; ((when (> numzeros 10000)) ; allows padding with zeros up a multiple of 4k
         ;;  (cw "Too many zeros (~x0)!  Skipping this segment!~%" numzeros) ; ttodo!
         ;;  (pe64-regions-to-load-aux (rest sections) all-bytes-len all-bytes acc))
         ;; (bytes (take filesz (nthcdr offset all-bytes)))
         ;; ;; Zero bytes at the end of the segment may not be stored in the file:
         ;; (bytes (if (posp numzeros)
         ;;            (append bytes (acl2::repeat numzeros 0)) ; optimize?
         ;;          bytes))
         )
      (pe64-regions-to-load-aux (rest sections)
                                ;all-bytes-len all-bytes
                                (cons (list memsz vaddr bytes)
                                      acc)))))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-pe64-regions-to-load-aux
    (implies (and ;(not (mv-nth 0 (pe64-regions-to-load-aux sections acc))) ; no error
                  (acl2::pe-section-listp sections)
                  (x::memory-regionsp acc)
                  ;;(acl2::byte-listp all-bytes)
                  ;;(equal all-bytes-len (len all-bytes))
                  )
             (x::memory-regionsp (mv-nth 1 (pe64-regions-to-load-aux sections acc))))
    :hints (("Goal" :expand (acl2::pe-section-listp sections)
             :in-theory (enable pe64-regions-to-load-aux x::memory-regionsp x::memory-regionp
                                acl2::pe-sectionp
                                acl2::pe-section-infop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pe64-regions-to-load (parsed-pe)
  (declare (xargs :guard (acl2::parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-pe-p)))))
  (b* ((sections (lookup-eq :sections parsed-pe))
       ;; (all-bytes (lookup-eq :bytes parsed-pe)) ; currently, each section stores its :raw-data
       )
    (pe64-regions-to-load-aux sections nil)))

(defthm memory-regionsp-of-mv-nth-1-of-pe64-regions-to-load
  (implies (acl2::parsed-pe-p parsed-pe)
           (x::memory-regionsp (mv-nth 1 (pe64-regions-to-load parsed-pe))))
  :hints (("Goal" :in-theory (enable pe64-regions-to-load acl2::parsed-pe-p))))
