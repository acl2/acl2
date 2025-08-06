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

;; TODO: Should these be in the x86isa package?

(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)

(defund get-pe-sections (parsed-pe)
  (acl2::lookup-eq-safe :sections parsed-pe))

;; Returns the section-info (an alist).
(defund get-pe-section-aux (name sections)
  (if (endp sections)
      (er hard 'get-pe-section-aux "Can't find section named ~x0." name)
    (let* ((entry (first sections))
           (this-name (car entry)))
      (if (equal this-name name)
          (cdr entry)
        (get-pe-section-aux name (rest sections))))))

;; Returns the section-info (an alist).
(defund get-pe-section (section-name parsed-pe)
  (get-pe-section-aux section-name (get-pe-sections parsed-pe)))

;; numbering starts at 1
(defund get-numbered-pe-section (section-num parsed-pe)
  (nth (+ -1 section-num) (get-pe-sections parsed-pe)))

;; Returns the section-info (an alist).
(defund get-pe-text-section (parsed-pe)
  (get-pe-section ".text" parsed-pe))

(defund get-pe-section-info-bytes (section-info)
  (acl2::lookup-eq-safe :raw-data section-info))

(defund get-pe-text-section-bytes (parsed-pe)
  (get-pe-section-info-bytes (get-pe-text-section parsed-pe)))

(defund get-pe-section-rva (section-name parsed-pe)
  (let* ((section-info (get-pe-section section-name parsed-pe))
         (header (lookup-eq-safe :header section-info))
         (section-rva (lookup-eq-safe :virtual-address header)))
    section-rva))

(defund get-numbered-pe-section-rva (section-num parsed-pe)
  (let* ((section (get-numbered-pe-section section-num parsed-pe))
         (section-info (cdr section))
         (header (lookup-eq-safe :header section-info))
         (section-rva (lookup-eq-safe :virtual-address header)))
    section-rva))

(defun lookup-pe-symbol (name symbol-table)
  (if (endp symbol-table)
      nil
    (if (equal name (acl2::lookup-eq-safe :name (first symbol-table)))
        (first symbol-table)
      (lookup-pe-symbol name (rest symbol-table)))))

(defun section-containing-rva (sections rva)
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

;; Relative to the base of the image
(defund get-pe-entry-point (parsed-pe)
  (let* ((optional-header-standard-fields (lookup-eq-safe :optional-header-standard-fields parsed-pe)))
    (lookup-eq-safe :address-of-entry-point optional-header-standard-fields)))

;; Relative to the base of the image
(defund get-pe-base-of-code (parsed-pe)
  (let* ((optional-header-standard-fields (lookup-eq-safe :optional-header-standard-fields parsed-pe)))
    (lookup-eq-safe :base-of-code optional-header-standard-fields)))

;This assumes we have a symbol table to find the address of the subroutine
(defun subroutine-address-within-text-section-pe-64 (subroutine-name
                                                     parsed-executable)
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-executable))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-address-within-text-section-pe-64 "No symbol table present."))
       (symbol-record (acl2::lookup-pe-symbol subroutine-name symbol-table))
       ((when (not symbol-record))
        (er hard? 'subroutine-address-within-text-section-pe-64 "Can't find ~x0 in symbol table." subroutine-name))
       (subroutine-address-within-text-section (acl2::lookup-eq-safe :value symbol-record)))
    subroutine-address-within-text-section))

;; Returns (mv offset-to-subroutine section-number).  Throws an error if not found
(defun subroutine-offset-and-section-number-pe-32 (target parsed-pe)
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-offset-pe-32 "No symbol table present.")
        (mv nil nil))
       (symbol-record (acl2::lookup-pe-symbol target symbol-table))
       (offset-to-subroutine (acl2::lookup-eq-safe :value symbol-record)) ;relative to the base of the section?
       (section-number (acl2::lookup-eq-safe :section-number symbol-record)))
    (mv offset-to-subroutine section-number)))

(defun subroutine-offset-pe-32 (target parsed-pe)
  (mv-let (offset-to-subroutine section-number)
    (subroutine-offset-and-section-number-pe-32 target parsed-pe)
    (declare (ignore section-number))
    offset-to-subroutine))

(defun pe-cpu-type (parsed-pe)
  (lookup-eq-safe :machine (lookup-eq-safe :coff-file-header parsed-pe)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund subroutine-address-pe-64 (subroutine-name parsed-pe)
  (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
       ((when (eq :none symbol-table))
        (er hard? 'subroutine-address-pe-64 "No symbol table present."))
       (symbol-record (acl2::lookup-pe-symbol subroutine-name symbol-table))
       ((when (not symbol-record))
        (er hard? 'subroutine-address-pe-64 "Can't find ~x0 in symbol table." subroutine-name))
       (value (lookup-eq-safe :value symbol-record))
       (section-number (lookup-eq-safe :section-number symbol-record))
       (section-address (get-numbered-pe-section-rva section-number parsed-pe)))
    (+ section-address value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-all-symbols-from-pe-symbol-table (symbol-table acc)
  (if (endp symbol-table)
      (reverse acc)
    (let ((entry (first symbol-table)))
      (get-all-symbols-from-pe-symbol-table (rest symbol-table)
                                            (cons (acl2::lookup-eq-safe :name entry)
                                                  acc)))))

(defun get-all-pe-symbols (parsed-pe)
  (get-all-symbols-from-pe-symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe) nil))

(defun pe-sectionp (section)
  (declare (xargs :guard t))
  (and (consp section)
       (let ((name (first section))
             (info (rest section)))
         (and (stringp name)
              (symbol-alistp info)
              (let ((header (lookup-eq :header info))
                    (bytes (lookup-eq :raw-data info)))
                (and (symbol-alistp header)
                     (byte-listp bytes)))))))


(defun pe-section-listp (sections)
  (declare (xargs :guard t))
  (if (not (consp sections))
      (null sections)
    (and (pe-sectionp (first sections))
         (pe-section-listp (rest sections)))))

(defun parsed-pe-p (pe)
  (declare (xargs :guard t))
  (and (symbol-alistp pe)
       (pe-section-listp (lookup-eq :sections pe))))
