; Tools for processing the alists that represent parsed PE files.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Should these be in the x86isa package?

(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)

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
