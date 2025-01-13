; Tools for processing the alists that represent parsed ELF files.
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-elf-file") ; overkill?  brings in get-elf-section-header.  really that book should include this one?
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
;(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
;(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)

;; todo: use the section-header-table?
(defund elf-section-presentp (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (if (assoc-equal section-name (lookup-eq :sections parsed-elf)) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund get-elf-section-bytes (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((res (lookup-equal-safe section-name (lookup-eq-safe :sections parsed-elf))))
    (if (not (byte-listp res))
        (er hard? 'get-elf-section-bytes "Non-bytes found.") ; todo: prove that this doesn't happen.  maybe redo the sections to not have their bytes stored?
      res)))

(defthm byte-listp-of-get-elf-section-bytes
  (implies (parsed-elfp parsed-elf)
           (byte-listp (get-elf-section-bytes section-name parsed-elf)))
  :hints (("Goal" :in-theory (enable get-elf-section-bytes parsed-elfp))))


;; Get the code from the .text section:
(defun get-elf-code (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (get-elf-section-bytes ".text" parsed-elf))

;; Returns the :addr field of the header with the give SECTION-NAME, or :none
(defun get-elf-section-address (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((header (get-elf-section-header section-name (lookup-eq-safe :section-header-table parsed-elf))))
    (if (eq :none header)
        :none
      (lookup-eq-safe :addr header))))

;; Returns the :addr field of the ".text" section, or :none.
(defun get-elf-code-address (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((addr (get-elf-section-address ".text" parsed-elf)))
    (if (eq :none addr)
        (er hard? 'get-elf-code-address "No .text section.") ;; todo: instead, return :none
      addr)))

;; Throws an error if the symbol has multiple matches
(defun get-elf-symbol-address-aux (name symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (elf-symbol-tablep symbol-table))
                  :guard-hints (("Goal" :in-theory (enable elf-symbol-tablep)))))
  (if (endp symbol-table)
      nil ; not found
    (let* ((entry (first symbol-table))
           (this-name (lookup-eq-safe :name entry)))
      (if (equal this-name name)
          (if (get-elf-symbol-address-aux name (rest symbol-table))
              (er hard? 'get-elf-symbol-address-aux "Multiple matches in symbol table for ~s0." name)
            (lookup-eq-safe :value entry) ; assumes it is not a relocatable file
            )
        (get-elf-symbol-address-aux name (rest symbol-table))))))

;; Throws an error if the symbol is not found or has multiple matches
(defun get-elf-symbol-address (name symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (elf-symbol-tablep symbol-table))))
  (let ((result (get-elf-symbol-address-aux name symbol-table)))
    (if (not result)
        (er hard? 'get-elf-symbol-address "Can't find ~s0 in symbol table." name)
      result)))

(defun get-names-from-elf-symbol-table (symbol-table acc)
  (declare (xargs :guard (and (elf-symbol-tablep symbol-table)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable elf-symbol-tablep)))))
  (if (endp symbol-table)
      (reverse acc)
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :name entry)))
      (get-names-from-elf-symbol-table (rest symbol-table)
                                       (if (stringp name) ; skips :no-name
                                           (cons name acc)
                                         acc)))))

(defopeners get-elf-symbol-address-aux)
(defopeners get-elf-symbol-address)

(defund parsed-elf-symbol-table (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq-safe :symbol-table parsed-elf))

;; Throws an error if not found
(defund subroutine-address-elf (name parsed-elf)
  (declare (xargs :guard (and (stringp name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elf-symbol-table
                                                           parsed-elfp)))))
  (get-elf-symbol-address name (parsed-elf-symbol-table parsed-elf)))

(defun parsed-elf-symbols (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp parsed-elf-symbol-table)))))
  (get-names-from-elf-symbol-table (parsed-elf-symbol-table parsed-elf) nil))

;; :rel or :exec or :dyn, etc.
(defun parsed-elf-type (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :type parsed-elf))

(defun parsed-elf-cpu-type (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :machine parsed-elf))

(defun parsed-elf-entry-point (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :entry parsed-elf))

;; all the bytes in the file, for looking up the bytes of the segments
(defund parsed-elf-bytes (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :bytes parsed-elf))

(defthm byte-listp-of-parsed-elf-bytes
  (implies (parsed-elfp parsed-elf)
           (byte-listp (parsed-elf-bytes parsed-elf)))
  :hints (("Goal" :in-theory (enable parsed-elf-bytes parsed-elfp))))

(defund parsed-elf-program-header-table (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :program-header-table parsed-elf))

(defthm program-header-tablep-of-parsed-elf-program-header-table
  (implies (parsed-elfp parsed-elf)
           (elf-program-header-tablep (parsed-elf-program-header-table parsed-elf)))
  :hints (("Goal" :in-theory (enable parsed-elf-program-header-table parsed-elfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parses an ELF executable.
;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable.
(defun parse-elf (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (b* (((mv existsp state) (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-elf "File ~x0 does not exist." filename)
                (mv t nil state)))
       ((mv erp bytes state) (read-file-into-byte-list filename state))
       ((when erp) (mv erp nil state))
       ((mv erp magic-number) (parse-executable-magic-number bytes filename))
       ((when erp) (mv erp nil state))
       ((when (not (= magic-number *elf-magic-number*)))
        (er hard? 'parse-elf "File ~x0 does not appear to be an ELF file." filename)
        (mv t nil state))
       ((mv erp parsed-elf)
        (parse-elf-file-bytes bytes)))
    (mv erp parsed-elf state)))

;; Returns an error triple (mv erp res state) where res contains information about the given ELF file.
(defun elf-info-fn (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable alistp-when-parsed-elfp)))))
  (b* (((mv erp parsed-elf state) (parse-elf filename state))
       ((when erp) (mv erp nil state))
       ;; (sections (lookup-eq-safe :sections parsed-elf))
       ;; (section-names (strip-cars sections))
       (info nil) ; to be extended below
       (info (acons :type (lookup-eq-safe :type parsed-elf) info))
       ;; (info (acons :section-names section-names info))
       (info (acons :section-header-table (lookup-eq-safe :section-header-table parsed-elf) info))
       (info (acons :program-header-table (lookup-eq-safe :program-header-table parsed-elf) info))
       (info (acons :symbol-table (lookup-eq-safe :symbol-table parsed-elf) info))
       ;(info (acons :sections sections info))
       ;; todo: extract more info, like section sizes
       (info (reverse info)))
    (mv nil info state)))

(defmacro elf-info (filename)
  `(elf-info-fn ,filename state))
