; Tools for processing the alists that represent parsed ELF files.
;
; Copyright (C) 2022-2023 Kestrel Institute
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

(defund elf-section-presentp (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (if (assoc-equal section-name (lookup-eq :sections parsed-elf)) t nil))

(defund get-elf-section-bytes (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (lookup-equal-safe section-name (lookup-eq-safe :sections parsed-elf)))

;; Get the code from the .text section:
(defun get-elf-code (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (get-elf-section-bytes ".text" parsed-elf))

(defun get-elf-section-address (section-name parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :verify-guards nil ; todo
                  ))
  (lookup-eq-safe :addr (get-elf-section-header section-name (lookup-eq-safe :section-header-table parsed-elf))))

(defun get-elf-code-address (parsed-elf)
  (get-elf-section-address ".text" parsed-elf))

(defun get-elf-symbol-address (name symbol-table)
  (if (endp symbol-table)
      (er hard? 'get-elf-symbol-address "Can't find ~s0 in symbol table." name)
    (let* ((entry (first symbol-table))
           (this-name (lookup-eq-safe :name entry)))
      (if (equal this-name name)
          (lookup-eq-safe :value entry) ; assumes it is not a relocatable file
        (get-elf-symbol-address name (rest symbol-table))))))

(defun get-names-from-elf-symbol-table (symbol-table acc)
  (if (endp symbol-table)
      (reverse acc)
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :name entry)))
      (get-names-from-elf-symbol-table (rest symbol-table)
                                       (if (stringp name) ; skips :no-name
                                           (cons name acc)
                                         acc)))))

(defopeners get-elf-symbol-address)

(defun get-elf-symbol-table (parsed-elf)
  (lookup-eq-safe :symbol-table parsed-elf))

;; Throws an error if not found
(defun subroutine-address-elf (name parsed-elf)
  (get-elf-symbol-address name (get-elf-symbol-table parsed-elf)))

(defun get-all-elf-symbols (parsed-elf)
  (get-names-from-elf-symbol-table (get-elf-symbol-table parsed-elf) nil))

(defun elf-cpu-type (parsed-elf)
  (lookup-eq-safe :machine parsed-elf))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parses an ELF executable.
;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable.
(defun parse-elf (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state
                  :verify-guards nil
                  ;:mode :program
                  ))
  (b* (((mv existsp state) (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-elf "File ~x0 does not exist." filename)
                (mv t nil state)))
       ((mv erp bytes state) (read-file-into-byte-list filename state))
       ((when erp) (mv erp nil state))
       ((mv erp magic-number) (parse-executable-magic-number bytes filename))
       ((when erp) (mv erp nil state))
       ((when (not (eq magic-number *elf-magic-number*)))
        (er hard? 'parse-elf "File ~x0 does not appear to be an ELF file." filename)
        (mv t nil state)))
    (mv nil ;no error
        (parse-elf-file-bytes bytes)
        state)))

;; Returns an error triple
(defun elf-info (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state
                  :verify-guards nil
                  ;:mode :program
                  ))
  (b* (((mv erp parsed-elf state) (parse-elf filename state))
       ((when erp) (mv erp nil state))
       (sections (lookup-eq-safe :sections parsed-elf))
       (section-names (strip-cars sections))
       (info (acons :section-names section-names nil))
       ;; todo: extract more info, like section sizes
       )
    (mv nil info state)))
