; Tools for processing the alists that represent parsed ELF files.
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-elf-file") ; overkill?  brings in get-elf-section-header
;(include-book "kestrel/utilities/defopeners" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
;(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)

(defun get-elf-section-bytes (section-name parsed-elf)
  (lookup-equal-safe section-name (lookup-eq-safe :sections parsed-elf)))

;; Get the code from the .text section:
(defun get-elf-code (parsed-elf)
  (get-elf-section-bytes ".text" parsed-elf))

(defun get-elf-section-address (section-name parsed-elf)
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
