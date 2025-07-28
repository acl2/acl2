; Parsing an x86 executable
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-mach-o-file")
(include-book "parse-pe-file")
(include-book "parse-elf-file")
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)

;; Returns (mv erp contents) where contents in an alist representing
;; the contents of the executable (exact format depends on the type of
;; the executable).
(defund parse-executable-bytes (bytes
                               filename ; only used in error messages
                               )
  (declare (xargs :guard (and (byte-listp bytes)
                              (stringp filename))))
  (b* (((mv erp magic-number)
        (parse-executable-magic-number bytes filename))
       ((when erp) (mv erp nil)))
    (if (= magic-number *elf-magic-number*)
        (prog2$ (cw "ELF file detected.~%")
                (parse-elf-file-bytes bytes))
      (if (member magic-number (strip-cars *mach-o-magic-numbers*))
          (prog2$ (cw "Mach-O file detected.~%")
                  (parse-mach-o-file-bytes bytes))
        (let ((sig (pe-file-signature bytes)))
          (if (eql sig *pe-signature*)
              (prog2$ (cw "PE file detected.~%")
                      (parse-pe-file-bytes bytes
                                           nil ; suppress-errorsp ; todo: pass in
                                           ))
            (mv t
                (er hard? 'parse-executable-bytes "Unexpected kind of file (not PE, ELF, or Mach-O).  Magic number is ~x0. PE file signature is ~x1" magic-number sig))))))))

;; Parses a PE or Mach-O or ELF executable.
;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable (exact format depends on the type of
;; the executable).
(defun parse-executable (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (b* (((mv existsp state) (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-executable "File does not exist: ~x0." filename)
                ;;(exit 1) ;return non-zero exit status (TODO: Think about this)
                (mv t nil state)))
       ((mv erp bytes state) (read-file-into-byte-list filename state))
       ((when erp) (mv erp nil state))
       ((mv erp contents) (parse-executable-bytes bytes filename))
       ((when erp) (mv erp nil state)))
    (mv nil contents state)))

;; Returns (mv erp event state) where EVENT is a defconst representing the
;; parsed form of the executable FILENAME.
(defun defconst-x86-fn (defconst-name filename state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv erp contents state) (parse-executable filename state))
       ((when erp) (mv t nil state)))
      (mv nil `(defconst ,defconst-name ',contents) state)))

;; Define a constant containing the parsed contents of the x86 executable file FILENAME
(defmacro defconst-x86 (defconst-name filename)
  `(make-event (defconst-x86-fn ',defconst-name ',filename state)))

;; Example: (DEFCONST-X86 *sha1sum* "../examples/sha1sum/sha1sum.exe")
