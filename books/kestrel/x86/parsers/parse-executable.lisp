; Parsing an x86 executable
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-mach-o-file")
(include-book "parse-pe-file")
(include-book "parse-elf-file")
(include-book "kestrel/lists-light/len-at-least" :dir :system)

;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable (exact format depends on the type of
;; the executable).  todo: don't pass in state? or filename?
(defun parse-executable-bytes (bytes filename state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (stringp filename)
                  ))
  (b* (((when (not (consp bytes))) ;I've seen this be a string error message
        (prog2$ (er hard? 'parse-executable-bytes "Failed to read any bytes from file: ~x0.  Result: ~x1" filename bytes)
                (mv t nil state)))
       ((when (not (acl2::len-at-least 4 bytes)))
        (prog2$ (er hard? 'parse-executable-bytes "Not enough bytes in file: ~x0.  Result: ~x1" filename bytes)
                (mv t nil state)))
       ((mv magic-number &) (parse-u32 bytes)))
    (if (eq magic-number *elf-magic-number*)
        (prog2$ (cw "ELF file detected.~%")
                (mv t
                    (er hard? 'parse-executable-bytes "ELF files are not yet supported by this tool.")
                    state))
      (if (member magic-number (strip-cars *mach-o-magic-numbers*))
          (prog2$ (cw "Mach-O file detected.~%")
                  (mv nil ;no error
                      (parse-mach-o-file-bytes bytes)
                      state))
        (let ((sig (pe-file-signature bytes)))
          (if (eql sig *pe-signature*)
              (prog2$ (cw "PE file detected.~%")
                      (mv nil ;no error
                          (parse-pe-file-bytes bytes)
                          state))
            (mv t
                (er hard? 'parse-executable-bytes "Unexpected kind of file (not PE, ELF, or Mach-O).  Magic number is ~x0. PE file signature is ~x1" magic-number sig)
                state)))))))

;; Parse a PE or Mach-O executable (TODO: Add support for ELF).
;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable (exact format depends on the type of
;; the executable).
(defun parse-executable (filename state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (stringp filename)))
  (b* (((mv existsp state) (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-executable "File does not exist: ~x0." filename)
                ;;(exit 1) ;return non-zero exit status (TODO: Think about this)
                (mv t nil state)))
       ((mv bytes state)
        (read-file-bytes filename state)))
    (parse-executable-bytes bytes filename state)))

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
