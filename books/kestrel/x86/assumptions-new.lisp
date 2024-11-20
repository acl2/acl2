; New method of generating assumptions for x86 lifting
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "assumptions") ; todo: for lifter-targetp
(include-book "parsers/elf-tools")

;; ;; Generate all the assumptions for an ELF64 file, whether relative or
;; ;; absolute.  Returns a list of terms.
;; (defun assumption-elf64-new (target
;;                              parsed-elf
;;                              stack-slots-needed
;;                              ;text-offset
;;                              state-term)
;;   (declare (xargs :guard (and (lifter-targetp target)
;;                               (acl2::parsed-elfp parsed-elf)
;;                               (natp stack-slots-needed)
;;                               ;; state-term may be untranslated?
;;                               )))
;;   (let (


;;         (text-section-bytes (acl2::get-elf-code parsed-elf)) ;all the code, not just the given subroutine
;;         (text-section-address (acl2::get-elf-code-address parsed-elf))
;;         (subroutine-address (acl2::subroutine-address-elf subroutine-name parsed-elf)))
;;     (standard-assumptions-core-64 text-section-bytes
;;                                   text-offset
;;                                   (- subroutine-address text-section-address)
;;                                   stack-slots-needed
;;                                   x86)))
