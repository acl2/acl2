; A variant of write-strings-to-file that can be used in make-event, etc.
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-strings-to-channel")
(local (include-book "std/io/base" :dir :system)) ;for reasoning support

(defttag file-io!)

;can be called from a make-event or clause processor because open-output-channel! is used (but requires a trust-tag)
;returns (mv erp state)
(defund write-strings-to-file! (strings filename ctx state)
  (declare (xargs :stobjs state
                  :guard (and (string-listp strings)
                              (stringp filename))))
  (mv-let (channel state)
    (open-output-channel! filename :character state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :character output." filename)
                (mv t state))
      (if (eq channel 'acl2-output-channel::standard-character-output-0) ;todo: prove that this doesn't happen
          (prog2$ (er hard? ctx "Unexpected output channel name: ~x0." channel)
                  (mv t state))
        (pprogn (write-strings-to-channel strings channel state)
                (close-output-channel channel state)
                (mv nil state))))))
