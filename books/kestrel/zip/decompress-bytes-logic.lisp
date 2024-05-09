; Logic-mode function for decompress-bytes.
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(local (include-book "kestrel/utilities/read-acl2-oracle" :dir :system))

;; This models the result of calling decompress-bytes.  We can't prove much
;; about it, just that the result is a function of the inputs.
(defstub decompress-bytes-result (byte-list format) t)

;; Decompresses the BYTE-LIST wrt the given FORMAT.  Returns a list of bytes.
;; Note that this definition gets replaced by raw Lisp code from
;; decompress-bytes-raw.lsp.
(defund decompress-bytes (byte-list format)
  (declare (xargs :guard (and (byte-listp byte-list)
                              (member-eq format '(:deflate :zlib :gzip)))))
  (prog2$ (er hard? 'decompress-bytes "Raw Lisp definition not installed?")
          (decompress-bytes-result byte-list format)))
