; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

; Dummy definition for cl-directory-relative,
; which gets overwritten by the raw version.
(define cl-directory-relative ((root-dir stringp)
                               (rest-of-file-pattern stringp))
  :returns
  (matching-filenames string-listp)
  (list "dummy" "definition" (string-append root-dir rest-of-file-pattern)))

(include-book "tools/include-raw" :dir :system)
; (depends-on "cl-directory-raw.lsp")

(defttag :leo-test-files)
(include-raw "cl-directory-raw.lsp")
