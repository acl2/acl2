; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We want to convert a Javascript/JSON string (of a particular format, e.g. that
; comes from cargo test output from snarkVM R1CS extraction tests) to an ACL2 string.
; However, we use the ACL2 JSON parser on it first, so \n in the first level
; of string quoting got converted to newline already.

; The only thing left to do is to remove the optional comment.

(define js-stdout-string-to-acl2-string ((js-string stringp))
  :returns (ret-string stringp :hyp :guard)
  (b* ((remove//? (str::strprefixp "//" js-string))
       ((unless remove//?)
        js-string)
       (end-of-comment (position #\newline js-string))
       ((unless (and (natp end-of-comment)
                     (< end-of-comment (length js-string))))
        ""))
    (subseq js-string end-of-comment (length js-string))))
