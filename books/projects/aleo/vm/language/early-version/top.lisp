; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM-EARLY")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ early-version
  :parents (aleovm::language)
  :short "An early version of the AleoVM language."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be updated to the latest version."))
  :order-subtopics (concrete-syntax
                    abstract-syntax))
