; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "arithmetic-theorems")
(include-book "oset-theorems")
(include-book "omap-theorems")
(include-book "oset-nonemptyp")
(include-book "lists-noforkp")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ library-extensions
  :parents (aleobft)
  :short "Library extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not specific to AleoBFT,
     so they will be moved to more general libraries.
     This is a convenient place to collect them temporarily."))
  :order-subtopics (arithmetic-theorems
                    oset-theorems
                    omap-theorems
                    set::nonemptyp
                    lists-noforkp)
  :default-parent t)
