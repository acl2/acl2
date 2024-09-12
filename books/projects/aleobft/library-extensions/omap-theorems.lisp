; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "std/omaps/core" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection omap-theorems
  :parents (library-extensions)
  :short "Some theorems about omaps."

  (defrule omap::lookup-of-update
    (equal (omap::lookup key (omap::update key1 val map))
           (if (equal key key1)
               val
             (omap::lookup key map)))
    :enable omap::lookup))
