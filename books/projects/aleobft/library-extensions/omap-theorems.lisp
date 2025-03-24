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
    :enable omap::lookup)

  (defruled omap::emptyp-of-keys-to-emptyp
    (equal (set::emptyp (omap::keys map))
           (omap::emptyp map))
    :induct t
    :enable omap::keys)

  (defruled omap::keys-of-delete
    (equal (omap::keys (omap::delete key map))
           (set::delete key (omap::keys map)))
    :induct t
    :enable (omap::delete
             set::expensive-rules))

  (defrule omap::assoc-of-delete
    (equal (omap::assoc key1 (omap::delete key map))
           (if (equal key1 key)
               nil
             (omap::assoc key1 map)))
    :induct t
    :enable omap::delete)

  (defrule omap::lookup-of-delete
    (equal (omap::lookup key1 (omap::delete key map))
           (if (equal key1 key)
               nil
             (omap::lookup key1 map)))
    :enable omap::lookup)

  (defruled omap::assoc-of-submap-is-assoc-of-supermap-when-present
    (implies (omap::submap map1 map2)
             (implies (omap::assoc key map1)
                      (equal (omap::assoc key map1)
                             (omap::assoc key map2))))
    :induct t
    :enable omap::submap))
