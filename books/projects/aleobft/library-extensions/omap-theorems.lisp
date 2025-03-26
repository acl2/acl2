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
(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection omap-theorems
  :parents (library-extensions)
  :short "Some theorems about omaps."
  :long
  (xdoc::topstring
   (xdoc::p
    "Among other theorems,
     we introduce pick-a-point reasoning support for @(tsee omap::submap).
     This is similar to pick-a-point reasoning fo @(tsee set::subset),
     but we use a @(tsee defun-sk) and a ruleset for omaps,
     instead of the approach used for osets."))

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
    :enable omap::submap)

  (define-sk omap::submap-sk ((map1 omap::mapp) (map2 omap::mapp))
    (forall (key)
            (implies (omap::assoc key map1)
                     (equal (omap::assoc key map1)
                            (omap::assoc key map2))))
    :skolem-name omap::submap-witness

    ///

    (in-theory (disable omap::submap-sk omap::submap-sk-necc))

    (defruled omap::submap-sk-of-tail-when-submap-sk
      (implies (omap::submap-sk map1 map2)
               (omap::submap-sk (omap::tail map1) map2))
      :expand (omap::submap-sk (omap::tail map1) map2)
      :enable omap::assoc-of-tail-when-assoc-of-tail
      :use (:instance omap::submap-sk-necc
                      (key (omap::submap-witness (omap::tail map1) map2))))

    (defruled omap::submap-sk-when-submap
      (implies (omap::submap map1 map2)
               (omap::submap-sk map1 map2))
      :enable (omap::submap-sk
               omap::assoc-of-submap-is-assoc-of-supermap-when-present))

    (defruled omap::submap-when-submap-sk
      (implies (omap::submap-sk map1 map2)
               (omap::submap map1 map2))
      :induct t
      :enable (omap::submap
               omap::submap-sk-of-tail-when-submap-sk)
      :hints ('(:use (:instance omap::submap-sk-necc
                                (key (mv-nth 0 (omap::head map1)))))))

    (defruled omap::submap-to-submap-sk
      (equal (omap::submap map1 map2)
             (omap::submap-sk map1 map2))
      :use (omap::submap-sk-when-submap
            omap::submap-when-submap-sk))

    ;; Enable this ruleset to perform pick-a-point reasoning on OMAP::SUBMAP.
    ;; The arbitrary element will be (OMAP::SUBMAP-WITNESS <map1> <map2>),
    ;; where <map1> and <map2> are the omaps for which
    ;; we want to prove that (OMAP::SUBMAP <map1> <map2>) holds.
    (acl2::def-ruleset omap::submap-pick-a-point
      '(omap::submap-to-submap-sk
        omap::submap-sk)))

  (defruled submap-of-delete
    (omap::submap (omap::delete key map) map)
    :enable omap::submap-pick-a-point
    :prep-lemmas
    ((defrule lemma
       (implies (omap::assoc key1 (omap::delete key map))
                (equal (omap::assoc key1 (omap::delete key map))
                       (omap::assoc key1 map)))
       :induct t
       :enable omap::delete))))
