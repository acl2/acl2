; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/utilities/omaps/core" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omap::in-of-mfix
  (equal (omap::in key (omap::mfix map))
         (omap::in key map))
  :induct t
  :enable omap::in)

(defruled omap::in-of-update*
  (equal (omap::in key (omap::update* new old))
         (or (omap::in key new)
             (omap::in key old)))
  :induct t
  :enable omap::update*)

(defruled omap::keys-iff-not-empty
  (iff (omap::keys map)
       (not (omap::empty map)))
  :induct t
  :enable omap::keys)

(defruled omap::in-to-in-of-keys
  (iff (omap::in key map)
       (set::in key (omap::keys map)))
  :induct t
  :enable omap::in)

(defruled omap::in-keys-when-in-forward
  (implies (omap::in key map)
           (set::in key (omap::keys map)))
  :rule-classes :forward-chaining
  :induct t
  :enable omap::keys)

(defruled omap::consp-of-in-iff-in
  (iff (consp (omap::in key map))
       (omap::in key map)))
