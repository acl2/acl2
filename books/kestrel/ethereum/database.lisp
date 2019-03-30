; Ethereum -- Database
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/omaps/fty" :dir :system)

(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection database
  :parents (ethereum)
  :short "Database."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [YP:D.1] and [YP:4.1],
     <see topic='@(url mmp-trees)'>MMP trees</see>
     rely on a database that associates byte arrays to hashes,
     where hashes are byte arrays of length 32 resulting from Keccak-256.
     This is called `trie database' in [YP:D.1], and just `DB' in [Wiki:MMP].
     [YP:4.1] uses the term `state database',
     but it does so in the context of the world state;
     indeed,
     the database also contains data that is not part of the world state,
     such as transactions and transaction receipts.
     In the documentation of our Ethereum model, we use the term `database'.")
   (xdoc::p
    "We introduce a <see topic='@(url acl2::fty)'>fixtype</see> for finite maps
     from <see topic='@(url byte-list32)'>byte arrays of length 32</see>
     to <see topic='@(url byte-list)'>byte arrays</see>,
     based on the fixtype of <see topic='@(url omap::omaps)'>omaps</see>."))

  (define databasep (x)
    :returns (yes/no booleanp)
    :parents (database)
    :short "Recognize databases."
    :long
    (xdoc::topstring-p
     "This definition is similar to @(tsee omap::mapp),
      but it also requires keys to be true lists of 32 bytes
      and values to be true lists of bytes.")
    (if (atom x)
        (null x)
      (and (consp (car x))
           (byte-list32p (caar x))
           (byte-listp (cdar x))
           (or (null (cdr x))
               (and (consp (cdr x))
                    (consp (cadr x))
                    (acl2::fast-<< (caar x) (caadr x))
                    (databasep (cdr x))))))
    :no-function t
    ///

    (defrule mapp-when-databasep
      (implies (databasep x)
               (omap::mapp x))
      :rule-classes (:rewrite :forward-chaining)
      :enable omap::mapp)

    (defrule databasep-of-tail
      (implies (databasep map)
               (databasep (omap::tail map)))
      :enable omap::tail)

    (defrule byte-list32p-of-head-key
      (implies (and (databasep map)
                    (not (omap::empty map)))
               (byte-list32p (mv-nth 0 (omap::head map))))
      :enable omap::head)

    (defrule byte-listp-of-head-value
      (implies (databasep map)
               (byte-listp (mv-nth 1 (omap::head map))))
      :enable omap::head)

    (defrule databasep-of-bytelist-bytelist-update
      (implies (and (databasep map)
                    (byte-list32p key)
                    (byte-listp val))
               (databasep (omap::update key val map)))
      :enable (omap::update omap::head omap::tail))

    (defrule databasep-of-update*
      (implies (and (databasep new)
                    (databasep old))
               (databasep (omap::update* new old)))
      :enable omap::update*)

    (defrule byte-listp-of-key-in-database
      (implies (and (omap::in key map) ; bind free MAP
                    (databasep map))
               (byte-list32p key))
      :enable omap::in)

    (defrule byte-list32p-of-car-of-in-when-databasep
      (implies (databasep map)
               (byte-listp (car (omap::in key map))))
      :enable omap::in)

    (defrule byte-listp-of-cdr-of-in-when-databasep
      (implies (databasep map)
               (byte-listp (cdr (omap::in key map))))
      :enable omap::in))

  (define database-fix ((x databasep))
    :returns (fixed-x databasep)
    :parents (database)
    :short "Fixing function for databases."
    (mbe :logic (if (databasep x) x nil)
         :exec x)
    :no-function t
    ///

    (defrule database-fix-when-databasep
      (implies (databasep x)
               (equal (database-fix x) x)))

    (defrule empty-of-database-fix
      (equal (omap::empty (database-fix map))
             (or (not (databasep map))
                 (omap::empty map)))
      :enable omap::empty))

  (fty::deffixtype database
    :pred databasep
    :fix database-fix
    :equiv database-equiv
    :define t
    :forward t))
