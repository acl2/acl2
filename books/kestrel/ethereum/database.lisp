; Ethereum Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/defomap" :dir :system)

(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap database
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
  :key-type byte-list32
  :val-type byte-list
  :pred databasep)
