; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "oset-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "kestrel/fty/map" :dir :system))
(local (include-book "omap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: move this "defs" book to std/omaps/defs.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names #!OMAP(mapp
                mfix
                emptyp
                head
                head-key
                head-val
                tail
                update
                update*
                delete
                delete*
                assoc
                in*
                list-in
                list-notin
                lookup
                lookup*
                list-lookup
                rlookup
                rlookup*
                restrict
                keys
                values
                compatiblep
                submap
                size
                from-lists
                from-alist
                omap-induction2
                emptyp$inline
                tail$inline
                head$inline
                mequiv
                ))

(defequiv omap::mequiv
  :package :equiv)
