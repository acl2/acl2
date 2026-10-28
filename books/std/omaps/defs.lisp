; Ordered Maps (Omaps) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

; This book introduces the definitions from core.lisp redundantly, without the
; theorems about them (other than the fact that mequiv is an equivalence).

(include-book "std/osets/defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "core"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (mapp
          mfix
          mequiv
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
          keys
          restrict
          values
          compatiblep
          submap
          size
          from-lists
          from-alist))

(defequiv mequiv)
