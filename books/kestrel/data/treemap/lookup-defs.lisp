; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "internal/lookup-defs")
(include-book "in-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (lookup
          lookup$inline
          head-val
          head
          lookup?
          lookup?$inline
          lookup!
          lookup!$inline
          lookup-=
          lookup-eq
          lookup-eql
          lookup?-=
          lookup?-eq
          lookup?-eql
          lookup!-=
          lookup!-eq
          lookup!-eql
          ))
