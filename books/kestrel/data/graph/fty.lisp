; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "centaur/fty/fixtype" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")

(set-induction-depth-limit 0)

(local (include-book "edge"))
(local (include-book "graph"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffixtype edge
  :pred edgep
  :fix edge-fix
  :equiv edge-equiv
  :hints (("Goal" :in-theory (enable edge-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffixtype graph
  :pred graphp
  :fix fix
  :equiv equiv
  :hints (("Goal" :in-theory (enable equiv))))
