; Ordered Bags (Obags) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OBAG")

(include-book "core")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection empty-fix
  :extension empty
  (fty::deffixequiv empty))

(defsection head-fix
  :extension head
  (fty::deffixequiv head))

(defsection tail-fix
  :extension tail
  (fty::deffixequiv tail))

(defsection insert-fix
  :extension insert
  (fty::deffixequiv insert
    :hints (("Goal" :in-theory (enable insert)))))

(defsection delete-fix
  :extension delete
  (fty::deffixequiv delete
    :hints (("Goal" :in-theory (enable delete)))))

(defsection in-fix
  :extension in
  (fty::deffixequiv in
    :hints (("Goal" :in-theory (enable in)))))

(defsection occs-fix
  :extension occs
  (fty::deffixequiv occs
    :hints (("Goal" :in-theory (enable occs)))))

(defsection cardinality-fix
  :extension cardinality
  (fty::deffixequiv cardinality
    :hints (("Goal" :in-theory (enable cardinality)))))

(defsection subfix
  :extension subbag
  (fty::deffixequiv subbag
    :hints (("Goal" :in-theory (enable subbag)))))

(defsection union-fix
  :extension union
  (fty::deffixequiv union
    :hints (("Goal" :in-theory (enable union)))))

(defsection intersect-fix
  :extension intersect
  (fty::deffixequiv intersect
    :hints (("Goal" :in-theory (enable intersect)))))

(defsection difference-fix
  :extension difference
  (fty::deffixequiv difference
    :hints (("Goal" :in-theory (enable difference)))))
