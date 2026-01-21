; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "core")

(include-book "kestrel/fty/map" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection emptyp-fix
  :extension emptyp
  (fty::deffixequiv emptyp))

(defsection head-fix
  :extension head
  (fty::deffixequiv head))

(defsection tail-fix
  :extension tail
  (fty::deffixequiv tail))

(defsection update-fix
  :extension update
  (fty::deffixequiv update
    :hints (("Goal" :in-theory (enable update)))))

(defsection update*-fix
  :extension update*
  (fty::deffixequiv update*
    :hints (("Goal" :in-theory (enable update*)))))

(defsection delete-fix
  :extension delete
  (fty::deffixequiv delete
    :hints (("Goal" :in-theory (enable delete)))))

(defsection delete*-fix
  :extension delete*
  (fty::deffixequiv delete*
    :hints (("Goal" :in-theory (enable delete*)))))

(defsection assoc-fix
  :extension assoc
  (fty::deffixequiv assoc
    :hints (("Goal" :in-theory (enable assoc)))))

(defsection in*-fix
  :extension in*
  (fty::deffixequiv in*
    :hints (("Goal" :in-theory (enable in*)))))

(defsection list-in-fix
  :extension list-in
  (fty::deffixequiv list-in
    :hints (("Goal" :in-theory (enable list-in)))))

(defsection list-notin-fix
  :extension list-notin
  (fty::deffixequiv list-notin
    :hints (("Goal" :in-theory (enable list-notin)))))

(defsection lookup-fix
  :extension lookup
  (fty::deffixequiv lookup))

(defsection lookup*-fix
  :extension lookup*
  (fty::deffixequiv lookup*
    :hints (("Goal" :in-theory (enable lookup*)))))

(defsection list-lookup-fix
  :extension list-lookup
  (fty::deffixequiv list-lookup
    :hints (("Goal" :in-theory (enable list-lookup)))))

(defsection rlookup-fix
  :extension rlookup
  (fty::deffixequiv rlookup
    :hints (("Goal" :in-theory (enable rlookup)))))

(defsection rlookup*-fix
  :extension rlookup*
  (fty::deffixequiv rlookup*
    :hints (("Goal" :in-theory (enable rlookup*)))))

(defsection restrict-fix
  :extension restrict
  (fty::deffixequiv restrict
    :hints (("Goal" :in-theory (enable restrict)))))

(defsection keys-fix
  :extension keys
  (fty::deffixequiv keys
    :hints (("Goal" :in-theory (enable keys)))))

(defsection values-fix
  :extension values
  (fty::deffixequiv values
    :hints (("Goal" :in-theory (enable values)))))

(defsection compatiblep-fix
  :extension compatiblep
  (fty::deffixequiv compatiblep
    :hints (("Goal" :in-theory (enable compatiblep)))))

(defsection submap-fix
  :extension submap
  (fty::deffixequiv submap
    :hints (("Goal" :in-theory (enable submap)))))

(defsection size-fix
  :extension size
  (fty::deffixequiv size
    :hints (("Goal" :in-theory (enable size)))))

(defsection from-lists
  :extension from-lists
  (fty::deffixequiv from-lists
    :hints (("Goal" :in-theory (enable from-lists)))))
