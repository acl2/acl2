; Ordered Maps (Omaps) -- Fixing Theorems
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "centaur/fty/top" :dir :system)

(include-book "core")

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

(defsection in-fix
  :extension in
  (fty::deffixequiv in
    :hints (("Goal" :in-theory (enable in)))))

(defsection in*-fix
  :extension in*
  (fty::deffixequiv in*
    :hints (("Goal" :in-theory (enable in*)))))

(defsection lookup-fix
  :extension lookup
  (fty::deffixequiv lookup))

(defsection lookup*-fix
  :extension lookup*
  (fty::deffixequiv lookup*
    :hints (("Goal" :in-theory (enable lookup*)))))

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
