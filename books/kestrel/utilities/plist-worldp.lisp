; A lightweight book about the built-in function plist-worldp
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable plist-worldp))

(defthm plist-worldp-forward-to-alistp
  (implies (plist-worldp wrld)
           (alistp wrld))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable plist-worldp))))
