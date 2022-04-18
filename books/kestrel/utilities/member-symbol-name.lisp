; A lightweight book about the built-in function member-symbol-name
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm not-member-symbol-name-when-not-consp
  (implies (not (consp l))
           (not (member-symbol-name str l)))
  :hints (("Goal" :in-theory (enable member-symbol-name))))
