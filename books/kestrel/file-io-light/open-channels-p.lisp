; A lightweight book about the built-in function open-channels-p
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable open-channels-p))

(defthm symbolp-when-assoc-equal-and-open-channels-p-forward
  (implies (and (open-channels-p channels)
                (assoc-equal channel channels))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable open-channels-p ordered-symbol-alistp))))
