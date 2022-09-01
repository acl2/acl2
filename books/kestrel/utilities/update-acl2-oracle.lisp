; Rules about the built-in function update-acl2-oracle
;
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (in-theory (disable state-p1)))

(defthm open-input-channels-of-update-acl2-oracle
  (equal (open-input-channels (update-acl2-oracle x st))
         (open-input-channels st))
  :hints (("Goal" :in-theory (enable open-input-channels update-acl2-oracle))))

(defthm w-of-update-acl2-oracle
  (equal (w (update-acl2-oracle x st))
         (w st))
  :hints (("Goal" :in-theory (enable w update-acl2-oracle))))

(defthm state-p1-of-update-acl2-oracle
   (implies (state-p1 state)
            (equal (state-p1 (update-acl2-oracle x state))
                   (true-listp x)))
   :hints (("Goal" :in-theory (enable update-acl2-oracle state-p1))))

;; The rule state-p1-of-update-acl2-oracle is better
(in-theory (disable update-acl2-oracle-preserves-state-p1))
