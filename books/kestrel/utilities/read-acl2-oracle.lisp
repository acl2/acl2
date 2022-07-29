; Rules about the built-in function read-acl2-oracle
;
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm state-p1-of-mv-nth-2-of-read-acl2-oracle
   (implies (state-p1 state)
            (state-p1 (mv-nth 2 (read-acl2-oracle state))))
   :hints (("Goal" :in-theory (enable read-acl2-oracle state-p1 open-output-channels))))

;move
(local
 (defthm open-input-channels-of-update-acl2-oracle
   (equal (open-input-channels (update-acl2-oracle x st))
          (open-input-channels st))
   :hints (("Goal" :in-theory (enable open-input-channels update-acl2-oracle)))))

(defthm open-input-channels-of-mv-nth-2-of-read-acl2-oracle
  (equal (open-input-channels (mv-nth 2 (read-acl2-oracle state)))
         (open-input-channels state))
  :hints (("Goal" :in-theory (enable open-input-channels read-acl2-oracle update-acl2-oracle))))
