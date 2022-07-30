; Rules about the built-in function read-acl2-oracle
;
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "update-acl2-oracle"))

(defthm state-p1-of-mv-nth-2-of-read-acl2-oracle
   (implies (state-p1 state)
            (state-p1 (mv-nth 2 (read-acl2-oracle state))))
   :hints (("Goal" :in-theory (enable read-acl2-oracle state-p1 open-output-channels))))

(defthm open-input-channels-of-mv-nth-2-of-read-acl2-oracle
  (equal (open-input-channels (mv-nth 2 (read-acl2-oracle state)))
         (open-input-channels state))
  :hints (("Goal" :in-theory (enable open-input-channels read-acl2-oracle update-acl2-oracle))))

(defthm w-of-mv-nth-2-of-read-acl2-oracle
  (equal (w (mv-nth 2 (read-acl2-oracle state)))
         (w state))
  :hints (("Goal" :in-theory (enable w read-acl2-oracle update-acl2-oracle))))
