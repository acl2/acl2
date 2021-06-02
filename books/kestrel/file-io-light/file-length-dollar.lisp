; A lightweight book about the built-in function file-length$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;move
(local
 (defthm state-p1-of-read-acl2-oracle
   (implies (state-p1 state)
            (state-p1 (mv-nth 2 (read-acl2-oracle state))))
   :hints (("Goal" :in-theory (enable read-acl2-oracle)))))

(in-theory (disable file-length$
                    open-input-channel-p
                    mv-nth))

(defthm open-input-channel-p-of-file-length$
  (implies (open-input-channel-p channel typ state)
           (open-input-channel-p channel typ (mv-nth 1 (file-length$ fname state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p
                                     open-input-channel
                                     open-input-channel-p1
                                     file-length$
                                     read-acl2-oracle
                                     update-acl2-oracle))))

(defthm state-p1-of-mv-nth-1-of-file-length$
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (file-length$ filename state))))
  :hints (("Goal" :in-theory (enable file-length$))))

(defthm state-p-of-mv-nth-1-of-file-length$
  (implies (state-p state)
           (state-p (mv-nth 1 (file-length$ filename state))))
  :hints (("Goal" :in-theory (enable state-p))))
