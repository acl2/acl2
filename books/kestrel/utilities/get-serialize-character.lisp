; A lightweight book about the built-in function get-serialize-character
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also get-serialize-character-ttag.lisp

(in-theory (disable get-serialize-character))

(local (in-theory (disable state-p1 open-output-channel put-global
                           open-output-channel!
                           open-output-channel-p1)))

(defthm get-serialize-character-of-put-global
  (implies (not (equal key 'serialize-character))
           (equal (get-serialize-character (put-global key value state))
                  (get-serialize-character state)))
  :hints (("Goal" :in-theory (enable get-serialize-character put-global
                                     get-global
                                     global-table
                                     update-global-table))))

(defthm get-serialize-character-of-mv-nth-1-of-open-output-channel
  (equal (get-serialize-character (mv-nth 1 (open-output-channel filename typ state)))
         (get-serialize-character state))
  :hints (("Goal" :in-theory (enable get-serialize-character open-output-channel
                                     update-open-output-channels
                                     get-global
                                     global-table
                                     update-file-clock))))
