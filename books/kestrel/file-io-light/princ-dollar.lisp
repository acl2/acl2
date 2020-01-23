; A lightweight book about the built-in function princ$.
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/io/base" :dir :system)) ;for reasoning support

(in-theory (disable princ$))

(defthm open-output-channel-p-of-princ$
  (implies (and (open-output-channel-p channel :character state)
                (symbolp channel)
                (state-p state))
           (open-output-channel-p channel :character (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     princ$
                                     open-output-channel-p1
                                     open-output-channels
                                     open-output-channel-p))))

(defthm state-p-of-princ$
  (implies (and (state-p state)
                (symbolp channel)
                (open-output-channel-p channel :character state))
           (state-p (princ$ x channel state)))
  :hints (("Goal" :use (:instance state-p1-of-princ$)
           :in-theory (e/d (open-output-channel-p)
                           (state-p1-of-princ$)))))
