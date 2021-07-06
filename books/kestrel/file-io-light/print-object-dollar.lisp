; A lightweight book about the built-in function print-object$
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/io/base" :dir :system)) ;for reasoning support

(in-theory (disable print-object$))

(defthm open-output-channel-p-of-print-object$
  (implies (open-output-channel-p channel2 typ state)
           (open-output-channel-p channel2 typ (print-object$ x channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     print-object$
                                     open-output-channel-p1
                                     open-output-channels
                                     open-output-channel-p))))

(defthm open-output-channel-p1-of-print-object$-gen
  (implies (open-output-channel-p1 channel2 typ state)
           (open-output-channel-p1 channel2 typ (print-object$ object channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     print-object$
                                     open-output-channel-p1
                                     open-output-channels
                                     open-output-channel-p))))

(defthm state-p-of-print-object$
  (implies (and (state-p state)
                (symbolp channel)
                (open-output-channel-p channel :object state))
           (state-p (print-object$ x channel state)))
  :hints (("Goal" :use (:instance state-p1-of-print-object$)
           :in-theory (e/d (open-output-channel-p)
                           (state-p1-of-print-object$)))))
