; A lightweight book about the built-in function print-object$-fn
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))
(local (include-book "open-output-channel-p"))

(in-theory (disable print-object$-fn))

(local (in-theory (disable open-output-channel-p1
                           open-output-channel-p)))

(defthm open-output-channel-p1-of-print-object$-fn
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (print-object$-fn x control channel2 state)))
  :hints (("Goal" :in-theory (enable print-object$-fn
                                     ;todo:
                                     open-output-channel-p1
                                     ))))

(defthm open-output-channel-p-of-print-object$-fn
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (print-object$-fn x control channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     print-object$-fn
                                     ;todo:
                                     open-output-channel-p1
                                     open-output-channel-p))))

(defthm state-p1-of-print-object$-fn
  (implies (and (state-p1 state)
                (open-output-channel-p channel :object state))
           (state-p1 (print-object$-fn x control channel state)))
  :hints (("Goal" :in-theory (enable print-object$-fn
                                     open-output-channel-p
                                     open-output-channel-p1))))

(defthm state-p-of-print-object$-fn
  (implies (and (state-p state)
                (open-output-channel-p channel :object state))
           (state-p (print-object$-fn x control channel state)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm global-table-of-print-object$-fn
  (equal (global-table (print-object$-fn x control channel state))
         (global-table state))
  :hints (("Goal" :in-theory (enable print-object$-fn))))
