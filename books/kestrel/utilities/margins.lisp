; Utilities dealing with setting margins
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "state"))

(in-theory (disable set-fmt-hard-right-margin))
(in-theory (disable set-fmt-soft-right-margin))

(local (in-theory (disable put-global)))

(defthm boundp-global1-of-set-fmt-hard-right-margin-irrel
  (implies (not (equal name 'fmt-hard-right-margin))
           (equal (boundp-global1 name (set-fmt-hard-right-margin val state))
                  (boundp-global1 name state)))
  :hints (("Goal" :in-theory (enable set-fmt-hard-right-margin))))

(defthm boundp-global1-of-set-fmt-soft-right-margin-irrel
  (implies (not (equal name 'fmt-soft-right-margin))
           (equal (boundp-global1 name (set-fmt-soft-right-margin val state))
                  (boundp-global1 name state)))
  :hints (("Goal" :in-theory (enable set-fmt-soft-right-margin))))

(defthm state-p-of-set-fmt-hard-right-margin
  (implies (state-p state)
           (state-p (set-fmt-hard-right-margin val state)))
  :hints (("Goal" :in-theory (enable set-fmt-hard-right-margin))))

(defthm state-p-of-set-fmt-soft-right-margin
  (implies (state-p state)
           (state-p (set-fmt-soft-right-margin val state)))
  :hints (("Goal" :in-theory (enable set-fmt-soft-right-margin))))
