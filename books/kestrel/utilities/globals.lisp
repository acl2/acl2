; A lightweight book about get-global and put-global
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable get-global put-global))

(defthm get-global-of-put-global
  (equal (get-global k1 (put-global k2 value state))
         (if (equal k1 k2)
             value
           (get-global k1 state)))
  :hints (("Goal" :in-theory (enable put-global get-global))))

(defthm w-of-put-global
  (equal (w (put-global key value state))
         (if (equal key 'current-acl2-world)
             value
           (w state))))

(defthm open-output-channel-p1-of-put-global
  (equal (open-output-channel-p1 channel typ (put-global key value state))
         (open-output-channel-p1 channel typ state))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm open-output-channel-p-of-put-global
  (equal (open-output-channel-p channel typ (put-global key value state))
         (open-output-channel-p channel typ state))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm iprint-last-index-of-put-global
  (implies (not (equal key 'iprint-ar))
           (equal (iprint-last-index (put-global key value state))
                  (iprint-last-index state)))
  :hints (("Goal" :in-theory (enable iprint-last-index))))

(defthm eviscerate-top-state-p-of-put-global
  (implies (not (member-equal key '(iprint-hard-bound iprint-fal iprint-ar)))
           (equal (eviscerate-top-state-p (put-global key value state))
                  (eviscerate-top-state-p state)))
  :hints (("Goal" :in-theory (e/d (eviscerate-top-state-p) (iprint-last-index
                                                            array1p
                                                            dimensions
                                                            header
                                                            maximum-length)))))
