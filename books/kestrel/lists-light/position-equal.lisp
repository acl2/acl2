; A lightweight book about the built-in-function position-equal
;
; Copyright (C) 2015-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "position-equal-ac"))

;; TODO: Clean this up

(in-theory (disable position-equal))

(defthm integerp-of-position-equal
  (implies (member-equal item lst)
           (integerp (position-equal item lst)))
  :hints (("Goal" :in-theory (enable member-equal position-equal))))

(defthm natp-of-position-equal-alt
  (implies (member-equal item lst)
           (natp (position-equal item lst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable member-equal position-equal))))

;drop?
(defthm natp-of-position-equal
  (implies (position-equal item lst)
           (natp (position-equal item lst)))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm position-equal-iff-alt
  (implies (not (stringp lst)) ;yuck
           (iff (position-equal item lst)
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable position-equal))))

;rename
(defthm position-equal-bound
  (implies (and (stringp str) ;fixme gen
                (position-equal item str))
           (< (position-equal item str)
              (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst (coerce str 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))



