; Rules (theorems) relied upon by the Formal Unit Tester
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: IN-PROGRESS

(include-book "kestrel/x86/portcullis" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)
;(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
;(include-book "kestrel/x86/read-and-write" :dir :system)
;(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)

;; Recognize a NaN
(defund is-nan (val)
  (declare (xargs :guard t))
  (or (equal 'x86isa::snan val)
      (equal 'x86isa::qnan val)
      ;; a special type of qnan:
      (equal 'x86isa::indef val)))

(acl2::add-known-boolean is-nan)

;; Only needed for Axe.
(defthmd booleanp-of-is-nan
  (booleanp (is-nan val)))

;; May be brittle.  introduce nicer versions of each subexpression?
;; TODO: Have the model just use is-nan?
(defthmd is-nan-intro
  (equal (if (equal 'x86isa::snan val) t (if (equal 'x86isa::qnan val) t (equal 'x86isa::indef val)))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(theory-invariant (incompatible (:rewrite is-nan-intro) (:definition is-nan)))

(defthm if-of-equal-of-indef-and-is-nan
  (equal (if (equal 'x86isa::indef val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-qnan-and-is-nan
  (equal (if (equal 'x86isa::qnan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-snan-and-is-nan
  (equal (if (equal 'x86isa::snan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))
