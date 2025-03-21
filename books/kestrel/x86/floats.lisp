; Rules (theorems) relied upon by the Formal Unit Tester
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: IN-PROGRESS

(include-book "kestrel/x86/portcullis" :dir :system)
(include-book "projects/x86isa/utils/fp-structures" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/cmp-spec" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/mxcsr" :dir :system)
(include-book "projects/x86isa/machine/state" :dir :system) ; for xr
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
;(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
;(include-book "kestrel/x86/read-and-write" :dir :system)
;(include-book "kestrel/x86/register-readers-and-writers64" :dir :system)
(include-book "projects/x86isa/machine/instructions/fp/add-mul-spec" :dir :system) ; for dazify
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for ACL2::LOGHEAD-BECOMES-BVCHOP
(local (include-book "kestrel/bv/logtail" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bitops" :dir :system))
(local (include-book "kestrel/bv/rtl" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

(in-theory (disable loghead))

(local (in-theory (e/d (ACL2::LOGTAIL-OF-BVCHOP)
                       ((:e tau-system) ; for speed
                        ))))

;; Recognize a NaN
(defund is-nan (val)
  (declare (xargs :guard t))
  (or (equal 'snan val)
      (equal 'qnan val)
      ;; a special type of qnan:
      (equal 'indef val)))

;; Only needed for Axe.
(defthmd booleanp-of-is-nan
  (booleanp (is-nan val)))

;; May be brittle.  introduce nicer versions of each subexpression?
;; TODO: Have the model just use is-nan?
(defthmd is-nan-intro
  (equal (if (equal 'snan val) t (if (equal 'qnan val) t (equal 'indef val)))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthmd is-nan-intro-from-boolif
  (equal (boolif (equal 'snan val) 't (boolif (equal 'qnan val) 't (equal 'indef val)))
         (is-nan val))
  :hints (("Goal" :in-theory (enable boolif is-nan))))

(theory-invariant (incompatible (:rewrite is-nan-intro) (:definition is-nan)))

(defthm if-of-equal-of-indef-and-is-nan
  (equal (if (equal 'indef val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-qnan-and-is-nan
  (equal (if (equal 'qnan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

(defthm if-of-equal-of-snan-and-is-nan
  (equal (if (equal 'snan val) t (is-nan val))
         (is-nan val))
  :hints (("Goal" :in-theory (enable is-nan))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable mxcsrbits-fix)))

(defthm unsigned-byte-p-of-mxcsrbits->ie (implies (posp size) (unsigned-byte-p size (mxcsrbits->ie m))))
(defthm unsigned-byte-p-of-mxcsrbits->de (implies (posp size) (unsigned-byte-p size (mxcsrbits->de m))))
(defthm unsigned-byte-p-of-mxcsrbits->ze (implies (posp size) (unsigned-byte-p size (mxcsrbits->ze m))))
(defthm unsigned-byte-p-of-mxcsrbits->oe (implies (posp size) (unsigned-byte-p size (mxcsrbits->oe m))))
(defthm unsigned-byte-p-of-mxcsrbits->ue (implies (posp size) (unsigned-byte-p size (mxcsrbits->ue m))))
(defthm unsigned-byte-p-of-mxcsrbits->pe (implies (posp size) (unsigned-byte-p size (mxcsrbits->pe m))))
(defthm unsigned-byte-p-of-mxcsrbits->daz (implies (posp size) (unsigned-byte-p size (mxcsrbits->daz m))))
(defthm unsigned-byte-p-of-mxcsrbits->im (implies (posp size) (unsigned-byte-p size (mxcsrbits->im m))))
(defthm unsigned-byte-p-of-mxcsrbits->dm (implies (posp size) (unsigned-byte-p size (mxcsrbits->dm m))))
(defthm unsigned-byte-p-of-mxcsrbits->zm (implies (posp size) (unsigned-byte-p size (mxcsrbits->zm m))))
(defthm unsigned-byte-p-of-mxcsrbits->om (implies (posp size) (unsigned-byte-p size (mxcsrbits->om m))))
(defthm unsigned-byte-p-of-mxcsrbits->um (implies (posp size) (unsigned-byte-p size (mxcsrbits->um m))))
(defthm unsigned-byte-p-of-mxcsrbits->pm (implies (posp size) (unsigned-byte-p size (mxcsrbits->pm m))))
(defthm unsigned-byte-p-of-mxcsrbits->rc (implies (and (<= 2 n) (integerp n)) (unsigned-byte-p n (mxcsrbits->rc y))) :hints (("Goal" :in-theory (enable mxcsrbits->rc))))
(defthm unsigned-byte-p-of-mxcsrbits->ftz (implies (posp size) (unsigned-byte-p size (mxcsrbits->ftz m))))
(defthm unsigned-byte-p-of-mxcsrbits->reserved (implies (and (<= 16 size) (integerp size)) (unsigned-byte-p size (mxcsrbits->reserved m))) :hints (("Goal" :in-theory (enable mxcsrbits->reserved))))

;todo: more
(defthm mxcsrbits->ie-of-loghead-32 (equal (mxcsrbits->ie (loghead 32 mxcsr)) (mxcsrbits->ie mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->ie))))
(defthm mxcsrbits->de-of-loghead-32 (equal (mxcsrbits->de (loghead 32 mxcsr)) (mxcsrbits->de mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->de))))
(defthm mxcsrbits->ze-of-loghead-32 (equal (mxcsrbits->ze (loghead 32 mxcsr)) (mxcsrbits->ze mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->ze))))
(defthm mxcsrbits->oe-of-loghead-32 (equal (mxcsrbits->oe (loghead 32 mxcsr)) (mxcsrbits->oe mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->oe))))
(defthm mxcsrbits->ue-of-loghead-32 (equal (mxcsrbits->ue (loghead 32 mxcsr)) (mxcsrbits->ue mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->ue))))
(defthm mxcsrbits->pe-of-loghead-32 (equal (mxcsrbits->pe (loghead 32 mxcsr)) (mxcsrbits->pe mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->pe))))
(defthm mxcsrbits->daz-of-loghead-32 (equal (mxcsrbits->daz (loghead 32 mxcsr)) (mxcsrbits->daz mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->daz))))
(defthm mxcsrbits->im-of-loghead-32 (equal (mxcsrbits->im (loghead 32 mxcsr)) (mxcsrbits->im mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->im))))
(defthm mxcsrbits->dm-of-loghead-32 (equal (mxcsrbits->dm (loghead 32 mxcsr)) (mxcsrbits->dm mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->dm))))
(defthm mxcsrbits->zm-of-loghead-32 (equal (mxcsrbits->zm (loghead 32 mxcsr)) (mxcsrbits->zm mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->zm))))
(defthm mxcsrbits->om-of-loghead-32 (equal (mxcsrbits->om (loghead 32 mxcsr)) (mxcsrbits->om mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->om))))
(defthm mxcsrbits->um-of-loghead-32 (equal (mxcsrbits->um (loghead 32 mxcsr)) (mxcsrbits->um mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->um))))
(defthm mxcsrbits->pm-of-loghead-32 (equal (mxcsrbits->pm (loghead 32 mxcsr)) (mxcsrbits->pm mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->pm))))
(defthm mxcsrbits->rc-of-loghead-32 (equal (mxcsrbits->rc (loghead 32 mxcsr)) (mxcsrbits->rc mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->rc))))
(defthm mxcsrbits->ftz-of-loghead-32 (equal (mxcsrbits->ftz (loghead 32 mxcsr)) (mxcsrbits->ftz mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->ftz))))
(defthm mxcsrbits->reserved-of-loghead-32 (equal (mxcsrbits->reserved (loghead 32 mxcsr)) (mxcsrbits->reserved mxcsr)) :hints (("Goal" :in-theory (enable mxcsrbits->reserved))))

(encapsulate ()
  (local (in-theory (enable mxcsrbits-fix)))
  (defthm mxcsrbits->ie-of-bvchop (implies (and (<= 1 size) (natp size)) (equal (mxcsrbits->ie (bvchop size mxcsr)) (mxcsrbits->ie mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->ie))))
  (defthm mxcsrbits->de-of-bvchop (implies (and (<= 2 size) (natp size)) (equal (mxcsrbits->de (bvchop size mxcsr)) (mxcsrbits->de mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->de))))
  (defthm mxcsrbits->ze-of-bvchop (implies (and (<= 3 size) (natp size)) (equal (mxcsrbits->ze (bvchop size mxcsr)) (mxcsrbits->ze mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->ze))))
  (defthm mxcsrbits->oe-of-bvchop (implies (and (<= 4 size) (natp size)) (equal (mxcsrbits->oe (bvchop size mxcsr)) (mxcsrbits->oe mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->oe))))
  (defthm mxcsrbits->ue-of-bvchop (implies (and (<= 5 size) (natp size)) (equal (mxcsrbits->ue (bvchop size mxcsr)) (mxcsrbits->ue mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->ue))))
  (defthm mxcsrbits->pe-of-bvchop (implies (and (<= 6 size) (natp size)) (equal (mxcsrbits->pe (bvchop size mxcsr)) (mxcsrbits->pe mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->pe))))
  (defthm mxcsrbits->daz-of-bvchop (implies (and (<= 7 size) (natp size)) (equal (mxcsrbits->daz (bvchop size mxcsr)) (mxcsrbits->daz mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->daz))))
  (defthm mxcsrbits->im-of-bvchop (implies (and (<= 8 size) (natp size)) (equal (mxcsrbits->im (bvchop size mxcsr)) (mxcsrbits->im mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->im))))
  (defthm mxcsrbits->dm-of-bvchop (implies (and (<= 9 size) (natp size)) (equal (mxcsrbits->dm (bvchop size mxcsr)) (mxcsrbits->dm mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->dm))))
  (defthm mxcsrbits->zm-of-bvchop (implies (and (<= 10 size) (natp size)) (equal (mxcsrbits->zm (bvchop size mxcsr)) (mxcsrbits->zm mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->zm))))
  (defthm mxcsrbits->om-of-bvchop (implies (and (<= 11 size) (natp size)) (equal (mxcsrbits->om (bvchop size mxcsr)) (mxcsrbits->om mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->om))))
  (defthm mxcsrbits->um-of-bvchop (implies (and (<= 12 size) (natp size)) (equal (mxcsrbits->um (bvchop size mxcsr)) (mxcsrbits->um mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->um))))
  (defthm mxcsrbits->pm-of-bvchop (implies (and (<= 13 size) (natp size)) (equal (mxcsrbits->pm (bvchop size mxcsr)) (mxcsrbits->pm mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->pm))))
  (defthm mxcsrbits->rc-of-bvchop (implies (and (<= 15 size) (natp size)) (equal (mxcsrbits->rc (bvchop size mxcsr)) (mxcsrbits->rc mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->rc))))
  (defthm mxcsrbits->ftz-of-bvchop (implies (and (<= 16 size) (natp size)) (equal (mxcsrbits->ftz (bvchop size mxcsr)) (mxcsrbits->ftz mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->ftz))))
  (defthm mxcsrbits->reserved-of-bvchop (implies (and (<= 32 size) (natp size)) (equal (mxcsrbits->reserved (bvchop size mxcsr)) (mxcsrbits->reserved mxcsr))) :hints (("Goal" :in-theory (enable mxcsrbits->reserved)))))

(encapsulate ()
  (local (in-theory (enable bvif)))
  (defthm mxcsrbits->ie-of-bvif (implies (and (<= 1 size) (natp size)) (equal (mxcsrbits->ie (bvif size test x y)) (bvif 1 test (mxcsrbits->ie x) (mxcsrbits->ie y)))))
  (defthm mxcsrbits->de-of-bvif (implies (and (<= 2 size) (natp size)) (equal (mxcsrbits->de (bvif size test x y)) (bvif 1 test (mxcsrbits->de x) (mxcsrbits->de y)))))
  (defthm mxcsrbits->ze-of-bvif (implies (and (<= 3 size) (natp size)) (equal (mxcsrbits->ze (bvif size test x y)) (bvif 1 test (mxcsrbits->ze x) (mxcsrbits->ze y)))))
  (defthm mxcsrbits->oe-of-bvif (implies (and (<= 4 size) (natp size)) (equal (mxcsrbits->oe (bvif size test x y)) (bvif 1 test (mxcsrbits->oe x) (mxcsrbits->oe y)))))
  (defthm mxcsrbits->ue-of-bvif (implies (and (<= 5 size) (natp size)) (equal (mxcsrbits->ue (bvif size test x y)) (bvif 1 test (mxcsrbits->ue x) (mxcsrbits->ue y)))))
  (defthm mxcsrbits->pe-of-bvif (implies (and (<= 6 size) (natp size)) (equal (mxcsrbits->pe (bvif size test x y)) (bvif 1 test (mxcsrbits->pe x) (mxcsrbits->pe y)))))
  (defthm mxcsrbits->daz-of-bvif (implies (and (<= 7 size) (natp size)) (equal (mxcsrbits->daz (bvif size test x y)) (bvif 1 test (mxcsrbits->daz x) (mxcsrbits->daz y)))))
  (defthm mxcsrbits->im-of-bvif (implies (and (<= 8 size) (natp size)) (equal (mxcsrbits->im (bvif size test x y)) (bvif 1 test (mxcsrbits->im x) (mxcsrbits->im y)))))
  (defthm mxcsrbits->dm-of-bvif (implies (and (<= 9 size) (natp size)) (equal (mxcsrbits->dm (bvif size test x y)) (bvif 1 test (mxcsrbits->dm x) (mxcsrbits->dm y)))))
  (defthm mxcsrbits->zm-of-bvif (implies (and (<= 10 size) (natp size)) (equal (mxcsrbits->zm (bvif size test x y)) (bvif 1 test (mxcsrbits->zm x) (mxcsrbits->zm y)))))
  (defthm mxcsrbits->om-of-bvif (implies (and (<= 11 size) (natp size)) (equal (mxcsrbits->om (bvif size test x y)) (bvif 1 test (mxcsrbits->om x) (mxcsrbits->om y)))))
  (defthm mxcsrbits->um-of-bvif (implies (and (<= 12 size) (natp size)) (equal (mxcsrbits->um (bvif size test x y)) (bvif 1 test (mxcsrbits->um x) (mxcsrbits->um y)))))
  (defthm mxcsrbits->pm-of-bvif (implies (and (<= 13 size) (natp size)) (equal (mxcsrbits->pm (bvif size test x y)) (bvif 1 test (mxcsrbits->pm x) (mxcsrbits->pm y)))))
  (defthm mxcsrbits->rc-of-bvif (implies (and (<= 15 size) (natp size)) (equal (mxcsrbits->rc (bvif size test x y)) (bvif 2 test (mxcsrbits->rc x) (mxcsrbits->rc y)))))
  (defthm mxcsrbits->ftz-of-bvif (implies (and (<= 16 size) (natp size)) (equal (mxcsrbits->ftz (bvif size test x y)) (bvif 1 test (mxcsrbits->ftz x) (mxcsrbits->ftz y)))))
  (defthm mxcsrbits->reserved-of-bvif (implies (and (<= 32 size) (natp size)) (equal (mxcsrbits->reserved (bvif size test x y)) (bvif 16 test (mxcsrbits->reserved x) (mxcsrbits->reserved y))))))

(encapsulate ()
  (local (in-theory (e/d (mxcsrbits-fix acl2::b-ior) (acl2::loghead-becomes-bvchop acl2::logbitp-to-getbit-equal-1))))
  (defthm mxcsrbits->ie-of-logior (equal (mxcsrbits->ie (logior x y)) (logior (mxcsrbits->ie x) (mxcsrbits->ie y))) :hints (("Goal" :in-theory (enable mxcsrbits->ie))))
  (defthm mxcsrbits->de-of-logior (equal (mxcsrbits->de (logior x y)) (logior (mxcsrbits->de x) (mxcsrbits->de y))) :hints (("Goal" :in-theory (enable mxcsrbits->de))))
  (defthm mxcsrbits->ze-of-logior (equal (mxcsrbits->ze (logior x y)) (logior (mxcsrbits->ze x) (mxcsrbits->ze y))) :hints (("Goal" :in-theory (enable mxcsrbits->ze))))
  (defthm mxcsrbits->oe-of-logior (equal (mxcsrbits->oe (logior x y)) (logior (mxcsrbits->oe x) (mxcsrbits->oe y))) :hints (("Goal" :in-theory (enable mxcsrbits->oe))))
  (defthm mxcsrbits->ue-of-logior (equal (mxcsrbits->ue (logior x y)) (logior (mxcsrbits->ue x) (mxcsrbits->ue y))) :hints (("Goal" :in-theory (enable mxcsrbits->ue))))
  (defthm mxcsrbits->pe-of-logior (equal (mxcsrbits->pe (logior x y)) (logior (mxcsrbits->pe x) (mxcsrbits->pe y))) :hints (("Goal" :in-theory (enable mxcsrbits->pe))))
  (defthm mxcsrbits->daz-of-logior (equal (mxcsrbits->daz (logior x y)) (logior (mxcsrbits->daz x) (mxcsrbits->daz y))) :hints (("Goal" :in-theory (enable mxcsrbits->daz))))
  (defthm mxcsrbits->im-of-logior (equal (mxcsrbits->im (logior x y)) (logior (mxcsrbits->im x) (mxcsrbits->im y))) :hints (("Goal" :in-theory (enable mxcsrbits->im))))
  (defthm mxcsrbits->dm-of-logior (equal (mxcsrbits->dm (logior x y)) (logior (mxcsrbits->dm x) (mxcsrbits->dm y))) :hints (("Goal" :in-theory (enable mxcsrbits->dm))))
  (defthm mxcsrbits->zm-of-logior (equal (mxcsrbits->zm (logior x y)) (logior (mxcsrbits->zm x) (mxcsrbits->zm y))) :hints (("Goal" :in-theory (enable mxcsrbits->zm))))
  (defthm mxcsrbits->om-of-logior (equal (mxcsrbits->om (logior x y)) (logior (mxcsrbits->om x) (mxcsrbits->om y))) :hints (("Goal" :in-theory (enable mxcsrbits->om))))
  (defthm mxcsrbits->um-of-logior (equal (mxcsrbits->um (logior x y)) (logior (mxcsrbits->um x) (mxcsrbits->um y))) :hints (("Goal" :in-theory (enable mxcsrbits->um))))
  (defthm mxcsrbits->pm-of-logior (equal (mxcsrbits->pm (logior x y)) (logior (mxcsrbits->pm x) (mxcsrbits->pm y))) :hints (("Goal" :in-theory (enable mxcsrbits->pm))))
  (defthm mxcsrbits->rc-of-logior (equal (mxcsrbits->rc (logior x y)) (logior (mxcsrbits->rc x) (mxcsrbits->rc y))) :hints (("Goal" :in-theory (enable mxcsrbits->rc))))
  (defthm mxcsrbits->ftz-of-logior (equal (mxcsrbits->ftz (logior x y)) (logior (mxcsrbits->ftz x) (mxcsrbits->ftz y))) :hints (("Goal" :in-theory (enable mxcsrbits->ftz))))
  (defthm mxcsrbits->reserved-of-logior (equal (mxcsrbits->reserved (logior x y)) (logior (mxcsrbits->reserved x) (mxcsrbits->reserved y))) :hints (("Goal" :in-theory (enable bvif mxcsrbits->reserved))))
  )

(defthm mxcsrbits->ie-of-bvor (implies (and (<= 1 size) (natp size)) (equal (mxcsrbits->ie (bvor size x y)) (bvor 1 (mxcsrbits->ie x) (mxcsrbits->ie y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->de-of-bvor (implies (and (<= 2 size) (natp size)) (equal (mxcsrbits->de (bvor size x y)) (bvor 1 (mxcsrbits->de x) (mxcsrbits->de y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->ze-of-bvor (implies (and (<= 3 size) (natp size)) (equal (mxcsrbits->ze (bvor size x y)) (bvor 1 (mxcsrbits->ze x) (mxcsrbits->ze y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->oe-of-bvor (implies (and (<= 4 size) (natp size)) (equal (mxcsrbits->oe (bvor size x y)) (bvor 1 (mxcsrbits->oe x) (mxcsrbits->oe y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->ue-of-bvor (implies (and (<= 5 size) (natp size)) (equal (mxcsrbits->ue (bvor size x y)) (bvor 1 (mxcsrbits->ue x) (mxcsrbits->ue y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->pe-of-bvor (implies (and (<= 6 size) (natp size)) (equal (mxcsrbits->pe (bvor size x y)) (bvor 1 (mxcsrbits->pe x) (mxcsrbits->pe y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->daz-of-bvor (implies (and (<= 7 size) (natp size)) (equal (mxcsrbits->daz (bvor size x y)) (bvor 1 (mxcsrbits->daz x) (mxcsrbits->daz y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->im-of-bvor (implies (and (<= 8 size) (natp size)) (equal (mxcsrbits->im (bvor size x y)) (bvor 1 (mxcsrbits->im x) (mxcsrbits->im y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->dm-of-bvor (implies (and (<= 9 size) (natp size)) (equal (mxcsrbits->dm (bvor size x y)) (bvor 1 (mxcsrbits->dm x) (mxcsrbits->dm y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->zm-of-bvor (implies (and (<= 10 size) (natp size)) (equal (mxcsrbits->zm (bvor size x y)) (bvor 1 (mxcsrbits->zm x) (mxcsrbits->zm y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->om-of-bvor (implies (and (<= 11 size) (natp size)) (equal (mxcsrbits->om (bvor size x y)) (bvor 1 (mxcsrbits->om x) (mxcsrbits->om y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->um-of-bvor (implies (and (<= 12 size) (natp size)) (equal (mxcsrbits->um (bvor size x y)) (bvor 1 (mxcsrbits->um x) (mxcsrbits->um y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->pm-of-bvor (implies (and (<= 13 size) (natp size)) (equal (mxcsrbits->pm (bvor size x y)) (bvor 1 (mxcsrbits->pm x) (mxcsrbits->pm y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->rc-of-bvor (implies (and (<= 15 size) (natp size)) (equal (mxcsrbits->rc (bvor size x y)) (bvor 2 (mxcsrbits->rc x) (mxcsrbits->rc y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->ftz-of-bvor (implies (and (<= 16 size) (natp size)) (equal (mxcsrbits->ftz (bvor size x y)) (bvor 1 (mxcsrbits->ftz x) (mxcsrbits->ftz y)))) :hints (("Goal" :in-theory (enable bvor))))
(defthm mxcsrbits->reserved-of-bvor (implies (and (<= 32 size) (natp size)) (equal (mxcsrbits->reserved (bvor size x y)) (bvor 16 (mxcsrbits->reserved x) (mxcsrbits->reserved y)))) :hints (("Goal" :in-theory (enable bvif bvor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; do we still need these?

(defthm mxcsrbits->daz-of-ifix
  (equal (mxcsrbits->daz (ifix mxcsr))
         (mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (enable mxcsrbits->daz mxcsrbits-fix))))

(defthm mxcsrbits->dm-of-ifix
  (equal (mxcsrbits->dm (ifix mxcsr))
         (mxcsrbits->dm mxcsr))
  :hints (("Goal" :in-theory (enable mxcsrbits->dm mxcsrbits-fix))))

(defthm mxcsrbits->im-of-ifix
  (equal (mxcsrbits->im (ifix mxcsr))
         (mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (enable mxcsrbits->im mxcsrbits-fix))))

(defthm mxcsrbits->ie-of-ifix
  (equal (mxcsrbits->ie (ifix mxcsr))
         (mxcsrbits->ie mxcsr))
  :hints (("Goal" :in-theory (enable mxcsrbits->ie mxcsrbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-mv-nth-0-of-sse-cmp
  (implies (and (equal (mxcsrbits->daz$inline mxcsr) 0)
                (equal (mxcsrbits->dm$inline mxcsr) 1)
                (equal (mxcsrbits->im$inline mxcsr) 1))
           (not (mv-nth 0 (sse-cmp operation op1 op2 mxcsr exp-width frac-width))))
  :hints (("Goal" :in-theory (e/d (sse-cmp
                                   sse-daz
                                   denormal-exception
                                   is-nan)
                                  (acl2::loghead-becomes-bvchop)))))

;gen?
(defthm mxcsrbits->daz-of-mv-nth-2-of-sse-cmp
  (equal (mxcsrbits->daz (mv-nth 2 (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (mxcsrbits->daz mxcsr))
  :hints (("Goal" :in-theory (e/d (sse-cmp denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

;gen?
(defthm mxcsrbits->dm-of-mv-nth-2-of-sse-cmp
  (equal (mxcsrbits->dm (mv-nth 2 (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (mxcsrbits->dm mxcsr))
    :hints (("Goal" :in-theory (e/d (sse-cmp denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

(defthm mxcsrbits->im-of-mv-nth-2-of-sse-cmp
  (equal (mxcsrbits->im (mv-nth 2 (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
         (mxcsrbits->im mxcsr))
  :hints (("Goal" :in-theory (e/d (sse-cmp denormal-exception)
                                  (acl2::loghead-becomes-bvchop)))))

(defthm integerp-of-mv-nth-2-of-sse-cmp
  (integerp (mv-nth 2 (sse-cmp operation op1 op2 mxcsr exp-width frac-width))))

(defthm fp-decode-of-bvchop-arg1
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (fp-decode (bvchop size x) exp-width frac-width)
                  (fp-decode x exp-width frac-width)))
  :hints (("Goal" :in-theory (enable fp-decode))))

(defthm sse-cmp-of-bvchop-arg2
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (sse-cmp operation (bvchop size op1) op2 mxcsr exp-width frac-width)
                  (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable sse-cmp))))

(defthm sse-cmp-of-bvchop-arg3
  (implies (and (< (+ exp-width frac-width) size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (equal (sse-cmp operation op1 (bvchop size op2) mxcsr exp-width frac-width)
                  (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable sse-cmp))))

(defthm sse-cmp-of-bvchop-arg4
  (implies (and (<= 32 size)
                (natp size))
           (equal (sse-cmp operation op1 op2 (bvchop size mxcsr) exp-width frac-width)
                  (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :hints (("Goal" :in-theory (enable sse-cmp))))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))

(defthm unsigned-byte-p-when-quotep-arg2
  (implies (and (syntaxp (quotep k))
                (natp k))
           (equal (unsigned-byte-p size k)
                  (and (natp size)
                       (<= (integer-length k) size))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-length))))

(local (in-theory (disable expt)))

;gen?
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-special
  (implies (and (< (+ exp-width frac-width) size)
                (<= 3 size)
                (posp frac-width)
                (natp exp-width)
                (natp size))
           (unsigned-byte-p size (mv-nth 1 (sse-cmp-special kind1 sign1 kind2 sign2 exp-width frac-width operation))))
  :hints (("Goal" :in-theory (e/d (sse-cmp-special) (expt)))))

;gen
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-32
  (implies (and (< (+ exp-width frac-width) 32)
                (posp frac-width)
                (natp exp-width)
                (unsigned-byte-p 32 mxcsr))
           (unsigned-byte-p 32 (mv-nth 1 (sse-cmp operation op1 op2 mxcsr exp-width frac-width))))
  :hints (("Goal" :in-theory (enable sse-cmp))))

;also prove for op8?
(defthm unsigned-byte-p-of-mv-nth-1-of-sse-cmp-of-OP-UCOMI
  (implies (and (<= 3 size)
                (natp size))
           (unsigned-byte-p size (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

(defthm mv-nth-1-of-sse-cmp-of-mv-nth-2-of-sse-cmp
  (equal (mv-nth 1 (sse-cmp operationa op1a op2a (mv-nth 2 (sse-cmp operationb op1b op2b mxcsr exp-widthb frac-widthb)) exp-widtha frac-widtha))
         (mv-nth 1 (sse-cmp operationa op1a op2a mxcsr exp-widtha frac-widtha)))
  :hints (("Goal" :in-theory (enable sse-cmp))))

;; compare op with itself
(defthm sse-cmp-of-op-ucomi-same
  (implies (and (equal (mxcsrbits->daz$inline mxcsr) 0)
                (equal (mxcsrbits->im$inline mxcsr) 1)
                (equal (mxcsrbits->dm$inline mxcsr) 1))
           (equal (mv-nth 1 (sse-cmp *op-ucomi* op op mxcsr exp-width frac-width))
                  (if (equal (mv-nth 0 (fp-decode op exp-width frac-width)) 'snan)
                      7
                    (if (equal (mv-nth 0 (fp-decode op exp-width frac-width)) 'qnan)
                        7
                      (if (equal (mv-nth 0 (fp-decode op exp-width frac-width)) 'indef)
                          7
                        4)))))
  :hints (("Goal" :in-theory (enable sse-cmp
                                     sse-cmp-special
                                     SSE-DAZ ;todo
                                     ))))

;; introduces X86ISA::SSE-CMP-BASE (rename?)
;; the mxcsr will often not be constant
(acl2::defopeners sse-cmp :hyps ((syntaxp (and (quotep x86isa::operation)
                                               (quotep x86isa::op1)
                                               (quotep x86isa::op2)
                                               (quotep x86isa::exp-width)
                                               (quotep x86isa::frac-width)))))

;; todo: move some of these:

;drop!
(include-book "kestrel/utilities/myif" :dir :system)
;drop!
(defthm boolif-of-myif-arg1-true
  (equal (boolif (myif test x1 x2) y z)
         (boolif (boolif test x1 x2) y z))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm not-denormal-exception-when-nan
  (implies (or (equal kind1 'snan)
               (equal kind1 'qnan)
               (equal kind1 'indef)
               (equal kind2 'snan)
               (equal kind2 'qnan)
               (equal kind2 'indef))
           (not (denormal-exception kind1 kind2)))
  :hints (("Goal" :in-theory (enable denormal-exception))))

;;(defstub stub (x y) t)
;; (thm
;;   (implies (and (equal (mxcsrbits->daz$inline mxcsr) 0)
;;                 (equal (mxcsrbits->im$inline mxcsr) 1)
;;                 (equal (mxcsrbits->dm$inline mxcsr) 1))
;;            (equal (EQUAL '0 (MV-NTH '1 (SSE-CMP '9 op1 op2 mxcsr '8 '23)))
;;                   (stub x y)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable SSE-CMP
;;                                      SSE-CMP-SPECIAL))))

;; essentialy, this puts in < instead of > -- todo make better named normal forms for such things

;; this puts the syntactically smaller op first
;; See also the Axe version of this rule.
(defthmd equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder
  (implies (and (syntaxp (acl2::smaller-termp op2 op1))
                (equal (mxcsrbits->daz$inline mxcsr) 0)
                (equal (mxcsrbits->im$inline mxcsr) 1)
                (equal (mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 0 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 1 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

;; this puts the syntactically smaller op first
;; See also the Axe version of this rule.
(defthmd equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder
  (implies (and (syntaxp (acl2::smaller-termp op2 op1))
                (equal (mxcsrbits->daz$inline mxcsr) 0)
                (equal (mxcsrbits->im$inline mxcsr) 1)
                (equal (mxcsrbits->dm$inline mxcsr) 1))
           (equal (equal 1 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 0 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))

;; this puts the syntactically smaller op first
;; See also the Axe version of this rule.
(defthmd equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder
  (implies (syntaxp (acl2::smaller-termp op2 op1))
           (equal (equal 7 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 7 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special))))


;dup??
(defthm sse-daz-of-nil-arg4
  (equal (SSE-DAZ kind exp frac nil)
         (mv kind exp frac))
  :hints (("Goal" :in-theory (enable SSE-DAZ))))

;strengthen?
(defthm not-equal-of-7-and-mv-nth-1-of-sse-cmp
  (implies (and (not (is-nan (mv-nth 0 (fp-decode x exp-width frac-width))))
                (not (is-nan (mv-nth 0 (fp-decode y exp-width frac-width))))
                (equal (mxcsrbits->daz$inline mxcsr) 0))
           (not (equal 7 (mv-nth 1 (sse-cmp *op-ucomi* y x mxcsr exp-width frac-width)))))
  :hints (("Goal" :in-theory (enable sse-cmp sse-cmp-special is-nan))))

(defthm sse-daz-of-nil
  (equal (SSE-DAZ kind exp frac nil)
         (mv kind exp frac))
  :hints (("Goal" :in-theory (enable SSE-DAZ))))

(defthm X86ISA::MXCSRBITS->IM-of-if
  (equal (MXCSRBITS->IM (if test x86 x86_2))
         (if test (MXCSRBITS->IM x86) (MXCSRBITS->IM x86_2))))

(defthm X86ISA::MXCSRBITS->DM-of-if
  (equal (MXCSRBITS->DM (if test x86 x86_2))
         (if test (MXCSRBITS->DM x86) (MXCSRBITS->DM x86_2))))

(defthm X86ISA::MXCSRBITS->DAZ-of-if
  (equal (MXCSRBITS->DAZ (if test x86 x86_2))
         (if test (MXCSRBITS->DAZ x86) (MXCSRBITS->DAZ x86_2))))

;todo: more like this, or look at how this is proved
(defthm MXCSRBITS->IM-of-!MXCSRBITS->IE
  (equal (MXCSRBITS->IM$INLINE (!mxcsrbits->IE$INLINE bit mxcsr))
         (MXCSRBITS->IM$INLINE mxcsr)))

(defthm MXCSRBITS->IM-of-!MXCSRBITS->DE
  (equal (MXCSRBITS->IM$INLINE (!MXCSRBITS->DE$INLINE bit mxcsr))
         (MXCSRBITS->IM$INLINE mxcsr)))

(defthm MXCSRBITS->DM-of-!MXCSRBITS->DE
  (equal (MXCSRBITS->DM$INLINE (!MXCSRBITS->DE$INLINE bit mxcsr))
         (MXCSRBITS->DM$INLINE mxcsr)))

(defthm MXCSRBITS->DM-of-!MXCSRBITS->IE
  (equal (MXCSRBITS->DM$INLINE (!MXCSRBITS->IE$INLINE bit mxcsr))
         (MXCSRBITS->DM$INLINE mxcsr)))

(defthm MXCSRBITS->DAZ-of-!MXCSRBITS->IE
  (equal (MXCSRBITS->DAZ$INLINE (!MXCSRBITS->IE$INLINE bit mxcsr))
         (MXCSRBITS->DAZ$INLINE mxcsr)))

(defthm MXCSRBITS->DAZ-of-!MXCSRBITS->DE
  (equal (MXCSRBITS->DAZ$INLINE (!MXCSRBITS->DE$INLINE bit mxcsr))
         (MXCSRBITS->DAZ$INLINE mxcsr)))

(defthm integerp-of-!MXCSRBITS->IE
  (integerp (!MXCSRBITS->IE$INLINE bit mxcsr)))

(defthm unsigned-byte-p-32-of-!MXCSRBITS->IE
  (unsigned-byte-p 32 (!MXCSRBITS->IE$INLINE bit mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::unsigned-byte-p-when-mxcsrbits-p))))

(defthm unsigned-byte-p-32-of-!MXCSRBITS->DE
  (unsigned-byte-p 32 (!MXCSRBITS->DE$INLINE bit mxcsr))
  :hints (("Goal" :in-theory (enable x86isa::unsigned-byte-p-when-mxcsrbits-p))))

(defthm integerp-of-!MXCSRBITS->DE
  (integerp (!MXCSRBITS->DE$INLINE bit mxcsr)))

(def-constant-opener fp-decode)
(def-constant-opener fp-to-rat)
(def-constant-opener rtl::bias)
(def-constant-opener rtl::expw)
(def-constant-opener snanp)
(def-constant-opener qnanp)
(def-constant-opener infp)
(def-constant-opener nanp)
(def-constant-opener bitn)
(def-constant-opener prec)
(def-constant-opener encodingp)
(def-constant-opener expf)
(def-constant-opener sgnf)
(def-constant-opener manf)
(def-constant-opener unsupp)
(def-constant-opener explicitp)
(def-constant-opener sigw)
(def-constant-opener formatp)
(def-constant-opener bits)
(def-constant-opener bvecp)
(def-constant-opener denormp)
(def-constant-opener sigf)
(def-constant-opener fl)
(def-constant-opener mxcsr-masks)
(def-constant-opener rtl::set-flag)
(def-constant-opener mxcsr-rc)
(def-constant-opener decode)
(def-constant-opener ddecode)
(def-constant-opener zencode)
(def-constant-opener binary-cat)

;rename
(defthm <-of-fp-to-rat
  (implies (and (natp frac)
                (natp exp)
                (not (equal 0 exp))
                (natp frac-width)
                (equal 8 exp-width) ; todo: gen
                )
           (equal (< (fp-to-rat sign exp frac bias exp-width frac-width) 0)
                  (and (not (equal 0 sign))
                       (if (equal 0 exp)
                           (not (equal 0 frac))
                         (<= exp (x86isa::fp-max-finite-exp exp-width))))))
  :hints (("Goal" :in-theory (enable fp-to-rat))))

(defthm integerp-of-xr-mxcsr
  (integerp (xr :mxcsr nil x86)))

(defthm dazify-of-0-arg2
  (equal (rtl::dazify x 0 f)
         x)
  :hints (("Goal" :in-theory (enable rtl::dazify))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: better place for this stuff?  it's not necessarily for floats

(defthm cr0bits->ts-of-bvchop
  (implies (and (< 3 n)
                (integerp n))
           (equal (x86isa::cr0bits->ts (bvchop n x))
                  (x86isa::cr0bits->ts x)))
  :hints (("Goal" :in-theory (enable x86isa::cr0bits->ts
                                     x86isa::cr0bits-fix))))

(defthm cr0bits->em-of-bvchop
  (implies (and (< 2 n)
                (integerp n))
           (equal (x86isa::cr0bits->em (bvchop n x))
                  (x86isa::cr0bits->em x)))
  :hints (("Goal" :in-theory (enable x86isa::cr0bits->em
                                     x86isa::cr0bits-fix))))

(defthm cr4bits->OSFXSR-of-bvchop
  (implies (and (< 9 n)
                (integerp n))
           (equal (x86isa::cr4bits->OSFXSR (bvchop n x))
                  (x86isa::cr4bits->OSFXSR x)))
  :hints (("Goal" :in-theory (enable x86isa::cr4bits->OSFXSR
                                     x86isa::cr4bits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd integerp-of-zencode
  (integerp (rtl::zencode sgn f)))

(defthmd integerp-of-iencode
  (integerp (rtl::iencode sgn f)))

(defthmd integerp-of-dencode
  (integerp (rtl::dencode x f)))

(defthmd integerp-of-nencode
  (integerp (rtl::nencode x f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd acl2-numberp-of-ddecode
  (acl2-numberp (rtl::ddecode x f)))

(defthmd acl2-numberp-of-ndecode
  (acl2-numberp (rtl::ndecode x f)))

(defthmd acl2-numberp-of-decode
  (acl2-numberp (rtl::decode x f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm unmasked-excp-p-of-63-arg2
  (equal (rtl::unmasked-excp-p flags 63)
         nil)
  :hints (("Goal" :in-theory (enable rtl::unmasked-excp-p
                                     rtl::zbit
                                     rtl::obit
                                     rtl::pbit
                                     rtl::ubit))))

(defthm unmasked-excp-p-of-0-arg1
  (equal (rtl::unmasked-excp-p 0 masks)
         nil)
  :hints (("Goal" :in-theory (enable rtl::unmasked-excp-p
                                     rtl::zbit
                                     rtl::obit
                                     rtl::pbit
                                     rtl::ubit
                                     ))))

;; since MXCSR-RC breaks the abstraction and accesses bits of the mxcsr directly
(defthm mxcsr-rc-redef
  (implies (integerp mxcsr) ;drop?
           (equal (rtl::mxcsr-rc mxcsr)
                  (case (mxcsrbits->rc mxcsr)
                   (0 'rtl::rne)
                   (1 'rtl::rdn)
                   (2 'rtl::rup)
                   (3 'rtl::rtz))))
  :hints (("Goal" :in-theory (enable rtl::mxcsr-rc
                                     ;acl2::bits-becomes-slice
                                     mxcsrbits->rc
                                     mxcsrbits-fix))))

;; since RTL::MXCSR-MASKS breaks the abstraction and accesses bits of the mxcsr directly
(defthm mxcsr-masks-redef
  (implies (integerp mxcsr)
           (equal (rtl::mxcsr-masks mxcsr)
                  (acl2::bvcat2 1 (mxcsrbits->pm mxcsr)
                                1 (mxcsrbits->um mxcsr)
                                1 (mxcsrbits->om mxcsr)
                                1 (mxcsrbits->zm mxcsr)
                                1 (mxcsrbits->dm mxcsr)
                                1 (mxcsrbits->im mxcsr))))
  :hints (("Goal" :in-theory (enable rtl::mxcsr-masks
                                     acl2::bits-becomes-slice
                                     mxcsrbits->im
                                     mxcsrbits->dm
                                     mxcsrbits->zm
                                     mxcsrbits->om
                                     mxcsrbits->um
                                     mxcsrbits->pm
                                     mxcsrbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we've already turned the bitn into getbit
(defthm getbit-of-daz-becomes-mxcsrbits->daz (equal (getbit (rtl::daz) mxcsr) (mxcsrbits->daz mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->daz rtl::daz))))
;; (defthm getbit-of-ie-becomes-mxcsrbits->-ie (equal (getbit (rtl::ie) mxcsr) (mxcsrbits->ie mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->ie rtl::ie))))
;; (defthm getbit-of-de-becomes-mxcsrbits->-de (equal (getbit (rtl::de) mxcsr) (mxcsrbits->de mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->de rtl::de))))
;; (defthm getbit-of-ze-becomes-mxcsrbits->-ze (equal (getbit (rtl::ze) mxcsr) (mxcsrbits->ze mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->ze rtl::ze))))
;; (defthm getbit-of-oe-becomes-mxcsrbits->-oe (equal (getbit (rtl::oe) mxcsr) (mxcsrbits->oe mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->oe rtl::oe))))
;; (defthm getbit-of-ue-becomes-mxcsrbits->-ue (equal (getbit (rtl::ue) mxcsr) (mxcsrbits->ue mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->ue rtl::ue))))
;; (defthm getbit-of-pe-becomes-mxcsrbits->-pe (equal (getbit (rtl::pe) mxcsr) (mxcsrbits->pe mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->pe rtl::pe))))
;; (defthm getbit-of-da-becomes-mxcsrbits->-da (equal (getbit (rtl::da) mxcsr) (mxcsrbits->da mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->da rtl::da))))
;; (defthm getbit-of-im-becomes-mxcsrbits->-im (equal (getbit (rtl::im) mxcsr) (mxcsrbits->im mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->im rtl::im))))
;; (defthm getbit-of-dm-becomes-mxcsrbits->-dm (equal (getbit (rtl::dm) mxcsr) (mxcsrbits->dm mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->dm rtl::dm))))
;; (defthm getbit-of-zm-becomes-mxcsrbits->-zm (equal (getbit (rtl::zm) mxcsr) (mxcsrbits->zm mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->zm rtl::zm))))
(defthm getbit-of-omsk-becomes-mxcsrbits->-om (equal (getbit (rtl::omsk) mxcsr) (mxcsrbits->om mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->om rtl::omsk mxcsrbits-fix))))
(defthm getbit-of-umsk-becomes-mxcsrbits->-um (equal (getbit (rtl::umsk) mxcsr) (mxcsrbits->um mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->um rtl::umsk mxcsrbits-fix))))
;; (defthm getbit-of-pm-becomes-mxcsrbits->-pm (equal (getbit (rtl::pm) mxcsr) (mxcsrbits->pm mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->pm rtl::pm))))

;; (rc 2bits)        ;; Rounding Control
(defthm getbit-of-ftz-becomes-mxcsrbits->-ftz (equal (getbit (rtl::ftz) mxcsr) (mxcsrbits->ftz mxcsr)) :hints (("Goal" :in-theory (enable x86isa::mxcsrbits->ftz rtl::ftz mxcsrbits-fix))))

(defthm natp-of-daz (natp (rtl::daz)))
(defthm natp-of-omsk (natp (rtl::omsk)))
(defthm natp-of-umsk (natp (rtl::umsk)))
(defthm natp-of-ftz (natp (rtl::ftz)))

;; helps when a bvif gets tightened
;more like this?
(defthm mxcsrbits->daz-when-unsigned-byte-p-too-small
  (implies (unsigned-byte-p 6 mxcsr)
           (equal (mxcsrbits->daz$inline mxcsr)
                  0))
  :hints (("Goal" :in-theory (enable mxcsrbits->daz))))


;daz remains 0
(defthm mxcsrbits->daz-of-mv-nth-1-of-sse-post-comp
  (implies (equal 0 (mxcsrbits->daz mxcsr))
           (equal (mxcsrbits->daz (mv-nth '1 (rtl::sse-post-comp u mxcsr f)))
                  0))
  :hints (("Goal" :in-theory (enable rtl::sse-post-comp rtl::obit rtl::pbit rtl::ubit ))))

;daz remains 0
(defthm mxcsrbits->daz-of-mv-nth-1-of-sse-binary-comp
  (implies (equal 0 (mxcsrbits->daz mxcsr))
           (equal (mxcsrbits->daz (mv-nth '1 (rtl::sse-binary-comp op a b mxcsr f)))
                  0))
  :hints (("Goal" :in-theory (enable rtl::sse-binary-comp
;                                     rtl::sse-post-comp ; todo
                                     rtl::obit rtl::pbit rtl::ubit ))))

(defthm integerp-of-qnanize
  (integerp (rtl::qnanize x f)))
