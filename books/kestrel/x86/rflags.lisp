; Theorems about functions like cf-spec32
;
; Copyright (C) 2022 Kestrel Technology, LLC
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ; or "X"?

(include-book "projects/x86isa/machine/rflags-spec" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; The unsigned-byte-p rules here allow the size param to be 1 or greater.

;; There is no af-spec8, etc.

(defthm unsigned-byte-p-of-cf-spec8 (implies (posp n) (unsigned-byte-p n (cf-spec8 result))) :hints (("Goal" :in-theory (enable cf-spec8))))
(defthm unsigned-byte-p-of-cf-spec16 (implies (posp n) (unsigned-byte-p n (cf-spec16 result))) :hints (("Goal" :in-theory (enable cf-spec16))))
(defthm unsigned-byte-p-of-cf-spec32 (implies (posp n) (unsigned-byte-p n (cf-spec32 result))) :hints (("Goal" :in-theory (enable cf-spec32))))
(defthm unsigned-byte-p-of-cf-spec64 (implies (posp n) (unsigned-byte-p n (cf-spec64 result))) :hints (("Goal" :in-theory (enable cf-spec64))))
(defthm bitp-of-cf-spec8 (bitp (cf-spec8 x)))
(defthm bitp-of-cf-spec16 (bitp (cf-spec16 x)))
(defthm bitp-of-cf-spec32 (bitp (cf-spec32 x)))
(defthm bitp-of-cf-spec64 (bitp (cf-spec64 x)))

(defthm unsigned-byte-p-of-of-spec8 (implies (posp n) (unsigned-byte-p n (of-spec8 result))) :hints (("Goal" :in-theory (enable of-spec8))))
(defthm unsigned-byte-p-of-of-spec16 (implies (posp n) (unsigned-byte-p n (of-spec16 result))) :hints (("Goal" :in-theory (enable of-spec16))))
(defthm unsigned-byte-p-of-of-spec32 (implies (posp n) (unsigned-byte-p n (of-spec32 result))) :hints (("Goal" :in-theory (enable of-spec32))))
(defthm unsigned-byte-p-of-of-spec64 (implies (posp n) (unsigned-byte-p n (of-spec64 result))) :hints (("Goal" :in-theory (enable of-spec64))))
(defthm bitp-of-of-spec8 (bitp (of-spec8 x)))
(defthm bitp-of-of-spec16 (bitp (of-spec16 x)))
(defthm bitp-of-of-spec32 (bitp (of-spec32 x)))
(defthm bitp-of-of-spec64 (bitp (of-spec64 x)))

(defthm unsigned-byte-p-of-pf-spec8 (implies (posp n) (unsigned-byte-p n (pf-spec8 result))) :hints (("Goal" :in-theory (enable pf-spec8))))
(defthm unsigned-byte-p-of-pf-spec16 (implies (posp n) (unsigned-byte-p n (pf-spec16 result))) :hints (("Goal" :in-theory (enable pf-spec16))))
(defthm unsigned-byte-p-of-pf-spec32 (implies (posp n) (unsigned-byte-p n (pf-spec32 result))) :hints (("Goal" :in-theory (enable pf-spec32))))
(defthm unsigned-byte-p-of-sf-spec64 (implies (posp n) (unsigned-byte-p n (sf-spec64 result))) :hints (("Goal" :in-theory (enable sf-spec64))))
(defthm bitp-of-pf-spec8 (bitp (pf-spec8 x)))
(defthm bitp-of-pf-spec16 (bitp (pf-spec16 x)))
(defthm bitp-of-pf-spec32 (bitp (pf-spec32 x)))
(defthm bitp-of-pf-spec64 (bitp (pf-spec64 x)))

(defthm unsigned-byte-p-of-sf-spec8 (implies (posp n) (unsigned-byte-p n (sf-spec8 result))) :hints (("Goal" :in-theory (enable sf-spec8))))
(defthm unsigned-byte-p-of-sf-spec16 (implies (posp n) (unsigned-byte-p n (sf-spec16 result))) :hints (("Goal" :in-theory (enable sf-spec16))))
(defthm unsigned-byte-p-of-sf-spec32 (implies (posp n) (unsigned-byte-p n (sf-spec32 result))) :hints (("Goal" :in-theory (enable sf-spec32))))
(defthm unsigned-byte-p-of-pf-spec64 (implies (posp n) (unsigned-byte-p n (pf-spec64 result))) :hints (("Goal" :in-theory (enable pf-spec64))))
(defthm bitp-of-sf-spec8 (bitp (sf-spec8 x)))
(defthm bitp-of-sf-spec16 (bitp (sf-spec16 x)))
(defthm bitp-of-sf-spec32 (bitp (sf-spec32 x)))
(defthm bitp-of-sf-spec64 (bitp (sf-spec64 x)))

(defthm unsigned-byte-p-of-zf-spec (implies (posp n) (unsigned-byte-p n (zf-spec result))) :hints (("Goal" :in-theory (enable zf-spec))))
(defthm bitp-of-zf-spec (bitp (zf-spec x)))
;; Only needed for Axe
;; todo: similar rules for other flag functions?
(defthmd integerp-of-zf-spec (integerp (zf-spec result)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm unsigned-byte-p-of-add-af-spec8 (implies (posp n) (unsigned-byte-p n (add-af-spec8 dst src))) :hints (("Goal" :in-theory (enable add-af-spec8))))
(defthm unsigned-byte-p-of-add-af-spec16 (implies (posp n) (unsigned-byte-p n (add-af-spec16 dst src))) :hints (("Goal" :in-theory (enable add-af-spec16))))
(defthm unsigned-byte-p-of-add-af-spec32 (implies (posp n) (unsigned-byte-p n (add-af-spec32 dst src))) :hints (("Goal" :in-theory (enable add-af-spec32))))
(defthm unsigned-byte-p-of-add-af-spec64 (implies (posp n) (unsigned-byte-p n (add-af-spec64 dst src))) :hints (("Goal" :in-theory (enable add-af-spec64))))
;todo: more like this?
(defthm bitp-of-add-af-spec8 (bitp (add-af-spec8 dst src)))
(defthm bitp-of-add-af-spec16 (bitp (add-af-spec16 dst src)))
(defthm bitp-of-add-af-spec32 (bitp (add-af-spec32 dst src)))
(defthm bitp-of-add-af-spec64 (bitp (add-af-spec64 dst src)))

(defthm unsigned-byte-p-of-sub-af-spec8 (implies (posp n) (unsigned-byte-p n (sub-af-spec8 dst src))) :hints (("Goal" :in-theory (enable sub-af-spec8))))
(defthm unsigned-byte-p-of-sub-af-spec16 (implies (posp n) (unsigned-byte-p n (sub-af-spec16 dst src))) :hints (("Goal" :in-theory (enable sub-af-spec16))))
(defthm unsigned-byte-p-of-sub-af-spec32 (implies (posp n) (unsigned-byte-p n (sub-af-spec32 dst src))) :hints (("Goal" :in-theory (enable sub-af-spec32))))
(defthm unsigned-byte-p-of-sub-af-spec64 (implies (posp n) (unsigned-byte-p n (sub-af-spec64 dst src))) :hints (("Goal" :in-theory (enable sub-af-spec64))))

;todo: more

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
