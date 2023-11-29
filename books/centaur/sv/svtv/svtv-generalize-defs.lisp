; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "svtv-spec")
(include-book "svtv-stobj-export")
(include-book "override-common")
(local (include-book "std/alists/alist-keys" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define alistlist-keys (x)
  (if (atom x)
      nil
    (cons (alist-keys (car x))
          (alistlist-keys (cdr x)))))


(define svtv-override-triplemap-refvar-keys ((x svtv-override-triplemap-p))
  (if (atom x)
      nil
    (if (and (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (svtv-override-triple->refvar (cdar x)))
        (cons (caar x)
              (svtv-override-triplemap-refvar-keys (cdr x)))
      (svtv-override-triplemap-refvar-keys (cdr x))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemap-overridekeys-ok ((triplemap svtv-override-triplemap-p)
                                                 (namemap svtv-name-lhs-map-p)
                                                 (override-keys svarlist-p))
  ;; Checks whether all the keys of triplemap -- which are namemap keys as well
  ;; -- map in namemap to LHSes containing only vars that are in override-keys.
  :returns (ok)
  (acl2::hons-subset (svtv-name-lhs-map-vars
                      (fal-extract (svtv-override-triplemap-refvar-keys triplemap)
                                   (svtv-name-lhs-map-fix namemap)))
                     (svarlist-change-override override-keys nil)))

(define svtv-override-triplemaplist-overridekeys-ok ((triplemaps svtv-override-triplemaplist-p)
                                                     (namemap svtv-name-lhs-map-p)
                                                     (override-keys svarlist-p))
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-overridekeys-ok (car triplemaps) namemap override-keys)
         (svtv-override-triplemaplist-overridekeys-ok (cdr triplemaps) namemap override-keys))))

(local (in-theory (disable acl2::hons-subset)))

(define svtv-override-triplemaplist-refvar-keys-subsetp ((triplemaps svtv-override-triplemaplist-p)
                                                         (test-alists svex-alistlist-p))
  :prepwork ((local (defthm hons-subset1-is-subsetp-alist-keys
                      (iff (acl2::hons-subset1 x a)
                           (subsetp-equal x (alist-keys a)))
                      :hints(("Goal" :in-theory (enable acl2::hons-subset1)))))
             (local (defthm alist-keys-when-svex-alist-p
                      (implies (svex-alist-p x)
                               (equal (alist-keys x)
                                      (svex-alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys svex-alist-keys))))))
  (if (atom triplemaps)
      t
    (and (mbe :logic (subsetp-equal (svtv-override-triplemap-refvar-keys (car triplemaps))
                                    (svex-alist-keys (car test-alists)))
              :exec (b* ((test-alist (car test-alists)))
                      (with-fast-alist test-alist
                        (acl2::hons-subset1 (svtv-override-triplemap-refvar-keys (car triplemaps)) test-alist))))
         (svtv-override-triplemaplist-refvar-keys-subsetp (cdr triplemaps) (cdr test-alists)))))

(define svtv-spec-override-syntax-checks ((spec svtv-spec-p)
                                          (overridekeys svarlist-p)
                                          (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  (b* (((svtv-spec spec))
       (namemap spec.namemap)
       (in-alists spec.in-alists)
       (test-alists spec.override-test-alists)
       (val-alists spec.override-val-alists)
       (probes spec.probes)
       (outvars (svtv-probealist-outvars spec.probes))
       (my-in-alists (take (len outvars) in-alists))
       ((base-fsm spec.fsm)))
    (and (svtv-override-triplemaplist-syntax-check
          test-alists val-alists probes triplemaps)
         (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
         (no-duplicatesp-each (svex-alist-keys-list test-alists))
         (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
         (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
         (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
         (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
         (svex-alistlist-check-monotonic my-in-alists)
         (<= (len test-alists) (len outvars))
         (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
         (svarlist-override-p (Svtv-cyclephaselist-keys spec.cycle-phases) nil)
         (svex-alist-check-monotonic spec.initst-alist)
         (svarlist-override-p (svex-alist-keys spec.fsm.nextstate) nil))))
