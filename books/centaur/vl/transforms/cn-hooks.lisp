; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


; These are hooks for additional transforms that we use at Centaur, but which
; have not yet been released for whatever reason.  When it comes time for us to
; run our transforms, we just defattach our implementations to these hooks.
; For non-Centaur users, these steps are just no-ops.
;
; Some of these transforms will never be released because they're gross hacks
; that are intended to address Centaur-specific things, and they wouldn't be of
; any interest outside of Centaur.  We may release the others eventually, but
; they may be in beta or tied into other libraries in a deep way that makes it
; hard to make them available at this time.

(encapsulate
  (((mp-verror-transform-hook *) => *
    :formals (x)
    :guard (vl-modulelist-p x)))

  (local (defun mp-verror-transform-hook (x) x))

  (defthm vl-modulelist-p-of-mp-verror-transform-hook
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mp-verror-transform-hook x))))

  (defthm vl-modulelist->names-of-mp-verror-transform-hook
    (equal (vl-modulelist->names (mp-verror-transform-hook x))
           (vl-modulelist->names x))))

(defattach mp-verror-transform-hook identity)



(encapsulate
  (((vl-modulelist-drop-vcovers-hook *) => *
    :formals (x)
    :guard (vl-modulelist-p x)))

  (local (defun vl-modulelist-drop-vcovers-hook (x) x))

  (defthm vl-modulelist-p-of-vl-modulelist-drop-vcovers-hook
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-drop-vcovers-hook x))))

  (defthm vl-modulelist->names-of-vl-modulelist-drop-vcovers-hook
    (equal (vl-modulelist->names (vl-modulelist-drop-vcovers-hook x))
           (vl-modulelist->names x))))

(defattach vl-modulelist-drop-vcovers-hook identity)




(encapsulate
  (((vl-modulelist-verrors-to-guarantees-hook *) => *
    :formals (x)
    :guard (vl-modulelist-p x)))

  (local (defun vl-modulelist-verrors-to-guarantees-hook (x) x))

  (defthm vl-modulelist-p-of-vl-modulelist-verrors-to-guarantees-hook
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-verrors-to-guarantees-hook x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-verrors-to-guarantees-hook
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names (vl-modulelist-verrors-to-guarantees-hook x))))))

(defattach vl-modulelist-verrors-to-guarantees-hook identity)




(encapsulate
  (((vl-modulelist-pre-toe-hook *) => *
    :formals (x)
    :guard (and (vl-modulelist-p x)
                (uniquep (vl-modulelist->names x)))))

  (local (defun vl-modulelist-pre-toe-hook (x) x))

  (defthm vl-modulelist-p-of-vl-modulelist-pre-toe-hook
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-pre-toe-hook x))))

  (defthm vl-modulelist->names-of-vl-modulelist-pre-toe-hook
    (equal (vl-modulelist->names (vl-modulelist-pre-toe-hook x))
           (vl-modulelist->names x))))

(defattach vl-modulelist-pre-toe-hook identity)



;; (encapsulate
;;   (((vl-modulelist-esim-trans-hook *) => *
;;     :formals (x)
;;     :guard (vl-modulelist-p x)))

;;   (local (defun vl-modulelist-esim-trans-hook (x) x))

;;   (defthm vl-modulelist-p-of-vl-modulelist-esim-trans-hook
;;     (implies (force (vl-modulelist-p x))
;;              (vl-modulelist-p (vl-modulelist-esim-trans-hook x))))

;;   (defthm vl-modulelist->names-of-vl-modulelist-esim-trans-hook
;;     (equal (vl-modulelist->names (vl-modulelist-esim-trans-hook x))
;;            (vl-modulelist->names x))))

;; (defattach vl-modulelist-esim-trans-hook identity)



