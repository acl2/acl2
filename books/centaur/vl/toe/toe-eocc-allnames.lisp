; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "centaur/esim/esim-sexpr-support" :dir :system)
(include-book "toe-emodwire")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/esim-lemmas"))

(defsection pat-flatten-rev

  (defund pat-flatten-rev (pat acc)
    (declare (xargs :guard t))
    (if pat
        (if (atom pat)
            (cons pat acc)
          (pat-flatten-rev (cdr pat)
                           (pat-flatten-rev (car pat)
                                            acc)))
      acc))

  (defthm pat-flatten-rev-removal
    (equal (pat-flatten-rev pat acc)
           (revappend (pat-flatten1 pat) acc))
    :hints(("Goal" :in-theory (enable pat-flatten-rev
                                      pat-flatten1)))))


(defsection vl-eocc-allnames

  (defund vl-eocc-allnames-exec (occ acc)
    (declare (xargs :guard t))
    (b* ((acc (cons (gpl :u occ) acc))
         (acc (pat-flatten-rev (gpl :i occ) acc))
         (acc (pat-flatten-rev (gpl :o occ) acc)))
      acc))

  (defund vl-eocc-allnames (occ)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (append (list (gpl :u occ))
                 (pat-flatten1 (gpl :i occ))
                 (pat-flatten1 (gpl :o occ)))
         :exec
         (reverse (vl-eocc-allnames-exec occ nil))))

  (defthm vl-eocc-allnames-exec-removal
    (equal (vl-eocc-allnames-exec occ acc)
           (revappend (vl-eocc-allnames occ) acc))
    :hints(("Goal" :in-theory (enable vl-eocc-allnames-exec
                                      vl-eocc-allnames))))

  (verify-guards vl-eocc-allnames
    :hints(("Goal" :in-theory (enable vl-eocc-allnames-exec
                                      vl-eocc-allnames)))))


(defmapappend vl-eocclist-allnames (x)
  (vl-eocc-allnames x)
  :guard t
  :transform-true-list-p t
  :transform-exec vl-eocc-allnames-exec)




;; BOZO we might eventually want some kind of stronger well-formedness predicate,
;; e.g., to ensure that everything we're building contains only good names...


;; (defund vl-emod-allnames (mod)
;;   (declare (xargs :guard t))
;;   (b* ((main (if (gpl :x mod)
;;                  (append (alist-keys (gpl :nst mod))
;;                          (alist-keys (gpl :out mod)))
;;                (vl-eocclist-allnames (gpl :occs mod)))))
;;     (mbe :logic
;;          (append (pat-flatten1 (gpl :i mod))
;;                  (pat-flatten1 (gpl :o mod))
;;                  main)
;;          :exec
;;          (pat-flatten (gpl :i mod)
;;                       (pat-flatten (gpl :o mod)
;;                                    main)))))

;; (defund vl-emod-okp (mod)
;;   (declare (xargs :guard t))
;;   (and (good-esim-modulep mod)
;;        (vl-emodwirelist-p (vl-emod-allnames mod))))

;; (defund vl-eocc-okp (occ)
;;   (declare (xargs :guard t))
;;   (and (good-esim-occp occ)
;;        (vl-emodwirelist-p (vl-eocc-allnames occ))))

;; (defund vl-eocclist-okp (occs)
;;   (declare (xargs :guard t))
;;   (and (good-esim-occsp occs)
;;        (vl-emodwirelist-p (vl-eocclist-allnames occs))))


;; (defthm good-esim-modulep-when-vl-emod-okp
;;   (implies (vl-emod-okp mod)
;;            (good-esim-modulep mod))
;;   :hints(("Goal" :in-theory (enable vl-emod-okp))))

;; (defthm good-esim-occp-when-vl-eocc-okp
;;   (implies (vl-eocc-okp occ)
;;            (good-esim-occp occ))
;;   :hints(("Goal" :in-theory (enable vl-eocc-okp))))

;; (defthm good-esim-occsp-when-vl-eocclist-okp
;;   (implies (vl-eocclist-okp occs)
;;            (good-esim-occsp occs))
;;   :hints(("Goal" :in-theory (enable vl-eocclist-okp))))


;; (defthm vl-emodwirelist-p-of-vl-emod-allnames
;;   (implies (vl-emod-okp mod)
;;            (vl-emodwirelist-p (vl-emod-allnames mod)))
;;   :hints(("Goal" :in-theory (enable vl-emod-okp))))

;; (defthm vl-emodwirelist-p-of-vl-eocc-allnames
;;   (implies (vl-eocc-okp mod)
;;            (vl-emodwirelist-p (vl-eocc-allnames mod)))
;;   :hints(("Goal" :in-theory (enable vl-eocc-okp))))

;; (defthm vl-emodwirelist-p-of-vl-eocclist-allnames
;;   (implies (vl-eocclist-okp mod)
;;            (vl-emodwirelist-p (vl-eocclist-allnames mod)))
;;   :hints(("Goal" :in-theory (enable vl-eocclist-okp))))

