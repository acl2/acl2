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
(include-book "../mlib/writer")
(include-book "../mlib/expr-tools")
(local (include-book "../util/arithmetic"))


(defsection vl-atom-fix

  (local (in-theory (enable vl-atom-p
                            vl-atom
                            vl-atom->finalwidth
                            vl-atom->finaltype
                            vl-atom->guts)))

  (defund vl-atom-fix (x)
    (declare (xargs :guard (vl-atom-p x)))
    (mbe :logic (change-vl-atom x
                                :finalwidth nil
                                :finaltype nil)
         :exec (if (or (vl-atom->finalwidth x)
                       (vl-atom->finaltype x))
                   (change-vl-atom x
                                   :finalwidth nil
                                   :finaltype nil)
                 x)))

  (local (in-theory (enable vl-atom-fix)))

  (defthm vl-atom-p-of-vl-atom-fix
    (implies (force (vl-atom-p x))
             (vl-atom-p (vl-atom-fix x)))))



(defsection vl-expr-fix

;; BOZO consider optimizing to avoid reconsing already-fixed expressions

  (mutual-recursion
   (defund vl-expr-fix (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (vl-atom-fix x)
       (change-vl-nonatom x
                          :args (vl-exprlist-fix (vl-nonatom->args x))
                          :atts nil
                          :finalwidth nil
                          :finaltype nil)))
   (defund vl-exprlist-fix (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-expr-fix (car x))
             (vl-exprlist-fix (cdr x))))))

  (flag::make-flag flag-vl-expr-fix
                   vl-expr-fix
                   :flag-mapping ((vl-expr-fix . expr)
                                  (vl-exprlist-fix . list)))

  (defthm len-of-vl-exprlist-fix
    (equal (len (vl-exprlist-fix x))
           (len x))
    :hints(("Goal"
            :induct (len x)
            :expand (vl-exprlist-fix x))))

  (defthm-flag-vl-expr-fix lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (vl-expr-fix x)))
          :name vl-expr-p-of-vl-expr-fix)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-fix x)))
          :name vl-exprlist-p-of-vl-exprlist-fix)
    :hints(("Goal"
            :induct (flag-vl-expr-fix flag x)
            :expand ((vl-expr-fix x)
                     (vl-exprlist-fix x))))))



(defsection vl-range-fix

  (defund vl-range-fix (x)
    (declare (xargs :guard (vl-range-p x)))
    (b* (((vl-range x) x))
      (change-vl-range x
                       :left (vl-expr-fix x.left)
                       :right (vl-expr-fix x.right))))

  (local (in-theory (enable vl-range-fix)))

  (defthm vl-range-p-of-vl-range-fix
    (implies (force (vl-range-p x))
             (vl-range-p (vl-range-fix x)))))


(defsection vl-maybe-range-fix

  (defund vl-maybe-range-fix (x)
    (declare (xargs :guard (vl-maybe-range-p x)))
    (if x
        (vl-range-fix x)
      x))

  (local (in-theory (enable vl-maybe-range-fix)))

  (defthm vl-maybe-range-p-of-vl-maybe-range-fix
    (implies (force (vl-maybe-range-p x))
             (vl-maybe-range-p (vl-maybe-range-fix x)))))


(defsection vl-rangelist-fix

  (defprojection vl-rangelist-fix (x)
    (vl-range-fix x)
    :guard (vl-rangelist-p x))

  (local (in-theory (enable vl-rangelist-fix)))

  (defthm vl-rangelist-p-of-vl-rangelist-fix
    (implies (force (vl-rangelist-p x))
             (vl-rangelist-p (vl-rangelist-fix x)))))



(defsection vl-assign-fix

  (defund vl-assign-fix (x)
    (declare (xargs :guard (vl-assign-p x)))
    (b* (((vl-assign x) x))
      (change-vl-assign x
                        :lvalue   (vl-expr-fix x.lvalue)
                        :expr     (vl-expr-fix x.expr)
                        :delay    nil
                        :strength nil
                        :loc      *vl-fakeloc*
                        :atts     nil)))

  (local (in-theory (enable vl-assign-fix)))

  (defthm vl-assign-p-of-vl-assign-fix
    (implies (force (vl-assign-p x))
             (vl-assign-p (vl-assign-fix x)))))


(defsection vl-assignlist-fix

  (defprojection vl-assignlist-fix (x)
    (vl-assign-fix x)
    :guard (vl-assignlist-p x))

  (local (in-theory (enable vl-assignlist-fix)))

  (defthm vl-assignlist-p-of-vl-assignlist-fix
    (implies (force (vl-assignlist-p x))
             (vl-assignlist-p (vl-assignlist-fix x)))))


(defsection vl-plainarg-fix

  (defund vl-plainarg-fix (x)
    (declare (xargs :guard (vl-plainarg-p x)))
    (b* (((vl-plainarg x) x))
      (change-vl-plainarg x
                          :expr (if x.expr
                                    (vl-expr-fix x.expr)
                                  nil)
                          :atts     nil
                          :portname nil
                          :dir      nil)))

  (local (in-theory (enable vl-plainarg-fix)))

  (defthm vl-plainarg-p-of-vl-plainarg-fix
    (implies (force (vl-plainarg-p x))
             (vl-plainarg-p (vl-plainarg-fix x)))))

(defsection vl-plainarglist-fix

  (defprojection vl-plainarglist-fix (x)
    (vl-plainarg-fix x)
    :guard (vl-plainarglist-p x))

  (local (in-theory (enable vl-plainarglist-fix)))

  (defthm vl-plainarglist-p-of-vl-plainarglist-fix
    (implies (force (vl-plainarglist-p x))
             (vl-plainarglist-p (vl-plainarglist-fix x)))))


(defsection vl-namedarg-fix

  (defund vl-namedarg-fix (x)
    (declare (xargs :guard (vl-namedarg-p x)))
    (b* (((vl-namedarg x) x))
      (change-vl-namedarg x
                          :expr (if x.expr
                                    (vl-expr-fix x.expr)
                                  nil)
                          :atts     nil)))

  (local (in-theory (enable vl-namedarg-fix)))

  (defthm vl-namedarg-p-of-vl-namedarg-fix
    (implies (force (vl-namedarg-p x))
             (vl-namedarg-p (vl-namedarg-fix x)))))

(defsection vl-namedarglist-fix

  (defprojection vl-namedarglist-fix (x)
    (vl-namedarg-fix x)
    :guard (vl-namedarglist-p x))

  (local (in-theory (enable vl-namedarglist-fix)))

  (defthm vl-namedarglist-p-of-vl-namedarglist-fix
    (implies (force (vl-namedarglist-p x))
             (vl-namedarglist-p (vl-namedarglist-fix x)))))


(defsection vl-arguments-fix

  (defund vl-arguments-fix (x)
    (declare (xargs :guard (vl-arguments-p x)))
    (b* ((namedp (vl-arguments->namedp x))
         (args   (vl-arguments->args x))
         (args-fix (if namedp
                       (vl-namedarglist-fix args)
                     (vl-plainarglist-fix args))))
      (vl-arguments namedp args-fix)))

  (local (in-theory (enable vl-arguments-fix)))

  (defthm vl-arguments-p-of-vl-arguments-fix
    (implies (force (vl-arguments-p x))
             (vl-arguments-p (vl-arguments-fix x)))))


(defsection vl-modinst-fix

  (defund vl-modinst-fix (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* (((vl-modinst x) x))
      (change-vl-modinst x
                         :range     (vl-maybe-range-fix x.range)
                         :paramargs (vl-arguments-fix x.paramargs)
                         :portargs  (vl-arguments-fix x.portargs)
                         :str nil
                         :delay nil
                         :atts nil
                         :loc *vl-fakeloc*)))

  (local (in-theory (enable vl-modinst-fix)))

  (defthm vl-modinst-p-of-vl-modinst-fix
    (implies (force (vl-modinst-p x))
             (vl-modinst-p (vl-modinst-fix x)))))


(defsection vl-modinstlist-fix

  (defprojection vl-modinstlist-fix (x)
    (vl-modinst-fix x)
    :guard (vl-modinstlist-p x))

  (local (in-theory (enable vl-modinstlist-fix)))

  (defthm vl-modinstlist-p-of-vl-modinstlist-fix
    (implies (force (vl-modinstlist-p x))
             (vl-modinstlist-p (vl-modinstlist-fix x)))))


(defsection vl-gateinst-fix

  (defund vl-gateinst-fix (x)
    (declare (xargs :guard (vl-gateinst-p x)))
    (b* (((vl-gateinst x) x))
      (change-vl-gateinst x
                         :range     (vl-maybe-range-fix x.range)
                         :strength  nil
                         :delay     nil
                         :args      (vl-plainarglist-fix x.args)
                         :atts      nil
                         :loc       *vl-fakeloc*)))

  (local (in-theory (enable vl-gateinst-fix)))

  (defthm vl-gateinst-p-of-vl-gateinst-fix
    (implies (force (vl-gateinst-p x))
             (vl-gateinst-p (vl-gateinst-fix x)))))

(defsection vl-gateinstlist-fix

  (defprojection vl-gateinstlist-fix (x)
    (vl-gateinst-fix x)
    :guard (vl-gateinstlist-p x))

  (local (in-theory (enable vl-gateinstlist-fix)))

  (defthm vl-gateinstlist-p-of-vl-gateinstlist-fix
    (implies (force (vl-gateinstlist-p x))
             (vl-gateinstlist-p (vl-gateinstlist-fix x)))))





(deflist vl-locationlist-p (x)
  (vl-location-p x)
  :guard t
  :elementp-of-nil nil)


(defsection vl-locationlist-string

  (defund vl-locationlist-string (n)
    (declare (xargs :guard (and (natp n)
                                (<= n 9))))
    (cond ((zp n)
           "")
          ((= n 1)
           (str::cat "~l1"))
          ((= n 2)
           (str::cat "~l2 and ~l1"))
          (t
           (str::cat "~l" (str::natstr n) ", " (vl-locationlist-string (- n 1))))))

  (local (in-theory (enable vl-locationlist-string)))

  (defthm stringp-of-vl-locationlist-string
    (stringp (vl-locationlist-string n))
    :rule-classes :type-prescription))


(defsection vl-make-duplicate-warning

  (defund vl-make-duplicate-warning (type locs modname)
    (declare (xargs :guard (and (stringp type)
                                (vl-locationlist-p locs)
                                (stringp modname))))
    (b* ((locs        (redundant-list-fix locs))
         (elide-p     (> (len locs) 9))
         (elided-locs (if elide-p (take 9 locs) locs)))
      (make-vl-warning
       :type :vl-warn-duplicates
       :msg  (str::cat "In module ~m0, found duplicated " type " at "
                       (vl-locationlist-string (len elided-locs))
                       (if elide-p
                           " (and other locations)."
                         "."))
       :args (cons modname elided-locs)
       :fatalp nil
       :fn 'vl-make-duplicate-warning
       )))

  (local (in-theory (enable vl-make-duplicate-warning)))

  (defthm vl-warning-p-of-vl-make-duplicate-warning
    (vl-warning-p (vl-make-duplicate-warning type locs modname))))



(defsection vl-duplicate-gateinst-warnings

  (defund vl-duplicate-gateinst-locations (dupe fixed orig)
    ;; Dupe is fixed and was duplicated in orig.
    ;; Fixed = (fix orig).
    ;; Collect locations of elements in orig that got fixed to dupe.
    (declare (xargs :guard (and (vl-gateinst-p dupe)
                                (vl-gateinstlist-p fixed)
                                (vl-gateinstlist-p orig)
                                (same-lengthp fixed orig))))
    (b* (((when (atom fixed))
          nil)
         (rest (vl-duplicate-gateinst-locations dupe (cdr fixed) (cdr orig)))
         ((when (equal dupe (car fixed)))
          (cons (vl-gateinst->loc (car orig)) rest)))
      rest))

  (local (in-theory (enable vl-duplicate-gateinst-locations)))

  (defthm vl-locationlist-p-of-vl-duplicate-gateinst-locations
    (implies (and (force (vl-gateinst-p dupe))
                  (force (vl-gateinstlist-p fixed))
                  (force (vl-gateinstlist-p orig))
                  (force (same-lengthp fixed orig)))
             (vl-locationlist-p (vl-duplicate-gateinst-locations dupe fixed orig))))

  (defund vl-duplicate-gateinst-warnings (dupes fixed orig modname)
    ;; Dupes are the fixed gateinsts that were duplicated.
    ;; Fixed = (fix orig).
    ;; Make warnings for each duplicate thing we found.
    (declare (xargs :guard (and (vl-gateinstlist-p dupes)
                                (vl-gateinstlist-p fixed)
                                (vl-gateinstlist-p orig)
                                (same-lengthp fixed orig)
                                (stringp modname))))
    (if (atom dupes)
        nil
      (b* ((locs    (vl-duplicate-gateinst-locations (car dupes) fixed orig))
           (warning (vl-make-duplicate-warning "gate instances" locs modname))
           (rest    (vl-duplicate-gateinst-warnings (cdr dupes) fixed orig modname)))
        (cons warning rest))))

  (local (in-theory (enable vl-duplicate-gateinst-warnings)))

  (defthm vl-warninglist-p-of-vl-duplicate-gateinst-warnings
    (vl-warninglist-p (vl-duplicate-gateinst-warnings dupes fixed orig modname))))


(defsection vl-duplicate-modinst-warnings

  (defund vl-duplicate-modinst-locations (dupe fixed orig)
    (declare (xargs :guard (and (vl-modinst-p dupe)
                                (vl-modinstlist-p fixed)
                                (vl-modinstlist-p orig)
                                (same-lengthp fixed orig))))
    (b* (((when (atom fixed))
          nil)
         (rest (vl-duplicate-modinst-locations dupe (cdr fixed) (cdr orig)))
         ((when (equal dupe (car fixed)))
          (cons (vl-modinst->loc (car orig)) rest)))
      rest))

  (local (in-theory (enable vl-duplicate-modinst-locations)))

  (defthm vl-locationlist-p-of-vl-duplicate-modinst-locations
    (implies (and (force (vl-modinst-p dupe))
                  (force (vl-modinstlist-p fixed))
                  (force (vl-modinstlist-p orig))
                  (force (same-lengthp fixed orig)))
             (vl-locationlist-p (vl-duplicate-modinst-locations dupe fixed orig))))

  (defund vl-duplicate-modinst-warnings (dupes fixed orig modname)
    (declare (xargs :guard (and (vl-modinstlist-p dupes)
                                (vl-modinstlist-p fixed)
                                (vl-modinstlist-p orig)
                                (same-lengthp fixed orig)
                                (stringp modname))))
    (if (atom dupes)
        nil
      (b* ((locs    (vl-duplicate-modinst-locations (car dupes) fixed orig))
           (warning (vl-make-duplicate-warning "module instances" locs modname))
           (rest    (vl-duplicate-modinst-warnings (cdr dupes) fixed orig modname)))
        (cons warning rest))))

  (local (in-theory (enable vl-duplicate-modinst-warnings)))

  (defthm vl-warninglist-p-of-vl-duplicate-modinst-warnings
    (vl-warninglist-p (vl-duplicate-modinst-warnings dupes fixed orig modname))))





(defsection vl-duplicate-assign-warnings

  (defund vl-duplicate-assign-locations (dupe fixed orig)
    (declare (xargs :guard (and (vl-assign-p dupe)
                                (vl-assignlist-p fixed)
                                (vl-assignlist-p orig)
                                (same-lengthp fixed orig))))
    (b* (((when (atom fixed))
          nil)
         (rest (vl-duplicate-assign-locations dupe (cdr fixed) (cdr orig)))
         ((when (equal dupe (car fixed)))
          (cons (vl-assign->loc (car orig)) rest)))
      rest))

  (local (in-theory (enable vl-duplicate-assign-locations)))

  (defthm vl-locationlist-p-of-vl-duplicate-assign-locations
    (implies (and (force (vl-assign-p dupe))
                  (force (vl-assignlist-p fixed))
                  (force (vl-assignlist-p orig))
                  (force (same-lengthp fixed orig)))
             (vl-locationlist-p (vl-duplicate-assign-locations dupe fixed orig))))

  (defund vl-duplicate-assign-warnings (dupes fixed orig modname)
    (declare (xargs :guard (and (vl-assignlist-p dupes)
                                (vl-assignlist-p fixed)
                                (vl-assignlist-p orig)
                                (same-lengthp fixed orig)
                                (stringp modname))))
    (if (atom dupes)
        nil
      (b* ((locs    (vl-duplicate-assign-locations (car dupes) fixed orig))
           (lvalue  (vl-assign->lvalue (car dupes)))
           (type    (if (vl-idexpr-p lvalue)
                        (str::cat "assignments to " (vl-idexpr->name lvalue))
                      (let ((lvalue-str (vl-pps-origexpr lvalue)))
                        (if (< (length lvalue-str) 40)
                            (str::cat "assignments to " lvalue-str)
                          (str::cat "assignments to \""
                                    (subseq lvalue-str 0 40)
                                    "...\"")))))
           (warning (vl-make-duplicate-warning type locs modname))
           (rest    (vl-duplicate-assign-warnings (cdr dupes) fixed orig modname)))
        (cons warning rest))))

  (local (in-theory (enable vl-duplicate-assign-warnings)))

  (defthm vl-warninglist-p-of-vl-duplicate-assign-warnings
    (vl-warninglist-p (vl-duplicate-assign-warnings dupes fixed orig modname))))



(defsection vl-module-duplicate-detect

  (defund vl-module-duplicate-detect (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)

         (gateinsts-fix (vl-gateinstlist-fix x.gateinsts))
         (modinsts-fix  (vl-modinstlist-fix x.modinsts))
         (assigns-fix   (vl-assignlist-fix x.assigns))

         (gateinst-dupes (duplicated-members gateinsts-fix))
         (modinst-dupes  (duplicated-members modinsts-fix))
         (assign-dupes   (duplicated-members assigns-fix))

         ((unless (or gateinst-dupes modinst-dupes assign-dupes))
          x)

         ((unless (and (vl-gateinstlist-p gateinst-dupes)
                       (vl-modinstlist-p modinst-dupes)
                       (vl-assignlist-p assign-dupes)))
          (er hard? 'vl-module-duplicate-detect
              "Eventually prove this never happens")
          x)

         (gate-warnings
          (and gateinst-dupes
               (vl-duplicate-gateinst-warnings gateinst-dupes gateinsts-fix
                                               x.gateinsts x.name)))

         (mod-warnings
          (and modinst-dupes
               (vl-duplicate-modinst-warnings modinst-dupes modinsts-fix
                                              x.modinsts x.name)))

         (ass-warnings
          (and assign-dupes
               (vl-duplicate-assign-warnings assign-dupes assigns-fix
                                             x.assigns x.name)))

         (warnings (append gate-warnings
                           mod-warnings
                           ass-warnings
                           x.warnings)))

      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-duplicate-detect)))

  (defthm vl-module-p-of-vl-module-duplicate-detect
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-duplicate-detect x))))

  (defthm vl-module->name-of-vl-module-duplicate-detect
    (equal (vl-module->name (vl-module-duplicate-detect x))
           (vl-module->name x))
    :hints(("Goal" :in-theory (disable (force))))))


(defsection vl-modulelist-duplicate-detect

  (defprojection vl-modulelist-duplicate-detect (x)
    (vl-module-duplicate-detect x)
    :guard (vl-modulelist-p x))

  (local (in-theory (enable vl-modulelist-duplicate-detect)))

  (defthm vl-modulelist-p-of-vl-modulelist-duplicate-detect
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-duplicate-detect x))))

  (defthm vl-modulelist->names-of-vl-modulelist-duplicate-detect
    (equal (vl-modulelist->names (vl-modulelist-duplicate-detect x))
           (vl-modulelist->names x))))

