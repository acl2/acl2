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
(include-book "duplicate-detect") ;; bozo for expr-fix
(include-book "../mlib/expr-tools")
(include-book "../mlib/writer")
(local (include-book "../util/arithmetic"))

(defxdoc duperhs-check
  :parents (checkers)
  :short "Check for assignments with the same right-hand side."
  :long "<p>This is a trivially simple check for cases like:</p>

@({
   assign a = rhs;
   assign b = rhs;
})

<p>That is, where @('rhs') is literally identical in both assignments.  Such
assignments are not necessarily errors, but are kind of odd.</p>")


(defalist vl-duperhs-alistp (x)
  :key (vl-expr-p x)        ;; Fixed up RHS
  :val (vl-assignlist-p x)  ;; Assignments that map to this RHS
  :keyp-of-nil nil
  :valp-of-nil t
  :parents (duperhs-check))


(defsection vl-make-duperhs-alist
  :parents (duperhs-check)
  :short "Builds the @(see vl-duperhs-alistp) for a list of assignments."

  (defund vl-make-duperhs-alist-aux (x alist)
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-duperhs-alistp alist))))
    (b* (((when (atom x))
          alist)
         (x1 (car x))
         ((vl-assign x1) x1)
         (rhs1 (hons-copy (vl-expr-fix x1.expr)))
         (look (hons-get rhs1 alist))
         ;; It doesn't matter if it exists or not, just add it in.
         (alist (hons-acons rhs1 (cons x1 (cdr look)) alist)))
      (vl-make-duperhs-alist-aux (cdr x) alist)))

  (local (in-theory (enable vl-make-duperhs-alist-aux)))

  (defthm vl-duperhs-alistp-of-vl-make-duperhs-alist-aux
    (implies (and (vl-assignlist-p x)
                  (vl-duperhs-alistp alist))
             (vl-duperhs-alistp (vl-make-duperhs-alist-aux x alist))))

  (defund vl-make-duperhs-alist (x)
    "Returns a slow alist."
    (declare (xargs :guard (vl-assignlist-p x)))
    (b* ((alist (len x))
         (alist (vl-make-duperhs-alist-aux x alist))
         (ans   (hons-shrink-alist alist nil)))
      (fast-alist-free alist)
      (fast-alist-free ans)
      ans))

  (local (in-theory (enable vl-make-duperhs-alist)))

  (defthm vl-duperhs-alistp-of-vl-make-duperhs-alist
    (implies (force (vl-assignlist-p x))
             (vl-duperhs-alistp (vl-make-duperhs-alist x)))))


(defsection vl-maybe-warn-duperhs
  :parents (duperhs-check)

  (defund vl-maybe-warn-duperhs
    (rhs      ;; The shared RHS among all these assignments
     assigns  ;; A list of assignments that share this RHS.
     warnings ;; Warnings accumulator to extend
     )
    "Returns WARNINGS'"
    (declare (xargs :guard (and (vl-expr-p rhs)
                                (vl-assignlist-p assigns))))
    (b* (((when (or (atom assigns)
                    (atom (cdr assigns))))
          ;; Nothing to do -- there isn't more than one assignment for this RHS.
          warnings)

         ((when (and (vl-fast-atom-p rhs)
                     (not (vl-fast-id-p (vl-atom->guts rhs)))))
          ;; It seems fine to assign a constant, weirdint, real, or string to
          ;; multiple wires; this is especially frequent for things like 0 and
          ;; 1, so don't warn in these cases.  However, note that we explicitly
          ;; exclude identifiers here, so if we have a situation like:
          ;;   assign wire1 = wirefoo;
          ;;   assign wire2 = wirefoo;
          ;; Then we'll still flag it, it might be a copy/paste error.
          warnings)

         (rhs-names (vl-expr-names rhs))
         (special-names (append (str::collect-strs-with-isubstr "ph1" rhs-names)
                                (str::collect-strs-with-isubstr "reset" rhs-names)
                                (str::collect-strs-with-isubstr "clear" rhs-names)
                                (str::collect-strs-with-isubstr "enable" rhs-names)
                                (str::collect-strs-with-isubstr "clken" rhs-names)
                                (str::collect-strs-with-isubstr "valid" rhs-names)
                                ))
         ((when (consp special-names))
          ;; It's common for the same expression to be used multiple times for clock
          ;; enables and for a clock to go multiple places, so try to filter this out.
          warnings)

         ;; BOZO maybe filter out other things? (reset, done, clear, stuff like
         ;; that, by name?)
         (w (make-vl-warning
             :type :vl-warn-same-rhs
             :msg "Found assignments that have exactly the same right-hand ~
                   side, which might indicate a copy/paste error:~%~s0"
             :args (list (str::prefix-lines (with-local-ps
                                             ;; may help avoid unnecessary line wrapping
                                             (vl-ps-update-autowrap-col 200)
                                             (vl-pp-assignlist assigns))
                                            "     ")
                         ;; These aren't printed, but we include them in the
                         ;; warning so our suppression mechanism can be
                         ;; applied.
                         assigns)
             :fatalp nil
             :fn 'vl-maybe-warn-duperhs)))
      (cons w warnings)))

  (local (in-theory (enable vl-maybe-warn-duperhs)))

  (defthm vl-warninglist-p-of-vl-maybe-warn-duperhs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-maybe-warn-duperhs rhs assigns warnings)))))


(defsection vl-warnings-for-duperhs-alist
  :parents (duperhs-check)

  (defund vl-warnings-for-duperhs-alist (alist warnings)
    (declare (xargs :guard (and (vl-duperhs-alistp alist)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom alist))
          warnings)
         (rhs      (caar alist))
         (assigns  (cdar alist))
         (warnings (vl-maybe-warn-duperhs rhs assigns warnings)))
      (vl-warnings-for-duperhs-alist (cdr alist) warnings)))

  (local (in-theory (enable vl-warnings-for-duperhs-alist)))

  (defthm vl-warninglist-p-of-vl-warnings-for-duperhs-alist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-warnings-for-duperhs-alist alist warnings)))))



(defsection vl-module-duperhs-check
  :parents (duperhs-check)

  (defund vl-module-duperhs-check (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (alist    (vl-make-duperhs-alist x.assigns))
;         (- (cw "Alist has ~x0 entries.~%" (len alist)))
         (warnings (vl-warnings-for-duperhs-alist alist x.warnings)))
      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-duperhs-check)))

  (defthm vl-module-p-of-vl-module-duperhs-check
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-duperhs-check x))))

  (defthm vl-module->name-of-vl-module-duperhs-check
    (equal (vl-module->name (vl-module-duperhs-check x))
           (vl-module->name x))))


(defsection vl-modulelist-duperhs-check
  :parents (duperhs-check)

  (defprojection vl-modulelist-duperhs-check (x)
    (vl-module-duperhs-check x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p
    :parents (duperhs-check))

  (defthm vl-modulelist->names-of-vl-modulelist-duperhs-check
    (equal (vl-modulelist->names (vl-modulelist-duperhs-check x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))


