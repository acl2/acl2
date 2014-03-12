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
(include-book "../mlib/filter")
(include-book "../mlib/hierarchy")
(local (include-book "../util/arithmetic"))

(defsection drop-missing-submodules
  :parents (lint)
  :short "(Unsound transform) Remove instances of missing submodules."

  :long "<p>In our ordinary transformation process, e.g., @(see vl-simplify),
modules that instance an undefined submodule are thrown out with fatal errors.
In VL-Lint, we still want to analyze them as much as we can.  So, in this
transformation, we simply delete any instances of missing submodules, perhaps
leaving us with \"partial\" superior modules.</p>

<p>This is obviously unsound and should never be used in our ordinary
transformation process.</p>")

(local (xdoc::set-default-parents drop-missing-submodules))

(define vl-module-drop-missing-submodules
  ((x       vl-module-p  "Module to rewrite.")
   (missing string-listp "List of missing modules.")
   (fal     "Precomputed fast alist for missing."
            (equal fal (make-lookup-alist missing))))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((mv bad-insts good-insts)
        (vl-fast-filter-modinsts-by-modname missing fal x.modinsts nil nil))
       ((when bad-insts)
        (b* ((nbad      (len bad-insts))
             (bad-names (mergesort (vl-modinstlist->modnames bad-insts)))
             (w (make-vl-warning
                 :type :vl-dropped-insts
                 :msg "In module ~m0, deleting ~x1 submodule instance~s2 ~
                       because ~s3 to the undefined module~s4 ~&5.  These ~
                       deletions might cause our analysis to be flawed."
                 :args (list x.name
                             nbad
                             (if (eql nbad 1) "" "s")
                             (if (eql nbad 1) "it refers" "they refer")
                             (if (vl-plural-p bad-names) "s" "")
                             bad-names)
                 :fatalp t
                 :fn 'vl-module-drop-missing-submodules)))
          (change-vl-module x
                            :modinsts good-insts
                            :warnings (cons w x.warnings)))))
    x))

(defprojection vl-modulelist-drop-missing-submodules-aux (x missing fal)
  (vl-module-drop-missing-submodules x missing fal)
  :guard (and (vl-modulelist-p x)
              (string-listp missing)
              (equal fal (make-lookup-alist missing)))
  :result-type vl-modulelist-p)

(define vl-modulelist-drop-missing-submodules ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* ((missing (vl-modulelist-missing x))
       (fal     (make-lookup-alist missing))
       (x-prime (vl-modulelist-drop-missing-submodules-aux x missing fal)))
    (fast-alist-free fal)
    x-prime))

(define vl-design-drop-missing-submodules ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-drop-missing-submodules x.mods))))
