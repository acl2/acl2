; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../mlib/filter")
(include-book "../mlib/hierarchy")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

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
   (fal     "Precomputed fast alist for missing." (equal fal (make-lookup-alist missing))))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((mv bad-insts good-insts)
        (vl-filter-modinsts-by-modname+ missing x.modinsts fal))
       ((when bad-insts)
        (b* ((nbad      (len bad-insts))
             (bad-names (mergesort (vl-modinstlist->modnames bad-insts)))
             (warnings  (fatal :type :vl-dropped-insts
                               :msg "In module ~m0, deleting ~x1 submodule ~
                                     instance~s2 because ~s3 to the undefined ~
                                     module~s4 ~&5.  These deletions might ~
                                     cause our analysis to be flawed."
                               :args (list x.name
                                           nbad
                                           (if (eql nbad 1) "" "s")
                                           (if (eql nbad 1) "it refers" "they refer")
                                           (if (vl-plural-p bad-names) "s" "")
                                           bad-names)
                               :acc x.warnings)))
          (change-vl-module x
                            :modinsts good-insts
                            :warnings warnings))))
    x))

(defprojection vl-modulelist-drop-missing-submodules-aux ((x       vl-modulelist-p)
                                                          (missing string-listp)
                                                          (fal     (equal fal (make-lookup-alist missing))))
  :returns (new-x vl-modulelist-p)
  (vl-module-drop-missing-submodules x missing fal))

(define vl-modulelist-drop-missing-submodules ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (b* ((missing (vl-modulelist-missing x))
       (fal     (make-lookup-alist missing))
       (x-prime (vl-modulelist-drop-missing-submodules-aux x missing fal)))
    (fast-alist-free fal)
    x-prime))

(define vl-design-drop-missing-submodules ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-drop-missing-submodules x.mods))))
