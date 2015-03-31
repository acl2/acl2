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
(include-book "../mlib/scopestack")
(include-book "../mlib/filter")
(include-book "../mlib/modnamespace")
(include-book "../mlib/blocks")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection drop-missing-submodules
  :parents (lint)
  :short "(Unsound transform) Remove instances of missing submodules."

  :long "<p>In our ordinary transformation process, e.g., @(see vl-simplify),
modules that instance an undefined submodule are thrown out with fatal
errors.</p>

<p>In @(see vl-lint), we still want to analyze them as much as we can.  So, in
this transformation, we simply delete any instances of missing submodules,
perhaps leaving us with \"partial\" superior modules.</p>

<p>This is obviously unsound and should never be used in our ordinary
transformation process.</p>")

(local (xdoc::set-default-parents drop-missing-submodules))

(define vl-gather-names-of-missing-definitions ((names string-listp)
                                                (ss    vl-scopestack-p))
  :returns (missing-names string-listp)
  (b* (((when (atom names))
        nil)
       (name1 (string-fix (car names)))
       (look  (vl-scopestack-find-definition name1 ss))
       ((when look)
        (vl-gather-names-of-missing-definitions (cdr names) ss)))
    (cons name1
          (vl-gather-names-of-missing-definitions (cdr names) ss))))

(def-genblob-transform vl-genblob-drop-missing-submodules
  ((ss            vl-scopestack-p)
   (dropped-insts vl-modinstlist-p "Accumulator"))
  :returns ((dropped-insts vl-modinstlist-p))
  (b* (((vl-genblob x) x)
       (ss                        (vl-scopestack-push (vl-genblob-fix x) ss))
       (all-modnames              (mergesort (vl-modinstlist->modnames x.modinsts)))
       (missing-modnames          (vl-gather-names-of-missing-definitions all-modnames ss))
       ((mv bad-insts good-insts) (vl-filter-modinsts-by-modname missing-modnames x.modinsts))
       (dropped-insts             (append bad-insts (vl-modinstlist-fix dropped-insts)))
       ((mv dropped-insts good-generates)
        (vl-generates-drop-missing-submodules x.generates ss dropped-insts)))
    (mv dropped-insts
        (change-vl-genblob x
                           :modinsts good-insts
                           :generates good-generates)))
     :apply-to-generates vl-generates-drop-missing-submodules)

(define vl-module-drop-missing-submodules
  ((x       vl-module-p  "Module to rewrite.")
   (ss      vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       (genblob       (vl-module->genblob x))
       ((mv dropped-insts new-genblob) (vl-genblob-drop-missing-submodules genblob ss nil))
       (nbad             (len dropped-insts))
       (missing-modnames (mergesort (vl-modinstlist->modnames dropped-insts)))
       (warnings (if (atom dropped-insts)
                     x.warnings
                   (fatal :type :vl-dropped-insts
                          :msg "Deleting ~x0 instance~s1 of undefined ~
                                module~s2 ~&3. This may cause our analysis to ~
                                be flawed."
                          :args (list nbad
                                      (if (eql nbad 1) "" "s")
                                      (if (vl-plural-p missing-modnames) "s" "")
                                      missing-modnames)
                          :acc x.warnings)))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module new-genblob x-warn)))

(defprojection vl-modulelist-drop-missing-submodules ((x  vl-modulelist-p)
                                                      (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-drop-missing-submodules x ss))

(define vl-design-drop-missing-submodules ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss   (vl-scopestack-init x))
       (mods (vl-modulelist-drop-missing-submodules x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
