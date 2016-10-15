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
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc drop-user-submodules
  :parents (vl-lint)
  :short "(Unsound transform) Remove modules that the user says to drop, and
simultaneously remove all instances of these submodules."

  :long "<p>This is useful for modules that the user knows VL-Lint can't make
any sense of, or for modules that the user just isn't interested in because
they are, say, owned by some other logic designer.</p>")

(local (xdoc::set-default-parents drop-user-submodules))

(define vl-module-drop-user-submodules
  ((x       vl-module-p  "Module to rewrite.")
   (names   string-listp "List of module names to drop.")
   (fal     "Precomputed fast alist for @('names')."
            (equal fal (make-lookup-alist names))))
  :returns (new-x vl-module-p)
  :short "Remove instances of modules that we're supposed to drop."
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((mv bad-insts good-insts)
        (vl-filter-modinsts-by-modname+ names x.modinsts fal))
       ((when bad-insts)
        (b* ((nbad      (len bad-insts))
             (bad-names (mergesort (vl-modinstlist->modnames bad-insts)))
             (warnings  (fatal :type :vl-dropped-insts
                               :msg "In module ~m0, deleting ~x1 submodule ~
                                     instance~s2 because ~s3 to the module~s4 ~
                                     ~&5, which we have been told to drop.  ~
                                     These deletions might cause our analysis ~
                                     to be flawed."
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

(defprojection vl-modulelist-drop-user-submodules-aux
  ((x     vl-modulelist-p)
   (names string-listp)
   (fal   (equal fal (make-lookup-alist names))))
  :returns (new-x vl-modulelist-p)
  (vl-module-drop-user-submodules x names fal))

(define vl-modulelist-drop-user-submodules
  ((x    vl-modulelist-p "Module list to filter.")
   (drop string-listp    "Names of modules to drop."))
  :returns (new-x vl-modulelist-p)
  (b* ((drop    (string-list-fix drop))
       (x       (vl-delete-modules drop x))
       (fal     (make-lookup-alist drop))
       (x-prime (vl-modulelist-drop-user-submodules-aux x drop fal)))
    (fast-alist-free fal)
    x-prime))

(define vl-design-drop-user-submodules ((x    vl-design-p)
                                        (drop string-listp))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-drop-user-submodules x.mods drop)))
    (change-vl-design x :mods new-mods)))
