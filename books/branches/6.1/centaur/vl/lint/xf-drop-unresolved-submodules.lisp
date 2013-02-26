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
(include-book "../mlib/filter")
(include-book "../mlib/hierarchy")
(local (include-book "../util/arithmetic"))


; VL-Lint Only.
;
; In our ordinary transformation process, failing to resolve the arguments of
; a module instance will just add fatal warnings and otherwise doesn't alter
; the module instance.
;
; For VL-Lint, we'd rather 

(defsection vl-module-drop-unresolved-submodules

  (defund vl-module-drop-missing-submodules (x missing fal)
    (declare (xargs :guard (and (vl-module-p x)
                                (string-listp missing)
                                (equal fal (make-lookup-alist missing)))))
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
                               (if (= nbad 1) "" "s")
                               (if (= nbad 1) "it refers" "they refer")
                               (if (vl-plural-p bad-names) "s" "")
                               bad-names)
                   :fatalp t
                   :fn 'vl-module-drop-missing-submodules)))
            (change-vl-module x
                              :modinsts good-insts
                              :warnings (cons w x.warnings)))))
      x))

  (local (in-theory (enable vl-module-drop-missing-submodules)))

  (defthm vl-module-p-of-vl-module-drop-missing-submodules
    (implies (and (force (vl-module-p x))
                  (force (equal fal (make-lookup-alist missing))))
             (vl-module-p (vl-module-drop-missing-submodules x missing fal))))

  (defthm vl-module->name-of-vl-module-drop-missing-submodules
    (implies (force (equal fal (make-lookup-alist missing)))
             (equal (vl-module->name (vl-module-drop-missing-submodules x missing fal))
                    (vl-module->name x)))))



(defsection vl-modulelist-drop-missing-submodules-aux

  (defprojection vl-modulelist-drop-missing-submodules-aux (x missing fal)
    (vl-module-drop-missing-submodules x missing fal)
    :guard (and (vl-modulelist-p x)
                (string-listp missing)
                (equal fal (make-lookup-alist missing)))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-drop-missing-submodules-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-drop-missing-submodules-aux
    (implies (force (equal fal (make-lookup-alist missing)))
             (equal (vl-modulelist->names
                     (vl-modulelist-drop-missing-submodules-aux x missing fal))
                    (vl-modulelist->names x)))))



(defsection vl-modulelist-drop-missing-submodules

  (defund vl-modulelist-drop-missing-submodules (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((missing (vl-modulelist-missing x))
         (fal     (make-lookup-alist missing))
         (x-prime (vl-modulelist-drop-missing-submodules-aux x missing fal))
         (-       (fast-alist-free fal)))
      x-prime))

  (local (in-theory (enable vl-modulelist-drop-missing-submodules)))

  (defthm vl-modulelist-p-of-vl-modulelist-drop-missing-submodules
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-drop-missing-submodules x))))

  (defthm vl-modulelist->names-of-vl-modulelist-drop-missing-submodules
    (equal (vl-modulelist->names (vl-modulelist-drop-missing-submodules x))
           (vl-modulelist->names x))))

