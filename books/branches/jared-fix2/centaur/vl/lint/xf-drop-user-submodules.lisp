; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))

(define vl-module-drop-user-submodules
  ((x       vl-module-p  "Module to rewrite.")
   (names   string-listp "List of module names to drop.")
   (fal     "Precomputed fast alist for @('names')."
            (equal fal (make-lookup-alist names))))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (vl-modulelist-drop-user-submodules)
  :short "Remove instances of modules that we're supposed to drop."

  (b* (((vl-module x) x)
       ((mv bad-insts good-insts)
        (vl-fast-filter-modinsts-by-modname names fal x.modinsts nil nil))
       ((when bad-insts)
        (b* ((nbad      (len bad-insts))
             (bad-names (mergesort (vl-modinstlist->modnames bad-insts)))
             (w (make-vl-warning
                 :type :vl-dropped-insts
                 :msg "In module ~m0, deleting ~x1 submodule instance~s2 ~
                       because ~s3 to the module~s4 ~&5, which we have been ~
                       told to drop.  These deletions might cause our ~
                       analysis to be flawed."
                 :args (list x.name
                             nbad
                             (if (eql nbad 1) "" "s")
                             (if (eql nbad 1) "it refers" "they refer")
                             (if (vl-plural-p bad-names) "s" "")
                             bad-names)
                 :fatalp t
                 :fn 'vl-module-drop-user-submodules)))
          (change-vl-module x
                            :modinsts good-insts
                            :warnings (cons w x.warnings)))))
    x)

  ///
  (defthm vl-module->name-of-vl-module-drop-user-submodules
    (equal (vl-module->name (vl-module-drop-user-submodules x names fal))
           (vl-module->name x))
    :hints(("Goal" :in-theory (disable (force))))))


(defprojection vl-modulelist-drop-user-submodules-aux (x names fal)
  (vl-module-drop-user-submodules x names fal)
  :guard (and (vl-modulelist-p x)
              (string-listp names)
              (equal fal (make-lookup-alist names)))
  :result-type vl-modulelist-p
  :parents (vl-modulelist-drop-user-submodules)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-drop-user-submodules-aux
     (implies (force (equal fal (make-lookup-alist names)))
              (equal (vl-modulelist->names
                      (vl-modulelist-drop-user-submodules-aux x names fal))
                     (vl-modulelist->names x))))))


(define vl-modulelist-drop-user-submodules
  ((x    vl-modulelist-p "Module list to filter.")
   (drop string-listp    "Names of modules to drop."))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  :parents (lint)
  :short "(Unsound transform) Remove modules that the user says to drop, and
simultaneously remove all instances of these submodules."

  (b* ((x       (vl-delete-modules drop x))
       (fal     (make-lookup-alist drop))
       (x-prime (vl-modulelist-drop-user-submodules-aux x drop fal))
       (-       (fast-alist-free fal)))
    x-prime)

  ///
  (defthm uniquep-of-vl-modulelist->names-of-vl-modulelist-drop-user-submodules
    (implies (force (uniquep (vl-modulelist->names x)))
             (uniquep (vl-modulelist->names
                       (vl-modulelist-drop-user-submodules x names))))))
