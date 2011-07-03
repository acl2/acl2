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
(include-book "../mlib/stmt-tools")
(include-book "../mlib/namefactory")
(local (include-book "../util/arithmetic"))


(defsection vl-evatom-negedge-elim

; Maybe rewrite an evatom, converting it from a negedge to a posedge version,
; using a new wire.

  (defund vl-evatom-negedge-elim (x nf netdecls assigns loc)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-evatom-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns)
                                (vl-location-p loc))))
    (b* (((unless (eq (vl-evatom->type x) :vl-negedge))
          (mv nf x netdecls assigns))

         (expr    (vl-evatom->expr x))
         (~expr   (make-vl-nonatom :op :vl-unary-bitnot :args (list expr)))

         ;; Generate a fresh wire and assign ~expr to it.
         ((mv new-name nf) (vl-namefactory-indexed-name "negedge" nf))
         (new-name-expr (make-vl-atom :guts (make-vl-id :name new-name)))
         (x-prime       (change-vl-evatom x
                                          :type :vl-posedge
                                          :expr new-name-expr))

         (atts     (acons "VL_NEGEDGE" expr nil))
         (new-decl (make-vl-netdecl :loc loc :name new-name :type :vl-wire :atts atts))
         (netdecls (cons new-decl netdecls))

         (new-assign (make-vl-assign :loc loc :lvalue new-name-expr :expr ~expr :atts atts))
         (assigns    (cons new-assign assigns)))

        (mv nf x-prime netdecls assigns)))

  (local (in-theory (enable vl-evatom-negedge-elim)))

  (defthm vl-evatom-negedge-elim-basics
    (implies (and (force (vl-evatom-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-location-p loc)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-evatom-negedge-elim x nf netdecls assigns loc)))
                  (vl-evatom-p
                   (mv-nth 1 (vl-evatom-negedge-elim x nf netdecls assigns loc)))
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-evatom-negedge-elim x nf netdecls assigns loc)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-evatom-negedge-elim x nf netdecls assigns loc)))))))


(defsection vl-evatomlist-negedge-elim

  (defund vl-evatomlist-negedge-elim (x nf netdecls assigns loc)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-evatomlist-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns)
                                (vl-location-p loc))))
    (b* (((when (atom x))
          (mv nf x netdecls assigns))
         ((mv nf car-prime netdecls assigns)
          (vl-evatom-negedge-elim (car x) nf netdecls assigns loc))
         ((mv nf cdr-prime netdecls assigns)
          (vl-evatomlist-negedge-elim (cdr x) nf netdecls assigns loc))
         (x-prime (cons car-prime cdr-prime)))
        (mv nf x-prime netdecls assigns)))

  (local (in-theory (enable vl-evatomlist-negedge-elim)))

  (defthm vl-evatomlist-negedge-elim-basics
    (implies (and (force (vl-evatomlist-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-location-p loc)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-evatomlist-negedge-elim x nf netdecls assigns loc)))
                  (vl-evatomlist-p
                   (mv-nth 1 (vl-evatomlist-negedge-elim x nf netdecls assigns loc)))
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-evatomlist-negedge-elim x nf netdecls assigns loc)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-evatomlist-negedge-elim x nf netdecls assigns loc)))))))


(defsection vl-eventcontrol-negedge-elim

  (defund vl-eventcontrol-negedge-elim (x nf netdecls assigns loc)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-eventcontrol-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns)
                                (vl-location-p loc))))
    (b* ((atoms (vl-eventcontrol->atoms x))
         ((mv nf atoms netdecls assigns)
          (vl-evatomlist-negedge-elim atoms nf netdecls assigns loc))
         (x-prime
          (change-vl-eventcontrol x :atoms atoms)))
        (mv nf x-prime netdecls assigns)))

  (local (in-theory (enable vl-eventcontrol-negedge-elim)))

  (defthm vl-eventcontrol-negedge-elim-basics
    (implies (and (force (vl-eventcontrol-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-location-p loc)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-eventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (vl-eventcontrol-p
                   (mv-nth 1 (vl-eventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (iff (mv-nth 1 (vl-eventcontrol-negedge-elim x nf netdecls assigns loc))
                       t)
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-eventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-eventcontrol-negedge-elim x nf netdecls assigns loc)))))))


(defsection vl-delayoreventcontrol-negedge-elim

  (defund vl-delayoreventcontrol-negedge-elim (x nf netdecls assigns loc)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-delayoreventcontrol-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns)
                                (vl-location-p loc))))
    (case (tag x)
      (:vl-eventcontrol (vl-eventcontrol-negedge-elim x nf netdecls assigns loc))
      (otherwise (mv nf x netdecls assigns))))

  (local (in-theory (enable vl-delayoreventcontrol-negedge-elim)))

  (defthm vl-delayoreventcontrol-negedge-elim-basics
    (implies (and (force (vl-delayoreventcontrol-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-location-p loc)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-delayoreventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (vl-delayoreventcontrol-p
                   (mv-nth 1 (vl-delayoreventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (iff (mv-nth 1 (vl-delayoreventcontrol-negedge-elim x nf netdecls assigns loc))
                       t)
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-delayoreventcontrol-negedge-elim x nf netdecls assigns loc)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-delayoreventcontrol-negedge-elim x nf netdecls assigns loc)))))))


(defsection vl-stmt-negedge-elim

  (mutual-recursion

   (defund vl-stmt-negedge-elim (x nf netdecls assigns loc)
     "Returns (MV NF' X' NETDECLS' ASSIGNS')"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-location-p loc))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (mv nf x netdecls assigns))

          (type (vl-compoundstmt->type x))
          (stmts (vl-compoundstmt->stmts x))

          ((mv nf stmts netdecls assigns)
           (vl-stmtlist-negedge-elim stmts nf netdecls assigns loc))

          (x (change-vl-compoundstmt x :stmts stmts))

          ((unless (eq type :vl-timingstmt))
           (mv nf x netdecls assigns))

          (ctrl (vl-timingstmt->ctrl x))
          (body (vl-timingstmt->body x))
          (atts (vl-compoundstmt->atts x))

          ((mv nf ctrl netdecls assigns)
           (vl-delayoreventcontrol-negedge-elim ctrl nf netdecls assigns loc))

          (x (make-vl-timingstmt :ctrl ctrl :body body :atts atts)))

         (mv nf x netdecls assigns)))

   (defund vl-stmtlist-negedge-elim (x nf netdecls assigns loc)
     "Returns (MV NF' X' NETDECLS' ASSIGNS')"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-location-p loc))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv nf nil netdecls assigns))
          ((mv nf car-prime netdecls assigns)
           (vl-stmt-negedge-elim (car x) nf netdecls assigns loc))
          ((mv nf cdr-prime netdecls assigns)
           (vl-stmtlist-negedge-elim (cdr x) nf netdecls assigns loc))
          (x-prime (cons car-prime cdr-prime)))
         (mv nf x-prime netdecls assigns))))

  (flag::make-flag vl-flag-stmt-negedge-elim
                   vl-stmt-negedge-elim
                   :flag-mapping ((vl-stmt-negedge-elim . stmt)
                                  (vl-stmtlist-negedge-elim . list)))

  (defthm vl-stmtlist-negedge-elim-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-negedge-elim x nf netdecls assigns loc)
                    (mv nf nil netdecls assigns)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-negedge-elim))))

  (defthm vl-stmtlist-negedge-elim-of-cons
    (equal (vl-stmtlist-negedge-elim (cons a x) nf netdecls assigns loc)
           (b* (((mv nf car-prime netdecls assigns)
                 (vl-stmt-negedge-elim a nf netdecls assigns loc))
                ((mv nf cdr-prime netdecls assigns)
                 (vl-stmtlist-negedge-elim x nf netdecls assigns loc))
                (x-prime (cons car-prime cdr-prime)))
               (mv nf x-prime netdecls assigns)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-negedge-elim))))

  (local (defun my-induction (x nf netdecls assigns loc)
           (if (atom x)
               (mv nf nil netdecls assigns)
             (b* (((mv nf car-prime netdecls assigns)
                   (vl-stmt-negedge-elim (car x) nf netdecls assigns loc))
                  ((mv nf cdr-prime netdecls assigns)
                   (my-induction (cdr x) nf netdecls assigns loc))
                  (x-prime (cons car-prime cdr-prime)))
                 (mv nf x-prime netdecls assigns)))))

  (defthm len-of-vl-stmtlist-negedge-elim
    (equal (len (mv-nth 1 (vl-stmtlist-negedge-elim x nf netdecls assigns loc)))
           (len x))
    :hints(("Goal" :induct (my-induction x nf netdecls assigns loc))))

  (local
   (defthm nasty-nasty

; Uggggh... Can't use vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
; because (vl-compoundstmt->type x) gets rewritten.  use of compoundstmt->exprs
; is horrible but gives us a binding for x.

     (implies (and (force (vl-compoundstmt-p x))
                   (force (equal :vl-timingstmt           (vl-compoundstmt->type x)))
                   (force (iff (double-rewrite new-name)  (vl-compoundstmt->name x)))
                   (force (iff (double-rewrite new-ctrl)  (vl-compoundstmt->ctrl x)))
                   (force (equal new-sequentialp          (vl-compoundstmt->sequentialp x)))
                   (force (equal new-casetype             (vl-compoundstmt->casetype x)))
                   (force (equal (consp new-decls) (consp (vl-compoundstmt->decls x))))
                   (force (equal (len (double-rewrite new-stmts)) (len (vl-compoundstmt->stmts x))))
                   )
              (vl-compoundstmt-basic-checksp :vl-timingstmt
                                             (vl-compoundstmt->exprs x)
                                             new-stmts new-name new-decls
                                             new-ctrl new-sequentialp new-casetype))
     :hints(("Goal"
             :in-theory (disable vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt)
             :use ((:instance vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
                              (new-exprs (vl-compoundstmt->exprs x))
                              ))))))

  (defthm-vl-flag-stmt-negedge-elim lemma

    (stmt (implies (and (force (vl-stmt-p x))
                        (force (vl-namefactory-p nf))
                        (force (vl-netdecllist-p netdecls))
                        (force (vl-assignlist-p assigns))
                        (force (vl-location-p loc)))
                   (and (vl-namefactory-p
                         (mv-nth 0 (vl-stmt-negedge-elim x nf netdecls assigns loc)))
                        (vl-stmt-p
                         (mv-nth 1 (vl-stmt-negedge-elim x nf netdecls assigns loc)))
                        (vl-netdecllist-p
                         (mv-nth 2 (vl-stmt-negedge-elim x nf netdecls assigns loc)))
                        (vl-assignlist-p
                         (mv-nth 3 (vl-stmt-negedge-elim x nf netdecls assigns loc)))))
          :name vl-stmt-negedge-elim-basics)

    (list (implies (and (force (vl-stmtlist-p x))
                        (force (vl-namefactory-p nf))
                        (force (vl-netdecllist-p netdecls))
                        (force (vl-assignlist-p assigns))
                        (force (vl-location-p loc)))
                   (and (vl-namefactory-p
                         (mv-nth 0 (vl-stmtlist-negedge-elim x nf netdecls assigns loc)))
                        (vl-stmtlist-p
                         (mv-nth 1 (vl-stmtlist-negedge-elim x nf netdecls assigns loc)))
                        (vl-netdecllist-p
                         (mv-nth 2 (vl-stmtlist-negedge-elim x nf netdecls assigns loc)))
                        (vl-assignlist-p
                         (mv-nth 3 (vl-stmtlist-negedge-elim x nf netdecls assigns loc)))))
          :name vl-stmtlist-negedge-elim-basics)

    :hints(("Goal"
            :induct (vl-flag-stmt-negedge-elim flag x nf netdecls assigns loc)
            :expand ((vl-stmt-negedge-elim x nf netdecls assigns loc)))))

  (verify-guards vl-stmt-negedge-elim))


(defsection vl-always-negedge-elim

  (defund vl-always-negedge-elim (x nf netdecls assigns)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-always-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns))))
    (b* ((stmt (vl-always->stmt x))
         (loc  (vl-always->loc x))
         ((mv nf stmt netdecls assigns)
          (vl-stmt-negedge-elim stmt nf netdecls assigns loc))
         (x-prime
          (change-vl-always x :stmt stmt)))
        (mv nf x-prime netdecls assigns)))

  (local (in-theory (enable vl-always-negedge-elim)))

  (defthm vl-always-negedge-elim-basics
    (implies (and (force (vl-always-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-always-negedge-elim x nf netdecls assigns)))
                  (vl-always-p
                   (mv-nth 1 (vl-always-negedge-elim x nf netdecls assigns)))
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-always-negedge-elim x nf netdecls assigns)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-always-negedge-elim x nf netdecls assigns)))))))


(defsection vl-alwayslist-negedge-elim

  (defund vl-alwayslist-negedge-elim (x nf netdecls assigns)
    "Returns (MV NF' X' NETDECLS' ASSIGNS')"
    (declare (xargs :guard (and (vl-alwayslist-p x)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns))))
    (b* (((when (atom x))
          (mv nf x netdecls assigns))
         ((mv nf car-prime netdecls assigns)
          (vl-always-negedge-elim (car x) nf netdecls assigns))
         ((mv nf cdr-prime netdecls assigns)
          (vl-alwayslist-negedge-elim (cdr x) nf netdecls assigns))
         (x-prime (cons car-prime cdr-prime)))
        (mv nf x-prime netdecls assigns)))

  (local (in-theory (enable vl-alwayslist-negedge-elim)))

  (defthm vl-alwayslist-negedge-elim-basics
    (implies (and (force (vl-alwayslist-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-assignlist-p assigns)))
             (and (vl-namefactory-p
                   (mv-nth 0 (vl-alwayslist-negedge-elim x nf netdecls assigns)))
                  (vl-alwayslist-p
                   (mv-nth 1 (vl-alwayslist-negedge-elim x nf netdecls assigns)))
                  (vl-netdecllist-p
                   (mv-nth 2 (vl-alwayslist-negedge-elim x nf netdecls assigns)))
                  (vl-assignlist-p
                   (mv-nth 3 (vl-alwayslist-negedge-elim x nf netdecls assigns)))))))



(defsection vl-module-negedge-elim

  (defund vl-module-negedge-elim (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* ((alwayses (vl-module->alwayses x))
         (netdecls (vl-module->netdecls x))
         (assigns  (vl-module->assigns x))
         (nf       (vl-starting-namefactory x))
         ((mv nf alwayses netdecls assigns)
          (vl-alwayslist-negedge-elim alwayses nf netdecls assigns))
         (-        (vl-free-namefactory nf))
         (x-prime
          (change-vl-module x
                            :alwayses alwayses
                            :netdecls netdecls
                            :assigns assigns)))
        x-prime))

  (local (in-theory (enable vl-module-negedge-elim)))

  (defthm vl-module-p-of-vl-module-negedge-elim
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-negedge-elim x))))

  (defthm vl-module->name-of-vl-module-negedge-elim
    (equal (vl-module->name (vl-module-negedge-elim x))
           (vl-module->name x))))


(defsection vl-modulelist-negedge-elim

  (defprojection vl-modulelist-negedge-elim (x)
    (vl-module-negedge-elim x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-negedge-elim)))

  (defthm vl-modulelist->names-of-vl-modulelist-negedge-elim
    (equal (vl-modulelist->names (vl-modulelist-negedge-elim x))
           (vl-modulelist->names x))))
