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
(local (include-book "../util/arithmetic"))

; VL-Lint Only.
;
; We eliminte $verror and $acc_readmem statements to cut down on noisy warnings
; about dropping unsupported constructs.

(defund vl-lint-throwaway-fn-p (x)
  (declare (xargs :guard (vl-stmt-p x)
                  :guard-debug t))
  (b* (((unless (vl-fast-enablestmt-p x))
        nil)
       ((vl-enablestmt x) x)
       ((unless (vl-fast-atom-p x.id))
        nil)
       ((vl-atom x.id) x.id)
       ((unless (vl-fast-sysfunname-p x.id.guts))
        nil)
       ((vl-sysfunname x.id.guts) x.id.guts))
    (member-equal x.id.guts.name
                  (list "$display" "$vcover" "$verror" "$acc_readmem"))))

(defsection vl-lint-stmt-rewrite

  (mutual-recursion

   (defund vl-lint-stmt-rewrite (x)
     (declare (xargs :guard (vl-stmt-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (cond ((vl-fast-atomicstmt-p x)
            (if (vl-lint-throwaway-fn-p x)
                (make-vl-nullstmt)
              x))
           (t
            (change-vl-compoundstmt x
                                    :stmts (vl-lint-stmtlist-rewrite
                                            (vl-compoundstmt->stmts x))))))

   (defund vl-lint-stmtlist-rewrite (x)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-lint-stmt-rewrite (car x))
             (vl-lint-stmtlist-rewrite (cdr x))))))

  (defthm len-of-vl-lint-stmtlist-rewrite
    (equal (len (vl-lint-stmtlist-rewrite x))
           (len x))
    :hints(("Goal"
            :expand ((vl-lint-stmtlist-rewrite x))
            :induct (len x))))

  (flag::make-flag vl-flag-lint-stmt-rewrite
                   vl-lint-stmt-rewrite
                   :flag-mapping ((vl-lint-stmt-rewrite . stmt)
                                  (vl-lint-stmtlist-rewrite . list)))

  (defthm-vl-flag-lint-stmt-rewrite
    (defthm vl-stmt-p-of-vl-lint-stmt-rewrite
      (implies (force (vl-stmt-p x))
               (vl-stmt-p (vl-lint-stmt-rewrite x)))
      :flag stmt)
    (defthm vl-stmtlist-p-of-vl-lint-stmtlist-rewrite
      (implies (force (vl-stmtlist-p x))
               (vl-stmtlist-p (vl-lint-stmtlist-rewrite x)))
      :flag list)
    :hints(("Goal"
            :expand ((vl-lint-stmt-rewrite x)
                     (vl-lint-stmtlist-rewrite x)))))

  (verify-guards vl-lint-stmt-rewrite))




(defsection vl-always-lint-stmt-rewrite

  (defund vl-always-lint-stmt-rewrite (x)
    (declare (xargs :guard (vl-always-p x)))
    (change-vl-always x :stmt (vl-lint-stmt-rewrite (vl-always->stmt x))))

  (local (in-theory (enable vl-always-lint-stmt-rewrite)))

  (defthm vl-always-p-of-vl-always-lint-stmt-rewrite
    (implies (force (vl-always-p x))
             (vl-always-p (vl-always-lint-stmt-rewrite x)))))



(defprojection vl-alwayslist-lint-stmt-rewrite (x)
  (vl-always-lint-stmt-rewrite x)
  :guard (vl-alwayslist-p x)
  :result-type vl-alwayslist-p)


(defsection vl-initial-lint-stmt-rewrite

  (defund vl-initial-lint-stmt-rewrite (x)
    (declare (xargs :guard (vl-initial-p x)))
    (change-vl-initial x :stmt (vl-lint-stmt-rewrite (vl-initial->stmt x))))

  (local (in-theory (enable vl-initial-lint-stmt-rewrite)))

  (defthm vl-initial-p-of-vl-initial-lint-stmt-rewrite
    (implies (force (vl-initial-p x))
             (vl-initial-p (vl-initial-lint-stmt-rewrite x)))))


(defprojection vl-initiallist-lint-stmt-rewrite (x)
  (vl-initial-lint-stmt-rewrite x)
  :guard (vl-initiallist-p x)
  :result-type vl-initiallist-p)


(defsection vl-module-lint-stmt-rewrite

  (defund vl-module-lint-stmt-rewrite (x)
    (declare (xargs :guard (and (vl-module-p x))))
    (b* (((vl-module x) x)
         ((unless (or x.alwayses x.initials))
          x)
         (alwayses (vl-alwayslist-lint-stmt-rewrite x.alwayses))
         (initials (vl-initiallist-lint-stmt-rewrite x.initials)))
      (change-vl-module x
                        :alwayses alwayses
                        :initials initials)))

  (local (in-theory (enable vl-module-lint-stmt-rewrite)))

  (defthm vl-module-p-of-vl-module-lint-stmt-rewrite
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-lint-stmt-rewrite x))))

  (defthm vl-module->name-of-vl-module-lint-stmt-rewrite
    (equal (vl-module->name (vl-module-lint-stmt-rewrite x))
           (vl-module->name x))))


(defsection vl-modulelist-lint-stmt-rewrite

  (defprojection vl-modulelist-lint-stmt-rewrite (x)
    (vl-module-lint-stmt-rewrite x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-lint-stmt-rewrite)))

  (defthm vl-modulelist->names-of-vl-modulelist-lint-stmt-rewrite
    (equal (vl-modulelist->names (vl-modulelist-lint-stmt-rewrite x))
           (vl-modulelist->names x))))

