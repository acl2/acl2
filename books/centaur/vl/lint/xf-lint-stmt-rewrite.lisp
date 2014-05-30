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
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection lint-stmt-rewrite
  :parents (lint)
  :short "(Unsound transform) eliminate @('$display') and various other
statements to cut down on noisy warnings about dropping unsupported
constructs.")

(local (xdoc::set-default-parents lint-stmt-rewrite))

(define vl-lint-throwaway-fn-p ((x vl-stmt-p))
  :returns (throwaway-p booleanp :rule-classes :type-prescription)
  (b* (((unless (vl-enablestmt-p x))
        nil)
       ((vl-enablestmt x) x)
       ((unless (vl-fast-atom-p x.id))
        nil)
       ((vl-atom x.id) x.id)
       ((unless (vl-fast-sysfunname-p x.id.guts))
        nil)
       ((vl-sysfunname x.id.guts) x.id.guts))
    (and (member-equal x.id.guts.name
                       (list "$display" "$vcover" "$verror" "$acc_readmem"))
         t)))

(defines vl-lint-stmt-rewrite
  :short "Main rewrite.  Recursively convert any throwaway statements into null
statements."

  (define vl-lint-stmt-rewrite ((x vl-stmt-p))
    :returns (new-x vl-stmt-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (if (vl-lint-throwaway-fn-p x)
              (make-vl-nullstmt)
            x))
         (sub-stmts (vl-compoundstmt->stmts x)))
      (change-vl-compoundstmt x :stmts (vl-lint-stmtlist-rewrite sub-stmts))))

  (define vl-lint-stmtlist-rewrite ((x vl-stmtlist-p))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (cons (vl-lint-stmt-rewrite (car x))
            (vl-lint-stmtlist-rewrite (cdr x)))))
  ///
  (verify-guards vl-lint-stmt-rewrite))

(define vl-always-lint-stmt-rewrite ((x vl-always-p))
  :returns (new-x vl-always-p)
  (change-vl-always x :stmt (vl-lint-stmt-rewrite (vl-always->stmt x))))

(defprojection vl-alwayslist-lint-stmt-rewrite ((x vl-alwayslist-p))
  :returns (new-x vl-alwayslist-p)
  (vl-always-lint-stmt-rewrite x))

(define vl-initial-lint-stmt-rewrite ((x vl-initial-p))
  :returns (new-x vl-initial-p)
  (change-vl-initial x :stmt (vl-lint-stmt-rewrite (vl-initial->stmt x))))

(defprojection vl-initiallist-lint-stmt-rewrite ((x vl-initiallist-p))
  :returns (new-x vl-initiallist-p)
  (vl-initial-lint-stmt-rewrite x))

(define vl-module-lint-stmt-rewrite ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((unless (or x.alwayses x.initials))
        x)
       (alwayses (vl-alwayslist-lint-stmt-rewrite x.alwayses))
       (initials (vl-initiallist-lint-stmt-rewrite x.initials)))
    (change-vl-module x
                      :alwayses alwayses
                      :initials initials)))

(defprojection vl-modulelist-lint-stmt-rewrite ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-lint-stmt-rewrite x))

(define vl-design-lint-stmt-rewrite ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-lint-stmt-rewrite x.mods))))

