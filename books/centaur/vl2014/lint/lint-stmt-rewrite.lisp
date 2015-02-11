; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
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
  (verify-guards vl-lint-stmt-rewrite
    :hints (("goal" :cases ((eq (vl-stmt-kind x) :vl-forstmt))))))

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

