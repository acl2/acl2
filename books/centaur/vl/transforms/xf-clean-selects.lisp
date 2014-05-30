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
(include-book "../mlib/clean-concats")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc clean-selects
  :parents (transforms)
  :short "Simplify concatenations and selects throughout a module."

  :long "<p>This is a mainly aesthetic transform that applies @(see
vl-expr-clean-selects) throughout modules.  This may help to make certain
concatenation and select expressions more readable.</p>

<p>Implementation-wise, this is the usual boilerplate to extend @(see
vl-expr-clean-selects) through the parse tree, except that we aren't going to
go through ranges: we only do this in assignments, instances, and statements,
where we expect to see wires.</p>")

(local (xdoc::set-default-parents clean-selects))

(defmacro def-vl-clean-selects (name &key type body)
  `(define ,name ((x ,type)
                  (mod vl-module-p)
                  (ialist (equal ialist (vl-moditem-alist mod))))
     :returns (new-x ,type)
     (declare (ignorable x mod ialist))
     ,body))

(defmacro def-vl-clean-selects-list (name &key type element)
  `(defprojection ,name ((x      ,type)
                         (mod    vl-module-p)
                         (ialist (equal ialist (vl-moditem-alist mod))))
     :returns (new-x ,type)
     (,element x mod ialist)))

(def-vl-clean-selects vl-maybe-expr-clean-selects
  :type vl-maybe-expr-p
  :body (and x (vl-expr-clean-selects x mod ialist)))


(def-vl-clean-selects vl-port-clean-selects
  :type vl-port-p
  :body (b* (((vl-port x) x))
          (change-vl-port x :expr (vl-maybe-expr-clean-selects x.expr mod ialist))))

(def-vl-clean-selects-list vl-portlist-clean-selects
  :type vl-portlist-p
  :element vl-port-clean-selects)


(def-vl-clean-selects vl-assign-clean-selects
  :type vl-assign-p
  :body (b* (((vl-assign x) x))
          (change-vl-assign x
                            :lvalue (vl-expr-clean-selects x.lvalue mod ialist)
                            :expr   (vl-expr-clean-selects x.expr mod ialist))))

(def-vl-clean-selects-list vl-assignlist-clean-selects
  :type vl-assignlist-p
  :element vl-assign-clean-selects)


(def-vl-clean-selects vl-plainarg-clean-selects
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x))
          (change-vl-plainarg x
                              :expr (vl-maybe-expr-clean-selects x.expr mod ialist))))

(def-vl-clean-selects-list vl-plainarglist-clean-selects
  :type vl-plainarglist-p
  :element vl-plainarg-clean-selects)

(def-vl-clean-selects vl-namedarg-clean-selects
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x))
          (change-vl-namedarg x
                              :expr (vl-maybe-expr-clean-selects x.expr mod ialist))))

(def-vl-clean-selects-list vl-namedarglist-clean-selects
  :type vl-namedarglist-p
  :element vl-namedarg-clean-selects)

(def-vl-clean-selects vl-arguments-clean-selects
  :type vl-arguments-p
  :body (vl-arguments-case x
          :named (make-vl-arguments-named :args (vl-namedarglist-clean-selects x.args mod ialist))
          :plain (make-vl-arguments-plain :args (vl-plainarglist-clean-selects x.args mod ialist))))

(def-vl-clean-selects vl-modinst-clean-selects
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x))
          (change-vl-modinst x
                             :portargs (vl-arguments-clean-selects x.portargs mod ialist))))

(def-vl-clean-selects-list vl-modinstlist-clean-selects
  :type vl-modinstlist-p
  :element vl-modinst-clean-selects)

(def-vl-clean-selects vl-gateinst-clean-selects
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x))
          (change-vl-gateinst x
                              :args (vl-plainarglist-clean-selects x.args mod ialist))))

(def-vl-clean-selects-list vl-gateinstlist-clean-selects
  :type vl-gateinstlist-p
  :element vl-gateinst-clean-selects)


(defines vl-stmt-clean-selects
  :parents (clean-selects)

  (define vl-stmt-clean-selects ((x      vl-stmt-p)
                                 (mod    vl-module-p)
                                 (ialist (equal ialist (vl-moditem-alist mod))))
    :returns (new-x vl-stmt-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))

         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             x)

            (:vl-assignstmt
             (b* (((vl-assignstmt x) x))
               (change-vl-assignstmt x
                                     :lvalue (vl-expr-clean-selects x.lvalue mod ialist)
                                     :expr (vl-expr-clean-selects x.expr mod ialist))))

            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x))
               (change-vl-deassignstmt x
                                       :lvalue (vl-expr-clean-selects x.lvalue mod ialist))))

            (:vl-enablestmt
             (b* (((vl-enablestmt x) x))
               (change-vl-enablestmt x
                                     :args (vl-exprlist-clean-selects x.args mod ialist))))

            (:vl-disablestmt
             x)

            (otherwise
             ;; event trigger statement
             x)))

         (exprs (vl-exprlist-clean-selects (vl-compoundstmt->exprs x) mod ialist))
         (stmts (vl-stmtlist-clean-selects (vl-compoundstmt->stmts x) mod ialist)))
      (change-vl-compoundstmt x :exprs exprs :stmts stmts)))

  (define vl-stmtlist-clean-selects ((x      vl-stmtlist-p)
                                     (mod    vl-module-p)
                                     (ialist (equal ialist (vl-moditem-alist mod))))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-stmtlist-count x)
    (if (consp x)
        (cons (vl-stmt-clean-selects (car x) mod ialist)
              (vl-stmtlist-clean-selects (cdr x) mod ialist))
      nil))
  ///
  (verify-guards vl-stmt-clean-selects)
  (deffixequiv-mutual vl-stmt-clean-selects)

  (defprojection vl-stmtlist-clean-selects (x mod ialist)
    (vl-stmt-clean-selects x mod ialist)
    :already-definedp t))


(def-vl-clean-selects vl-always-clean-selects
  :type vl-always-p
  :body (b* (((vl-always x) x))
          (change-vl-always x
                            :stmt (vl-stmt-clean-selects x.stmt mod ialist))))

(def-vl-clean-selects-list vl-alwayslist-clean-selects
  :type vl-alwayslist-p
  :element vl-always-clean-selects)


(def-vl-clean-selects vl-initial-clean-selects
  :type vl-initial-p
  :body (b* (((vl-initial x) x))
          (change-vl-initial x
                             :stmt (vl-stmt-clean-selects x.stmt mod ialist))))

(def-vl-clean-selects-list vl-initiallist-clean-selects
  :type vl-initiallist-p
  :element vl-initial-clean-selects)

(define vl-module-clean-selects ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       (ialist (vl-moditem-alist x))
       (ans (change-vl-module
             x
             :ports      (vl-portlist-clean-selects      x.ports      x ialist)
             :assigns    (vl-assignlist-clean-selects    x.assigns    x ialist)
             :modinsts   (vl-modinstlist-clean-selects   x.modinsts   x ialist)
             :gateinsts  (vl-gateinstlist-clean-selects  x.gateinsts  x ialist)
             :alwayses   (vl-alwayslist-clean-selects    x.alwayses   x ialist)
             :initials   (vl-initiallist-clean-selects   x.initials   x ialist))))
    (fast-alist-free ialist)
    ans))

(defprojection vl-modulelist-clean-selects ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-clean-selects x))

(define vl-design-clean-selects ((x vl-design-p))
  :short "Top-level @(see clean-selects) transform."
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-clean-selects x.mods))))

