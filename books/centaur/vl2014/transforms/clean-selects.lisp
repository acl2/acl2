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
                  (ss vl-scopestack-p))
     :returns (new-x ,type)
     (declare (ignorable x ss))
     ,body))

(defmacro def-vl-clean-selects-list (name &key type element)
  `(defprojection ,name ((x      ,type)
                         (ss     vl-scopestack-p))
     :returns (new-x ,type)
     (,element x ss)))

(def-vl-clean-selects vl-maybe-expr-clean-selects
  :type vl-maybe-expr-p
  :body (and x (vl-expr-clean-selects x ss)))


(def-vl-clean-selects vl-port-clean-selects
  :type vl-port-p
  :body (b* ((x (vl-port-fix x))
             ((when (eq (tag x) :vl-interfaceport)) x)
             ((vl-regularport x) x))
          (change-vl-regularport x :expr (vl-maybe-expr-clean-selects x.expr ss))))

(def-vl-clean-selects-list vl-portlist-clean-selects
  :type vl-portlist-p
  :element vl-port-clean-selects)


(def-vl-clean-selects vl-assign-clean-selects
  :type vl-assign-p
  :body (b* (((vl-assign x) x))
          (change-vl-assign x
                            :lvalue (vl-expr-clean-selects x.lvalue ss)
                            :expr   (vl-expr-clean-selects x.expr ss))))

(def-vl-clean-selects-list vl-assignlist-clean-selects
  :type vl-assignlist-p
  :element vl-assign-clean-selects)


(def-vl-clean-selects vl-plainarg-clean-selects
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x))
          (change-vl-plainarg x
                              :expr (vl-maybe-expr-clean-selects x.expr ss))))

(def-vl-clean-selects-list vl-plainarglist-clean-selects
  :type vl-plainarglist-p
  :element vl-plainarg-clean-selects)

(def-vl-clean-selects vl-namedarg-clean-selects
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x))
          (change-vl-namedarg x
                              :expr (vl-maybe-expr-clean-selects x.expr ss))))

(def-vl-clean-selects-list vl-namedarglist-clean-selects
  :type vl-namedarglist-p
  :element vl-namedarg-clean-selects)

(def-vl-clean-selects vl-arguments-clean-selects
  :type vl-arguments-p
  :body (vl-arguments-case x
          :vl-arguments-named
          (change-vl-arguments-named x :args (vl-namedarglist-clean-selects x.args ss))
          :vl-arguments-plain
          (change-vl-arguments-plain x :args (vl-plainarglist-clean-selects x.args ss))))

(def-vl-clean-selects vl-modinst-clean-selects
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x))
          (change-vl-modinst x
                             :portargs (vl-arguments-clean-selects x.portargs ss))))

(def-vl-clean-selects-list vl-modinstlist-clean-selects
  :type vl-modinstlist-p
  :element vl-modinst-clean-selects)

(def-vl-clean-selects vl-gateinst-clean-selects
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x))
          (change-vl-gateinst x
                              :args (vl-plainarglist-clean-selects x.args ss))))

(def-vl-clean-selects-list vl-gateinstlist-clean-selects
  :type vl-gateinstlist-p
  :element vl-gateinst-clean-selects)


(defines vl-stmt-clean-selects
  :parents (clean-selects)

  (define vl-stmt-clean-selects ((x      vl-stmt-p)
                                 (ss     vl-scopestack-p))
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
                                     :lvalue (vl-expr-clean-selects x.lvalue ss)
                                     :expr (vl-expr-clean-selects x.expr ss))))

            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x))
               (change-vl-deassignstmt x
                                       :lvalue (vl-expr-clean-selects x.lvalue ss))))

            (:vl-enablestmt
             (b* (((vl-enablestmt x) x))
               (change-vl-enablestmt x
                                     :args (vl-exprlist-clean-selects x.args ss))))

            (:vl-disablestmt
             x)

            (:vl-returnstmt
             (b* (((vl-returnstmt x)))
               (if x.val
                   (change-vl-returnstmt x :val (vl-expr-clean-selects x.val ss))
                 x)))

            (otherwise
             ;; event trigger statement
             x)))

         (exprs (vl-exprlist-clean-selects (vl-compoundstmt->exprs x) ss))
         (stmts (vl-stmtlist-clean-selects (vl-compoundstmt->stmts x) ss)))
      (change-vl-compoundstmt x :exprs exprs :stmts stmts)))

  (define vl-stmtlist-clean-selects ((x      vl-stmtlist-p)
                                     (ss     vl-scopestack-p))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-stmtlist-count x)
    (if (consp x)
        (cons (vl-stmt-clean-selects (car x) ss)
              (vl-stmtlist-clean-selects (cdr x) ss))
      nil))
  ///
  (verify-guards vl-stmt-clean-selects)
  (deffixequiv-mutual vl-stmt-clean-selects)

  (defprojection vl-stmtlist-clean-selects (x ss)
    (vl-stmt-clean-selects x ss)
    :already-definedp t))


(def-vl-clean-selects vl-always-clean-selects
  :type vl-always-p
  :body (b* (((vl-always x) x))
          (change-vl-always x
                            :stmt (vl-stmt-clean-selects x.stmt ss))))

(def-vl-clean-selects-list vl-alwayslist-clean-selects
  :type vl-alwayslist-p
  :element vl-always-clean-selects)


(def-vl-clean-selects vl-initial-clean-selects
  :type vl-initial-p
  :body (b* (((vl-initial x) x))
          (change-vl-initial x
                             :stmt (vl-stmt-clean-selects x.stmt ss))))

(def-vl-clean-selects-list vl-initiallist-clean-selects
  :type vl-initiallist-p
  :element vl-initial-clean-selects)

(define vl-module-clean-selects ((x vl-module-p) (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       (ss (vl-scopestack-push x ss))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       (ans (change-vl-module
             x
             :ports      (vl-portlist-clean-selects      x.ports      ss)
             :assigns    (vl-assignlist-clean-selects    x.assigns    ss)
             :modinsts   (vl-modinstlist-clean-selects   x.modinsts   ss)
             :gateinsts  (vl-gateinstlist-clean-selects  x.gateinsts  ss)
             :alwayses   (vl-alwayslist-clean-selects    x.alwayses   ss)
             :initials   (vl-initiallist-clean-selects   x.initials   ss))))
    ans))

(defprojection vl-modulelist-clean-selects ((x vl-modulelist-p) (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-clean-selects x ss))

(define vl-design-clean-selects ((x vl-design-p))
  :short "Top-level @(see clean-selects) transform."
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-clean-selects x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))

