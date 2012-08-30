; VL Verilog Toolkit
; Copyright (C) 2008-2012 Centaur Technology
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
(local (include-book "../util/arithmetic"))


(defxdoc clean-selects
  :parents (transforms)
  :short "Simplify concatenations and selects throughout a module."

  :long "<p>This is a mainly aesthetic transform that applies @(see
vl-expr-clean-selects) throughout modules.  This may help to make certain
concatenation and select expressions more readable.</p>")

; This is the usual boilerplate to extend vl-expr-clean-selects through the
; parse tree, except that we aren't going to go through ranges: we only do this
; in assignments, instances, and statements, where we expect to see wires.

(defmacro def-vl-clean-selects (name &key type body)
  `(defsection ,name
     :parents (clean-selects)

     (defund ,name (x mod ialist)
       (declare (xargs :guard (and (,type x)
                                   (vl-module-p mod)
                                   (equal ialist (vl-moditem-alist mod))))
                (ignorable x mod ialist))
       ,body)

     (local (in-theory (enable ,name)))

     (defthm ,(intern-in-package-of-symbol
               (cat (symbol-name type) "-OF-" (symbol-name name))
               name)
       (implies (and (force (,type x))
                     (force (vl-module-p mod))
                     (force (equal ialist (vl-moditem-alist mod))))
                (,type (,name x mod ialist))))))

(defmacro def-vl-clean-selects-list (name &key type element)

  `(encapsulate
     ()
     (defprojection ,name (x mod ialist)
       (,element x mod ialist)
       :guard (and (,type x)
                   (vl-module-p mod)
                   (equal ialist (vl-moditem-alist mod)))
       :parents (clean-selects)
       :nil-preservingp nil)

    (defthm ,(intern-in-package-of-symbol
              (cat (symbol-name type) "-OF-" (symbol-name name))
              name)
      (implies (and (force (,type x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (,type (,name x mod ialist)))
      :hints(("Goal" :induct (len x))))))

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
  :body (vl-arguments
         (vl-arguments->namedp x)
         (if (vl-arguments->namedp x)
             (vl-namedarglist-clean-selects (vl-arguments->args x) mod ialist)
           (vl-plainarglist-clean-selects (vl-arguments->args x) mod ialist))))

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



(def-vl-clean-selects vl-nullstmt-clean-selects
  :type vl-nullstmt-p
  :body x)

(def-vl-clean-selects vl-assignstmt-clean-selects
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x))
          (change-vl-assignstmt x
                                :lvalue (vl-expr-clean-selects x.lvalue mod ialist)
                                :expr (vl-expr-clean-selects x.expr mod ialist))))

(def-vl-clean-selects vl-deassignstmt-clean-selects
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x))
          (change-vl-deassignstmt x
                                  :lvalue (vl-expr-clean-selects x.lvalue mod ialist))))

(def-vl-clean-selects vl-enablestmt-clean-selects
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x))
          (change-vl-enablestmt x
                                :args (vl-exprlist-clean-selects x.args mod ialist))))

(def-vl-clean-selects vl-disablestmt-clean-selects
  :type vl-disablestmt-p
  :body x)

(def-vl-clean-selects vl-eventtriggerstmt-clean-selects
  :type vl-eventtriggerstmt-p
  :body x)

(def-vl-clean-selects vl-atomicstmt-clean-selects
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-clean-selects x mod ialist))
          (:vl-assignstmt       (vl-assignstmt-clean-selects x mod ialist))
          (:vl-deassignstmt     (vl-deassignstmt-clean-selects x mod ialist))
          (:vl-enablestmt       (vl-enablestmt-clean-selects x mod ialist))
          (:vl-disablestmt      (vl-disablestmt-clean-selects x mod ialist))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-clean-selects x mod ialist))))


(defsection vl-stmt-clean-selects

  (mutual-recursion

   (defund vl-stmt-clean-selects (x mod ialist)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (vl-atomicstmt-clean-selects x mod ialist))
          ((vl-compoundstmt x) x))
       (change-vl-compoundstmt x
                               :exprs (vl-exprlist-clean-selects x.exprs mod ialist)
                               :stmts (vl-stmtlist-clean-selects x.stmts mod ialist))))

   (defund vl-stmtlist-clean-selects (x mod ialist)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (cons (vl-stmt-clean-selects (car x) mod ialist)
               (vl-stmtlist-clean-selects (cdr x) mod ialist))
       nil)))

  (defthm vl-stmtlist-clean-selects-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-clean-selects x mod ialist)
                    nil))
    :hints(("Goal" :in-theory (enable vl-stmtlist-clean-selects))))

  (defthm vl-stmtlist-clean-selects-of-cons
    (equal (vl-stmtlist-clean-selects (cons a x) mod ialist)
           (cons (vl-stmt-clean-selects a mod ialist)
                 (vl-stmtlist-clean-selects x mod ialist)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-clean-selects))))

  (defprojection vl-stmtlist-clean-selects (x mod ialist)
    (vl-stmt-clean-selects x mod ialist)
    :already-definedp t)

  (local (defthm lemma
           (implies (and (not (vl-atomicstmt-p x))
                         (vl-stmtlist-p (vl-stmtlist-clean-selects (vl-compoundstmt->stmts x) mod ialist))
                         (vl-stmt-p x)
                         (vl-module-p mod)
                         (equal ialist (vl-moditem-alist mod)))
                    (vl-compoundstmt-basic-checksp
                     (vl-compoundstmt->type x)
                     (vl-exprlist-clean-selects (vl-compoundstmt->exprs x) mod ialist)
                     (vl-stmtlist-clean-selects (vl-compoundstmt->stmts x) mod ialist)
                     (vl-compoundstmt->name x)
                     (vl-compoundstmt->decls x)
                     (vl-compoundstmt->ctrl x)
                     (vl-compoundstmt->sequentialp x)
                     (vl-compoundstmt->casetype x)))
           :hints(("goal"
                   :in-theory (e/d (vl-compoundstmt-basic-checksp)
                                   (vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
                   :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))))))

  (defthm-vl-flag-stmt-p vl-stmt-p-of-vl-stmt-clean-selects
    (stmt (implies (and (force (vl-stmt-p x))
                        (force (vl-module-p mod))
                        (force (equal ialist (vl-moditem-alist mod))))
                   (vl-stmt-p (vl-stmt-clean-selects x mod ialist))))
    (list (implies (and (force (vl-stmtlist-p x))
                        (force (vl-module-p mod))
                        (force (equal ialist (vl-moditem-alist mod))))
                   (vl-stmtlist-p (vl-stmtlist-clean-selects x mod ialist))))
    :hints(("Goal"
            :induct (vl-flag-stmt-p flag x)
            :expand ((vl-stmt-clean-selects x mod ialist)))))

  (verify-guards vl-stmt-clean-selects))

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


(defsection vl-module-clean-selects
  :parents (clean-selects)

  (defund vl-module-clean-selects (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
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

  (local (in-theory (enable vl-module-clean-selects)))

  (defthm vl-module-p-of-vl-module-clean-selects
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-clean-selects x))))

  (defthm vl-module->name-of-vl-module-clean-selects
    (equal (vl-module->name (vl-module-clean-selects x))
           (vl-module->name x))))


(defprojection vl-modulelist-clean-selects (x)
  (vl-module-clean-selects x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (clean-selects))

(defthm vl-modulelist->names-of-vl-modulelist-clean-selects
  (equal (vl-modulelist->names (vl-modulelist-clean-selects x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))

