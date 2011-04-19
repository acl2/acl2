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
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc allexprs
  :parents (mlib)
  :short "Functions for gathering all the expressions used throughout some
module item."

  :long "<p>These functions gather up what we regard as the \"top level\"
expressions used throughout various module items.  That is, consider an
assignment statement such as <tt>foo = a + b</tt>; the associated list of
allexprs would include two expressions: one for <tt>foo</tt>, and one for <tt>a
+ b</tt>.</p>

<p>Note that despite the name \"allexprs\", we actually do not gather
expressions within <tt>(* foo = bar *)</tt>-style attributes.</p>")

(defmacro def-vl-allexprs (&key type
                                exec-body
                                body)

  (let* ((mksym-package-symbol 'vl)

         (rec            (mksym type '-p))
         (collect-exec   (mksym type '-allexprs-exec))
         (collect        (mksym type '-allexprs))
         (remove-thm     (mksym collect-exec '-removal))
         (true-list-thm  (mksym 'true-listp-of- collect))
         (type-thm       (mksym 'vl-exprlist-p-of- collect))

         (rec-s           (symbol-name rec))
         (collect-s       (symbol-name collect))

         (short          (str::cat
"Gather all top-level expressions from a @(see " rec-s ")."))
         (long           (str::cat
"<p><b>Signature</b> @(call " collect-s ") returns a @(see vl-exprlist-p).</p>

<p>We return a list of all the top-level expressions used throughout a @(see "
rec-s "), as described in @(see allexprs).</p>

<p>For efficiency we use a tail-recursive, accumulator-style functions to do
the collection.  Under the hood, we also use <tt>nreverse</tt>
optimization.</p>")))

    `(defsection ,collect
       :parents (,rec allexprs)
       :short ,short
       :long ,long

       (definlined ,collect-exec (x acc)
         (declare (xargs :guard (,rec x)))
         ,exec-body)

       (defund ,collect (x)
         (declare (xargs :guard (,rec x)
                         :verify-guards nil))
         (mbe :logic ,body
              :exec (reverse (,collect-exec x nil))))

       (local (in-theory (enable ,collect-exec ,collect)))

       (defthm ,remove-thm
         (equal (,collect-exec x acc)
                (append (rev (,collect x))
                        acc)))

       (verify-guards ,collect)

       (defthm ,true-list-thm
         (true-listp (,collect x))
         :rule-classes :type-prescription)

       (defthm ,type-thm
         (implies (force (,rec x))
                  (vl-exprlist-p (,collect x))))

       (defttag vl-optimize)
       (progn!
        (set-raw-mode t)
        (setf (gethash ',collect-exec ACL2::*never-profile-ht*) t)
        (defun ,collect (x)
          (nreverse (,collect-exec x nil))))
       (defttag nil))))


(defmacro def-vl-allexprs-list (&key list element)
  (let* ((mksym-package-symbol 'vl)

         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-allexprs))
         (element-collect      (mksym element '-allexprs))
         (element-collect-exec (mksym element '-allexprs-exec))
         (type-thm             (mksym 'vl-exprlist-p-of- list-collect))

         (list-rec-s          (symbol-name list-rec))
         (list-collect-s      (symbol-name list-collect))

         (short          (str::cat
"Gather all top-level expressions from a @(see " list-rec-s ")."))
         (long           (str::cat
"<p><b>Signature</b> @(call " list-collect-s ") returns a @(see vl-exprlist-p).</p>

<p>We return a list of all the top-level expressions used throughout a @(see "
list-rec-s "), as described in @(see allexprs).</p>")))

    `(defsection ,list-collect
       :parents (,list-rec allexprs)
       :short ,short
       :long ,long

       (defmapappend ,list-collect (x)
         (,element-collect x)
         :guard (,list-rec x)
         :transform-true-list-p t
         :transform-exec ,element-collect-exec)

       (local (in-theory (enable ,list-collect)))

       (defthm ,type-thm
         (implies (force (,list-rec x))
                  (vl-exprlist-p (,list-collect x)))))))

(def-vl-allexprs
  :type vl-maybe-expr
  :exec-body (if x (cons x acc) acc)
  :body (if x (list x) nil))

(def-vl-allexprs
  :type vl-plainarg
  :exec-body (vl-maybe-expr-allexprs-exec (vl-plainarg->expr x) acc)
  :body (vl-maybe-expr-allexprs (vl-plainarg->expr x)))

(def-vl-allexprs-list
  :list vl-plainarglist
  :element vl-plainarg)

(def-vl-allexprs
  :type vl-namedarg
  :exec-body (vl-maybe-expr-allexprs-exec (vl-namedarg->expr x) acc)
  :body (vl-maybe-expr-allexprs (vl-namedarg->expr x)))

(def-vl-allexprs-list
  :list vl-namedarglist
  :element vl-namedarg)

(def-vl-allexprs
  :type vl-arguments
  :exec-body
  (b* (((vl-arguments x) x))
      (if x.namedp
          (vl-namedarglist-allexprs-exec x.args acc)
        (vl-plainarglist-allexprs-exec x.args acc)))
  :body
  (b* (((vl-arguments x) x))
      (if x.namedp
          (vl-namedarglist-allexprs x.args)
        (vl-plainarglist-allexprs x.args))))

(def-vl-allexprs
  :type vl-range
  :exec-body
  (b* (((vl-range x) x))
      (list* x.right x.left acc))
  :body
  (b* (((vl-range x) x))
      (list x.left x.right)))

(def-vl-allexprs
  :type vl-maybe-range
  :exec-body (if x (vl-range-allexprs-exec x acc) acc)
  :body (if x (vl-range-allexprs x) nil))

(def-vl-allexprs-list
  :list vl-rangelist
  :element vl-range)

(def-vl-allexprs
  :type vl-gatedelay
  :exec-body
  (b* (((vl-gatedelay x) x))
      (vl-maybe-expr-allexprs-exec x.high (list* x.fall x.rise acc)))
  :body
  (b* (((vl-gatedelay x) x))
      (list* x.rise x.fall (vl-maybe-expr-allexprs x.high))))

(def-vl-allexprs
  :type vl-maybe-gatedelay
  :exec-body (if x (vl-gatedelay-allexprs-exec x acc) acc)
  :body (if x (vl-gatedelay-allexprs x) nil))

(def-vl-allexprs
  :type vl-assign
  :exec-body
  (b* (((vl-assign x) x))
      (vl-maybe-gatedelay-allexprs-exec x.delay (list* x.lvalue x.expr acc)))
  :body
  (b* (((vl-assign x) x))
      (list* x.expr x.lvalue (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-assignlist
  :element vl-assign)

(def-vl-allexprs
  :type vl-gateinst
  :exec-body
  (b* (((vl-gateinst x) x)
       (acc (vl-maybe-range-allexprs-exec x.range acc))
       (acc (vl-plainarglist-allexprs-exec x.args acc)))
      (vl-maybe-gatedelay-allexprs-exec x.delay acc))
  :body
  (b* (((vl-gateinst x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-plainarglist-allexprs x.args)
              (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-gateinstlist
  :element vl-gateinst)

(def-vl-allexprs
  :type vl-modinst
  :exec-body
  (b* (((vl-modinst x) x)
       (acc (vl-maybe-range-allexprs-exec x.range acc))
       (acc (vl-arguments-allexprs-exec x.paramargs acc))
       (acc (vl-arguments-allexprs-exec x.portargs acc)))
      (vl-maybe-gatedelay-allexprs-exec x.delay acc))
  :body
  (b* (((vl-modinst x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-arguments-allexprs x.paramargs)
              (vl-arguments-allexprs x.portargs)
              (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-allexprs
  :type vl-netdecl
  :exec-body
  (b* (((vl-netdecl x) x)
       (acc (vl-maybe-range-allexprs-exec x.range acc))
       (acc (vl-rangelist-allexprs-exec x.arrdims acc)))
      (vl-maybe-gatedelay-allexprs-exec x.delay acc))
  :body
  (b* (((vl-netdecl x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-rangelist-allexprs x.arrdims)
              (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-netdecllist
  :element vl-netdecl)

(def-vl-allexprs
  :type vl-vardecl
  :exec-body
  (b* (((vl-vardecl x) x)
       (acc (vl-rangelist-allexprs-exec x.arrdims acc)))
    (vl-maybe-expr-allexprs-exec x.initval acc))
  :body
  (b* (((vl-vardecl x) x))
      (append (vl-rangelist-allexprs x.arrdims)
              (vl-maybe-expr-allexprs x.initval))))

(def-vl-allexprs-list
  :list vl-vardecllist
  :element vl-vardecl)

(def-vl-allexprs
  :type vl-regdecl
  :exec-body
  (b* (((vl-regdecl x) x)
       (acc (vl-maybe-range-allexprs-exec x.range acc))
       (acc (vl-rangelist-allexprs-exec x.arrdims acc)))
    (vl-maybe-expr-allexprs-exec x.initval acc))
  :body
  (b* (((vl-regdecl x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-rangelist-allexprs x.arrdims)
              (vl-maybe-expr-allexprs x.initval))))

(def-vl-allexprs-list
  :list vl-regdecllist
  :element vl-regdecl)

(def-vl-allexprs
  :type vl-eventdecl
  :exec-body (vl-rangelist-allexprs-exec (vl-eventdecl->arrdims x) acc)
  :body (vl-rangelist-allexprs (vl-eventdecl->arrdims x)))

(def-vl-allexprs-list
  :list vl-eventdecllist
  :element vl-eventdecl)

(def-vl-allexprs
  :type vl-portdecl
  :exec-body (vl-maybe-range-allexprs-exec (vl-portdecl->range x) acc)
  :body (vl-maybe-range-allexprs (vl-portdecl->range x)))

(def-vl-allexprs-list
  :list vl-portdecllist
  :element vl-portdecl)

(def-vl-allexprs
  :type vl-paramdecl
  :exec-body
  (b* (((vl-paramdecl x) x))
      (vl-maybe-range-allexprs-exec x.range (cons x.expr acc)))
  :body
  (b* (((vl-paramdecl x) x))
      (cons x.expr (vl-maybe-range-allexprs x.range))))

(def-vl-allexprs-list
  :list vl-paramdecllist
  :element vl-paramdecl)

(def-vl-allexprs
  :type vl-delaycontrol
  :exec-body (cons (vl-delaycontrol->value x) acc)
  :body (list (vl-delaycontrol->value x)))

(def-vl-allexprs
  :type :vl-evatom
  :exec-body (cons (vl-evatom->expr x) acc)
  :body (list (vl-evatom->expr x)))

(def-vl-allexprs-list
  :list vl-evatomlist
  :element vl-evatom)

(def-vl-allexprs
  :type vl-eventcontrol
  :exec-body (vl-evatomlist-allexprs-exec (vl-eventcontrol->atoms x) acc)
  :body (vl-evatomlist-allexprs (vl-eventcontrol->atoms x)))

(def-vl-allexprs
  :type vl-repeateventcontrol
  :exec-body
  (b* (((vl-repeateventcontrol x) x))
      (vl-eventcontrol-allexprs-exec x.ctrl (cons x.expr acc)))
  :body
  (b* (((vl-repeateventcontrol x) x))
      (cons x.expr (vl-eventcontrol-allexprs x.ctrl))))

(def-vl-allexprs
  :type vl-delayoreventcontrol
  :exec-body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-allexprs-exec x acc))
    (:vl-eventcontrol (vl-eventcontrol-allexprs-exec x acc))
    (:vl-repeat-eventcontrol (vl-repeateventcontrol-allexprs-exec x acc))
    (otherwise
     (prog2$ (er hard 'vl-delayoreventcontrol-allexprs-exec "Provably impossible.")
             acc)))
  :body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-allexprs x))
    (:vl-eventcontrol (vl-eventcontrol-allexprs x))
    (:vl-repeat-eventcontrol (vl-repeateventcontrol-allexprs x))))

(def-vl-allexprs
  :type vl-maybe-delayoreventcontrol
  :exec-body (if x (vl-delayoreventcontrol-allexprs-exec x acc) acc)
  :body (if x (vl-delayoreventcontrol-allexprs x) nil))

(def-vl-allexprs
  :type vl-assignstmt
  :exec-body
  (b* (((vl-assignstmt x) x))
      (vl-maybe-delayoreventcontrol-allexprs-exec x.ctrl
                                                  (list* x.expr x.lvalue acc)))
  :body
  (b* (((vl-assignstmt x) x))
      (list* x.lvalue
             x.expr
             (vl-maybe-delayoreventcontrol-allexprs x.ctrl))))

(def-vl-allexprs
  :type vl-deassignstmt
  :exec-body (cons (vl-deassignstmt->lvalue x) acc)
  :body (list (vl-deassignstmt->lvalue x)))

(def-vl-allexprs
  :type vl-enablestmt
  :exec-body
  (b* (((vl-enablestmt x) x))
      (revappend-without-guard x.args (cons x.id acc)))
  :body
  (b* (((vl-enablestmt x) x))
      (cons x.id (list-fix x.args))))

(def-vl-allexprs
  :type vl-disablestmt
  :exec-body (cons (vl-disablestmt->id x) acc)
  :body (list (vl-disablestmt->id x)))

(def-vl-allexprs
  :type vl-eventtriggerstmt
  :exec-body (cons (vl-eventtriggerstmt->id x) acc)
  :body (list (vl-eventtriggerstmt->id x)))

(def-vl-allexprs
  :type vl-atomicstmt
  :exec-body
  (case (tag x)
    (:vl-nullstmt         acc)
    (:vl-assignstmt       (vl-assignstmt-allexprs-exec x acc))
    (:vl-deassignstmt     (vl-deassignstmt-allexprs-exec x acc))
    (:vl-enablestmt       (vl-enablestmt-allexprs-exec x acc))
    (:vl-disablestmt      (vl-disablestmt-allexprs-exec x acc))
    (:vl-eventtriggerstmt (vl-eventtriggerstmt-allexprs-exec x acc))
    (otherwise
     (prog2$ (er hard 'vl-atomicstmt-allexprs-exec "Provably impossible.")
             acc)))
  :body
  (case (tag x)
    (:vl-nullstmt         nil)
    (:vl-assignstmt       (vl-assignstmt-allexprs x))
    (:vl-deassignstmt     (vl-deassignstmt-allexprs x))
    (:vl-enablestmt       (vl-enablestmt-allexprs x))
    (:vl-disablestmt      (vl-disablestmt-allexprs x))
    (:vl-eventtriggerstmt (vl-eventtriggerstmt-allexprs x))))

(def-vl-allexprs
  :type vl-blockitem
  :exec-body
  (case (tag x)
    (:vl-regdecl   (vl-regdecl-allexprs-exec x acc))
    (:vl-vardecl   (vl-vardecl-allexprs-exec x acc))
    (:vl-eventdecl (vl-eventdecl-allexprs-exec x acc))
    (:vl-paramdecl (vl-paramdecl-allexprs-exec x acc))
    (otherwise
     (prog2$ (er hard 'vl-blockitem-allexprs-exec "Provably impossible.")
             acc)))
  :body
  (case (tag x)
    (:vl-regdecl   (vl-regdecl-allexprs x))
    (:vl-vardecl   (vl-vardecl-allexprs x))
    (:vl-eventdecl (vl-eventdecl-allexprs x))
    (:vl-paramdecl (vl-paramdecl-allexprs x))))

(def-vl-allexprs-list
  :list vl-blockitemlist
  :element vl-blockitem)


(defsection vl-stmt-allexprs
  :parents (allexprs vl-stmt-p)
  :short "Gather all top-level expressions from a @(see vl-stmt-p)."

  :long "<p><b>Signature</b> @(call vl-stmt-allexprs) returns a @(see
vl-exprlist-p).</p>

<p>We return a list of all the top-level expressions used throughout a
@(see vl-stmt-p), as described in @(see allexprs).</p>

<p>For efficiency we use a tail-recursive, accumulator-style functions to do
the collection.  Under the hood, we also use <tt>nreverse</tt>
optimization.</p>"

  (mutual-recursion

   (defund vl-stmt-allexprs-exec (x acc)
     (declare (xargs :guard (vl-stmt-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-allexprs-exec x acc)
       (b* (((vl-compoundstmt x) x)
            (acc (revappend-without-guard x.exprs acc))
            (acc (vl-blockitemlist-allexprs-exec x.decls acc))
            (acc (vl-maybe-delayoreventcontrol-allexprs-exec x.ctrl acc)))
           (vl-stmtlist-allexprs-exec x.stmts acc))))

   (defund vl-stmtlist-allexprs-exec (x acc)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         acc
       (let ((acc (vl-stmt-allexprs-exec (car x) acc)))
         (vl-stmtlist-allexprs-exec (cdr x) acc)))))

  (mutual-recursion

   (defund vl-stmt-allexprs (x)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (mbe :logic
          (if (vl-atomicstmt-p x)
              (vl-atomicstmt-allexprs x)
            (b* (((vl-compoundstmt x) x))
                (append x.exprs
                        (vl-blockitemlist-allexprs x.decls)
                        (vl-maybe-delayoreventcontrol-allexprs x.ctrl)
                        (vl-stmtlist-allexprs x.stmts))))
          :exec
          (reverse (vl-stmt-allexprs-exec x nil))))

   (defund vl-stmtlist-allexprs (x)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (atom x)
              nil
            (append (vl-stmt-allexprs (car x))
                    (vl-stmtlist-allexprs (cdr x))))
          :exec
          (reverse (vl-stmtlist-allexprs-exec x nil)))))

  (flag::make-flag vl-flag-stmt-allexprs-exec
                   vl-stmt-allexprs-exec
                   :flag-mapping ((vl-stmt-allexprs-exec . stmt)
                                  (vl-stmtlist-allexprs-exec . list)))

  (defthm-vl-flag-stmt-allexprs-exec lemma
    (stmt (equal (vl-stmt-allexprs-exec x acc)
                 (revappend (vl-stmt-allexprs x) acc))
          :name vl-stmt-allexprs-exec-removal)
    (list (equal (vl-stmtlist-allexprs-exec x acc)
                 (revappend (vl-stmtlist-allexprs x) acc))
          :name vl-stmtlist-allexprs-exec-removal)
    :hints(("Goal"
            :induct (vl-flag-stmt-allexprs-exec flag x acc)
            :expand ((vl-stmt-allexprs x)
                     (vl-stmtlist-allexprs x)
                     (vl-stmt-allexprs-exec x acc)
                     (vl-stmtlist-allexprs-exec x acc)))))

  (verify-guards vl-stmt-allexprs
                 :hints(("Goal" :in-theory (enable vl-stmt-allexprs
                                                   vl-stmtlist-allexprs))))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-stmt-allexprs-exec ACL2::*never-profile-ht*) t)
   (setf (gethash 'vl-stmtlist-allexprs-exec ACL2::*never-profile-ht*) t)
   (defun vl-stmt-allexprs (x)
     (nreverse (vl-stmt-allexprs-exec x nil)))
   (defun vl-stmtlist-allexprs (x)
     (nreverse (vl-stmtlist-allexprs-exec x nil))))
  (defttag nil)

  (defthm-vl-flag-stmt-p lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-exprlist-p (vl-stmt-allexprs x)))
          :name vl-exprlist-p-of-vl-stmt-allexprs)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-exprlist-p (vl-stmtlist-allexprs x)))
          :name vl-exprlist-p-of-vl-stmtlist-allexprs)
    :hints(("Goal"
            :induct (vl-flag-stmt-p flag x)
            :expand ((vl-stmt-allexprs x)
                     (vl-stmtlist-allexprs x))))))

(def-vl-allexprs
  :type vl-initial
  :exec-body (vl-stmt-allexprs-exec (vl-initial->stmt x) acc)
  :body (vl-stmt-allexprs (vl-initial->stmt x)))

(def-vl-allexprs-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-allexprs
  :type vl-always
  :exec-body (vl-stmt-allexprs-exec (vl-always->stmt x) acc)
  :body (vl-stmt-allexprs (vl-always->stmt x)))

(def-vl-allexprs-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-allexprs
  :type :vl-port
  :exec-body (vl-maybe-expr-allexprs-exec (vl-port->expr x) acc)
  :body (vl-maybe-expr-allexprs (vl-port->expr x)))

(def-vl-allexprs-list
  :list vl-portlist
  :element vl-port)

(def-vl-allexprs
  :type vl-module
  :exec-body
  (b* (((vl-module x) x)
       ;; bozo add support for params eventually
       (acc (vl-portlist-allexprs-exec x.ports acc))
       (acc (vl-portdecllist-allexprs-exec x.portdecls acc))
       (acc (vl-assignlist-allexprs-exec x.assigns acc))
       (acc (vl-netdecllist-allexprs-exec x.netdecls acc))
       (acc (vl-vardecllist-allexprs-exec x.vardecls acc))
       (acc (vl-regdecllist-allexprs-exec x.regdecls acc))
       (acc (vl-eventdecllist-allexprs-exec x.eventdecls acc))
       (acc (vl-paramdecllist-allexprs-exec x.paramdecls acc))
       (acc (vl-modinstlist-allexprs-exec x.modinsts acc))
       (acc (vl-gateinstlist-allexprs-exec x.gateinsts acc))
       (acc (vl-alwayslist-allexprs-exec x.alwayses acc))
       (acc (vl-initiallist-allexprs-exec x.initials acc)))
      acc)
  :body
  (b* (((vl-module x) x))
      (append (vl-portlist-allexprs x.ports)
              (vl-portdecllist-allexprs x.portdecls)
              (vl-assignlist-allexprs x.assigns)
              (vl-netdecllist-allexprs x.netdecls)
              (vl-vardecllist-allexprs x.vardecls)
              (vl-regdecllist-allexprs x.regdecls)
              (vl-eventdecllist-allexprs x.eventdecls)
              (vl-paramdecllist-allexprs x.paramdecls)
              (vl-modinstlist-allexprs x.modinsts)
              (vl-gateinstlist-allexprs x.gateinsts)
              (vl-alwayslist-allexprs x.alwayses)
              (vl-initiallist-allexprs x.initials))))

(def-vl-allexprs-list
  :list vl-modulelist
  :element vl-module)


(defsection vl-module-exprnames-set

  (local (defthm vl-exprlist-names-of-append
           (equal (vl-exprlist-names (append x y))
                  (append (vl-exprlist-names x)
                          (vl-exprlist-names y)))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (enable vl-exprlist-names)))))

  (local (defthm lemma1
           (implies (member-equal a (vl-exprlist-names x))
                    (member-equal a (vl-exprlist-names (append x y))))
           :hints(("Goal"
                   :in-theory (enable vl-exprlist-names)
                   :induct (len x)))))

  (local (defthm lemma2
           (iff (member-equal a (vl-exprlist-names (rev x)))
                (member-equal a (vl-exprlist-names x)))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (enable vl-exprlist-names)))))

  (defun vl-module-exprnames-set (x)
    (declare (xargs :guard (vl-module-p x)))
    (mbe :logic (mergesort (vl-exprlist-names (vl-module-allexprs x)))
         :exec
         (let* ((exprs (vl-module-allexprs-exec x nil))
                (names (vl-exprlist-names-exec exprs nil)))
           (mergesort names)))))