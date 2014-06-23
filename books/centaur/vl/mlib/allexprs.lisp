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
(include-book "../parsetree")
(include-book "expr-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))


(defxdoc allexprs
  :parents (mlib)
  :short "Functions for gathering all the expressions used throughout some
module item."

  :long "<p>These functions gather up what we regard as the \"top level\"
expressions used throughout various module items.  That is, consider an
assignment statement such as @('foo = a + b'); the associated list of allexprs
would include two expressions: one for @('foo'), and one for @('a + b').</p>

<p>Note that despite the name \"allexprs\", we actually do not gather
expressions within @('(* foo = bar *)')-style attributes.</p>")

(defmacro def-vl-allexprs (&key type
                                nrev-body
                                body)

  (let* ((mksym-package-symbol 'vl::foo)
         (rec            (mksym type '-p))
         (fix            (mksym type '-fix))
         (collect-nrev   (mksym type '-allexprs-nrev))
         (collect        (mksym type '-allexprs))
         (short          (cat "Gather all top-level expressions from a @(see "
                              (symbol-name rec) ").")))

    `(progn

       (define ,collect-nrev ((x ,rec)
                              (nrev))
         :parents (,collect)
         :inline t
         (b* ((x (,fix x)))
           ,nrev-body))

       (define ,collect ((x ,rec))
         :returns (exprs vl-exprlist-p)
         :parents (allexprs)
         :short ,short
         :verify-guards nil
         (mbe :logic (b* ((x (,fix x)))
                       ,body)
              :exec (with-local-nrev (,collect-nrev x nrev)))
         ///
         (defthm ,(mksym 'true-listp-of- collect)
           (true-listp (,collect x))
           :rule-classes :type-prescription)

         (defthm ,(mksym collect-nrev '-removal)
           (equal (,collect-nrev x nrev)
                  (append nrev (,collect x)))
           :hints(("Goal" :in-theory (enable acl2::rcons
                                             ,collect-nrev))))

         (verify-guards ,collect)))))


(defmacro def-vl-allexprs-list (&key list element)
  (let* ((mksym-package-symbol 'vl::foo)
         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-allexprs))
         (list-collect-nrev    (mksym list '-allexprs-nrev))
         (element-collect      (mksym element '-allexprs))
         (element-collect-nrev (mksym element '-allexprs-nrev))
         (short                (cat "Gather all top-level expressions from a @(see "
                                    (symbol-name list-rec) ").")))
    `(progn
       (define ,list-collect-nrev ((x ,list-rec) nrev)
         :parents (,list-collect)
         (if (atom x)
             (nrev-fix nrev)
           (let ((nrev (,element-collect-nrev (car x) nrev)))
             (,list-collect-nrev (cdr x) nrev))))

       (define ,list-collect ((x ,list-rec))
         :returns (exprs vl-exprlist-p)
         :parents (allexprs)
         :short ,short
         :verify-guards nil
         (mbe :logic (if (atom x)
                         nil
                       (append (,element-collect (car x))
                               (,list-collect (cdr x))))
              :exec (with-local-nrev
                      (,list-collect-nrev x nrev)))
         ///
         (defthm ,(mksym 'true-listp-of- list-collect)
           (true-listp (,list-collect x))
           :rule-classes :type-prescription)

         (defthm ,(mksym list-collect-nrev '-removal)
           (equal (,list-collect-nrev x nrev)
                  (append nrev (,list-collect x)))
           :hints(("Goal" :in-theory (enable acl2::rcons
                                             ,list-collect-nrev))))

         (verify-guards ,list-collect)

         (defmapappend ,list-collect (x)
           (,element-collect x)
           :already-definedp t
           :transform-true-list-p t
           :parents nil)))))

(def-vl-allexprs
  :type vl-maybe-expr
  :nrev-body (if x
                 (nrev-push x nrev)
               (nrev-fix nrev))
  :body (if x
            (list x)
          nil))

(def-vl-allexprs
  :type vl-plainarg
  :nrev-body (vl-maybe-expr-allexprs-nrev (vl-plainarg->expr x) nrev)
  :body (vl-maybe-expr-allexprs (vl-plainarg->expr x)))

(def-vl-allexprs-list
  :list vl-plainarglist
  :element vl-plainarg)

(def-vl-allexprs
  :type vl-namedarg
  :nrev-body (vl-maybe-expr-allexprs-nrev (vl-namedarg->expr x) nrev)
  :body (vl-maybe-expr-allexprs (vl-namedarg->expr x)))

(def-vl-allexprs-list
  :list vl-namedarglist
  :element vl-namedarg)

(def-vl-allexprs
  :type vl-arguments
  :nrev-body
  (vl-arguments-case x
    :named (vl-namedarglist-allexprs-nrev x.args nrev)
    :plain (vl-plainarglist-allexprs-nrev x.args nrev))
  :body
  (vl-arguments-case x
    :named (vl-namedarglist-allexprs x.args)
    :plain (vl-plainarglist-allexprs x.args)))

(def-vl-allexprs
  :type vl-range
  :nrev-body
  (b* (((vl-range x) x)
       (nrev (nrev-push x.msb nrev))
       (nrev (nrev-push x.lsb nrev)))
    nrev)
  :body
  (b* (((vl-range x) x))
      (list x.msb x.lsb)))

(def-vl-allexprs
  :type vl-maybe-range
  :nrev-body (if x
                 (vl-range-allexprs-nrev x nrev)
               (nrev-fix nrev))
  :body (if x
            (vl-range-allexprs x)
          nil))

(def-vl-allexprs-list
  :list vl-rangelist
  :element vl-range)

(def-vl-allexprs
  :type vl-gatedelay
  :nrev-body
  (b* (((vl-gatedelay x) x)
       (nrev (nrev-push x.rise nrev))
       (nrev (nrev-push x.fall nrev)))
    (vl-maybe-expr-allexprs-nrev x.high nrev))
  :body
  (b* (((vl-gatedelay x) x))
      (list* x.rise x.fall (vl-maybe-expr-allexprs x.high))))

(def-vl-allexprs
  :type vl-maybe-gatedelay
  :nrev-body (if x
                 (vl-gatedelay-allexprs-nrev x nrev)
               (nrev-fix nrev))
  :body (if x
            (vl-gatedelay-allexprs x)
          nil))

(def-vl-allexprs
  :type vl-assign
  :nrev-body
  (b* (((vl-assign x) x)
       (nrev (nrev-push x.expr nrev))
       (nrev (nrev-push x.lvalue nrev)))
      (vl-maybe-gatedelay-allexprs-nrev x.delay nrev))
  :body
  (b* (((vl-assign x) x))
      (list* x.expr x.lvalue (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-assignlist
  :element vl-assign)

(def-vl-allexprs
  :type vl-gateinst
  :nrev-body
  (b* (((vl-gateinst x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-plainarglist-allexprs-nrev x.args nrev)))
      (vl-maybe-gatedelay-allexprs-nrev x.delay nrev))
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
  :nrev-body
  (b* (((vl-modinst x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-arguments-allexprs-nrev x.paramargs nrev))
       (nrev (vl-arguments-allexprs-nrev x.portargs nrev)))
      (vl-maybe-gatedelay-allexprs-nrev x.delay nrev))
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
  :nrev-body
  (b* (((vl-netdecl x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-rangelist-allexprs-nrev x.arrdims nrev)))
      (vl-maybe-gatedelay-allexprs-nrev x.delay nrev))
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
  :nrev-body
  (b* (((vl-vardecl x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-rangelist-allexprs-nrev x.arrdims nrev)))
    (vl-maybe-expr-allexprs-nrev x.initval nrev))
  :body
  (b* (((vl-vardecl x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-rangelist-allexprs x.arrdims)
              (vl-maybe-expr-allexprs x.initval))))

(def-vl-allexprs-list
  :list vl-vardecllist
  :element vl-vardecl)

(def-vl-allexprs
  :type vl-eventdecl
  :nrev-body (vl-rangelist-allexprs-nrev (vl-eventdecl->arrdims x) nrev)
  :body (vl-rangelist-allexprs (vl-eventdecl->arrdims x)))

(def-vl-allexprs-list
  :list vl-eventdecllist
  :element vl-eventdecl)

(def-vl-allexprs
  :type vl-portdecl
  :nrev-body (vl-maybe-range-allexprs-nrev (vl-portdecl->range x) nrev)
  :body (vl-maybe-range-allexprs (vl-portdecl->range x)))

(def-vl-allexprs-list
  :list vl-portdecllist
  :element vl-portdecl)

(def-vl-allexprs
  :type vl-paramdecl
  :nrev-body
  (b* (((vl-paramdecl x) x)
       (nrev (nrev-push x.expr nrev)))
    (vl-maybe-range-allexprs-nrev x.range nrev))
  :body
  (b* (((vl-paramdecl x) x))
      (cons x.expr (vl-maybe-range-allexprs x.range))))

(def-vl-allexprs-list
  :list vl-paramdecllist
  :element vl-paramdecl)

(def-vl-allexprs
  :type vl-delaycontrol
  :nrev-body (nrev-push (vl-delaycontrol->value x) nrev)
  :body (list (vl-delaycontrol->value x)))

(def-vl-allexprs
  :type :vl-evatom
  :nrev-body (nrev-push (vl-evatom->expr x) nrev)
  :body (list (vl-evatom->expr x)))

(def-vl-allexprs-list
  :list vl-evatomlist
  :element vl-evatom)

(def-vl-allexprs
  :type vl-eventcontrol
  :nrev-body (vl-evatomlist-allexprs-nrev (vl-eventcontrol->atoms x) nrev)
  :body (vl-evatomlist-allexprs (vl-eventcontrol->atoms x)))

(def-vl-allexprs
  :type vl-repeateventcontrol
  :nrev-body
  (b* (((vl-repeateventcontrol x) x)
       (nrev (nrev-push x.expr nrev)))
    (vl-eventcontrol-allexprs-nrev x.ctrl nrev))
  :body
  (b* (((vl-repeateventcontrol x) x))
    (cons x.expr (vl-eventcontrol-allexprs x.ctrl))))

(def-vl-allexprs
  :type vl-delayoreventcontrol
  :nrev-body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-allexprs-nrev x nrev))
    (:vl-eventcontrol (vl-eventcontrol-allexprs-nrev x nrev))
    (otherwise        (vl-repeateventcontrol-allexprs-nrev x nrev)))
  :body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-allexprs x))
    (:vl-eventcontrol (vl-eventcontrol-allexprs x))
    (otherwise        (vl-repeateventcontrol-allexprs x))))

(def-vl-allexprs
  :type vl-maybe-delayoreventcontrol
  :nrev-body (if x
                 (vl-delayoreventcontrol-allexprs-nrev x nrev)
               (nrev-fix nrev))
  :body (if x
            (vl-delayoreventcontrol-allexprs x)
          nil))

(def-vl-allexprs
  :type vl-blockitem
  :nrev-body
  (case (tag x)
    (:vl-vardecl   (vl-vardecl-allexprs-nrev x nrev))
    (:vl-eventdecl (vl-eventdecl-allexprs-nrev x nrev))
    (otherwise     (vl-paramdecl-allexprs-nrev x nrev)))
  :body
  (case (tag x)
    (:vl-vardecl   (vl-vardecl-allexprs x))
    (:vl-eventdecl (vl-eventdecl-allexprs x))
    (otherwise     (vl-paramdecl-allexprs x))))

(def-vl-allexprs-list
  :list vl-blockitemlist
  :element vl-blockitem)

(defines vl-stmt-allexprs-nrev
  :verbosep t
  :flag-local nil
  (define vl-stmt-allexprs-nrev ((x vl-stmt-p) nrev)
    :measure (vl-stmt-count x)
    :flag :stmt
    (vl-stmt-case x
      :vl-nullstmt
      (nrev-fix nrev)
      :vl-assignstmt
      (b* ((nrev (nrev-push x.lvalue nrev))
           (nrev (nrev-push x.expr nrev))
           (nrev (vl-maybe-delayoreventcontrol-allexprs-nrev x.ctrl nrev)))
        nrev)
      :vl-deassignstmt
      (b* ((nrev (nrev-push x.lvalue nrev)))
        nrev)
      :vl-enablestmt
      (b* ((nrev (nrev-push x.id nrev))
           (nrev (nrev-append x.args nrev)))
        nrev)
      :vl-disablestmt
      (b* ((nrev (nrev-push x.id nrev)))
        nrev)
      :vl-eventtriggerstmt
      (b* ((nrev (nrev-push x.id nrev)))
        nrev)
      :vl-casestmt
      (b* ((nrev (nrev-push x.test nrev))
           (nrev (vl-stmt-allexprs-nrev x.default nrev))
           (nrev (vl-caselist-allexprs-nrev x.cases nrev)))
        nrev)
      :vl-ifstmt
      (b* ((nrev (nrev-push x.condition nrev))
           (nrev (vl-stmt-allexprs-nrev x.truebranch nrev))
           (nrev (vl-stmt-allexprs-nrev x.falsebranch nrev)))
        nrev)
      :vl-foreverstmt
      (b* ((nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-waitstmt
      (b* ((nrev (nrev-push x.condition nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-whilestmt
      (b* ((nrev (nrev-push x.condition nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-forstmt
      (b* ((nrev (nrev-push x.initlhs nrev))
           (nrev (nrev-push x.initrhs nrev))
           (nrev (nrev-push x.test nrev))
           (nrev (nrev-push x.nextlhs nrev))
           (nrev (nrev-push x.nextrhs nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-repeatstmt
      (b* ((nrev (nrev-push x.condition nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-blockstmt
      (b* ((nrev (vl-blockitemlist-allexprs-nrev x.decls nrev))
           (nrev (vl-stmtlist-allexprs-nrev x.stmts nrev)))
        nrev)
      :vl-timingstmt
      (b* ((nrev (vl-stmt-allexprs-nrev x.body nrev))
           (nrev (vl-delayoreventcontrol-allexprs-nrev x.ctrl nrev)))
        nrev)))

  (define vl-stmtlist-allexprs-nrev ((x vl-stmtlist-p) nrev)
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-stmt-allexprs-nrev (car x) nrev)))
      (vl-stmtlist-allexprs-nrev (cdr x) nrev)))

  (define vl-caselist-allexprs-nrev ((x vl-caselist-p) nrev)
    :measure (vl-caselist-count x)
    :flag :cases
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (nrev-fix nrev))
         ((cons expr stmt) (car x))
         (nrev (nrev-push expr nrev))
         (nrev (vl-stmt-allexprs-nrev stmt nrev)))
      (vl-caselist-allexprs-nrev (cdr x) nrev))))


(defines vl-stmt-allexprs
  :parents (allexprs)

  (define vl-stmt-allexprs ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    :returns (exprs vl-exprlist-p)
    :verify-guards nil
    (mbe :logic
         (vl-stmt-case x
           :vl-nullstmt         nil
           :vl-assignstmt       (list* x.lvalue x.expr (vl-maybe-delayoreventcontrol-allexprs x.ctrl))
           :vl-deassignstmt     (list x.lvalue)
           :vl-enablestmt       (cons x.id (list-fix x.args))
           :vl-disablestmt      (list x.id)
           :vl-eventtriggerstmt (list x.id)
           :vl-casestmt         (cons x.test
                                      (append (vl-stmt-allexprs x.default)
                                              (vl-caselist-allexprs x.cases)))
           :vl-ifstmt           (cons x.condition
                                      (append (vl-stmt-allexprs x.truebranch)
                                              (vl-stmt-allexprs x.falsebranch)))
           :vl-foreverstmt      (vl-stmt-allexprs x.body)
           :vl-waitstmt         (cons x.condition (vl-stmt-allexprs x.body))
           :vl-whilestmt        (cons x.condition (vl-stmt-allexprs x.body))
           :vl-forstmt          (list* x.initlhs
                                       x.initrhs
                                       x.test
                                       x.nextlhs
                                       x.nextrhs
                                       (vl-stmt-allexprs x.body))
           :vl-repeatstmt      (cons x.condition (vl-stmt-allexprs x.body))
           :vl-blockstmt       (append (vl-blockitemlist-allexprs x.decls)
                                       (vl-stmtlist-allexprs x.stmts))
           :vl-timingstmt      (append (vl-stmt-allexprs x.body)
                                       (vl-delayoreventcontrol-allexprs x.ctrl)))
         :exec
         (with-local-nrev (vl-stmt-allexprs-nrev x nrev))))

  (define vl-stmtlist-allexprs ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    :returns (exprs vl-exprlist-p)
    (mbe :logic (if (atom x)
                    nil
                  (append (vl-stmt-allexprs (car x))
                          (vl-stmtlist-allexprs (cdr x))))
         :exec
         (with-local-nrev (vl-stmtlist-allexprs-nrev x nrev))))

  (define vl-caselist-allexprs ((x vl-caselist-p))
    :measure (vl-caselist-count x)
    :returns (exprs vl-exprlist-p)
    (mbe :logic (b* ((x (vl-caselist-fix x))
                     ((when (atom x))
                      nil)
                     ((cons expr stmt) (car x)))
                  (cons expr
                        (append (vl-stmt-allexprs stmt)
                                (vl-caselist-allexprs (cdr x)))))
         :exec
         (with-local-nrev (vl-caselist-allexprs-nrev x nrev))))
  ///
  (defthm-vl-stmt-allexprs-nrev-flag
    (defthm vl-stmt-allexprs-nrev-removal
      (equal (vl-stmt-allexprs-nrev x nrev)
             (append nrev (vl-stmt-allexprs x)))
      :flag :stmt)
    (defthm vl-stmtlist-allexprs-nrev-removal
      (equal (vl-stmtlist-allexprs-nrev x nrev)
             (append nrev (vl-stmtlist-allexprs x)))
      :flag :list)
    (defthm vl-caselist-allexprs-nrev-removal
      (equal (vl-caselist-allexprs-nrev x nrev)
             (append nrev (vl-caselist-allexprs x)))
      :flag :cases)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-stmtlist-allexprs-nrev x nrev)
                     (vl-caselist-allexprs-nrev x nrev)
                     (vl-stmt-allexprs-nrev x nrev)))))
  (verify-guards vl-stmt-allexprs))

(def-vl-allexprs
  :type vl-initial
  :nrev-body (vl-stmt-allexprs-nrev (vl-initial->stmt x) nrev)
  :body (vl-stmt-allexprs (vl-initial->stmt x)))

(def-vl-allexprs-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-allexprs
  :type vl-always
  :nrev-body (vl-stmt-allexprs-nrev (vl-always->stmt x) nrev)
  :body (vl-stmt-allexprs (vl-always->stmt x)))

(def-vl-allexprs-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-allexprs
  :type :vl-port
  :nrev-body (vl-maybe-expr-allexprs-nrev (vl-port->expr x) nrev)
  :body (vl-maybe-expr-allexprs (vl-port->expr x)))

(def-vl-allexprs-list
  :list vl-portlist
  :element vl-port)

(def-vl-allexprs
  :type :vl-taskport
  :nrev-body (vl-maybe-range-allexprs-nrev (vl-taskport->range x) nrev)
  :body (vl-maybe-range-allexprs (vl-taskport->range x)))

(def-vl-allexprs-list
  :list vl-taskportlist
  :element vl-taskport)

(def-vl-allexprs
  :type :vl-fundecl
  :nrev-body (b* (((vl-fundecl x) x)
                  (nrev (vl-maybe-range-allexprs-nrev x.rrange nrev))
                  (nrev (vl-taskportlist-allexprs-nrev x.inputs nrev))
                  (nrev (vl-blockitemlist-allexprs-nrev x.decls nrev)))
               (vl-stmt-allexprs-nrev x.body nrev))
  :body (b* (((vl-fundecl x) x))
          (append (vl-maybe-range-allexprs x.rrange)
                  (vl-taskportlist-allexprs x.inputs)
                  (vl-blockitemlist-allexprs x.decls)
                  (vl-stmt-allexprs x.body))))

(def-vl-allexprs-list
  :list vl-fundecllist
  :element vl-fundecl)

(def-vl-allexprs
  :type :vl-taskdecl
  :nrev-body (b* (((vl-taskdecl x) x)
                  (nrev (vl-taskportlist-allexprs-nrev x.ports nrev))
                  (nrev (vl-blockitemlist-allexprs-nrev x.decls nrev)))
               (vl-stmt-allexprs-nrev x.body nrev))
  :body (b* (((vl-taskdecl x) x))
          (append (vl-taskportlist-allexprs x.ports)
                  (vl-blockitemlist-allexprs x.decls)
                  (vl-stmt-allexprs x.body))))

(def-vl-allexprs-list
  :list vl-taskdecllist
  :element vl-taskdecl)


(def-vl-allexprs
  :type vl-module
  :nrev-body
  (b* (((vl-module x) x)
       ;; bozo add support for params eventually
       (nrev (vl-portlist-allexprs-nrev x.ports nrev))
       (nrev (vl-portdecllist-allexprs-nrev x.portdecls nrev))
       (nrev (vl-assignlist-allexprs-nrev x.assigns nrev))
       (nrev (vl-netdecllist-allexprs-nrev x.netdecls nrev))
       (nrev (vl-vardecllist-allexprs-nrev x.vardecls nrev))
       (nrev (vl-eventdecllist-allexprs-nrev x.eventdecls nrev))
       (nrev (vl-paramdecllist-allexprs-nrev x.paramdecls nrev))
       (nrev (vl-fundecllist-allexprs-nrev x.fundecls nrev))
       (nrev (vl-taskdecllist-allexprs-nrev x.taskdecls nrev))
       (nrev (vl-modinstlist-allexprs-nrev x.modinsts nrev))
       (nrev (vl-gateinstlist-allexprs-nrev x.gateinsts nrev))
       (nrev (vl-alwayslist-allexprs-nrev x.alwayses nrev))
       (nrev (vl-initiallist-allexprs-nrev x.initials nrev)))
      nrev)
  :body
  (b* (((vl-module x) x))
      (append (vl-portlist-allexprs x.ports)
              (vl-portdecllist-allexprs x.portdecls)
              (vl-assignlist-allexprs x.assigns)
              (vl-netdecllist-allexprs x.netdecls)
              (vl-vardecllist-allexprs x.vardecls)
              (vl-eventdecllist-allexprs x.eventdecls)
              (vl-paramdecllist-allexprs x.paramdecls)
              (vl-fundecllist-allexprs x.fundecls)
              (vl-taskdecllist-allexprs x.taskdecls)
              (vl-modinstlist-allexprs x.modinsts)
              (vl-gateinstlist-allexprs x.gateinsts)
              (vl-alwayslist-allexprs x.alwayses)
              (vl-initiallist-allexprs x.initials))))

(def-vl-allexprs-list
  :list vl-modulelist
  :element vl-module)

(define vl-module-exprnames-set ((x vl-module-p))
  ;; This used to have a more optimized definition that avoided reversal, but
  ;; now with nrev there isn't a way to do it.
  (mergesort (vl-exprlist-names (vl-module-allexprs x))))
