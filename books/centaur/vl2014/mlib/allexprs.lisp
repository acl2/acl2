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

  (let* ((mksym-package-symbol 'vl2014::foo)
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
  (let* ((mksym-package-symbol 'vl2014::foo)
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
  :type vl-packeddimension
  :nrev-body
  (if (eq x :vl-unsized-dimension)
      (nrev-fix nrev)
    (vl-range-allexprs-nrev x nrev))
  :body
  (if (eq x :vl-unsized-dimension)
      nil
    (vl-range-allexprs x)))

(def-vl-allexprs
  :type vl-maybe-packeddimension
  :nrev-body
  (if x
      (vl-packeddimension-allexprs-nrev x nrev)
    (nrev-fix nrev))
  :body
  (if x
      (vl-packeddimension-allexprs x)
    nil))

(def-vl-allexprs-list
  :list vl-packeddimensionlist
  :element vl-packeddimension)

(def-vl-allexprs
  :type vl-enumbasetype
  :nrev-body
  (b* (((vl-enumbasetype x) x))
    (vl-maybe-packeddimension-allexprs-nrev x.dim nrev))
  :body
  (b* (((vl-enumbasetype x) x))
    (vl-maybe-packeddimension-allexprs x.dim)))

(def-vl-allexprs
  :type vl-enumitem
  :nrev-body
  (b* (((vl-enumitem x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-maybe-expr-allexprs-nrev x.value nrev)))
    nrev)
  :body
  (b* (((vl-enumitem x) x))
    (append (vl-maybe-range-allexprs x.range)
            (vl-maybe-expr-allexprs x.value))))

(def-vl-allexprs-list
  :list vl-enumitemlist
  :element vl-enumitem)

(defines vl-datatype-allexprs-nrev
  :parents (vl-datatype-allexprs)
  :flag-local nil

  (define vl-datatype-allexprs-nrev ((x vl-datatype-p) nrev)
    :measure (vl-datatype-count x)
    :flag :datatype
    (vl-datatype-case x
      (:vl-coretype
       (b* ((nrev (vl-packeddimensionlist-allexprs-nrev x.pdims nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.udims nrev)))
         nrev))
      (:vl-struct
       (b* ((nrev (vl-packeddimensionlist-allexprs-nrev x.pdims nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.udims nrev)))
         (vl-structmemberlist-allexprs-nrev x.members nrev)))
      (:vl-union
       (b* ((nrev (vl-packeddimensionlist-allexprs-nrev x.pdims nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.udims nrev)))
         (vl-structmemberlist-allexprs-nrev x.members nrev)))
      (:vl-enum
       (b* ((nrev (vl-enumbasetype-allexprs-nrev x.basetype nrev))
            (nrev (vl-enumitemlist-allexprs-nrev x.items nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.pdims nrev)))
         (vl-packeddimensionlist-allexprs-nrev x.udims nrev)))
      (:vl-usertype
       (b* ((nrev (nrev-push x.kind nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.pdims nrev))
            (nrev (vl-packeddimensionlist-allexprs-nrev x.udims nrev)))
         nrev))))

  (define vl-structmemberlist-allexprs-nrev ((x vl-structmemberlist-p) nrev)
    :flag :structmemberlist
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-structmember-allexprs-nrev (car x) nrev)))
      (vl-structmemberlist-allexprs-nrev (cdr x) nrev)))

  (define vl-structmember-allexprs-nrev ((x vl-structmember-p) nrev)
    :flag :structmember
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x)
         (nrev (vl-maybe-expr-allexprs-nrev x.rhs nrev)))
      (vl-datatype-allexprs-nrev x.type nrev))))

(defines vl-datatype-allexprs
  :parents (allexprs)
  :flag-local nil

  (define vl-datatype-allexprs ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    :returns (exprs vl-exprlist-p)
    :verify-guards nil
    (mbe :logic
         (vl-datatype-case x
           (:vl-coretype
            (append (vl-packeddimensionlist-allexprs x.pdims)
                    (vl-packeddimensionlist-allexprs x.udims)))
           (:vl-struct
            (append (vl-packeddimensionlist-allexprs x.pdims)
                    (vl-packeddimensionlist-allexprs x.udims)
                    (vl-structmemberlist-allexprs x.members)))
           (:vl-union
            (append (vl-packeddimensionlist-allexprs x.pdims)
                    (vl-packeddimensionlist-allexprs x.udims)
                    (vl-structmemberlist-allexprs x.members)))
           (:vl-enum
            (append (vl-enumbasetype-allexprs x.basetype)
                    (vl-enumitemlist-allexprs x.items)
                    (vl-packeddimensionlist-allexprs x.pdims)
                    (vl-packeddimensionlist-allexprs x.udims)))
           (:vl-usertype
            (cons x.kind
                  (append (vl-packeddimensionlist-allexprs x.pdims)
                          (vl-packeddimensionlist-allexprs x.udims)))))
         :exec
         (with-local-nrev (vl-datatype-allexprs-nrev x nrev))))

  (define vl-structmemberlist-allexprs ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    :returns (exprs vl-exprlist-p)
    (mbe :logic
         (if (atom x)
             nil
           (append (vl-structmember-allexprs (car x))
                   (vl-structmemberlist-allexprs (cdr x))))
         :exec
         (with-local-nrev (vl-structmemberlist-allexprs-nrev x nrev))))

  (define vl-structmember-allexprs ((x vl-structmember-p) )
    :measure (vl-structmember-count x)
    :returns (exprs vl-exprlist-p)
    (mbe :logic
         (b* (((vl-structmember x) x))
           (append (vl-maybe-expr-allexprs x.rhs)
                   (vl-datatype-allexprs x.type)))
         :exec
         (with-local-nrev (vl-structmember-allexprs-nrev x nrev))))
  ///
  (defthm-vl-datatype-allexprs-nrev-flag
    (defthm vl-datatype-allexprs-nrev-removal
      (equal (vl-datatype-allexprs-nrev x nrev)
             (append nrev (vl-datatype-allexprs x)))
      :flag :datatype)
    (defthm vl-structmemberlist-allexprs-nrev-removal
      (equal (vl-structmemberlist-allexprs-nrev x nrev)
             (append nrev (vl-structmemberlist-allexprs x)))
      :flag :structmemberlist)
    (defthm vl-structmember-allexprs-nrev-removal
      (equal (vl-structmember-allexprs-nrev x nrev)
             (append nrev (vl-structmember-allexprs x)))
      :flag :structmember)
    :hints(("Goal"
            :expand ((vl-datatype-allexprs x)
                     (vl-datatype-allexprs-nrev x nrev)
                     (vl-structmember-allexprs x)
                     (vl-structmember-allexprs-nrev x nrev)
                     (vl-structmemberlist-allexprs x)
                     (vl-structmemberlist-allexprs-nrev x nrev)))))
  (verify-guards vl-datatype-allexprs))

(def-vl-allexprs
  :type vl-maybe-datatype
  :nrev-body
  (if x
      (vl-datatype-allexprs-nrev x nrev)
    (nrev-fix nrev))
  :body
  (if x
      (vl-datatype-allexprs x)
    nil))

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
    :vl-arguments-named (vl-namedarglist-allexprs-nrev x.args nrev)
    :vl-arguments-plain (vl-plainarglist-allexprs-nrev x.args nrev))
  :body
  (vl-arguments-case x
    :vl-arguments-named (vl-namedarglist-allexprs x.args)
    :vl-arguments-plain (vl-plainarglist-allexprs x.args)))


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
  :type vl-paramvalue
  :nrev-body
  (vl-paramvalue-case x
    :expr (nrev-push x nrev)
    :datatype (vl-datatype-allexprs-nrev x nrev))
  :body
  (vl-paramvalue-case x
    :expr (list x)
    :datatype (vl-datatype-allexprs x)))

(def-vl-allexprs-list
  :list vl-paramvaluelist
  :element vl-paramvalue)

(def-vl-allexprs
  :type vl-maybe-paramvalue
  :nrev-body (if x
                 (vl-paramvalue-allexprs-nrev x nrev)
               (nrev-fix nrev))
  :body (if x
            (vl-paramvalue-allexprs x)
          nil))

(def-vl-allexprs
  :type vl-namedparamvalue
  :nrev-body
  (b* (((vl-namedparamvalue x) x))
    (vl-maybe-paramvalue-allexprs-nrev x.value nrev))
  :body
  (b* (((vl-namedparamvalue x) x))
    (vl-maybe-paramvalue-allexprs x.value)))

(def-vl-allexprs-list
  :list vl-namedparamvaluelist
  :element vl-namedparamvalue)

(def-vl-allexprs
  :type vl-paramargs
  :nrev-body
  (vl-paramargs-case x
    :vl-paramargs-named (vl-namedparamvaluelist-allexprs-nrev x.args nrev)
    :vl-paramargs-plain (vl-paramvaluelist-allexprs-nrev x.args nrev))
  :body
  (vl-paramargs-case x
    :vl-paramargs-named (vl-namedparamvaluelist-allexprs x.args)
    :vl-paramargs-plain (vl-paramvaluelist-allexprs x.args)))

(def-vl-allexprs
  :type vl-modinst
  :nrev-body
  (b* (((vl-modinst x) x)
       (nrev (vl-maybe-range-allexprs-nrev x.range nrev))
       (nrev (vl-paramargs-allexprs-nrev x.paramargs nrev))
       (nrev (vl-arguments-allexprs-nrev x.portargs nrev)))
      (vl-maybe-gatedelay-allexprs-nrev x.delay nrev))
  :body
  (b* (((vl-modinst x) x))
      (append (vl-maybe-range-allexprs x.range)
              (vl-paramargs-allexprs x.paramargs)
              (vl-arguments-allexprs x.portargs)
              (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-allexprs
  :type vl-vardecl
  :nrev-body
  (b* (((vl-vardecl x) x)
       (nrev (vl-datatype-allexprs-nrev x.type nrev))
       (nrev (vl-maybe-expr-allexprs-nrev x.initval nrev))
       (nrev (vl-maybe-gatedelay-allexprs-nrev x.delay nrev)))
    nrev)
  :body
  (b* (((vl-vardecl x) x))
    (append (vl-datatype-allexprs x.type)
            (vl-maybe-expr-allexprs x.initval)
            (vl-maybe-gatedelay-allexprs x.delay))))

(def-vl-allexprs-list
  :list vl-vardecllist
  :element vl-vardecl)

(def-vl-allexprs
  :type vl-portdecl
  :nrev-body (vl-datatype-allexprs-nrev (vl-portdecl->type x) nrev)
  :body (vl-datatype-allexprs (vl-portdecl->type x)))

(def-vl-allexprs-list
  :list vl-portdecllist
  :element vl-portdecl)

(def-vl-allexprs
  :type vl-paramtype
  :nrev-body
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (b* ((nrev (vl-maybe-range-allexprs-nrev x.range nrev)))
       (vl-maybe-expr-allexprs-nrev x.default nrev)))
    (:vl-explicitvalueparam
     (b* ((nrev (vl-datatype-allexprs-nrev x.type nrev)))
       (vl-maybe-expr-allexprs-nrev x.default nrev)))
    (:vl-typeparam
     (vl-maybe-datatype-allexprs-nrev x.default nrev)))
  :body
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (append (vl-maybe-range-allexprs x.range)
             (vl-maybe-expr-allexprs x.default)))
    (:vl-explicitvalueparam
     (append (vl-datatype-allexprs x.type)
             (vl-maybe-expr-allexprs x.default)))
    (:vl-typeparam
     (vl-maybe-datatype-allexprs x.default))))

(def-vl-allexprs
  :type vl-paramdecl
  :nrev-body
  (b* (((vl-paramdecl x) x))
    (vl-paramtype-allexprs-nrev x.type nrev))
  :body
  (b* (((vl-paramdecl x) x))
    (vl-paramtype-allexprs x.type)))

(def-vl-allexprs-list
  :list vl-paramdecllist
  :element vl-paramdecl)

(def-vl-allexprs
  :type vl-delaycontrol
  :nrev-body (nrev-push (vl-delaycontrol->value x) nrev)
  :body (list (vl-delaycontrol->value x)))

(def-vl-allexprs
  :type vl-evatom
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
      :vl-returnstmt
      (b* ((nrev (if x.val (nrev-push x.val nrev) (nrev-fix nrev))))
        nrev)
      :vl-eventtriggerstmt
      (b* ((nrev (nrev-push x.id nrev)))
        nrev)
      :vl-casestmt
      (b* ((nrev (nrev-push x.test nrev))
           (nrev (vl-stmt-allexprs-nrev x.default nrev))
           (nrev (vl-caselist-allexprs-nrev x.caselist nrev)))
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
      (b* ((nrev (vl-vardecllist-allexprs-nrev x.initdecls nrev))
           (nrev (vl-stmtlist-allexprs-nrev x.initassigns nrev))
           (nrev (nrev-push x.test nrev))
           (nrev (vl-stmtlist-allexprs-nrev x.stepforms nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-repeatstmt
      (b* ((nrev (nrev-push x.condition nrev))
           (nrev (vl-stmt-allexprs-nrev x.body nrev)))
        nrev)
      :vl-blockstmt
      (b* ((nrev (vl-vardecllist-allexprs-nrev x.vardecls nrev))
           (nrev (vl-paramdecllist-allexprs-nrev x.paramdecls nrev))
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
         ((cons exprs stmt) (car x))
         (nrev (nrev-append exprs nrev))
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
           :vl-returnstmt       (and x.val (list x.val))
           :vl-eventtriggerstmt (list x.id)
           :vl-casestmt         (cons x.test
                                      (append (vl-stmt-allexprs x.default)
                                              (vl-caselist-allexprs x.caselist)))
           :vl-ifstmt           (cons x.condition
                                      (append (vl-stmt-allexprs x.truebranch)
                                              (vl-stmt-allexprs x.falsebranch)))
           :vl-foreverstmt      (vl-stmt-allexprs x.body)
           :vl-waitstmt         (cons x.condition (vl-stmt-allexprs x.body))
           :vl-whilestmt        (cons x.condition (vl-stmt-allexprs x.body))
           :vl-forstmt          (append (vl-vardecllist-allexprs x.initdecls)
                                        (vl-stmtlist-allexprs x.initassigns)
                                        (cons x.test
                                              (append (vl-stmtlist-allexprs x.stepforms)
                                                      (vl-stmt-allexprs x.body))))
           :vl-repeatstmt      (cons x.condition (vl-stmt-allexprs x.body))
           :vl-blockstmt       (append (vl-vardecllist-allexprs x.vardecls)
                                       (vl-paramdecllist-allexprs x.paramdecls)
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
                     ((cons exprs stmt) (car x)))
                  (append exprs
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
  :type vl-port
  :nrev-body
  (b* ((x (vl-port-fix x)))
    (if (eq (tag x) :vl-interfaceport)
        (vl-packeddimensionlist-allexprs-nrev (vl-interfaceport->udims x) nrev)
      (vl-maybe-expr-allexprs-nrev (vl-regularport->expr x) nrev)))
  :body
  (b* ((x (vl-port-fix x)))
    (if (eq (tag x) :vl-interfaceport)
        (vl-packeddimensionlist-allexprs (vl-interfaceport->udims x))
      (vl-maybe-expr-allexprs (vl-regularport->expr x)))))

(def-vl-allexprs-list
  :list vl-portlist
  :element vl-port)


(def-vl-allexprs
  :type vl-fundecl
  :nrev-body (b* (((vl-fundecl x) x)
                  (nrev (vl-datatype-allexprs-nrev x.rettype nrev))
                  (nrev (vl-portdecllist-allexprs-nrev x.portdecls nrev))
                  (nrev (vl-vardecllist-allexprs-nrev x.vardecls nrev))
                  (nrev (vl-paramdecllist-allexprs-nrev x.paramdecls nrev)))
               (vl-stmt-allexprs-nrev x.body nrev))
  :body (b* (((vl-fundecl x) x))
          (append (vl-datatype-allexprs x.rettype)
                  (vl-portdecllist-allexprs x.portdecls)
                  (vl-vardecllist-allexprs x.vardecls)
                  (vl-paramdecllist-allexprs x.paramdecls)
                  (vl-stmt-allexprs x.body))))

(def-vl-allexprs-list
  :list vl-fundecllist
  :element vl-fundecl)

(def-vl-allexprs
  :type vl-taskdecl
  :nrev-body (b* (((vl-taskdecl x) x)
                  (nrev (vl-portdecllist-allexprs-nrev x.portdecls nrev))
                  (nrev (vl-vardecllist-allexprs-nrev x.vardecls nrev))
                  (nrev (vl-paramdecllist-allexprs-nrev x.paramdecls nrev)))
               (vl-stmt-allexprs-nrev x.body nrev))
  :body (b* (((vl-taskdecl x) x))
          (append (vl-portdecllist-allexprs x.portdecls)
                  (vl-vardecllist-allexprs x.vardecls)
                  (vl-paramdecllist-allexprs x.paramdecls)
                  (vl-stmt-allexprs x.body))))

(def-vl-allexprs-list
  :list vl-taskdecllist
  :element vl-taskdecl)


(def-vl-allexprs
  :type vl-alias
  :nrev-body (b* (((vl-alias x) x)
                  (nrev (nrev-push x.lhs nrev))
                  (nrev (nrev-push x.rhs nrev)))
               nrev)
  :body (b* (((vl-alias x) x))
          (list x.lhs x.rhs)))

(def-vl-allexprs-list
  :list vl-aliaslist
  :element vl-alias)

(def-vl-allexprs
  :type vl-module
  :nrev-body
  (b* (((vl-module x) x)
       ;; bozo add support for params eventually
       (nrev (vl-portlist-allexprs-nrev x.ports nrev))
       (nrev (vl-portdecllist-allexprs-nrev x.portdecls nrev))
       (nrev (vl-assignlist-allexprs-nrev x.assigns nrev))
       (nrev (vl-vardecllist-allexprs-nrev x.vardecls nrev))
       (nrev (vl-paramdecllist-allexprs-nrev x.paramdecls nrev))
       (nrev (vl-fundecllist-allexprs-nrev x.fundecls nrev))
       (nrev (vl-taskdecllist-allexprs-nrev x.taskdecls nrev))
       (nrev (vl-modinstlist-allexprs-nrev x.modinsts nrev))
       (nrev (vl-gateinstlist-allexprs-nrev x.gateinsts nrev))
       (nrev (vl-alwayslist-allexprs-nrev x.alwayses nrev))
       (nrev (vl-initiallist-allexprs-nrev x.initials nrev))
       (nrev (vl-aliaslist-allexprs-nrev x.aliases nrev)))
      nrev)
  :body
  (b* (((vl-module x) x))
      (append (vl-portlist-allexprs x.ports)
              (vl-portdecllist-allexprs x.portdecls)
              (vl-assignlist-allexprs x.assigns)
              (vl-vardecllist-allexprs x.vardecls)
              (vl-paramdecllist-allexprs x.paramdecls)
              (vl-fundecllist-allexprs x.fundecls)
              (vl-taskdecllist-allexprs x.taskdecls)
              (vl-modinstlist-allexprs x.modinsts)
              (vl-gateinstlist-allexprs x.gateinsts)
              (vl-alwayslist-allexprs x.alwayses)
              (vl-initiallist-allexprs x.initials)
              (vl-aliaslist-allexprs x.aliases))))

(def-vl-allexprs-list
  :list vl-modulelist
  :element vl-module)

(define vl-module-exprnames-set ((x vl-module-p))
  ;; This used to have a more optimized definition that avoided reversal, but
  ;; now with nrev there isn't a way to do it.
  (mergesort (vl-exprlist-names (vl-module-allexprs x))))
