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
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/modnamespace")
(include-book "../../mlib/hid-tools")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc resolve-indexing
  :parents (annotate)
  :short "Resolve @(':vl-index') operators that are applied to simple
bitvectors into @(':vl-bitselect') operators."

  :long "<p>When our @(see parser) encounters a subexpression like @('foo[i]'),
it does not know whether @('foo') is an ordinary vector like @('wire [3:0]
foo'), an array like @('reg [63:0] foo [128:0];'), or something more
complicated like a reference into an array of instances or similar.  To account
for this, the parser just produces @(':vl-index') operators whenever it sees a
selection like @('foo[i]').  Similarly when it encounters a range select such
as @('foo[5:3]') or @('foo[4+:6]'), it produces either a @(':vl-select-colon'),
@(':vl-select-pluscolon'), or @(':vl-select-minuscolon') operator; these could
be simple partselects or they could be selecting a range of substructures.</p>

<p>In this transform, we convert these unresolved index operators into
@(':vl-bitselect'), @(':vl-partselect-colon'), @(':vl-partselect-pluscolon'),
and @(':vl-partselect-minuscolon') operations when we can tell that they can be
treated as selects from a simple vector.  This transform should typically be
run very early in the transformation sequence, as later transforms often expect
to find proper @(':vl-bitselect') operators.</p>

<p>As we implement better array support, this transform remains useful for
backward compatibility with other transforms that don't deal correctly with
arrays and complex SystemVerilog datatypes.  Generally, when a transform is
written with arrays and complex datatypes in mind, it will treat the resolved
and unresolved versions of these index operators equivalently.  Otherwise, it
will only deal with the resolved versions and should produce a warning if it
comes across an unresolved operator.</p>")

(local (xdoc::set-default-parents resolve-indexing))

(define vl-datatype-bitselect-p ((x vl-datatype-p))
  :short "Recognize a datatype for which an indexing operator is a bitselect/partselect."
  :long "<p>This is more complicated than one might think.  For example, a
packed struct can be bitselected/partselected from and acts just like a vector
in that case.  However, a packed array is always indexed as an array.</p>

<p>The datatype should have usertypes resolved away before calling.</p>"
  (b* ((udims (vl-datatype->udims x))
       (pdims (vl-datatype->pdims x))
       ((when (consp udims))
        ;; If there are unpacked dimensions, we're definitely array-indexing.
        nil)
       ((when (consp pdims))
        ;; The one time a packed-dimensioned object can be
        ;; bitselected from is the common case where it is a
        ;; reg/logic/bit and has exactly one packed dimension.
        ;; Otherwise, you're indexing into a packed array of
        ;; some higher structures.
        (and (eq (vl-datatype-kind x) :vl-coretype)
             (member (vl-coretype->name x) '(:vl-reg :vl-logic :vl-bit))
             (atom (cdr pdims)))))
    ;; No dimensions.
    (vl-datatype-case x

      (:vl-coretype
       (or
        ;; Vector integer types.  Oddly, it likely should be an error to index
        ;; into these (since here we know it doesn't have any dimensions), but
        ;; we don't make that this transform's business.
        (member x.name '(:vl-reg :vl-logic :vl-bit))
        ;; Atomic integer types.  It seems okay to bit-select from these.  They
        ;; should never have associated dimensions.
        (member x.name '(:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer)))
        ;; Anything else is just too hard and we're not going to think about
        ;; it.  This includes, e.g.,: real, string, chandle, void, event
        )
      (:vl-struct x.packedp)
      (:vl-union x.packedp)

      ;; BOZO figure out about enums
      (:otherwise nil))))

(define vl-expr-is-bitselect-type ((x vl-expr-p) (ss vl-scopestack-p))
  :short "Checks whether an expression is of a bitselectable type."
  :long "<p>Should only be called on an appropriate operand for an
indexing/partselect operation, that is, some number of indexing operators
applied to a HID/identifier.  Otherwise, we generate a warning and fail.</p>"
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (bitselectp "true if successful and the expression is of bitselectable type."))
  (b* (((mv warning type) (vl-index-find-type x ss (vl-expr-fix x)))
       ((when warning) (mv warning nil)))
    (mv nil (vl-datatype-bitselect-p type))))


(defines vl-expr-resolve-indexing-aux
  :short "Core routine for introducing @(':vl-array-index') and
@(':vl-bitselect') operators throughout a @(see vl-expr-p)."

  (define vl-expr-resolve-indexing-aux
    ((x        vl-expr-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription
                      "Optimization, don't re-cons index-free expresions.")
        (new-x        vl-expr-p))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (mv (ok) nil x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))
         ((when (member op '(:vl-index
                             :vl-select-colon :vl-select-pluscolon :vl-select-minuscolon)))
          (b* (((mv warning bitselp) (vl-expr-is-bitselect-type (first args) ss))
               ((when warning)
                (mv (cons warning (ok)) nil x))
               ((unless bitselp) (mv (ok) nil x)))
            (mv (ok) t (change-vl-nonatom
                        x :op (case op
                                (:vl-index :vl-bitselect)
                                (:vl-select-colon :vl-partselect-colon)
                                (:vl-select-pluscolon :vl-partselect-pluscolon)
                                (:vl-select-minuscolon :vl-partselect-minuscolon))))))

         ((mv warnings args-changedp args)
          (vl-exprlist-resolve-indexing-aux args ss warnings)))
      (mv warnings args-changedp
          (if args-changedp
              (change-vl-nonatom x :args args)
            x))))

  (define vl-exprlist-resolve-indexing-aux
    ((x        vl-exprlist-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription)
        (new-x        (and (vl-exprlist-p new-x)
                           (equal (len new-x) (len x)))))
    :verify-guards nil
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil nil))
         ((mv warnings car-changedp car-prime)
          (vl-expr-resolve-indexing-aux (car x) ss warnings))
         ((mv warnings cdr-changedp cdr-prime)
          (vl-exprlist-resolve-indexing-aux (cdr x) ss warnings))
         (changedp (or car-changedp cdr-changedp))
         (new-x    (cons car-prime cdr-prime)))
      (mv warnings changedp new-x)))
  ///
  (defthm-vl-expr-resolve-indexing-aux-flag
    (defthm true-listp-of-vl-exprlist-resolve-indexing-aux
      (b* (((mv ?warnings ?changedp new-x)
            (vl-exprlist-resolve-indexing-aux x ss warnings)))
        (true-listp new-x))
      :rule-classes :type-prescription
      :flag :list)
    :skip-others t)

  (local (defthm-vl-expr-resolve-indexing-aux-flag
           ;; BOZO wtf, why do I need this?
           (defthm l0
             (b* (((mv ?warnings ?changedp new-x)
                   (vl-exprlist-resolve-indexing-aux x ss warnings)))
               (iff new-x (consp x)))
             :flag :list)
           :skip-others t))

  (verify-guards vl-expr-resolve-indexing-aux)

  (deffixequiv-mutual vl-expr-resolve-indexing-aux))

(defmacro def-vl-resolve-indexing (name &key body)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn   (mksym name '-resolve-indexing))
       (type (mksym name '-p))
       (fix  (mksym name '-fix)))
    `(define ,fn
       :short ,(cat "Resolve @(':vl-index') operators throughout a @(see " (symbol-name type) ").")
       ((x        ,type)
        (ss       vl-scopestack-p)
        (warnings vl-warninglist-p))
       :returns
       (mv (warnings vl-warninglist-p)
           (new-x    ,type))
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-resolve-indexing-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn      (mksym name '-resolve-indexing))
       (elem-fn (mksym element '-resolve-indexing))
       (type    (mksym name '-p))
       ;(fix     (mksym name '-fix))
       )
    `(define ,fn
       :short ,(cat "Resolve @(':vl-index') operators throughout a @(see " (symbol-name type) ").")
       ((x        ,type)
        (ss       vl-scopestack-p)
        (warnings vl-warninglist-p))
       :returns
       (mv (warnings vl-warninglist-p)
           (new-x    ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) ss warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) ss warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defthm ,(mksym 'true-listp-of- fn)
         (true-listp (mv-nth 1 (,fn x ss warnings)))
         :rule-classes :type-prescription)

       (defthm ,(mksym 'len-of- fn)
         (equal (len (mv-nth 1 (,fn x ss warnings)))
                (len x))))))

(def-vl-resolve-indexing vl-expr
  ;; Simple wrapper that just bundles up the changedp optimization.
  :body
  (b* (((mv warnings ?changedp new-x)
        (vl-expr-resolve-indexing-aux x ss warnings)))
    (mv warnings new-x)))

;; Simple wrapper that just bundles up the changedp optimization.
(def-vl-resolve-indexing-list vl-exprlist :element vl-expr)

(def-vl-resolve-indexing vl-maybe-expr
  :body
  (if (not x)
      (mv warnings nil)
    (vl-expr-resolve-indexing x ss warnings)))

(def-vl-resolve-indexing vl-assign
  :body
  (b* (((vl-assign x) x)
       ((mv warnings lvalue-prime)
        (vl-expr-resolve-indexing x.lvalue ss warnings))
       ((mv warnings expr-prime)
        (vl-expr-resolve-indexing x.expr ss warnings)))
    (mv warnings
        (change-vl-assign x
                          :lvalue lvalue-prime
                          :expr expr-prime))))

(def-vl-resolve-indexing-list vl-assignlist :element vl-assign)

(def-vl-resolve-indexing vl-plainarg
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr ss warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-plainarglist :element vl-plainarg)

(def-vl-resolve-indexing vl-namedarg
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr ss warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-namedarglist :element vl-namedarg)

(def-vl-resolve-indexing vl-arguments
  :body
  (vl-arguments-case x
    :vl-arguments-named
    (b* (((mv warnings args-prime)
          (vl-namedarglist-resolve-indexing x.args ss warnings)))
      (mv warnings (change-vl-arguments-named x :args args-prime)))
    :vl-arguments-plain
    (b* (((mv warnings args-prime)
          (vl-plainarglist-resolve-indexing x.args ss warnings)))
      (mv warnings (change-vl-arguments-plain x :args args-prime)))))

(def-vl-resolve-indexing vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-resolve-indexing x.portargs ss warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-resolve-indexing-list vl-modinstlist :element vl-modinst)

(def-vl-resolve-indexing vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-resolve-indexing x.args ss warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-resolve-indexing-list vl-gateinstlist :element vl-gateinst)

(def-vl-resolve-indexing vl-delaycontrol
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-resolve-indexing x.value ss warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-resolve-indexing vl-evatom
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr ss warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-evatomlist :element vl-evatom)

(def-vl-resolve-indexing vl-eventcontrol
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-resolve-indexing x.atoms ss warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-resolve-indexing vl-repeateventcontrol
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr ss warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-resolve-indexing x.ctrl ss warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol
           (vl-delaycontrol-resolve-indexing x ss warnings))
          (:vl-eventcontrol
           (vl-eventcontrol-resolve-indexing x ss warnings))
          (otherwise
           (vl-repeateventcontrol-resolve-indexing x ss warnings))))

(def-vl-resolve-indexing vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-resolve-indexing x ss warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-resolve-indexing-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-resolve-indexing x ss warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-resolve-indexing
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-resolve-indexing.new-x))
          :use ((:instance
                 vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-resolve-indexing.new-x)))))

(defines vl-stmt-resolve-indexing

  (define vl-stmt-resolve-indexing
    ((x        vl-stmt-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x        vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv (ok) x))
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)
                  ((mv warnings lvalue-prime) (vl-expr-resolve-indexing x.lvalue ss warnings))
                  ((mv warnings expr-prime)   (vl-expr-resolve-indexing x.expr ss warnings))
                  ((mv warnings ctrl-prime)   (vl-maybe-delayoreventcontrol-resolve-indexing x.ctrl ss warnings))
                  (x-prime                    (change-vl-assignstmt x
                                                                    :lvalue lvalue-prime
                                                                    :expr expr-prime
                                                                    :ctrl ctrl-prime)))
               (mv (ok) x-prime)))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue-prime) (vl-expr-resolve-indexing x.lvalue ss warnings))
                  (x-prime                    (change-vl-deassignstmt x :lvalue lvalue-prime)))
               (mv warnings x-prime)))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id-prime)   (vl-expr-resolve-indexing x.id ss warnings))
                  ((mv warnings args-prime) (vl-exprlist-resolve-indexing x.args ss warnings))
                  (x-prime                  (change-vl-enablestmt x
                                                                  :id id-prime
                                                                  :args args-prime)))
               (mv warnings x-prime)))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id-prime) (vl-expr-resolve-indexing x.id ss warnings))
                  (x-prime                (change-vl-disablestmt x :id id-prime)))
               (mv warnings x-prime)))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x)
                  ((mv warnings val)
                   (if x.val
                       (vl-expr-resolve-indexing x.val ss warnings)
                     (mv warnings x.val))))
               (mv (ok) (change-vl-returnstmt x :val val))))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id-prime) (vl-expr-resolve-indexing x.id ss warnings))
                  (x-prime                (change-vl-eventtriggerstmt x :id id-prime)))
               (mv warnings x-prime)))
            (otherwise (mv (impossible) x))))
         ((mv warnings exprs-prime)
          (vl-exprlist-resolve-indexing (vl-compoundstmt->exprs x) ss warnings))
         ((mv warnings stmts-prime)
          (vl-stmtlist-resolve-indexing (vl-compoundstmt->stmts x) ss warnings))
         ((mv warnings ctrl-prime)
          (vl-maybe-delayoreventcontrol-resolve-indexing (vl-compoundstmt->ctrl x) ss warnings))
         (x-prime
          (change-vl-compoundstmt x
                                  :exprs exprs-prime
                                  :stmts stmts-prime
                                  :ctrl ctrl-prime)))
      (mv (ok) x-prime)))

  (define vl-stmtlist-resolve-indexing
    ((x        vl-stmtlist-p)
     (ss       vl-scopestack-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x        (and (vl-stmtlist-p new-x)
                           (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime)
          (vl-stmt-resolve-indexing (car x) ss warnings))
         ((mv warnings cdr-prime)
          (vl-stmtlist-resolve-indexing (cdr x) ss warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-resolve-indexing)
  (deffixequiv-mutual vl-stmt-resolve-indexing))

(def-vl-resolve-indexing vl-always
  :body (b* (((vl-always x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt ss warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-alwayslist :element vl-always)

(def-vl-resolve-indexing vl-initial
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt ss warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-initiallist :element vl-initial)

(def-vl-resolve-indexing vl-port
  :body (b* ((x (vl-port-fix x))
             ((when (eq (tag x) :vl-interfaceport))
              (mv warnings x))
             ((vl-regularport x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr ss warnings))
             (x-prime
              (change-vl-regularport x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-portlist :element vl-port)


(def-vl-resolve-indexing vl-fundecl
  :body
  (b* (((vl-fundecl x) x)

       (ss (vl-scopestack-push (vl-fundecl->blockscope x) ss))

       ((mv warnings new-body)
        (vl-stmt-resolve-indexing x.body ss warnings))

       (new-x (change-vl-fundecl x :body new-body)))
    (mv warnings new-x)))

(def-vl-resolve-indexing-list vl-fundecllist :element vl-fundecl)

(define vl-module-resolve-indexing ((x vl-module-p)
                                    (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       (ss (vl-scopestack-push x ss))

       (warnings x.warnings)
       ((mv warnings ports)     (vl-portlist-resolve-indexing     x.ports ss warnings))
       ((mv warnings assigns)   (vl-assignlist-resolve-indexing   x.assigns ss warnings))
       ((mv warnings modinsts)  (vl-modinstlist-resolve-indexing  x.modinsts ss warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-resolve-indexing x.gateinsts ss warnings))
       ((mv warnings alwayses)  (vl-alwayslist-resolve-indexing   x.alwayses ss warnings))
       ((mv warnings initials)  (vl-initiallist-resolve-indexing  x.initials ss warnings))
       ((mv warnings fundecls)  (vl-fundecllist-resolve-indexing  x.fundecls ss warnings))

       (new-x (change-vl-module x
                                :ports ports
                                :assigns assigns
                                :modinsts modinsts
                                :gateinsts gateinsts
                                :alwayses alwayses
                                :initials initials
                                :fundecls fundecls
                                :warnings warnings)))
    new-x))

(defprojection vl-modulelist-resolve-indexing ((x vl-modulelist-p)
                                               (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-resolve-indexing x ss))

(define vl-design-resolve-indexing ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (new-mods (vl-modulelist-resolve-indexing x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods new-mods)))

