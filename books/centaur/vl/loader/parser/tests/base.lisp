; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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

(in-package "VL")
(include-book "../utils")
(include-book "../../lexer/top") ;; for make-test-tokens, etc.
(include-book "../../../parsetree")
(include-book "../../../mlib/expr-tools")

; We now introduce a function to convert expressions into a "pretty" format
; which makes it a bit easier to see if an expression is what you expect for
; writing unit tests.

;; (define vl-pretty-atom ((x vl-expr-p))
;;   :guard (vl-atom-p x)
;;   (let ((guts (vl-atom->guts x)))
;;     (cond ((vl-constint-p guts)    (vl-constint->value guts))
;;           ((vl-weirdint-p guts)
;;            (list 'weird
;;                  (vl-bitlist->string (vl-weirdint->bits guts))))
;;           ((vl-string-p guts)      (list 'str  (vl-string->value guts)))
;;           ((vl-real-p guts)        (list 'real (vl-real->value guts)))
;;           ((vl-id-p guts)          (list 'id   (vl-id->name guts)))
;;           ((vl-hidpiece-p guts)    (list 'hid  (vl-hidpiece->name guts)))
;;           ((vl-funname-p guts)     (list 'fun  (vl-funname->name guts)))
;;           ((vl-typename-p guts)    (list 'type (vl-typename->name guts)))
;;           ((vl-sysfunname-p guts)  (list 'sys  (vl-sysfunname->name guts)))
;;           ((vl-keyguts-p guts)     (list 'key  (vl-keyguts->type guts)))
;;           ((vl-basictype-p guts)   (list 'basic (vl-basictype->kind guts)))
;;           ((vl-tagname-p guts)     (list 'tag  (vl-tagname->name guts)))

;;           ((vl-time-p guts)
;;            (list 'time
;;                  (concatenate 'string
;;                               (vl-time->quantity guts)
;;                               (vl-timeunit->string
;;                                (vl-time->units guts)))))
;;           ((vl-extint-p guts)
;;            (list 'ext (vl-extint->value guts)))
;;           (t
;;            (raise "Unsupported kind of atom: ~x0." x)))))

(define vl-pretty-value ((x vl-value-p))
  (vl-value-case x
    :vl-constint x.value
    :vl-weirdint (list 'weird x.bits)
    :vl-extint   (list 'ext x.value)
    :vl-real     (list 'real x.value)
    :vl-time     (list 'time (str::cat x.quantity (vl-timeunit->string x.units)))
    :vl-string   (list 'str x.value)))

(define vl-pretty-scopename ((x vl-scopename-p))
  (let ((x (vl-scopename-fix x)))
    (case x
      (:vl-local '(key :vl-local))
      (:vl-$unit '(key :vl-$unit))
      (t         x))))

(define vl-pretty-hidname ((x vl-hidname-p))
  (let ((x (vl-hidname-fix x)))
    (case x
      (:vl-$root '(key :vl-$root))
      (otherwise x))))

(define vl-pretty-specialkey ((x vl-specialkey-p))
  (let ((x (vl-specialkey-fix x)))
    (case x
      (:vl-null       '(key :vl-null))
      (:vl-$          '(key :vl-$))
      (:vl-emptyqueue '(key :vl-emptyqueue)))))

(local (defthm vl-atts-p-of-remove-from-alist
         (implies (vl-atts-p atts)
                  (vl-atts-p (remove-from-alist key atts)))
         :hints(("Goal" :in-theory (enable remove-from-alist)))))

(local (defthm vl-atts-count-of-remove-from-alist
         (implies (vl-atts-p atts)
                  (<= (vl-atts-count (remove-from-alist key atts))
                      (vl-atts-count atts)))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal"
                 :in-theory (enable vl-atts-count remove-from-alist)
                 :induct (remove-from-alist key atts)))))

(local (defthm vl-paramvalue-count-of-maybe-paramvalue
         (implies (and (vl-maybe-paramvalue-p x)
                       x)
                  (< (vl-paramvalue-count x) (vl-maybe-paramvalue-count x)))
         :hints(("Goal" :expand ((vl-maybe-paramvalue-count x)
                                 (vl-maybe-paramvalue-some->val x))))
         :rule-classes :linear))

(local (defthm vl-paramargs-count-of-maybe-paramargs
         (implies (and (vl-maybe-paramargs-p x)
                       x)
                  (< (vl-paramargs-count x) (vl-maybe-paramargs-count x)))
         :hints(("Goal" :expand ((vl-maybe-paramargs-count x)
                                 (vl-maybe-paramargs-some->val x))))
         :rule-classes :linear))

(defines vl-pretty-exprs
  :flag nil

  (define vl-pretty-hidindex ((x vl-hidindex-p))
    :measure (vl-hidindex-count x)
    (b* (((vl-hidindex x))
         ((unless x.indices)
          x.name))
      (list :vl-hid-index
            (vl-pretty-hidname x.name)
            (vl-pretty-exprlist x.indices))))

  (define vl-pretty-hidexpr ((x vl-hidexpr-p))
    :measure (vl-hidexpr-count x)
    (vl-hidexpr-case x
      (:end x.name)
      (:dot (list :dot
                  (vl-pretty-hidindex x.first)
                  (vl-pretty-hidexpr x.rest)))))

  (define vl-pretty-scopeexpr ((x vl-scopeexpr-p))
    :measure (vl-scopeexpr-count x)
    (vl-scopeexpr-case x
      (:end   (vl-pretty-hidexpr x.hid))
      (:colon (if x.paramargs
                  (list :scope
                        (vl-pretty-scopename x.first)
                        (vl-pretty-paramargs x.paramargs)
                        (vl-pretty-scopeexpr x.rest))
                (list :scope
                      (vl-pretty-scopename x.first)
                      (vl-pretty-scopeexpr x.rest))))))

  (define vl-pretty-plusminus ((x vl-plusminus-p))
    :measure (vl-plusminus-count x)
    (b* (((vl-plusminus x)))
      (list (if x.minusp :minuscolon :pluscolon)
            (vl-pretty-expr x.base)
            (vl-pretty-expr x.width))))

  (define vl-pretty-partselect ((x vl-partselect-p))
    :measure (vl-partselect-count x)
    (vl-partselect-case x
      (:none  nil)
      (:range (list :colon
                    (vl-pretty-expr x.msb)
                    (vl-pretty-expr x.lsb)))
      (:plusminus (vl-pretty-plusminus x.plusminus))))



  (define vl-pretty-arrayrange ((x vl-arrayrange-p))
    :measure (vl-arrayrange-count x)
    (vl-arrayrange-case x
      (:none      nil)
      (:range     (vl-pretty-range x.range))
      (:plusminus (vl-pretty-plusminus x.plusminus))
      (:index     (list :arrindex (vl-pretty-expr x.expr)))))

  (define vl-pretty-streamexpr ((x vl-streamexpr-p))
    :measure (vl-streamexpr-count x)
    (b* (((vl-streamexpr x))
         ((when (vl-arrayrange-case x.part :none))
          (vl-pretty-expr x.expr)))
      (list (vl-pretty-expr x.expr)
            :with
            (vl-pretty-arrayrange x.part))))

  (define vl-pretty-streamexprlist ((x vl-streamexprlist-p))
    :measure (vl-streamexprlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-streamexpr (car x))
            (vl-pretty-streamexprlist (cdr x)))))

  (define vl-pretty-valuerange ((x vl-valuerange-p))
    :measure (vl-valuerange-count x)
    (vl-valuerange-case x
      (:valuerange-single (vl-pretty-expr x.expr))
      (:valuerange-range (list :range
                               (vl-pretty-expr x.low)
                               (vl-pretty-expr x.high)))))

  (define vl-pretty-valuerangelist ((x vl-valuerangelist-p))
    :measure (vl-valuerangelist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-valuerange (car x))
            (vl-pretty-valuerangelist (cdr x)))))

  (define vl-pretty-patternkey ((x vl-patternkey-p))
    :measure (vl-patternkey-count x)
    (vl-patternkey-case x
      (:expr      (vl-pretty-expr x.key))
      (:structmem (list :structmem x.name))
      (:type      (vl-pretty-datatype x.type))
      (:default   :vl-default)))

  (define vl-pretty-slicesize ((x vl-slicesize-p))
    :measure (vl-slicesize-count x)
    (vl-slicesize-case x
      (:expr (vl-pretty-expr x.expr))
      (:type (vl-pretty-datatype x.type))
      (:none nil)))

  (define vl-pretty-keyvallist ((x vl-keyvallist-p))
    :measure (vl-keyvallist-count x)
    (b* ((x (vl-keyvallist-fix x))
         ((when (atom x))
          nil)
         ((cons key val) (car x)))
      (cons (list key '<- val)
            (vl-pretty-keyvallist (cdr x)))))

  (define vl-pretty-assignpat ((x vl-assignpat-p))
    :measure (vl-assignpat-count x)
    (vl-assignpat-case x
      (:positional (vl-pretty-exprlist x.vals))
      (:keyval     (vl-pretty-keyvallist x.pairs))
      (:repeat     (list :vl-repeat
                         (vl-pretty-expr x.reps)
                         (vl-pretty-exprlist x.vals)))))

  (define vl-pretty-casttype ((x vl-casttype-p))
    :measure (vl-casttype-count x)
    (vl-casttype-case x
      :type       (vl-pretty-datatype x.type)
      :size       (vl-pretty-expr x.size)
      :signedness (if x.signedp :signed :unsigned)
      :const      :const))

  (define vl-pretty-expr ((x vl-expr-p))
    :measure (vl-expr-count x)
    (let ((atts (remove-from-alist "VL_LINESTART" (vl-expr->atts x))))
      (vl-expr-case x
        :vl-special (vl-pretty-specialkey x.key)
        :vl-literal (vl-pretty-value x.val)
        :vl-index
        (b* (((when (vl-idexpr-p x))
              (list 'id (vl-idexpr->name x))))
          (list :index
                (vl-pretty-atts atts)
                (vl-pretty-scopeexpr x.scope)
                (vl-pretty-exprlist x.indices)
                (vl-pretty-partselect x.part)))
        :vl-unary   (list x.op
                          (vl-pretty-atts atts)
                          (vl-pretty-expr x.arg))
        :vl-binary  (list x.op
                          (vl-pretty-atts atts)
                          (vl-pretty-expr x.left)
                          (vl-pretty-expr x.right))
        :vl-qmark   (list :vl-qmark
                          (vl-pretty-atts atts)
                          (vl-pretty-expr x.test)
                          (vl-pretty-expr x.then)
                          (vl-pretty-expr x.else))
        :vl-mintypmax (list :vl-mintypmax
                            (vl-pretty-atts atts)
                            (vl-pretty-expr x.min)
                            (vl-pretty-expr x.typ)
                            (vl-pretty-expr x.max))
        :vl-concat (list* :vl-concat
                          (vl-pretty-atts atts)
                          (vl-pretty-exprlist x.parts))
        :vl-multiconcat (list* :vl-multiconcat
                               (vl-pretty-atts atts)
                               (vl-pretty-expr x.reps)
                               (vl-pretty-exprlist x.parts))
        :vl-stream (list* (if (eq x.dir :left)
                              :vl-stream-left
                            :vl-stream-right)
                          (vl-pretty-atts atts)
                          (if (vl-slicesize-case x.size :none)
                              (vl-pretty-streamexprlist x.parts)
                            (cons (vl-pretty-slicesize x.size)
                                  (vl-pretty-streamexprlist x.parts))))
        :vl-call (list* (if x.systemp :vl-syscall :vl-funcall)
                        (vl-pretty-atts atts)
                        (vl-pretty-scopeexpr x.name)
                        ;; bozo no tests for namedargs yet
                        (append (if x.typearg
                                    (cons (vl-pretty-maybe-datatype x.typearg)
                                          (vl-pretty-maybe-exprlist x.plainargs))
                                  (vl-pretty-maybe-exprlist x.plainargs))
                                (vl-pretty-call-namedargs x.namedargs)))
        :vl-cast (list :cast
                       (vl-pretty-atts atts)
                       (vl-pretty-casttype x.to)
                       (vl-pretty-expr x.expr))
        :vl-inside (list* :inside
                          (vl-pretty-atts atts)
                          (vl-pretty-expr x.elem)
                          (vl-pretty-valuerangelist x.set))
        :vl-tagged (list* :vl-tagged
                          (vl-pretty-atts atts)
                          x.tag
                          (if x.expr
                              (list (vl-pretty-maybe-expr x.expr))
                            nil))
        :vl-pattern (list* :pattern
                           (vl-pretty-atts atts)
                           (vl-pretty-maybe-datatype x.pattype)
                           (vl-pretty-assignpat x.pat))
        :vl-eventexpr (list* :event
                             (vl-pretty-atts x.atts)
                             (vl-pretty-evatomlist x.atoms)))))

  (define vl-pretty-atts ((x vl-atts-p))
    :measure (vl-atts-count x)
    (b* ((x (vl-atts-fix x))
         ((when (atom x))
          nil)
         ((cons key val) (car x)))
      (cons (if val
                (list key '<- (vl-pretty-maybe-expr val))
              key)
         (vl-pretty-atts (cdr x)))))

  (define vl-pretty-exprlist ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-expr (car x))
            (vl-pretty-exprlist (cdr x)))))

  (define vl-pretty-maybe-exprlist ((x vl-maybe-exprlist-p))
    :measure (vl-maybe-exprlist-count x)
    (if (atom x)
        nil
      (if (car x)
          (cons (vl-pretty-expr (car x))
                (vl-pretty-maybe-exprlist (cdr x)))
        (cons nil
              (vl-pretty-maybe-exprlist (cdr x))))))

  (define vl-pretty-call-namedargs ((x vl-call-namedargs-p))
    :measure (vl-call-namedargs-count x)
    (b* ((x (vl-call-namedargs-fix x)))
      (if (atom x)
          nil
        (if (cdar x)
            (cons (list (caar x) (vl-pretty-expr (cdar x)))
                  (vl-pretty-call-namedargs (cdr x)))
          (cons (list (caar x) nil)
                (vl-pretty-call-namedargs (cdr x)))))))

  (define vl-pretty-maybe-expr ((x vl-maybe-expr-p))
    :measure (vl-maybe-expr-count x)
    (if x
        (vl-pretty-expr x)
      nil))

  (define vl-pretty-enumitem ((x vl-enumitem-p))
    :measure (vl-enumitem-count x)
    (b* (((vl-enumitem x) x))
      (append (list x.name)
              (and x.range
                   (list (vl-pretty-maybe-range x.range)))
              (and x.value
                   (list '= (vl-pretty-maybe-expr x.value))))))

  (define vl-pretty-enumitemlist ((x vl-enumitemlist-p))
    :measure (vl-enumitemlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-enumitem (car x))
            (vl-pretty-enumitemlist (cdr x)))))

  (define vl-pretty-range ((x vl-range-p))
    :measure (vl-range-count x)
    (b* (((vl-range x)))
      (list :range
            (vl-pretty-expr x.msb)
            (vl-pretty-expr x.lsb))))

  (define vl-pretty-maybe-range ((x vl-maybe-range-p))
    :measure (vl-maybe-range-count x)
    (if x
        (vl-pretty-range x)
      '(no-range)))

  (define vl-pretty-dimension ((x vl-dimension-p))
    :measure (vl-dimension-count x)
    (vl-dimension-case x
      :unsized :vl-unsized-dimension
      :star    :vl-star-dimension
      :range   (vl-pretty-range x.range)
      :datatype (list :vl-type-dimension (vl-pretty-datatype x.type))
      :queue    (list :vl-queue-dimension (vl-pretty-maybe-expr x.maxsize))))

  (define vl-pretty-dimensionlist ((x vl-dimensionlist-p))
    :measure (vl-dimensionlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-dimension (car x))
            (vl-pretty-dimensionlist (cdr x)))))

  (define vl-pretty-maybe-dimension ((x vl-maybe-dimension-p))
    :measure (vl-maybe-dimension-count x)
    (if x
        (vl-pretty-dimension x)
      nil))

  (define vl-pretty-datatype ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x

      ;; this is messy but we're trying to be compatible without rewriting all the tests
      (:vl-coretype
       (append (list x.name
                     (if x.signedp 'signed 'unsigned))
               (and x.pdims (vl-pretty-dimensionlist x.pdims))
               (and x.udims (cons :udims (vl-pretty-dimensionlist x.udims)))))

      (:vl-struct
       (append '(:vl-struct)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.pdims (cons :dims (vl-pretty-dimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-dimensionlist x.udims)))))

      (:vl-union
       (append '(:vl-union)
               (if x.taggedp '(tagged) nil)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.pdims (cons :dims (vl-pretty-dimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-dimensionlist x.udims)))))

      (:vl-enum
       (append '(:vl-enum)
               (vl-pretty-datatype x.basetype)
               (vl-pretty-enumitemlist x.items)
               (and x.pdims (cons :dims (vl-pretty-dimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-dimensionlist x.udims)))))

      (:vl-usertype
       (append '(:vl-usertype)
               (list (vl-pretty-scopeexpr x.name))
               (and x.pdims (cons :dims (vl-pretty-dimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-dimensionlist x.udims)))))))

  (define vl-pretty-paramargs ((x vl-paramargs-p))
    :measure (vl-paramargs-count x)
    (vl-paramargs-case x
      (:vl-paramargs-named (vl-pretty-namedparamvaluelist x.args))
      (:vl-paramargs-plain (vl-pretty-paramvaluelist x.args))))

  (define vl-pretty-paramvalue ((x vl-paramvalue-p))
    :measure (vl-paramvalue-count x)
    (vl-paramvalue-case x
      (:type (vl-pretty-datatype x.type))
      (:expr (vl-pretty-expr x.expr))))
  
  (define vl-pretty-namedparamvalue ((x vl-namedparamvalue-p))
    :measure (vl-namedparamvalue-count x)
    (b* (((vl-namedparamvalue x)))
      (if x.value 
          (cons x.name (vl-pretty-paramvalue x.value))
        (list x.name))))

  (define vl-pretty-paramvaluelist ((x vl-paramvaluelist-p))
    :measure (vl-paramvaluelist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-paramvalue (car x))
            (vl-pretty-paramvaluelist (cdr x)))))

  (define vl-pretty-namedparamvaluelist ((x vl-namedparamvaluelist-p))
    :measure (vl-namedparamvaluelist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-namedparamvalue (car x))
            (vl-pretty-namedparamvaluelist (cdr x)))))
  

  (define vl-pretty-structmemberlist ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-structmember (car x))
            (vl-pretty-structmemberlist (cdr x)))))

  (define vl-pretty-structmember ((x vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x))
      (append (list x.name)
              (and x.rand (list x.rand))
              (vl-pretty-datatype x.type)
              (and x.rhs
                   (list '= (vl-pretty-maybe-expr x.rhs))))))

  (define vl-pretty-maybe-datatype ((x vl-maybe-datatype-p))
    :measure (vl-maybe-datatype-count x)
    (if x
        (vl-pretty-datatype x)
      nil))

  (define vl-pretty-evatom ((x vl-evatom-p))
    :measure (vl-evatom-count x)
    (b* (((vl-evatom x)))
      (list x.type (vl-pretty-expr x.expr))))

  (define vl-pretty-evatomlist ((x vl-evatomlist-p))
    :measure (vl-evatomlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-evatom (car x))
            (vl-pretty-evatomlist (cdr x))))))


(define vl-pretty-range-list ((x vl-rangelist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-range (car x))
          (vl-pretty-range-list (cdr x)))))

(define vl-pretty-plainarg ((x vl-plainarg-p))
  (let ((expr (vl-plainarg->expr x)))
    (if (not expr)
        :blank
      (vl-pretty-expr expr))))

(define vl-pretty-plainarg-list ((x vl-plainarglist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-plainarg (car x))
          (vl-pretty-plainarg-list (cdr x)))))

(define vl-pretty-namedarg ((x vl-namedarg-p))
  (let ((name (vl-namedarg->name x))
        (expr (vl-namedarg->expr x)))
    (list name '<-- (if expr (vl-pretty-expr expr) :blank))))

(define vl-pretty-namedarg-list ((x vl-namedarglist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-namedarg (car x))
          (vl-pretty-namedarg-list (cdr x)))))

(define vl-pretty-arguments ((x vl-arguments-p))
  (vl-arguments-case x
    :vl-arguments-named
    (list :namedargs (vl-pretty-namedarg-list x.args))
    :vl-arguments-plain
    (list :plainargs (vl-pretty-plainarg-list x.args))))



(define vl-pretty-fwdtypedef ((x vl-fwdtypedef-p))
  (b* (((vl-fwdtypedef x) x))
    (list 'fwdtypedef
          x.kind
          x.name)))

(define vl-pretty-typedef ((x vl-typedef-p))
  (b* (((vl-typedef x) x))
    (list :vl-typedef x.name
          (vl-pretty-datatype x.type))))

(define vl-pretty-type-declaration ((x (or (vl-typedef-p x)
                                           (vl-fwdtypedef-p x))))
  (if (eq (tag x) :vl-fwdtypedef)
      (vl-pretty-fwdtypedef x)
    (vl-pretty-typedef x)))


(define vl-pretty-eventcontrol ((x vl-eventcontrol-p))
  (b* (((vl-eventcontrol x)))
    (if x.starp
        (cons '* (vl-pretty-evatomlist x.atoms))
      (vl-pretty-evatomlist x.atoms))))

(define vl-pretty-delaycontrol ((x vl-delaycontrol-p))
  (vl-pretty-expr (vl-delaycontrol->value x)))

(define vl-pretty-repeateventcontrol ((x vl-repeateventcontrol-p))
  (b* (((vl-repeateventcontrol x)))
    (list :repeat
          (vl-pretty-expr x.expr)
          (vl-pretty-eventcontrol x.ctrl))))

(define vl-pretty-delayoreventcontrol ((x vl-delayoreventcontrol-p))
  (case (tag x)
    (:vl-delaycontrol       (vl-pretty-delaycontrol x))
    (:vl-eventcontrol       (vl-pretty-eventcontrol x))
    (:vl-repeateventcontrol (vl-pretty-repeateventcontrol x))))




(local (defthm vl-distweighttype-p-forward
         (implies (vl-distweighttype-p x)
                  (or (equal x :vl-weight-each)
                      (equal x :vl-weight-total)))
         :rule-classes :forward-chaining))

(local (defthm vl-distitem->type-forward
         (implies (vl-distweighttype-p x)
                  (or (equal x :vl-weight-each)
                      (equal x :vl-weight-total)))
         :rule-classes :forward-chaining))

(define vl-pretty-distitem ((x vl-distitem-p))
  (b* (((vl-distitem x)))
    (append (list (vl-pretty-expr x.left))
            (and x.right
                 (list (vl-pretty-expr x.right)))
            (case x.type
              (:vl-weight-each  '(:=))
              (:vl-weight-total '(:/)))
            (list (vl-pretty-expr x.weight)))))

(defprojection vl-pretty-distlist ((x vl-distlist-p))
  (vl-pretty-distitem x))

(define vl-pretty-exprdist ((x vl-exprdist-p))
  (b* (((vl-exprdist x))
       ((unless (consp x.dist))
        (vl-pretty-expr x.expr)))
    (list* :dist
           (vl-pretty-expr x.expr)
           (vl-pretty-distlist x.dist))))

(define vl-pretty-exprdistlist ((x vl-exprdistlist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-exprdist (car x))
          (vl-pretty-exprdistlist (cdr x)))))

(define vl-pretty-repetition ((x vl-repetition-p))
  (b* (((vl-repetition x)))
    (list* (case x.type
             (:vl-repetition-consecutive    :[*])
             (:vl-repetition-goto           :[->])
             (:vl-repetition-nonconsecutive :[=]))
           (vl-pretty-expr x.left)
           (if x.right
               (list (vl-pretty-expr x.right))
             nil))))

(defines vl-pretty-propexpr

  (define vl-pretty-propexpr ((x vl-propexpr-p))
    :measure (vl-propexpr-count x)
    (vl-propexpr-case x
      (:vl-propcore (vl-pretty-exprdist x.guts))
      (:vl-propinst (list* :inst
                           (vl-pretty-scopeexpr x.ref)
                           (vl-pretty-propactuallist x.args)))
      (:vl-propthen (list :then
                          (vl-pretty-propexpr x.left)
                          (vl-pretty-range x.delay)
                          (vl-pretty-propexpr x.right)))
      (:vl-proprepeat (list :repeat
                            (vl-pretty-propexpr x.seq)
                            (vl-pretty-repetition x.reps)))
      (:vl-propassign (list* :assign
                             (vl-pretty-propexpr x.seq)
                             (vl-pretty-exprlist x.items)))
      (:vl-propthroughout (list :throughout
                                (vl-pretty-exprdist x.left)
                                (vl-pretty-propexpr x.right)))
      (:vl-propclock (list :clock
                           (vl-pretty-evatomlist x.trigger)
                           (vl-pretty-propexpr x.then)))
      (:vl-propunary (list (case x.op
                             (:vl-prop-firstmatch :firstmatch)
                             (:vl-prop-not        :not)
                             (:vl-prop-strong     :strong)
                             (:vl-prop-weak       :weak))
                           (vl-pretty-propexpr x.arg)))
      (:vl-propbinary (list (case x.op
                              (:vl-prop-and           :and)
                              (:vl-prop-intersect     :intersect)
                              (:vl-prop-or            :or)
                              (:vl-prop-within        :within)
                              (:vl-prop-iff           :iff)
                              (:vl-prop-until         :until)
                              (:vl-prop-suntil        :s_until)
                              (:vl-prop-untilwith     :until_with)
                              (:vl-prop-suntilwith    :s_until_with)
                              (:vl-prop-word-implies  :implies)
                              (:vl-prop-thin-implies  :->)
                              (:vl-prop-fat-implies   :=>)
                              (:vl-prop-thin-follows  :#-#)
                              (:vl-prop-fat-follows   :#=#))
                            (vl-pretty-propexpr x.left)
                            (vl-pretty-propexpr x.right)))
      (:vl-propalways (list (if x.strongp :s_always :always)
                            (vl-pretty-maybe-range x.range)
                            (vl-pretty-propexpr x.prop)))
      (:vl-propeventually (list (if x.strongp :s_eventually :eventually)
                                (vl-pretty-maybe-range x.range)
                                (vl-pretty-propexpr x.prop)))
      (:vl-propaccept (list (case x.op
                              (:vl-prop-accepton      :accept_on)
                              (:vl-prop-syncaccepton  :sync_accept_on)
                              (:vl-prop-rejecton      :reject_on)
                              (:vl-prop-syncrejecton  :sync_reject_on))
                            (vl-pretty-exprdist x.condition)
                            (vl-pretty-propexpr x.prop)))
      (:vl-propnexttime (list (if x.strongp :s_nexttime :nexttime)
                              (vl-pretty-maybe-expr x.expr)
                              (vl-pretty-propexpr x.prop)))
      (:vl-propif (list :if
                        (vl-pretty-exprdist x.condition)
                        (vl-pretty-propexpr x.then)
                        (vl-pretty-propexpr x.else)))
      (:vl-propcase (list* :case
                          (vl-pretty-exprdist x.condition)
                          (vl-pretty-propcaseitemlist x.cases)))))

  (define vl-pretty-propactual ((x vl-propactual-p))
    :measure (vl-propactual-count x)
    (vl-propactual-case x
      (:blank (list :blank x.name))
      (:event (list :event x.name '<- (vl-pretty-evatomlist x.evatoms)))
      (:prop  (list :prop x.name '<- (vl-pretty-propexpr x.prop)))))

  (define vl-pretty-propactuallist ((x vl-propactuallist-p))
    :measure (vl-propactuallist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-propactual (car x))
            (vl-pretty-propactuallist (cdr x)))))

  (define vl-pretty-propcaseitem ((x vl-propcaseitem-p))
    :measure (vl-propcaseitem-count x)
    (b* (((vl-propcaseitem x)))
      (list :case
            (vl-pretty-exprdistlist x.match)
            :-->
            (vl-pretty-propexpr x.prop))))

  (define vl-pretty-propcaseitemlist ((x vl-propcaseitemlist-p))
    :measure (vl-propcaseitemlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-propcaseitem (car x))
            (vl-pretty-propcaseitemlist (cdr x))))))


(define vl-pretty-propspec ((x vl-propspec-p))
  (b* (((vl-propspec x)))
    (append (list :propspec (vl-pretty-evatomlist x.evatoms))
            (and x.disable (list :disable (vl-pretty-exprdist x.disable)))
            (list (vl-pretty-propexpr x.prop)))))


(define vl-pretty-assign-type ((x vl-assign-type-p))
  (case x
    (:vl-blocking    :=)
    (:vl-nonblocking :<=)
    (:vl-assign      :assign)
    (:vl-force       :force)))

(define vl-pretty-deassign-type ((x vl-deassign-type-p))
  (case x
    (:vl-deassign :deassign)
    (:vl-release  :release)))

(define vl-pretty-blocktype ((x vl-blocktype-p))
  (case x
    (:vl-beginend     :begin)
    (:vl-forkjoin     :fork)
    (:vl-forkjoinany  :fork-join-any)
    (:vl-forkjoinnone :fork-join-none)))

(define vl-pretty-rhs ((x vl-rhs-p))
  (vl-rhs-case x
    (:vl-rhsexpr (vl-pretty-expr x.guts))
    (:vl-rhsnew (list* :new x.arrsize (vl-pretty-exprlist x.args)))))

(defines vl-pretty-stmt

  (define vl-pretty-stmt ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    (vl-stmt-case x
      :vl-nullstmt :null
      :vl-assignstmt (list* (vl-pretty-expr x.lvalue)
                            (vl-pretty-assign-type x.type)
                            (vl-pretty-rhs x.rhs)
                            (append (and x.ctrl (list :ctrl (vl-pretty-delayoreventcontrol x.ctrl))
                                    (and x.atts (list :atts (vl-pretty-atts x.atts))))))
      :vl-deassignstmt (list* (vl-pretty-deassign-type x.type)
                              (vl-pretty-expr x.lvalue)
                              (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-callstmt (list* :call
                          (vl-pretty-scopeexpr x.id)
                          (append (and x.typearg (list (vl-pretty-datatype x.typearg)))
                                  (vl-pretty-maybe-exprlist x.args)
                                  (and x.systemp (list :system))
                                  (and x.voidp (list :void))
                                  (and x.atts (list :atts (vl-pretty-atts x.atts)))))
      :vl-disablestmt (list* :disable
                             (vl-pretty-scopeexpr x.id)
                             (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-eventtriggerstmt (list* :trigger
                                  (vl-pretty-expr x.id)
                                  (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-casestmt :bozo-case-statements
      :vl-ifstmt (list* :if (vl-pretty-expr x.condition)
                        :then (vl-pretty-stmt x.truebranch)
                        :else (vl-pretty-stmt x.falsebranch)
                        (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-foreverstmt (list* :forever
                             (vl-pretty-stmt x.body)
                             (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-waitstmt (list* :wait
                          (vl-pretty-expr x.condition)
                          (vl-pretty-stmt x.body)
                          (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-repeatstmt (list* :repeat
                            (vl-pretty-expr x.condition)
                            (vl-pretty-stmt x.body)
                            (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-whilestmt (list* :while
                           (vl-pretty-expr x.condition)
                           (vl-pretty-stmt x.body)
                           (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-dostmt (list* :do (vl-pretty-stmt x.body)
                        :while (vl-pretty-expr x.condition)
                        (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-forstmt (list* :for :bozo-for-loops)
      :vl-foreachstmt (list* :foreach
                             (vl-pretty-scopeexpr x.array)
                             :vars x.loopvars
                             :body (vl-pretty-stmt x.body)
                             (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-breakstmt (list* :break
                           (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-continuestmt (list* :continue
                              (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-blockstmt (list* (vl-pretty-blocktype x.blocktype)
                           :name x.name
                           :bozo-declaration-stuff
                           :stmts (vl-pretty-stmtlist x.stmts)
                           (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-timingstmt (list* :timing
                            (vl-pretty-delayoreventcontrol x.ctrl)
                            (vl-pretty-stmt x.body)
                            (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-returnstmt (list* :return
                            (vl-pretty-maybe-expr x.val)
                            (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-assertstmt (list :assert
                           (vl-pretty-assertion x.assertion)
                           (and x.atts (list :atts (vl-pretty-atts x.atts))))
      :vl-cassertstmt (list :cassert
                            (vl-pretty-cassertion x.cassertion)
                            (and x.atts (list :atts (vl-pretty-atts x.atts))))))

  (define vl-pretty-assertion ((x vl-assertion-p))
    :measure (vl-assertion-count x)
    (b* (((vl-assertion x)))
      (list :assert
            x.type
            x.name
            :deferral x.deferral
            :condition (vl-pretty-expr x.condition)
            :success (vl-pretty-stmt x.success)
            :failure (vl-pretty-stmt x.failure))))

  (define vl-pretty-cassertion ((x vl-cassertion-p))
    :measure (vl-cassertion-count x)
    (b* (((vl-cassertion x)))
      (list* :cassert
             x.type
             x.name
             :sequencep x.sequencep
             :condition (vl-pretty-propspec x.condition)
             :success (vl-pretty-stmt x.success)
             :failure (vl-pretty-stmt x.failure))))

  (define vl-pretty-stmtlist ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-stmt (car x))
            (vl-pretty-stmtlist (cdr x))))))


;; A very useful tracing mechanism for debugging:

(defun vl-debug-tokstream (tokstream)
  (declare (xargs :stobjs tokstream
                  :guard-debug t))
  (let* ((tokens (list-fix (vl-tokstream->tokens)))
         (n      (min 5 (len tokens))))
    (vl-tokenlist->string-with-spaces (take n tokens))))

(defmacro trace-parser (fn &key printer)
  `(trace! (,fn
            :entry (list ',fn :tokens (vl-debug-tokstream tokstream))
            :exit (list ',fn
                        :errmsg (with-local-ps (vl-print-warning (first values)))
                        :val ,(if printer
                                  `(with-local-ps (,printer (second values)))
                                `(second values))
                        :remainder (vl-debug-tokstream (third values))))))

