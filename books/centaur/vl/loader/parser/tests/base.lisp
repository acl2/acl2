; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "../../lexer/lexer") ;; for make-test-tokens, etc.
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
      (:colon (list :scope
                    (vl-pretty-scopename x.first)
                    (vl-pretty-scopeexpr x.rest)))))

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
      (:range (vl-pretty-range x.range))
      (:single (vl-pretty-expr x.expr))))

  (define vl-pretty-valuerangelist ((x vl-valuerangelist-p))
    :measure (vl-valuerangelist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-valuerange (car x))
            (vl-pretty-valuerangelist (cdr x)))))

  (define vl-pretty-patternkey ((x vl-patternkey-p))
    :measure (vl-patternkey-count x)
    (vl-patternkey-case x
      (:expr (vl-pretty-expr x.key))
      (:type (vl-pretty-datatype x.type))
      (:default :vl-default)))

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
    (vl-expr-case x
      :vl-special (vl-pretty-specialkey x.key)
      :vl-literal (vl-pretty-value x.val)
      :vl-index
      (b* (((when (vl-idexpr-p x))
            (list 'id (vl-idexpr->name x))))
        (list :index
              (vl-pretty-atts x.atts)
              (vl-pretty-scopeexpr x.scope)
              (vl-pretty-exprlist x.indices)
              (vl-pretty-partselect x.part)))
      :vl-unary   (list x.op
                        (vl-pretty-atts x.atts)
                        (vl-pretty-expr x.arg))
      :vl-binary  (list x.op
                        (vl-pretty-atts x.atts)
                        (vl-pretty-expr x.left)
                        (vl-pretty-expr x.right))
      :vl-qmark   (list :vl-qmark
                        (vl-pretty-atts x.atts)
                        (vl-pretty-expr x.test)
                        (vl-pretty-expr x.then)
                        (vl-pretty-expr x.else))
      :vl-mintypmax (list :vl-mintypmax
                          (vl-pretty-atts x.atts)
                          (vl-pretty-expr x.min)
                          (vl-pretty-expr x.typ)
                          (vl-pretty-expr x.max))
      :vl-concat (list* :vl-concat
                        (vl-pretty-atts x.atts)
                        (vl-pretty-exprlist x.parts))
      :vl-multiconcat (list* :vl-multiconcat
                             (vl-pretty-atts x.atts)
                             (vl-pretty-expr x.reps)
                             (vl-pretty-exprlist x.parts))
      :vl-stream (list* (if (eq x.dir :left)
                            :vl-stream-left
                          :vl-stream-right)
                        (vl-pretty-atts x.atts)
                        (if (vl-slicesize-case x.size :none)
                            (vl-pretty-streamexprlist x.parts)
                          (cons (vl-pretty-slicesize x.size)
                                (vl-pretty-streamexprlist x.parts))))
      :vl-call (list* (if x.systemp :vl-syscall :vl-funcall)
                      (vl-pretty-atts x.atts)
                      (vl-pretty-scopeexpr x.name)
                      (if x.typearg
                          (cons (vl-pretty-maybe-datatype x.typearg)
                                (vl-pretty-exprlist x.args))
                        (vl-pretty-exprlist x.args)))
      :vl-cast (list :cast
                     (vl-pretty-atts x.atts)
                     (vl-pretty-casttype x.to)
                     (vl-pretty-expr x.expr))
      :vl-inside (list* :inside
                        (vl-pretty-atts x.atts)
                        (vl-pretty-expr x.elem)
                        (vl-pretty-valuerangelist x.set))
      :vl-tagged (list* :vl-tagged
                        (vl-pretty-atts x.atts)
                        x.tag
                        (if x.expr
                            (list (vl-pretty-maybe-expr x.expr))
                          nil))
      :vl-pattern (list* :pattern
                         (vl-pretty-atts x.atts)
                         (vl-pretty-maybe-datatype x.pattype)
                         (vl-pretty-assignpat x.pat))))

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

  (define vl-pretty-packeddimension ((x vl-packeddimension-p))
    :measure (vl-packeddimension-count x)
    (vl-packeddimension-case x
      :unsized :vl-unsized-dimension
      :range   (vl-pretty-range x.range)))

  (define vl-pretty-packeddimensionlist ((x vl-packeddimensionlist-p))
    :measure (vl-packeddimensionlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-packeddimension (car x))
            (vl-pretty-packeddimensionlist (cdr x)))))

  (define vl-pretty-maybe-packeddimension ((x vl-maybe-packeddimension-p))
    :measure (vl-maybe-packeddimension-count x)
    (if x
        (vl-pretty-packeddimension x)
      nil))

  (define vl-pretty-datatype ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x

      ;; this is messy but we're trying to be compatible without rewriting all the tests
      (:vl-coretype
       (append (list x.name
                     (if x.signedp 'signed 'unsigned))
               (and x.pdims (vl-pretty-packeddimensionlist x.pdims))
               (and x.udims (cons :udims (vl-pretty-packeddimensionlist x.udims)))))

      (:vl-struct
       (append '(:vl-struct)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.pdims (cons :dims (vl-pretty-packeddimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-packeddimensionlist x.udims)))))

      (:vl-union
       (append '(:vl-union)
               (if x.taggedp '(tagged) nil)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.pdims (cons :dims (vl-pretty-packeddimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-packeddimensionlist x.udims)))))

      (:vl-enum
       (append '(:vl-enum)
               (vl-pretty-datatype x.basetype)
               (vl-pretty-enumitemlist x.items)
               (and x.pdims (cons :dims (vl-pretty-packeddimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-packeddimensionlist x.udims)))))

      (:vl-usertype
       (append '(:vl-usertype)
               (list (vl-pretty-scopeexpr x.name))
               (and x.pdims (cons :dims (vl-pretty-packeddimensionlist x.pdims)))
               (and x.udims (cons :udims (vl-pretty-packeddimensionlist x.udims)))))))

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
      nil)))

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


(define vl-pretty-evatom ((x vl-evatom-p))
  (b* (((vl-evatom x)))
    (list x.type (vl-pretty-expr x.expr))))

(define vl-pretty-evatomlist ((x vl-evatomlist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-evatom (car x))
          (vl-pretty-evatomlist (cdr x)))))

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

