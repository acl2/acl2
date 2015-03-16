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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "vl-expr")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))

(local (in-theory (disable 
        (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-CORETYPE)
        (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-ENUM)
        (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-STRUCT)
        (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-UNION)
        (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-USERTYPE)
        (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-CORETYPE)
        (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-ENUM)
        (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-STRUCT)
        (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-UNION)
        (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-USERTYPE)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-BINARY)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-CALL)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-CAST)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-CONCAT)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-INDEX)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-INSIDE)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-MINTYPMAX)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-MULTICONCAT)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-PATTERN)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-QMARK)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-SPECIAL)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-STREAM)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-TAGGED)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-UNARY)
        (:REWRITE VL-EXPR-TYPE-WHEN-VL-VALUE))))

(local (in-theory (disable (tau-system)
                           vl-warninglist-p-when-subsetp-equal
                           vl-warninglist-p-when-not-consp
                           double-containment
                           not)))



(defprod vl-paramref
  ((name svex::svar-p)
   (expr vl-expr-p)
   (type vl-datatype-p)
   (ss   vl-scopestack-p)))

(fty::deflist vl-paramreflist :elt-type vl-paramref)



(define vl-expr-toplevel-parameter-ref ((x vl-expr-p)
                                        (ss vl-scopestack-p))
  :returns (params (and (vl-paramreflist-p params)
                        (setp params)))
  (vl-expr-case x
    :vl-index (b* (((mv err opinfo) (vl-index-expr-typetrace x ss))
                   ((when err) nil)
                   ((vl-operandinfo opinfo))
                   ((vl-hidstep decl) (car opinfo.hidtrace))
                   ((unless (eq (tag decl.item) :vl-paramdecl))
                    nil)
                   ((vl-paramdecl decl.item)))
                (vl-paramtype-case decl.item.type
                  :vl-explicitvalueparam
                  (b* (((unless decl.item.type.default) nil)
                       ((unless (vl-hidtrace-resolved-p opinfo.hidtrace)) nil)
                       ((mv err name) (vl-seltrace-to-svar nil opinfo ss))
                       ((when err) nil))
                    (set::insert
                     (make-vl-paramref
                      :name name
                      :expr decl.item.type.default
                      :type decl.item.type.type
                      :ss decl.ss)
                     nil))
                  :otherwise nil))
    :otherwise nil))


(fty::defvisitor-template parameter-refs ((x :object)
                                          (ss vl-scopestack-p))
  :returns (params (:join (union params1 params)
                    :tmp-var params1
                    :initial nil)
                   (and (vl-paramreflist-p params)
                        (setp params)))
  :type-fns ((vl-expr vl-expr-parameter-refs)) ;; not defined yet!
  :field-fns ((atts :skip))
  :fnname-template <type>-parameter-refs)

(fty::defvisitor-for-deftype vl-datatype-parameter-refs
  :type expressions-and-datatypes  :template parameter-refs
  :measure (two-nats-measure :count 0)

  ;; The autogenerated vl-expr visitor becomes vl-expr-subexpr-parameter-refs,
  ;; which traverses it but doesn't get the top-level reference.  This fixes it
  ;; by adding in the toplevel reference, if any.
  (define vl-expr-parameter-refs ((x vl-expr-p)
                                       (ss vl-scopestack-p))
    :returns (params (and (vl-paramreflist-p params)
                          (setp params)))
    :measure (two-nats-measure (vl-expr-count x) 1)
    (union (vl-expr-toplevel-parameter-ref x ss)
           (vl-expr-subexpr-parameter-refs x ss)))

  :renames ((vl-expr vl-expr-subexpr-parameter-refs)))


(fty::defvisitor vl-parameter-refs
  :template parameter-refs
  :types vl-design)
