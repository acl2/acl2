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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "../../mlib/hid-tools")
(local (include-book "../../util/default-hints"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


;; Certain constructs in SystemVerilog may either be a type or expression.  We
;; can't easily tell the difference at parse time, but once we have a full
;; module hierarchy we can use scopestacks to determine which is which.  In the
;; parser, we always parse an expression if possible and then a datatype if
;; that doesn't work, so we only need to convert expressions to datatypes, not
;; vice versa.

(define vl-expr-to-datatype ((x vl-expr-p)
                             (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p
                         "Warning if we couldn't make sense of something.")
               (type (iff (vl-datatype-p type) type)
                     "The resulting datatype, if it is one."))
  (b* ((warnings nil)
       (x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-index (b* (((mv err trace ?context tail)
                      (vl-follow-scopeexpr x.scope ss))
                     ((when err)
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Couldn't look up variable ~a0: ~@1"
                                :args (list x err))
                          nil))
                     ((vl-hidstep decl) (car trace))
                     ((unless (or (eq (tag decl.item) :vl-typedef)
                                  (eq (tag decl.item) :vl-paramdecl)))
                      ;; not a type
                      (mv nil nil))
                     ((when (and (eq (tag decl.item) :vl-paramdecl)
                                 (b* (((vl-paramdecl param) decl.item))
                                   (not (vl-paramtype-case param.type :vl-typeparam)))))
                      (mv nil nil))
                     ;; We have either a typedef or paramdecl.  It's weird if we
                     ;; have indices.  It might be a little less weird to have a
                     ;; partselect bc it could look like a packed dimension, but
                     ;; I don't think it's allowed and it'd still be weird if
                     ;; e.g. the type was unpacked.
                     ((when (consp x.indices))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with indices: ~a0"
                                :args (list x))
                          nil))
                     ((unless (vl-partselect-case x.part :none))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with partselect: ~a0"
                                :args (list x))
                          nil))
                     ;; It's also weird if there's a tail, i.e. some sort of
                     ;; selects into the type.
                     ((unless (vl-hidexpr-case tail :end))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with field selects: ~a0"
                                :args (list x))
                          nil)))
                  (mv nil (make-vl-usertype :name x.scope)))
      :otherwise (mv nil nil))))



(define vl-call-type-disambiguate (systemp
                                   (typearg vl-maybe-datatype-p)
                                   (plainargs vl-maybe-exprlist-p)
                                   (ss vl-scopestack-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-typearg vl-maybe-datatype-p)
               (new-plainargs vl-maybe-exprlist-p))
  (if (and systemp (not typearg) (consp plainargs) (car plainargs))
      (b* ((warnings nil)
           ((wmv warnings typearg)
            (vl-expr-to-datatype (car plainargs) ss)))
        (if typearg
            (mv warnings typearg (vl-maybe-exprlist-fix (cdr plainargs)))
          (mv warnings nil (vl-maybe-exprlist-fix plainargs))))
    (mv nil
        (vl-maybe-datatype-fix typearg)
        (vl-maybe-exprlist-fix plainargs))))

(define vl-expr-type-disambiguate1 ((x vl-expr-p)
                                    (ss vl-scopestack-p)
                                    (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-expr-p))
  (b* ((warnings (vl-warninglist-fix warnings)))
    (vl-expr-case x
                  :vl-call (if (and x.systemp (not x.typearg) (consp x.plainargs) (car x.plainargs))
                               ;; System calls' first argument may be a type
                               (b* (((wmv warnings typearg)
                                     (vl-expr-to-datatype (car x.plainargs) ss)))
                                 (mv warnings
                                     (if typearg
                                         (change-vl-call x :typearg typearg :plainargs (cdr x.plainargs))
                                       (vl-expr-fix x))))
                             (mv warnings (vl-expr-fix x)))
                  :otherwise (mv warnings (vl-expr-fix x)))))
