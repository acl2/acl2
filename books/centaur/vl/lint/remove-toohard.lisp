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
(include-book "../mlib/writer")
(include-book "../mlib/allexprs")
(include-book "../mlib/syscalls")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection remove-toohard
  :parents (lint)
  :short "(Unsound transform).  Remove from each module any assignments,
instances, or inital/always blocks that have any \"toohard\" expressions in
them, such as unresolved hierarchical identifiers, strings, function calls,
system functions, and similar."

  :long "<p>This is obviously unsound and should never be used in the ordinary
transformation process.  We use it in our @(see lint)ing tool to prepare
modules for sizing for the linter.</p>")

(local (xdoc::set-default-parents remove-toohard))

(define vl-atom-toohard ((x vl-expr-p))
  :returns (ans "NIL if the atom is okay, or X otherwise."
                (equal (vl-expr-p ans) (if ans t nil)))
  :guard (vl-atom-p x)
  (b* ((x    (vl-expr-fix x))
       (guts (vl-atom->guts x))
       ((when (or (vl-fast-id-p guts)
                  (vl-fast-constint-p guts)
                  (vl-fast-weirdint-p guts)))
        nil))
    x))

(defval *not-toohard-ops*
  :short "Operators that we sort of expect to be able to deal with in the
          linter."
  (list :VL-UNARY-PLUS :VL-UNARY-MINUS :VL-UNARY-LOGNOT
        :VL-UNARY-BITNOT :VL-UNARY-BITAND :VL-UNARY-NAND
        :VL-UNARY-BITOR :VL-UNARY-NOR :VL-UNARY-XOR
        :VL-UNARY-XNOR :VL-BINARY-PLUS :VL-BINARY-MINUS
        :VL-BINARY-TIMES :VL-BINARY-DIV :VL-BINARY-REM
        :VL-BINARY-EQ :VL-BINARY-NEQ :VL-BINARY-CEQ
        :VL-BINARY-CNE :VL-BINARY-LOGAND :VL-BINARY-LOGOR
        :VL-BINARY-POWER :VL-BINARY-LT :VL-BINARY-LTE
        :VL-BINARY-GT :VL-BINARY-GTE :VL-BINARY-BITAND
        :VL-BINARY-BITOR :VL-BINARY-XOR :VL-BINARY-XNOR
        :VL-BINARY-SHR :VL-BINARY-SHL :VL-BINARY-ASHR
        :VL-BINARY-ASHL :VL-QMARK :VL-BITSELECT :VL-PARTSELECT-COLON
        :VL-CONCAT :VL-MULTICONCAT

        ;; Even though these are SystemVerilog things, I don't think they
        ;; will be too hard, since we basically know how to size them...
        :vl-implies :vl-equiv
        :vl-binary-wildeq :vl-binary-wildneq
        ))

(defval *toohard-ops*
  :short "Operators that we don't think we'll be able to handle."
  (list :VL-MINTYPMAX
        :VL-PARTSELECT-PLUSCOLON
        :VL-PARTSELECT-MINUSCOLON
        :VL-FUNCALL
        :VL-SYSCALL
        :VL-HID-DOT
        :vl-index         ;; BOZO we probably need to allow this??
        :vl-select-colon
        :vl-select-pluscolon
        :vl-select-minuscolon
        :vl-scope
        :vl-with-colon
        :vl-with-index
        :vl-with-minuscolon
        :vl-with-pluscolon
        :vl-stream-left
        :vl-stream-left-sized
        :vl-stream-right
        :vl-stream-right-sized
        :vl-tagged

        :vl-binary-cast ;; eventually we should be able to handle these
        :vl-pattern-multi
        :vl-pattern-type
        :vl-pattern-keyvalue
        :vl-pattern-positional
        :vl-keyvalue


        ;; We shouldn't have to handle any of these because we'll have gotten rid
        ;; of them with the elim-increment transform
        :vl-unary-preinc :vl-unary-predec :vl-unary-postinc :vl-unary-postdec
        :vl-binary-assign
        :vl-binary-plusassign :vl-binary-minusassign
        :vl-binary-timesassign :vl-binary-divassign :vl-binary-remassign
        :vl-binary-andassign :vl-binary-orassign :vl-binary-xorassign
        :vl-binary-shlassign :vl-binary-shrassign :vl-binary-ashlassign :vl-binary-ashrassign

        :vl-inside :vl-valuerange :vl-valuerangelist
        ))

(assert! (equal (mergesort (append *toohard-ops* *not-toohard-ops*))
                (mergesort (strip-cars *vl-ops-table*))))

(define vl-op-toohard-p ((x vl-op-p))
  :guard-hints(("Goal" :in-theory (enable vl-op-p)))
  (if (member (vl-op-fix x) *toohard-ops*)
      t
    nil))

(defines vl-expr-toohard-subexpr

  (define vl-expr-toohard-subexpr ((x vl-expr-p))
    :returns (ans "NIL if the expression is okay, or a problematic subexpression
                   if the expression has a problem."
                  (equal (vl-expr-p ans) (if ans t nil)))
    :measure (vl-expr-count x)
    (b* ((x (vl-expr-fix x))
         ((when (vl-fast-atom-p x))
          (vl-atom-toohard x))
         ((when (vl-$random-expr-p x))
          nil)
         ((when (vl-op-toohard-p (vl-nonatom->op x)))
          x))
      (vl-exprlist-toohard-subexpr (vl-nonatom->args x))))

   (define vl-exprlist-toohard-subexpr ((x vl-exprlist-p))
    :returns (ans "NIL if all of the expressions are okay, or a problematic
                   subexpression if the expression has a problem."
                  (equal (vl-expr-p ans) (if ans t nil)))
     :measure (vl-exprlist-count x)
     (if (atom x)
         nil
       (or (vl-expr-toohard-subexpr (car x))
           (vl-exprlist-toohard-subexpr (cdr x))))))

(define vl-assignlist-remove-toohard ((x vl-assignlist-p)
                                      (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-assignlist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings cdr-prime)
        (vl-assignlist-remove-toohard (cdr x) warnings))
       (x1        (vl-assign-fix (car x)))
       (car-exprs (vl-assign-allexprs x1))
       (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
       ((when car-hard)
        (mv (fatal :type :vl-dropped-assign
                   :msg "Deleting ~a0 because it has unsupported ~
                         subexpression ~a1. This deletion may cause our ~
                         analysis to be flawed."
                 :args (list x1 car-hard))
            cdr-prime))
       (x-prime (cons x1 cdr-prime)))
    (mv warnings x-prime)))

(define vl-modinstlist-remove-toohard ((x vl-modinstlist-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-modinstlist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings cdr-prime)
        (vl-modinstlist-remove-toohard (cdr x) warnings))
       (x1        (vl-modinst-fix (car x)))
       (car-exprs (vl-modinst-allexprs x1))
       (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
       ((when car-hard)
        (mv (fatal :type :vl-dropped-modinst
                   :msg "Deleting ~a0 because it has unsupported ~
                         subexpression ~a1. This deletion may cause our ~
                         analysis to be flawed."
                   :args (list x1 car-hard))
            cdr-prime))
       (x-prime (cons x1 cdr-prime)))
    (mv warnings x-prime)))

(define vl-gateinstlist-remove-toohard ((x vl-gateinstlist-p)
                                        (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-gateinstlist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings cdr-prime)
        (vl-gateinstlist-remove-toohard (cdr x) warnings))
       (x1        (vl-gateinst-fix (car x)))
       (car-exprs (vl-gateinst-allexprs x1))
       (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
       ((when car-hard)
        (mv (fatal :type :vl-dropped-gateinst
                   :msg "Deleting ~a0 because it has unsupported ~
                         subexpression ~a1. This deletion may cause our ~
                         analysis to be flawed."
                   :args (list x1 car-hard))
            cdr-prime))
       (x-prime (cons x1 cdr-prime)))
    (mv warnings x-prime)))

(define vl-initiallist-remove-toohard ((x vl-initiallist-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-initiallist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings cdr-prime)
        (vl-initiallist-remove-toohard (cdr x) warnings))
       (x1        (vl-initial-fix (car x)))
       (car-exprs (vl-initial-allexprs x1))
       (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
       ((when car-hard)
        (mv (fatal :type :vl-dropped-initial
                   :msg "Deleting ~a0 because it has unsupported ~
                         subexpression ~a1. This deletion may cause our ~
                         analysis to be flawed."
                   :args (list x1 car-hard))
            cdr-prime))
       (x-prime (cons x1 cdr-prime)))
    (mv warnings x-prime)))

(define vl-alwayslist-remove-toohard ((x vl-alwayslist-p)
                                      (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-alwayslist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings cdr-prime)
        (vl-alwayslist-remove-toohard (cdr x) warnings))
       (x1        (vl-always-fix (car x)))
       (car-exprs (vl-always-allexprs x1))
       (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
       ((when car-hard)
        (mv (fatal :type :vl-dropped-always
                   :msg "Deleting ~a0 because it has unsupported ~
                         subexpression ~a1. This deletion may cause our ~
                         analysis to be flawed."
                   :args (list x1 car-hard))
            cdr-prime))
       (x-prime (cons x1 cdr-prime)))
    (mv warnings x-prime)))

(define vl-module-remove-toohard ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       (warnings x.warnings)
       ((mv warnings assigns)   (vl-assignlist-remove-toohard x.assigns warnings))
       ((mv warnings modinsts)  (vl-modinstlist-remove-toohard x.modinsts warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-remove-toohard x.gateinsts warnings))
       ((mv warnings initials)  (vl-initiallist-remove-toohard x.initials warnings))
       ((mv warnings alwayses)  (vl-alwayslist-remove-toohard x.alwayses warnings)))
    (change-vl-module x
                      :warnings warnings
                      :assigns assigns
                      :modinsts modinsts
                      :gateinsts gateinsts
                      :initials initials
                      :alwayses alwayses)))

(defprojection vl-modulelist-remove-toohard ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-remove-toohard x))

(define vl-design-remove-toohard ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-remove-toohard x.mods))))



#||

; A funny, alternate, not-quite implemented idea.  We might imagine doing
; something to try to throw away only small pieces of expressions that use
; constructs that are too hard.  Here's the start at some code that might do
; this... the basic idea is that if we have an expression that makes use of
; function calls or strings or some such, then we want to get rid of the
; offending parts of the expression with as little damage as possible.  It
; might be best to change something like "A + HARD" into A, instead of throwing
; away the whole module element that mentions it.



(deflist vl-maybe-exprlist-p (x)
  (vl-maybe-expr-p x)
  :guard t)

(defconst *toohard-x*
  (make-vl-atom :guts (make-vl-weirdint :width 1
                                        :signedp nil
                                        :bits (list :vl-xval))))

(defund vl-op-eliminate-toohard (op args)
  (declare (xargs :guard (and (vl-op-p op)
                              (vl-maybe-exprlist-p args)
                              (vl-atts-p atts)
                              (or (not (vl-op-arity op))
                                  (equal (len args) (vl-op-arity op))))))
  (case op

    ((:vl-unary-plus :vl-unary-minus :vl-unary-lognot :vl-unary-bitnot
                     :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
                     :vl-unary-xor :vl-unary-xnor)
     (b* (((list a) args))
       (cond (a
              ;; [op] A --> [op] A
              (make-vl-nonatom :op op :atts atts :args (list a)))
             (t
              ;; [op] HARD --> HARD
              nil))))

    ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
                      :vl-binary-rem :vl-binary-eq :vl-binary-neq :vl-binary-ceq
                      :vl-binary-cne :vl-binary-logand :vl-binary-logor :vl-binary-power
                      :vl-binary-lt :vl-binary-lte :vl-binary-gte :vl-binary-gte
                      :vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor
                      :vl-binary-shr :vl-binary-shl :vl-binary-ashr
                      :vl-binary-ashl)
     (b* (((list a b) args))
       (cond ((and a b)               ;; A [op] B --> A [op] B
              (make-vl-nonatom :op op :atts atts :args (list a b)))
             ((and (not a) (not b))   ;; HARD [op] HARD --> HARD
              nil)
             ((not a)                 ;; HARD [op] B --> B
              b)
             ((not b)                 ;; A [op] HARD --> B
              a)
             (t (er hard 'vl-op-eliminate-toohard "Impossible")))))

    ((:vl-funcall :vl-syscall :vl-mintypmax :vl-hid-dot :vl-index
                  :vl-partselect-pluscolon :vl-partselect-minuscolon)
     ;; Automatically hard always hard.
     nil)

    (:vl-qmark
     (b* (((list a b c) args))
       (cond ((and a b c)
              ;; A ? B : C --> A ? B : C
              (make-vl-nonatom :op op :atts atts :args (list a b c)))
             ((and (not b) (not c))
              ;; __ ? HARD : HARD --> HARD
              nil)
             ((and (not a) (not b))
              ;; HARD ? HARD : C --> C
              c)
             ((and (not a) (not c))
              ;; HARD ? B : HARD --> B
              b)
             ((not a)
              ;; HARD ? B : C --> 1'bX ? B : C
              (make-vl-nonatom :op op :atts atts :args (list *toohard-x* b c)))
             ((not b)
              ;; A ? HARD : C --> A ? C : C
              (make-vl-nonatom :op op :atts atts :args (list a c c)))
             ((not c)
              ;; A ? B : HARD --> A ? B : B
              (make-vl-nonatom :op op :atts atts :args (list a b b)))
             (t
              (er hard 'vl-op-eliminate-toohard "Impossible")))))

    ((:vl-bitselect)
     (b* (((list a b) args))
       (cond ((and a b)
              ;; A[B] --> A[B]
              (make-vl-nonatom :op op :atts atts :args (list a b)))
             (t
              ;; HARD[B] or A[HARD] --> HARD.
              nil))))

    ((:vl-partselect-colon)
     (b* (((list a b c) args))
       (cond ((and a b c)
              ;; A[B:C] --> A[B:C]
              (make-vl-nonatom :op op :atts atts :args (list a b c)))
             (t
              ;; HARD[__:__] or A[HARD:__] or A[__:HARD] --> HARD
              nil))))

    ((:vl-multiconcat)
     (




(defun vl-expr-eliminate-toohard (x)
  ;; Returns a VL-MAYBE-EXPR-P.
  (if


; expressions are "too hard" to have their widths decided.  We basically want
; to
; These removal functions should be called AFTER the hid elimination has
; flattened any HIDs that were properly resolved.  They throw away any module
; elements that still have HIDs.

(defsection vl-expr-toohard-p

;

(defun vl-expr-toohard-p (x)


||#


