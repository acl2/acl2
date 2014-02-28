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
(include-book "../mlib/writer")
(include-book "../mlib/allexprs")
(local (include-book "../util/arithmetic"))

(defsection remove-toohard
  :parents (lint)
  :short "(Unsound transform).  Remove from each module any assignments,
instances, or inital/always blocks that have any \"toohard\" expressions in
them, such as unresolved hierarchical identifiers, strings, function calls,
system functions, and similar."

  :long "<p>This is obviously unsound and should never be used in the ordinary
transformation process.  We use it in our @(see lint)ing tool to prepare
modules for sizing for the linter.</p>")

(defsection vl-atom-toohard
  :parents (remove-toohard)

  (defund vl-atom-toohard (x)
    ;; Returns NIL if the atom is okay, or X otherwise.
    (declare (xargs :guard (vl-atom-p x)))
    (let ((guts (vl-atom->guts x)))
      (if (or (vl-fast-id-p guts)
              (vl-fast-constint-p guts)
              (mbe :logic (vl-weirdint-p guts)
                   :exec (eq (tag guts) :vl-weirdint)))
          nil
        x)))

  (defthm vl-expr-p-of-vl-atom-toohard
    (implies (force (vl-atom-p x))
             (equal (vl-expr-p (vl-atom-toohard x))
                    (if (vl-atom-toohard x)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-atom-toohard)))))

(defsection vl-expr-toohard-subexpr
  :parents (remove-toohard)

  (defconst *not-toohard-ops*
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

  (defconst *toohard-ops*
    (list :VL-MINTYPMAX
          :VL-PARTSELECT-PLUSCOLON
          :VL-PARTSELECT-MINUSCOLON
          :VL-ARRAY-INDEX
          :VL-FUNCALL
          :VL-SYSCALL
          :VL-HID-DOT
          :vl-index
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
          ))

  (assert! (equal (mergesort (append *toohard-ops* *not-toohard-ops*))
                  (mergesort (strip-cars *vl-ops-table*))))

  (defund vl-op-toohard-p (x)
    (declare (xargs :guard (vl-op-p x)
                    :guard-hints(("Goal" :in-theory (enable vl-op-p)))))
    (if (member x *toohard-ops*)
        t
      nil))

  (mutual-recursion

   (defund vl-expr-toohard-subexpr (x)
     ;; Returns NIL if the expression is okay, or a problematic subexpression if
     ;; the expression has a problem.
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atom-p x)
            (vl-atom-toohard x))
           ((vl-$random-expr-p x)
            nil)
           ((vl-op-toohard-p (vl-nonatom->op x))
            x)
           (t
            (vl-exprlist-toohard-subexpr (vl-nonatom->args x)))))

   (defund vl-exprlist-toohard-subexpr (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (or (vl-expr-toohard-subexpr (car x))
           (vl-exprlist-toohard-subexpr (cdr x))))))

  (flag::make-flag flag-vl-expr-toohard-subexpr
                   vl-expr-toohard-subexpr
                   :flag-mapping ((vl-expr-toohard-subexpr . expr)
                                  (vl-exprlist-toohard-subexpr . list)))

  (defthm-flag-vl-expr-toohard-subexpr
    (defthm vl-expr-p-of-vl-expr-toohard-subexpr
      (implies (force (vl-expr-p x))
               (equal (vl-expr-p (vl-expr-toohard-subexpr x))
                      (if (vl-expr-toohard-subexpr x)
                          t
                        nil)))
      :flag expr)
    (defthm vl-expr-p-of-vl-exprlist-toohard-subexpr
      (implies (force (vl-exprlist-p x))
               (equal (vl-expr-p (vl-exprlist-toohard-subexpr x))
                      (if (vl-exprlist-toohard-subexpr x)
                          t
                        nil)))
      :flag list)
    :hints(("Goal"
            :expand ((vl-expr-toohard-subexpr x)
                     (vl-exprlist-toohard-subexpr x))))))




(defsection vl-assignlist-remove-toohard
  :parents (remove-toohard)

  (defund vl-assignlist-remove-toohard (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((mv warnings cdr-prime)
          (vl-assignlist-remove-toohard (cdr x) warnings))
         (car-exprs (vl-assign-allexprs (car x)))
         (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
         ((when car-hard)
          (b* ((w (make-vl-warning
                   :type :vl-dropped-assign
                   :msg "Deleting ~a0 because it has unsupported subexpression ~a1. ~
                         This deletion may cause our analysis to be flawed."
                   :args (list (car x) car-hard)
                   :fatalp t
                   :fn 'vl-assignlist-remove-toohard)))
            (mv (cons w warnings) cdr-prime)))
         (x-prime (cons (car x) cdr-prime)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-assignlist-remove-toohard)))

  (defthm vl-warninglist-p-of-vl-assignlist-remove-toohard
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-assignlist-remove-toohard x warnings)))))

  (defthm vl-assignlist-p-of-vl-assignlist-remove-toohard
    (implies (force (vl-assignlist-p x))
             (vl-assignlist-p
              (mv-nth 1 (vl-assignlist-remove-toohard x warnings))))))



(defsection vl-modinstlist-remove-toohard
  :parents (remove-toohard)

  (defund vl-modinstlist-remove-toohard (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((mv warnings cdr-prime)
          (vl-modinstlist-remove-toohard (cdr x) warnings))
         (car-exprs (vl-modinst-allexprs (car x)))
         (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
         ((when car-hard)
          (b* ((w (make-vl-warning
                   :type :vl-dropped-modinst
                   :msg "Deleting ~a0 because it has unsupported subexpression ~a1. ~
                         This deletion may cause our analysis to be flawed."
                   :args (list (car x) car-hard)
                   :fatalp t
                   :fn 'vl-modinstlist-remove-toohard)))
            (mv (cons w warnings) cdr-prime)))
         (x-prime (cons (car x) cdr-prime)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-modinstlist-remove-toohard)))

  (defthm vl-warninglist-p-of-vl-modinstlist-remove-toohard
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinstlist-remove-toohard x warnings)))))

  (defthm vl-modinstlist-p-of-vl-modinstlist-remove-toohard
    (implies (force (vl-modinstlist-p x))
             (vl-modinstlist-p
              (mv-nth 1 (vl-modinstlist-remove-toohard x warnings))))))



(defsection vl-gateinstlist-remove-toohard
  :parents (remove-toohard)

  (defund vl-gateinstlist-remove-toohard (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((mv warnings cdr-prime)
          (vl-gateinstlist-remove-toohard (cdr x) warnings))
         (car-exprs (vl-gateinst-allexprs (car x)))
         (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
         ((when car-hard)
          (b* ((w (make-vl-warning
                   :type :vl-dropped-gateinst
                   :msg "Deleting ~a0 because it has unsupported subexpression ~a1. ~
                         This deletion may cause our analysis to be flawed."
                   :args (list (car x) car-hard)
                   :fatalp t
                   :fn 'vl-gateinstlist-remove-toohard)))
            (mv (cons w warnings) cdr-prime)))
         (x-prime (cons (car x) cdr-prime)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-gateinstlist-remove-toohard)))

  (defthm vl-warninglist-p-of-vl-gateinstlist-remove-toohard
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-gateinstlist-remove-toohard x warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gateinstlist-remove-toohard
    (implies (force (vl-gateinstlist-p x))
             (vl-gateinstlist-p
              (mv-nth 1 (vl-gateinstlist-remove-toohard x warnings))))))



(defsection vl-initiallist-remove-toohard
  :parents (remove-toohard)

  (defund vl-initiallist-remove-toohard (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-initiallist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((mv warnings cdr-prime)
          (vl-initiallist-remove-toohard (cdr x) warnings))
         (car-exprs (vl-initial-allexprs (car x)))
         (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
         ((when car-hard)
          (b* ((w (make-vl-warning
                   :type :vl-dropped-initial
                   :msg "Deleting ~a0 because it has unsupported subexpression ~a1. ~
                         This deletion may cause our analysis to be flawed."
                   :args (list (car x) car-hard)
                   :fatalp t
                   :fn 'vl-initiallist-remove-toohard)))
            (mv (cons w warnings) cdr-prime)))
         (x-prime (cons (car x) cdr-prime)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-initiallist-remove-toohard)))

  (defthm vl-warninglist-p-of-vl-initiallist-remove-toohard
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-initiallist-remove-toohard x warnings)))))

  (defthm vl-initiallist-p-of-vl-initiallist-remove-toohard
    (implies (force (vl-initiallist-p x))
             (vl-initiallist-p
              (mv-nth 1 (vl-initiallist-remove-toohard x warnings))))))



(defsection vl-alwayslist-remove-toohard
  :parents (remove-toohard)

  (defund vl-alwayslist-remove-toohard (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-alwayslist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil))
         ((mv warnings cdr-prime)
          (vl-alwayslist-remove-toohard (cdr x) warnings))
         (car-exprs (vl-always-allexprs (car x)))
         (car-hard  (vl-exprlist-toohard-subexpr car-exprs))
         ((when car-hard)
          (b* ((w (make-vl-warning
                   :type :vl-dropped-always
                   :msg "Deleting ~a0 because it has unsupported subexpression ~a1. ~
                         This deletion may cause our analysis to be flawed."
                   :args (list (car x) car-hard)
                   :fatalp t
                   :fn 'vl-alwayslist-remove-toohard)))
            (mv (cons w warnings) cdr-prime)))
         (x-prime (cons (car x) cdr-prime)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-alwayslist-remove-toohard)))

  (defthm vl-warninglist-p-of-vl-alwayslist-remove-toohard
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-alwayslist-remove-toohard x warnings)))))

  (defthm vl-alwayslist-p-of-vl-alwayslist-remove-toohard
    (implies (force (vl-alwayslist-p x))
             (vl-alwayslist-p
              (mv-nth 1 (vl-alwayslist-remove-toohard x warnings))))))



(defsection vl-module-remove-toohard
  :parents (remove-toohard)

  (defund vl-module-remove-toohard (x)
    "Returns X-PRIME"
    (declare (xargs :guard (vl-module-p x)))
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

  (local (in-theory (enable vl-module-remove-toohard)))

  (defthm vl-module-p-of-vl-module-remove-toohard
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-remove-toohard x))))

  (defthm vl-module->name-of-vl-module-remove-toohard
    (equal (vl-module->name (vl-module-remove-toohard x))
           (vl-module->name x))))


(defprojection vl-modulelist-remove-toohard (x)
  (vl-module-remove-toohard x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (remove-toohard)
  :rest ((defthm vl-modulelist->names-of-vl-modulelist-remove-toohard
           (equal (vl-modulelist->names (vl-modulelist-remove-toohard x))
                  (vl-modulelist->names x)))))


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


