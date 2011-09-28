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
(include-book "gen-adder")
(include-book "gen-compare")
(include-book "gen-mul")
(include-book "gen-select")
(include-book "gen-shl")
(include-book "gen-shr")
(include-book "gen-simple")
(include-book "gen-xdet")
(include-book "../../mlib/expr-slice")
(include-book "../../mlib/namefactory")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))


(defconst *vl-occform-memoize*
  '(vl-make-n-bit-binary-op
    vl-make-n-bit-assign
    vl-make-n-bit-not
    vl-make-n-bit-reduction-op
    vl-make-n-bit-mux
    vl-make-n-bit-zmux
    vl-make-n-bit-ceq
    vl-make-n-bit-adder-core
    vl-make-n-bit-plusminus
    vl-make-n-bit-unsigned-gte
    vl-make-n-bit-signed-gte
    vl-make-n-bit-mult
    vl-make-2^n-bit-dynamic-bitselect
    vl-make-n-bit-dynamic-bitselect
    vl-make-n-bit-dynamic-bitselect-m
    vl-make-n-bit-shl-place-p
    vl-make-n-bit-shl-by-m-bits
    vl-make-n-bit-shr-place-p
    vl-make-n-bit-shr-by-m-bits
    vl-make-n-bit-xdetect
    vl-make-n-bit-xor-each
    vl-make-n-bit-x-propagator))

(defun memoize-list-fn (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(memoize ',(car x))
          (memoize-list-fn (cdr x)))))

(defmacro memoize-list (x)
  `(make-event
    (b* ((fns   ,x)
         (-     (or (not fns)
                    (cw "Memoizing ~&0.~%" fns)))
         (forms (memoize-list-fn fns)))
      `(with-output :off (summary)
         (progn . ,forms)))))

(memoize-list *vl-occform-memoize*)

(defun clear-these-memoize-tables (fns)
  (declare (xargs :guard t))
  (if (atom fns)
      nil
    (prog2$ (clear-memoize-table (car fns))
            (clear-these-memoize-tables (cdr fns)))))



;; BOZO we probably want to memoize the generators and possibly have all of the generators produce honsed modules.
;; If all of the new-modules are honsed, then the mergesort here should be really fast
;;   - the EQUAL check in FAST-UNION will be quickly YES by pointer-equality or quickly NO by module-name mismatch
;;   - the << checks in FAST-UNION will be quickly settled by module-name comparison
;; But if there are EQUAL-but-not-EQ modules, the EQUAL checks could become quite expensive.

;; BOZO try to standardize the parameter-names in generated modules into some
;; common scheme, e.g., "out" versus "o", etc.

;; BOZO any generators that can be improved by using bustable exprs?  Shifting was improved a lot by using part-selects
;; instead of lots of stupid buffers.  I think the partial-product generation for multiplication can also be patched
;; up like this.  Searching for "buf" might be a good start toward looking at these.

;; BOZO many generators could also probably switch to instance muxes instead of laying down their own gates to do
;; muxing, which could make their function more clear

;; BOZO are we handling signed things correctly?  need regressions and similar.

;; BOZO these width-checks could probably be turned into welltyped-assign-p checks or similar, if we had such
;; a concept and all of the relevant theorems about it.


(defxdoc occform
  :parents (transforms)
  :short "Transform assignments into occurrences."

  :long "<p>We now introduce routines to transform post-@(see split)
assignments into occurrences of new, primitive modules.</p>

<p>We expect to see assignments of the form:</p>

<code>
    assign LVALUE = EXPR ;
</code>

<p>where <tt>EXPR</tt> consists either of a single operand or of a single
operation applied to operands.  We expect to not encounter certain operators
such as <tt>==</tt> and <tt>||</tt> which are handled by @(see oprewrite).</p>

<p>We typically replace each assignment with an instance of a newly-generated
module.  For instance, if our operation is <tt>a + b</tt>, where the operation
is being done in <tt>n</tt> bits, we introduce a new <tt>VL_N_BIT_PLUS</tt>
module, and replace the assignment with an instance of this module.</p>

<p>Each of our <tt>-occform</tt> functions takes as arguments:</p>

<ul>
<li><tt>x</tt>, an assignment that typically must be of some particular
form,</li>
<li><tt>nf</tt>, a @(see vl-namefactory-p) to use when generating new names,
and</li>
<li><tt>warnings</tt>, an ordinary @(see warnings) accumulator.</li>
</ul>

<p>And returns <tt>(mv new-warnings new-modules new-modinsts new-nf)</tt>,
where:</p>

<ul>

<li><tt>new-warnings</tt> is the new warnings accumulator which has been
extended with any warnings,</li>

<li><tt>new-modules</tt> are any newly generated modules that need to be added
so that we can instantiate them---that is, this list will define modules like
<tt>VL_13_BIT_PLUS</tt> that will be used to replace this assignment,</li>

<li><tt>new-modinsts</tt> and <tt>new-assigns</tt> are any new module instances
and assignments that, taken together, can replace <tt>x</tt>, and</li>

<li><tt>new-nf</tt> is the updated @(see vl-namefactory-p) that is used to
generate module instance names.</li>

</ul>

<p>Typically <tt>new-assigns</tt> will be empty on success, and will just be
<tt>(list x)</tt> on failure.</p>")

(defmacro def-vl-occform (name &key
                               (parents '(occform))
                               (short '"")
                               (long '"")
                               ops
                               body
                               (guard 't)
                               guard-debug)
  (declare (xargs :guard (and (symbolp name)
                              (vl-oplist-p ops))))
  (let ((mksym-package-symbol name))
    `(defsection ,name
       :parents ,parents
       :short ,short
       :long ,(str::cat "<p><b>Signature:</b> @(call " (symbol-name name) ")
produces <tt>(mv new-warnings new-modules new-modinsts new-n)</tt>, as
described in @(see occform).</p>" long)

       (defund ,name (x nf warnings)
         "Returns (mv new-warnings new-modules new-modinsts new-gateinsts new-nf)"
         (declare (xargs :guard (and (vl-assign-p x)
                                     ,@(and ops
                                            `((not (vl-atom-p (vl-assign->expr x)))
                                              (member (vl-nonatom->op (vl-assign->expr x)) ',ops)))
                                     ,guard
                                     (vl-namefactory-p nf)
                                     (vl-warninglist-p warnings))
                         :guard-debug ,guard-debug))
         ,body)

       (local (in-theory (enable ,name)))

       (defthm ,(mksym 'vl-warninglist-p-of- name)
         (implies (force (vl-warninglist-p warnings))
                  (vl-warninglist-p (mv-nth 0 (,name x nf warnings)))))

       (defthm ,(mksym name '-basics)
         (implies (and (force (vl-assign-p x))
                       ,@(and ops
                              `((force (not (vl-atom-p (vl-assign->expr x))))
                                (force (member (vl-nonatom->op (vl-assign->expr x)) ',ops))))
                       (force ,guard)
                       (force (vl-namefactory-p nf)))
                  (let ((ret (,name x nf warnings)))
                    (and (vl-modulelist-p   (mv-nth 1 ret))
                         (vl-modinstlist-p  (mv-nth 2 ret))
                         (vl-assignlist-p   (mv-nth 3 ret))
                         (vl-namefactory-p  (mv-nth 4 ret))))))

       (defthm ,(mksym 'true-listp-of- name '|-1|)
         (true-listp (mv-nth 1 (,name x nf warnings)))
         :rule-classes :type-prescription)

       (defthm ,(mksym 'true-listp-of- name '|-2|)
         (true-listp (mv-nth 2 (,name x nf warnings)))
         :rule-classes :type-prescription)

       (defthm ,(mksym 'true-listp-of- name '|-3|)
         (true-listp (mv-nth 3 (,name x nf warnings)))
         :rule-classes :type-prescription))))


(defmacro occform-return (&key (warnings 'warnings) (nf 'nf) mods modinsts assigns)
  `(mv ,warnings ,mods ,modinsts ,assigns ,nf))



(def-vl-occform vl-basic-binary-op-occform
  :short "Transform an assignment of a basic binary operation into
occurrences."

  :long "<p><tt>x</tt> should have one of the following forms:</p>
<ul>
 <li>assign lhs = <tt>a &amp; b</tt></li>
 <li>assign lhs = <tt>a | b</tt></li>
 <li>assign lhs = <tt>a ^ b</tt></li>
 <li>assign lhs = <tt>a ^~ b</tt></li>
</ul>"

  :ops (:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)

  :body
  (b* (((vl-assign x) x)
       (op    (vl-nonatom->op x.expr))
       (arg1  (first  (vl-nonatom->args x.expr)))
       (arg2  (second (vl-nonatom->args x.expr)))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth arg1))
                     (equal width (vl-expr->finalwidth arg2))
                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype arg1))
                     (eq type (vl-expr->finaltype arg2))))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of binary op."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-basic-binary-op-occform)
                         warnings)))

       (gtype    (case op
                   (:vl-binary-bitand :vl-and)
                   (:vl-binary-bitor  :vl-or)
                   (:vl-binary-xor    :vl-xor)
                   (:vl-binary-xnor   :vl-xnor)))
       (basename (case op
                   (:vl-binary-bitand "vl_band")
                   (:vl-binary-bitor  "vl_bor")
                   (:vl-binary-xor    "vl_bxor")
                   (:vl-binary-xnor   "vl_bxnor")))
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-binary-op gtype (vl-expr->finalwidth x.lvalue)))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-unary-not-occform
  :short "Transform <tt>assign lhs = ~a</tt> into occurrences."
  :ops (:vl-unary-bitnot)
  :body
  (b* (((vl-assign x) x)
       (arg1  (first (vl-nonatom->args x.expr)))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth arg1))
                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype arg1))))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of unary bitwise not."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-unary-not-occform)
                         warnings)))

       ((mv instname nf) (vl-namefactory-indexed-name "vl_unot" nf))
       (mods (vl-make-n-bit-not width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "in"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-plain-occform
  :short "Transform a plain assignment into occurrences."

  :long "<p><tt>x</tt> should have the form <tt>assign lhs = rhs</tt>, where
<tt>rhs</tt> is a <see topic='@(url vl-expr-sliceable-p)'>sliceable</see>
expression, such as a plain identifier, bit-select, part-select, or
concatenation of wires.</p>"

  :guard (vl-expr-sliceable-p (vl-assign->expr x))
  :body
  (b* (((vl-assign x) x)
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     type
                     (vl-expr->finaltype x.lvalue)))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of plain expression."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-plain-occform)
                         warnings)))

       ;; BOZO delays -- if we ever care about delays, we'll need to probably
       ;; figure out how to do something a little smarter here.
       ((mv instname nf) (vl-namefactory-indexed-name "vl_ass" nf))
       (mods (vl-make-n-bit-assign width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr x.expr   :dir :vl-input  :portname (hons-copy "in"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-unary-reduction-op-occform
  :short "Transform an assignment of a reduction operation into an equivalent
module instance."

  :long "<p><tt>x</tt> should have one of the following forms:</p>
<ul>
  <li><tt>assign lhs = &amp;rhs;</tt></li>
  <li><tt>assign lhs = |rhs;</tt></li>
  <li><tt>assign lhs = ^rhs;</tt></li>
</ul>"

  :ops (:vl-unary-bitand :vl-unary-bitor :vl-unary-xor)
  :body
  (b* (((vl-assign x) x)
       (op    (vl-nonatom->op x.expr))
       (arg   (first (vl-nonatom->args x.expr)))

       ((unless (and (equal (vl-expr->finalwidth x.expr) 1)
                     (equal (vl-expr->finaltype x.expr) :vl-unsigned)
                     (equal (vl-expr->finalwidth x.lvalue) 1)
                     (vl-expr->finaltype x.lvalue)
                     (posp  (vl-expr->finalwidth arg))
                     (vl-expr->finaltype arg)))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types for assignment of reduction op."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-unary-reduction-op-occform)
                         warnings)))

       (basename (case op
                   (:vl-unary-bitand "vl_uand")
                   (:vl-unary-bitor  "vl_uor")
                   (:vl-unary-xor    "vl_uxor")))
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-reduction-op op (vl-expr->finalwidth arg)))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg      :dir :vl-input  :portname (hons-copy "in"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-plusminus-occform
  :short "Transform an assignment of a addition/subtraction into occurrences."

  :long "<p><tt>x</tt> should have one of the following forms:</p>
<ul>
 <li><tt>assign lhs = a + b;</tt></li>
 <li><tt>assign lhs = a - b;</tt></li>
</ul>"

  :ops (:vl-binary-plus :vl-binary-minus)
  :body
  (b* (((vl-assign x) x)
       (op    (vl-nonatom->op x.expr))
       (arg1  (first (vl-nonatom->args x.expr)))
       (arg2  (second (vl-nonatom->args x.expr)))

       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth arg1))
                     (equal width (vl-expr->finalwidth arg2))
                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype arg1))
                     (eq type (vl-expr->finaltype arg2))))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of addition/subtraction."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-plusminus-occform)
                         warnings)))

       (warnings (if (eq type :vl-unsigned)
                     warnings
                   (cons (make-vl-warning :type :vl-signed-addition
                                          :msg "~a0: make sure signed addition/subtraction is right."
                                          :args (list x)
                                          :fatalp nil
                                          :fn 'vl-plusminus-occform)
                         warnings)))

       (basename (case op
                   (:vl-binary-plus "vl_plus")
                   (:vl-binary-minus "vl_minus")))

       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-plusminus op width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "sum"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-mult-occform
  :short "Transform <tt>assign lhs = a * b</tt> into occurrences."
  :ops (:vl-binary-times)
  :body
  (b* (((vl-assign x) x)
       (arg1  (first (vl-nonatom->args x.expr)))
       (arg2  (second (vl-nonatom->args x.expr)))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth arg1))
                     (equal width (vl-expr->finalwidth arg2))
                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype arg1))
                     (eq type (vl-expr->finaltype arg2))))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in multiplication."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-mult-occform)
                         warnings)))

       (warnings (if (eq type :vl-unsigned)
                     warnings
                   (cons (make-vl-warning :type :vl-signed-addition
                                          :msg "~a0: make sure signed multiplication is right."
                                          :args (list x)
                                          :fatalp nil
                                          :fn 'vl-mult-occform)
                         warnings)))

       (basename "vl_mult")
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-mult width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "o"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-gte-occform
  :short "Transform <tt>assign lhs = a &gt; b</tt> into occurrences."
  :ops (:vl-binary-gte)
  :body
  (b* (((vl-assign x) x)
       (arg1      (first (vl-nonatom->args x.expr)))
       (arg2      (second (vl-nonatom->args x.expr)))
       (arg1width (vl-expr->finalwidth arg1))
       (arg1type  (vl-expr->finaltype arg1))

       ((unless (and (equal (vl-expr->finalwidth x.expr) 1)
                     (equal (vl-expr->finaltype x.expr) :vl-unsigned)
                     (equal (vl-expr->finalwidth x.lvalue) 1)
                     (vl-expr->finaltype x.lvalue)
                     arg1type
                     (posp arg1width)
                     (equal arg1type (vl-expr->finaltype arg2))
                     (equal arg1width (vl-expr->finalwidth arg2))))
        (occform-return
         :assigns  (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of >= operation."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-gte-occform)
                         warnings)))

       (warnings
        (if (eq arg1type :vl-unsigned)
            warnings
          (cons (make-vl-warning
                 :type :vl-warn-signed-comparison
                 :msg "~a0: found a signed comparison expression.  This is ~
                       dangerous because whereas NCVerilog properly carries ~
                       out a comparison between 2's complement numbers, ~
                       Verilog-XL incorrectly uses an unsigned comparison.  ~
                       We follow the standard and mimick NCVerilog, but to ~
                       ensure compatibility across Verilog implementations, ~
                       you should probably not use signed comparisons.  Some ~
                       typical causes of signedness are plain decimal numbers ~
                       like 17, and the use of integer variables instead of ~
                       regs."
                 :args (list x)
                 :fatalp nil
                 :fn 'vl-gte-occform)
                warnings)))

       ((mv instname nf) (vl-namefactory-indexed-name "vl_gte" nf))
       (mods (if (eq arg1type :vl-unsigned)
                 (vl-make-n-bit-unsigned-gte arg1width)
               (vl-make-n-bit-signed-gte arg1width)))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-mux-occform
  :short "Transform an assignment of a conditional expression into occurrences."

  :long "<p><tt>x</tt> should have the form <tt>assign lhs = a ? b : c;</tt>.</p>

<p>As a special case, <tt>sel ? a : n'bZ</tt> is transformed into a zmux, and
in @(see oprewrite) we rewrite <tt>sel ? n'bZ : a</tt> into <tt>sel ? a :
n'bZ</tt> so this covers both cases.  Otherwise, we create an ordinary mux.</p>

<p>Advanced note.  Ordinarily, we produce an approx mux as described in the
documentation for @(see vl-make-n-bit-mux).  An advanced user can choose to use
the non-approx version by adding the attribute <tt>VL_X_SELECT</tt> to the
conditional operator.  An example of the syntax for doing this is as
follows:</p>

<box> assign out = sel ? (* VL_X_SELECT *) a : b ; </box>

<p>If this attribute is provided, a non-approx mux will be created instead.  This
may be necessary if you want to reason about <tt>out</tt> even when <tt>sel</tt>
is <tt>X</tt> or <tt>Z</tt>.</p>"

  :ops (:vl-qmark)
  :body
  (b* (((vl-assign x) x)

       (sel (first (vl-nonatom->args x.expr)))
       (a   (second (vl-nonatom->args x.expr)))
       (b   (third (vl-nonatom->args x.expr)))

       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (and (equal (vl-expr->finalwidth sel) 1)
                     (vl-expr->finaltype sel)

                     (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth a))
                     (equal width (vl-expr->finalwidth b))

                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype a))
                     (eq type (vl-expr->finaltype b))))
        (occform-return
         :assigns (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths on assignment of conditional expression."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-mux-occform)
                         warnings)))

       ((when (vl-zatom-p b))
        ;; Found "a ? b : z" -- make a zmux.
        (b* (((mv instname nf) (vl-namefactory-indexed-name "vl_zmux" nf))
             (mods (vl-make-n-bit-zmux width))
             (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                         (make-vl-plainarg :expr sel      :dir :vl-input  :portname (hons-copy "sel"))
                         (make-vl-plainarg :expr a        :dir :vl-input  :portname (hons-copy "a"))))
             (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                       :instname  instname
                                       :paramargs (vl-arguments nil nil)
                                       :portargs  (vl-arguments nil args)
                                       :atts      x.atts
                                       :loc       x.loc)))
          (occform-return :mods mods
                          :modinsts (list modinst))))

       ;; Else, found "a ? b : c" -- make a regular mux.  By default we will
       ;; now use our "less precise" mode.  But if the attribute VL_X_SELECT is
       ;; present, we use the "more precise" mode where, e.g., X ? 1 : 1 is 1.
       ((mv instname nf) (vl-namefactory-indexed-name "vl_mux" nf))
       (approxp (not (hons-assoc-equal "VL_X_SELECT" (vl-nonatom->atts x.expr))))

       (mods (vl-make-n-bit-mux width approxp))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr sel      :dir :vl-input  :portname (hons-copy "sel"))
                   (make-vl-plainarg :expr a        :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr b        :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  instname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-shift-occform
  :short "Transform an assignment of a shift expression into occurrences."

  :long "<p><tt>x</tt> should have one of these forms:</p>
<ul>
 <li><tt>assign lhs = a &lt;&lt; b;</tt></li>
 <li><tt>assign lhs = a &gt;&gt; b;</tt></li>
</ul>"

  :ops (:vl-binary-shl :vl-binary-shr)
  :body
  (b* (((vl-assign x) x)
       (op    (vl-nonatom->op x.expr))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       (arg1 (first (vl-nonatom->args x.expr)))
       (arg2 (second (vl-nonatom->args x.expr)))

       ((unless (and (posp width)
                     (equal width (vl-expr->finalwidth x.lvalue))
                     (equal width (vl-expr->finalwidth arg1))
                     (posp (vl-expr->finalwidth arg2))
                     type
                     (vl-expr->finaltype x.lvalue)
                     (eq type (vl-expr->finaltype arg1))
                     (vl-expr->finaltype arg2)))
        (occform-return
         :assigns (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of shift."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-shift-occform)
                         warnings)))

       ;; Make a module and instantiate it.
       (basename (case op
                   (:vl-binary-shl "vl_shl")
                   (:vl-binary-shr "vl_shr")))
       ((mv iname nf) (vl-namefactory-indexed-name basename nf))
       (mods (case op
               (:vl-binary-shl (vl-make-n-bit-shl-by-m-bits width (vl-expr->finalwidth arg2)))
               (:vl-binary-shr (vl-make-n-bit-shr-by-m-bits width (vl-expr->finalwidth arg2)))))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  iname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-bitselect-occform
  :short "Transform <tt>assign lhs = foo[i]</tt> into occurrences (dynamic
bitselects only!)."

  :long "<p>This is only for dynamic bitselects, not static selects like
<tt>foo[3]</tt>.  See @(see vl-assign-occform): any sliceable expressions get
handled by @(see vl-plain-occform), and any static bitselects are
sliceable.</p>"

  :ops (:vl-bitselect)
  :body
  (b* (((vl-assign x) x)

       (from       (first (vl-nonatom->args x.expr)))
       (idx        (second (vl-nonatom->args x.expr)))
       (from-width (vl-expr->finalwidth from))
       (idx-width  (vl-expr->finalwidth idx))

       ((unless (and (equal (vl-expr->finalwidth x.expr) 1)
                     (equal (vl-expr->finalwidth x.lvalue) 1)
                     (posp from-width)
                     (posp idx-width)
                     (eq (vl-expr->finaltype x.expr) :vl-unsigned)
                     (vl-expr->finaltype x.lvalue)
                     (vl-expr->finaltype from)
                     (vl-expr->finaltype idx)))
        (occform-return
         :assigns (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of bit-select."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-bitselect-occform)
                         warnings)))

       (warnings (if (vl-expr-resolved-p idx)
                     (cons (make-vl-warning
                            :type :vl-programming-error
                            :msg "~a0: how did this get called?  we're using a ~
                                  dynamic bitselect when a static one would do."
                            :args (list x)
                            :fatalp t
                            :fn 'vl-bitselect-occform)
                           warnings)
                   warnings))

       ((mv iname nf) (vl-namefactory-indexed-name "vl_bsel" nf))

       (mods (vl-make-n-bit-dynamic-bitselect-m from-width idx-width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr from     :dir :vl-input  :portname (hons-copy "in"))
                   (make-vl-plainarg :expr idx      :dir :vl-input  :portname (hons-copy "idx"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  iname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))



(def-vl-occform vl-ceq-occform
  :short "Transform an assignment of a <tt>===</tt> expression into occurrences."

  :long "<p><tt>x</tt> should have the form: <tt>assign lhs = (a === b);</tt></p>"

  :ops (:vl-binary-ceq)
  :body
  (b* (((vl-assign x) x)
       (arg1      (first (vl-nonatom->args x.expr)))
       (arg2      (second (vl-nonatom->args x.expr)))
       (arg1width (vl-expr->finalwidth arg1))
       (arg1type  (vl-expr->finaltype arg1))

       ((unless (and (equal (vl-expr->finalwidth x.expr) 1)
                     (equal (vl-expr->finaltype x.expr) :vl-unsigned)
                     (equal (vl-expr->finalwidth x.lvalue) 1)
                     (vl-expr->finaltype x.lvalue)
                     arg1type
                     (posp arg1width)
                     (equal arg1type  (vl-expr->finaltype arg2))
                     (equal arg1width (vl-expr->finalwidth arg2))))
        (occform-return
         :assigns (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of ceq."
                          :args (list x)
                          :fatalp t
                          :fn 'vl-ceq-occform)
                         warnings)))

       ;; Make a module and instantiate it.
       ((mv iname nf) (vl-namefactory-indexed-name "vl_ceq" nf))
       (mods          (vl-make-n-bit-ceq arg1width))
       (args (list (make-vl-plainarg :expr x.lvalue :dir :vl-output :portname (hons-copy "out"))
                   (make-vl-plainarg :expr arg1     :dir :vl-input  :portname (hons-copy "a"))
                   (make-vl-plainarg :expr arg2     :dir :vl-input  :portname (hons-copy "b"))))
       (modinst (make-vl-modinst :modname   (vl-module->name (car mods))
                                 :instname  iname
                                 :paramargs (vl-arguments nil nil)
                                 :portargs  (vl-arguments nil args)
                                 :atts      x.atts
                                 :loc       x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-assign-occform
  :short "Transform an arbitrary single assignment into occurrences."

  :long "<p>We don't support certain operators like division and modulus yet.
It should be straightforward to add new operators: just figure out how to
generate a gate-based conservative approximation, and then plug it in
below.</p>"

  :guard-debug t
  :body
  (b* ((expr (vl-assign->expr x))

       ((when (vl-expr-sliceable-p expr))
        (vl-plain-occform x nf warnings))

       ((when (vl-fast-atom-p expr))
        ;; Any reasonable atom should be sliceable.
        (occform-return
         :assigns (list x)
         :warnings (cons (make-vl-warning
                          :type :vl-not-implemented
                          :msg "~a0: don't know how to occform ~x1 atom."
                          :args (list x (tag (vl-atom->guts expr)))
                          :fn 'vl-assign-occform
                          :fatalp t)
                         warnings)))

       (op (vl-nonatom->op expr)))

    (case op
      ((:vl-unary-bitand :vl-unary-bitor :vl-unary-xor)
       (vl-unary-reduction-op-occform x nf warnings))

      (:vl-unary-bitnot
       (vl-unary-not-occform x nf warnings))

      ((:vl-binary-plus :vl-binary-minus)
       (vl-plusminus-occform x nf warnings))

      ((:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       (vl-basic-binary-op-occform x nf warnings))

      ((:vl-binary-gte)
       (vl-gte-occform x nf warnings))

      ((:vl-binary-ceq)
       (vl-ceq-occform x nf warnings))

      ((:vl-bitselect)
       ;; Must be a dynamic bitselect...
       (vl-bitselect-occform x nf warnings))

      ((:vl-qmark)
       (vl-mux-occform x nf warnings))

      ((:vl-binary-shl :vl-binary-shr)
       (vl-shift-occform x nf warnings))

      ((:vl-binary-times)
       (vl-mult-occform x nf warnings))

      ;; Now these should all be handled above, since they should be sliceable.
      ((:vl-partselect-colon :vl-concat :vl-multiconcat)
       (occform-return
        :assigns (list x)
        :warnings (cons (make-vl-warning
                         :type :vl-programming-error
                         :msg "~a0: expected ~x1 operator to be sliceable!"
                         :args (list x op)
                         :fn 'vl-assign-occform
                         :fatalp t)
                        warnings)))

      (otherwise
       (occform-return
        :assigns (list x)
        :warnings (cons (make-vl-warning
                         :type :vl-not-implemented
                         :msg "~a0: don't know how to occform ~x1 operator."
                         :args (list x op)
                         :fn 'vl-assign-occform
                         :fatalp t)
                        warnings))))))



(defsection vl-assignlist-occform
  :parents (occform)
  :short "Project @(see vl-assign-occform) across a list of assignments."

  (defund vl-assignlist-occform (x nf warnings)
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nil nf))
         ((mv warnings mods1 modinsts1 assigns1 nf) (vl-assign-occform (car x) nf warnings))
         ((mv warnings mods2 modinsts2 assigns2 nf) (vl-assignlist-occform (cdr x) nf warnings))
         (mods     (append mods1 mods2))
         (modinsts (append modinsts1 modinsts2))
         (assigns  (append assigns1 assigns2)))
      (mv warnings mods modinsts assigns nf)))

  (local (in-theory (enable vl-assignlist-occform)))

  (defthm vl-warninglist-p-of-vl-assignlist-occform
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-assignlist-occform x nf warnings)))))

  (defthm true-listp-of-vl-assignlist-occform-1
    (true-listp (mv-nth 1 (vl-assignlist-occform x nf warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-assignlist-occform-2
    (true-listp (mv-nth 2 (vl-assignlist-occform x nf warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-assignlist-occform-3
    (true-listp (mv-nth 3 (vl-assignlist-occform x nf warnings)))
    :rule-classes :type-prescription)

  (defthm vl-assignlist-occform-basics
    (implies (and (force (vl-assignlist-p x))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-assignlist-occform x nf warnings)))
               (and (vl-modulelist-p   (mv-nth 1 ret))
                    (vl-modinstlist-p  (mv-nth 2 ret))
                    (vl-assignlist-p   (mv-nth 3 ret))
                    (vl-namefactory-p  (mv-nth 4 ret)))))))




(defsection vl-module-occform

  (defund vl-module-occform (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          (mv nil x))

         ((vl-module x) x)

         (nf (vl-starting-namefactory x))
         ((mv warnings new-mods new-modinsts new-assigns nf)
          (vl-assignlist-occform x.assigns nf x.warnings))
         (- (vl-free-namefactory nf))

         (x-prime (change-vl-module x
                                    :warnings warnings
                                    :assigns  new-assigns
                                    :modinsts (append new-modinsts x.modinsts))))
      (mv new-mods x-prime)))

  (local (in-theory (enable vl-module-occform)))

  (defthm true-listp-of-vl-module-occform1
    (true-listp (mv-nth 0 (vl-module-occform x)))
    :rule-classes :type-prescription)

  (defthm props-of-vl-module-occform
    (implies (vl-module-p x)
             (and (vl-modulelist-p (mv-nth 0 (vl-module-occform x)))
                  (vl-module-p (mv-nth 1 (vl-module-occform x)))))))


(defsection vl-modulelist-occform-aux

  (defund vl-modulelist-occform-aux (x)
    "Returns (MV NEW-MODS X-PRIME)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv mods1 car-prime) (vl-module-occform (car x)))
         ((mv mods2 cdr-prime) (vl-modulelist-occform-aux (cdr x)))
         (new-mods (append mods1 mods2))
         (x-prime  (cons car-prime cdr-prime)))
        (mv new-mods x-prime)))

  (local (in-theory (enable vl-modulelist-occform-aux)))

  (defthm true-listp-of-vl-modulelist-occform-aux1
    (true-listp (mv-nth 0 (vl-modulelist-occform-aux x)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-modulelist-occform-aux2
    (true-listp (mv-nth 1 (vl-modulelist-occform-aux x)))
    :rule-classes :type-prescription)

  (defthm props-of-vl-modulelist-occform-aux
    (implies (force (vl-modulelist-p x))
             (and (vl-modulelist-p (mv-nth 0 (vl-modulelist-occform-aux x)))
                  (vl-modulelist-p (mv-nth 1 (vl-modulelist-occform-aux x)))))))



(defsection vl-modulelist-occform

  (defund vl-modulelist-occform (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((mv new-mods x-prime)
          (vl-modulelist-occform-aux x))
         (- (clear-these-memoize-tables *vl-occform-memoize*))
         (new-mods-sort (mergesort new-mods))
         (full-mods     (append new-mods-sort x-prime))
         (all-names     (vl-modulelist->names full-mods))
         ((unless (uniquep all-names))
          (er hard? 'vl-modulelist-occform "Name collision")))
      full-mods))

  (local (in-theory (enable vl-modulelist-occform)))

  (defthm vl-modulelist-p-of-vl-modulelist-occform
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-occform x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-occform
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-occform x)))))




