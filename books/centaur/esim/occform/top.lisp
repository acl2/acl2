; ESIM Symbolic Hardware Simulator
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
(include-book "add")
(include-book "compare")
(include-book "div")
(include-book "mul")
(include-book "select")
(include-book "shl")
(include-book "shr")
(include-book "simple")
(include-book "xdet")
(include-book "centaur/vl2014/mlib/expr-slice" :dir :system)
(include-book "centaur/vl2014/mlib/namefactory" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))


;; BOZO we probably want to memoize the generators and possibly have all of the
;; generators produce honsed modules.  If all of the new-modules are honsed,
;; then the mergesort here should be really fast
;;
;;   - the EQUAL check in FAST-UNION will be quickly YES by pointer-equality or
;;     quickly NO by module-name mismatch
;;
;;   - the << checks in FAST-UNION will be quickly settled by module-name
;;     comparison
;;
;; But if there are EQUAL-but-not-EQ modules, the EQUAL checks could become
;; quite expensive.

;; BOZO try to standardize the parameter-names in generated modules into some
;; common scheme, e.g., "out" versus "o", etc.

;; BOZO any generators that can be improved by using bustable exprs?  Shifting
;; was improved a lot by using part-selects instead of lots of stupid buffers.
;; I think the partial-product generation for multiplication can also be
;; patched up like this.  Searching for "buf" might be a good start toward
;; looking at these.

;; BOZO many generators could also probably switch to instance muxes instead of
;; laying down their own gates to do muxing, which could make their function
;; more clear

;; BOZO are we handling signed things correctly?  need regressions and similar.

;; BOZO these width-checks could probably be turned into welltyped-assign-p
;; checks or similar, if we had such a concept and all of the relevant theorems
;; about it.


(defxdoc occform
  :parents (transforms)
  :short "Transform assignments into occurrences."

  :long "<p>We now introduce routines to transform post-@(see split)
assignments into occurrences of new, primitive modules.</p>

<p>We expect to see assignments of the form:</p>

@({
    assign LVALUE = EXPR ;
})

<p>where @('EXPR') consists either of a single operand or of a single operation
applied to operands.  We expect to not encounter certain operators such as
@('==') and @('||') which are handled by @(see oprewrite).</p>

<p>We typically replace each assignment with an instance of a newly-generated
module.  For instance, if our operation is @('a + b'), where the operation is
being done in @('n') bits, we introduce a new @('VL_N_BIT_PLUS') module, and
replace the assignment with an instance of this module.</p>

<p>Each of our @('-occform') functions takes as arguments:</p>

<ul>

<li>@('x'), an assignment that typically must be of some particular form,</li>

<li>@('nf'), a @(see vl-namefactory-p) to use when generating new names,
and</li>

<li>@('warnings'), an ordinary @(see warnings) accumulator.</li>

</ul>

<p>And returns @('(mv new-warnings new-modules new-modinsts new-nf)'),
where:</p>

<ul>

<li>@('new-warnings') is the new warnings accumulator which has been extended
with any warnings,</li>

<li>@('new-modules') are any newly generated modules that need to be added so
that we can instantiate them---that is, this list will define modules like
@('VL_13_BIT_PLUS') that will be used to replace this assignment,</li>

<li>@('new-modinsts') and @('new-assigns') are any new module instances and
assignments that, taken together, can replace @('x'), and</li>

<li>@('new-nf') is the updated @(see vl-namefactory-p) that is used to generate
module instance names.</li>

</ul>

<p>Typically @('new-assigns') will be empty on success, and will just be
@('(list x)') on failure.</p>")

(defconst *vl-occform-memoize*
  '(vl-make-n-bit-binary-op
    vl-make-n-bit-assign
    vl-make-n-bit-not
    vl-make-n-bit-reduction-op
    vl-make-n-bit-mux
    vl-make-n-bit-zmux
    vl-make-n-bit-ceq
    vl-make-n-bit-x
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
    vl-make-n-bit-x-propagator
    vl-make-n-bit-div-step
    vl-make-n-bit-div-core
    vl-make-n-bit-div-rem
    vl-make-n-bit-unsigned-div
    vl-make-n-bit-unsigned-rem
    ))

(define memoize-list-fn (x)
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

(define clear-these-memoize-tables (fns)
  (if (atom fns)
      nil
    (prog2$ (clear-memoize-table (car fns))
            (clear-these-memoize-tables (cdr fns)))))



(define vl-occform-extend-id
  :parents (vl-occform-argfix)
  ((x        vl-expr-p         "Wire that we need to perhaps extend.")
   (range    vl-maybe-range-p  "Range of this wire.")
   (warnings vl-warninglist-p))
  :guard (and (vl-idexpr-p x)
              (posp (vl-expr->finalwidth x))
              (vl-expr->finaltype x))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-expr-p))
  (b* ((x          (vl-expr-fix x))
       (range      (vl-maybe-range-fix range))
       (finalwidth (vl-expr->finalwidth x))
       (finaltype  (vl-expr->finaltype x))
       ((unless (vl-maybe-range-resolved-p range))
        (mv (fatal :type :vl-occform-bad-id
                   :msg "Expected range for ~a0 to be resolved: ~a1."
                   :args (list x range))
            x))
       (actual-size (vl-maybe-range-size range))
       ((when (eql actual-size finalwidth))
        ;; No problems
        (mv (ok) x))
       ((when (< finalwidth actual-size))
        (mv (fatal :type :vl-occform-bad-id
                   :msg "Finalwidth of ~a0 is too small for range ~a1."
                   :args (list x range))
            x))
       ;; Otherwise, need to zero or sign extend.
       (name      (vl-idexpr->name x))
       (id-part   (vl-idexpr name actual-size finaltype))
       (pad-width (- finalwidth actual-size))
       (pad-bit
        (cond ((eq finaltype :vl-unsigned)
               |*sized-1'b0*|)
              ((not range)
               ;; Special case: signed one-bit wire.  Pad bit is just the wire itself.
               (vl-idexpr name 1 :vl-signed))
              (t
               ;; Normal case, signed one-bit wire with some MSB and LSB.
               (make-vl-nonatom :op :vl-bitselect
                                :args (list id-part
                                            (vl-make-index (vl-resolved->val (vl-range->msb range))))
                                :finalwidth 1
                                :finaltype :vl-unsigned))))
       (concat (make-vl-nonatom :op :vl-concat
                                :args (append (replicate pad-width pad-bit)
                                              (list id-part))
                                :finalwidth finalwidth
                                :finaltype :vl-unsigned)))
    (mv (ok) concat))
  ///
  (defthm vl-expr->finalwidth-of-vl-occform-extend-id
    (equal (vl-expr->finalwidth (mv-nth 1 (vl-occform-extend-id x range warnings)))
           (vl-expr->finalwidth x)))

  (local (defthm l0
           (equal (vl-exprlist->finalwidths (replicate len x))
                  (replicate len (vl-expr->finalwidth x)))
           :hints(("Goal" :in-theory (enable replicate)))))

  (local (in-theory (enable tag-reasoning)))

  (defthm vl-expr-welltyped-p-of-vl-occform-extend-id
    (implies (and (vl-expr-welltyped-p x)
                  (vl-idexpr-p x)
                  (vl-expr->finaltype x))
             (vl-expr-welltyped-p (mv-nth 1 (vl-occform-extend-id x range warnings))))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-atom-welltyped-p
                                      vl-idexpr
                                      vl-make-index)))))

(define vl-occform-argfix
  :parents (occform)
  :short "Make extensions explicit for arguments to occform modules."

  ((x        vl-expr-p                             "Argument to some operator, sizes already computed.")
   (mod      vl-module-p                           "Module where @('x') occurs.")
   (ialist   (equal ialist (vl-make-moditem-alist mod)) "For fast lookups.")
   (warnings vl-warninglist-p))
  :guard (and (posp (vl-expr->finalwidth x))
              (vl-expr->finaltype x))

  :returns (mv (warnings vl-warninglist-p)
               (new-expr vl-expr-p))

  :long "<p>See @(see vl-atom-welltyped-p) and note that our internal
representation of sized expressions leaves zero/sign extensions of identifiers
implicit.  This is unfortunate because it means that, e.g., if we have
something like:</p>

@({
    wire [3:0] a;
    wire [4:0] b;
    assign lhs = a + b;
})

<p>And we translate it into:</p>

@({
    VL_5_BIT_PLUS my_adder (lhs, a, b);
})

<p>Then the sizes of the arguments appear to be wrong in the pretty-printed
representation of the output.  We would rather produce something like:</p>

@({
    VL_5_BIT_PLUS my_adder (lhs, {1'b0, a}, b);
})

<p>So that the extensions are explicit.  It's relatively easy to do this, now,
because since we're going to give this operands as an argument to a submodule,
its signedness is no longer relevant.</p>"

  ;; The errors below should never happen, because we should only call this on
  ;; things we're intending to occform, which have already passed through
  ;; sizing successfully.
  (b* ((x (vl-expr-fix x))
       ((unless (vl-idexpr-p x))
        (mv (ok) x))

       (name (vl-idexpr->name x))
       (item (vl-fast-find-moduleitem name mod ialist))

       ((unless item)
        (mv (fatal :type :vl-occform-bad-id
                   :msg "No declaration found for ~a0."
                   :args (list x))
            x))

       (tag (tag item))
       ((unless (eq tag :vl-vardecl))
        (mv (fatal :type :vl-occform-bad-id
                   :msg "Trying to occform identifier ~a0, which has some strange type ~x1."
                   :args (list x (tag item)))
            x))

       ((unless (vl-simplevar-p item))
        (mv (fatal :type :vl-occform-bad-id
                   :msg "Trying to occform identifier ~a0, which is not a simple var."
                   :args (list x))
            x)))

    (vl-occform-extend-id x (vl-simplevar->range item) warnings))
  ///
  (defthm vl-expr->finalwidth-of-vl-occform-argfix
    (equal (vl-expr->finalwidth (mv-nth 1 (vl-occform-argfix x mod ialist warnings)))
           (vl-expr->finalwidth x))))

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
  `(define ,name
     :parents ,parents
     :short ,short
     :long ,long
     ((x        vl-assign-p)
      (nf       vl-namefactory-p)
      (mod      vl-module-p)
      (ialist   (equal ialist (vl-make-moditem-alist mod)))
      (warnings vl-warninglist-p))
     :guard (and ,@(and ops
                        `((not (vl-atom-p (vl-assign->expr x)))
                          (member (vl-nonatom->op (vl-assign->expr x)) ',ops)))
                 ,guard)
     :returns (mv (new-warnings  vl-warninglist-p)
                  (new-modules   vl-modulelist-p)
                  (new-modinsts  vl-modinstlist-p)
                  (new-assigns   vl-assignlist-p)
                  (new-nf        vl-namefactory-p))
     :guard-debug ,guard-debug
     (b* ((x        (vl-assign-fix x))
          (warnings (vl-warninglist-fix warnings))
          (nf       (vl-namefactory-fix nf)))
       ,body)
     ///
     (defmvtypes ,name (nil true-listp true-listp true-listp nil))))

(defmacro occform-return (&key (warnings 'warnings) (nf 'nf) mods modinsts assigns)
  `(mv ,warnings ,mods ,modinsts ,assigns ,nf))



(def-vl-occform vl-basic-binary-op-occform
  :short "Transform an assignment of a basic binary operation into
occurrences."

  :long "<p>@('x') should have one of the following forms:</p>

<ul>
<li>assign lhs = @('a & b')</li>
<li>assign lhs = @('a | b')</li>
<li>assign lhs = @('a ^ b')</li>
<li>assign lhs = @('a ^~ b')</li>
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of binary op."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

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
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-unary-not-occform
  :short "Transform @('assign lhs = ~a') into occurrences."
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of unary bitwise not."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))

       ((mv instname nf) (vl-namefactory-indexed-name "vl_unot" nf))
       (mods (vl-make-n-bit-not width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-plain-occform
  :short "Transform a plain assignment into occurrences."

  :long "<p>@('x') should have the form @('assign lhs = rhs'), where @('rhs')
is a <see topic='@(url vl-expr-sliceable-p)'>sliceable</see> expression, such
as a plain identifier, bit-select, part-select, or concatenation of wires.</p>"

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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of plain expression."
                          :args (list x))))

       ((mv warnings expr) (vl-occform-argfix x.expr mod ialist warnings))

       ;; BOZO delays -- if we ever care about delays, we'll need to probably
       ;; figure out how to do something a little smarter here.
       ((mv instname nf) (vl-namefactory-indexed-name "vl_ass" nf))
       (mods (vl-make-n-bit-assign width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue expr)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-unary-reduction-op-occform
  :short "Transform an assignment of a reduction operation into an equivalent
module instance."

  :long "<p>@('x') should have one of the following forms:</p>
<ul>
  <li>@('assign lhs = &rhs;')</li>
  <li>@('assign lhs = |rhs;')</li>
  <li>@('assign lhs = ^rhs;')</li>
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types for assignment of reduction op."
                          :args (list x))))

       ((mv warnings arg) (vl-occform-argfix arg mod ialist warnings))

       (basename (case op
                   (:vl-unary-bitand "vl_uand")
                   (:vl-unary-bitor  "vl_uor")
                   (:vl-unary-xor    "vl_uxor")))
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-reduction-op op (vl-expr->finalwidth arg)))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-plusminus-occform
  :short "Transform an assignment of a addition/subtraction into occurrences."

  :long "<p>@('x') should have one of the following forms:</p>
<ul>
 <li>@('assign lhs = a + b;')</li>
 <li>@('assign lhs = a - b;')</li>
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of addition/subtraction."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       (basename (case op
                   (:vl-binary-plus "vl_plus")
                   (:vl-binary-minus "vl_minus")))

       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-plusminus op width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-mult-occform
  :short "Transform @('assign lhs = a * b') into occurrences."
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in multiplication."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       (basename "vl_mult")
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods (vl-make-n-bit-mult width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-div-occform
  :short "Transform @('assign lhs = a / b') into occurrences."
  :ops (:vl-binary-div)
  :body
  (b* (((vl-assign x) x)
       (arg1  (first  (vl-nonatom->args x.expr)))
       (arg2  (second (vl-nonatom->args x.expr)))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (eq type :vl-unsigned))
        (occform-return
         :assigns (list x)
         :warnings (fatal :type :vl-warn-signed-div
                          :msg "~a0: signed divide is not implemented yet"
                          :args (list x))))

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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in divide."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       (basename "vl_div")
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods    (vl-make-n-bit-unsigned-div width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))

(def-vl-occform vl-rem-occform
  :short "Transform @('assign lhs = a % b') into occurrences."
  :ops (:vl-binary-rem)
  :body
  (b* (((vl-assign x) x)
       (arg1  (first  (vl-nonatom->args x.expr)))
       (arg2  (second (vl-nonatom->args x.expr)))
       (width (vl-expr->finalwidth x.expr))
       (type  (vl-expr->finaltype x.expr))

       ((unless (eq type :vl-unsigned))
        (occform-return
         :assigns (list x)
         :warnings (fatal :type :vl-warn-signed-rem
                          :msg "~a0: signed remainder (i.e., modulus, %) is not implemented yet"
                          :args (list x))))

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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in remainder (i.e., modulus, %)."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       (basename "vl_rem")
       ((mv instname nf) (vl-namefactory-indexed-name basename nf))
       (mods    (vl-make-n-bit-unsigned-rem width))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-gte-occform
  :short "Transform @('assign lhs = a > b') into occurrences."
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths/types in assignment of >= operation."
                          :args (list x))))

       (warnings
        (if (eq arg1type :vl-unsigned)
            warnings
          (warn :type :vl-warn-signed-comparison
                :msg "~a0: found a signed comparison expression.  This is ~
                       dangerous because whereas NCVerilog properly carries ~
                       out a comparison between 2's complement numbers, ~
                       Verilog-XL incorrectly uses an unsigned comparison.  ~
                       We follow the Verilog-2005 standard and mimick ~
                       NCVerilog, but to ensure compatibility across Verilog ~
                       implementations, you should probably not use signed ~
                       comparisons.  Some typical causes of signedness are ~
                       plain decimal numbers like 17, and the use of integer ~
                       variables instead of regs."
                :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       ((mv instname nf) (vl-namefactory-indexed-name "vl_gte" nf))
       (mods (if (eq arg1type :vl-unsigned)
                 (vl-make-n-bit-unsigned-gte arg1width)
               (vl-make-n-bit-signed-gte arg1width)))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-mux-occform
  :short "Transform an assignment of a conditional expression into occurrences."

  :long "<p>@('x') should have the form @('assign lhs = a ? b : c;').</p>

<p>As a special case, @('sel ? a : n'bZ') is transformed into a zmux, and in
@(see oprewrite) we rewrite @('sel ? n'bZ : a') into @('sel ? a : n'bZ') so
this covers both cases.  Otherwise, we create an ordinary mux.</p>

<p>Advanced note.  Ordinarily, we produce an approx mux as described in the
documentation for @(see vl-make-n-bit-mux).  An advanced user can choose to use
the non-approx version by adding the attribute @('VL_X_SELECT') to the
conditional operator.  An example of the syntax for doing this is as
follows:</p>

<box> assign out = sel ? (* VL_X_SELECT *) a : b ; </box>

<p>If this attribute is provided, a non-approx mux will be created instead.
This may be necessary if you want to reason about @('out') even when @('sel')
is @('X') or @('Z').</p>"

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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths on assignment of conditional expression."
                          :args (list x))))

       ((when (vl-zatom-p b))
        ;; Found "a ? b : z" -- make a zmux.
        (b* (((mv instname nf) (vl-namefactory-indexed-name "vl_zmux" nf))
             (mods    (vl-make-n-bit-zmux width))
             (modinst (vl-simple-instantiate (car mods) instname
                                             (list x.lvalue sel a)
                                             :loc x.loc)))
          (occform-return :mods mods
                          :modinsts (list modinst))))

       ;; Else, found "a ? b : c" -- make a regular mux.  By default we will
       ;; now use our "less precise" mode.  But if the attribute VL_X_SELECT is
       ;; present, we use the "more precise" mode where, e.g., X ? 1 : 1 is 1.
       ((mv instname nf) (vl-namefactory-indexed-name "vl_mux" nf))
       (approxp (not (hons-assoc-equal "VL_X_SELECT" (vl-nonatom->atts x.expr))))

       ((mv warnings sel) (vl-occform-argfix sel mod ialist warnings))
       ((mv warnings a)   (vl-occform-argfix a   mod ialist warnings))
       ((mv warnings b)   (vl-occform-argfix b   mod ialist warnings))

       (mods (vl-make-n-bit-mux width approxp))
       (modinst (vl-simple-instantiate (car mods) instname
                                       (list x.lvalue sel a b)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-shift-occform
  :short "Transform an assignment of a shift expression into occurrences."

  :long "<p>@('x') should have one of these forms:</p>
<ul>
 <li>@('assign lhs = a << b;')</li>
 <li>@('assign lhs = a >> b;')</li>
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of shift."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       ;; Make a module and instantiate it.
       (basename (case op
                   (:vl-binary-shl "vl_shl")
                   (:vl-binary-shr "vl_shr")))
       ((mv iname nf) (vl-namefactory-indexed-name basename nf))
       (mods (case op
               (:vl-binary-shl (vl-make-n-bit-shl-by-m-bits width (vl-expr->finalwidth arg2)))
               (:vl-binary-shr (vl-make-n-bit-shr-by-m-bits width (vl-expr->finalwidth arg2)))))
       (modinst (vl-simple-instantiate (car mods) iname
                                       (list x.lvalue arg1 arg2)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))


(def-vl-occform vl-bitselect-occform
  :short "Transform @('assign lhs = foo[i]') into occurrences (dynamic
bitselects only!)."

  :long "<p>This is only for dynamic bitselects, not static selects like
@('foo[3]').  See @(see vl-assign-occform): any sliceable expressions get
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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of bit-select."
                          :args (list x))))

       (warnings (if (vl-expr-resolved-p idx)
                     (fatal :type :vl-programming-error
                            :msg "~a0: how did this get called?  we're using a ~
                                  dynamic bitselect when a static one would do."
                            :args (list x))
                   warnings))

       ((mv warnings from) (vl-occform-argfix from mod ialist warnings))
       ((mv warnings idx)  (vl-occform-argfix idx mod ialist warnings))

       ((mv iname nf) (vl-namefactory-indexed-name "vl_bsel" nf))

       (mods (vl-make-n-bit-dynamic-bitselect-m from-width idx-width))
       (modinst (vl-simple-instantiate (car mods) iname
                                       (list x.lvalue from idx)
                                       :loc x.loc)))
    (occform-return :mods mods
                    :modinsts (list modinst))))



(def-vl-occform vl-ceq-occform
  :short "Transform an assignment of a @('===') expression into occurrences."

  :long "<p>@('x') should have the form: @('assign lhs = (a === b);')</p>"

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
         :warnings (fatal :type :vl-programming-error
                          :msg "~a0: bad widths in assignment of ceq."
                          :args (list x))))

       ((mv warnings arg1) (vl-occform-argfix arg1 mod ialist warnings))
       ((mv warnings arg2) (vl-occform-argfix arg2 mod ialist warnings))

       ;; Make a module and instantiate it.
       ((mv iname nf) (vl-namefactory-indexed-name "vl_ceq" nf))
       (mods          (vl-make-n-bit-ceq arg1width))
       (modinst       (vl-simple-instantiate (car mods) iname
                                             (list x.lvalue arg1 arg2)
                                             :loc x.loc)))
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
        (vl-plain-occform x nf mod ialist warnings))

       ((when (vl-fast-atom-p expr))
        ;; Any reasonable atom should be sliceable.
        (occform-return
         :assigns (list x)
         :warnings (fatal :type :vl-not-implemented
                          :msg "~a0: don't know how to occform ~x1 atom."
                          :args (list x (tag (vl-atom->guts expr))))))

       (op (vl-nonatom->op expr)))

    (case op
      ((:vl-unary-bitand :vl-unary-bitor :vl-unary-xor)
       (vl-unary-reduction-op-occform x nf mod ialist warnings))

      (:vl-unary-bitnot
       (vl-unary-not-occform x nf mod ialist warnings))

      ((:vl-binary-plus :vl-binary-minus)
       (vl-plusminus-occform x nf mod ialist warnings))

      ((:vl-binary-bitand :vl-binary-bitor :vl-binary-xor :vl-binary-xnor)
       (vl-basic-binary-op-occform x nf mod ialist warnings))

      ((:vl-binary-gte)
       (vl-gte-occform x nf mod ialist warnings))

      ((:vl-binary-ceq)
       (vl-ceq-occform x nf mod ialist warnings))

      ((:vl-bitselect)
       ;; Must be a dynamic bitselect...
       (vl-bitselect-occform x nf mod ialist warnings))

      ((:vl-qmark)
       (vl-mux-occform x nf mod ialist warnings))

      ((:vl-binary-shl :vl-binary-shr)
       (vl-shift-occform x nf mod ialist warnings))

      ((:vl-binary-times)
       (vl-mult-occform x nf mod ialist warnings))

      ((:vl-binary-div)
       (vl-div-occform x nf mod ialist warnings))

      ((:vl-binary-rem)
       (vl-rem-occform x nf mod ialist warnings))

      ;; Now these should all be handled above, since they should be sliceable.
      ((:vl-partselect-colon :vl-concat :vl-multiconcat)
       (occform-return
        :assigns (list x)
        :warnings (fatal :type :vl-programming-error
                         :msg "~a0: expected ~x1 operator to be sliceable!"
                         :args (list x op))))

      (otherwise
       (occform-return
        :assigns (list x)
        :warnings (fatal :type :vl-not-implemented
                         :msg "~a0: don't know how to occform ~x1 operator."
                         :args (list x op)))))))


(define vl-assignlist-occform ((x vl-assignlist-p)
                               (nf vl-namefactory-p)
                               (mod vl-module-p)
                               (ialist (equal ialist (vl-make-moditem-alist mod)))
                               (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (mods     vl-modulelist-p)
               (insts    vl-modinstlist-p)
               (assigns  vl-assignlist-p)
               (nf       vl-namefactory-p))
  :parents (occform)
  :short "Project @(see vl-assign-occform) across a list of assignments."
  (b* (((when (atom x))
        (mv (ok) nil nil nil (vl-namefactory-fix nf)))
       ((mv warnings mods1 modinsts1 assigns1 nf)
        (vl-assign-occform (car x) nf mod ialist warnings))
       ((mv warnings mods2 modinsts2 assigns2 nf)
        (vl-assignlist-occform (cdr x) nf mod ialist warnings))
       (mods     (append mods1 mods2))
       (modinsts (append modinsts1 modinsts2))
       (assigns  (append assigns1 assigns2)))
    (mv warnings mods modinsts assigns nf))
  ///
  (defmvtypes vl-assignlist-occform (nil true-listp true-listp true-listp nil)))


(define vl-module-occform ((x vl-module-p))
  :returns (mv (addmods vl-modulelist-p)
               (new-x   vl-module-p))
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        (mv nil (vl-module-fix x)))
       (nf (vl-starting-namefactory x))
       (ialist (vl-make-moditem-alist x))
       ((mv warnings addmods new-modinsts new-assigns nf)
        (vl-assignlist-occform x.assigns nf x ialist x.warnings))
       (- (fast-alist-free ialist))
       (new-x (change-vl-module x
                                :warnings warnings
                                :assigns  new-assigns
                                :modinsts (append new-modinsts x.modinsts))))
    (vl-free-namefactory nf)
    (mv addmods new-x))
  ///
  (defthm true-listp-of-vl-module-occform1
    (true-listp (mv-nth 0 (vl-module-occform x)))
    :rule-classes :type-prescription))


(define vl-modulelist-occform-aux ((x vl-modulelist-p))
  :returns (mv (addmods vl-modulelist-p)
               (new-x   vl-modulelist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv addmods1 car) (vl-module-occform (car x)))
       ((mv addmods2 cdr) (vl-modulelist-occform-aux (cdr x)))
       (addmods (append addmods1 addmods2))
       (new-x   (cons car cdr)))
    (mv addmods new-x))
  ///
  (defmvtypes vl-modulelist-occform-aux (true-listp true-listp)))


(define vl-modulelist-occform ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (b* (((mv new-mods x-prime)
        (vl-modulelist-occform-aux x))
       (- (clear-these-memoize-tables *vl-occform-memoize*))
       (new-mods-sort (mergesort new-mods))
       (full-mods     (append new-mods-sort x-prime))
       (all-names     (vl-modulelist->names full-mods))
       ((unless (uniquep all-names))
        (raise "Name collision")))
    full-mods)
  ///
  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-occform
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-occform x)))))

(define vl-design-occform ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-occform x.mods))))
