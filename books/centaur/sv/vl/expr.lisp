; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
(include-book "trunc")
(include-book "../mods/svmods")
(include-book "../svex/lattice")
(include-book "../svex/constraints")
(include-book "literal")
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/mlib/selfsize" :dir :system)
(include-book "centaur/vl/mlib/typedecide" :dir :system)
(include-book "centaur/vl/mlib/elabindex" :dir :system)
(include-book "../svex/select")
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(include-book "std/testing/assert-bang" :dir :system)

(defxdoc vl-expr-svex-translation
  :parents (vl-design->sv-design)
  :short "Compilation from (sized) @(see vl::vl) expressions into @(see
sv::svex) expressions."

  :long "<p>There are several top-level functions for converting a VL
expression into a @(see sv::svex) expression, including @(see
vl-expr-to-svex-untyped), @(see vl-expr-to-svex-selfdet), and @(see
vl-expr-to-svex-maybe-typed).</p>

<p>We assume that the expressions we are dealing with are sized.</p>

<p><b>The Garbage Convention</b>. Our goal is to produce svex expressions that
are \"correct\" at least for this size.  We don't care about the bits that are
\"past\" the expression's final width.</p>

<p>For example, if we are converting @('3'b100') into an svex expression, it
would be valid to just use @('(concat 3 #b100 anything)').</p>

<p>This has widespread consequences.</p>

<p>In many cases, we don't have to worry about the upper bits, because we know,
for instance, that after sizing, in a VL expression like @('a & b'), that the
widths of @('a') and @('b') agree with the final width of the whole @('a & b')
expression.  So any \"garbage\" in the upper bits can only affect the upper bits
of the result.</p>

<p>However, in certain cases we have to be more careful.  For instance, if we
are translating @('a < b'), then the svex semantics are that we do an infinite
width comparison, so we need to be careful to properly sign/zero extend the two
arguments to their appropriate, final value.</p>

<p>Why do it this way?  Some possible alternatives:</p>

<ul>

<li>Force everything past the final width to X.</li>

<li>Sign/zero extend everything so that every expression is correct out to
infinite width.</li>

</ul>

<p>Forcing the high bits to X has some appeal: it would be nice to know that
any accidental use of the upper bits would be conservative.  In most ways it
would be very similar to what we are doing now: we would still have to be
careful in cases like @('a < b') to mask out those Xes.  But we would also have
to do more to ensure that we were following this convention.  For instance, by
not caring about the upper bits, we don't have to do anything special when
translating sums: the carry from @('a + b') can go into the upper bits and it's
just garbage.  If we wanted all the upper bits to be X, we'd need to do extra
work to mask them out in this case.</p>

<p>The other alternative seems sort of more proactive: we would essentially be
fixing everything up to be the right size whether it needs to be fixed up or
not.  For instance, if we are translating something like @('(a + b) & c'), we
don't really need to know the true upper bits of @('a + b') or @('c').  We
suspect that arranging for every expression to be correct out to infinite width
would therefore incur some overhead.</p>")


(defxdoc sv::vl-expr.lisp :parents (vl-expr-svex-translation))

(local (xdoc::set-default-parents sv::vl-expr.lisp))

(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))


(local (in-theory (disable member-equal append
                           acl2::member-of-cons
                           true-listp len
                           vl-warninglist-p-when-subsetp-equal
                           acl2::list-fix-when-len-zero
                           sv::svarlist-addr-p-when-not-consp
                           acl2::consp-by-len
                           acl2::subsetp-member
                           acl2::subsetp-when-atom-right
                           acl2::list-fix-when-not-consp
                           not
                           cons-equal
                           acl2::member-equal-append
                           acl2::zp-open)))

;; (defthm len-cdr-when-consp
;;   (implies (consp x)
;;            (equal (len (cdr x))
;;                   (+ -1 (len x))))
;;   :hints(("Goal" :in-theory (enable len)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

(local (defthm len-posp-when-consp
         (implies (consp x)
                  (posp (len x)))
         :hints(("Goal" :in-theory (enable len)))
         :rule-classes :forward-chaining))

(local (defthm len-of-cdr
           (implies (posp (len x))
                    (equal (len (cdr x))
                           (1- (len x))))
           :hints(("Goal" :in-theory (enable len)))))


;; (fty::defalist vl-svexalist :key-type vl-scopeexpr :val-type sv::svex-p)

;; (fty::defalist vl-fnportalist :key-type vl-scopeexpr :val-type vl-portdecllist)


;; (defprod vl-svexconf
;;   :short "Static configuration object for expr to svex conversion."
;;   ((ss vl-scopestack-p
;;        "The scopestack at the source location of the expression.")
;;    (typeov vl-typeoverride-p "Scopeexprs mapped to resolved types")
;;    (fns    vl-svexalist-p "Function definition table")
;;    (fnports vl-fnportalist-p "Function portlist table")
;;    (params vl-svexalist-p "Parameter definition table")))

;; (define vl-svexconf-free ((x vl-svexconf-p))
;;   (b* (((vl-svexconf x)))
;;     (progn$ (fast-alist-free x.typeov)
;;             (fast-alist-free x.fns)
;;             (fast-alist-free x.params))))





(define svex-x ()
  :returns (svex sv::svex-p)
  :short "Infinite width X"
  (sv::svex-quote (sv::4vec-x)))


(define vl-bitlist->onset ((x vl-bitlist-p))
  :returns (onset natp :rule-classes :type-prescription)
  ;; Note: works LSB-first.  Reverse the bitlist held in a weirdint before calling.
  (if (atom x)
      0
    (acl2::logcons (case (vl-bit-fix (car x))
                     ((:vl-0val :vl-zval) 0)
                     (t 1))
                   (vl-bitlist->onset (cdr x)))))

(define vl-bitlist->offset ((x vl-bitlist-p))
  :returns (offset natp :rule-classes :type-prescription)
  ;; Note: works LSB-first.  Reverse the bitlist held in a weirdint before calling.
  (if (atom x)
      0
    (acl2::logcons (case (vl-bit-fix (car x))
                     ((:vl-1val :vl-zval) 0)
                     (t 1))
                   (vl-bitlist->offset (cdr x)))))

(define vl-bitlist->4vec ((msb-bits vl-bitlist-p))
  :short "Turn a vl-bitlist into a 4vec.  Assumes msb-first ordering, such as in a vl-weirdint."
  :returns (val sv::4vec-p)
  (let ((lsb-bits (rev (vl-bitlist-fix msb-bits))))
    (sv::4vec (vl-bitlist->onset lsb-bits)
                (lognot (vl-bitlist->offset lsb-bits)))))

(defmacro svex-int (&rest args) `(sv::svex-int . ,args))
(add-macro-alias svex-int sv::svex-int$inline)

(define svex-extend ((type vl-exprsign-p)
                     (width natp)
                     (x sv::svex-p))
  :short "Returns an svex representing the sign- or zero-extension of x at the given width."

  :long "<p>We don't have to extend/truncate operands when translating VL
expressions like @('a & b'), but we do need to do it to the inputs of
expressions like @('a < b'), to chop off any garbage in the upper bits.</p>"

  :returns (sv sv::svex-p)
  (if (vl-exprsign-equiv type :vl-signed)
      (sv::svex-signx width x)
    (sv::svex-zerox width x))
  ///
  (defthm svex-vars-of-svex-extend
    (implies (not (member v (sv::svex-vars x)))
             (not (member v (sv::svex-vars (svex-extend type width x)))))))

#!sv
(defines svex-variable-free-p
  (define svex-variable-free-p ((x svex-p))
    :measure (svex-count x)
    (svex-case x
      :call (svexlist-variable-free-p x.args)
      :quote t
      :var nil))
  (define svexlist-variable-free-p ((x svexlist-p))
    :measure (svexlist-count x)
    (if (atom x)
        t
      (and (svex-variable-free-p (car x))
           (svexlist-variable-free-p (cdr x)))))
  ///
  (defthm-svex-variable-free-p-flag
    (defthm eval-when-svex-variable-free-p
      (implies (and (syntaxp (not (equal env ''nil)))
                    (svex-variable-free-p x))
               (equal (svex-eval x env)
                      (svex-eval x nil)))
      :flag svex-variable-free-p)
    (defthm eval-when-svexlist-variable-free-p
      (implies (and (syntaxp (not (equal env ''nil)))
                    (svexlist-variable-free-p x))
               (equal (svexlist-eval x env)
                      (svexlist-eval x nil)))
      :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
      :flag svexlist-variable-free-p))
  (in-theory (Disable eval-when-svex-variable-free-p
                      eval-when-svexlist-variable-free-p))

  (memoize 'svex-variable-free-p :condition '(svex-case x :call))

  (fty::deffixequiv-mutual svex-variable-free-p))


#!sv
(defines svex-reduce-consts
  :verify-guards nil
  (define svex-reduce-consts ((x svex-p))
    :returns (new-x svex-p)
    :measure (svex-count x)
    (svex-case x
      :call (b* ((args (svexlist-reduce-consts x.args))
                 (val (svex-fn/args-xeval x.fn args)))
              (if (4vec-xfree-p val)
                  (svex-quote val)
                (svex-call x.fn args)))
      :otherwise (svex-fix x)))
  (define svexlist-reduce-consts ((x svexlist-p))
    :returns (new-x svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (cons (svex-reduce-consts (car x))
            (svexlist-reduce-consts (cdr x)))))
  ///
  (verify-guards svex-reduce-consts)

  (local (in-theory (disable svex-reduce-consts
                             svexlist-reduce-consts)))

  (local (defthm svex-fn/args-xeval-is-xeval
           (equal (svex-fn/args-xeval fn args)
                  (svex-xeval (svex-call fn args)))
           :hints(("Goal" :in-theory (enable svex-xeval svex-call-xeval)))))

  (local (defthm svex-apply-when-4vec-xfree-of-minval
           (implies (and (syntaxp (not (equal env ''nil)))
                         (4vec-xfree-p (svex-xeval (svex-call fn args))))
                    (equal (svex-apply fn (svexlist-eval args env))
                           (svex-xeval (svex-call fn args))))
           :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-of-minval
                                  (n (svex-call fn args))))))))
         

  (defthm-svex-reduce-consts-flag
    (defthm svex-reduce-consts-correct
      (equal (svex-eval (svex-reduce-consts x) env)
             (svex-eval x env))
      :flag svex-reduce-consts)
    (defthm svexlist-reduce-consts-correct
      (equal (svexlist-eval (svexlist-reduce-consts x) env)
             (svexlist-eval x env))
      :hints ((and stable-under-simplificationp
                   '(:expand ((svexlist-eval x env)))))
      :flag svexlist-reduce-consts)
    :hints ((acl2::just-expand-mrec-default-hint 'svex-reduce-consts id t world)))

  (deffixequiv-mutual svex-reduce-consts)

  (defthm-svex-reduce-consts-flag
    (defthm vars-of-svex-reduce-consts
      (implies (not (member v (svex-vars x)))
               (not (member v (svex-vars (svex-reduce-consts x)))))
      :flag svex-reduce-consts)
    (defthm vars-of-svexlist-reduce-consts
      (implies (not (member v (svexlist-vars x)))
               (not (member v (svexlist-vars (svexlist-reduce-consts x)))))
      :flag svexlist-reduce-consts)
    :hints ((acl2::just-expand-mrec-default-hint 'svex-reduce-consts id t
                                                 world)))

  (memoize 'svex-reduce-consts :condition '(svex-case x :call)))

;; #!sv
;; (define svex-maybe-reduce-to-const ((x svex-p))
;;   :returns (x1 svex-p)
;;   (b* ((x-eval (svex-xeval x)))
;;     (if (2vec-p x-eval)
;;         (svex-quote x-eval)
;;       (svex-fix x)))
;;   ///
;;   (defthm svex-maybe-reduce-to-const-correct
;;     (equal (svex-eval (svex-maybe-reduce-to-const x) env)
;;            (svex-eval x env))
;;     :hints(("Goal" :in-theory (enable svex-eval-when-2vec-p-of-minval)
;;             :expand ((:free (a env) (svex-eval (svex-quote a) env))) )))

;;   (defthmd svex-maybe-reduce-to-const-implies-env-irrelevant
;;     (implies (and (syntaxp (not (equal env ''nil)))
;;                   (equal (svex-kind (svex-maybe-reduce-to-const x)) :quote))
;;              (equal (svex-eval x env)
;;                     (svex-eval x nil)))
;;         :hints(("Goal" :in-theory (enable svex-eval-when-2vec-p-of-minval)
;;             :expand ((:free (a env) (svex-eval (svex-quote a) env))) )))

;;   (defthm svex-quote->val-of-maybe-reduce-to-const
;;     (implies (equal (svex-kind (svex-maybe-reduce-to-const x)) :quote)
;;              (equal (svex-quote->val (svex-maybe-reduce-to-const x))
;;                     (svex-eval x nil))))

;;   (defthm vars-of-svex-maybe-reduce-to-const
;;     (implies (not (member v (svex-vars x)))
;;              (not (member v (svex-vars (svex-maybe-reduce-to-const x)))))))


(define vl-string->bits ((x stringp) (n natp))
  :guard (<= (nfix n) (length x))
  :measure (nfix n)
  :returns (val natp)
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system)))
  (b* (((when (zp n)) 0)
       (charval (char-code (char x (1- n))))
       (rest (vl-string->bits x (1- n))))
    (logior (ash rest 8) charval)))


(define vl-value-to-svex ((x vl-value-p))
  :prepwork ((local (defthm vl-bit-p-of-vl-extint->value-forward
                      (vl-bit-p (vl-extint->value x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-extint->value x)))))))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (vl-value-case x
    :vl-constint (mv nil (svex-extend x.origsign x.origwidth (svex-int x.value)))
    :vl-weirdint (mv nil (svex-extend x.origsign (len x.bits)
                                      (sv::svex-quote (vl-bitlist->4vec (vl-weirdint->bits x)))))
    :vl-extint   (mv nil (case x.value
                           (:vl-1val (svex-int -1))
                           (:vl-0val (svex-int 0))
                           (:vl-xval (svex-x))
                           (:vl-zval (sv::svex-quote (sv::4vec-z)))))
    :vl-string   (mv nil (svex-int (vl-string->bits x.value (length x.value))))
    :otherwise   (mv (vmsg "Unsupported value type: ~a0" (make-vl-literal :val x))
                     (svex-x)))
  ///
  (defret vars-of-vl-value-to-svex
    (not (member v (sv::svex-vars svex)))))

(define vl-select-resolved-p ((x vl-select-p))
  (vl-select-case x
    :field t
    :index (vl-expr-resolved-p x.val)))

(define vl-selstep-resolved-p ((x vl-selstep-p))
  :enabled t
  (vl-select-resolved-p (vl-selstep->select x)))

(define vl-selstep->svex-name ((x vl-selstep-p))
  :guard (vl-selstep-resolved-p x)
  :guard-hints (("goal" :in-theory (enable vl-select-resolved-p)))
  :returns (name sv::name-p
                 :hints(("Goal" :in-theory (enable sv::name-p))))
  (b* ((sel (vl-selstep->select x)))
    (vl-select-case sel
      :field sel.name
      :index (vl-resolved->val sel.val))))


(define vl-seltrace-unres-count ((x vl-seltrace-p))
  :short "Checks that all indices in the seltrace are resolved expressions."
  :returns (count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (if (vl-selstep-resolved-p (car x)) 0 1)
       (vl-seltrace-unres-count (cdr x)))))


(define vl-seltrace-add-to-path ((x vl-seltrace-p)
                                 (path sv::path-p))
  :guard (equal (vl-seltrace-unres-count x) 0)
  :guard-hints (("goal" :in-theory (enable vl-seltrace-unres-count)))
  :returns (new-path sv::path-p)
  (if (atom x)
      (sv::path-fix path)
    (vl-seltrace-add-to-path
     (cdr x)
     (sv::make-path-scope
      :namespace (vl-selstep->svex-name (car x))
      :subpath path))))

(define vl-seltrace-to-path ((x vl-seltrace-p)
                             (path (or (not path)
                                       (sv::path-p path))))
  :short "Turns a seltrace object into an svex path."
  :long "<p>Note: This isn't the end of the story; we still need to deal with
e.g. bitselects, partselects, and nonconstant array selects.</p>"
  :returns (new-path (implies new-path (sv::path-p new-path))
                     "Empty indicates the seltrace was empty, as in just a bare
                      variable.")
  :guard (equal (vl-seltrace-unres-count x) 0)
  :guard-hints (("goal" :in-theory (enable vl-seltrace-unres-count)))
  (b* (((when (atom x))
        (and path (sv::path-fix path)))
       (path1 (if path
                  (sv::make-path-scope
                   :namespace (vl-selstep->svex-name (car x))
                   :subpath path)
                (sv::make-path-wire :name (vl-selstep->svex-name (car x))))))
    (vl-seltrace-add-to-path (cdr x) path1)))

(define vl-hidstep-resolved-p ((x vl-hidstep-p))
  :short "Checks that the index, if any, is resolved, and that the item has a name."
  (b* (((vl-hidstep x)))
    (or (not x.index) (vl-expr-resolved-p x.index))))

(define vl-hidstep->svex-index ((x vl-hidstep-p))
  :guard (vl-hidstep-resolved-p x)
  :guard-hints(("Goal" :in-theory (enable vl-hidstep-resolved-p)))
  :returns (index (implies index (sv::name-p index))
                 :hints(("Goal" :in-theory (enable sv::name-p))))
  (b* (((vl-hidstep x)))
    (and x.index (vl-resolved->val x.index))))

(define vl-hidtrace-resolved-p ((x vl-hidtrace-p))
  (if (atom x)
      t
    (and (vl-hidstep-resolved-p (car x))
         (vl-hidtrace-resolved-p (cdr x)))))


(define vl-hidtrace-add-to-path ((x vl-hidtrace-p)
                                 (path sv::path-p))
  :guard (vl-hidtrace-resolved-p x)
  :returns (new-path sv::path-p)
  :guard-hints (("goal" :in-theory (enable vl-hidtrace-resolved-p sv::name-p)))
  (if (atom x)
      (sv::path-fix path)
    (vl-hidtrace-add-to-path
     (cdr x)
     (b* ((idx (vl-hidstep->svex-index (car x)))
          (idxpath (if idx
                       (sv::make-path-scope :namespace idx :subpath path)
                     path)))
       (sv::make-path-scope
        :namespace (vl-hidstep->name (car x))
        :subpath idxpath)))))

(define vl-hidtrace-to-path ((x vl-hidtrace-p)
                             (path (or (not path)
                                       (sv::path-p path))))
  :guard (and (consp x)
              (vl-hidtrace-resolved-p x))
  :guard-hints (("goal" :in-theory (enable vl-hidtrace-resolved-p
                                           sv::name-p)))
  :returns (new-path sv::path-p)
  (if path
      (vl-hidtrace-add-to-path x path)
    (vl-hidtrace-add-to-path
     (cdr x)
     ;; NOTE: using the fact that the last element in a hid trace produced by
     ;; follow-hid has no index -- vl-follow-hidexpr-no-index-on-first
     (sv::make-path-wire :name (vl-hidstep->name (car x))))))

(define vl-upscope-to-svex-upscope ((vl-levels natp "number of levels up we're going")
                                    (ss vl-scopestack-p "scopestack we're traversing")
                                    &key
                                    ((strictp booleanp) 't))
  :returns (mv (err (implies err (vl-msg-p err)))
               (svex-levels (implies (not err) (natp svex-levels))
                            :rule-classes :type-prescription))
  :verify-guards nil
  (b* (((when (zp vl-levels)) (mv nil 0)))
    (vl-scopestack-case ss
      :null (mv (vmsg "Tried to go ~x0 level~s1 up from the empty scope"
                      vl-levels (if (eql vl-levels 1) "" "s"))
                nil)
      :global (mv (vmsg "Tried to go ~x0 level~s1 up from the global scope"
                        vl-levels (if (eql vl-levels 1) "" "s"))
                  nil)
      :local
      (b* ((type (vl-scope->scopetype ss.top))
           ((mv err incr)
            (case type
              ;; This says that each generate block and generate array
              ;; correspond to a single nesting of scopes in terms of SV
              ;; modules, and that blockstmt and forstmt scopes don't
              ;; correspond to additional nesting levels.  Basically, for the
              ;; former, we need to be sure to keep the scopes corresponding,
              ;; whereas for the latter the vl-svstmt transform takes care of
              ;; scoping and basically gets rid of local variables, so there
              ;; are no corresponding scopes in SV world.
              (:vl-genblock        (mv nil 1))
              (:vl-genarrayblock   (mv nil 1))
              (:vl-genarray        (mv nil 1))
              (:vl-blockstmt       (mv nil 0))
              (:vl-forstmt         (mv nil 0))
              (:vl-foreachstmt     (mv nil 0))

              ;; bozo -- this was 1 but I think it should be 0 for the same
              ;; reasons as blockstmt/forstmt.
              (:vl-fundecl         (mv nil 0))

              ;; (:vl-anonymous-scope (mv nil 1))
              (otherwise
               (if strictp
                   (mv (vmsg "Tried to go ~x0 level~s1 up through a scope of type ~x2"
                             vl-levels (if (eql vl-levels 1) "" "s") type)
                       nil)
                 ;; Non-strict: the variable name doesn't need to correlate to
                 ;; the svex module hierarchy -- likely because it's a
                 ;; parameter that's going to be replaced by its value.
                 (mv nil 0)))))
           ((when err) (mv err nil))
           ((mv err rest) (vl-upscope-to-svex-upscope (1- vl-levels) ss.super))
           ((when err) (mv err nil)))
        (mv nil (+ incr rest)))))
  ///
  (verify-guards vl-upscope-to-svex-upscope-fn))


#||

(trace$
 #!vl
 (vl-scopecontext-to-addr :entry (list 'vl-scopecontext-to-addr x path
                                       (vl-scopestack->path ss))))

(trace$
 #!vl (vl-design-addnames :entry (list 'vl-design-addnames
                                       (vl-pps-modulelist (vl-design->mods x)))
                          :exit (list 'vl-design-addnames
                                      (vl-pps-modulelist (vl-design->mods value)))))

(trace$
 #!vl (vl-design-elaborate-fn :entry (list 'vl-design-elaborate
                                       (vl-pps-modulelist (vl-design->mods x)))
                          :exit (list 'vl-design-elaborate
                                      (vl-pps-modulelist (vl-design->mods value)))))

||#

(define vl-scopecontext-to-addr ((x vl-scopecontext-p)
                                 (ss vl-scopestack-p)
                                 (path sv::path-p)
                                 &key
                                 ((strictp booleanp) 't))
  :short "Create an svex address from a path, based on which scope the scopecontext
          object indicates."
  :long "<p>Svex supports three kinds of addresses -- see @(see sv::address)
for more.  This function tries to determine the right kind of address to make
from a VL hid expression by looking up the basename of the path in the
scopestack to see where it was found.</p>

<p>The scopecontext tells us almost what we need to know to make a proper svex
address.  Either:</p>

<ul>
<li>It's at root scope.  We make a root address.</li>

<li>It's in a package or module scope.  We don't support this yet, but they'll
translate to something based at the root scope.</li>

<li>It's at local scope, N levels up.  We make a local address, but we have to
translate the number of levels by examining the scopestack. -- see below.</li>

</ul>

<p>There is a subtle disconnect between svex's concept of scopes and VL's.  In
VL, if you're inside a generate block in a module, you probably have three
scope levels: the block, the module, and the global scope.  In svex, if you're
inside the same block, you might be inside several more levels of scope if the
module is instantiated deep in the hierarchy, or if the module is the top
module, you might just be inside the block within the module (so only two
levels deep).  In translating between these we assume that VL scopes basically
consist of a single global scope, the single module scope, and some number of
nested block scopes.  In translating to svex, we require that the number of
levels up only includes these nested block scopes.  We also need to be careful
to be consistent with our scoping conventions -- most particularly, a generate
array (the elaborated result of a generate loop) has a level of scoping for the
array itself, and an additional one for each of the blocks in the array (the
replicated loop bodies).  On the other hand, statement scopes are handled by
the vl-svstmt transform which eliminates local variables, so subscopes within
statements are not related to svex scopes. Vl-upscope-to-svex-upscope accounts
for these issues.</p>

<p>For package and module contexts, we produce an error because variables in
those scopes aren't yet supported.  We also return an address, however, because
we use this for resolving function names, in which case the error can be
ignored.</p>"
  :returns (mv (err (iff (vl-msg-p err) err))
               (addr (and (implies (not err) (sv::address-p addr))
                          (implies addr (sv::address-p addr)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  (vl-scopecontext-case x
    :local (b* (((mv err levels)
                 (vl-upscope-to-svex-upscope x.levels ss :strictp strictp))
                ((when err) (mv err nil)))
             (mv nil
                 (sv::make-address
                  :path path
                  :scope levels)))
    :root  (mv nil
               (sv::make-address :path path :scope :root))
    :package (mv (and strictp (vmsg "Package-scoped variables aren't yet supported"))
                 (sv::make-address :scope :root
                                     :path (sv::make-path-scope
                                            :namespace (vl-package->name x.pkg)
                                            :subpath path)))
    :module (mv (and strictp (vmsg "Module-scoped variables aren't yet supported"))
                (sv::make-address :scope :root
                                    :path (sv::make-path-scope
                                           :namespace (vl-module->name x.mod)
                                           :subpath path)))
    :interface (mv (and strictp (vmsg "Module-scoped variables aren't yet supported"))
                   (sv::make-address :scope :root
                                     :path (sv::make-path-scope
                                            :namespace (vl-interface->name x.iface)
                                            :subpath path)))
    ))

(define vl-seltrace-type ((x vl-seltrace-p)
                          (base-type vl-datatype-p))
  :guard (and (vl-seltrace-usertypes-ok x)
              (vl-datatype-resolved-p base-type))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
  :returns (type vl-datatype-p)
  (if (consp x)
      (b* (((vl-selstep sel) (car x)))
        sel.type)
    (vl-datatype-fix base-type))
  ///
  (std::defret usertypes-ok-of-vl-seltrace-type/ss
    (implies (and (vl-seltrace-usertypes-ok x)
                  (vl-datatype-resolved-p base-type))
             (vl-datatype-resolved-p type))
    :hints(("Goal" :in-theory (enable vl-operandinfo-usertypes-ok)))))

(define vl-operandinfo-base-svar ((x vl-operandinfo-p)
                                  (outer-ss vl-scopestack-p)
                                  &key
                                  ((strictp booleanp) 't))
  :guard (and (vl-operandinfo-usertypes-ok x)
              (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace x)))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svar (implies (not err) (sv::svar-p svar))))
  (b* (((vl-operandinfo x))
       (path (vl-hidtrace-to-path x.hidtrace nil))
       ((mv err addr)
        (vl-scopecontext-to-addr x.context outer-ss path :strictp strictp))
       ((when err) (mv err nil)))
    (mv nil (sv::make-svar :name addr)))
  ///
  (defret vars-of-vl-operandinfo-base-svar
    (implies (not err)
             (sv::svar-addr-p svar))
    :hints(("Goal" :in-theory (enable sv::svar-addr-p)))))

;; (define vl-seltrace-to-svex-var ((x vl-seltrace-p)
;;                                  (opinfo vl-operandinfo-p)
;;                                  (outer-ss vl-scopestack-p))
;;   :short "Takes a fully resolved seltrace and the operandinfo of which it is a
;;           part and returns an svex variable created from its address."
;;   :guard (and (vl-operandinfo-usertypes-ok opinfo)
;;               (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo))
;;               (equal (vl-seltrace-unres-count x) 0))
;;   :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (svex sv::svex-p))
;;   (b* (((mv err svar) (vl-seltrace-to-svar x opinfo outer-ss))
;;        ((when err) (mv err (svex-x))))
;;     (mv nil (sv::make-svex-var :name svar)))
;;   ///
;;   (defret vars-of-vl-seltrace-to-svex-var
;;     (sv::svarlist-addr-p (sv::svex-vars svex)))

;;   (defthm svex-select-p-of-vl-seltrace-to-svex-var
;;     (sv::svex-select-p (mv-nth 1 (vl-seltrace-to-svex-var x opinfo outer-ss)))
;;     :hints(("Goal" :in-theory (enable ::svex-select-p)))))

(define vl-datatype-index-is-bitselect ((x vl-datatype-p))
  ;; This doesn't check for the error if e.g. we apply an index to a 1-bit
  ;; coretype with no pdims.
  :guard (vl-datatype-resolved-p x)
  (b* ((x (vl-maybe-usertype-resolve x))
       (udims (vl-datatype->udims x))
       (pdims (vl-datatype->pdims x))
       ((when (consp udims)) nil)
       ((when (atom pdims))
        ;; It's a bitselect if we have a packed type.
        (vl-datatype-packedp x))
       ;; Now get the type after indexing in once.
       (x-minus-1d (vl-datatype-update-pdims (cdr pdims) x))
       (x-minus-1d (vl-maybe-usertype-resolve x-minus-1d)))
    ;; We now have a bitselect only if the base type is a 1-bit coretype with no dims.
    (and (atom (vl-datatype->pdims x-minus-1d))
         (atom (vl-datatype->udims x-minus-1d))
         (vl-datatype-case x-minus-1d
           :vl-coretype (b* (((vl-coredatatype-info xinfo)
                              (vl-coretypename->info x-minus-1d.name)))
                          (eql xinfo.size 1))
           :otherwise nil))))

(define vl-structmemberlist-shift-bits ((x vl-structmemberlist-p)
                                        (field stringp))
  ;; NOTE: x should be REVERSED from the normal order here.
  :guard (vl-structmemberlist-resolved-p x)
  :verify-guards nil
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (natp shift)) :rule-classes :type-prescription))
  (b* ((field (string-fix field))
       ((when (atom x))
        (mv (vmsg "Field not found: ~s0" field) nil))
       ((vl-structmember x1) (car x))
       ((when (equal x1.name field)) (mv nil 0))
       ((mv err size) (vl-datatype-size x1.type))
       ((when err) (mv err nil))
       ((unless size) (mv (vmsg "Couldn't size struct member type: ~a0" x1.type) nil))
       ((mv err rest) (vl-structmemberlist-shift-bits (cdr x) field))
       ((when err) (mv err nil)))
    (mv nil (+ size rest)))
  ///
  (verify-guards vl-structmemberlist-shift-bits))


#|
(trace$ #!vl (vl-datatype-field-shift-amount
              :entry (list 'vl-datatype-field-shift-amount
                           (with-local-ps (vl-pp-datatype x))
                           (with-local-ps (vl-pp-dimensionlist
                                           (vl-datatype->udims x)))
                           field)
              :exit (list 'vl-datatype-field-shift-amount
                          (car values)
                          (cadr values))))

|#
(define vl-datatype-field-shift-amount ((x vl-datatype-p)
                                        (field stringp))
  :prepwork ((local (defthm vl-structmemberlist-resolved-p-of-append
                      (implies (and (vl-structmemberlist-resolved-p x)
                                    (vl-structmemberlist-resolved-p y))
                               (vl-structmemberlist-resolved-p (append x y)))
                      :hints(("Goal" :in-theory (enable append)))))
             (local (defthm vl-structmemberlist-resolved-p-of-rev
                      (implies (vl-structmemberlist-resolved-p x)
                               (vl-structmemberlist-resolved-p (rev x)))
                      :hints(("Goal" :in-theory (enable rev))))))
  :guard (vl-datatype-resolved-p x)
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (integerp shift)) :rule-classes :type-prescription))
  (b* ((field (string-fix field))
       (x (vl-maybe-usertype-resolve x))
       (udims (vl-datatype->udims x))
       (pdims (vl-datatype->pdims x))
       ((when (or (consp udims) (consp pdims)))
        (mv (vmsg "Can't select field ~s0 from datatype ~a1 because it has dimensions"
                  field x)
            nil)))
    (vl-datatype-case x
      :vl-union (if (vl-find-structmember field x.members)
                    ;; all union fields are right-aligned
                    (mv nil 0)
                  (mv (vmsg "~s0 is not a member of ~a1" field x) nil))
      :vl-struct (vl-structmemberlist-shift-bits (rev x.members) field)
      :otherwise (mv (vmsg "Can't select field ~s0 from non-struct/union datatype ~a1"
                           field x)
                     nil))))

#|
(trace$ #!vl (vl-datatype-index-shift-amount
              :entry (list 'vl-datatype-index-shift-amount

                           (with-local-ps (vl-pp-datatype x))
                           (with-local-ps (vl-pp-dimensionlist
                                           (vl-datatype->udims x)))
                           idx)
              :exit (list 'vl-datatype-index-shift-amount
                          (car values)
                          (cadr values))))

|#

(define vl-datatype-slot-width/range ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :returns (mv (err (iff (vl-msg-p err) err))
               (slotwidth natp :rule-classes :type-prescription)
               (range-left integerp :rule-classes :type-prescription)
               (range-right integerp :rule-classes :type-prescription))
  (b* ((x (vl-maybe-usertype-resolve x))
       ((mv err ?caveat slottype dim) (vl-datatype-remove-dim x))
       ((when err) (mv err 0 0 0))
       ((mv err size) (vl-datatype-size slottype))
       ((when err) (mv err 0 0 0))
       ((unless size) (mv (vmsg "Couldn't size array slot type ~a0" slottype) 0 0 0))
       ((unless (vl-dimension-case dim :range))
        (mv (vmsg "unsupported dimension on ~a0" x) 0 0 0))
       ((vl-range range) (vl-dimension->range dim))
       ((unless (vl-range-resolved-p range))
        (mv (vmsg "unresolved dimension on array type ~a0" x) 0 0 0))
       (msb (vl-resolved->val range.msb))
       (lsb (vl-resolved->val range.lsb)))
    (mv nil size msb lsb)))

(define vl-index-shift-amount ((size natp)
                               (msb integerp)
                               (lsb integerp)
                               (idx sv::svex-p))
  :returns (shift (implies (not err) (sv::svex-p shift)))
  (b* ((size (lnfix size))
       (msb (lifix msb))
       (lsb (lifix lsb))
       ((when (>= msb lsb))
        ;; BOZO: If we use this function to get the shift amount for the LSB of
        ;; an ascending partselect, e.g. [4:6], on a declared range with equal
        ;; MSB/LSB [5:5], then we're going to get a weird result: a shift of
        ;; +2, meaning we're already out of bounds to the left on the LSB; then
        ;; we'll calculate a width of 3 for the partselect, which means we're
        ;; actually accessing [8:6] rather than [4:6] -- in particular, the
        ;; existant bits of the selected variable aren't part of the range
        ;; we're accessing.  Oddly enough, this seems to agree with VCS
        ;; (ncverilog seems to return all Xes when any part of the select is
        ;; out of bounds).
        (sv::svex-reduce-consts
         (sv::svcall * (svex-int size)
                     (sv::svcall sv::b- idx (svex-int lsb))))))
    (sv::svex-reduce-consts
     (sv::svcall * (svex-int size)
                 (sv::svcall sv::b- (svex-int lsb) idx))))
  ///
  (defret vars-of-vl-index-shift-amount
    (implies (not (member v (sv::svex-vars idx)))
             (not (member v (sv::svex-vars shift))))))

(define vl-datatype-index-shift-amount ((x vl-datatype-p)
                                        (idx sv::svex-p))
  :guard (vl-datatype-resolved-p x)
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (sv::svex-p shift))))
  (b* (((mv err size msb lsb) (vl-datatype-slot-width/range x))
       ((when err) (mv err nil)))
    (mv nil (vl-index-shift-amount size msb lsb idx)))
  ///
  (defret vars-of-vl-datatype-index-shift-amount
    (implies (and (not err)
                  (not (member v (sv::svex-vars idx))))
             (not (member v (sv::svex-vars shift))))))



;; #!sv
;; (define 4vec-lsb-shift ((shift-amt 4vec-p)
;;                         (x 4vec-p))
;;   :returns (res 4vec-p)
;;   (if (2vec-p shift-amt)
;;       (b* ((sh (2vec->val shift-amt)))
;;         (if (< sh 0)
;;             (4vec-concat (2vec (- sh)) (4vec-x) x)
;;           (4vec-rsh (2vec sh) x)))
;;     (4vec-x)))

;; #!sv
;; (define svex-lsb-shift ((shift-amt svex-p)
;;                         (x svex-p))
;;   :short "Adjust an expression for the LSB end of a select."
;;   :long "<p>When computing the svex for an array access like @('v[i]'),
;; typically you wanto to right-shift @('v') by some number of bits, depending on
;; @('i') and the declared range of @('v').  But if @('i') is out of the bounds of
;; that declared range, you instead want to return @('X').  More generally, if you
;; have a ranged select like @('v[u:i]'), then if @('i') is out of bounds on the
;; LSB side of the declared range, you want to concatenate some number of @('X')
;; bits onto @('v').  This computes that shifted/concatenated version of @('v'),
;; if the shift amount is computed elsewhere.</p>"

;;   :returns (res svex-p)
;;   (b* ((sh (svex-reduce-consts shift-amt)))
;;     (svex-case sh
;;       :quote (if (2vec-p sh.val)
;;                  (if (<= 0 (2vec->val sh.val))
;;                      (svex-rsh (2vec->val sh.val) x)
;;                    (svex-concat (- (2vec->val sh.val)) (svex-x) x))
;;                (svex-x))
;;       :otherwise ;; (b* ((concat-amt (svcall ?
;;                  ;;                                (svcall < sh (vl::svex-int 0))
;;                  ;;                                (svcall u- sh)
;;                  ;;                                (vl::svex-int 0)))
;;                  ;;      (rsh-amt    (svcall ?
;;                  ;;                                (svcall < sh (vl::svex-int 0))
;;                  ;;                                (vl::svex-int 0)
;;                  ;;                                sh)))
;;                  ;;   (svcall concat
;;                  ;;           concat-amt
;;                  ;;           (svex-x)
;;                  ;;           (svcall rsh rsh-amt x)))
;;       (svcall ?
;;               (svcall < sh (vl::svex-int 0))
;;               ;; if the shift is negative, we're concatenating Xes, otherwise
;;               ;; we're right-shifting.
;;               (svcall concat (svcall u- sh) (svex-x) x)
;;               (svcall rsh sh x))))
;;   ///
;;   (local (defthm 4vec-<-of-non-2vec
;;            (implies (not (2vec-p x))
;;                     (equal (4vec-< x y) (4vec-x)))
;;            :hints(("Goal" :in-theory (enable 4vec-<)))))

;;   (local (defthm 4vec-uminus-of-non-2vec
;;            (implies (not (2vec-p x))
;;                     (equal (4vec-uminus x) (4vec-x)))
;;            :hints(("Goal" :in-theory (enable 4vec-uminus)))))

;;   (local (defthm 4vec-concat-of-non-2vec
;;            (implies (not (2vec-p x))
;;                     (equal (4vec-concat x y z) (4vec-x)))
;;            :hints(("Goal" :in-theory (enable 4vec-concat)))))

;;   (local (in-theory (disable 4vec->lower-when-2vec-p)))


;;   (local (defthm svex-quote->val-of-reduce-consts
;;            (implies (equal (svex-kind (svex-reduce-consts x)) :quote)
;;                     (equal (svex-eval x env)
;;                            (svex-quote->val (svex-reduce-consts x))))
;;            :hints (("goal" :use ((:instance svex-reduce-consts-correct))
;;                     :in-theory (e/d (svex-eval-when-quote)
;;                                     (svex-reduce-consts-correct))))))

;;   (defthm svex-lsb-shift-correct
;;     (equal (svex-eval (svex-lsb-shift shift-amt x) env)
;;            (4vec-lsb-shift (svex-eval shift-amt env)
;;                            (svex-eval x env)))
;;     :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4vec-lsb-shift)
;;             :rw-cache-state nil)
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable 4vec-< 4vec-? 3vec-? 4vec-uminus)))))

;;   (defthm vars-of-svex-lsb-shift
;;     (implies (and (not (member v (svex-vars shift-amt)))
;;                   (not (member v (svex-vars x))))
;;              (not (member v (svex-vars (svex-lsb-shift shift-amt x)))))))

;; (define vl-seltrace-split ((x vl-seltrace-p)
;;                            (unres-count (equal (vl-seltrace-unres-count x)
;;                                                unres-count)))
;;   :short "Splits a seltrace at the point where all remaining indices are resolved."
;;   :prepwork ((local (in-theory (enable vl-seltrace-unres-count))))
;;   :returns (mv (unres vl-seltrace-p)
;;                (res vl-seltrace-p))
;;   :measure (len x)
;;   (if (mbe :logic (equal (vl-seltrace-unres-count x) 0)
;;            :exec (zp unres-count))
;;       (mv nil (vl-seltrace-fix x))
;;     (b* (((mv unres res) (vl-seltrace-split (cdr x)
;;                                             (if (vl-selstep-resolved-p (car x))
;;                                                 unres-count
;;                                               (1- unres-count)))))
;;       (mv (cons (vl-selstep-fix (car x)) unres) res)))
;;   ///
;;   (defret vl-seltrace-usertypes-ok-of-vl-seltrace-split
;;     (implies (vl-seltrace-usertypes-ok x)
;;              (and (vl-seltrace-usertypes-ok unres)
;;                   (vl-seltrace-usertypes-ok res)))
;;     :hints(("Goal" :in-theory (enable vl-seltrace-usertypes-ok))))

;;   (defret vl-seltrace-index-count-of-vl-seltrace-split
;;     (<= (vl-seltrace-index-count unres)
;;         (vl-seltrace-index-count x))
;;     :hints(("Goal" :in-theory (enable vl-seltrace-index-count)))
;;     :rule-classes :linear)

;;   (defret vl-seltrace-unres-count-of-vl-seltrace-split
;;     (and (equal (vl-seltrace-unres-count unres)
;;                 (vl-seltrace-unres-count x))
;;          (equal (vl-seltrace-unres-count res) 0))
;;     :rule-classes :linear)

;;   (defret len-of-vl-seltrace-split-parts
;;     (= (+ (len unres) (len res)) (len x))
;;     :rule-classes (:rewrite :linear))

;;   (defret vl-seltrace-index-count-of-vl-seltrace-split-parts
;;     (= (+ (vl-seltrace-index-count unres) (vl-seltrace-index-count res))
;;        (vl-seltrace-index-count x))
;;     :hints(("Goal" :in-theory (enable vl-seltrace-index-count)))
;;     :rule-classes (:rewrite :linear)))





(define vl-seltrace-to-svex-select
  ((x vl-seltrace-p)
   (indices sv::svexlist-p)
   (base-type vl-datatype-p "The type of the variable that the selects are indexing into.")
   (base-svar sv::svar-p)
   (outer-ss vl-scopestack-p))
  :guard (and (vl-seltrace-usertypes-ok x)
              (vl-datatype-resolved-p base-type)
              (>= (len indices)
                  (vl-seltrace-index-count x))
              ;; (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo))
              )
  :verify-guards nil
  :returns (mv (err (iff (vl-msg-p err) err))
               (select (implies (not err) (sv::svex-select-p select))))
  :measure (len x)
  :prepwork ((local (defthm unres-count-when-atom
                      (implies (atom x)
                               (equal (vl-seltrace-unres-count x) 0))
                      :hints(("Goal" :in-theory (enable vl-seltrace-unres-count)))))
             (local (defthm consp-when-unres-count
                      (implies (not (equal (vl-seltrace-unres-count x) 0))
                               (consp x))
                      :hints(("Goal" :in-theory (enable vl-seltrace-unres-count)))
                      :rule-classes :forward-chaining)))
  (b* ((type (vl-seltrace-type x base-type))
       ((mv err size) (vl-datatype-size type))
       ((when err) (mv err nil))
       ((unless size) (mv (vmsg "Could not size datatype ~s0" type) nil))

       ((when (atom x))
        (mv nil (sv::make-svex-select-var :name base-svar :width size)))


       ;; Unres-count nonzero implies (consp x)
       ((vl-selstep step) (car x))



       (rest-type (vl-seltrace-type (cdr x) base-type))
       (rest-type (vl-maybe-usertype-resolve rest-type))

       ((mv err shift-amt)
        (vl-select-case step.select
          :field (b* (((mv err idx)
                       (vl-datatype-field-shift-amount rest-type step.select.name))
                      ((when err) (mv err idx)))
                   (mv nil (svex-int idx)))
          :index (vl-datatype-index-shift-amount rest-type (car indices))))
       ((when err) (mv err nil))

       ((mv err rest) (vl-seltrace-to-svex-select
                       (cdr x)
                       (vl-select-case step.select
                         :field indices
                         :index (cdr indices))
                       base-type
                       base-svar
                       outer-ss))
       ((when err) (mv err nil)))
    (mv err (sv::make-svex-select-part :lsb shift-amt :width size :subexp rest)))
  ///

  (local (in-theory (disable (:d vl-seltrace-to-svex-select))))

  (local (defthm equal-len-0
           (equal (equal (len x) 0)
                  (atom x))
           :hints(("Goal" :in-theory (enable len)))))

  (local (defthm consp-by-len-forward
           (implies (equal (len x) n)
                    (if (equal n 0)
                        (atom x)
                      (consp x)))
           :hints(("Goal" :in-theory (enable len)))
           :rule-classes :forward-chaining))

  (verify-guards vl-seltrace-to-svex-select
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable vl-seltrace-usertypes-ok
                                      vl-seltrace-unres-count
                                      vl-seltrace-index-count
                                      vl-select-resolved-p)))))

  (defret vars-of-vl-seltrace-to-svex-select
    (implies (and (not (member v (double-rewrite (sv::svexlist-vars indices))))
                  (not (equal v (sv::svar-fix base-svar)))
                  (not err))
             (not (member v (sv::svex-select-vars select))))
    :hints(("Goal" :in-theory (enable vl-seltrace-to-svex-select
                                      sv::svex-select-vars
                                      sv::svex-select->indices
                                      sv::svex-select-inner-var
                                      acl2::member-of-cons)))))


(define vl-operandinfo-to-svex-preproc ((x vl-operandinfo-p)
                                        (indices sv::svexlist-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (new-x vl-operandinfo-p)
               (new-indices sv::svexlist-p))
  :guard (and (vl-operandinfo-usertypes-ok x)
              (equal (len indices)
                     (vl-operandinfo-index-count x)))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-index-count
                                           vl-operandinfo-usertypes-ok
                                           vl-seltrace-usertypes-ok
                                           vl-seltrace-index-count)))
  :prepwork ((local (defthm natp-abs
                      (implies (integerp a)
                               (natp (abs a)))
                      :rule-classes :type-prescription))
             (local (in-theory (disable abs))))
  :short "Preprocesses an operandinfo, changing an outer bitselect or partselect
          into a @('+:') style partselect."
  :long "<p>This is just a code-simplifying step so that we don't have to deal
with so many separate cases later.</p>

<p>Note: This function's correctness depends on the ordering in which indices
are listed by @(see vl-operandinfo->indices), so keep these two functions in
sync.</p>

<p>The result is an operandinfo with the following characteristics:</p>

<ul>
<li>The select trace has no bitselect; it's just vector-level operations all
the way.</li>

<li>If we have a partselect, it's a plusminus select with resolved width.</li>
</ul>
"
  (b* ((indices (sv::svexlist-fix indices))
       ((vl-operandinfo x) (vl-operandinfo-fix x)))
    (vl-partselect-case x.part
      :none (b* (((when (atom x.seltrace)) ;; no selects so no bitselect
                  (mv nil x indices))
                 ((vl-selstep sel1) (car x.seltrace))
                 ((unless (vl-select-case sel1.select :index))
                  ;; final select is a field access, so not a bitselect
                  (mv nil x indices))
                 (type (vl-seltrace-type (cdr x.seltrace) x.hidtype))
                 ((unless (vl-datatype-index-is-bitselect type))
                  ;; final index, but not a bitselect
                  (mv nil x indices))
                 ((vl-select-index idx) sel1.select)
                 ((cons bitselect-index rest-indices) indices))
              ;; Have a bitselect.  Change it into a width-1 plusminus select
              ;; and correct the indices.
              (mv nil
                  (change-vl-operandinfo
                   x
                   :seltrace (cdr x.seltrace)
                   :part (vl-plusminus->partselect
                          (make-vl-plusminus :width (vl-make-index 1)
                                             :base idx.val)))
                  ;; in sync with vl-operandinfo->indices,
                  ;; index order is base, width, seltrace
                  (list* (sv::svex-fix bitselect-index) (svex-int 1) rest-indices)))
      :range ;; turn it into a plusminus select
      (b* (((list* ?msb-index ?lsb-index rest-indices) indices)
           ((unless (and (vl-expr-resolved-p x.part.msb)
                         (vl-expr-resolved-p x.part.lsb)))
            (mv (vmsg "Unresolved partselect range") x indices))
           (msb (vl-resolved->val x.part.msb))
           (lsb (vl-resolved->val x.part.lsb))
           (minusp (< msb lsb))
           (width (+ 1 (abs (- msb lsb))))
           (new-part (vl-plusminus->partselect
                      (make-vl-plusminus
                       :base x.part.lsb
                       :width (vl-make-index width)
                       :minusp minusp))))
        (mv nil
            (change-vl-operandinfo x :part new-part)
            (list* (svex-int lsb) (svex-int width) rest-indices)))

      :plusminus
      ;; already a plusminus, so no fixup.  Just check whether the width is resolved.
      (b* (((unless (b* ((width (cadr indices)))
                      (sv::svex-case width
                        :quote (and (sv::2vec-p width.val)
                                    (natp (sv::2vec->val width.val)))
                        :otherwise nil)))
            ;;(vl-expr-resolved-p x.part.width))
            (mv (vmsg "Unresolved plusminus select width") x indices)))
        (mv nil x indices))))
  ///


  (defret vl-operandinfo-usertypes-ok-of-vl-operandinfo-to-svex-preproc
    (implies (vl-operandinfo-usertypes-ok x)
             (vl-operandinfo-usertypes-ok new-x))
    :hints(("Goal" :in-theory (enable vl-operandinfo-usertypes-ok
                                      vl-seltrace-usertypes-ok))))

  (defret len-indices-of-vl-operandinfo-to-svex-preproc
    (implies (equal (len indices)
                    (vl-operandinfo-index-count x))
             (equal (len new-indices)
                    (vl-operandinfo-index-count new-x)))
    :hints(("Goal" :in-theory (enable vl-operandinfo-index-count
                                      vl-seltrace-index-count
                                      len))))

  (defret partselect-kind-of-vl-operandinfo-to-svex-preproc
    (implies (not err)
             (or (equal (vl-partselect-kind
                         (vl-operandinfo->part new-x))
                        :none)
                 (equal (vl-partselect-kind
                         (vl-operandinfo->part new-x))
                        :plusminus)))
    :rule-classes
    ((:forward-chaining :trigger-terms
      ((vl-partselect-kind
        (vl-operandinfo->part
         (mv-nth 1 (vl-operandinfo-to-svex-preproc x indices))))))))

  (defret vars-of-vl-operandinfo-to-svex-preproc
    (implies (not (member v (sv::svexlist-vars indices)))
             (not (member v (sv::svexlist-vars new-indices)))))

  (defret constant-width-of-vl-operandinfo-to-svex-preproc-width
    (implies (and (not err)
                  (not (equal (vl-partselect-kind
                         (vl-operandinfo->part new-x))
                        :none)))
             (b* ((sv::width (cadr new-indices)))
               #!sv (and (equal (svex-kind width) :quote)
                         (equal (4vec->lower (svex-quote->val width))
                                (4vec->upper (svex-quote->val width)))
                         (natp (4vec->upper (svex-quote->val width))))))
    :hints(("Goal" :in-theory (enable svex-int)))))


;; (trace$
;;  #!vl (vl-plusminus-partselect->svex
;;        :entry (list 'vl-plusminus-partselect->svex
;;                     x
;;                     (with-local-ps (vl-pp-datatype type))
;;                     (with-local-ps (vl-pp-plusminus psel))
;;                     :base base-svex :width width-svex)
;;        :exit (b* (((list err svex) values))
;;                (if err
;;                    (list 'vl-plusminus-partselect->svex
;;                          (with-local-ps (vl-cw "~@0" err)))
;;                  (list 'vl-plusminus-partselect->svex svex)))))

(define vl-plusminus-partselect->svex ((x sv::svex-select-p "select to apply the partselect to")
                                       (type vl-datatype-p "type of base expr")
                                       (psel vl-plusminus-p)
                                       (base-svex sv::svex-p "base index")
                                       (width natp "width index"))
  :short "This ONLY shifts the base expression to the right point for the partselect;
          it does not truncate it at the right width."
  :guard (vl-datatype-resolved-p type)
  :returns (mv (err (iff (vl-msg-p err) err))
               (result (implies (not err) (sv::svex-select-p result))))
  (b* (((vl-plusminus psel))
       ((mv err slotsize dim-msb dim-lsb) (vl-datatype-slot-width/range type))
       ((when err) (mv err nil))
       (downp (<= dim-lsb dim-msb))
       (width-svex (svex-int (lnfix width)))
       (sel-lsb (if downp
                    (if psel.minusp
                        ;; base is the msb, compute the lsb
                        (sv::svcall + base-svex
                                    (sv::svcall + (svex-int 1)
                                                (sv::svcall sv::u- width-svex)))
                      ;; base is the lsb
                      base-svex)
                  (if psel.minusp
                      base-svex
                    ;; base is the msb, compute the lsb
                    (sv::svcall + base-svex
                                (sv::svcall + (svex-int -1) width-svex)))))
       (shift-amt
        (vl-index-shift-amount slotsize dim-msb dim-lsb sel-lsb))
       (width (* slotsize (lnfix width))))
    (mv nil (sv::make-svex-select-part :lsb shift-amt :width width :subexp x)))

  ///
  (defret vars-of-vl-plusminus-partselect->svex
    (implies (and (not (member v (double-rewrite (sv::svex-select-vars x))))
                  (not (member v (double-rewrite (sv::svex-vars base-svex))))
                  (not err))
             (not (member v (sv::svex-select-vars result))))
    :hints(("Goal" :in-theory (enable sv::svex-select-vars
                                      sv::svex-select->indices
                                      sv::svex-select-inner-var
                                      acl2::member-of-cons)))))



(local (include-book "std/lists/nthcdr" :dir :system))
;; (local (include-book "std/lists/take" :dir :system))

(local #!sv (std::deflist svexlist-p (x)
              (svex-p x)
              :true-listp t))

#||
(trace$
 #!vl
 (vl-operandinfo-to-svex-select
  :entry (list 'vl-operandinfo-to-svex-select
               (with-local-ps (vl-pp-expr (vl-operandinfo->orig-expr x)))
               indices
               (vl-scopestack->path ss))))

||#

(define vl-operandinfo-to-svex-select
  ((x vl-operandinfo-p)
   (indices sv::svexlist-p)
   (ss vl-scopestack-p)
   (scopes vl-elabscopes-p))



  ;; Process an index expression's operandinfo to obtain
  ;;   -- an svex expression for its longest static prefix, in terms of a variable
  ;;      representing its HID/vardecl part
  ;;   -- a variable representing the longest static prefix
  ;;   -- an svex expression for the entire expression, in terms of the longest
  ;;   static prefix var.

  ;; Why break it into these parts?  When processing assignments where the LHS
  ;; contains a dynamic array index

  ;; Note: This does NOT properly sign- or zero-extend either part.

  :prepwork (;; (local (defthm seltrace-index-count-in-terms-of-operandinfo
             ;;          (equal (vl-seltrace-index-count (vl-operandinfo->seltrace x))
             ;;                 (- (vl-operandinfo-index-count x)
             ;;                    (b* ((part (vl-operandinfo->part x)))
             ;;                      (vl-partselect-case part :none 0 :otherwise 2))))
             ;;          :hints(("Goal" :in-theory (enable vl-operandinfo-index-count)))
             ;;          :rule-classes (:rewrite :linear)))
             ;; (local (defthm len-of-cdr
             ;;          (implies (posp (len x))
             ;;                   (equal (len (cdr x))
             ;;                          (1- (len x))))))
             (local (defthmd consp-by-len
                      (implies (posp (len x))
                               (consp x))
                      :hints(("Goal" :in-theory (enable len)))))
             ;; (local (defthm len-cdr
             ;;          (implies (consp x)
             ;;                   (equal (len (cdr x))
             ;;                          (+ -1 (len x))))))
             (local (in-theory (disable len-of-cdr
                                        acl2::take-of-len-free
                                        acl2::len-when-atom
                                        acl2::take
                                        acl2::nthcdr-when-zp
                                        acl2::subsetp-when-atom-left
                                        nthcdr)))

             ;; (local (in-theory (disable acl2::nthcdr-of-cdr)))
             )
  :guard (and (vl-operandinfo-usertypes-ok x)
              (equal (len indices)
                     (vl-operandinfo-index-count x)))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-index-count
                                           consp-by-len len-of-cdr)
                 :do-not-induct t))
  :guard-debug t
  :returns (mv (err (iff (vl-msg-p err) err))
               (select-expr (implies (not err) (sv::svex-select-p select-expr)))
               (paramval    sv::maybe-4vec-p
                            "Value corresponds to the innermost nested variable of select-expr."))

  (b* (((fun (fail err)) (mv err nil nil))
       ((mv err x indices) (vl-operandinfo-to-svex-preproc x indices))
       (indices (list-fix indices))
       ((when err) (fail err))
       ((vl-operandinfo x))

       ((unless (vl-hidtrace-resolved-p x.hidtrace))
        (fail (vmsg "Unresolved hid indices")))
       ((vl-hidstep decl) (car x.hidtrace))
       (decl-scopes (vl-elabscopes-traverse (rev decl.elabpath) scopes))
       (info (vl-elabscopes-item-info x.declname decl-scopes))
       (item (or info decl.item))

       ((mv err paramval)
        (b* (((when (eq (tag item) :vl-vardecl))
              (b* (((vl-vardecl item)))
                (mv nil (and item.constp item.constval))))
             ((when (member (tag item) '(:vl-modinst
                                         :vl-interfaceport)))
              (mv nil nil))
             ((unless (eq (tag item) :vl-paramdecl))
              (mv (vmsg "Referenced name not referring to a variable, interface instance, or parameter")
                  nil))
             (paramval (b* (((vl-paramdecl item)))
                         (vl-paramtype-case item.type
                           :vl-explicitvalueparam item.type.final-value
                           :otherwise nil)))
             ((unless paramval)
              (mv (vmsg "Parameter value is not resolved") nil)))
          (mv nil paramval)))
       ((when err) (fail err))

       ;; If we have a paramval, we don't really care whether the svex variable
       ;; name correctly corresponds to the svex hierarchy, because we're going
       ;; to replace it with the paramval.  Setting strictp=nil tells this to
       ;; be lenient with one particular error we want to avoid here.
       ((mv err base-svar)
        (vl-operandinfo-base-svar x ss :strictp (not paramval)))
       ((when err) (fail err))



       (partsel-p (not (vl-partselect-case x.part :none)))
       (seltrace-indices (if partsel-p
                             (cddr indices)
                           indices))

       ((mv err seltrace-select)
        (vl-seltrace-to-svex-select x.seltrace seltrace-indices x.hidtype base-svar ss))

       ((when err) (fail err))

       ((unless partsel-p)
        (mv nil seltrace-select paramval))

       ;; From here down we have a partselect.
       ((list base-svex width-svex) indices)

       (psel-width (sv::2vec->val (sv::svex-quote->val width-svex)))
       ;; ((unless psel-width)
       ;;  (fail (vmsg "Partselect width was not resolved")))

       ((mv err psel-select)
        (vl-plusminus-partselect->svex
         seltrace-select
         (vl-seltrace-type x.seltrace x.hidtype)
         (vl-partselect->plusminus x.part)
         base-svex psel-width))

       ((when err) (fail err)))
    (mv nil psel-select paramval))
  ///

  (local (defthm svexlist-vars-of-cdr
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svexlist-vars (cdr x)))))))

  (local (defthm svex-vars-of-car
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svex-vars (car x)))))))

  ;; (local (defthm svexlist-vars-of-take
  ;;          #!sv
  ;;          (implies (not (member v (svexlist-vars x)))
  ;;                   (not (member v (svexlist-vars (take n x)))))
  ;;          :hints(("Goal" :in-theory (enable acl2::take)))))

  ;; (local (defthm svexlist-vars-of-nthcdr
  ;;          #!sv
  ;;          (implies (not (member v (svexlist-vars x)))
  ;;                   (not (member v (svexlist-vars (nthcdr n x)))))
  ;;          :hints(("Goal" :in-theory (enable nthcdr)))))

  ;; (local (defthm member-of-list-a
  ;;          (iff (member v (list a))
  ;;               (equal v a))
  ;;          :hints(("Goal" :in-theory (enable member)))))

  ;; (local (defthm svexlist-vars-of-list-fix
  ;;          #!sv (equal (svexlist-vars (list-fix x))
  ;;                      (svexlist-vars x))))

  (defret vars-of-vl-operandinfo-to-svex-select
    (implies (and (sv::svarlist-addr-p (sv::svexlist-vars indices))
                  (not err))
             (sv::svarlist-addr-p (sv::svex-select-vars select-expr)))))


(define vl-operandinfo-to-svex ((x vl-operandinfo-p)
                                (indices sv::svexlist-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :prepwork (;; (local (defthm seltrace-index-count-in-terms-of-operandinfo
             ;;          (equal (vl-seltrace-index-count (vl-operandinfo->seltrace x))
             ;;                 (- (vl-operandinfo-index-count x)
             ;;                    (b* ((part (vl-operandinfo->part x)))
             ;;                      (vl-partselect-case part :none 0 :otherwise 2))))
             ;;          :hints(("Goal" :in-theory (enable vl-operandinfo-index-count)))
             ;;          :rule-classes (:rewrite :linear)))
             ;; (local (defthm len-of-cdr
             ;;          (implies (posp (len x))
             ;;                   (equal (len (cdr x))
             ;;                          (1- (len x))))))
             (local (defthm consp-by-len
                      (implies (posp (len x))
                               (consp x))
                      :hints(("Goal" :in-theory (enable len)))))
             )
  :guard (and (vl-operandinfo-usertypes-ok x)
              (equal (len indices)
                     (vl-operandinfo-index-count x)))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-index-count)
                 :do-not-induct t))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (b* (((vl-operandinfo x))

       ((mv err size) (vl-datatype-size x.type))
       ((when err) (mv err (svex-x)))
       ((unless size)
        (mv (vmsg "Unsizable datatype ~a0" x.type) (svex-x)))
       ((mv ?caveat class) (vl-datatype-arithclass x.type))
       ((mv err select paramval)
        (vl-operandinfo-to-svex-select
         x indices ss scopes))

       ((when err) (mv err (svex-x)))

       (svex-select (sv::svex-select-to-svex select))
       (svex-ext (if (vl-integer-arithclass-p class)
                     (svex-extend (vl-integer-arithclass->exprsign class) size svex-select)
                   ;; Something like an interface, array, etc.
                   svex-select))

       ((unless paramval) (mv nil (sv::svex-reduce-consts svex-ext)))

       (param-svex (sv::svex-reduce-consts
                    (sv::svex-replace-var svex-ext (sv::svex-select-inner-var select)
                                          (sv::svex-quote paramval)))))
    (mv nil param-svex))

  ///

  (local (defthm member-svex-vars-of-car
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svex-vars (car x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cadr
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svex-vars (cadr x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cdr
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svexlist-vars (cdr x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))


  (local (in-theory (disable len consp-by-len member-equal)))

  (local (defthm svex-alist-vars-of-single
           #!sv (equal (svex-alist-vars (list (cons a b)))
                       (and (svar-p a)
                            (svex-vars b)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-vars)))))

  (local (defthm svex-alist-keys-of-single
           #!sv (equal (svex-alist-keys (list (cons a b)))
                       (and (svar-p a) (list a)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-keys)))))

  (local (defthm member-single
           (iff (member a (list b))
                (equal a b))
           :hints(("Goal" :in-theory (enable member)))))

  (defret vars-of-vl-operandinfo-to-svex
    (implies (sv::svarlist-addr-p (sv::svexlist-vars indices))
             (sv::svarlist-addr-p (sv::svex-vars svex)))
    :hints(("Goal" :in-theory (enable sv::vars-of-svex-compose-strong)))))





#|

(trace$
 #!vl
 (vl-datatype-$dimensions
  :entry (list 'vl-datatype-$dimensions
               (with-local-ps (vl-pp-datatype x)))
  :exit (list 'vl-datatype-$dimensions value)))

|#

(define vl-datatype-$dimensions ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :measure (vl-datatype-count x)
  :ruler-extenders :all
;; SystemVerilog spec says: $dimensions shall return the following:
;;   The total number of dimensions in the array (packed and unpacked, static or dynamic)
;;   1 for the string data type or any other nonarray type that is equivalent to a simple bit vector
;; type (see 6.11.1)
;;   0 for any other type

  ;; Needs testing; this is just a plausible guess
  (+ (len (vl-datatype->udims x))
     (len (vl-datatype->pdims x))
     (vl-datatype-case x
       :vl-coretype ;; is it a vector type?
       (b* (((vl-coredatatype-info info) (vl-coretypename->info x.name)))
         (if (or (eq x.name :vl-string)
                 (and info.size (not (eql info.size 1))))
             1
           0))
       :vl-struct (if x.packedp 1 0)
       :vl-union (if x.packedp 1 0)
       :vl-enum 1
       :vl-usertype (mbe :logic (if x.res
                                    (vl-datatype-$dimensions x.res)
                                  0)
                         :exec (vl-datatype-$dimensions x.res)))))

(define vl-datatype-$unpacked_dimensions ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :measure (vl-datatype-count x)
  :ruler-extenders :all

;; SystemVerilog spec says: $unpacked_dimensions shall return the following:
;;   The total number of unpacked dimensions for an array (static or dynamic)
;;   0 for any other type

  ;; Needs testing; this is just a plausible guess
  (+ (len (vl-datatype->udims x))
     (if (consp (vl-datatype->pdims x))
         0
       (vl-datatype-case x
         :vl-usertype (mbe :logic (if x.res
                                      (vl-datatype-$unpacked_dimensions x.res)
                                    0)
                           :exec (vl-datatype-$unpacked_dimensions x.res))
         :otherwise 0))))

(define vl-datatype-syscall-remove-dims ((n natp)
                                         (type vl-datatype-p))
  :guard (vl-datatype-resolved-p type)
  :returns (mv (err (iff (vl-msg-p err) err))
               (final-dim (implies (not err) (vl-dimension-p final-dim))))
  :measure (nfix n)
  (b* (((mv err ?caveat new-type dim)
        (vl-datatype-remove-dim type))
       ((when err) (mv err nil))
       ((when (zp n)) (mv nil dim)))
    (vl-datatype-syscall-remove-dims (1- n) new-type)))


(define vl-datatype-syscall-to-svex ((orig-x vl-expr-p)
                                     (fn stringp)
                                     (type vl-datatype-p)
                                     (index maybe-natp)
                                     (ss vl-scopestack-p)
                                     (scopes vl-elabscopes-p))
  :returns (mv (warnings vl-warninglist-p)
               (res sv::Svex-p))
  (b* ((warnings nil)
       (fn (string-fix fn))
       (index (maybe-natp-fix index))
       (orig-x (vl-expr-fix orig-x))
       ((when (and index (zp index)))
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Dimension argument of 0 is illegal in array query system calls: ~a0"
                   :args (list orig-x))
            (svex-x)))
       ((when (and index (member-equal fn '("$bits" "$dimensions" "$unpacked_dimensions"))))
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Dimension argument is illegal: ~a0"
                   :args (list orig-x))
            (svex-x)))

       ((mv err type)
        (vl-datatype-usertype-resolve type ss :scopes scopes))
       ((when err)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't resolve datatype in ~a0: ~@1"
                   :args (list orig-x err))
            (svex-x))))
    (cond ((equal fn "$bits")
           (b* (((mv err size) (vl-datatype-size type))
                ((when (or err (not size)))
                 (mv (fatal :type :vl-expr-to-svex-fail
                            :msg "Couldn't size datatype in ~a0: ~@1"
                            :args (list orig-x (or err "unsizable datatype")))
                     (svex-x))))
             (mv (ok) (svex-int size))))
          ((equal fn "$dimensions")
           (mv nil (svex-int (vl-datatype-$dimensions type))))
          ((equal fn "$unpacked_dimensions")
           (mv nil (svex-int (vl-datatype-$unpacked_dimensions type))))

          ((member-equal fn '("$left"
                              "$right"
                              "$increment"
                              "$low"
                              "$high"
                              "$size"))
           ;; Deals with the outermost dimension
           (b* (((mv err dim)
                 (vl-datatype-syscall-remove-dims (if index (1- index) 0) type))
                ((when (or err
                           ;; BOZO some of these might work for more exotic kinds of dimensions
                           (not (vl-dimension-case dim :range))
                           (not (vl-range-resolved-p (vl-dimension->range dim)))))
                 (mv (fatal :type :vl-expr-to-svex-fail
                            :msg "Couldn't resolve outermost dimension for ~a0: ~@1"
                            :args (list orig-x
                                        (or err "unresolved dimension")))
                     (svex-x)))
                (dim.range (vl-dimension->range dim))
                ((vl-range dim) dim.range))
             (cond ((equal fn "$left")  (mv nil (svex-int (vl-resolved->val dim.msb))))
                   ((equal fn "$right") (mv nil (svex-int (vl-resolved->val dim.lsb))))
                   ((equal fn "$increment")
                    (mv nil
                        (svex-int (if (< (vl-resolved->val dim.msb)
                                         (vl-resolved->val dim.lsb))
                                      -1
                                    1))))
                   ((equal fn "$low")
                    (mv nil
                        (svex-int (if (< (vl-resolved->val dim.msb)
                                         (vl-resolved->val dim.lsb))
                                      (vl-resolved->val dim.msb)
                                    (vl-resolved->val dim.lsb)))))
                   ((equal fn "$high")
                    (mv nil
                        (svex-int (if (< (vl-resolved->val dim.msb)
                                         (vl-resolved->val dim.lsb))
                                      (vl-resolved->val dim.lsb)
                                    (vl-resolved->val dim.msb)))))
                   (t
                    (mv nil
                        (svex-int (vl-range-size dim.range)))))))

          (t (mv (fatal :type :vl-expr-unsupported
                        :msg "Unrecognized system function: ~a0"
                        :args (list orig-x))
                 (svex-x)))))




  ///
  (defret vars-of-vl-datatype-syscall-to-svex
    (equal (sv::svex-vars res) nil)))





(define vl-function-pair-inputs-with-actuals ((inputs vl-portdecllist-p)
                                              (args sv::svexlist-p))
  :guard (equal (len inputs) (len args))
  :returns (sigma sv::svex-alist-p)
  :guard-hints (("goal" :in-theory (enable sv::name-p)))
  (if (atom inputs)
      nil
    (cons (cons #!sv
                (make-svar
                 :name (make-address
                        :path (make-path-wire
                               :name #!vl (vl-portdecl->name (car inputs)))))
                (sv::svex-fix (car args)))
          (vl-function-pair-inputs-with-actuals (cdr inputs) (cdr args))))
  ///
  (more-returns
   (sigma :name vars-of-vl-function-pair-inputs-with-actuals
          (implies (not (member v (sv::svexlist-vars args)))
                   (not (member v (sv::svex-alist-vars sigma))))
          :hints(("Goal" :in-theory (enable sv::svex-alist-vars))))))


(fty::deflist vl-datatypelist :elt-type vl-datatype)

(define vl-datatypelist-resolved-p ((x vl-datatypelist-p))
  (if (atom x)
      t
    (and (vl-datatype-resolved-p (car x))
        (vl-datatypelist-resolved-p (cdr x))))
  ///
  (defthm vl-datatypelist-resolved-p-of-repeat
    (implies (vl-datatype-resolved-p x)
             (vl-datatypelist-resolved-p (repeat n x)))
    :hints(("Goal" :in-theory (enable repeat)))))

(Define vl-datatypelist-usertype-resolve ((x vl-datatypelist-p)
                                          (ss vl-scopestack-p)
                                          (scopes vl-elabscopes-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (new-x vl-datatypelist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv err1 x1) (vl-datatype-usertype-resolve (car x) ss :scopes scopes))
       ((mv err2 x2) (vl-datatypelist-usertype-resolve (cdr x) ss scopes)))
    (mv (or err1 err2)
        (cons x1 x2)))
  ///
  (defret vl-datatypelist-resolved-p-of-vl-datatypelist-usertype-resolve
    (implies (not err)
             (vl-datatypelist-resolved-p new-x))
    :hints(("Goal" :in-theory (enable vl-datatypelist-resolved-p))))

  (defret len-of-vl-datatypelist-usertype-resolve
    (equal (len new-x) (len x))))

(defprojection vl-portdecllist->types ((x vl-portdecllist-p))
  :returns (types vl-datatypelist-p)
  (vl-portdecl->type x))

(defprojection vl-structmemberlist->types ((x vl-structmemberlist-p))
  :returns (types vl-datatypelist-p)
  (vl-structmember->type x)
  ///
  (defret vl-datatypelist-resolved-p-of-vl-structmemberlist->types
    (implies (vl-structmemberlist-resolved-p x)
             (vl-datatypelist-resolved-p types))
    :hints(("Goal" :in-theory (enable vl-datatypelist-resolved-p
                                      vl-structmemberlist-resolved-p)))))


(local (in-theory (disable nfix)))

(define vl-unaryop-to-svex ((op vl-unaryop-p)
                            (arg sv::svex-p)
                            (arg-size natp)
                            (size natp)
                            (signedness vl-exprsign-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (b* ((op (vl-unaryop-fix op))
       (body
        (case op
          (:vl-unary-plus   (sv::svcall sv::xdet arg))
          (:vl-unary-minus  (sv::svcall sv::u- arg))
          (:vl-unary-bitnot (sv::svcall sv::bitnot arg))
          (:vl-unary-lognot (sv::svcall sv::bitnot (sv::svcall sv::uor arg)))
          (:vl-unary-bitand (sv::svcall sv::uand   (sv::svex-signx arg-size arg)))
          (:vl-unary-nand   (sv::svcall sv::bitnot
                                          (sv::svcall sv::uand (sv::svex-signx arg-size arg))))
          (:vl-unary-bitor  (sv::svcall sv::uor     arg))
          (:vl-unary-nor    (sv::svcall sv::bitnot  (sv::svcall sv::uor    arg)))
          (:vl-unary-xor    (sv::svcall sv::uxor    (sv::svex-zerox arg-size arg)))
          (:vl-unary-xnor   (sv::svcall sv::bitnot
                                          (sv::svcall sv::uxor (sv::svex-zerox arg-size arg)))))))
    (mv (and (not body)
             (vmsg "Operator not implemented: ~s0" (vl-unaryop-string op)))
        (if body
            (svex-extend signedness size body)
          (svex-x))))
  ///
  (defret vars-of-vl-unaryop-to-svex
    (implies (not (member v (sv::svex-vars arg)))
             (not (member v (sv::svex-vars svex))))))

(define vl-binaryop-to-svex ((op vl-binaryop-p)
                             (left sv::svex-p)
                             (right sv::svex-p)
                             (left-size natp)
                             (right-size natp)
                             (size natp)
                             (signedness vl-exprsign-p))
  (declare (ignorable right-size))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (b* ((op (vl-binaryop-fix op))
       (body
        (case op
          (:vl-binary-plus    (sv::svcall +          left right))
          (:vl-binary-minus   (sv::svcall sv::b-     left right))
          (:vl-binary-times   (sv::svcall *          left right))
          (:vl-binary-div     (sv::svcall /          left right))
          (:vl-binary-rem     (sv::svcall sv::%      left right))
          (:vl-binary-eq      (sv::svcall sv::==     left right))
          (:vl-binary-neq     (sv::svcall sv::bitnot (sv::svcall sv::==     left right)))
          (:vl-binary-ceq     (sv::svcall sv::===    left right))
          (:vl-binary-cne     (sv::svcall sv::bitnot (sv::svcall sv::===    left right)))
          (:vl-binary-wildeq  (sv::svcall sv::==?    left right))
          (:vl-binary-wildneq (sv::svcall sv::bitnot (sv::svcall sv::==?    left right)))
          (:vl-binary-logand  (sv::svcall sv::bitand (sv::svcall sv::uor    left)
                                                     (sv::svcall sv::uor    right)))
          (:vl-binary-logor   (sv::svcall sv::bitor  (sv::svcall sv::uor    left)
                                                     (sv::svcall sv::uor    right)))
          (:vl-binary-lt      (sv::svcall sv::<      left right))
          (:vl-binary-lte     (sv::svcall sv::bitnot (sv::svcall sv::<      right left)))
          (:vl-binary-gt      (sv::svcall sv::<      right left))
          (:vl-binary-gte     (sv::svcall sv::bitnot (sv::svcall sv::<      left right)))
          (:vl-binary-bitand  (sv::svcall sv::bitand left right))
          (:vl-binary-bitor   (sv::svcall sv::bitor  left right))
          (:vl-binary-xor     (sv::svcall sv::bitxor left right))
          (:vl-binary-xnor    (sv::svcall sv::bitnot (sv::svcall sv::bitxor left right)))
          (:vl-binary-power   (sv::svcall sv::pow    left right))
          ;; Shift amounts need to be zero-extended -- right arg is always
          ;; treated as unsigned per SV spec 11.4.10.
          (:vl-binary-shr     (sv::svcall sv::rsh
                                          ;; Weird case:
                                          (sv::svex-zerox right-size right)
                                          (sv::svex-zerox left-size left)))
          (:vl-binary-shl     (sv::svcall sv::lsh
                                          (sv::svex-zerox right-size right)
                                          left))
          (:vl-binary-ashr    (sv::svcall sv::rsh
                                          (sv::svex-zerox right-size right)
                                          left))
          (:vl-binary-ashl    (sv::svcall sv::lsh
                                          (sv::svex-zerox right-size right)
                                          left))
          (:vl-implies        (sv::svcall sv::bitor
                                            (sv::svcall sv::bitnot
                                                          (sv::svcall sv::uor    left))
                                            (sv::svcall sv::uor    right)))
          (:vl-equiv          (sv::svcall sv::bitnot
                                            (sv::svcall sv::bitxor
                                                          (sv::svcall sv::uor    left)
                                                          (sv::svcall sv::uor    right))))
          (otherwise          nil))))
    (mv (and (not body)
             (vmsg "Operator not implemented: ~s0" (vl-binaryop-string op)))
        (if body
            (svex-extend signedness size body)
          (svex-x))))
  ///
  (defret vars-of-vl-binaryop-to-svex
    (implies (and (not (member v (sv::svex-vars left)))
                  (not (member v (sv::svex-vars right))))
             (not (member v (sv::svex-vars svex))))))


(define svex-concat-list-aux ((widths nat-listp "the widths of the expressions remaining in x")
                              (x sv::svexlist-p "the less-significant expressions, most-significant first")
                              (acc sv::svex-p "the final svex for the more-significant part"))
  :guard (eql (len widths) (len x))
  :guard-hints (("goal" :in-theory (enable len)))
  :returns (concat sv::svex-p)
  (if (atom x)
      (sv::svex-fix acc)
    (svex-concat-list-aux
     (cdr widths) (cdr x)
     (sv::svex-concat (car widths) (car x) acc)))
  ///
  (defthm vars-of-svex-concat-list-aux
    (implies (and (not (member v (sv::svexlist-vars x)))
                  (not (member v (sv::svex-vars acc))))
             (not (member v (sv::svex-vars (svex-concat-list-aux widths x acc)))))))

(define svex-concat-list ((widths nat-listp) (x sv::svexlist-p))
  ;; Because Verilog concats go MSB to LSB, we do this tail-recursively,
  ;; accumulating terms onto the MSBs.
  ;; x and widths are therefore both MSB-first.
  :guard (eql (len widths) (len x))
  :guard-hints (("goal" :in-theory (enable len)))
  :returns (concat sv::svex-p)
  (if (atom x)
      (svex-x) ;; no elements in the concat -- bad case
    (svex-concat-list-aux (cdr widths) (cdr x)
                          ;; This plays really nicely with the garbage convention: note
                          ;; that we don't have to fix this up at all.
                          (car x)))
  ///
  (defthm vars-of-svex-concat-list
    (implies (not (member v (sv::svexlist-vars x)))
             (not (member v (sv::svex-vars (svex-concat-list widths x)))))))


(define svex-repeat-aux ((n natp)
                         (width natp)
                         (x sv::svex-p)
                         (acc sv::svex-p))
  :returns (concat sv::svex-p)
  (if (zp n)
      (sv::svex-fix acc)
    (svex-repeat-aux (1- n) width x (sv::svex-concat (lnfix width) x acc)))
  ///
  (defret vars-of-svex-repeat-aux
    (implies (and (not (member v (sv::svex-vars x)))
                  (not (member v (sv::svex-vars acc))))
             (not (member v (sv::svex-vars concat))))))

(define svex-repeat ((n natp) (width natp) (x sv::svex-p))
  :returns (concat sv::svex-p)
  (if (zp n)
      (svex-x)
    (svex-repeat-aux (1- n) width x x))
  ///
  (defret vars-of-svex-repeat
    (implies (not (member v (sv::svex-vars x)))
             (not (member v (sv::svex-vars concat))))))

(define svex-multiconcat ((n natp) (x sv::svexlist-p) (widths nat-listp))
  :guard (eql (len x) (len widths))
  :returns (concat sv::svex-p)
  (svex-repeat n (sum-nats widths) (svex-concat-list widths x))
  ///
  (defret vars-of-svex-multiconcat
    (implies (not (member v (sv::svexlist-vars x)))
             (not (member v (sv::svex-vars concat))))))






(define vl-value-in-range ((x vl-expr-p)
                           (range vl-range-p))
  :guard (and (vl-expr-resolved-p x)
              (vl-range-resolved-p range))
  (b* (((vl-range range))
       (msb (vl-resolved->val range.msb))
       (lsb (vl-resolved->val range.lsb))
       (x (vl-resolved->val x)))
    (or (and (<= msb x) (<= x lsb))
        (and (<= lsb x) (<= x msb)))))


;; BOZO maybe should also check for more than 1 default key?
(define vl-check-array-assignpat-keys ((pairs vl-keyvallist-p)
                                       (range vl-range-p))
  :guard (vl-range-resolved-p range)
  :returns (err (iff (vl-msg-p err) err))
  :measure (vl-keyvallist-count pairs)
  (b* ((pairs (vl-keyvallist-fix pairs))
       ((when (atom pairs)) nil)
       (key (caar pairs))
       (err (vl-patternkey-case key
              :expr (if (vl-expr-resolved-p key.key)
                        (if (vl-value-in-range key.key range)
                            nil
                          (vmsg "Key ~a0 not in valid range" key.key))
                      (vmsg "Key ~a0 not resolved" key.key))
              :structmem (vmsg "Struct member name key ~a0 not valid for array patterns." key.name)
              :type (vmsg "Datatype key ~a0 not valid for array patterns" key.type)
              :default nil)))
    (or err
        (vl-check-array-assignpat-keys (cdr pairs) range))))

(fty::defalist vl-svex-keyvallist :key-type vl-patternkey :val-type sv::svex-p
  ///
  (defthm vl-svex-keyvallist-p-of-pairlis
    (implies (and (vl-keyvallist-p x)
                  (sv::svexlist-p vals)
                  (equal (len x) (len vals)))
             (vl-svex-keyvallist-p (pairlis$ (alist-keys x) vals)))
    :hints(("Goal" :in-theory (enable alist-keys vl-keyvallist-p pairlis$)
            :induct (pairlis$ x vals)))))

(define vl-svex-keyvallist-vars ((x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  (b* ((x (vl-svex-keyvallist-fix x)))
    (if (atom x)
        nil
      (append (sv::svex-vars (cdar x))
              (vl-svex-keyvallist-vars (cdr x)))))
  ///
  (defthm vl-svex-keyvallist-vars-of-pairlis$
    (implies (and (not (member v (sv::svexlist-vars vals)))
                  (equal (len keys) (len vals)))
             (not (member v (vl-svex-keyvallist-vars (pairlis$ keys vals)))))
    :hints(("Goal" :in-theory (enable pairlis$)))))

(define vl-svex-keyval-default-lookup ((x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  :returns (ans (implies ans (sv::svex-p ans)))
  (b* ((x (vl-svex-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key :default)) (cdar x)))
    (vl-svex-keyval-default-lookup (cdr x)))
  ///
  (defret vars-of-vl-svex-keyval-default-lookup
    (implies (and ans
                  (not (member v (vl-svex-keyvallist-vars x))))
             (not (member v (sv::svex-vars ans))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))


(define vl-svex-keyval-index-lookup ((n integerp)
                                     (x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  :returns (ans (implies ans (sv::svex-p ans)))
  (b* ((x (vl-svex-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key
                :expr (and (vl-expr-resolved-p key.key)
                           (eql (vl-resolved->val key.key)
                                (lifix n)))
                :otherwise nil))
        (cdar x)))
    (vl-svex-keyval-index-lookup n (cdr x)))
  ///
  (defret vars-of-vl-svex-keyval-index-lookup
    (implies (and ans
                  (not (member v (vl-svex-keyvallist-vars x))))
             (not (member v (sv::svex-vars ans))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))

(define vl-array-assignpat-keyval-resolve ((lsb integerp)
                                           (msb integerp)
                                           (x vl-svex-keyvallist-p))
  :measure (abs (- (ifix lsb) (ifix msb)))
  ;; BOZO only returning one of the errors...
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex-membs sv::svexlist-p
                           "Most-significant first"))
  :verify-guards nil
  :prepwork ((local (in-theory (enable acl2::arith-equiv-forwarding))))
  (b* ((first (or (vl-svex-keyval-index-lookup msb x)
                  (vl-svex-keyval-default-lookup x)))
       (err1 (and (not first)
                  (vmsg "No assignment pattern entry for array index ~x0"
                        (lifix msb))))
       ((when (eql (lifix lsb) (lifix msb)))
        ;; Last one
        (mv err1
            (list (or first (svex-x)))))
       (next (if (< (lifix lsb) (lifix msb))
                 (- (lifix msb) 1)
               (+ (lifix msb) 1)))
       ((mv err rest)
        (vl-array-assignpat-keyval-resolve lsb next x)))
    (mv (or err1 err)
        (cons (or first (svex-x)) rest)))
  ///
  (defret len-of-vl-array-assignpat-keyval-resolve
    (equal (len svex-membs)
           (+ 1 (abs (- (ifix msb) (ifix lsb))))))
  (defthm len-of-vl-array-assignpat-keyval-resolve-range
    (implies (vl-range-resolved-p range)
             (b* (((vl-range range)))
               (equal (len (mv-nth 1 (vl-array-assignpat-keyval-resolve
                                      (vl-resolved->val range.lsb)
                                      (vl-resolved->val range.msb)
                                      x)))
                      (vl-range-size range))))
    :hints(("Goal" :in-theory (enable vl-range-size))))
  (verify-guards vl-array-assignpat-keyval-resolve)

  (defret vars-of-vl-array-assignpat-keyval-resolve
    (implies (and ans
                  (not (member v (vl-svex-keyvallist-vars x))))
             (not (member v (sv::svexlist-vars svex-membs))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))


;; (define vl-simple-idexpr-name ((x vl-expr-p))
;;   :returns (name (iff (stringp name) name))
;;   (vl-expr-case x
;;     :vl-index (and (vl-partselect-case x.part :none)
;;                    (atom x.indices)
;;                    (vl-simple-id-name x.scope))
;;     :otherwise nil))

(define vl-check-struct-assignpat-keys ((pairs vl-keyvallist-p)
                                        (membs vl-structmemberlist-p))
  :returns (err (iff (vl-msg-p err) err))
  :measure (vl-keyvallist-count pairs)
  (b* ((pairs (vl-keyvallist-fix pairs))
       ((when (atom pairs)) nil)
       (key (caar pairs))
       (err (vl-patternkey-case key
              ;; We used to leave these as expressions, but now they should be
              ;; structmem fields, so we shouldn't see any complex expressions
              ;; being mixed in.
              ;; :expr (b* ((name (vl-simple-idexpr-name key.key))
              ;;            ((unless name)
              ;;             (vmsg "Bad expression for struct assignment pattern key: ~a0" key.key))
              ;;            ((unless (vl-find-structmember name membs))
              ;;             (vmsg "Not a field name: ~a0" key.key)))
              ;;         nil)
              :expr
              (vmsg "Array indexing key ~a0 not valid for struct patterns" key.key)
              :structmem
              (if (vl-find-structmember key.name membs)
                  nil
                (vmsg "Not a field name: ~a0" key.name))
              :type
              ;; BOZO could support these someday
              (vmsg "Datatype key ~a0 not valid for struct patterns" key.type)
              :default nil)))
    (or err
        (vl-check-struct-assignpat-keys (cdr pairs) membs))))

(define vl-keyval-default-lookup ((x vl-keyvallist-p))
  :measure (len (vl-keyvallist-fix x))
  :returns (ans (implies ans (vl-expr-p ans)))
  (b* ((x (vl-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key :default)) (cdar x)))
    (vl-keyval-default-lookup (cdr x)))
  ///
  (defret vl-expr-count-of-vl-keyval-default-lookup
    (implies ans
             (< (vl-expr-count ans)
                (vl-keyvallist-count x)))
    :rule-classes :linear))


(define vl-keyval-member-lookup ((name stringp)
                                 (x vl-keyvallist-p))
  :measure (len (vl-keyvallist-fix x))
  :returns (ans (implies ans (vl-expr-p ans)))
  (b* ((x (vl-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key
                ;; From back when things were expressions:
                ;; :expr (equal (vl-simple-idexpr-name key.key)
                ;;              (string-fix name))
                :structmem (equal key.name (string-fix name))
                :otherwise nil))
        (cdar x)))
    (vl-keyval-member-lookup name (cdr x)))
  ///
  (defret vl-expr-count-of-vl-keyval-member-lookup
    (implies ans
             (< (vl-expr-count ans)
                (vl-keyvallist-count x)))
    :rule-classes :linear))



(local (defthm vl-exprlist-count-of-assignpat-keyval-values
         ;; (implies (vl-keyvallist-p x)
                  (<= (vl-exprlist-count (alist-vals x))
                      (vl-keyvallist-count x))
         :hints(("Goal" :in-theory (enable vl-exprlist-count
                                           vl-keyvallist-count
                                           alist-vals)))
         :rule-classes :linear))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (atom x))))

(local (defthm vl-expr-opacity-type-forward
         (vl-opacity-p (vl-expr-opacity x))
         :rule-classes
         ((:forward-chaining :trigger-terms ((vl-expr-opacity x))))))

(local (defthm nat-listp-when-maybe-nat-list-p
         (implies (and (maybe-nat-list-p x)
                       (not (member nil x)))
                  (nat-listp x))
         :hints(("Goal" :in-theory (enable member)))))

(local (defthm vl-exprlist-p-alist-vals-of-keyvallist
         (implies (vl-keyvallist-p x)
                  (vl-exprlist-p (alist-vals x)))
         :hints(("Goal" :in-theory (enable vl-keyvallist-p alist-vals)))))

(local (defthm len-alist-keys-of-keyvallist
         (implies (vl-keyvallist-p x)
                  (equal (len (alist-keys x)) (len x)))
         :hints(("Goal" :in-theory (enable alist-keys vl-keyvallist-p)))))





;; (defines vl-expr-paramref-measure
;;   :prepwork ((local (defthm natp-max
;;                       (implies (and (natp a) (natp b))
;;                                (natp (max a b)))
;;                       :rule-classes :type-prescription))
;;              (local (in-theory (disable max))))
;;   :ruler-extenders :all
;;   (define vl-expr-paramref-measure ((x vl-expr-p)
;;                                     (ss vl-scopestack-p)
;;                                     &key ((rec-limit natp) '1000))
;;     :short "Measure of the recursion depth necessary to recursively process an
;;             expression plus the expressions assigned to all of the parameters it
;;             uses.  Nil if there is a dependency loop."
;;     :returns (rec-depth maybe-natp :rule-classes :type-prescription)
;;     :measure (two-nats-measure rec-limit (vl-expr-count x))
;;     (b* ((sub-depth (vl-exprlist-paramref-measure
;;                      (vl-expr->subexprs x) ss :rec-limit rec-limit))
;;          ((unless sub-depth) nil)
;;          (self-depth
;;           (vl-expr-case x
;;             :vl-index (b* (((mv err opinfo) (vl-index-expr-typetrace x ss))
;;                            ((when err) 0)
;;                            ((vl-operandinfo opinfo))
;;                            ((vl-hidstep decl) (car opinfo.hidtrace))
;;                            ((unless (eq (tag decl.item) :vl-paramdecl))
;;                             0)
;;                            ((vl-paramdecl decl.item))
;;                            ((when (zp rec-limit)) nil))
;;                         (vl-paramtype-case decl.item.type
;;                           :vl-explicitvalueparam
;;                           (b* ((meas (vl-expr-paramref-measure decl.item.type.default
;;                                                                decl.ss
;;                                                                :rec-limit (1- (lnfix rec-limit)))))
;;                             (and meas (+ 1 meas)))
;;                           :otherwise 0))
;;             :otherwise 0))
;;          ((unless self-depth) nil))
;;       (max self-depth sub-depth)))

;;   (define vl-exprlist-paramref-measure ((x vl-exprlist-p)
;;                                         (ss vl-scopestack-p)
;;                                         &key ((rec-limit natp) '1000))
;;     :returns (rec-depth maybe-natp :rule-classes :type-prescription)
;;     :measure (two-nats-measure rec-limit (vl-exprlist-count x))
;;     (b* (((when (atom x)) 0)
;;          (depth1 (vl-expr-paramref-measure (car x) ss :rec-limit rec-limit))
;;          ((unless depth1) nil)
;;          (depth2 (vl-exprlist-paramref-measure (cdr x) ss :rec-limit rec-limit))
;;          ((unless depth2) nil))
;;       (max depth1 depth2)))
;;   ///
;;   (deffixequiv-mutual vl-expr-paramref-measure)

;;   (local (defthm vl-expr-paramref-measure-of-member-exists
;;            (implies (and (vl-exprlist-paramref-measure x ss :rec-limit rec-limit)
;;                          ;; (vl-expr-paramref-measure y ss :rec-limit rec-limit)
;;                          (member y x))
;;                     (vl-expr-paramref-measure y ss :rec-limit rec-limit))
;;            :hints (("goal" :induct (member y x)
;;                     :in-theory (enable (:i member)))
;;                    (and stable-under-simplificationp
;;                         '(:expand ((vl-exprlist-paramref-measure x ss :rec-limit rec-limit)
;;                                    (member-equal y x)))))))

;;   (local (defthm vl-expr-paramref-measure-of-member-bound
;;            (implies (and (vl-exprlist-paramref-measure x ss :rec-limit rec-limit)
;;                          ;; (vl-expr-paramref-measure y ss :rec-limit rec-limit)
;;                          (member y x))
;;                     (<= (vl-expr-paramref-measure y ss :rec-limit rec-limit)
;;                         (vl-exprlist-paramref-measure x ss :rec-limit rec-limit)))
;;            :hints (("goal" :induct (member y x)
;;                     :in-theory (enable (:i member)))
;;                    (and stable-under-simplificationp
;;                         '(:expand ((vl-exprlist-paramref-measure x ss :rec-limit rec-limit)
;;                                    (member-equal y x))))
;;                    (and stable-under-simplificationp
;;                         '(:in-theory (enable max))))
;;            :rule-classes :linear))


;;   (defthm vl-expr-paramref-measure-of-member-subexprs-exists
;;     (implies (and (member y (vl-expr->subexprs x))
;;                   (vl-expr-paramref-measure x ss :rec-limit rec-limit))
;;              (vl-expr-paramref-measure y ss :rec-limit rec-limit))
;;     :hints (("Goal" :expand ((vl-expr-paramref-measure x ss :rec-limit rec-limit)))))

;;   (defthm vl-expr-paramref-measure-of-member-subexprs-bound
;;     (implies (and (member y (vl-expr->subexprs x))
;;                   (vl-expr-paramref-measure x ss :rec-limit rec-limit))
;;              (<= (vl-expr-paramref-measure y ss :rec-limit rec-limit)
;;                  (vl-expr-paramref-measure x ss :rec-limit rec-limit)))
;;     :hints (("Goal" :expand ((vl-expr-paramref-measure x ss :rec-limit rec-limit))
;;              :in-theory (enable max)))
;;     :rule-classes (:rewrite :linear)))




;; (define vl-funname->svex-funname ((x vl-scopeexpr-p)
;;                                   (ss vl-scopestack-p))
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (var (implies (not err) (sv::svar-p var)))
;;                (hidtrace vl-hidtrace-p))
;;   (b* (((mv err trace context ?tail)
;;         (vl-follow-scopeexpr x ss))
;;        ((when err) (mv err nil trace))
;;        ((unless (vl-hidtrace-resolved-p trace))
;;         (mv (vmsg "Function ~a0 has unresolved indices??"
;;                   :args (list (vl-scopeexpr-fix x)))
;;             nil trace))
;;        (path (vl-hidtrace-to-path trace nil))
;;        ((mv ?err addr) (vl-scopecontext-to-addr context ss path))
;;        ;; Ignore the error here because we really just want to generate a fully
;;        ;; scoped name for the function.
;;        (fnname (sv::make-svar :name addr)))
;;     (mv nil fnname trace))
;;   ///
;;   (defret consp-of-vl-funname->svex-funname.hidtrace
;;     (implies (not err)
;;              (consp hidtrace))
;;     :rule-classes :type-prescription))

(define vl-funname-lookup ((x vl-scopeexpr-p)
                           (ss vl-scopestack-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (decl (implies (not err) (vl-fundecl-p decl)))
               (decl-ss (implies (not err) (vl-scopestack-p decl-ss)))
               (elabpath vl-elabtraversal-p))
  (b* (((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x ss))
       ((when err) (mv err nil nil nil))
       ((unless (vl-hidtrace-resolved-p trace))
        (mv (vmsg "Function ~a0 has unresolved indices??"
                  :args (list (vl-scopeexpr-fix x)))
            nil nil nil))
       ((vl-hidstep lookup) (car trace))
       ((unless (eq (tag lookup.item) :vl-fundecl))
        (mv (vmsg "Function name ~a0 does not refer to a fundecl but instead ~
                   ~a1"
                   :args (list (vl-scopeexpr-fix x) lookup.item))
            nil nil nil)))
    (mv nil lookup.item lookup.ss lookup.elabpath)))


(define vl-streamexprlist-has-with ((x vl-streamexprlist-p))
  (if (atom x)
      nil
    (or (b* (((vl-streamexpr x1) (car x)))
          (not (vl-arrayrange-case x1.part :none)))
        (vl-streamexprlist-has-with (cdr x)))))

(define vl-streamexprlist->exprs ((x vl-streamexprlist-p))
  (if (atom x)
      nil
    (cons (vl-streamexpr->expr (car x))
          (vl-streamexprlist->exprs (cdr x)))))


(define vl-slicesize-resolve ((x vl-slicesize-p)
                              (ss vl-scopestack-p)
                              (scopes vl-elabscopes-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (size (implies (not err) (posp size)) :rule-classes :type-prescription))
  (b* ((x (vl-slicesize-fix x)))
    (vl-slicesize-case x
      :none (mv nil 1)
      :expr (b* (((unless (vl-expr-resolved-p x.expr))
                  (mv (vmsg "Slice size is unresolved expression") nil))
                 (val (vl-resolved->val x.expr))
                 ((unless (posp val))
                  (mv (vmsg "Slice size must be positive") nil)))
              (mv nil val))
      :type (b* (((mv err type) (vl-datatype-usertype-resolve x.type ss :scopes scopes))
                 ((when err) (mv err nil))
                 ((mv err size) (vl-datatype-size type))
                 ((when err) (mv err nil))
                 ((unless (posp size))
                  (mv (vmsg "Slice size must be nonzero") nil)))
              (mv nil size)))))

(define vl-size-to-unsigned-logic ((x posp))
  :returns (type vl-datatype-p)
  (hons-copy (make-vl-coretype :name :vl-logic
                               :pdims (list (vl-range->dimension
                                             (make-vl-range
                                              :msb (vl-make-index (1- (pos-fix x)))
                                              :lsb (vl-make-index 0))))))
  ///
  (defret vl-size-to-unsigned-logic-type-ok
    (vl-datatype-resolved-p type)))


(define vl-arrayrange->rel-lsb-and-width ((x vl-arrayrange-p)
                                          (dim-lsb natp)
                                          (dim-msb natp))
  :returns (mv (err (iff (vl-msg-p err) err))
               (rel-lsb (implies (not err) (natp rel-lsb)) :rule-classes :type-prescription)
               (width (implies (not err) (posp width)) :rule-classes :type-prescription))
  :guard (not (vl-arrayrange-case x :none))
  (b* ((dim-lsb (lnfix dim-lsb))
       (dim-msb (lnfix dim-msb)))
    (vl-arrayrange-case x
      :range (b* (((unless (and (vl-expr-resolved-p x.lsb)
                                (vl-expr-resolved-p x.msb)))
                   (mv "Array range not resolved" nil nil))
                  (sel-lsb (vl-resolved->val x.lsb))
                  (sel-msb (vl-resolved->val x.msb))
                  ((when (or (and (< sel-lsb sel-msb)
                                  (< dim-msb dim-lsb))
                             (and (> sel-lsb sel-msb)
                                  (> dim-msb dim-lsb))))
                   (mv "Reversed array range" nil nil))
                  ((unless (or (and (<= dim-lsb sel-lsb)
                                    (<= sel-msb dim-msb))
                               (and (>= dim-lsb sel-lsb)
                                    (>= sel-msb dim-msb))))
                   (mv "Range indices out of bounds" nil nil))
                  (rel-lsb (abs (- sel-lsb dim-lsb)))
                  (width   (+ 1 (abs (- sel-msb sel-lsb)))))
               (mv nil rel-lsb width))
      :index (b* (((unless (vl-expr-resolved-p x.expr))
                   (mv "Array index not resolved" nil nil))
                  (sel (vl-resolved->val x.expr))
                  ((unless (or (and (<= dim-lsb sel)
                                    (<= sel dim-msb))
                               (and (>= dim-lsb sel)
                                    (>= sel dim-msb))))
                   (mv "Range index out of bounds" nil nil))
                  (rel-lsb (abs (- sel dim-lsb)))
                  (width   1))
               (mv nil rel-lsb width))
      :plusminus (b* (((unless (and (vl-expr-resolved-p x.width)
                                    (vl-expr-resolved-p x.base)))
                       (mv "Array range not resolved" nil nil))
                      (sel-base (vl-resolved->val x.base))
                      (sel-width (vl-resolved->val x.width))
                      ((unless (> sel-width 0))
                       (mv "Range width zero" nil nil))
                      (sel-end  (if x.minusp
                                    (- sel-base (- sel-width 1))
                                  (+ sel-base (- sel-width 1))))
                      ((unless (if (< dim-lsb dim-msb)
                                   (and (<= dim-lsb sel-base)
                                        (<= dim-lsb sel-end)
                                        (<= sel-base dim-msb)
                                        (<= sel-end  dim-msb))
                                 (and (<= dim-msb sel-base)
                                      (<= dim-msb sel-end)
                                      (<= sel-base dim-lsb)
                                      (<= sel-end  dim-lsb))))
                       (mv "Range indices out of bounds" nil nil))
                      (rel-lsb (min (abs (- sel-base dim-lsb))
                                    (abs (- sel-end dim-lsb)))))
                   (mv nil rel-lsb sel-width))
      :otherwise (prog2$ (impossible)
                         (mv "impossible" nil nil)))))


(local (defthm vl-expr-count-helper-for-inside
         (implies (equal (vl-expr-kind x) :vl-inside)
                  (< (+ (VL-EXPR-COUNT (VL-INSIDE->ELEM X))
                        (VL-VALUERANGELIST-COUNT (VL-INSIDE->SET X)))
                     (VL-EXPR-COUNT X)))
         :rule-classes :linear
         :hints(("Goal" :expand ((vl-expr-count x))))))

;; (define vl-datatype-compatibility-warning ((a vl-datatype-p)
;;                                            (b vl-datatype-p)
;;                                            (x vl-expr-p)
;;                                            (compattype vl-typecompat-p)
;;                                            (warnings vl-warninglist-p))
;;   :guard (and (vl-datatype-resolved-p a)
;;               (vl-datatype-resolved-p b))
;;   :returns (new-warnings vl-warninglist-p)
;;   (b* ((errmsg (vl-check-datatype-compatibility a b compattype)))
;;     (if errmsg
;;         (fatal :type :vl-expr-to-svex-fail
;;                :msg "~a0 doesn't have the required type. ~@1"
;;                :args (list (vl-expr-fix x) errmsg))
;;       (ok))))


(define vl-datatype-size-warn ((type vl-datatype-p)
                               (x vl-expr-p)
                               (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (size maybe-natp :rule-classes :type-prescription))
  :guard (vl-datatype-resolved-p type)
  (b* ((type (vl-datatype-fix type))
       (x (vl-expr-fix x))
       ((mv err size) (vl-datatype-size type))
       ((when (or err (not size)))
        (mv (warn :type :vl-expr-to-svex-fail
                  :msg "Couldn't size datatype ~a0 for expression ~a1: ~@2"
                  :args (list type x (or err "unsizeable")))
            nil)))
    (mv (ok) size)))

(define vl-convert-dollarsign-to-expr ((x vl-expr-p) (dollar-expr vl-expr-p))
  :returns (new-x vl-expr-p)
  (b* ((x (vl-expr-fix x))
       (dollar-expr (vl-expr-fix dollar-expr)))
    (vl-expr-case x
      :vl-special (if (vl-specialkey-equiv x.key :vl-$)
                      dollar-expr
                    x)
      :otherwise x))
  ///
  (defret vl-expr-count-of-convert-dollarsign-to-expr
    (< (vl-expr-count new-x) (+ (vl-expr-count dollar-expr)
                                (vl-expr-count x)))
    :rule-classes :linear))

(define vl-err->fatal ((err (implies err (vl-msg-p err)))
                       &key
                       (type symbolp)
                       (msg stringp)
                       (args true-listp)
                       ((fn symbolp) '__function__)
                       ((acc vl-warninglist-p) 'warnings))
  :returns (warnings vl-warninglist-p)
  (b* ((warnings acc)
       (msg (string-fix msg))
       (args (mbe :logic (list-fix args) :exec args)))
    (if err
        (fatal :type type :msg "~@0: ~@1"
               :args (list (make-vl-msg :msg msg
                                        :args args)
                           err)
               :fn fn)
      (ok))))

(define vl-streaming-concat-trunc/extend ((bitstream sv::svex-p)
                                          (target-size natp)
                                          (concat-size natp))
  :returns (ans sv::svex-p)
  (b* ((target-size (lnfix target-size))
       (concat-size (lnfix concat-size)))
    (cond ((> target-size concat-size)
           (sv::svcall sv::concat
                       (svex-int (- target-size concat-size))
                       (svex-int 0)
                       bitstream))
          ((< target-size concat-size)
           ;; This is an error, but NCV still runs it.
           (sv::svex-rsh (- concat-size target-size) bitstream))
          (t (sv::svex-fix bitstream))))
  ///
  (defret vars-of-vl-streaming-concat-trunc/extend
    (implies (not (member v (sv::svex-vars bitstream)))
             (not (member v (sv::svex-vars ans))))))

(define vl-trunc/extend-type-err ((lhs-size natp)
                                  (rhs-selfsize natp))
  :returns (err vl-maybe-type-error-p)
  (and (not (equal (lnfix lhs-size)
                   (lnfix rhs-selfsize)))
       (make-vl-type-error-trunc/extend :lhs-size lhs-size :rhs-selfsize rhs-selfsize)))

(define vl-funcall-args-to-ordered ((ports vl-portdecllist-p "port declarations of the function")
                                    (plainargs vl-maybe-exprlist-p "initial plainargs")
                                    (namedargs vl-call-namedargs-p "named args"))
  :prepwork ((local (defthm alistp-of-namedargs
                      (implies (vl-call-namedargs-p x) (alistp x))
                      :hints(("Goal" :in-theory (enable alistp)))))
             (local (defthm vl-expr-p-of-lookup-in-namedargs
                      (implies (and (vl-call-namedargs-p x)
                                    (cdr (assoc key x)))
                               (vl-expr-p (cdr (assoc key x))))
                      :hints(("Goal" :in-theory (enable assoc))))))
  :returns (mv (err (iff (vl-msg-p err) err))
               (args vl-exprlist-p))
  (b* (((when (atom ports)) (mv nil nil))
       ((vl-portdecl port) (car ports))
       (arg (if (consp plainargs)
                (car plainargs)
              (cdr (assoc-equal port.name (vl-call-namedargs-fix namedargs)))))
       ((unless arg)
        (mv (vmsg "Blank or no argument for port ~a0" port.name) nil))
       ((mv err rest) (vl-funcall-args-to-ordered (cdr ports) (cdr plainargs) namedargs)))
    (mv err
        (and (not err)
             (cons (vl-expr-fix arg) rest))))
  ///
  (std::defret len-of-args-when-no-error
    (implies (not err)
             (equal (len args) (len ports))))

  (local (include-book "centaur/misc/remove-assoc" :dir :system))

  (local (defthm namedargs-count-of-remove-assoc-weak
           (implies (vl-call-namedargs-p x)
                    (<= (vl-call-namedargs-count (acl2::remove-assoc key x))
                        (vl-call-namedargs-count x)))
           :hints(("Goal" :in-theory (enable assoc acl2::remove-assoc-equal
                                             vl-call-namedargs-count
                                             vl-call-namedargs-p
                                             vl-call-namedargs-fix
                                             vl-maybe-expr-some->val)
                   :induct t
                   :expand ((vl-call-namedargs-count x)
                            (:free (x) (vl-maybe-expr-count x))
                            (:free (a b) (vl-call-namedargs-count (cons a b))))))
           :rule-classes :linear))

  (local (defthm namedargs-count-of-remove-assoc
           (implies (and (vl-call-namedargs-p x)
                         (assoc key x)
                         (cdr (assoc key x)))
                    (< (vl-call-namedargs-count (acl2::remove-assoc key x))
                        (- (vl-call-namedargs-count x)
                           (vl-expr-count (cdr (assoc key x))))))
           :hints(("Goal" :in-theory (enable assoc acl2::remove-assoc-equal
                                             vl-call-namedargs-count
                                             vl-call-namedargs-p
                                             vl-call-namedargs-fix
                                             vl-maybe-expr-some->val)
                   :induct t
                   :expand ((vl-call-namedargs-count x)
                            (:free (x) (vl-maybe-expr-count x))
                            (:free (a b) (vl-call-namedargs-count (cons a b))))))
           :rule-classes :linear))

  (local (defun args-to-ordered-alt (ports namedargs)
           (b* (((when (atom ports)) (mv nil nil))
                ((vl-portdecl port) (car ports))
                (arg (cdr (assoc-equal port.name (vl-call-namedargs-fix namedargs))))
                (namedargs (acl2::remove-assoc-equal port.name (vl-call-namedargs-fix namedargs)))
                ((unless arg)
                 (mv (vmsg "Blank or no argument for port ~a0" port.name) nil))
                ((mv err rest) (args-to-ordered-alt (cdr ports) namedargs)))
             (mv err
                 (and (not err)
                      (cons (vl-expr-fix arg) rest))))))

  (local (defthm funcall-args-to-ordered-of-remove-assoc-when-not-member
           (implies (not (member key (vl-portdecllist->names ports)))
                    (equal (vl-funcall-args-to-ordered
                            ports plainargs (acl2::remove-assoc key (vl-call-namedargs-fix namedargs)))
                           (vl-funcall-args-to-ordered ports plainargs namedargs)))
           :hints(("Goal" :in-theory (enable vl-portdecllist->names member)))))

  (local (defthm funcall-args-to-ordered-when-atom-plainargs
           (implies (and (syntaxp (not (equal plainargs ''nil)))
                         (atom plainargs))
                    (equal (vl-funcall-args-to-ordered ports plainargs namedargs)
                           (vl-funcall-args-to-ordered ports nil namedargs)))
           :hints(("Goal" :in-theory (enable vl-funcall-args-to-ordered)))))


  (local (defthm funcall-args-to-ordered-is-args-to-ordered-alt
           (implies (and (no-duplicatesp (vl-portdecllist->names ports)))
                    (equal (vl-funcall-args-to-ordered ports nil namedargs)
                           (args-to-ordered-alt ports namedargs)))
           :hints(("Goal" :in-theory (enable vl-portdecllist->names)
                   :induct (args-to-ordered-alt ports namedargs)))))

  (local (defthm count-of-args-to-ordered
           (b* (((mv err args) (args-to-ordered-alt ports namedargs)))
             (implies (and (no-duplicatesp (vl-portdecllist->names ports))
                           (not err))
                      (<= (vl-exprlist-count args)
                          (vl-call-namedargs-count namedargs))))
           :hints(("Goal" :in-theory (enable vl-exprlist-count)))
           :rule-classes :linear))


  (std::defret count-of-vl-funcall-args-to-ordered
    (implies (and (no-duplicatesp (vl-portdecllist->names ports))
                  (not err))
             (<= (vl-exprlist-count args)
                 (+ (vl-maybe-exprlist-count plainargs)
                    (vl-call-namedargs-count namedargs))))
    :hints(("Goal" :in-theory (e/d (vl-maybe-exprlist-count vl-exprlist-count
                                                            vl-portdecllist->names)
                                   ((:d vl-funcall-args-to-ordered)))
            :induct t)
           (and stable-under-simplificationp
                (or (member-equal '(not (consp plainargs)) clause)
                    (member-equal '(consp ports) clause))
                '(:expand ((vl-funcall-args-to-ordered ports plainargs namedargs)))))
    :rule-classes :linear)

  (defthm count-of-vl-funcall-args-to-ordered-rw
    (b* (((vl-call x))
         ((mv err args) (vl-funcall-args-to-ordered ports x.plainargs x.namedargs)))
      (implies (and (no-duplicatesp (vl-portdecllist->names ports))
                    (not err)
                    (equal (vl-expr-kind x) :vl-call))
               (< (vl-exprlist-count args)
                  (vl-expr-count x))))
    :hints(("Goal" :in-theory (e/d () (vl-funcall-args-to-ordered))
            :expand ((vl-expr-count x))))
    :rule-classes (:rewrite :linear)))

(local (in-theory (disable acl2::hons-dups-p)))


(define vl-$test$plusargs-p ((arg      stringp)
                             (plusargs string-listp "Plusses removed"))
  ;; See SystemVerilog-2012 21.6.  Search for a particular plusarg among the
  ;; given plusargs.  The search is by string prefix.
  (cond ((atom plusargs)
         nil)
        ((str::strprefixp arg (car plusargs))
         t)
        (t
         (vl-$test$plusargs-p arg (cdr plusargs)))))


(define vl-value-to-string-aux ((value natp)
                                (acc character-listp))
  :returns (acc character-listp)
  (if (zp value)
      (character-list-fix acc)
    (vl-value-to-string-aux (ash (lnfix value) -8)
                            (cons (code-char (logand value #xFF))
                                  acc)))
  :prepwork
  ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
   (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
   (local (in-theory (enable acl2-count)))
   (local (defthm l0
            (implies (posp x)
                     (< (acl2::logcdr x) x))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable acl2::logcdr)))))
   (local (defthm l1
            (implies (and (posp x)
                          (posp n))
                     (< (acl2::logtail n x) x))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              )))))
   (local (defthm l2
            (implies (posp n)
                     (< (acl2::loghead n x) (ash 1 n)))
            :rule-classes :linear
            :hints(("Goal" :in-theory (enable bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              )))))))

(define vl-integer-to-string ((val vl-value-p))
  :guard (vl-value-case val :vl-constint)
  ;; Interpret an integer value as a string of ascii characters
  (str::implode (vl-value-to-string-aux (vl-constint->value val) nil))
  ///
  (assert!
   (b* ((str "Hello")
        (int (+ (ash (char-code #\H) (* 4 8))
                (ash (char-code #\e) (* 3 8))
                (ash (char-code #\l) (* 2 8))
                (ash (char-code #\l) (* 1 8))
                (ash (char-code #\o) (* 0 8))))
        (interp (vl-integer-to-string
                 (vl-literal->val (vl-make-index int)))))
     (equal str interp))))

(define vl-$test$plusargs-to-svex ((expr vl-expr-p)
                                   (design vl-design-p))
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (sv::svex-p svex)
                          (sv::svarlist-addr-p (sv::svex-vars svex)))))
  ;; SystemVerilog-2012 21.6 suggests that $test$plusargs(...) should work on
  ;; arguments other than string literals, but it seems horrible to try to
  ;; support that because we'd basically need to implement SVEX based string
  ;; prefix comparisons against the full list of all plusargs that have been
  ;; supplied, which seems really horrible.  On the other hand, supporting
  ;; $test$plusargs("foo") seems pretty straightforward so let's do that.
  (b* ((expr (vl-expr-fix expr))
       (arg-str (vl-expr-case expr
                  :vl-literal (vl-value-case expr.val
                                :vl-constint (vl-integer-to-string expr.val)
                                :vl-string expr.val.value
                                :otherwise nil)
                  :otherwise nil))
       ((unless arg-str)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Unsupported $test$plusargs(...) call.  We only ~
                         support literal strings like ~
                         $test$plusargs(\"foo\"). but found ~
                         $test$plusargs(~a0)."
                   :args (list expr)
                   :acc nil)
            (svex-x)))
       (ans-svex
        ;; SystemVerilog-2012 21.6 only says that we should return a nonzero or
        ;; zero integer.  It seems like other tools return 1 or 0, which seems
        ;; like the most sensible thing to do.
        (if (vl-$test$plusargs-p arg-str (vl-design->plusargs design))
            ;; BOZO ugly way to write these
            (sv::svex-quote (sv::4vec 1 1))
          (sv::svex-quote (sv::4vec 0 0)))))
    (mv nil ans-svex)))

#!sv
(define constraintlist-subst-memo ((x constraintlist-p)
                                   (subst svex-alist-p))
  :returns (new-x constraintlist-p)
  (if (atom x)
      nil
    (cons (change-constraint (car x) :cond (svex-subst-memo (constraint->cond (Car x)) subst))
          (constraintlist-subst-memo (cdr x) subst)))
  ///
  (defret vars-of-constraintlist-subst-memo
    (implies (not (member v (svex-alist-vars subst)))
             (not (member v (constraintlist-vars new-x))))
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))


(fty::defflexsum vttree
  :parents (vl-expr-svex-translation)
  :short "A data structure for collecting warnings and constraints
          while translating VL expressions to svex expressions."
  :long "<p>Similar to ACL2's ttrees. A vttree is either nil, a warninglist
tagged with @(':warnings'), a constraintlist tagged with @(':constraints'), or
a cons of two vttrees.</p>"

  (:none :cond (atom x)
   :shape (eq x nil)
   :type-name vttree-none
   :ctor-body nil)
  (:warnings
   :type-name vttree-warnings
   :cond (eq (car x) :warnings)
   :fields ((warnings :acc-body (cdr x)
                      :type vl-warninglist))
   :ctor-body (cons :warnings warnings))
  (:constraints
   :type-name vttree-constraints
   :cond (eq (car x) :constraints)
   :fields ((constraints :acc-body (cdr x)
                         :type sv::constraintlist))
   :ctor-body (cons :constraints constraints))
  (:context
   :type-name vttree-context
   :cond (eq (car x) :context)
   :shape (consp (cdr x))
   :fields ((ctx :acc-body (cadr x))
            (subtree :acc-body (cddr x) :type vttree))
   :ctor-body (cons :context (cons ctx subtree)))
  (:branch
   :type-name vttree-branch
   :fields ((left :acc-body (car x) :type vttree)
            (right :acc-body (cdr x) :type vttree))
   :ctor-body (cons left right))
  :post-pred-events
  ((defthmd vttree-not-equal-bad-keys
     (implies (vttree-p x)
              (and (not (equal x :warnings))
                   (not (equal x :constraints))
                   (not (equal x :context))))
     :hints(("Goal" :expand ((vttree-p x)))))
   (local (in-theory (enable vttree-not-equal-bad-keys)))))

(define vttree->warnings-acc ((x vttree-p)
                              (context)
                              (acc vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  :measure (vttree-count x)
  :verify-guards nil
  (vttree-case x
    :none (vl-warninglist-fix acc)
    :warnings (revappend-without-guard
               (if context (vl-warninglist-add-ctx x.warnings context) x.warnings)
               (vl-warninglist-fix acc))
    :constraints (vl-warninglist-fix acc)
    :context (vttree->warnings-acc x.subtree
                                                (or x.ctx context)
                                                acc)
    :branch (vttree->warnings-acc
             x.right context
             (vttree->warnings-acc x.left context acc)))
  ///
  (verify-guards vttree->warnings-acc))

;; (define vttree->warnings-acc ((x vttree-p)
;;                               (acc vl-warninglist-p))
;;   :returns (warnings vl-warninglist-p)
;;   :measure (vttree-count x)
;;   :verify-guards nil
;;   (vttree-case x
;;     :none (vl-warninglist-fix acc)
;;     :warnings (revappend-without-guard x.warnings (vl-warninglist-fix acc))
;;     :constraints (vl-warninglist-fix acc)
;;     :context (vttree->warnings-acc-with-context x.subtree x.ctx acc)
;;     :branch (vttree->warnings-acc x.right (vttree->warnings-acc x.left acc)))
;;   ///
;;   (verify-guards vttree->warnings-acc))

;; BOZO move
(defthm vl-warninglist-add-ctx-of-null-context
  (equal (vl-warninglist-add-ctx warnings nil)
         (list-fix (vl-warninglist-fix warnings)))
  :hints(("Goal" :in-theory (e/d (vl-warninglist-add-ctx vl-warning-add-ctx vl-warninglist-fix
                                                         vl-warning-fix-redef)
; Matt K. mod, 6/2020: avoid loop between vl-warning-fix-redef and
; vl-warning-of-fields.
                                 (vl-warning-of-fields)))))

(define vttree->warnings ((x vttree-p))
  :returns (warnings vl-warninglist-p)
  :measure (vttree-count x)
  :verify-guards nil
  (mbe :logic
       (vttree-case x
         :none nil
         :warnings (list-fix x.warnings)
         :constraints nil
         :context (vl-warninglist-add-ctx (vttree->warnings x.subtree) x.ctx)
         :branch (append-without-guard
                  (vttree->warnings x.left)
                  (vttree->warnings x.right)))
       :exec (rev (vttree->warnings-acc x nil nil)))
  ///


  (local (defthm vl-warninglist-add-ctx-of-vl-warninglist-add-ctx
           (implies (case-split ctx1)
                    (Equal (vl-warninglist-add-ctx (vl-warninglist-add-ctx
                                                    warnings ctx1) ctx2)
                           (vl-warninglist-add-ctx warnings ctx1)))
           :hints(("Goal" :in-theory (enable vl-warninglist-add-ctx vl-warning-add-ctx)))))

  (local (defthm vttree->warnings-acc-elim
           (equal (vttree->warnings-acc x ctx acc)
                  (revappend (vl-warninglist-add-ctx (vttree->warnings x) ctx) (vl-warninglist-fix acc)))
           :hints(("Goal" :in-theory (enable vttree->warnings-acc)))))

  (defret true-listp-of-vttree->warnings
    (true-listp warnings)
    :rule-classes :type-prescription)

  (verify-guards vttree->warnings :guard-debug t))

(define constraintlist-add-ctx ((x sv::constraintlist-p)
                                (ctx))
  :returns (new-x sv::constraintlist-p)
  (if (atom x)
      nil
    (cons (b* (((sv::constraint x1) (car x)))
            (sv::change-constraint x1
                                   :name (if (and ctx (atom x1.name))
                                             (cons ctx x1.name)
                                           x1.name)))
          (constraintlist-add-ctx (cdr x) ctx)))
  ///
  (defthm constraintlist-add-ctx-of-append
    (equal (constraintlist-add-ctx (append x y) ctx)
           (append (constraintlist-add-ctx x ctx)
                   (constraintlist-add-ctx y ctx))))

  (defthm constraintlist-add-ctx-of-atom
    (implies (atom x)
             (equal (constraintlist-add-ctx x ctx) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm constraintlist-add-ctx-of-null-ctx
    (equal (constraintlist-add-ctx constraints nil)
           (list-fix (sv::constraintlist-fix constraints)))
    :hints(("Goal" :in-theory (e/d (constraintlist-add-ctx
                                    sv::constraintlist-fix
                                    sv::constraint-fix-redef)
; Matt K. mod, 6/2020: avoid loop between sv::constraint-fix-redef and
; sv::constraint-of-fields.
                                   (sv::constraint-of-fields))))))


(define vttree->constraints-acc ((x vttree-p)
                                 (context)
                                 (acc sv::constraintlist-p))
  :returns (constraints sv::constraintlist-p)
  :measure (vttree-count x)
  :verify-guards nil
  (vttree-case x
    :none (sv::constraintlist-fix acc)
    :constraints (revappend-without-guard
                  (if context
                      (constraintlist-add-ctx x.constraints context)
                    x.constraints)
                  (sv::constraintlist-fix acc))
    :warnings (sv::constraintlist-fix acc)
    :context (vttree->constraints-acc x.subtree (or x.ctx context) acc)
    :branch (vttree->constraints-acc x.right context (vttree->constraints-acc x.left context acc)))
  ///
  (verify-guards vttree->constraints-acc))

(define vttree->constraints ((x vttree-p))
  :returns (constraints sv::constraintlist-p)
  :measure (vttree-count x)
  :verify-guards nil
  (mbe :logic
       (vttree-case x
         :none nil
         :constraints (list-fix x.constraints)
         :warnings nil
         :context (constraintlist-add-ctx (vttree->constraints x.subtree) x.ctx)
         :branch (append-without-guard
                  (vttree->constraints x.left)
                  (vttree->constraints x.right)))
       :exec (rev (vttree->constraints-acc x nil nil)))
  ///

  (local (defthm constraintlist-add-ctx-of-constraintlist-add-ctx
           (implies (case-split ctx1)
                    (equal (constraintlist-add-ctx (constraintlist-add-ctx
                                                    warnings ctx1) ctx2)
                           (constraintlist-add-ctx warnings ctx1)))
           :hints(("Goal" :in-theory (enable constraintlist-add-ctx)))))

  (defret true-listp-of-vttree->constraints
    (true-listp constraints)
    :rule-classes :type-prescription)

  (local (defthm vttree->constraints-acc-elim
           (equal (vttree->constraints-acc x ctx acc)
                  (revappend (constraintlist-add-ctx (vttree->constraints x) ctx)
                             (sv::constraintlist-fix acc)))
           :hints(("Goal" :in-theory (enable vttree->constraints-acc)))))

  (verify-guards vttree->constraints :guard-debug t))

(define vttree-join ((x vttree-p)
                     (y vttree-p))
  :returns (join vttree-p)
  (cond ((vttree-case x :none) (vttree-fix y))
        ((vttree-case y :none) (vttree-fix x))
        (t (make-vttree-branch :left x :right y)))
  ///
  (defret vttree->warnings-of-vttree-join
    (equal (vttree->warnings join)
           (append (vttree->warnings x)
                   (vttree->warnings y)))
    :hints(("Goal" :in-theory (enable vttree->warnings)
            :expand ((vttree->warnings (vttree-branch x y))))))

  (defret vttree->constraints-of-vttree-join
    (equal (vttree->constraints join)
           (append (vttree->constraints x)
                   (vttree->constraints y)))
    :hints(("Goal" :in-theory (enable vttree->constraints)
            :expand ((vttree->constraints (vttree-branch x y)))))))

(define vttree-add-warnings ((x vl-warninglist-p)
                             (vttree vttree-p)
                             &key ctx)
  :returns (new-vttree vttree-p)
  (if (atom x)
      (vttree-fix vttree)
    (vttree-join
     (if ctx
         (make-vttree-context :ctx ctx :subtree (make-vttree-warnings :warnings x))
       (make-vttree-warnings :warnings x))
     vttree))
  ///
  (defret vttree->warnings-of-vttree-add-warnings
    (equal (vttree->warnings new-vttree)
           (append (vl-warninglist-add-ctx x ctx)
                   (vttree->warnings vttree)))
    :hints (("goal" :expand ((vttree->warnings (vttree-warnings x))
                             (:free (x) (vttree->warnings (vttree-context ctx x)))))))

  (defret vttree->constraints-of-vttree-add-warnings
    (equal (vttree->constraints new-vttree)
           (vttree->constraints vttree))
    :hints (("goal" :expand ((vttree->constraints (vttree-warnings x))
                             (:free (x) (vttree->constraints (vttree-context ctx x))))))))

(define vttree-add-constraints ((x sv::constraintlist-p)
                                (vttree vttree-p)
                                &key ctx)
  :returns (new-vttree vttree-p)
  (if (atom x)
      (vttree-fix vttree)
    (vttree-join
     (if ctx
         (make-vttree-context :ctx ctx :subtree (make-vttree-constraints :constraints x))
       (make-vttree-constraints :constraints x))
     vttree))
  ///
  (defret vttree->warnings-of-vttree-add-constraints
    (equal (vttree->warnings new-vttree)
           (vttree->warnings vttree))
    :hints (("goal" :expand ((vttree->warnings (vttree-constraints x))
                             (:free (x) (vttree->warnings (vttree-context ctx x)))))))

  (defret vttree->constraints-of-vttree-add-constraints
    (equal (vttree->constraints new-vttree)
           (append (constraintlist-add-ctx x ctx)
                   (vttree->constraints vttree)))
    :hints (("goal" :expand ((vttree->constraints (vttree-constraints x))
                             (:free (x) (vttree->constraints (vttree-context ctx x))))))))

(acl2::def-b*-binder vmv
  :parents (vttree)
  :short "B* binder to automatically join returned vttrees"
  :body
  (b* (((mv ctx args)
        (b* ((mem (member :ctx acl2::args)))
          (if mem
              (mv (cadr mem)
                  (append (take (- (len acl2::args) (len mem)) acl2::args)
                          (cddr mem)))
            (mv nil args)))))
    `(b* (,(if (equal args '(vttree))
               `(__tmp__vttree . ,acl2::forms)
             `((mv . ,(subst '__tmp__vttree 'vttree args)) . ,acl2::forms))
          (vttree (vttree-join
                   ,(if ctx
                        `(make-vttree-context :ctx ,ctx :subtree __tmp__vttree)
                      '__tmp__vttree)
                   vttree)))
       ,acl2::rest-expr)))


(acl2::def-b*-binder wvmv
  :parents (vttree)
  :short "B* binder to automatically join returned warnings to a vttree"
  :body
  (b* (((mv ctx args)
        (b* ((mem (member :ctx acl2::args)))
          (if mem
              (mv (cadr mem)
                  (append (take (- (len acl2::args) (len mem)) acl2::args)
                          (cddr mem)))
            (mv nil args)))))
    `(b* (,(if (equal args '(vttree))
               `(__tmp__warnings . ,acl2::forms)
             `((mv . ,(subst '__tmp__warnings 'vttree args)) . ,acl2::forms))
          (vttree (vttree-add-warnings __tmp__warnings vttree :ctx ,ctx)))
       ,acl2::rest-expr)))






(defmacro vfatal (&rest args)
  `(b* ((warnings nil)
        (warnings (fatal . ,args)))
     (vttree-add-warnings warnings vttree)))

(defmacro vwarn (&rest args)
  `(b* ((warnings nil)
        (warnings (warn . ,args)))
     (vttree-add-warnings warnings vttree)))

(define vl-err->vfatal ((err (implies err (vl-msg-p err)))
                        &key
                        (type symbolp)
                        (msg stringp)
                        (args true-listp)
                        ((fn symbolp) '__function__)
                        ((vttree vttree-p) 'vttree))
  :returns (new-vttree vttree-p)
  (if err
      (vttree-add-warnings (b* ((warnings nil))
                             (fatal :type type
                                    :msg "~@0: ~@1"
                                    :args (list (make-vl-msg :msg (string-fix msg)
                                                             :args (mbe :logic (list-fix args) :exec args))
                                                err)
                                    :fn fn))
                           vttree)
    (vttree-fix vttree))
  ///
  (defret constraints-of-vl-err->vfatal
    (equal (vttree->constraints new-vttree)
           (vttree->constraints vttree))))


(defines vl-expr-to-svex
  :ruler-extenders :all
  :verify-guards nil
  :prepwork ((local (in-theory (disable not max
                                        acl2::member-of-cons
                                        member-equal
                                        true-listp
                                        vl-warninglist-p-when-not-consp
                                        vl-warninglist-p-when-subsetp-equal
                                        sv::svexlist-p-when-not-consp
                                        default-car
                                        acl2::repeat-when-zp
                                        sv::svex-alist-p-when-not-consp
                                        sv::svarlist-addr-p-when-subsetp-equal
                                        acl2::member-when-atom
                                        acl2::consp-of-append
                                        ;; consp-by-len-equal-1
                                        acl2::append-atom-under-list-equiv
                                        acl2::len-of-append)))
             ;; (local (defthm consp-by-len-equal-1
             ;;          (implies (equal (len x) 1)
             ;;                   (consp x))
             ;;          :hints(("Goal" :in-theory (enable len)))))
             (local (defthm and*-open
                      (implies (acl2::rewriting-negative-literal `(binary-and* ,x ,y))
                               (iff (and* x y)
                                    (and x y)))
                      :hints(("Goal" :in-theory (enable and*)))))

             (local (defthm or*-open
                      (implies (acl2::rewriting-positive-literal `(binary-or* ,x ,y))
                               (iff (or* x y)
                                    (or x y)))
                      :hints(("Goal" :in-theory (enable or*)))))

             (local (defthm expr-count-of-car-plainargs-when-unary-syscall-p
                      (implies (vl-unary-syscall-p fn x)
                               (< (vl-expr-count (car (vl-call->plainargs x)))
                                  (vl-expr-count x)))
                      :hints(("Goal" :in-theory (enable vl-unary-syscall-p)
                              :expand ((vl-expr-count x)
                                       (vl-maybe-exprlist-count (vl-call->plainargs x))
                                       (vl-maybe-expr-count (car (vl-call->plainargs x))))))))
             (local (defthm expr-p-of-car-plainargs-when-unary-syscall-p
                      (implies (vl-unary-syscall-p fn x)
                               (vl-expr-p (car (vl-call->plainargs x))))
                      :hints(("Goal" :in-theory (enable vl-unary-syscall-p)))))
             (local (defthm constraintlist-vars-of-append
                      (Equal (sv::constraintlist-vars (append a b))
                             (append (sv::constraintlist-vars a)
                                     (sv::constraintlist-vars b)))
                      :hints(("Goal" :in-theory (enable sv::constraintlist-vars)))))

             ;; (local (defthm and*-lhs
             ;;          (implies (and* x y)
             ;;                   x)
             ;;          :hints(("Goal" :in-theory (enable and*)))
             ;;          :rule-classes :forward-chaining))

             ;; (local (defthm and*-rhs
             ;;          (implies (and* x y)
             ;;                   y)
             ;;          :hints(("Goal" :in-theory (enable and*)))
             ;;          :rule-classes :forward-chaining))
             ;; (local (defcong iff iff (and* x y) 1 :hints(("Goal" :in-theory (enable and*)))))
             ;; (local (defcong iff iff (and* x y) 2 :hints(("Goal" :in-theory (enable and*)))))
             )

  #||

  (trace$ #!vl (vl-expr-to-svex-untyped
  :entry (list 'vl-expr-to-svex-untyped (with-local-ps (vl-pp-expr x)))
  :exit (b* (((list warnings svex type size) values))
  (list 'vl-expr-to-svex-untyped
  (with-local-ps (vl-print-warnings warnings))
  svex (and type (with-local-ps (vl-pp-datatype type))) size))))
  ||#
  (define vl-expr-to-svex-untyped ((x vl-expr-p)
                                   (ss vl-scopestack-p)
                                   (scopes vl-elabscopes-p))
    :short "Convert an expression to svex, and return its datatype."
    :long "<p>In some cases we need to convert an expression and also check what
type it is returning.  For example, if the expression is the port connection of
an instance array, we know the type of a single port but we don't know whether
all instances' ports are receiving the whole expression, or whether the bits of
the expression are being distributed across the instances.  To determine that,
we need to get the type of the expression.</p>

<p>We shouldn't care about the signedness of the return type here; when we only
know the size of a vector expression, we just return a unsigned packed logic
vector.</p>"
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type))))
                 (size maybe-natp :rule-classes :type-prescription))
    :measure (two-nats-measure (vl-expr-count x) 20)
    (b* ((vttree nil)
         (x (vl-expr-fix x)))
      (vl-expr-case x
        :vl-index (b* (((vmv vttree svex type)
                        (vl-index-expr-to-svex x ss scopes))
                       ((unless type)
                        (mv vttree svex type nil))
                       ((wvmv vttree size) (vl-datatype-size-warn type x nil)))
                    (mv vttree svex type size))
        :vl-cast (vl-casttype-case x.to
                   :type (b* (((mv err type)
                               (vl-datatype-usertype-resolve x.to.type ss :scopes scopes))
                              ((when err)
                               (mv (vfatal :type :vl-expr-to-svex-fail
                                           :msg "Usertypes not resolved in cast ~a0: ~@1"
                                           :args (list x err))
                                   (svex-x) nil nil))
                              ((vmv vttree type-err svex)
                               (vl-expr-to-svex-datatyped x.expr nil type ss scopes :compattype :cast))
                              ((wvmv vttree) (vl-typecast-type-error-warn type-err x ss))
                              ((wvmv vttree size) (vl-datatype-size-warn type x nil)))
                           (mv vttree svex type size))
                   :size (b* (((unless (vl-expr-resolved-p x.to.size))
                               (mv (vfatal :type :vl-expr-to-svex-fail
                                           :msg "Unresolved size cast: ~a0"
                                           :args (list x))
                                   (svex-x) nil nil))
                              (castsize  (vl-resolved->val x.to.size))
                              ((unless (posp castsize))
                               (mv (vfatal :type :vl-expr-to-svex-fail
                                           :msg "Zero or negative size cast: ~a0"
                                           :args (list x))
                                   (svex-x) nil nil))
                              ((mv vttree svex ?size)
                               (vl-expr-to-svex-selfdet x.expr castsize ss scopes)))
                           (mv vttree svex
                               (vl-size-to-unsigned-logic castsize)
                               castsize))
                   :otherwise
                   (b* (((vmv vttree svex size)
                         (vl-expr-to-svex-selfdet x nil ss scopes)))
                     (mv vttree svex
                         (and (posp size)
                              (vl-size-to-unsigned-logic size))
                         size)))

        :vl-call
        (b* (((when x.systemp)
              (b* (((mv vttree svex size)
                    (vl-expr-to-svex-selfdet x nil ss scopes)))
                (mv vttree svex
                    (and (posp size)
                         (vl-size-to-unsigned-logic size))
                    size)))
             ((vmv vttree svex ftype)
              (vl-funcall-to-svex x ss scopes))
             ((unless ftype)
              (mv vttree svex nil nil))
             ((wvmv vttree size) (vl-datatype-size-warn ftype x nil)))
          (mv vttree
              svex ftype size))

        :vl-stream
        (b* (((mv vttree svex size)
              (vl-streaming-concat-to-svex x ss scopes)))
          ;; BOZO A streaming concat shouldn't really exist in the middle of
          ;; some other expression unless there is a cast around it.  However,
          ;; we want to call vl-expr-to-svex-untyped in some top-level contexts
          ;; where a streaming concat should be allowed.  In those contexts the
          ;; size is important but not the type.  So here we'll return NIL as
          ;; the type even if we got a good size.
          (mv vttree svex nil size))

        :otherwise
        (b* (((vmv vttree svex size)
              (vl-expr-to-svex-selfdet x nil ss scopes)))
          (mv vttree svex
              (and (posp size)
                   (vl-size-to-unsigned-logic size))
              size)))))


  #||
  (trace$ #!vl (vl-streaming-concat-to-svex
  :entry (list 'vl-streaming-concat-to-svex
  (with-local-ps (vl-pp-expr x)))
  :exit (cons 'vl-streaming-concat-to-svex (cdr values))))

  ||#
  (define vl-streaming-concat-to-svex ((x vl-expr-p)
                                       (ss vl-scopestack-p)
                                       (scopes vl-elabscopes-p))
    :guard (vl-expr-case x :vl-stream)
    :measure (two-nats-measure (vl-expr-count x) 15)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp))
    (b* (((vl-stream x) (vl-expr-fix x))
         ((unless (mbt (vl-expr-case x :vl-stream)))
          ;; termination
          (mv nil (svex-x) nil))
         (vttree nil)
         ((mv err slicesize) (if (eq x.dir :left)
                                 (vl-slicesize-resolve x.size ss scopes)
                               ;; irrelevant
                               (mv nil 1)))
         ((when err)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Failed to resolve slice size of streaming ~
                               concat expression ~a0: ~@1"
                      :args (list x err))
              (svex-x) nil))
         ((vmv vttree concat concat-size) (vl-streamexprlist-to-svex x.parts ss scopes))
         ((unless concat-size)
          ;; Already warned, presumably.
          (mv vttree (svex-x) nil))

         (bitstream (if (eq x.dir :right)
                        concat
                      (sv::svcall sv::blkrev
                                  (svex-int concat-size)
                                  (svex-int slicesize)
                                  concat))))
      ;; In SV, we'd now stick the bitstream into a container of the
      ;; appropriate datatype.  But in svex, everything's just kept as a
      ;; bitstream, so we're already done.
      (mv vttree bitstream concat-size)))
  #||
  (trace$ #!vl (vl-expr-to-svex-selfdet
  :entry (list 'vl-expr-to-svex-selfdet
  (with-local-ps (vl-pp-expr x))
  :orig (with-local-ps (vl-pp-origexpr x))
  ctxsize)
  :exit (b* (((list warnings svex size) values))
  (list 'vl-expr-to-svex-selfdet
  (with-local-ps (vl-print-warnings warnings))
  svex size))))

  ||#

  (define vl-expr-to-svex-selfdet ((x vl-expr-p)
                                   (ctxsize maybe-natp)
                                   (ss vl-scopestack-p)
                                   (scopes vl-elabscopes-p))
    :short "Translates a VL expression to svex in a self-determined context, perhaps
            with a context size."
    :long "<p>This function sign- or zero-extends the result so that other
functions can assume all bits of it are good.</p>"
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription
                       "Size if available.  If not, we've already warned about it."))
    :measure (two-nats-measure (vl-expr-count x) 10)
    (b* ((x (vl-expr-fix x))
         (ctxsize (maybe-natp-fix ctxsize))
         (opacity (vl-expr-opacity x))
         (vttree nil)
         ((when (eq opacity :special))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Need a type context to interpret special expression ~a0"
                      :args (list x))
              (svex-x)
              nil))
         ((wvmv vttree class) (vl-expr-typedecide x ss scopes))
         ((unless (vl-integer-arithclass-p class))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg (if (vl-arithclass-equiv class :vl-error-class)
                               "Couldn't decide signedness of expression ~a0."
                             "Unsupported arithmetic class of expression ~a0: ~s1")
                      :args (list x class))
              (svex-x)
              nil))
         (signedness (vl-integer-arithclass->exprsign class))
         ((wvmv vttree size) (vl-expr-selfsize x ss scopes))
         ((unless size)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Couldn't size expression ~a0."
                      :args (list x))
              (svex-x)
              nil))
         (finalsize (if ctxsize (max ctxsize size) size))
         (ext-size (if (eq opacity :transparent)
                       finalsize
                     size))
         ((vmv vttree svex)
          (if (eq opacity :opaque)
              (vl-expr-to-svex-opaque x ss scopes)
            (vl-expr-to-svex-transparent x finalsize signedness ss scopes)))
         (signedness
          ;; [Jared] On 2016-03-18 we discovered that we were incorrectly
          ;; treating extension integers like '1 as signed, when the standard
          ;; says they are unsigned.  After fixing that, we found we needed to
          ;; add a special case for extints here.  Why?  If we have something
          ;; like assign foo[3:0] = '1, then the '1 is context-determined, so
          ;; normally we would sign/zero-extend it to the desired width based
          ;; on its type.  But extints are special and basically we still need
          ;; to sign-extend 'x or '1 even though they are unsigned.
          (if (vl-expr-case x
                :vl-literal (vl-value-case x.val :vl-extint)
                :otherwise nil)
              :vl-signed
            signedness)))
      (mv vttree (svex-extend signedness ext-size svex) finalsize)))

  (define vl-expr-to-svex-vector ((x vl-expr-p)
                                  (size natp)
                                  (signedness vl-exprsign-p)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p))
    :measure (two-nats-measure (vl-expr-count x) 6)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (opacity (vl-expr-opacity x))
         (vttree nil)
         ((when (eq opacity :special))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Need a type context to interpret special expression ~a0"
                      :args (list x))
              (svex-x)))
         ((unless (eq opacity :opaque))
          (vl-expr-to-svex-transparent x size signedness ss scopes))
         ((wvmv vttree selfsize) (vl-expr-selfsize x ss scopes))
         ((unless selfsize)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Sizing of ~a0 failed unexpectedly."
                      :args (list x))
              (svex-x)))
         ((vmv vttree svex)
          (vl-expr-to-svex-opaque x ss scopes))
         (size
          ;; Special case for extints -- they get sign/zero-extended at their
          ;; context size, not their self size.
          (if (vl-expr-case x
                :vl-literal (vl-value-case x.val :vl-extint)
                :otherwise nil)
              size
            selfsize)))
      (mv vttree (svex-extend signedness size svex))))

  (define vl-expr-to-svex-transparent ((x vl-expr-p)
                                       (size natp)
                                       (signedness vl-exprsign-p)
                                       (ss vl-scopestack-p)
                                       (scopes vl-elabscopes-p))
    :guard (equal (vl-expr-opacity x) :transparent)
    :measure (two-nats-measure (vl-expr-count x) 4)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (vttree nil))
      (vl-expr-case x
        :vl-unary
        (b* (((unless (member x.op '(:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Operators with side-effects aren't supported: ~a0"
                          :args (list x))
                  (svex-x)))
             ((vmv vttree subexp)
              (vl-expr-to-svex-vector x.arg size signedness ss scopes))
             ((vmv err svex)
              (vl-unaryop-to-svex x.op subexp size size signedness)))
          (mv (vl-err->vfatal err  :type :vl-expr-to-svex-fail
                              :msg "Failed to convert expression ~a0"
                              :args (list x))
              svex))
        :vl-binary
        ;; Two categories: either transparent in just the first operand, or both.
        (b* (((vmv vttree left-svex)
              (vl-expr-to-svex-vector x.left size signedness ss scopes))
             ((vmv vttree right-svex right-size)
              (if (member x.op '(:vl-binary-power
                                 :vl-binary-shl
                                 :vl-binary-shr
                                 :vl-binary-ashl
                                 :vl-binary-ashr))
                  ;; Transparent only in the first operand.
                  (vl-expr-to-svex-selfdet x.right nil ss scopes)
                ;; Transparent in both operands.
                (b* (((mv vttree right-svex)
                      (vl-expr-to-svex-vector x.right size signedness ss scopes)))
                  (mv vttree right-svex size))))
             ((vmv err svex)
              (vl-binaryop-to-svex x.op left-svex right-svex size
                                   ;; Presumably we don't get here if we don't
                                   ;; get a size for the right arg.  But in any
                                   ;; case we've already warned about it.
                                   (or right-size size)
                                   size signedness)))
          (mv (vl-err->vfatal err :type :vl-expr-to-svex-fail
                              :msg "Failed to convert expression ~a0"
                              :args (list x))
              svex))

        :vl-qmark
        (b* (((vmv vttree test-svex ?test-size)
              (vl-expr-to-svex-selfdet x.test nil ss scopes))
             ((vmv vttree then-svex)
              (vl-expr-to-svex-vector x.then size signedness ss scopes))
             ((vmv vttree else-svex)
              (vl-expr-to-svex-vector x.else size signedness ss scopes)))
          (mv (vttree-fix vttree)
              (sv::svcall sv::? test-svex then-svex else-svex)))

        :vl-mintypmax
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Don't yet support mintypmax expressions: ~a0."
                    :args (list x))
            (svex-x))
        :otherwise
        (mv (vttree-fix vttree) (prog2$ (impossible) (svex-x))))))

  (define vl-inside-expr-cases-to-svex
    ;; Process ELEM inside { RANGE, VAL, RANGE, ... }
    ((elem          vl-expr-p           "LHS expression to check for set membership.")
     (elem-selfsize natp                "Pre-computed self-determined size of lhs.")
     (elem-type     vl-exprsign-p       "Pre-computed self-determined signedness of the lhs.")
     (set           vl-valuerangelist-p "RHS expressions and ranges.")
     (ss            vl-scopestack-p)
     (scopes        vl-elabscopes-p)
     (fullexpr      vl-expr-p           "Context for error messages."))
    :measure (two-nats-measure (+ (vl-expr-count elem) (vl-valuerangelist-count set)) 0)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((vttree nil)
         (fullexpr (vl-expr-fix fullexpr))
         (set      (vl-valuerangelist-fix set))
         ((when (atom set))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Inside expression with no cases: ~a0"
                      :args (list fullexpr))
              (svex-x)))
         ((when (atom (cdr set)))
          ;; Singleton set, so no need to wrap it in an OR.
          (vl-inside-expr-case-to-svex elem elem-selfsize elem-type (car set) ss scopes fullexpr))
         ;; Else, just OR together the membership checks.
         ((vmv vttree in-first-svex) (vl-inside-expr-case-to-svex elem elem-selfsize elem-type (car set) ss scopes fullexpr))
         ((vmv vttree in-rest-svex)  (vl-inside-expr-cases-to-svex elem elem-selfsize elem-type (cdr set) ss scopes fullexpr))
         (in-any-svex                  (sv::svcall sv::bitor in-first-svex in-rest-svex)))
      (mv vttree in-any-svex)))

  (define vl-inside-expr-case-to-svex
    ;; Process a single ELEM inside { RANGE }
    ((elem          vl-expr-p           "LHS expression to check for set membership.")
     (elem-selfsize natp                "Pre-computed self-determined size of lhs.")
     (elem-type     vl-exprsign-p       "Pre-computed self-determined signedness of the lhs.")
     (range         vl-valuerange-p     "Single member (or range) of the set.")
     (ss            vl-scopestack-p)
     (scopes        vl-elabscopes-p)
     (fullexpr      vl-expr-p           "Context for error messages."))
    :measure (two-nats-measure (+ (vl-expr-count elem) (vl-valuerange-count range)) 5)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((vttree nil)
         (elem-selfsize (lnfix elem-selfsize))
         (elem-type     (vl-exprsign-fix elem-type))
         (elem-class    (vl-exprsign->arithclass elem-type))
         (elem          (vl-expr-fix elem))
         (fullexpr      (vl-expr-fix fullexpr)))
      (vl-valuerange-case range
        :valuerange-single
        (b* (((wvmv vttree rhs-size)  (vl-expr-selfsize range.expr ss scopes))
             ((wvmv vttree rhs-class) (vl-expr-typedecide range.expr ss scopes))
             ((unless (and* rhs-size (vl-integer-arithclass-p rhs-class)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to find size and signedness of expression ~a0"
                          :args (list range.expr))
                  (svex-x)))
             (final-size               (max elem-selfsize rhs-size))
             (final-class              (vl-arithclass-max elem-class rhs-class))
             (final-type               (vl-integer-arithclass->exprsign final-class))
             ((vmv vttree elem-svex) (vl-expr-to-svex-vector elem final-size final-type ss scopes))
             ((vmv vttree rhs-svex)  (vl-expr-to-svex-vector range.expr final-size final-type ss scopes))
             ((mv err svex)
              (vl-binaryop-to-svex :vl-binary-wildeq elem-svex rhs-svex final-size final-size 1 :vl-unsigned))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to convert expression ~a0 ==? ~a1 for inside expr ~a2: ~@3"
                          :args (list elem range.expr fullexpr err))
                  (svex-x))))
          (mv (vttree-fix vttree) svex))
        :valuerange-range
        (b* (;; The range can have a dollar sign to mean the lowest or highest
             ;; value in the range.  Note that NCVerilog says that, e.g., 1'bx
             ;; inside { [$:$] } is X instead of true.  (Our version of VCS
             ;; doesn't seem to support $ signs yet, so we can't test this on
             ;; both simulators.)  I think a nice, easy way to handle this is
             ;; to just replace $ signs with elem itself.  That'll turn things
             ;; into A <= A comparisons, which will be true unless there are
             ;; X/Z bits, and that seems like what NCV does.
             (low   (vl-convert-dollarsign-to-expr range.low elem))
             (high  (vl-convert-dollarsign-to-expr range.high elem))

             ;; Context will be the max size/sign of expr, low, and high, so we
             ;; need to know the types and sizes of everything in play...
             ((wvmv vttree low-size)  (vl-expr-selfsize   low ss scopes))
             ((wvmv vttree low-class) (vl-expr-typedecide low ss scopes))
             ((unless (and* low-size (vl-integer-arithclass-p low-class)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to find size and signedness of expression ~a0"
                          :args (list low))
                  (svex-x)))
             ((wvmv vttree high-size)  (vl-expr-selfsize   high ss scopes))
             ((wvmv vttree high-class) (vl-expr-typedecide high ss scopes))
             ((unless (and* high-size (vl-integer-arithclass-p high-class)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to find size and signedness of expression ~a0"
                          :args (list high))
                  (svex-x)))

             ;; First guess -- all sizes matter
             ;; (final-size               (max elem-selfsize (max low-size high-size)))
             ;; (final-type               (vl-exprsign-max elem-type (vl-exprsign-max low-type high-type)))
             ;; ((vmv vttree elem-svex) (vl-expr-to-svex-vector elem final-size final-type ss scopes))
             ;; ((vmv vttree low-svex)  (vl-expr-to-svex-vector low  final-size final-type ss scopes))
             ;; ((vmv vttree high-svex) (vl-expr-to-svex-vector high final-size final-type ss scopes))
             ;; ((mv err low<=elem-svex)
             ;;  (vl-binaryop-to-svex :vl-binary-lte low-svex elem-svex final-size final-size 1 :vl-unsigned))
             ;; ((when err)
             ;;  (mv (vfatal :type :vl-expr-to-svex-fail
             ;;             :msg "Failed to convert ~a0 <= ~a1 for inside expr ~a2: ~@3"
             ;;             :args (list low elem fullexpr err))
             ;;      (svex-x)))
             ;; ((mv err elem<=high-svex)
             ;;  (vl-binaryop-to-svex :vl-binary-lte elem-svex high-svex final-size final-size 1 :vl-unsigned))
             ;; ((when err)
             ;;  (mv (vfatal :type :vl-expr-to-svex-fail
             ;;             :msg "Failed to convert ~a0 <= ~a1 for inside expr ~a2: ~@3"
             ;;             :args (list elem high fullexpr err))
             ;;      (svex-x)))
             ;; (final-svex (sv::svcall sv::bitand low<=elem-svex elem<=high-svex)))

             ;; New guess -- do comparisons independently
             (lowcmp-size              (max elem-selfsize low-size))
             (lowcmp-class             (vl-arithclass-max elem-class low-class))
             (lowcmp-type              (vl-integer-arithclass->exprsign lowcmp-class))
             ((vmv vttree elem-svex) (vl-expr-to-svex-vector elem lowcmp-size lowcmp-type ss scopes))
             ((vmv vttree low-svex)  (vl-expr-to-svex-vector low  lowcmp-size lowcmp-type ss scopes))
             ((mv err low<=elem-svex)
              (vl-binaryop-to-svex :vl-binary-lte low-svex elem-svex lowcmp-size lowcmp-size 1 :vl-unsigned))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to convert ~a0 <= ~a1 for inside expr ~a2: ~@3"
                          :args (list low elem fullexpr err))
                  (svex-x)))

             (highcmp-size             (max elem-selfsize high-size))
             (highcmp-class            (vl-arithclass-max elem-class high-class))
             (highcmp-type             (vl-integer-arithclass->exprsign highcmp-class))
             ((vmv vttree elem-svex) (vl-expr-to-svex-vector elem highcmp-size highcmp-type ss scopes))
             ((vmv vttree high-svex) (vl-expr-to-svex-vector high highcmp-size highcmp-type ss scopes))
             ((mv err elem<=high-svex)
              (vl-binaryop-to-svex :vl-binary-lte elem-svex high-svex highcmp-size highcmp-size 1 :vl-unsigned))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to convert ~a0 <= ~a1 for inside expr ~a2: ~@3"
                          :args (list elem high fullexpr err))
                  (svex-x)))
             (final-svex (sv::svcall sv::bitand low<=elem-svex elem<=high-svex)))
          (mv (vttree-fix vttree) final-svex)))))



  (define vl-typequery-syscall-args-extract ((x vl-expr-p)
                                             (ss vl-scopestack-p)
                                             (scopes vl-elabscopes-p))
    ;; A syscall like $size(...) or $bits(...) takes a type like integer, or
    ;; an expression like foo, or a type and expression argument where the
    ;; expression is something like an array dimension into the type, or an
    ;; expression and an index.  Here we are just consolidating these cases
    ;; so that we can get the type and the index no matter what format the
    ;; arguments are in.
    :guard (vl-expr-case x :vl-call)
    :measure (two-nats-measure (vl-expr-count x) 3)
    :returns (mv (okp)
                 (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type vl-maybe-datatype-p)
                 (index (iff (vl-expr-p index) index)))
    (b* (((unless (mbt (vl-expr-case x :vl-call)))
          (mv nil nil nil nil))
         ((vl-call x) (vl-expr-fix x))
         (vttree nil)
         ;; Bozo -- to optimize proof time, maybe pull some of this
         ;; junk out into a different function in the mutual recursion.
         (args-ok (and (if x.typearg
                           (or (atom x.plainargs)
                               (and (car x.plainargs)
                                    (atom (cdr x.plainargs))))
                         (and (consp x.plainargs)
                              (car x.plainargs)
                              (or (atom (cdr x.plainargs))
                                  (atom (cddr x.plainargs)))))
                       (not x.namedargs)))
         ((unless args-ok)
          (mv nil
              (vfatal :type :vl-expr-unsupported
                      :msg "Unsupported system call: ~a0 (bad arity for type query)"
                      :args (list x))
              nil nil))
         ((when x.typearg)
          (mv t nil x.typearg (and (consp x.plainargs) (car x.plainargs))))
         ((mv vttree ?arg-svex type ?size)
          (vl-expr-to-svex-untyped (car x.plainargs) ss scopes)))
      (mv t vttree type (and (consp (cdr x.plainargs)) (cadr x.plainargs)))))



  (define vl-expr-to-svex-opaque ((x vl-expr-p)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p))
    :guard (equal (vl-expr-opacity x) :opaque)
    :measure (two-nats-measure (vl-expr-count x) 4)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (ss (vl-scopestack-fix ss))
         (scopes (vl-elabscopes-fix scopes))
         (vttree nil))
      (vl-expr-case x

        :vl-literal
        (b* (((mv err svex) (vl-value-to-svex x.val)))
          (mv (vl-err->vfatal err
                              :type :vl-expr-to-svex-fail
                              :msg "Failed to convert expression ~a0"
                              :args (list x))
              svex))

        :vl-index
        (b* (((vmv vttree svex &)
              (vl-index-expr-to-svex x ss scopes)))
          (mv vttree svex))

        :vl-unary
        ;; All the opaque unary operations have 1-bit results and
        ;; selfdetermined operands.
        (b* (((vmv vttree arg-svex arg-size) (vl-expr-to-svex-selfdet x.arg nil ss scopes))
             ((unless arg-size)
              ;; already warned
              (mv vttree (svex-x)))
             ((mv err svex)
              (vl-unaryop-to-svex x.op arg-svex arg-size 1 :vl-unsigned)))
          (mv (vl-err->vfatal err
                              :type :vl-expr-to-svex-fail
                              :msg "Failed to convert expression ~a0"
                              :args (list x))
              svex))

        :vl-binary
        ;; Two types of operators here: logicals, where the operands are
        ;; selfdetermined, and comparisons, where the operands are sized to the
        ;; larger of the two.
        (b* (((when (member x.op '(:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)))
              ;; Logicals -- self-determined operands
              (b* (((vmv vttree left-svex left-size) (vl-expr-to-svex-selfdet x.left nil ss scopes))
                   ((vmv vttree right-svex right-size) (vl-expr-to-svex-selfdet x.right nil ss scopes))
                   ((unless (and* left-size right-size))
                    ;; already warned
                    (mv vttree (svex-x)))
                   ;; It doesn't matter if these are sign- or zero-extended.
                   ((mv err svex)
                    (vl-binaryop-to-svex x.op left-svex right-svex left-size right-size 1 :vl-unsigned)))
                (mv (vl-err->vfatal err
                                    :type :vl-expr-to-svex-fail
                                    :msg "Failed to convert expression ~a0"
                                    :args (list x))
                    svex)))
             ;; Vectors -- find sizes first
             ((wvmv vttree left-size) (vl-expr-selfsize x.left ss scopes))
             ((wvmv vttree right-size) (vl-expr-selfsize x.right ss scopes))
             ((wvmv vttree left-class) (vl-expr-typedecide x.left ss scopes))
             ((wvmv vttree right-class) (vl-expr-typedecide x.right ss scopes))
             ((unless (and* left-size right-size
                            (vl-integer-arithclass-p left-class)
                            (vl-integer-arithclass-p right-class)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to find size and signedness of expression ~a0"
                          :args (list (if (and left-size (vl-integer-arithclass-p left-class))
                                          x.right
                                        x.left)))
                  (svex-x)))
             ;; Size each under the max size
             (arg-size  (max left-size right-size))
             (arg-class (vl-arithclass-max left-class right-class))
             (arg-type  (vl-integer-arithclass->exprsign arg-class))
             ((vmv vttree left-svex) (vl-expr-to-svex-vector x.left arg-size arg-type ss scopes))
             ((vmv vttree right-svex) (vl-expr-to-svex-vector x.right arg-size arg-type ss scopes))
             ((mv err svex)
              (vl-binaryop-to-svex x.op left-svex right-svex arg-size arg-size 1 :vl-unsigned)))
          (mv (vl-err->vfatal err
                              :type :vl-expr-to-svex-fail
                              :msg "Failed to convert expression ~a0"
                              :args (list x))
              svex))

        :vl-concat
        (b* (((vmv vttree svexes sizes) (vl-exprlist-to-svex-selfdet x.parts ss scopes))
             ((when (member nil sizes))
              ;; already warned
              (mv vttree (svex-x)))
             (svex (svex-concat-list sizes svexes)))
          (mv (vttree-fix vttree) svex))

        :vl-multiconcat
        (b* (((vmv vttree svexes sizes) (vl-exprlist-to-svex-selfdet x.parts ss scopes))
             ((unless (vl-expr-resolved-p x.reps))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Unresolved reps in multiple concatenation ~a0"
                          :args (list x))
                  (svex-x)))
             (reps (vl-resolved->val x.reps))
             ((unless (<= 0 reps))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Negative value for reps in multiple concatenation ~a0"
                          :args (list x))
                  (svex-x)))
             ((when (member nil sizes))
              (mv vttree (svex-x)))
             (svex
              (svex-multiconcat reps svexes sizes)))
          (mv (vttree-fix vttree) svex))

        :vl-inside
        (b* (((wvmv vttree elem-selfsize) (vl-expr-selfsize x.elem ss scopes))
             ((wvmv vttree elem-class)    (vl-expr-typedecide x.elem ss scopes))
             ((unless (and* elem-selfsize
                            (vl-integer-arithclass-p elem-class)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Failed to find size and signedness of inside expression lhs: ~a0"
                          :args (list x))
                  (svex-x)))
             (elem-type (vl-integer-arithclass->exprsign elem-class))
             ((vmv vttree svex)
              (vl-inside-expr-cases-to-svex x.elem elem-selfsize elem-type x.set ss scopes x)))
          (mv (vttree-fix vttree) svex))

        :vl-call
        (if x.systemp
            (b* ((simple-name (vl-simple-id-name x.name))
                 ((unless simple-name)
                  (mv (vfatal :type :vl-expr-to-svex-fail
                              :msg "Bad system function name: ~a0"
                              :args (list x))
                      (svex-x)))

                 ((when (member-equal simple-name '("$signed" "$unsigned")))
                  ;; Same as a signedness cast -- don't need to do anything but check arity.
                  (b* (((unless (and (consp x.plainargs)
                                     (car x.plainargs)
                                     (not (consp (cdr x.plainargs)))
                                     (not x.typearg)
                                     (not x.namedargs)))
                        (mv (vfatal :type :vl-expr-to-svex-fail
                                    :msg "Bad arity for system call ~a0"
                                    :args (list x))
                            (svex-x)))
                       ((mv vttree svex &)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree svex)))

                 ((when (vl-unary-syscall-p "$clog2" x))
                  (b* (((vmv vttree arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree
                        (sv::svcall sv::clog2 arg-svex))))

                 ((when (vl-unary-syscall-p "$isunknown" x))
                  (b* (((vmv vttree arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree
                        (sv::svcall sv::uxor (sv::svcall sv::bitxor arg-svex arg-svex)))))

                 ((when (vl-unary-syscall-p "$countones" x))
                  (b* (((vmv vttree arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree
                        (sv::svcall sv::countones arg-svex))))

                 ((when (vl-unary-syscall-p "$onehot" x))
                  (b* (((vmv vttree arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree
                        (sv::svcall sv::onehot arg-svex))))

                 ((when (vl-unary-syscall-p "$onehot0" x))
                  (b* (((vmv vttree arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.plainargs) nil ss scopes)))
                    (mv vttree
                        (sv::svcall sv::onehot0 arg-svex))))

                 ((when (vl-unary-syscall-p "$test$plusargs" x))
                  (b* ((design (vl-scopestack->design ss))
                       ((unless design)
                        (mv (vfatal :type :vl-expr-to-svex-fail
                                    :msg "Can't look up plusargs without a design."
                                    :args (list x))
                            (svex-x)))
                       ((mv warnings svex)
                        (vl-$test$plusargs-to-svex (car x.plainargs) design))
                       (vttree (vttree-add-warnings warnings vttree)))
                    (mv vttree svex)))

                 ;; It happens that almost all the system functions we support
                 ;; basically act on datatypes, and if an expression is given
                 ;; instead, they run on the type of the expression.
                 ((vmv args-ok vttree type index)
                  (vl-typequery-syscall-args-extract x ss scopes))

                 ((unless (and args-ok type))
                  ;; already warned
                  (mv vttree (svex-x)))

                 ((when (and index
                             (not (and (vl-expr-resolved-p index)
                                       (<= 0 (vl-resolved->val index))))))
                  (mv (vfatal :type :vl-expr-unsupported
                              :msg "Unsupported system call: ~a0 ~
                                         (dimension argument not resolved to ~
                                         nonnegative constant)"
                              :args (list x))
                      (svex-x)))

                 ((wvmv vttree svex)
                  (vl-datatype-syscall-to-svex x simple-name type
                                               (and index (vl-resolved->val index))
                                               ss scopes)))
              (mv vttree svex))

          (b* (((vmv vttree svex &)
                (vl-funcall-to-svex x ss scopes)))
            (mv vttree svex)))

        :vl-cast
        ;; If we get here, we've already gotten the size/signedness of the cast
        ;; expression and decided it's OK as a vector type.  However, the inner
        ;; expression might not be a vector expression -- e.g. the type could
        ;; be a packed struct and the inner expression an assignment pattern
        ;; creating that struct.  So we have to use vl-expr-to-svex-datatyped
        ;; here.
        (vl-casttype-case x.to
          :type (b* (((mv err to-type) (vl-datatype-usertype-resolve x.to.type ss
                                                                     :scopes scopes))
                     ((when err)
                      (mv (vfatal :type :vl-expr-to-svex-fail
                                  :msg "Usertypes not resolved in cast ~a0: ~@1"
                                  :args (list x err))
                          (svex-x)))
                     ((vmv vttree type-err svex)
                      (vl-expr-to-svex-datatyped x.expr nil to-type ss scopes :compattype :cast))
                     ((wvmv vttree) (vl-typecast-type-error-warn type-err x ss)))
                  (mv vttree svex))
          :size (b* (((unless (vl-expr-resolved-p x.to.size))
                      (mv (vfatal :type :vl-expr-to-svex-fail
                                  :msg "Unresolved size cast: ~a0"
                                  :args (list x))
                          (svex-x)))
                     (size (vl-resolved->val x.to.size))
                     ((unless (<= 0 size))
                      (mv (vfatal :type :vl-expr-to-svex-fail
                                  :msg "Negative size cast: ~a0"
                                  :args (list x))
                          (svex-x)))
                     ((mv vttree svex &)
                      (vl-expr-to-svex-selfdet x.expr size ss scopes)))
                  (mv vttree svex))
          :signedness
          ;; Don't need to do anything about the signedness here; it only
          ;; affects the expressions outside this one.  Also, tests seem to
          ;; indicate that the signedness cast is opaque, so we fortunately
          ;; don't need a contextsize.
          (b* (((mv vttree svex &)
                (vl-expr-to-svex-selfdet x.expr nil ss scopes)))
            (mv vttree svex))
          :const
          ;; What does this even mean?
          (b* (((mv vttree svex &)
                (vl-expr-to-svex-selfdet x.expr nil ss scopes)))
            (mv vttree svex)))


        :vl-pattern
        (b* (((unless x.pattype)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Untyped assignment pattern: ~a0"
                          :args (list x))
                  (svex-x)))
             ((mv err pattype) (vl-datatype-usertype-resolve x.pattype ss :scopes scopes))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Usertypes not resolved in pattern ~a0: ~@1"
                          :args (list x err))
                  (svex-x)))
             ((vmv vttree type-err svex)
              (vl-assignpat-to-svex x.pat pattype ss scopes x))
             ((wvmv vttree) (vl-assignpat-cast-type-error-warn type-err x ss)))
          (mv vttree svex))
        :otherwise
        (mv (vttree-fix vttree) (prog2$ (impossible) (svex-x))))))

  #||

  (defttag foo)
  (trace$ #!vl (vl-index-expr-to-svex
  :entry (list 'vl-index-expr-to-svex (with-local-ps (vl-pp-expr x)))
  :exit (b* (((list ?vttree ?svex ?type) values))
  (list 'vl-index-expr-to-svex
  (with-local-ps (vl-print-vttree vttree))))))

  #!vl
  (defun traces (names)
  (if (Atom names)
  nil
  (cons (let ((fn (car names)))
  `(trace$ (,fn :entry '(,fn)
  :exit (b* ((vttree (car values)))
  (list ',fn (with-local-ps (vl-print-vttree vttree)))))))
  (traces (cdr names)))))

  #!vl
  (defmacro do-traces (&rest names)
  (cons 'er-progn
  (traces names)))

  #!vl
  (do-traces vl-expr-to-svex-datatyped-fn
  vl-expr-to-svex-untyped
  vl-index-expr-to-svex
  vl-streamexpr-to-svex)
  ||#

  (define vl-index-expr-to-svex ((x vl-expr-p)
                                 (ss vl-scopestack-p)
                                 (scopes vl-elabscopes-p))
    :guard (vl-expr-case x :vl-index)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type)))))
    :measure (two-nats-measure (vl-expr-count x) 2)
    (b* ((vttree nil)
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv (vttree-fix vttree) (svex-x) nil))
         (x (vl-expr-fix x))
         ((mv err opinfo) (vl-index-expr-typetrace x ss scopes))
         ((when err)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Failed to convert expression typetrace ~a0: ~@1"
                      :args (list x err))
              (svex-x) nil))
         ((vl-operandinfo opinfo))
         ((vmv vttree svex-indices ?sizes)
          (vl-exprlist-to-svex-selfdet
           (vl-operandinfo->indices opinfo) ss scopes))
         ((mv err svex)
          (vl-operandinfo-to-svex opinfo svex-indices ss scopes)))
      (mv (vl-err->vfatal err
                          :type :vl-expr-to-svex-fail
                          :msg "Failed to convert expression ~a0"
                          :args (list x))
          svex
          opinfo.type)))

  ;; (trace$ #!vl (vl-funcall-to-svex
  ;;               :entry (list 'vl-funcall-to-svex
  ;;                            (with-local-ps (vl-pp-expr x)))
  ;;               :exit (list 'vl-funcall-to-svex
  ;;                           (with-local-ps (vl-print-vttree (car values)))
  ;;                           (and (caddr values)
  ;;                                (with-local-ps (vl-pp-datatype (caddr values)))))))

  (define vl-funcall-to-svex ((x vl-expr-p)
                              (ss vl-scopestack-p)
                              (scopes vl-elabscopes-p))
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type)))))
    :guard (vl-expr-case x :vl-call)
    :measure (two-nats-measure (vl-expr-count x) 2)
    (b* ((vttree nil)
         ((unless (mbt (vl-expr-case x :vl-call)))
          (impossible) ;; need this case for measure
          (mv (vttree-fix vttree) (svex-x) nil))
         ((vl-call x) (vl-expr-fix x))
         ((mv err trace ?context ?tail) (vl-follow-scopeexpr x.name ss))
         ((when err)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Failed lookup of function ~a0"
                      :args (list x.name))
              (svex-x) nil))
         ((vl-hidstep step) (car trace))
         ((unless (eq (tag step.item) :vl-fundecl))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Lookup of function ~a0 yielded ~a1"
                      :args (list x.name step.item))
              (svex-x) nil))
         (decl-scopes (vl-elabscopes-traverse (rev step.elabpath) scopes))
         (info (vl-elabscopes-item-info (vl-fundecl->name step.item) decl-scopes))
         (item (or info step.item))
         ((unless (eq (tag item) :vl-fundecl))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Lookup of function ~a0 yielded ~a1"
                      :args (list x.name item))
              (svex-x) nil))
         ((vl-fundecl item))
         ;; ((mv err fnname trace) (vl-funname->svex-funname x.name ss))
         ((unless (vl-datatype-resolved-p item.rettype))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Function hasn't been preprocessed (return type unresolved): ~a0"
                      :args (list x))
              (svex-x) nil))
         (port-types (vl-portdecllist->types item.portdecls))
         ((unless (vl-datatypelist-resolved-p port-types))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Function hasn't been preprocessed (unresolved ~
                           types in portdecls): ~a0"
                      :args (list x))
              (svex-x) nil))
         ((when (acl2::hons-dups-p (vl-portdecllist->names item.portdecls)))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Function declaration has duplicate port names so we can't process call ~a0"
                      :args (list x))
              (svex-x) nil))
         ((mv err x.args) (vl-funcall-args-to-ordered item.portdecls x.plainargs x.namedargs))
         ((when err)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Bad arguments in function call ~a0: ~@1"
                      :args (list x err))
              (svex-x) nil))
         ((unless item.function)
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Function hasn't been preprocessed (unresolved ~
                           body function): ~a0"
                      :args (list x))
              (svex-x) nil))
         ((vmv vttree type-errs args-svex)
          (vl-exprlist-to-svex-datatyped
           x.args
           port-types
           ss scopes :compattype :assign))
         ((wvmv vttree) (vl-subexpr-type-error-list-warn x type-errs ss))
         (comp-alist (vl-function-pair-inputs-with-actuals item.portdecls args-svex))
         ((with-fast comp-alist))
         (ans (sv::svex-subst-memo item.function comp-alist))
         (constraints (sv::constraintlist-subst-memo item.constraints comp-alist))
         (vttree (vttree-add-constraints constraints vttree)))
      (clear-memoize-table 'sv::svex-subst-memo)
      (mv (vttree-fix vttree) ans item.rettype)))

  #||

  (trace$ #!vl (vl-expr-to-svex-datatyped-fn
  :entry (list 'vl-expr-to-svex-datatyped
  (with-local-ps (vl-pp-expr x))
  (with-local-ps (vl-pp-vardecl (make-vl-vardecl :name "____" :type type :loc *vl-fakeloc*)))
  (vl-scopestack->hashkey ss)
  (strip-cars scopes))
  ::exit (list 'vl-expr-to-svex-datatyped
  (with-local-ps (vl-print-vttree (car values)))
  (cadr values))))

  ||#

  (define vl-expr-to-svex-datatyped ((x    vl-expr-p)
                                     (lhs  vl-maybe-expr-p
                                           "LHS, if applicable, for truncation warnings.")
                                     (type vl-datatype-p)
                                     (ss vl-scopestack-p)
                                     (scopes vl-elabscopes-p)
                                     &key
                                     ((compattype vl-typecompat-p) ':equiv)
                                     (explicit-cast-p booleanp))
    :guard (vl-datatype-resolved-p type)
    :measure (two-nats-measure (vl-expr-count x) 16)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type-err vl-maybe-type-error-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (lhs (vl-maybe-expr-fix lhs))
         (type (vl-datatype-fix type))
         (ss (Vl-scopestack-fix ss))
         (scopes (vl-elabscopes-fix scopes))
         (compattype (vl-typecompat-fix compattype))
         (vttree nil)
         (opacity (vl-expr-opacity x))
         (packedp (vl-datatype-packedp type))
         (selfdetp (and packedp
                        (not (eq opacity :special))
                        (not (vl-expr-case x :vl-pattern))
                        (or (not (vl-expr-case x :vl-qmark))
                            ;; It used to be that when we had a qmark
                            ;; expression, we never went the self-determined
                            ;; route because there could have been patterns
                            ;; inside the branches.  This led to bugs due to
                            ;; not propagating the type/size information
                            ;; between the branches -- e.g.
                            ;; 1'b1 ? signed'(a[3:0]) : 8'
                            ;; would produce signx(4,a) where it should have
                            ;; produced zerox(4,a).
                             (b* (((mv & class) (vl-expr-typedecide x ss scopes)))
                               ;; We omit these warnings for now, we'll get
                               ;; them elsewhere.
                               (vl-integer-arithclass-p class)))))
         ((when selfdetp)
          ;; A non-special opacity generally means the expression is
          ;; vector-like, and I think that if the datatype is packed we get the
          ;; right results by simply treating the expression as a vector with
          ;; the given size.  We may need to add exceptions to this.
          (b* (((mv err size) (vl-datatype-size type))
               ((when (or err (not size)))
                ;; (break$)
                (mv (vfatal :type :vl-expr-to-svex-fail
                            :msg "Couldn't size packed datatype ~a0"
                            :args (list (vl-datatype-fix type)))
                    nil
                    (svex-x)))
               ((vmv vttree svex ?rhs-size) (vl-expr-to-svex-selfdet x size ss scopes))

               ;; ((vmv vttree) (vl-maybe-warn-about-implicit-truncation lhs size x rhs-size ss))
               ((mv & x-selfsize) (vl-expr-selfsize x ss scopes))
               ((unless x-selfsize)
                ;; Some kind of error.
                (mv vttree nil svex))
               ;; ((vmv vttree)
               ;;  (if (and x-selfsize
               ;;           ;; [Jared] Previously we didn't exclude casts here,
               ;;           ;; but that meant that VL-Lint issued warnings about
               ;;           ;; cases like foo_t'(bar) where the logic designer was
               ;;           ;; explicitly using a cast to extend bar to additional
               ;;           ;; bits.  Designers complained about these warnings,
               ;;           ;; so, we now suppress extension warnings in case of
               ;;           ;; casts.  We originally tried to just check whether
               ;;           ;; compattype was :cast, but that gets used in more
               ;;           ;; places so we add an explicit-cast-p argument.
               ;;           (not explicit-cast-p))
               ;;      (vl-maybe-warn-about-implicit-extension size x-selfsize x ss)
               ;;    nil))
               (type-err (vl-trunc/extend-type-err size x-selfsize)))
            (mv vttree type-err svex))))

      (vl-expr-case x
        :vl-index
        (b* (((vmv vttree svex itype)
              (vl-index-expr-to-svex x ss scopes))
             ((unless itype)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Couldn't find type for expression: ~a0"
                          :args (list x))
                  nil
                  svex))
             (type-err (vl-datatype-compatibility-type-error type itype compattype)))
          (mv vttree type-err svex))

        :vl-qmark
        (b* (((vmv vttree test-svex ?test-size)
              (vl-expr-to-svex-selfdet x.test nil ss scopes))

             ((vmv vttree type-err1 then-svex)
              ;; BOZO should we really pass the lhs down here?  Maybe?
              (vl-expr-to-svex-datatyped x.then lhs type ss scopes
                                         :compattype compattype
                                         :explicit-cast-p explicit-cast-p))
             ((vmv vttree type-err2 else-svex)
              (vl-expr-to-svex-datatyped x.else lhs type ss scopes
                                         :compattype compattype
                                         :explicit-cast-p explicit-cast-p))

             (svex (sv::svcall sv::? test-svex then-svex else-svex))

             ;; [Sol] Tweaked the check above again -- now we actually run
             ;; typedecide to see if the qmark produces an integer-class object
             ;; and use vl-expr-to-svex-selfdet if so, so I think we should get
             ;; the right warnings now without doing this extra thing.
             ;; 
             ;; ;; [Jared] historically we didn't need to do anything special
             ;; ;; here, but in commit aad0bcb6b181dcba68385ff764a967a3528db506 we
             ;; ;; tweaked the check for vector-like expressions above (packed,
             ;; ;; non-special, not pattern, not qmark) to include ?: expressions
             ;; ;; in order to support expressions like a ? '{...} : '{...}.
             ;; ;; Unfortunately, that means we no longer get fussy size warnings
             ;; ;; for expressions like a ? b[3:0] : c[7:0] and similar.
             ;; ;;
             ;; ;; As a dumb way to restore these warnings, we now explicitly call
             ;; ;; vl-expr-selfsize here, even though we don't care what size it
             ;; ;; thinks things are.  We are just using it to generate warnings.
             ;; ;; See vl-expr-selfsize for details and note that it properly
             ;; ;; doesn't cause a warning if the arguments don't have self-sizes.
             ;; ((wvmv vttree ?ignored-size) (vl-expr-selfsize x ss scopes))

             (type-err (vl-type-error-qmark-combine x type-err1 type-err2)))
          (mv vttree type-err svex))

        :vl-call
        (b* (((when x.systemp)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "System call ~a0 supposed to return unpacked type ~a1"
                          :args (list x (vl-datatype-fix type)))
                  nil
                  (svex-x)))
             ((vmv vttree svex ftype)
              (vl-funcall-to-svex x ss scopes))
             ((unless ftype)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Couldn't find type for expression: ~a0"
                          :args (list x))
                  nil
                  svex))
             (type-err (vl-datatype-compatibility-type-error type ftype compattype)))
          (mv vttree type-err svex))

        :vl-cast
        (vl-casttype-case x.to
          :type (b* (((mv err to-type) (vl-datatype-usertype-resolve x.to.type ss :scopes scopes))
                     ((when err)
                      (mv (vfatal :type :vl-expr-to-svex-fail
                                  :msg "Usertypes not resolved in cast ~a0: ~@1"
                                  :args (list x err))
                          nil
                          (svex-x)))
                     ((vmv vttree type-err1 svex)
                      ;; We're casting to a new type so don't pass the lhs down.
                      (vl-expr-to-svex-datatyped x.expr nil to-type ss scopes
                                                 :compattype :cast
                                                 :explicit-cast-p t))
                     ((wvmv vttree) (vl-typecast-type-error-warn type-err1 x ss))
                     (type-err (vl-datatype-compatibility-type-error type to-type compattype)))
                  (mv vttree type-err svex))
          :const
          ;; Maybe we just ignore this?
          ;; No idea whether we should pass lhs down.  Or anything else.  Sigh.
          (vl-expr-to-svex-datatyped x.expr lhs type ss scopes :compattype compattype)
          :otherwise
          ;; This seems bogus, we have a non-packed type but we're casting to a
          ;; signedness or size.
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "~s0 cast in non-vector context: ~a1"
                      :args (list (if* (eq x.kind :signedness)
                                       "Signedness"
                                       "Size")
                                  x))
              nil
              (svex-x)))

        :vl-mintypmax
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Don't yet support mintypmax expressions: ~a0."
                    :args (list x))
            nil
            (svex-x))

        :vl-pattern
        (b* (((unless x.pattype)
              (vl-assignpat-to-svex x.pat type ss scopes x))
             ((mv err pattype)
              (vl-datatype-usertype-resolve x.pattype ss :scopes scopes))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Usertypes not resolved in pattern ~a0: ~@1"
                          :args (list x err))
                  nil
                  (svex-x)))
             ((vmv vttree type-err svex)
              (vl-assignpat-to-svex x.pat pattype ss scopes x))
             ((wvmv vttree) (vl-assignpat-cast-type-error-warn type-err x ss))
             (type-err (vl-datatype-compatibility-type-error type pattype compattype)))
          (mv vttree type-err svex))

        :vl-special
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Don't yet support ~a0."
                    :args (list x))
            nil
            (svex-x))

        :vl-stream
        (b* (((vmv vttree bitstream concat-size)
              (vl-streaming-concat-to-svex x ss scopes))
             ((unless (posp concat-size))
              (mv vttree nil (svex-x)))
             ((mv err target-size) (vl-datatype-size type))
             ((when (or err (not (posp target-size))))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Problem sizing datatype ~a0 for streaming concat ~a1: ~@2"
                          :args (list type x
                                      (or* err (if target-size "size zero" "unsizable"))))
                  nil
                  (svex-x)))
             (vttree (if (> concat-size target-size)
                         (vwarn :type :vl-streaming-concat-error
                                :msg "The streaming concatenation ~a0 is ~
                                       larger than its target type ~a1 -- ~
                                       SystemVerilog says this is an error."
                                :args (list x type))
                       vttree))
             (ans (vl-streaming-concat-trunc/extend bitstream target-size concat-size)))
          ;; In SystemVerilog, we'd now stick the bitstream into a container of the
          ;; appropriate datatype.  But in svex, everything's just kept as a
          ;; bitstream, so we're already done.
          (mv vttree nil ans))

        :vl-tagged
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Don't yet support ~a0."
                    :args (list x))
            nil
            (svex-x))


        :otherwise
        ;; :vl-value, :vl-unary, :vl-binary, :vl-concat, :vl-multiconcat, :vl-inside
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Vector expression ~a0 doesn't fit in unpacked type ~a1"
                    :args (list x (vl-datatype-fix type)))
            nil
            (svex-x)))))

  (define vl-streamexprlist-to-svex ((x vl-streamexprlist-p)
                                     (ss vl-scopestack-p)
                                     (scopes vl-elabscopes-p))
    :measure (two-nats-measure (vl-streamexprlist-count x) 0)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription))
    (b* ((vttree nil)
         ((when (atom x)) (mv vttree (svex-x) 0))
         ((vmv vttree svex1 size1) (vl-streamexpr-to-svex (car x) ss scopes))
         ((vmv vttree svex2 size2) (vl-streamexprlist-to-svex (cdr x) ss scopes))
         ((unless (and size1 size2))
          ;; already warned
          (mv vttree (svex-x) nil)))
      (mv vttree
          (sv::svex-concat size2 svex2 svex1)
          (+ size1 size2))))

  (define vl-streamexpr-to-svex ((x vl-streamexpr-p)
                                 (ss vl-scopestack-p)
                                 (scopes vl-elabscopes-p))
    :measure (two-nats-measure (vl-streamexpr-count x) 200)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription))
    (b* (((vl-streamexpr x))
         ((mv vttree svex ?type size)
          (vl-expr-to-svex-untyped x.expr ss scopes)))

      (vl-arrayrange-case x.part
        :none (mv vttree svex size) ;; already warned if size is nil
        :otherwise
        (mv (vfatal :type :vl-unsupported-expression
                    :msg "Streaming concatenations using the 'with' keyword ~
                         are unsupported: ~a0"
                    :args (list (vl-streamexpr-fix x)))
            (svex-x) nil))))
  #||

  (trace$ #!vl (vl-assignpat-to-svex
  :entry (list 'vl-assignpat-to-svex
  (with-local-ps (vl-pp-assignpat x))
  (with-local-ps (vl-pp-datatype type))
  (vl-scopestack->hashkey ss)
  (strip-cars scopes)
  (with-local-ps (vl-pp-expr orig-x)))
  ::exit (list 'vl-assignpat-to-svex
  (with-local-ps (vl-print-vttree (car values)))
  (cadr values))))

  ||#
  (define vl-assignpat-to-svex ((x vl-assignpat-p)
                                (type vl-datatype-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p)
                                (orig-x vl-expr-p))
    :guard (vl-datatype-resolved-p type)
    :measure (two-nats-measure (vl-assignpat-count x) 16)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type-err vl-maybe-type-error-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (vttree nil)
         (type (vl-maybe-usertype-resolve type))
         ;; Makes sure type is not just a bare usertype.  If the result is a
         ;; usertype, it at least has an array dimension.
         ((when (or (consp (vl-datatype->udims type))
                    (consp (vl-datatype->pdims type))))
          ;; Array.
          (b* (((mv ?err ?caveat slottype dim)
                (vl-datatype-remove-dim type))
               ;; Never an error because we have dims.
               ((unless (vl-dimension-case dim :range))
                (mv (vfatal :type :vl-expr-to-svex-fail
                            :msg "unsupported dimension in type of assignment pattern ~a0"
                            :args (list orig-x))
                    nil
                    (svex-x)))
               (range (vl-dimension->range dim))
               ((unless (vl-range-resolved-p range))
                (mv (vfatal :type :vl-expr-to-svex-fail
                            :msg "unresolved dimension in type of assignment pattern ~a0"
                            :args (list orig-x))
                    nil
                    (svex-x))))
            (vl-array-assignpat-to-svex x slottype range ss scopes orig-x))))
      (vl-datatype-case type
        :vl-struct
        (vl-struct-assignpat-to-svex x type.members ss scopes orig-x)
        :otherwise
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Bad type ~a0 for assignment pattern ~a1"
                    :args (list type orig-x))
            nil
            (svex-x)))))


  (define vl-array-assignpat-to-svex ((x vl-assignpat-p)
                                      (slottype vl-datatype-p)
                                      (range vl-range-p)
                                      (ss vl-scopestack-p)
                                      (scopes vl-elabscopes-p)
                                      (orig-x vl-expr-p))
    :guard (and (vl-range-resolved-p range)
                (vl-datatype-resolved-p slottype))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type-err vl-maybe-type-error-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (vttree nil)
         (slottype (vl-datatype-fix slottype))
         (subexprs (vl-assignpat-case x
                     :positional x.vals
                     :keyval (alist-vals x.pairs)
                     :repeat x.vals))
         ((mv err slotsize) (vl-datatype-size slottype))
         ((when (or err (not slotsize)))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Couldn't size assignpattern slot type ~a0 (expr: ~a1)"
                      :args (list slottype orig-x))
              nil
              (svex-x)))
         (arrsize (vl-range-size range))
         ((vl-range range))
         ((vmv vttree type-errs svex-subexprs)
          (vl-exprlist-to-svex-datatyped
           subexprs
           (repeat (len subexprs) slottype)
           ss scopes :compattype :assign))
         ((wvmv vttree) (vl-subexpr-type-error-list-warn orig-x type-errs ss)))
      (vl-assignpat-case x
        :positional
        (b* (((unless (eql (len subexprs) arrsize))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Wrong number of elements in positional assignment ~
                               pattern ~a0. (Range: [~a1, ~a2].)"
                          :args (list orig-x range.msb range.lsb))
                  ;; BOZO someday this could be a type error instead of a warning
                  nil
                  (svex-x))))
          (mv (vttree-fix vttree)
              nil
              (svex-concat-list (repeat (len subexprs) slotsize) svex-subexprs)))
        :repeat
        (b* (((unless (vl-expr-resolved-p x.reps))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Unresolved repetition count in assignment pattern: ~a0"
                          :args (list orig-x))
                  nil
                  (svex-x)))
             (reps (vl-resolved->val x.reps))
             ((unless (eql (* reps (len subexprs)) arrsize))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Wrong number of elements in positional assignment ~
                               pattern ~a0. (Range: [~a1, ~a2].)"
                          :args (list orig-x range.msb range.lsb))
                  ;; BOZO someday this could be a type error instead of a warning
                  nil
                  (svex-x))))
          (mv (vttree-fix vttree)
              nil
              (svex-multiconcat reps svex-subexprs (repeat (len subexprs) slotsize))))
        :keyval
        (b* ((err (vl-check-array-assignpat-keys x.pairs range))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Bad key in assignment pattern ~a0: ~@1"
                          :args (list orig-x err))
                  ;; BOZO someday this could be a type error instead of a warning
                  nil
                  (svex-x)))
             (svex-keyvals (pairlis$ (alist-keys x.pairs) svex-subexprs))
             ((mv err svex-slots)
              (vl-array-assignpat-keyval-resolve
               (vl-resolved->val range.lsb)
               (vl-resolved->val range.msb)
               svex-keyvals)))
          (mv (vl-err->vfatal err
                              :type :vl-expr-to-svex-fail
                              :msg "Bad key/val assignment pattern ~a0"
                              :args (list orig-x))
              nil
              (svex-concat-list (repeat arrsize slotsize) svex-slots))))))

  (define vl-struct-assignpat-keyval-resolve ((x vl-keyvallist-p)
                                              (membs vl-structmemberlist-p)
                                              (ss vl-scopestack-p)
                                              (scopes vl-elabscopes-p)
                                              (orig-x vl-expr-p))
    :guard (vl-structmemberlist-resolved-p membs)
    :measure (two-nats-measure (vl-keyvallist-count x)
                               (len membs))
    ;; BOZO only returning one of the errors...
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svex-membs
                  (and (sv::svexlist-p svex-membs)
                       (equal (len svex-membs) (len membs))
                       (sv::svarlist-addr-p (sv::svexlist-vars svex-membs)))
                  "Most-significant first"))
    :verify-guards nil
    (b* ((orig-x (vl-expr-fix orig-x))
         (vttree nil)
         ((when (atom membs)) (mv nil nil))
         ((vl-structmember m1) (car membs))
         (first (or (vl-keyval-member-lookup m1.name x)
                    (vl-keyval-default-lookup x)))
         ((vmv vttree rest)
          (vl-struct-assignpat-keyval-resolve
           x (cdr membs) ss scopes orig-x)))
      (if first
          (b* (((vmv vttree type-err first-sv)
                (vl-expr-to-svex-datatyped
                 first nil m1.type ss scopes :compattype :assign))
               ((wvmv vttree) (vl-struct-assignpat-keyval-type-err-warn orig-x m1 first type-err ss)))
            (mv vttree (cons first-sv rest)))
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "No entry for struct member ~s1 in ~
                                  assignment pattern ~a1"
                    :args (list m1.name orig-x))
            (cons (svex-x) rest)))))

  (define vl-struct-assignpat-to-svex ((x vl-assignpat-p)
                                       (membs vl-structmemberlist-p)
                                       (ss vl-scopestack-p)
                                       (scopes vl-elabscopes-p)
                                       (orig-x vl-expr-p))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :guard (vl-structmemberlist-resolved-p membs)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type-err vl-maybe-type-error-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (vttree nil)
         ((mv err widths) (vl-structmemberlist-sizes membs))
         ((when (or err (member nil widths)))
          (mv (vfatal :type :vl-expr-to-svex-fail
                      :msg "Couldn't size struct members for assignment ~
                           pattern ~a0"
                      :args (list orig-x))
              nil
              (svex-x))))
      (vl-assignpat-case x
        :positional
        (b* (((unless (eql (len x.vals) (len membs)))
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Wrong number of entries in positional ~
                               assignment pattern ~a0"
                          :args (list orig-x))
                  ;; BOZO someday this could be a type error instead of a warning
                  nil
                  (svex-x)))
             (types (vl-structmemberlist->types membs))
             ((vmv vttree type-errs svex-vals)
              (vl-exprlist-to-svex-datatyped x.vals types ss scopes :compattype :assign))
             ((wvmv vttree) (vl-subexpr-type-error-list-warn orig-x type-errs ss)))
          (mv (vttree-fix vttree)
              nil
              (svex-concat-list widths svex-vals)))
        :repeat
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Repetitions not supported for struct-typed ~
                         assignment patterns: ~a0"
                    :args (list orig-x))
            nil
            (svex-x))
        :keyval
        (b* ((err (vl-check-struct-assignpat-keys x.pairs membs))
             ((when err)
              (mv (vfatal :type :vl-expr-to-svex-fail
                          :msg "Bad key in assignment pattern ~a0: ~@1"
                          :args (list orig-x err))
                  ;; BOZO someday this could be a type error instead of a warning
                  nil
                  (svex-x)))
             ((vmv vttree svex-membs)
              (vl-struct-assignpat-keyval-resolve
               x.pairs membs ss scopes orig-x)))
          (mv vttree
              nil
              (svex-concat-list widths svex-membs))))))

  (define vl-exprlist-to-svex-datatyped ((x vl-exprlist-p)
                                         (types vl-datatypelist-p)
                                         (ss vl-scopestack-p)
                                         (scopes vl-elabscopes-p)
                                         &key ((compattype vl-typecompat-p) ':equiv))
    :guard (and (equal (len types) (len x))
                (vl-datatypelist-resolved-p types))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (type-errs vl-subexpr-type-error-list-p)
                 (svexes
                  (and (sv::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (sv::svarlist-addr-p (sv::svexlist-vars svexes)))))
    (b* ((vttree nil)
         ((when (atom x)) (mv (vttree-fix vttree) nil nil))
         ((vmv vttree type-err1 first)
          (vl-expr-to-svex-datatyped
           (car x) nil (car types) ss scopes :compattype compattype))
         ((vmv vttree type-errs2 rest)
          (vl-exprlist-to-svex-datatyped
           (cdr x) (cdr types) ss scopes :compattype compattype))
         (type-errs (vl-subexpr-type-error-list-combine (car x) (car types) type-err1 type-errs2)))
      (mv vttree type-errs (cons first rest))))

  (define vl-exprlist-to-svex-selfdet ((x vl-exprlist-p)
                                       (ss vl-scopestack-p)
                                       (scopes vl-elabscopes-p))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (svexes
                  (and (sv::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (sv::svarlist-addr-p (sv::svexlist-vars svexes))))
                 (sizes
                  (and (maybe-nat-list-p sizes)
                       (equal (len sizes) (len x))
                       (true-listp sizes))))
    (b* ((vttree nil)
         ((when (atom x)) (mv (vttree-fix vttree) nil nil))
         ((vmv vttree first size1)
          (vl-expr-to-svex-selfdet
           (car x) nil ss scopes))
         ((vmv vttree rest rest-sizes)
          (vl-exprlist-to-svex-selfdet
           (cdr x) ss scopes)))
      (mv vttree (cons first rest)
          (cons size1 rest-sizes))))
  ///

  (local
   (make-event
    `(in-theory (disable . ,(flag::get-clique-members 'vl-expr-to-svex-vector (w state))))))

  (with-output :off (event)
    (verify-guards vl-expr-to-svex-selfdet
      :hints (("goal" :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((vl-datatypelist-resolved-p types)
                              (vl-structmemberlist-resolved-p membs)
                              (vl-expr-opacity x))
                     :in-theory (enable acl2::natp-when-maybe-natp))))
      :guard-debug t))

  (local (in-theory (disable len)))

  (deffixequiv-mutual vl-expr-to-svex
    :hints ((acl2::just-expand-mrec-default-hint 'vl-expr-to-svex-selfdet id t world)
            '(:do-not-induct t))))

;; (set-default-hints
;;  '((and (equal (acl2::parse-clause-id "Subgoal *1/30.53'''") id)
;;         '(:in-theory nil))))


#||
(include-book
 "svex-rewrite")
(define test-partselect ((decl-msb natp)
                         (decl-lsb natp)
                         (sel-msb natp)
                         (sel-lsb natp)
                         &key
                         (unitsz maybe-natp))
  :prepwork ((local (in-theory (enable vl-maybe-range-resolved-p
                                       vl-range-resolved-p))))
  :verify-guards nil
  :hooks nil
  (b* ((range (vl-range (vl-make-index decl-msb)
                        (vl-make-index decl-lsb)))
       (rest-range (if unitsz
                       (list (vl-range (vl-make-index (1- unitsz))
                                       (vl-make-index 0)))
                     nil))
       (decl (make-vl-vardecl :name "a"
                              :type (make-vl-coretype :name :vl-logic
                                                      :pdims (cons range rest-range))
                              :nettype :vl-wire
                              :loc *vl-fakeloc*))
       (mod (make-vl-module :name "foo" :origname "foo"
                            :vardecls (list decl)
                            :minloc *vl-fakeloc*
                            :maxloc *vl-fakeloc*))
       (ss (vl-scopestack-push mod (vl-scopestack-init (make-vl-design))))
       (expr (vl-idexpr "a"))
       (sel-expr (change-vl-index expr
                                  :part (vl-range->partselect
                                         (make-vl-range :msb (vl-make-index sel-msb)
                                                        :lsb (vl-make-index sel-lsb)))))
       ((wmv warnings svex size)
        (vl-expr-to-svex-selfdet sel-expr nil ss nil 'test-partselect nil)))
    (mv warnings
        (car (sv::svexlist-rewrite-fixpoint (list svex)))
        size)))

(test-partselect 3 7 5 9 :unitsz 5)
 logic [3:7] [4:0] a  = a[3][4:0] a[4][4:0] a[5][4:0] a[6][4:0] a[7][4:0]
    a[5:9] -->  a[5][4:0] a[6][4:0] a[7][4:0] x[4:0] x[4:0]
(test-partselect 3 7 1 5 :unitsz 5)
(test-partselect 3 7 4 7)
(test-partselect 3 7 4 6)
(test-partselect 3 7 2 9)
(test-partselect 3 7 2 7)
(test-partselect 3 7 2 6)

(test-partselect 7 3 9 5)
(test-partselect 7 3 7 4)
(test-partselect 7 3 6 4)
(test-partselect 7 3 9 2)
(test-partselect 7 3 7 2)
(test-partselect 7 3 6 2)
||#


#||

(trace$ #!vl (vl-expr-to-svex-lhs
              :entry (list 'vl-expr-to-svex-lhs
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'vl-expr-to-svex-lhs (cadr values))))

(trace$ #!vl (vl-expr-to-svex-untyped
              :entry (list 'vl-expr-to-svex-untyped
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'vl-expr-to-svex-untyped (cadr values) (cadddr values))))

||#

(define vl-expr-to-svex-lhs ((x vl-expr-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p))
  :returns (mv (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (svex (and (sv::lhs-p svex)
                          (sv::svarlist-addr-p (sv::lhs-vars svex))))
               (type (and (vl-maybe-datatype-p type)
                          (implies type
                                   (vl-datatype-resolved-p type)))))
  (b* ((vttree nil)
       ((mv vttree svex type)
        (vl-expr-case x
          :vl-index (vl-index-expr-to-svex x ss scopes)
          :vl-concat (b* (((vmv vttree svex size)
                           (vl-expr-to-svex-selfdet x nil ss scopes))
                          ((unless (posp size))
                           (mv vttree svex nil)))
                       (mv vttree svex
                           (vl-size-to-unsigned-logic size)))
          :vl-stream (b* (((vmv vttree svex size)
                           (vl-streaming-concat-to-svex x ss scopes))
                          ((unless (posp size))
                           (mv (vfatal :type :vl-expr-to-svex-fail
                                       :msg "Bad LHS: zero-size streaming concat"
                                       :args (list (vl-expr-fix x)))
                               (svex-x) nil)))
                       (mv vttree svex (vl-size-to-unsigned-logic size)))
          :otherwise (mv (vfatal :type :vl-expr-to-svex-fail
                                 :msg "Bad LHS expression: ~a0"
                                 :args (list (vl-expr-fix x)))
                         (svex-x) nil)))
       ((unless type)
        (mv vttree nil type))
       ((mv err size) (vl-datatype-size type))
       ((when (or err (not size)))
        ;; (break$)
        (mv (vfatal :type :vl-expr-to-svex-fail
                    :msg "Couldn't size the datatype ~a0 of ~
                                    LHS expression ~a1: ~@2"
                    :args (list type (vl-expr-fix x) (or err (vmsg "unsizeable"))))
            nil nil))
       (lhssvex (sv::svex-lhsrewrite svex size))
       ((unless (sv::lhssvex-bounded-p size lhssvex))
        (mv (vfatal :type :vl-expr->svex-lhs-fail
                    :msg "Not a supported LHS expression: ~a0"
                    :args (list (vl-expr-fix x)))
            nil nil)))
    (mv vttree (sv::svex->lhs-bound size lhssvex) type))
  ///
  (defret vl-expr-to-svex-lhs-type-size-ok
    (implies type
             (not (mv-nth 0 (vl-datatype-size type))))
    :hints(("Goal" :in-theory (enable vl-datatype-size)))))





(define vl-expr-to-svex-maybe-typed ((x vl-expr-p)
                                     (type vl-maybe-datatype-p)
                                     (ss vl-scopestack-p)
                                     (scopes vl-elabscopes-p)
                                     &key ((compattype vl-typecompat-p) ':equiv))
  :short "Convert an expression to svex, maybe given a datatype that it needs to match."
  :guard (or (not type) (vl-datatype-resolved-p type))
  :guard-debug t
  :guard-hints (("goal" :in-theory (enable vl-maybe-datatype-p)))
  :returns (mv (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (svex (and (sv::svex-p svex)
                          (sv::svarlist-addr-p (sv::svex-vars svex))))
               (res-type (and (vl-maybe-datatype-p res-type)
                              (and (implies res-type
                                            (vl-datatype-resolved-p res-type)))))
               (res-size maybe-natp :rule-classes :type-prescription)
               (type-err vl-maybe-type-error-p))
  (b* ((type (vl-maybe-datatype-fix type)))
    (if type
        (b* (((mv vttree type-err svex) (vl-expr-to-svex-datatyped x nil type ss scopes :compattype compattype))
             ((mv err size) (vl-datatype-size type))
             ((when (or err (not size)))
              (mv (vwarn :type :vl-expr-to-svex-fail
                         :msg "Datatype ~a0 for expression ~a1 couldn't be sized: ~@0"
                         :args (list type (vl-expr-fix x)
                                     (or err "unsizable")))
                  svex
                  (and (mbt (vl-datatype-resolved-p type)) type)
                  nil type-err)))
          (mv vttree svex
              (and (mbt (vl-datatype-resolved-p type)) type)
              size type-err))
      (b* (((mv vttree svex res-type res-size)
            (vl-expr-to-svex-untyped x ss scopes)))
        (mv vttree svex res-type res-size nil)))))








(define vl-expr-needs-type-context ((x vl-expr-p))
  :measure (vl-expr-count x)
  (vl-expr-case x
    :vl-qmark (or (vl-expr-needs-type-context x.then)
                  (vl-expr-needs-type-context x.else))
    :vl-pattern t
    :vl-stream t
    :otherwise nil))
