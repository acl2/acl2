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
(include-book "../svex/rewrite-base")
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/mlib/selfsize" :dir :system)
(include-book "centaur/vl/mlib/typedecide" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(defxdoc vl-expr-svex-translation
  :parents (vl-design->svex-design)
  :short "Compilation from (sized) @(see vl::vl) expressions into @(see
sv::svex) expressions."

  :long "<p>The top-level function for converting a VL expression into a @(see
sv::svex) expression is @(see vl-expr->svex).</p>

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


(fty::defalist vl-svexalist :key-type vl-scopeexpr :val-type sv::svex-p)

(fty::defalist vl-fnportalist :key-type vl-scopeexpr :val-type vl-portdecllist)


(defprod vl-svexconf
  :short "Static configuration object for expr to svex conversion."
  ((ss vl-scopestack-p
       "The scopestack at the source location of the expression.")
   (typeov vl-typeoverride-p "Scopeexprs mapped to resolved types")
   (fns    vl-svexalist-p "Function definition table")
   (fnports vl-fnportalist-p "Function portlist table")
   (params vl-svexalist-p "Parameter definition table")))

(define vl-svexconf-free ((x vl-svexconf-p))
  (b* (((vl-svexconf x)))
    (progn$ (fast-alist-free x.typeov)
            (fast-alist-free x.fns)
            (fast-alist-free x.params))))


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
  :parents (vl-expr-to-svex)
  :short "Turn a vl-bitlist into a 4vec.  Assumes msb-first ordering, such as in a vl-weirdint."
  :returns (val sv::4vec-p)
  (let ((lsb-bits (rev (vl-bitlist-fix msb-bits))))
    (sv::4vec (vl-bitlist->onset lsb-bits)
                (lognot (vl-bitlist->offset lsb-bits)))))

(define svex-int ((x integerp))
  :short "convenient abbreviation"
  :returns (sv sv::svex-p)
  (sv::svex-quote (sv::2vec x))
  ///
  (defthm svex-eval-of-svex-int
    (equal (sv::svex-eval (svex-int x) env)
           (sv::2vec x)))

  (defthm vars-of-svex-int
    (equal (sv::svex-vars (svex-int x)) nil)))

(define svex-extend ((type vl-exprsign-p)
                     (width natp)
                     (x sv::svex-p))
  :parents (vl-expr->svex)
  :short "Returns an svex representing the sign- or zero-extension of x at the given width."

  :long "<p>We don't have to extend/truncate operands when translating VL
expressions like @('a & b'), but we do need to do it to the inputs of
expressions like @('a < b'), to chop off any garbage in the upper bits.</p>"

  :returns (sv sv::svex-p)
  (b* ((extend (if (eq (vl-exprsign-fix type) :vl-signed) 'sv::signx 'sv::zerox))
       (width (lnfix width))
       ((when (eq (sv::svex-kind x) :quote))
        (sv::svex-quote
         (if (eq (vl-exprsign-fix type) :vl-signed)
             (sv::4vec-sign-ext (sv::2vec width) (sv::svex-quote->val x))
           (sv::4vec-zero-ext (sv::2vec width) (sv::svex-quote->val x))))))
    (sv::make-svex-call :fn extend :args (list (svex-int width) x)))
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

  (memoize 'svex-variable-free-p :condition '(svex-case x :call)))


#!sv
(defines svex-reduce-consts
  :verify-guards nil
  (define svex-reduce-consts ((x svex-p))
    :returns (new-x svex-p)
    :measure (svex-count x)
    (svex-case x
      :call (b* ((args (svexlist-reduce-consts x.args))
                 ((when (svexlist-variable-free-p args))
                  (svex-quote (svex-apply x.fn (svexlist-eval args nil))))
                 (args-eval (svexlist-xeval args))
                 (res (svex-apply
                       (case x.fn
                         (=== '==)
                         (==? 'safer-==?)
                         (otherwise x.fn))
                       args-eval)))
              (if (4vec-xfree-p res)
                  (svex-quote res)
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


  (defthm-svex-reduce-consts-flag
    (defthm svex-reduce-consts-correct
      (equal (svex-eval (svex-reduce-consts x) env)
             (svex-eval x env))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable svex-eval-when-4vec-xfree-of-minval-apply
                                        svex-eval-when-4vec-xfree-of-minval-apply-===
                                        svex-eval-when-4vec-xfree-of-minval-apply-==?
                                        eval-when-svexlist-variable-free-p))))
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
                                    (ss vl-scopestack-p "scopestack we're traversing"))
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
              ;; These are the two expected cases.  Genblocks are one-to-one
              ;; with svex module nestings.  Genarrayblocks have an additional
              ;; nesting level in svex-world: one level for the whole array,
              ;; one level for the individual blocks.
              (:vl-genblock (mv nil 1))
              (:vl-genarrayblock (mv nil 1))
              (:vl-fundecl         (mv nil 1))
              (:vl-anonymous-scope (mv nil 1))
              ;; Perhaps someday we'll need to add something about
              ;; statememts/functions/tasks here, but for the moment all that
              ;; is taken care of elsewhere (and complicated scoping stuff
              ;; isn't allowed in those contexts).
              (otherwise
               (mv (vmsg "Tried to go ~x0 level~s1 up through a scope of type ~x2"
                         vl-levels (if (eql vl-levels 1) "" "s") type)
                   nil))))
           ((when err) (mv err nil))
           ((mv err rest) (vl-upscope-to-svex-upscope (1- vl-levels) ss.super))
           ((when err) (mv err nil)))
        (mv nil (+ incr rest)))))
  ///
  (verify-guards vl-upscope-to-svex-upscope))


(define vl-scopecontext-to-addr ((x vl-scopecontext-p)
                                 (ss vl-scopestack-p)
                                 (path sv::path-p))
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
levels up only includes these nested block scopes.  We also need to compensate
for a peculiarity: in VL, only one level of scopestack is used for a generate
array, but in svex there's a scope nested around all of the entries in the
array as well.  Vl-upscope-to-svex-upscope accounts for these issues.</p>

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
                 (vl-upscope-to-svex-upscope x.levels ss))
                ((when err) (mv err nil)))
             (mv nil
                 (sv::make-address
                  :path path
                  :scope levels)))
    :root  (mv nil
               (sv::make-address :path path :scope :root))
    :package (mv (vmsg "Package-scoped variables aren't yet supported")
                 (sv::make-address :scope :root
                                     :path (sv::make-path-scope
                                            :namespace (vl-package->name x.pkg)
                                            :subpath path)))
    :module (mv (vmsg "Module-scoped variables aren't yet supported")
                (sv::make-address :scope :root
                                    :path (sv::make-path-scope
                                           :namespace (vl-module->name x.mod)
                                           :subpath path)))
    :interface (mv (vmsg "Module-scoped variables aren't yet supported")
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

(define vl-seltrace-to-svar ((x vl-seltrace-p)
                             (opinfo vl-operandinfo-p)
                             (outer-ss vl-scopestack-p))
  :short "Takes a fully resolved seltrace and the operandinfo of which it is a
          part and returns an svar variable created from its address."
  :guard (and (vl-operandinfo-usertypes-ok opinfo)
              (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo))
              (equal (vl-seltrace-unres-count x) 0))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svar (implies (not err) (sv::svar-p svar))))
  (b* (((vl-operandinfo opinfo))
       (path1 (vl-seltrace-to-path x nil))
       (path (vl-hidtrace-to-path opinfo.hidtrace path1))
       ((mv err addr)
        (vl-scopecontext-to-addr opinfo.context outer-ss path))
       ((when err) (mv err nil)))
    (mv nil (sv::make-svar :name addr)))
  ///
  (defret vars-of-vl-seltrace-to-svar
    (implies (not err)
             (sv::svar-addr-p svar))
    :hints(("Goal" :in-theory (enable sv::svar-addr-p)))))

(define vl-seltrace-to-svex-var ((x vl-seltrace-p)
                                 (opinfo vl-operandinfo-p)
                                 (outer-ss vl-scopestack-p))
  :short "Takes a fully resolved seltrace and the operandinfo of which it is a
          part and returns an svex variable created from its address."
  :guard (and (vl-operandinfo-usertypes-ok opinfo)
              (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo))
              (equal (vl-seltrace-unres-count x) 0))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (b* (((mv err svar) (vl-seltrace-to-svar x opinfo outer-ss))
       ((when err) (mv err (svex-x))))
    (mv nil (sv::make-svex-var :name svar)))
  ///
  (defret vars-of-vl-seltrace-to-svex-var
    (sv::svarlist-addr-p (sv::svex-vars svex))))

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
                           (with-local-ps (vl-pp-packeddimensionlist
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
                           (with-local-ps (vl-pp-packeddimensionlist
                                           (vl-datatype->udims x)))
                           idx)
              :exit (list 'vl-datatype-index-shift-amount
                          (car values)
                          (cadr values))))

|#

(define vl-datatype-index-shift-amount ((x vl-datatype-p)
                                        (idx sv::svex-p))
  :guard (vl-datatype-resolved-p x)
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (sv::svex-p shift))))
  (b* ((x (vl-maybe-usertype-resolve x))
       ((mv err ?caveat slottype dim) (vl-datatype-remove-dim x))
       ((when err) (mv err nil))
       ((mv err size) (vl-datatype-size slottype))
       ((when err) (mv err nil))
       ((unless size) (mv (vmsg "Couldn't size array slot type ~a0" slottype) nil))
       ((when (vl-packeddimension-case dim :unsized))
        (mv (vmsg "unsized packed dimension on array type ~a0" x) nil))
       ((vl-range range) (vl-packeddimension->range dim))
       ((unless (vl-range-resolved-p range))
        (mv (vmsg "unresolved packed dimension on array type ~a0" x) nil))
       (msb (vl-resolved->val range.msb))
       (lsb (vl-resolved->val range.lsb))
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
        (mv nil (sv::svex-reduce-consts
                 (sv::svcall * (svex-int size)
                               (sv::svcall sv::b- idx (svex-int lsb)))))))
    (mv nil (sv::svex-reduce-consts
             (sv::svcall * (svex-int size)
                           (sv::svcall sv::b- (svex-int lsb) idx)))))
  ///
  (defret vars-of-vl-datatype-index-shift-amount
    (implies (and (not err)
                  (not (member v (sv::svex-vars idx))))
             (not (member v (sv::svex-vars shift))))))


#!sv
(define 4vec-lsb-shift ((shift-amt 4vec-p)
                        (x 4vec-p))
  :returns (res 4vec-p)
  (if (2vec-p shift-amt)
      (b* ((sh (2vec->val shift-amt)))
        (if (< sh 0)
            (4vec-concat (2vec (- sh)) (4vec-x) x)
          (4vec-rsh (2vec sh) x)))
    (4vec-x)))

#!sv
(define svex-lsb-shift ((shift-amt svex-p)
                        (x svex-p))
  :short "Adjust an expression for the LSB end of a select."
  :long "<p>When computing the svex for an array access like @('v[i]'),
typically you wanto to right-shift @('v') by some number of bits, depending on
@('i') and the declared range of @('v').  But if @('i') is out of the bounds of
that declared range, you instead want to return @('X').  More generally, if you
have a ranged select like @('v[u:i]'), then if @('i') is out of bounds on the
LSB side of the declared range, you want to concatenate some number of @('X')
bits onto @('v').  This computes that shifted/concatenated version of @('v'),
if the shift amount is computed elsewhere.</p>"

  :returns (res svex-p)
  (b* ((sh (svex-reduce-consts shift-amt)))
    (svex-case sh
      :quote (if (2vec-p sh.val)
                 (if (<= 0 (2vec->val sh.val))
                     (svex-rsh (2vec->val sh.val) x)
                   (svex-concat (- (2vec->val sh.val)) (svex-x) x))
               (svex-x))
      :otherwise ;; (b* ((concat-amt (svcall ?
                 ;;                                (svcall < sh (vl::svex-int 0))
                 ;;                                (svcall u- sh)
                 ;;                                (vl::svex-int 0)))
                 ;;      (rsh-amt    (svcall ?
                 ;;                                (svcall < sh (vl::svex-int 0))
                 ;;                                (vl::svex-int 0)
                 ;;                                sh)))
                 ;;   (svcall concat
                 ;;           concat-amt
                 ;;           (svex-x)
                 ;;           (svcall rsh rsh-amt x)))
      (svcall ?
              (svcall < sh (vl::svex-int 0))
              ;; if the shift is negative, we're concatenating Xes, otherwise
              ;; we're right-shifting.
              (svcall concat (svcall u- sh) (svex-x) x)
              (svcall rsh sh x))))
  ///
  (local (defthm 4vec-<-of-non-2vec
           (implies (not (2vec-p x))
                    (equal (4vec-< x y) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-<)))))

  (local (defthm 4vec-uminus-of-non-2vec
           (implies (not (2vec-p x))
                    (equal (4vec-uminus x) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-uminus)))))

  (local (defthm 4vec-concat-of-non-2vec
           (implies (not (2vec-p x))
                    (equal (4vec-concat x y z) (4vec-x)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (local (in-theory (disable 4vec->lower-when-2vec-p)))


  (local (defthm svex-quote->val-of-reduce-consts
           (implies (equal (svex-kind (svex-reduce-consts x)) :quote)
                    (equal (svex-eval x env)
                           (svex-quote->val (svex-reduce-consts x))))
           :hints (("goal" :use ((:instance svex-reduce-consts-correct))
                    :in-theory (e/d (svex-eval-when-quote)
                                    (svex-reduce-consts-correct))))))

  (defthm svex-lsb-shift-correct
    (equal (svex-eval (svex-lsb-shift shift-amt x) env)
           (4vec-lsb-shift (svex-eval shift-amt env)
                           (svex-eval x env)))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4vec-lsb-shift)
            :rw-cache-state nil)
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-< 4vec-? 3vec-? 4vec-uminus)))))

  (defthm vars-of-svex-lsb-shift
    (implies (and (not (member v (svex-vars shift-amt)))
                  (not (member v (svex-vars x))))
             (not (member v (svex-vars (svex-lsb-shift shift-amt x)))))))

(define vl-seltrace-split ((x vl-seltrace-p)
                           (unres-count (equal (vl-seltrace-unres-count x)
                                               unres-count)))
  :short "Splits a seltrace at the point where all remaining indices are resolved."
  :prepwork ((local (in-theory (enable vl-seltrace-unres-count))))
  :returns (mv (unres vl-seltrace-p)
               (res vl-seltrace-p))
  :measure (len x)
  (if (mbe :logic (equal (vl-seltrace-unres-count x) 0)
           :exec (zp unres-count))
      (mv nil (vl-seltrace-fix x))
    (b* (((mv unres res) (vl-seltrace-split (cdr x)
                                            (if (vl-selstep-resolved-p (car x))
                                                unres-count
                                              (1- unres-count)))))
      (mv (cons (vl-selstep-fix (car x)) unres) res)))
  ///
  (defret vl-seltrace-usertypes-ok-of-vl-seltrace-split
    (implies (vl-seltrace-usertypes-ok x)
             (and (vl-seltrace-usertypes-ok unres)
                  (vl-seltrace-usertypes-ok res)))
    :hints(("Goal" :in-theory (enable vl-seltrace-usertypes-ok))))

  (defret vl-seltrace-index-count-of-vl-seltrace-split
    (<= (vl-seltrace-index-count unres)
        (vl-seltrace-index-count x))
    :hints(("Goal" :in-theory (enable vl-seltrace-index-count)))
    :rule-classes :linear)

  (defret vl-seltrace-unres-count-of-vl-seltrace-split
    (and (equal (vl-seltrace-unres-count unres)
                (vl-seltrace-unres-count x))
         (equal (vl-seltrace-unres-count res) 0))
    :rule-classes :linear)

  (defret len-of-vl-seltrace-split-parts
    (= (+ (len unres) (len res)) (len x))
    :rule-classes (:rewrite :linear))

  (defret vl-seltrace-index-count-of-vl-seltrace-split-parts
    (= (+ (vl-seltrace-index-count unres) (vl-seltrace-index-count res))
       (vl-seltrace-index-count x))
    :hints(("Goal" :in-theory (enable vl-seltrace-index-count)))
    :rule-classes (:rewrite :linear)))


(define vl-seltrace-to-svex-vector
  ((x vl-seltrace-p)
   (indices sv::svexlist-p)
   (base-type vl-datatype-p "The type of the variable that the selects are indexing into.")
   (base-svex sv::svex-p)
   (outer-ss vl-scopestack-p))
  :guard (and (vl-seltrace-usertypes-ok x)
              (vl-datatype-resolved-p base-type)
              (>= (len indices)
                  (vl-seltrace-index-count x))
              ;; (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo))
              )
  :verify-guards nil
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
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
       ((when err) (mv err (svex-x)))
       ((unless size) (mv (vmsg "Could not size datatype ~s0" type) (svex-x)))

       ((when (atom x))
        (mv nil (sv::svcall sv::concat (svex-int size) base-svex (svex-x))))


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
       ((when err) (mv err (svex-x)))

       ((mv err rest) (vl-seltrace-to-svex-vector
                       (cdr x)
                       (vl-select-case step.select
                         :field indices
                         :index (cdr indices))
                       base-type
                       base-svex
                       outer-ss))
       ((when err) (mv err (svex-x))))
    (mv err (sv::svcall sv::concat (svex-int size)
                          (sv::svex-lsb-shift shift-amt rest)
                          (svex-x))))
  ///
  (local (in-theory (disable (:d vl-seltrace-to-svex-vector))))

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

  (verify-guards vl-seltrace-to-svex-vector
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable vl-seltrace-usertypes-ok
                                      vl-seltrace-unres-count
                                      vl-seltrace-index-count
                                      vl-select-resolved-p)))))

  (defret vars-of-vl-seltrace-to-svex-vector
    (implies (and (not (member v (sv::svexlist-vars indices)))
                  (not (member v (sv::svex-vars base-svex))))
             (not (member v (sv::svex-vars svex))))
    :hints(("Goal" :in-theory (enable vl-seltrace-to-svex-vector)))))


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
      (b* (((unless (vl-expr-resolved-p x.part.width))
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
             (not (member v (sv::svexlist-vars new-indices))))))


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

(define vl-plusminus-partselect->svex ((x sv::svex-p "expr to apply the partselect to")
                                       (type vl-datatype-p "type of base expr")
                                       (psel vl-plusminus-p)
                                       (base-svex sv::svex-p "base index")
                                       (width-svex sv::svex-p "width index"))
  :short "This ONLY shifts the base expression to the right point for the partselect;
          it does not truncate it at the right width."
  :guard (vl-datatype-resolved-p type)
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex sv::svex-p))
  (b* (((vl-plusminus psel))
       ((mv err ?caveat ?basetype dim) (vl-datatype-remove-dim type))
       ((when err) (mv err (svex-x)))
       ((when (vl-packeddimension-case dim :unsized))
        (mv (vmsg "Unsized dimension") (svex-x)))
       ((vl-range dimrange) (vl-packeddimension->range dim))
       ((unless (vl-range-resolved-p dimrange))
        (mv (vmsg "Unresolved dimension") (svex-x)))
       (dim-msb (vl-resolved->val dimrange.msb))
       (dim-lsb (vl-resolved->val dimrange.lsb))
       (downp (<= dim-lsb dim-msb))
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
       ((mv err shift-amt)
        (vl-datatype-index-shift-amount type sel-lsb))
       ((when err) (mv err (svex-x))))
    (mv nil (sv::svex-lsb-shift shift-amt x)))

  ///
  (defret vars-of-vl-plusminus-partselect->svex
    (implies (and (not (member v (sv::svex-vars x)))
                  (not (member v (sv::svex-vars base-svex)))
                  (not (member v (sv::svex-vars width-svex))))
             (not (member v (sv::svex-vars svex))))))


(defconst *svex-longest-static-prefix-var*
  :svex-longest-static-prefix)

(local (include-book "std/lists/nthcdr" :dir :system))
;; (local (include-book "std/lists/take" :dir :system))

(local #!sv (std::deflist svexlist-p (x)
              (svex-p x)
              :true-listp t))

(define vl-operandinfo-to-svex-longest-static-prefix
  ((x vl-operandinfo-p)
   (indices sv::svexlist-p)
   (ss vl-scopestack-p)
   (params vl-svexalist-p))



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
                                        acl2::take-redefinition
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
               (lsp-expr sv::svex-p)
               (lsp-type
                (implies (not err)
                         (and (vl-datatype-p lsp-type)
                              (implies (vl-operandinfo-usertypes-ok x)
                                       (vl-datatype-resolved-p lsp-type)))))
               (full-expr sv::svex-p)) ;; in terms of lsp-var
  (b* (((fun (fail err)) (mv err (svex-x) nil (svex-x)))
       ((mv err x indices) (vl-operandinfo-to-svex-preproc x indices))
       (indices (list-fix indices))
       ((when err) (fail err))
       ((vl-operandinfo x))

       ((unless (vl-hidtrace-resolved-p x.hidtrace))
        (fail (vmsg "Unresolved hid indices")))
       ((vl-hidstep decl) (car x.hidtrace))

       ((mv err base-svex)
        (if (eq (tag decl.item) :vl-vardecl)
            (b* (;; ((mv unres-sels res-sels)
                 ;;  (vl-seltrace-split x.seltrace
                 ;;                     (vl-seltrace-unres-count x.seltrace)))
                 ;; If we have a bunch of resolved selects, we can encode them
                 ;; as either an explicit select (right shift + concat) or as a
                 ;; name, where eventually this will be resolved to a shift by
                 ;; alias resolution.  Let's go with the former for now since
                 ;; the latter won't work for elaboration, where we don't yet
                 ;; have a complete module hierarchy.
                 ((mv err base-var)
                  ;; Note we're passing NIL as the seltrace here, so it's
                  ;; really only making a variable of the part corresponding to
                  ;; the vardecl (hid), with no selects.
                  (vl-seltrace-to-svex-var nil x ss)))
              (mv err base-var))
          (b* ((look (cdr (hons-get x.prefixname (vl-svexalist-fix params))))
               ((unless look)
                ;; (cw "var: ~x0 look: ~x1 alist: ~x2~%" var look params);; (break$)
                (mv (vmsg "Parameter definition not found") nil))
               ((unless (sv::svex-addr-p look))
                (mv (vmsg "Parameter expression malformed") nil)))
            (mv nil look))))
       ((when err) (fail err))

       (unres-count (vl-seltrace-unres-count x.seltrace))
       ((mv unres-sels res-sels)
        ;; Note: It might be better (?) to determine which selects are resolved
        ;; based on their svexes.  This wouldn't work, e.g., if we didn't
        ;; replace constant indices by their values during elaboration: test this!
        ;; E.g.,
        ;;  parameter foo = 5;
        ;; always_comb
        ;;     bar[foo+1][idx] = a;
        ;; always_comb
        ;;     bar[foo+2][idx] = b;
        ;; If this works, then bar[foo+1] and bar[foo+2] are the two longest
        ;; static prefixes and these two blocks won't interfere with each
        ;; other.
        (vl-seltrace-split x.seltrace unres-count))

       ;; longest static prefix
       (partsel-p (not (vl-partselect-case x.part :none)))
       (seltrace-indices (if partsel-p
                             (cddr indices)
                           indices))
       (nonstatic-count (vl-seltrace-index-count unres-sels))
       (nonstatic-indices (take nonstatic-count seltrace-indices))
       (static-indices (nthcdr nonstatic-count seltrace-indices))

       ((mv err lsp-sel-expr)
        (vl-seltrace-to-svex-vector res-sels static-indices x.hidtype base-svex ss))
       ((when err) (fail err))
       (lsp-sel-type (vl-seltrace-type res-sels x.hidtype))

       ((mv err sel-nonstatic)
        (vl-seltrace-to-svex-vector unres-sels nonstatic-indices lsp-sel-type
                                    (sv::make-svex-var :name *svex-longest-static-prefix-var*)
                                    ss))
       ((when err) (fail err))
       ;; Cases:
       ;; 1 the entire seltrace is static and there is no partselect.
       ;; 2 part of the seltrace is nonstatic and there is no partselect (handled with 1).
       ;; 3 the entire seltrace is static and there is a static partselect.
       ;; 4 the entire seltrace is static and there is a nonstatic partselect.
       ;; 5 part of the seltrace is nonstatic and there is a partselect (don't
       ;;   care whether static).

       ;; Cases 1&2 -- no partselect.  Don't really care if there are nonstatic
       ;; selects or not.
       ((unless partsel-p)
        (mv nil lsp-sel-expr lsp-sel-type sel-nonstatic))

       ;; From here down we have a partselect.
       ((list base-svex width-svex) indices)

       ;; Case 4&5 -- part of the seltrace or the partselect is nonstatic:
       ((when (or (consp unres-sels)
                  (not (vl-expr-resolved-p (vl-partselect-plusminus->base x.part)))))
        (b* (((mv err psel-svex)
              (vl-plusminus-partselect->svex
               sel-nonstatic
               (vl-seltrace-type unres-sels lsp-sel-type)
               (vl-partselect->plusminus x.part)
               base-svex width-svex))
             ((when err) (fail err)))
          (mv nil lsp-sel-expr lsp-sel-type psel-svex)))

       ;; Case 3 -- everything is static:
       ((mv err psel-svex)
        (vl-plusminus-partselect->svex
         lsp-sel-expr lsp-sel-type
         (vl-partselect->plusminus x.part)
         base-svex width-svex))
       ((when err) (fail err)))
    (mv nil psel-svex x.type (sv::make-svex-var :name *svex-longest-static-prefix-var*)))
  ///

  (local (defthm svexlist-vars-of-cdr
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svexlist-vars (cdr x)))))))

  (local (defthm svex-vars-of-car
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svex-vars (car x)))))))

  (local (defthm svexlist-vars-of-take
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svexlist-vars (take n x)))))
           :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

  (local (defthm svexlist-vars-of-nthcdr
           #!sv
           (implies (not (member v (svexlist-vars x)))
                    (not (member v (svexlist-vars (nthcdr n x)))))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (local (defthm member-of-list-a
           (iff (member v (list a))
                (equal v a))
           :hints(("Goal" :in-theory (enable member)))))

  (local (defthm svexlist-vars-of-list-fix
           #!sv (equal (svexlist-vars (list-fix x))
                       (svexlist-vars x))))

  (defret vars-of-vl-operandinfo-to-svex-longest-static-prefix-full
    (implies (and (not (equal v *svex-longest-static-prefix-var*))
                  (not (member v (sv::svexlist-vars indices))))
             (not (member v (sv::svex-vars full-expr)))))

  (defret vars-of-vl-operandinfo-to-svex-longest-static-prefix-lsp
    (implies (sv::svarlist-addr-p (sv::svexlist-vars indices))
             (sv::svarlist-addr-p (sv::svex-vars lsp-expr)))))




(define vl-operandinfo-to-svex ((x vl-operandinfo-p)
                                (indices sv::svexlist-p)
                                (ss vl-scopestack-p)
                                (params vl-svexalist-p))
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
       ((mv & signedness) (vl-datatype-signedness x.type))

       ((mv err lsp-expr ?lsp-type dyn-expr)
        (vl-operandinfo-to-svex-longest-static-prefix
         x indices ss params))

       ((when err) (mv err (svex-x)))

       (res-base (sv::svex-replace-var dyn-expr *svex-longest-static-prefix-var* lsp-expr)))
    (clear-memoize-table 'sv::svex-replace-var)
    (mv nil (sv::svex-reduce-consts
             (if signedness
                 (svex-extend signedness size res-base)
               res-base))))
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
                       (svex-vars b))
           :hints(("Goal" :in-theory (enable sv::svex-alist-vars)))))

  (local (defthm svex-alist-keys-of-single
           #!sv (equal (svex-alist-keys (list (cons a b)))
                       (list (svar-fix a)))
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




(define vl-datatype-syscall-to-svex ((orig-x vl-expr-p)
                                     (fn stringp)
                                     (type vl-datatype-p)
                                     (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (res sv::Svex-p))
  (b* (((vl-svexconf conf))
       (warnings nil)
       ((mv err type)
        (vl-datatype-usertype-resolve type conf.ss :typeov conf.typeov))
       ((when err)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't resolve datatype in ~a0: ~@1"
                   :args (list (vl-expr-fix orig-x) err))
            (svex-x)))
       (fn (string-fix fn)))
    (cond ((equal fn "$bits")
           (b* (((mv err size) (vl-datatype-size type))
                ((when (or err (not size)))
                 (mv (fatal :type :vl-expr-to-svex-fail
                            :msg "Couldn't size datatype in ~a0: ~@1"
                            :args (list (vl-expr-fix orig-x) (or err "unsizable datatype")))
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
           (b* (((mv err & & dim)
                 (vl-datatype-remove-dim type))
                ((when (or err
                           ;; BOZO some of these might work for unsized dimensions
                           (vl-packeddimension-case dim :unsized)
                           (not (vl-range-resolved-p (vl-packeddimension->range dim)))))
                 (mv (fatal :type :vl-expr-to-svex-fail
                            :msg "Couldn't resolve outermost dimension for ~a0: ~@1"
                            :args (list (vl-expr-fix orig-x)
                                        (or err "unresolved dimension")))
                     (svex-x)))
                (dim.range (vl-packeddimension->range dim))
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
                        :args (list (vl-expr-fix orig-x)))
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


(fty::deflist vl-datatypelist :elt-type vl-datatype
  ///
  (defthm vl-datatypelist-fix-of-repeat
    (equal (vl-datatypelist-fix (repeat n x))
           (repeat n (vl-datatype-fix x)))
    :hints(("Goal" :in-theory (enable repeat)))))

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
                                          (ss vl-scopestack-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (new-x vl-datatypelist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv err1 x1) (vl-datatype-usertype-resolve (car x) ss))
       ((mv err2 x2) (vl-datatypelist-usertype-resolve (cdr x) ss)))
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
          (:vl-unary-bitand (sv::svcall sv::uand   (sv::svcall sv::signx
                                                                     (svex-int (lnfix arg-size))
                                                                     arg)))
          (:vl-unary-nand   (sv::svcall sv::bitnot
                                          (sv::svcall sv::uand
                                                        (sv::svcall sv::signx
                                                                      (svex-int (lnfix arg-size))
                                                                      arg))))
          (:vl-unary-bitor  (sv::svcall sv::uor     arg))
          (:vl-unary-nor    (sv::svcall sv::bitnot  (sv::svcall sv::uor    arg)))
          (:vl-unary-xor    (sv::svcall sv::uxor    (sv::svcall sv::zerox
                                                                      (svex-int (lnfix arg-size))
                                                                      arg)))
          (:vl-unary-xnor   (sv::svcall sv::bitnot
                                          (sv::svcall sv::uxor
                                                        (sv::svcall sv::zerox
                                                                      (svex-int (lnfix arg-size))
                                                                      arg)))))))
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
          (:vl-binary-plus    (sv::svcall +            left right))
          (:vl-binary-minus   (sv::svcall sv::b-     left right))
          (:vl-binary-times   (sv::svcall *            left right))
          (:vl-binary-div     (sv::svcall /            left right))
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
          ;; Shift amounts need to be zero-extended -- right arg is always
          ;; treated as unsigned per SV spec 11.4.10.
          (:vl-binary-shr     (sv::svcall sv::rsh
                                          ;; Weird case: 
                                          (sv::svcall sv::zerox
                                                      (svex-int (lnfix right-size))
                                                      right)
                                          (sv::svcall sv::zerox
                                                      (svex-int (lnfix left-size))
                                                      left)))
          (:vl-binary-shl     (sv::svcall sv::lsh
                                          (sv::svcall sv::zerox
                                                      (svex-int (lnfix right-size))
                                                      right)
                                          left))
          (:vl-binary-ashr    (sv::svcall sv::rsh
                                          (sv::svcall sv::zerox
                                                      (svex-int (lnfix right-size))
                                                      right)
                                          left))
          (:vl-binary-ashl    (sv::svcall sv::lsh
                                          (sv::svcall sv::zerox
                                                      (svex-int (lnfix right-size))
                                                      right)
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
             (not (member v (sv::svex-vars (svex-concat-list-aux widths x
                                                                   acc)))))))

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

(define vl-compare-datatypes ((a vl-datatype-p)
                              (b vl-datatype-p))
  :returns (err (iff (vl-msg-p err) err))
  (if (vl-datatype-equiv a b)
      nil
    ;; We'll see how often this bites us...
    (vmsg "Mismatching datatypes: ~a0, ~a1"
          (vl-datatype-fix a) (vl-datatype-fix b))))




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


(define vl-svex-keyval-index-lookup ((n natp)
                                     (x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  :returns (ans (implies ans (sv::svex-p ans)))
  (b* ((x (vl-svex-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key
                :expr (and (vl-expr-resolved-p key.key)
                           (eql (vl-resolved->val key.key)
                                (lnfix n)))
                :otherwise nil))
        (cdar x)))
    (vl-svex-keyval-index-lookup n (cdr x)))
  ///
  (defret vars-of-vl-svex-keyval-index-lookup
    (implies (and ans
                  (not (member v (vl-svex-keyvallist-vars x))))
             (not (member v (sv::svex-vars ans))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))

(define vl-array-assignpat-keyval-resolve ((lsb natp)
                                           (msb natp)
                                           (x vl-svex-keyvallist-p))
  :measure (abs (- (nfix lsb) (nfix msb)))
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
                        (lnfix msb))))
       ((when (eql (lnfix lsb) (lnfix msb)))
        ;; Last one
        (mv err1
            (list (or first (svex-x)))))
       (next (if (< (lnfix lsb) (lnfix msb))
                 (- (lnfix msb) 1)
               (+ (lnfix msb) 1)))
       ((mv err rest)
        (vl-array-assignpat-keyval-resolve lsb next x)))
    (mv (or err1 err)
        (cons (or first (svex-x)) rest)))
  ///
  (defret len-of-vl-array-assignpat-keyval-resolve
    (equal (len svex-membs)
           (+ 1 (abs (- (nfix msb) (nfix lsb))))))
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
               (decl-ss (implies (not err) (vl-scopestack-p decl-ss))))
  (b* (((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x ss))
       ((when err) (mv err nil trace))
       ((unless (vl-hidtrace-resolved-p trace))
        (mv (vmsg "Function ~a0 has unresolved indices??"
                  :args (list (vl-scopeexpr-fix x)))
            nil nil))
       ((vl-hidstep lookup) (car trace))
       ((unless (eq (tag lookup.item) :vl-fundecl))
        (mv (vmsg "Function name ~a0 does not refer to a fundecl but instead ~
                   ~a1"
                   :args (list (vl-scopeexpr-fix x) lookup.item))
            nil nil)))
    (mv nil lookup.item lookup.ss)))


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
                              (conf vl-svexconf-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (size (implies (not err) (posp size)) :rule-classes :type-prescription))
  (b* ((x (vl-slicesize-fix x)))
    (vl-slicesize-case x
      :none (mv nil 1)
      :expr (b* (((unless (vl-expr-resolved-p x.expr))
                  (mv (vmsg "Slice size is unresolved expression") nil))
                 (val (vl-resolved->val x.expr))
                 ((unless (posp val))
                  (mv (vmsg "Slice size must be nonzero") nil)))
              (mv nil val))
      :type (b* (((vl-svexconf conf))
                 ((mv err type) (vl-datatype-usertype-resolve x.type conf.ss :typeov conf.typeov))
                 ((when err) (mv err nil))
                 ((mv err size) (vl-datatype-size type))
                 ((when err) (mv err nil))
                 ((unless (posp size))
                  (mv (vmsg "Slice size must be nonzero") nil)))
              (mv nil size)))))

(define vl-size-to-unsigned-logic ((x posp))
  :returns (type vl-datatype-p)
  (make-vl-coretype :name :vl-logic
                    :pdims (list (vl-range->packeddimension
                                  (make-vl-range
                                   :msb (vl-make-index (1- (pos-fix x)))
                                   :lsb (vl-make-index 0)))))
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
                                        acl2::member-when-atom)))
             (local (defthm consp-by-len-equal-1
                      (implies (equal (len x) 1)
                               (consp x))
                      :hints(("Goal" :in-theory (enable len))))))


  (define vl-expr-to-svex-untyped ((x vl-expr-p)
                                   (conf vl-svexconf-p))
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
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type))))
                 (size maybe-natp))
    :measure (two-nats-measure (vl-expr-count x) 20)
    (b* ((warnings nil)
         (x (vl-expr-fix x)))
      (vl-expr-case x
        :vl-index (b* (((wmv warnings svex type)
                        (vl-index-expr-to-svex x conf))
                       ((unless type)
                        (mv warnings svex type nil))
                       ((mv err size) (vl-datatype-size type))
                       ((when (or err (not size)))
                        (mv (warn :type :vl-expr-to-svex-fail
                                  :msg "Couldn't size datatype ~a0 for expression ~a1: ~@2"
                                  :args (list type x (or err "unsizeable")))
                            svex type nil)))
                    (mv warnings svex type size))
        :vl-cast (vl-casttype-case x.to
                   :type (b* (((vl-svexconf conf))
                              ((mv err type)
                               (vl-datatype-usertype-resolve x.to.type conf.ss :typeov conf.typeov))
                              ((when err)
                               (mv (fatal :type :vl-expr-to-svex-fail
                                          :msg "Usertypes not resolved in cast ~a0: ~@1"
                                          :args (list x err))
                                   (svex-x) nil nil))
                              ((wmv warnings svex)
                               (vl-expr-to-svex-datatyped x.expr nil type conf))
                              ((mv err size) (vl-datatype-size type))
                              ((when (or err (not size)))
                               (mv (warn :type :vl-expr-to-svex-fail
                                         :msg "Couldn't size datatype ~a0 for expression ~a1: ~@2"
                                         :args (list type x (or err "unsizeable")))
                                   svex type nil)))
                           (mv warnings svex type size))
                   :size (b* (((unless (vl-expr-resolved-p x.to.size))
                               (mv (fatal :type :vl-expr-to-svex-fail
                                          :msg "Unresolved size cast: ~a0"
                                          :args (list x))
                                   (svex-x) nil nil))
                              ((mv warnings svex size)
                               (vl-expr-to-svex-selfdet x.expr (vl-resolved->val x.to.size) conf)))
                           (mv warnings svex
                               (and (posp size)
                                    (vl-size-to-unsigned-logic size))
                               size))
                   :otherwise
                   (b* (((wmv warnings svex size)
                         (vl-expr-to-svex-selfdet x nil conf)))
                     (mv warnings svex
                         (and (posp size)
                              (vl-size-to-unsigned-logic size))
                         size)))
        :otherwise
        (b* (((wmv warnings svex size)
              (vl-expr-to-svex-selfdet x nil conf)))
          (mv warnings svex
              (and (posp size)
                   (vl-size-to-unsigned-logic size))
              size)))))


  (define vl-expr-to-svex-selfdet ((x vl-expr-p)
                                   (ctxsize maybe-natp)
                                   (conf vl-svexconf-p))
    :short "Translates a VL expression to svex in a self-determined context, perhaps
            with a context size."
    :long "<p>This function sign- or zero-extends the result so that other
functions can assume all bits of it are good.</p>"
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription
                       "Size if available.  If not, we've already warned about it."))
    :measure (two-nats-measure (vl-expr-count x) 10)
    (b* ((x (vl-expr-fix x))
         ((vl-svexconf conf))
         (ctxsize (maybe-natp-fix ctxsize))
         (opacity (vl-expr-opacity x))
         (warnings nil)
         ((when (eq opacity :special))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Need a type context to interpret special expression ~a0"
                     :args (list x))
              (svex-x)
              nil))
         ((wmv warnings signedness) (vl-expr-typedecide x conf.ss conf.typeov))
         ((unless signedness)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Couldn't decide signedness of expression ~a0."
                     :args (list x))
              (svex-x)
              nil))
         ((wmv warnings size) (vl-expr-selfsize x conf.ss conf.typeov))
         ((unless size)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Couldn't size expression ~a0."
                     :args (list x))
              (svex-x)
              nil))
         (finalsize (if ctxsize (max ctxsize size) size))
         (ext-size (if (eq opacity :transparent)
                       finalsize
                     size))
         ((wmv warnings svex)
          (if (eq opacity :opaque)
              (vl-expr-to-svex-opaque x conf)
            (vl-expr-to-svex-transparent x finalsize signedness conf))))
      (mv warnings (svex-extend signedness ext-size svex) finalsize)))

  (define vl-expr-to-svex-vector ((x vl-expr-p)
                                  (size natp)
                                  (signedness vl-exprsign-p)
                                  (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-expr-count x) 6)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         ((vl-svexconf conf))
         (opacity (vl-expr-opacity x))
         (warnings nil)
         ((when (eq opacity :special))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Need a type context to interpret special expression ~a0"
                     :args (list x))
              (svex-x)))
         ((unless (eq opacity :opaque))
          (vl-expr-to-svex-transparent x size signedness conf))
         ((wmv warnings selfsize) (vl-expr-selfsize x conf.ss conf.typeov))
         ((unless selfsize)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Sizing of ~a0 failed unexpectedly."
                     :args (list x))
              (svex-x)))
         ((wmv warnings svex)
          (vl-expr-to-svex-opaque x conf))
         (size
          ;; Special case for extints -- they get sign/zero-extended at their
          ;; context size, not their self size.
          (if (vl-expr-case x
                :vl-literal (vl-value-case x.val :vl-extint)
                :otherwise nil)
              size
            selfsize)))
      (mv warnings (svex-extend signedness size svex))))


  (define vl-expr-to-svex-transparent ((x vl-expr-p)
                                       (size natp)
                                       (signedness vl-exprsign-p)
                                       (conf vl-svexconf-p))
    :guard (equal (vl-expr-opacity x) :transparent)
    :measure (two-nats-measure (vl-expr-count x) 4)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (warnings nil))
      (vl-expr-case x
        :vl-unary
        (b* (((unless (member x.op '(:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Operators with side-effects aren't supported: ~a0"
                         :args (list x))
                  (svex-x)))
             ((wmv warnings subexp)
              (vl-expr-to-svex-vector x.arg size signedness conf))
             ((wmv err svex)
              (vl-unaryop-to-svex x.op subexp size size signedness)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))
        :vl-binary
        ;; Two categories: either transparent in just the first operand, or both.
        (b* (((wmv warnings left-svex)
              (vl-expr-to-svex-vector x.left size signedness conf))
             ((wmv warnings right-svex right-size)
              (if (member x.op '(:vl-binary-power
                                 :vl-binary-shl
                                 :vl-binary-shr
                                 :vl-binary-ashl
                                 :vl-binary-ashr))
                  ;; Transparent only in the first operand.
                  (vl-expr-to-svex-selfdet x.right nil conf)
                ;; Transparent in both operands.
                (b* (((mv warnings right-svex)
                      (vl-expr-to-svex-vector x.right size signedness conf)))
                  (mv warnings right-svex size))))
             ((wmv err svex)
              (vl-binaryop-to-svex x.op left-svex right-svex size
                                   ;; Presumably we don't get here if we don't
                                   ;; get a size for the right arg.  But in any
                                   ;; case we've already warned about it.
                                   (or right-size size)
                                   size signedness)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))

        :vl-qmark
        (b* (((wmv warnings test-svex ?test-size)
              (vl-expr-to-svex-selfdet x.test nil conf))
             ((wmv warnings then-svex)
              (vl-expr-to-svex-vector x.then size signedness conf))
             ((wmv warnings else-svex)
              (vl-expr-to-svex-vector x.else size signedness conf)))
          (mv (ok)
              (sv::svcall sv::? test-svex then-svex else-svex)))

        :vl-mintypmax
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support mintypmax expressions: ~a0."
                   :args (list x))
            (svex-x))
        :otherwise
        (mv (ok) (prog2$ (impossible) (svex-x))))))

  (define vl-expr-to-svex-opaque ((x vl-expr-p)
                                  (conf vl-svexconf-p))
    :guard (equal (vl-expr-opacity x) :opaque)
    :measure (two-nats-measure (vl-expr-count x) 4)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (warnings nil)
         ((vl-svexconf conf)))
      (vl-expr-case x

        :vl-literal
        (b* (((mv err svex) (vl-value-to-svex x.val)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))

        :vl-index
        (b* (((wmv warnings svex &)
              (vl-index-expr-to-svex x conf)))
          (mv warnings svex))

        :vl-unary
        ;; All the opaque unary operations have 1-bit results and
        ;; selfdetermined operands.
        (b* (((wmv warnings arg-svex arg-size) (vl-expr-to-svex-selfdet x.arg nil conf))
             ((unless arg-size)
              ;; already warned
              (mv warnings (svex-x)))
             ((mv err svex)
              (vl-unaryop-to-svex x.op arg-svex arg-size 1 :vl-unsigned)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))

        :vl-binary
        ;; Two types of operators here: logicals, where the operands are
        ;; selfdetermined, and comparisons, where the operands are sized to the
        ;; larger of the two.
        (b* (((when (member x.op '(:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)))
              ;; Logicals -- self-determined operands
              (b* (((wmv warnings left-svex left-size) (vl-expr-to-svex-selfdet x.left nil conf))
                   ((wmv warnings right-svex right-size) (vl-expr-to-svex-selfdet x.right nil conf))
                   ((unless (and left-size right-size))
                    ;; already warned
                    (mv warnings (svex-x)))
                   ;; It doesn't matter if these are sign- or zero-extended.
                   ((mv err svex)
                    (vl-binaryop-to-svex x.op left-svex right-svex left-size right-size 1 :vl-unsigned)))
                (mv (if err
                        (fatal :type :vl-expr-to-svex-fail
                               :msg "Failed to convert expression ~a0: ~@1"
                               :args (list x err))
                      (ok))
                    svex)))
             ;; Vectors -- find sizes first
             ((wmv warnings left-size) (vl-expr-selfsize x.left conf.ss conf.typeov))
             ((wmv warnings right-size) (vl-expr-selfsize x.right conf.ss conf.typeov))
             ((wmv warnings left-type) (vl-expr-typedecide x.left conf.ss conf.typeov))
             ((wmv warnings right-type) (vl-expr-typedecide x.right conf.ss conf.typeov))
             ((unless (and left-size right-size left-type right-type))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to find size and signedness of expression ~a0"
                         :args (list (if (and left-size left-type)
                                         x.right
                                       x.left)))
                  (svex-x)))
             ;; Size each under the max size
             (arg-size (max left-size right-size))
             (arg-type (vl-exprsign-max left-type right-type))
             ((wmv warnings left-svex)
              (vl-expr-to-svex-vector x.left arg-size arg-type conf))
             ((wmv warnings right-svex)
              (vl-expr-to-svex-vector x.right arg-size arg-type conf))
             ((mv err svex)
              (vl-binaryop-to-svex x.op left-svex right-svex arg-size arg-size 1 :vl-unsigned)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))

        :vl-concat
        (b* (((wmv warnings svexes sizes) (vl-exprlist-to-svex-selfdet x.parts conf))
             ((when (member nil sizes))
              ;; already warned
              (mv warnings (svex-x)))
             (svex (svex-concat-list sizes svexes)))
          (mv (ok) svex))

        :vl-multiconcat
        (b* (((wmv warnings svexes sizes) (vl-exprlist-to-svex-selfdet x.parts conf))
             ((unless (vl-expr-resolved-p x.reps))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Unresolved reps in multiple concatenation ~a0"
                         :args (list x))
                  (svex-x)))
             ((when (member nil sizes))
              (mv warnings (svex-x)))
             (svex
              (svex-multiconcat (vl-resolved->val x.reps) svexes sizes)))
          (mv (ok) svex))

        :vl-inside
        (mv (fatal :type :vl-expr-unsupported
                   :msg "Inside expressions are not yet supported: ~a0"
                   :args (list x))
            (svex-x))

        :vl-call
        (if x.systemp
            (b* ((simple-name (vl-simple-id-name x.name))
                 ((unless simple-name)
                  (mv (fatal :type :vl-expr-to-svex-fail
                             :msg "Bad system function name: ~a0"
                             :args (list x))
                      (svex-x)))

                 ((when (vl-unary-syscall-p "$clog2" x))
                  (b* (((wmv warnings arg-svex ?size)
                        (vl-expr-to-svex-selfdet (car x.args) nil conf)))
                    (mv warnings
                        (sv::svcall sv::clog2 arg-svex))))

                 ;; It happens that almost all the system functions we support
                 ;; basically act on datatypes, and if an expression is given
                 ;; instead, they run on the type of the expression.

                 ((when (and (atom x.args)
                             x.typearg))
                  (vl-datatype-syscall-to-svex x simple-name x.typearg conf))

                 ((unless (and (not x.typearg)
                               (eql (len x.args) 1)))
                  (mv (fatal :type :vl-expr-unsupported
                             :msg "Unsupported system call: ~a0"
                             :args (list x))
                      (svex-x)))

                 ;; Resolve the expression to its type.
                 ((wmv warnings ?arg-svex type ?size)
                  (vl-expr-to-svex-untyped (car x.args) conf))

                 ((unless type)
                  ;; Already warned
                  (mv warnings (svex-x)))

                 ((wmv warnings svex)
                  (vl-datatype-syscall-to-svex x simple-name type conf)))
              (mv warnings svex))

          (b* (((wmv warnings svex &)
                (vl-funcall-to-svex x conf)))
            (mv warnings svex)))

        :vl-cast
        ;; If we get here, we've already gotten the size/signedness of the cast
        ;; expression and decided it's OK as a vector type.  However, the inner
        ;; expression might not be a vector expression -- e.g. the type could
        ;; be a packed struct and the inner expression an assignment pattern
        ;; creating that struct.  So we have to use vl-expr-to-svex-datatyped
        ;; here.
        (vl-casttype-case x.to
          :type (b* (((mv err to-type) (vl-datatype-usertype-resolve x.to.type conf.ss
                                                                     :typeov conf.typeov))
                     ((when err)
                      (mv (fatal :type :vl-expr-to-svex-fail
                                 :msg "Usertypes not resolved in cast ~a0: ~@1"
                                 :args (list x err))
                          (svex-x))))
                  (vl-expr-to-svex-datatyped x.expr nil to-type conf))
          :size (b* (((unless (vl-expr-resolved-p x.to.size))
                      (mv (fatal :type :vl-expr-to-svex-fail
                                 :msg "Unresolved size cast: ~a0"
                                 :args (list x))
                          (svex-x)))
                     ((mv warnings svex &)
                      (vl-expr-to-svex-selfdet x.expr (vl-resolved->val x.to.size) conf)))
                  (mv warnings svex))
          :signedness
          ;; Don't need to do anything about the signedness here; it only
          ;; affects the expressions outside this one.  Also, tests seem to
          ;; indicate that the signedness cast is opaque, so we fortunately
          ;; don't need a contextsize.
          (b* (((mv warnings svex &)
                (vl-expr-to-svex-selfdet x.expr nil conf)))
            (mv warnings svex))
          :const
          ;; What does this even mean?
          (b* (((mv warnings svex &)
                (vl-expr-to-svex-selfdet x.expr nil conf)))
            (mv warnings svex)))


        :vl-pattern
        (b* (((unless x.pattype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Untyped assignment pattern: ~a0"
                         :args (list x))
                  (svex-x)))
             ((mv err pattype) (vl-datatype-usertype-resolve x.pattype conf.ss :typeov conf.typeov))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in pattern ~a0: ~@1"
                         :args (list x err))
                  (svex-x))))
          (vl-assignpat-to-svex x.pat pattype conf x))
        :otherwise
        (mv (ok) (prog2$ (impossible) (svex-x))))))

  (define vl-index-expr-to-svex ((x vl-expr-p)
                                 (conf vl-svexconf-p))
    :guard (vl-expr-case x :vl-index)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type)))))
    :measure (two-nats-measure (vl-expr-count x) 2)
    (b* ((warnings nil)
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv (ok) (svex-x) nil))
         ((vl-svexconf conf))
         (x (vl-expr-fix x))
         ((mv err opinfo) (vl-index-expr-typetrace x conf.ss conf.typeov))
         ((when err)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to convert expression ~a0: ~@1"
                     :args (list x err))
              (svex-x) nil))
         ((vl-operandinfo opinfo))
         ((wmv warnings svex-indices ?sizes)
          (vl-exprlist-to-svex-selfdet
           (vl-operandinfo->indices opinfo) conf))
         ((vl-hidstep decl) (car opinfo.hidtrace))
         ((mv err svex)
          (vl-operandinfo-to-svex opinfo svex-indices conf.ss conf.params)))
      (mv (if err
              (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to convert expression ~a0: ~@1"
                     :args (list x err))
            (ok))
          svex
          opinfo.type)))

  ;; (trace$ #!vl (vl-funcall-to-svex
  ;;               :entry (list 'vl-funcall-to-svex
  ;;                            (with-local-ps (vl-pp-expr x)))
  ;;               :exit (list 'vl-funcall-to-svex
  ;;                           (with-local-ps (vl-print-warnings (car values)))
  ;;                           (and (caddr values)
  ;;                                (with-local-ps (vl-pp-datatype (caddr values)))))))

  (define vl-funcall-to-svex ((x vl-expr-p)
                              (conf vl-svexconf-p))
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (type (and (vl-maybe-datatype-p type)
                            (implies type
                                     (vl-datatype-resolved-p type)))))
    :guard (vl-expr-case x :vl-call)
    :measure (two-nats-measure (vl-expr-count x) 2)
    (b* ((warnings nil)
         ((unless (mbt (vl-expr-case x :vl-call)))
          (impossible) ;; need this case for measure
          (mv (ok) (svex-x) nil))
         ((vl-svexconf conf))
         ((vl-call x) (vl-expr-fix x))
         ;; ((mv err fnname trace) (vl-funname->svex-funname x.name conf.ss))
         (expr (cdr (hons-get x.name conf.fns)))
         ((unless expr)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function hasn't been preprocessed: ~a0"
                     :args (list x))
              (svex-x) nil))
         (rettype (cdr (hons-get x.name conf.typeov)))
         ((unless rettype)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function hasn't been preprocessed (return type missing): ~a0"
                     :args (list x))
              (svex-x) nil))
         ((unless (vl-datatype-resolved-p rettype))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function hasn't been preprocessed (return type unresolved): ~a0"
                     :args (list x))
              (svex-x) nil))
         (portdecl-look (hons-get x.name conf.fnports))
         ((unless portdecl-look)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function hasn't been preprocessed (port declarations missing): ~a0"
                     :args (list x))
              (svex-x) nil))
         (portdecls (cdr portdecl-look))
         (port-types (vl-portdecllist->types portdecls))
         ((unless (vl-datatypelist-resolved-p port-types))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function hasn't been preprocessed (unresolved ~
                           types in portdecls): ~a0"
                     :args (list x))
              (svex-x) nil))
         ((unless (eql (len port-types) (len x.args)))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Wrong number of arguments in function call ~a0: ~
                           supposed to be ~x1 ports"
                     :args (list x (len port-types)))
              (svex-x) nil))
         ((wmv warnings args-svex)
          (vl-exprlist-to-svex-datatyped
           x.args
           port-types
           conf))
         (comp-alist (vl-function-pair-inputs-with-actuals portdecls args-svex))
         ((with-fast comp-alist))
         (ans (sv::svex-subst-memo expr comp-alist)))
      (clear-memoize-table 'sv::svex-subst-memo)
      (mv (ok) ans rettype)))

  (define vl-expr-to-svex-datatyped ((x    vl-expr-p)
                                     (lhs  vl-maybe-expr-p
                                           "LHS, if applicable, for truncation warnings.")
                                     (type vl-datatype-p)
                                     (conf vl-svexconf-p))
    :guard (vl-datatype-resolved-p type)
    :measure (two-nats-measure (vl-expr-count x) 16)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (type (vl-datatype-fix type))
         (warnings nil)
         ((vl-svexconf conf))
         (opacity (vl-expr-opacity x))
         (packedp (vl-datatype-packedp type))
         ((when (and packedp 
                     (not (eq opacity :special))
                     (not (vl-expr-case x :vl-pattern))))
          ;; A non-special opacity generally means the expression is
          ;; vector-like, and I think that if the datatype is packed we get the
          ;; right results by simply treating the expression as a vector with
          ;; the given size.  We may need to add exceptions to this.
          (b* (((mv err size) (vl-datatype-size type))
               ((when (or err (not size)))
                ;; (break$)
                (mv (fatal :type :vl-expr-to-svex-fail
                           :msg "Couldn't size packed datatype ~a0"
                           :args (list (vl-datatype-fix type)))
                    (svex-x)))
               ((wmv warnings svex rhs-size) (vl-expr-to-svex-selfdet x size conf))
               ((unless rhs-size)
                ;; Some kind of error.
                (mv warnings svex))
               (ss (vl-svexconf->ss conf))
               ((wmv warnings) (vl-maybe-warn-about-implicit-truncation lhs size x rhs-size ss))
               ((mv & & x-selfsize) (vl-expr-to-svex-selfdet x nil conf))
               ((wmv warnings) (if x-selfsize
                                   (vl-maybe-warn-about-implicit-extension size x-selfsize x ss)
                                 nil)))
            (mv warnings svex))))

      (vl-expr-case x
        :vl-index
        (b* (((wmv warnings svex itype)
              (vl-index-expr-to-svex x conf))
             ((unless itype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Couldn't find type for expression: ~a0"
                         :args (list x))
                  svex))
             (err (vl-compare-datatypes type itype)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x itype (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-qmark
        (b* (((wmv warnings test-svex ?test-size)
              (vl-expr-to-svex-selfdet x.test nil conf))
             ((wmv warnings then-svex)
              ;; BOZO should we really pass the lhs down here?  Maybe?
              (vl-expr-to-svex-datatyped x.then lhs type conf))
             ((wmv warnings else-svex)
              (vl-expr-to-svex-datatyped x.else lhs type conf)))
          (mv (ok)
              (sv::svcall sv::? test-svex then-svex else-svex)))

        :vl-call
        (b* (((when x.systemp)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "System call ~a0 supposed to return unpacked type ~a1"
                         :args (list x (vl-datatype-fix type)))
                  (svex-x)))
             ((wmv warnings svex ftype)
              (vl-funcall-to-svex x conf))
             ((unless ftype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Couldn't find type for expression: ~a0"
                         :args (list x))
                  svex))
             (err (vl-compare-datatypes type ftype)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x ftype (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-cast
        (vl-casttype-case x.to
          :type (b* (((mv err to-type) (vl-datatype-usertype-resolve x.to.type conf.ss :typeov conf.typeov))
                     ((when err)
                      (mv (fatal :type :vl-expr-to-svex-fail
                                 :msg "Usertypes not resolved in cast ~a0: ~@1"
                                 :args (list x err))
                          (svex-x)))
                     ((wmv warnings svex)
                      ;; We're casting to a new type so don't pass the lhs down.
                      (vl-expr-to-svex-datatyped x.expr nil to-type conf))
                     (err (vl-compare-datatypes type to-type)))
                  (mv (if err
                          (fatal :type :vl-expr-to-svex-fail
                                 :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                                 :args (list x x.to (vl-datatype-fix type) err))
                        (ok))
                      svex))
          :const
          ;; Maybe we just ignore this?
          ;; No idea whether we should pass lhs down.  Or anything else.  Sigh.
          (vl-expr-to-svex-datatyped x.expr lhs type conf)
          :otherwise
          ;; This seems bogus, we have a non-packed type but we're casting to a
          ;; signedness or size.
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "~s0 cast in non-vector context: ~a1"
                     :args (list (if (eq x.kind :signedness)
                                     "Signedness"
                                   "Size")
                                 x))
              (svex-x)))

        :vl-mintypmax
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support mintypmax expressions: ~a0."
                   :args (list x))
            (svex-x))

        :vl-pattern
        (b* (((unless x.pattype)
              (vl-assignpat-to-svex x.pat type conf x))
             ((mv err pattype)
              (vl-datatype-usertype-resolve x.pattype conf.ss :typeov conf.typeov))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in pattern ~a0: ~@1"
                         :args (list x err))
                  (svex-x)))
             ((wmv warnings svex)
              (vl-assignpat-to-svex x.pat pattype conf x))
             (err (if (and packedp (vl-datatype-packedp pattype))
                      nil
                    (vl-compare-datatypes type pattype))))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x pattype (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-special
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support ~a0."
                   :args (list x))
            (svex-x))

        :vl-stream
        (b* (((mv err slicesize) (if (eq x.dir :left)
                                     (vl-slicesize-resolve x.size conf)
                                   ;; irrelevant
                                   (mv nil 1)))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to resolve slice size of streaming ~
                               concat expression ~a0: ~@1"
                         :args (list x err))
                  (svex-x)))
             ((wmv warnings concat concat-size) (vl-streamexprlist-to-svex x.parts conf))
             ((unless concat-size)
              ;; Already warned, presumably.
              (mv warnings (svex-x)))
             ((mv err target-size) (vl-datatype-size type))
             ((when (or err (not (posp target-size))))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Problem sizing datatype ~a0 for streaming concat ~a1: ~@2"
                         :args (list type x
                                     (or err (if target-size "size zero" "unsizable"))))
                  (svex-x)))
             (warnings (if (> concat-size target-size)
                           (warn :type :vl-streaming-concat-error
                                 :msg "The streaming concatenation ~a0 is ~
                                       larger than its target type ~a1 -- ~
                                       SystemVerilog says this is an error."
                                 :args (list x type))
                         warnings))

             (bitstream (if (eq x.dir :right)
                            concat
                          (sv::svcall sv::blkrev
                                      (svex-int target-size)
                                      (svex-int slicesize)
                                      concat))))
          ;; In SV, we'd now stick the bitstream into a container of the
          ;; appropriate datatype.  But in svex, everything's just kept as a
          ;; bitstream, so we're already done.
          (mv warnings bitstream))

        :vl-tagged
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support ~a0."
                   :args (list x))
            (svex-x))


        :otherwise
        ;; :vl-value, :vl-unary, :vl-binary, :vl-concat, :vl-multiconcat, :vl-inside
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Vector expression ~a0 doesn't fit in unpacked type ~a1"
                   :args (list x (vl-datatype-fix type)))
            (svex-x)))))

  (define vl-streamexprlist-to-svex ((x vl-streamexprlist-p)
                                     (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-streamexprlist-count x) 0)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription))
    (b* ((warnings nil)
         ((when (atom x)) (mv warnings (svex-x) 0))
         ((wmv warnings svex1 size1) (vl-streamexpr-to-svex (car x) conf))
         ((wmv warnings svex2 size2) (vl-streamexprlist-to-svex (cdr x) conf))
         ((unless (and size1 size2))
          ;; already warned
          (mv warnings (svex-x) nil)))
      (mv warnings
          (sv::svcall sv::concat (svex-int size2) svex2 svex1)
          (+ size1 size2))))

  (define vl-streamexpr-to-svex ((x vl-streamexpr-p)
                                 (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-streamexpr-count x) 200)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex)
                            (sv::svarlist-addr-p (sv::svex-vars svex))))
                 (size maybe-natp :rule-classes :type-prescription))
    (b* (((vl-streamexpr x))
         ((mv warnings svex ?type size)
          (vl-expr-to-svex-untyped x.expr conf)))

      (vl-arrayrange-case x.part
        :none (mv warnings svex size) ;; already warned if size is nil
        :otherwise
        (b* (((unless type) (mv warnings svex nil)) ;; already warned
             ((mv err ?caveat basetype dim1) (vl-datatype-remove-dim type))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad type ~a0 from expression ~a1 in streaming concat: ~@2"
                         :args (list type x.expr err))
                  (svex-x) nil))
             ((mv err basesize) (vl-datatype-size basetype))
             ((when (or err (not (posp basesize))))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Unsizable basetype ~a0 from expression ~a1 in ~
                               streaming concat: ~@2"
                         :args (list type x.expr (or err
                                                     (if basesize "zero size" "unsizable"))))
                  (svex-x) nil))
             ((when (vl-packeddimension-case dim1 :unsized))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Array range on unsized array expression ~a0 in streaming concat"
                         :args (list x.expr))
                  (svex-x) nil))
             ((vl-range dimrange) (vl-packeddimension->range dim1))
             ((unless (vl-range-resolved-p dimrange))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Array range unresolved on unsized array ~
                               expression ~a0 in streaming concat"
                         :args (list x.expr))
                  (svex-x) nil))
             (dim-msb (vl-resolved->val dimrange.msb))
             (dim-lsb (vl-resolved->val dimrange.lsb))
             ((mv err relative-lsb width)
              (vl-arrayrange->rel-lsb-and-width x.part dim-lsb dim-msb))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad array range in streaming concat on expression ~a0: ~@1"
                         :args (list x.expr err))
                  (svex-x) nil))
             (shift (* relative-lsb basesize))
             (size (* width basesize)))
          (mv warnings
              (sv::svcall sv::rsh (svex-int shift) svex)
              size)))))

  (define vl-assignpat-to-svex ((x vl-assignpat-p)
                                (type vl-datatype-p)
                                (conf vl-svexconf-p)
                                (orig-x vl-expr-p))
    :guard (vl-datatype-resolved-p type)
    :measure (two-nats-measure (vl-assignpat-count x) 16)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         (type (vl-maybe-usertype-resolve type))
         ;; Makes sure type is not just a bare usertype.  If the result is a
         ;; usertype, it at least has an array dimension.
         ((when (or (consp (vl-datatype->udims type))
                    (consp (vl-datatype->pdims type))))
          ;; Array.
          (b* (((mv ?err ?caveat slottype dim)
                (vl-datatype-remove-dim type))
               ;; Never an error because we have dims.
               ((when (vl-packeddimension-case dim :unsized))
                (mv (fatal :type :vl-expr-to-svex-fail
                           :msg "unsized dimension in type of assignment patter ~a0"
                           :args (list orig-x))
                    (svex-x)))
               (range (vl-packeddimension->range dim))
               ((unless (vl-range-resolved-p range))
                (mv (fatal :type :vl-expr-to-svex-fail
                           :msg "unresolved dimension in type of assignment pattern ~a0"
                           :args (list orig-x))
                    (svex-x))))
            (vl-array-assignpat-to-svex x slottype range conf orig-x))))
      (vl-datatype-case type
        :vl-struct
        (vl-struct-assignpat-to-svex x type.members conf orig-x)
        :otherwise
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Bad type ~a0 for assignment pattern ~a1"
                   :args (list type orig-x))
            (svex-x)))))


  (define vl-array-assignpat-to-svex ((x vl-assignpat-p)
                                      (slottype vl-datatype-p)
                                      (range vl-range-p)
                                      (conf vl-svexconf-p)
                                      (orig-x vl-expr-p))
    :guard (and (vl-range-resolved-p range)
                (vl-datatype-resolved-p slottype))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         (slottype (vl-datatype-fix slottype))
         (subexprs (vl-assignpat-case x
                     :positional x.vals
                     :keyval (alist-vals x.pairs)
                     :repeat x.vals))
         ((mv err slotsize) (vl-datatype-size slottype))
         ((when (or err (not slotsize)))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Couldn't size assignpattern slot type ~a0 (expr: ~a1)"
                     :args (list slottype orig-x))
              (svex-x)))
         (arrsize (vl-range-size range))
         ((vl-range range))
         ((wmv warnings svex-subexprs)
          (vl-exprlist-to-svex-datatyped
           subexprs
           (repeat (len subexprs) slottype)
           conf)))
      (vl-assignpat-case x
        :positional
        (b* (((unless (eql (len subexprs) arrsize))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Wrong number of elements in positional assignment ~
                               pattern ~a0. (Range: [~a1, ~a2].)"
                         :args (list orig-x range.msb range.lsb))
                  (svex-x))))
          (mv (ok)
              (svex-concat-list (repeat (len subexprs) slotsize) svex-subexprs)))
        :repeat
        (b* (((unless (vl-expr-resolved-p x.reps))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Unresolved repetition count in assignment pattern: ~a0"
                         :args (list orig-x))
                  (svex-x)))
             (reps (vl-resolved->val x.reps))
             ((unless (eql (* reps (len subexprs)) arrsize))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Wrong number of elements in positional assignment ~
                               pattern ~a0. (Range: [~a1, ~a2].)"
                         :args (list orig-x range.msb range.lsb))
                  (svex-x))))
          (mv (ok)
              (svex-multiconcat reps svex-subexprs (repeat (len subexprs) slotsize))))
        :keyval
        (b* ((err (vl-check-array-assignpat-keys x.pairs range))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad key in assignment pattern ~a0: ~@1"
                         :args (list orig-x err))
                  (svex-x)))
             (svex-keyvals (pairlis$ (alist-keys x.pairs) svex-subexprs))
             ((mv err svex-slots)
              (vl-array-assignpat-keyval-resolve
               (vl-resolved->val range.lsb)
               (vl-resolved->val range.msb)
               svex-keyvals)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad key/val assignment pattern ~a0: ~@1"
                         :args (list orig-x err))
                (ok))
              (svex-concat-list (repeat arrsize slotsize) svex-slots))))))

  (define vl-struct-assignpat-keyval-resolve ((x vl-keyvallist-p)
                                              (membs vl-structmemberlist-p)
                                              (conf vl-svexconf-p)
                                              (orig-x vl-expr-p))
    :guard (vl-structmemberlist-resolved-p membs)
    :measure (two-nats-measure (vl-keyvallist-count x)
                               (len membs))
    ;; BOZO only returning one of the errors...
    :returns (mv (warnings vl-warninglist-p)
                 (svex-membs
                  (and (sv::svexlist-p svex-membs)
                       (equal (len svex-membs) (len membs))
                       (sv::svarlist-addr-p (sv::svexlist-vars svex-membs)))
                  "Most-significant first"))
    :verify-guards nil
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         ((when (atom membs)) (mv nil nil))
         ((vl-structmember m1) (car membs))
         (first (or (vl-keyval-member-lookup m1.name x)
                    (vl-keyval-default-lookup x)))
         ((wmv warnings first)
          (if first
              (vl-expr-to-svex-datatyped
               first nil m1.type conf)
            (mv (fatal :type :vl-expr-to-svex-fail
                       :msg "No entry for struct member ~s1 in ~
                                  assignment pattern ~a1"
                       :args (list m1.name orig-x))
                (svex-x))))
         ((wmv warnings rest)
          (vl-struct-assignpat-keyval-resolve
           x (cdr membs) conf orig-x)))
      (mv warnings
          (cons first rest))))

  (define vl-struct-assignpat-to-svex ((x vl-assignpat-p)
                                       (membs vl-structmemberlist-p)
                                       (conf vl-svexconf-p)
                                       (orig-x vl-expr-p))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :guard (vl-structmemberlist-resolved-p membs)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (sv::svex-p svex) (sv::svarlist-addr-p (sv::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         ((mv err widths) (vl-structmemberlist-sizes membs))
         ((when (or err (member nil widths)))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Couldn't size struct members for assignment ~
                           pattern ~a0"
                     :args (list orig-x))
              (svex-x))))
      (vl-assignpat-case x
        :positional
        (b* (((unless (eql (len x.vals) (len membs)))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Wrong number of entries in positional ~
                               assignment pattern ~a0"
                         :args (list orig-x))
                  (svex-x)))
             (types (vl-structmemberlist->types membs))
             ((wmv warnings svex-vals)
              (vl-exprlist-to-svex-datatyped x.vals types conf)))
          (mv (ok)
              (svex-concat-list widths svex-vals)))
        :repeat
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Repetitions not supported for struct-typed ~
                         assignment patterns: ~a0"
                   :args (list orig-x))
            (svex-x))
        :keyval
        (b* ((err (vl-check-struct-assignpat-keys x.pairs membs))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad key in assignment pattern ~a0: ~@1"
                         :args (list orig-x err))
                  (svex-x)))
             ((wmv warnings svex-membs)
              (vl-struct-assignpat-keyval-resolve
               x.pairs membs conf orig-x)))
          (mv warnings
              (svex-concat-list widths svex-membs))))))

  (define vl-exprlist-to-svex-datatyped ((x vl-exprlist-p)
                                         (types vl-datatypelist-p)
                                         (conf vl-svexconf-p))
    :guard (and (equal (len types) (len x))
                (vl-datatypelist-resolved-p types))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svexes
                  (and (sv::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (sv::svarlist-addr-p (sv::svexlist-vars svexes)))))
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil))
         ((wmv warnings first)
          (vl-expr-to-svex-datatyped
           (car x) nil (car types) conf))
         ((wmv warnings rest)
          (vl-exprlist-to-svex-datatyped
           (cdr x) (cdr types) conf)))
      (mv warnings (cons first rest))))

  (define vl-exprlist-to-svex-selfdet ((x vl-exprlist-p)
                                       (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svexes
                  (and (sv::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (sv::svarlist-addr-p (sv::svexlist-vars svexes))))
                 (sizes
                  (and (vl-maybe-nat-listp sizes)
                       (equal (len sizes) (len x))
                       (true-listp sizes))))
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil nil))
         ((wmv warnings first size1)
          (vl-expr-to-svex-selfdet
           (car x) nil conf))
         ((wmv warnings rest rest-sizes)
          (vl-exprlist-to-svex-selfdet
           (cdr x) conf)))
      (mv warnings (cons first rest)
          (cons size1 rest-sizes))))
  ///
  (local (in-theory (disable vl-expr-to-svex-vector
                             vl-expr-to-svex-transparent
                             vl-expr-to-svex-opaque
                             vl-index-expr-to-svex
                             vl-funcall-to-svex
                             vl-expr-to-svex-datatyped
                             vl-assignpat-to-svex
                             vl-array-assignpat-to-svex
                             vl-struct-assignpat-keyval-resolve
                             vl-struct-assignpat-to-svex
                             vl-exprlist-to-svex-datatyped
                             vl-exprlist-to-svex-selfdet
                             )))

  (with-output :off (event)
    (verify-guards vl-expr-to-svex-selfdet
      :hints (("goal" :do-not-induct t)
              (and stable-under-simplificationp
                   '(:expand ((vl-datatypelist-resolved-p types)
                              (vl-structmemberlist-resolved-p membs)
                              (vl-expr-opacity x))
                     :in-theory (enable acl2::natp-when-maybe-natp))))
      :guard-debug t
      :otf-flg t))

  (local (in-theory (disable len)))

  (deffixequiv-mutual vl-expr-to-svex
    :hints ((acl2::just-expand-mrec-default-hint 'vl-expr-to-svex-selfdet id t world)
            '(:do-not-induct t))))


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




(define vl-expr-to-svex-lhs ((x vl-expr-p)
                             (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (sv::lhs-p svex)
                          (sv::svarlist-addr-p (sv::lhs-vars svex))))
               (type (and (vl-maybe-datatype-p type)
                          (implies type
                                   (vl-datatype-resolved-p type)))))
  (b* ((warnings nil)
       ((wmv warnings svex type)
        (vl-expr-case x
          :vl-index (vl-index-expr-to-svex x conf)
          :vl-concat (b* (((wmv warnings svex size)
                           (vl-expr-to-svex-selfdet x nil conf))
                          ((unless (posp size))
                           (mv warnings svex nil)))
                       (mv warnings svex
                           (make-vl-coretype :name :vl-logic
                                             :pdims (list (vl-range->packeddimension
                                                           (make-vl-range
                                                            :msb (vl-make-index (1- size))
                                                            :lsb (vl-make-index 0)))))))
          :otherwise (mv (fatal :type :vl-expr-to-svex-fail
                                :msg "Bad LHS expression: ~a0"
                                :args (list (vl-expr-fix x)))
                         (svex-x) nil)))
       ((unless type)
        (mv warnings nil type))
       ((mv err size) (vl-datatype-size type))
       ((when (or err (not size)))
        ;; (break$)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't size the datatype ~a0 of ~
                                    LHS expression ~a1: ~@2"
                   :args (list type (vl-expr-fix x) err))
            nil nil))
       (lhssvex (sv::svex-concat size
                                   (sv::svex-lhsrewrite svex 0 size)
                                   (sv::svex-z)))
       ((unless (sv::lhssvex-p lhssvex))
        (mv (fatal :type :vl-expr->svex-lhs-fail
                   :msg "Not a supported LHS expression: ~a0"
                   :args (list (vl-expr-fix x)))
            nil nil)))
    (mv warnings (sv::svex->lhs lhssvex) type))
  ///
  (defret vl-expr-to-svex-lhs-type-size-ok
    (implies type
             (not (mv-nth 0 (vl-datatype-size type))))
    :hints(("Goal" :in-theory (enable vl-datatype-size)))))





(define vl-expr-to-svex-maybe-typed ((x vl-expr-p)
                                     (type vl-maybe-datatype-p)
                                     (conf vl-svexconf-p))
  :guard (or (not type) (vl-datatype-resolved-p type))
  :guard-debug t
  :guard-hints (("goal" :in-theory (enable vl-maybe-datatype-p)))
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (sv::svex-p svex)
                          (sv::svarlist-addr-p (sv::svex-vars svex))))
               (res-type (and (vl-maybe-datatype-p res-type)
                              (and (implies res-type
                                            (vl-datatype-resolved-p res-type)))))
               (res-size maybe-natp :rule-classes :type-prescription))
  (b* ((type (vl-maybe-datatype-fix type)))
    (if type
        (b* (((mv warnings svex) (vl-expr-to-svex-datatyped x nil type conf))
             ((mv err size) (vl-datatype-size type))
             ((when (or err (not size)))
              (mv (warn :type :vl-expr-to-svex-fail
                        :msg "Datatype ~a0 for expression ~a1 couldn't be sized: ~@0"
                        :args (list type (vl-expr-fix x)
                                    (or err "unsizable")))
                  svex
                  (and (mbt (vl-datatype-resolved-p type)) type)
                  nil)))
          (mv warnings svex
              (and (mbt (vl-datatype-resolved-p type)) type)
              size))
      (vl-expr-to-svex-untyped x conf))))


(define vl-upperlower-to-bitlist ((upper integerp)
                                  (lower integerp)
                                  (width natp))
  :returns (res vl-bitlist-p "MSB-first")
  (b* (((when (zp width)) nil)
       (width (1- width))
       (bit (if (logbitp width upper)
                (if (logbitp width lower)
                    :vl-1val
                  :vl-xval)
              (if (logbitp width lower)
                  :vl-zval
                :vl-0val))))
    (cons bit (vl-upperlower-to-bitlist upper lower width)))
  ///
  (defret consp-of-vl-upperlower-to-bitlist
    (equal (consp res)
           (posp width))))

(define vl-4vec-to-value ((x sv::4vec-p)
                          (width posp)
                          &key
                          ((signedness vl-exprsign-p) ':vl-signed))
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (in-theory (disable unsigned-byte-p acl2::loghead)))
             (local (defthm 4vec->lower-of-4vec-zero-ext
                      (implies (natp n)
                               (unsigned-byte-p n (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x))))
                      :hints(("Goal" :in-theory (e/d (sv::2vec-p sv::2vec sv::2vec->val sv::4vec-zero-ext))))))
             (local (defthm 4vec->lower-of-4vec-zero-ext-bounds
                      (implies (natp n)
                               (and (<= 0 (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x)))
                                    (< (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x)) (expt 2 n))))
                      :hints(("Goal" :use 4vec->lower-of-4vec-zero-ext
                              :in-theory (e/d (unsigned-byte-p)
                                              (4vec->lower-of-4vec-zero-ext)))))))
  :returns (val vl-value-p)
  (b* ((width (lposfix width))
       (trunc (sv::4vec-zero-ext (sv::2vec width) x))
       ((when (sv::2vec-p trunc))
        (b* ((val (sv::2vec->val trunc)))
          (make-vl-constint :origwidth width
                            :origsign signedness
                            :wasunsized t
                            :value val)))
       (val (vl-upperlower-to-bitlist (sv::4vec->upper trunc)
                                      (sv::4vec->lower trunc)
                                      width)))
    (make-vl-weirdint :bits val
                      :origsign signedness
                      :wasunsized t)))




(define vl-expr-consteval ((x vl-expr-p)
                           (conf vl-svexconf-p)
                           &key
                           ((ctxsize maybe-natp) 'nil))
  :short "Return an expression equivalent to @('x'), resolved to a constant value if possible."
  :long "<p>Works on vector expressions (including packed arrays/structs/unions).</p>

<p>At the moment, it only works if the expression evaluates to something
2-valued, i.e., no Xes or Zs.</p>"
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-expr-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-expr-fix x))))))
  (b* ((warnings nil)
       ((wmv warnings svex size)
        (vl-expr-to-svex-selfdet x ctxsize conf))
       ((vl-svexconf conf))
       ((wmv warnings signedness) (vl-expr-typedecide x conf.ss conf.typeov))
       ((when (or (vl-some-warning-fatalp warnings)
                  (not size)
                  (eql size 0)))
        (mv warnings nil (vl-expr-fix x)))
       (svex (sv::svex-reduce-consts svex))
       (val (sv::svex-case svex
              :quote svex.val
              :otherwise nil))
       ((unless val)
        (mv warnings nil (vl-expr-fix x)))
       (new-x (make-vl-literal :val (vl-4vec-to-value val size
                                                      :signedness (or signedness :vl-signed)))))
    (mv warnings t new-x)))

(define vl-exprlist-consteval ((x vl-exprlist-p)
                               (conf vl-svexconf-p))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-exprlist-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-exprlist-fix x))))
                      :hints (("goal" :induct t)
                              (and stable-under-simplificationp
                                   '(:expand ((vl-exprlist-fix x)))))))
  :verify-guards nil
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil nil))
       ((wmv warnings changedp1 new-x1) (vl-expr-consteval (car x) conf))
       ((wmv warnings changedp2 new-x2) (vl-exprlist-consteval (cdr x) conf))
       (changedp (or changedp1 changedp2)))
    (mv warnings
        changedp
        (mbe :logic (cons new-x1 new-x2)
             :exec (if changedp
                       (cons new-x1 new-x2)
                     x))))
  ///
  (verify-guards vl-exprlist-consteval)
  (defret len-of-vl-exprlist-consteval
    (equal (len new-x)
           (len x))))
