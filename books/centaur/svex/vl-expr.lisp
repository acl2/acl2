; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/mlib/selfsize" :dir :system)
(include-book "centaur/vl/mlib/typedecide" :dir :system)
(include-book "lattice")
(include-book "svmods")
(include-book "svex-rewrite-base")
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(defxdoc vl-expr-svex-translation
  :parents (vl-design->svex-design)
  :short "Compilation from (sized) @(see vl::vl) expressions into @(see svex)
expressions."

  :long "<p>The top-level function for converting a VL expression into a @(see
svex) expression is @(see vl-expr->svex).</p>

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


(defxdoc svex::vl-expr.lisp :parents (vl-expr-svex-translation))

(local (xdoc::set-default-parents svex::vl-expr.lisp))

(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))


(local (in-theory (disable member-equal append
                           acl2::member-of-cons
                           true-listp len
                           vl-warninglist-p-when-subsetp-equal
                           acl2::list-fix-when-len-zero
                           svex::svarlist-addr-p-when-not-consp
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







(define svex-x ()
  :returns (svex svex::svex-p)
  :short "Infinite width X"
  (svex::svex-quote (svex::4vec-x)))


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
  :returns (val svex::4vec-p)
  (let ((lsb-bits (rev (vl-bitlist-fix msb-bits))))
    (svex::4vec (vl-bitlist->onset lsb-bits)
                (lognot (vl-bitlist->offset lsb-bits)))))

(define svex-int ((x integerp))
  :short "convenient abbreviation"
  :returns (sv svex::svex-p)
  (svex::svex-quote (svex::2vec x))
  ///
  (defthm svex-eval-of-svex-int
    (equal (svex::svex-eval (svex-int x) env)
           (svex::2vec x)))
  
  (defthm vars-of-svex-int
    (equal (svex::svex-vars (svex-int x)) nil)))

(define svex-extend ((type vl-exprtype-p)
                     (width natp)
                     (x svex::svex-p))
  :parents (vl-expr->svex)
  :short "Returns an svex representing the sign- or zero-extension of x at the given width."

  :long "<p>We don't have to extend/truncate operands when translating VL
expressions like @('a & b'), but we do need to do it to the inputs of
expressions like @('a < b'), to chop off any garbage in the upper bits.</p>"

  :returns (sv svex::svex-p)
  (b* ((extend (if (eq (vl-exprtype-fix type) :vl-signed) 'svex::signx 'svex::zerox))
       (width (lnfix width))
       ((when (eq (svex::svex-kind x) :quote))
        (svex::svex-quote
         (if (eq (vl-exprtype-fix type) :vl-signed)
             (svex::4vec-sign-ext (svex::2vec width) (svex::svex-quote->val x))
           (svex::4vec-zero-ext (svex::2vec width) (svex::svex-quote->val x))))))
    (svex::make-svex-call :fn extend :args (list (svex-int width) x)))
  ///
  (defthm svex-vars-of-svex-extend
    (implies (not (member v (svex::svex-vars x)))
             (not (member v (svex::svex-vars (svex-extend type width x)))))))

#!svex
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


#!svex
(defines svex-reduce-consts
  :verify-guards nil
  (define svex-reduce-consts ((x svex-p))
    :returns (new-x svex-p)
    :measure (svex-count x)
    (svex-case x
      :call (b* ((args (svexlist-reduce-consts x.args))
                 (args-eval (svexlist-xeval args))
                 (res (svex-apply x.fn args-eval)))
              (if (or (2vec-p res)
                      (svexlist-variable-free-p args))
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

  (local (defthm svex-eval-call-when-2vec-p-of-minval
           (implies (and (syntaxp (not (equal env ''nil)))
                         (2vec-p (svex-apply fn (svexlist-eval args nil))))
                    (equal (svex-apply fn (svexlist-eval args env))
                           (svex-apply fn (svexlist-eval args nil))))
           :hints (("goal" :use ((:instance svex-eval-when-2vec-p-of-minval
                                  (n (svex-call fn args))))))))
           

  (defthm-svex-reduce-consts-flag
    (defthm svex-reduce-consts-correct
      (equal (svex-eval (svex-reduce-consts x) env)
             (svex-eval x env))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable svex-eval-when-2vec-p-of-minval
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

;; #!svex
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
               (svex svex::svex-p))
  (vl-value-case x
    :vl-constint (mv nil (svex-extend x.origtype x.origwidth (svex-int x.value)))
    :vl-weirdint (mv nil (svex-extend x.origtype (len x.bits)
                                      (svex::svex-quote (vl-bitlist->4vec (vl-weirdint->bits x)))))
    :vl-extint   (mv nil (case x.value
                           (:vl-1val (svex-int -1))
                           (:vl-0val (svex-int 0))
                           (:vl-xval (svex-x))
                           (:vl-zval (svex::svex-quote (svex::4vec-z)))))
    :vl-string   (mv nil (svex-int (vl-string->bits x.value (length x.value))))
    :otherwise   (mv (vmsg "Unsupported value type: ~a0" (make-vl-value :val x))
                     (svex-x)))
  ///
  (defret vars-of-vl-value-to-svex
    (not (member v (svex::svex-vars svex)))))

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
  :returns (name svex::name-p
                 :hints(("Goal" :in-theory (enable svex::name-p))))
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
                                 (path svex::path-p))
  :guard (equal (vl-seltrace-unres-count x) 0)
  :guard-hints (("goal" :in-theory (enable vl-seltrace-unres-count)))
  :returns (new-path svex::path-p)
  (if (atom x)
      (svex::path-fix path)
    (vl-seltrace-add-to-path
     (cdr x)
     (svex::make-path-scope
      :namespace (vl-selstep->svex-name (car x))
      :subpath path))))

(define vl-seltrace-to-path ((x vl-seltrace-p)
                             (path (or (not path)
                                       (svex::path-p path))))
  :short "Turns a seltrace object into an svex path."
  :long "<p>Note: This isn't the end of the story; we still need to deal with
e.g. bitselects, partselects, and nonconstant array selects.</p>"
  :returns (new-path (implies new-path (svex::path-p new-path))
                     "Empty indicates the seltrace was empty, as in just a bare
                      variable.")
  :guard (equal (vl-seltrace-unres-count x) 0)
  :guard-hints (("goal" :in-theory (enable vl-seltrace-unres-count)))
  (b* (((when (atom x))
        (and path (svex::path-fix path)))
       (path1 (if path
                  (svex::make-path-scope
                   :namespace (vl-selstep->svex-name (car x))
                   :subpath path)
                (svex::make-path-wire :name (vl-selstep->svex-name (car x))))))
    (vl-seltrace-add-to-path (cdr x) path1)))
  
(define vl-hidstep-resolved-p ((x vl-hidstep-p))
  :short "Checks that the index, if any, is resolved, and that the item has a name."
  (b* (((vl-hidstep x)))
    (or (not x.index) (vl-expr-resolved-p x.index))))

(define vl-hidstep->svex-index ((x vl-hidstep-p))
  :guard (vl-hidstep-resolved-p x)
  :guard-hints(("Goal" :in-theory (enable vl-hidstep-resolved-p)))
  :returns (index (implies index (svex::name-p index))
                 :hints(("Goal" :in-theory (enable svex::name-p))))
  (b* (((vl-hidstep x)))
    (and x.index (vl-resolved->val x.index))))

(define vl-hidtrace-resolved-p ((x vl-hidtrace-p))
  (if (atom x)
      t
    (and (vl-hidstep-resolved-p (car x))
         (vl-hidtrace-resolved-p (cdr x)))))


(define vl-hidtrace-add-to-path ((x vl-hidtrace-p)
                                 (path svex::path-p))
  :guard (vl-hidtrace-resolved-p x)
  :returns (new-path svex::path-p)
  :guard-hints (("goal" :in-theory (enable vl-hidtrace-resolved-p svex::name-p)))
  (if (atom x)
      (svex::path-fix path)
    (vl-hidtrace-add-to-path
     (cdr x)
     (b* ((idx (vl-hidstep->svex-index (car x)))
          (idxpath (if idx
                       (svex::make-path-scope :namespace idx :subpath path)
                     path)))
       (svex::make-path-scope
        :namespace (vl-hidstep->name (car x))
        :subpath idxpath)))))

(define vl-hidtrace-to-path ((x vl-hidtrace-p)
                             (path (or (not path)
                                       (svex::path-p path))))
  :guard (and (consp x)
              (vl-hidtrace-resolved-p x))
  :guard-hints (("goal" :in-theory (enable vl-hidtrace-resolved-p
                                           svex::name-p)))
  :returns (new-path svex::path-p)
  (if path
      (vl-hidtrace-add-to-path x path)
    (vl-hidtrace-add-to-path
     (cdr x)
     ;; NOTE: using the fact that the last element in a hid trace produced by
     ;; follow-hid has no index -- vl-follow-hidexpr-no-index-on-first
     (svex::make-path-wire :name (vl-hidstep->name (car x))))))

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
              (:vl-genarrayblock (mv nil 2))
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
                                 (path svex::path-p))
  :short "Create an svex address from a path, based on which scope the scopecontext
          object indicates."
  :long "<p>Svex supports three kinds of addresses -- see @(see svex::address)
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
               (addr (and (implies (not err) (svex::address-p addr))
                          (implies addr (svex::address-p addr)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svex::name-p))))
  (vl-scopecontext-case x
    :local (b* (((mv err levels)
                 (vl-upscope-to-svex-upscope x.levels ss))
                ((when err) (mv err nil)))
             (mv nil
                 (svex::make-address
                  :path path
                  :scope levels)))
    :root  (mv nil
               (svex::make-address :path path :scope :root))
    :package (mv (vmsg "Package-scoped variables aren't yet supported")
                 (svex::make-address :scope :root
                                     :path (svex::make-path-scope
                                            :namespace (vl-package->name x.pkg)
                                            :subpath path)))
    :module (mv (vmsg "Module-scoped variables aren't yet supported")
                (svex::make-address :scope :root
                                    :path (svex::make-path-scope
                                           :namespace (vl-module->name x.mod)
                                           :subpath path)))))

(define vl-seltrace-type/ss ((x vl-seltrace-p)
                             (opinfo vl-operandinfo-p))
  :guard (and (vl-seltrace-usertypes-ok x)
              (vl-operandinfo-usertypes-ok opinfo))
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-usertypes-ok)))
  :returns (mv (type vl-datatype-p)
               (ss vl-scopestack-p))
  (if (consp x)
      (b* (((vl-selstep sel) (car x)))
        (mv sel.type sel.ss))
    (b* ((hid (car (vl-operandinfo->hidtrace opinfo)))
         ((vl-hidstep hid)))
      (mv (vl-vardecl->type hid.item) hid.ss)))
  ///
  (std::defret usertypes-ok-of-vl-seltrace-type/ss
    (implies (and (vl-seltrace-usertypes-ok x)
                  (vl-operandinfo-usertypes-ok opinfo))
             (not (vl-datatype-check-usertypes type ss)))
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
               (svar (implies (not err) (svex::svar-p svar))))
  (b* (((vl-operandinfo opinfo))
       (path1 (vl-seltrace-to-path x nil))
       (path (vl-hidtrace-to-path opinfo.hidtrace path1))
       ((mv err addr)
        (vl-scopecontext-to-addr opinfo.context outer-ss path))
       ((when err) (mv err nil)))
    (mv nil (svex::make-svar :name addr)))
  ///
  (defret vars-of-vl-seltrace-to-svar
    (implies (not err)
             (svex::svar-addr-p svar))
    :hints(("Goal" :in-theory (enable svex::svar-addr-p)))))

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
               (svex svex::svex-p))
  (b* (((mv err svar) (vl-seltrace-to-svar x opinfo outer-ss))
       ((when err) (mv err (svex-x))))
    (mv nil (svex::make-svex-var :name svar)))
  ///
  (defret vars-of-vl-seltrace-to-svex-var
    (svex::svarlist-addr-p (svex::svex-vars svex))))

(define vl-datatype-index-is-bitselect ((x vl-datatype-p)
                                        (ss vl-scopestack-p))
  ;; This doesn't check for the error if e.g. we apply an index to a 1-bit
  ;; coretype with no pdims.
  :guard (not (vl-datatype-check-usertypes x ss))
  (b* (((mv x ss) (vl-maybe-usertype-resolve x ss))
       (udims (vl-datatype->udims x))
       (pdims (vl-datatype->pdims x))
       ((when (consp udims)) nil)
       ((when (atom pdims))
        ;; It's a bitselect if we have a packed type.
        (vl-datatype-packedp x ss))
       ;; Now get the type after indexing in once.
       (x-minus-1d (vl-datatype-update-pdims (cdr pdims) x))
       ((mv x-minus-1d ?ss) (vl-maybe-usertype-resolve x-minus-1d ss)))
    ;; We now have a bitselect only if the base type is a 1-bit coretype with no dims.
    (and (atom (vl-datatype->pdims x-minus-1d))
         (atom (vl-datatype->udims x-minus-1d))
         (vl-datatype-case x-minus-1d
           :vl-coretype (b* (((vl-coredatatype-info xinfo)
                              (vl-coretypename->info x-minus-1d.name)))
                          (eql xinfo.size 1))
           :otherwise nil))))

(define vl-structmemberlist-shift-bits ((x vl-structmemberlist-p)
                                        (field stringp)
                                        (ss vl-scopestack-p))
  ;; NOTE: x should be REVERSED from the normal order here.
  :guard (not (vl-structmemberlist-check-usertypes x ss :rec-limit 1000))
  :verify-guards nil
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (natp shift)) :rule-classes :type-prescription))
  (b* ((field (string-fix field))
       ((when (atom x))
        (mv (vmsg "Field not found: ~s0" field) nil))
       ((vl-structmember x1) (car x))
       ((when (equal x1.name field)) (mv nil 0))
       ((mv err size) (vl-datatype-size x1.type ss))
       ((when err) (mv err nil))
       ((unless size) (mv (vmsg "Couldn't size struct member type: ~a0" x1.type) nil))
       ((mv err rest) (vl-structmemberlist-shift-bits (cdr x) field ss))
       ((when err) (mv err nil)))
    (mv nil (+ size rest)))
  ///
  (verify-guards vl-structmemberlist-shift-bits
    :hints (("goal" :in-theory (enable vl-structmemberlist-check-usertypes)))))

(define vl-datatype-field-shift-amount ((x vl-datatype-p)
                                        (field stringp)
                                        (ss vl-scopestack-p))
  :guard (not (vl-datatype-check-usertypes x ss))
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (integerp shift)) :rule-classes :type-prescription))
  :prepwork ((local (defthm vl-structmemberlist-check-usertypes-of-structmembers
                      (implies (and (not (vl-datatype-check-usertypes x ss))
                                    (vl-datatype-case x :vl-struct))
                               (not (vl-structmemberlist-check-usertypes
                                     (vl-struct->members x) ss :rec-limit 1000)))
                      :hints (("goal" :expand ((vl-datatype-check-usertypes x ss)))))))
  (b* ((field (string-fix field))
       ((mv x ss) (vl-maybe-usertype-resolve x ss))
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
      :vl-struct (vl-structmemberlist-shift-bits x.members field ss)
      :otherwise (mv (vmsg "Can't select field ~s0 from non-struct/union datatype ~a1"
                           field x)
                     nil))))


(define vl-datatype-index-shift-amount ((x vl-datatype-p)
                                        (idx svex::svex-p)
                                        (ss vl-scopestack-p))
  :guard (not (vl-datatype-check-usertypes x ss))
  :returns (mv (err (iff (vl-msg-p err) err))
               (shift (implies (not err) (svex::svex-p shift))))
  (b* (((mv x ss) (vl-maybe-usertype-resolve x ss))
       ((mv err ?caveat slottype dim slotss) (vl-datatype-remove-dim x ss))
       ((when err) (mv err nil))
       ((mv err size) (vl-datatype-size slottype slotss))
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
        (mv nil (svex::svex-reduce-consts
                 (svex::svcall * (svex-int size)
                               (svex::svcall svex::b- idx (svex-int lsb)))))))
    (mv nil (svex::svex-reduce-consts
             (svex::svcall * (svex-int size)
                           (svex::svcall svex::b- (svex-int lsb) idx)))))
  ///
  (defret vars-of-vl-datatype-index-shift-amount
    (implies (and (not err)
                  (not (member v (svex::svex-vars idx))))
             (not (member v (svex::svex-vars shift))))))


#!svex
(define 4vec-lsb-shift ((shift-amt 4vec-p)
                        (x 4vec-p))
  :returns (res 4vec-p)
  (if (2vec-p shift-amt)
      (b* ((sh (2vec->val shift-amt)))
        (if (< sh 0)
            (4vec-concat (2vec (- sh)) (4vec-x) x)
          (4vec-rsh (2vec sh) x)))
    (4vec-x)))
  
#!svex
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
      :otherwise (b* ((concat-amt (svcall ?
                                                (svcall < sh (vl::svex-int 0))
                                                (svcall u- sh)
                                                (vl::svex-int 0)))
                      (rsh-amt    (svcall ?
                                                (svcall < sh (vl::svex-int 0))
                                                (vl::svex-int 0)
                                                sh)))
                   (svcall concat
                                 concat-amt
                                 (svex-x)
                                 (svcall rsh rsh-amt x)))))
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





(define vl-seltrace-to-svex-vector
  ((x vl-seltrace-p)
   (indices svex::svexlist-p)
   (unres-count natp)
   (opinfo vl-operandinfo-p
           "The full operandinfo of which the seltrace is a part.")
   (outer-ss vl-scopestack-p))
  :guard (and (vl-seltrace-usertypes-ok x)
              (vl-operandinfo-usertypes-ok opinfo)
              (equal (len indices)
                     (vl-seltrace-index-count x))
              (equal unres-count (vl-seltrace-unres-count x))
              (vl-hidtrace-resolved-p (vl-operandinfo->hidtrace opinfo)))
  :verify-guards nil
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex svex::svex-p))
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
  (b* ((resolved-p (mbe :logic (equal (vl-seltrace-unres-count x) 0)
                        :exec (eql unres-count 0)))

       ((mv type type-ss) (vl-seltrace-type/ss x opinfo))
       ((mv err size) (vl-datatype-size type type-ss))
       ((when err) (mv err (svex-x)))
       ((unless size) (mv (vmsg "Could not size datatype ~s0" type) (svex-x)))
       
       ((when resolved-p)
        (b* (((mv err svex-var)
              (vl-seltrace-to-svex-var x opinfo outer-ss))
             ((when err) (mv err (svex-x))))
          (mv nil (svex::svcall svex::concat (svex-int size) svex-var (svex-x)))))
             

       ;; Unres-count nonzero implies (consp x)
       ((vl-selstep step) (car x))

       

       ((mv rest-type rest-ss) (vl-seltrace-type/ss (cdr x) opinfo))
       ((mv rest-type rest-ss) (vl-maybe-usertype-resolve rest-type rest-ss))

       ((mv err shift-amt)
        (vl-select-case step.select
          :field (b* (((mv err idx)
                       (vl-datatype-field-shift-amount rest-type step.select.name rest-ss))
                      ((when err) (mv err idx)))
                   (mv nil (svex-int idx)))
          :index (vl-datatype-index-shift-amount rest-type (car indices) rest-ss)))
       ((when err) (mv err (svex-x)))

       ((mv err rest) (vl-seltrace-to-svex-vector
                       (cdr x)
                       (vl-select-case step.select
                         :field indices
                         :index (cdr indices))
                       (if (vl-select-resolved-p step.select)
                           unres-count
                         (1- (lnfix unres-count)))
                       opinfo
                       outer-ss))
       ((when err) (mv err (svex-x))))
    (mv err (svex::svcall svex::concat (svex-int size)
                          (svex::svex-lsb-shift shift-amt rest)
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
    (implies (svex::svarlist-addr-p (svex::svexlist-vars indices))
             (svex::svarlist-addr-p (svex::svex-vars svex)))
    :hints(("Goal" :in-theory (enable vl-seltrace-to-svex-vector)))))


(define vl-operandinfo-to-svex-preproc ((x vl-operandinfo-p)
                                        (indices svex::svexlist-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (new-x vl-operandinfo-p)
               (new-indices svex::svexlist-p))
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
  (b* ((indices (svex::svexlist-fix indices))
       ((vl-operandinfo x) (vl-operandinfo-fix x)))
    (vl-partselect-case x.part
      :none (b* (((when (atom x.seltrace)) ;; no selects so no bitselect
                  (mv nil x indices))
                 ((vl-selstep sel1) (car x.seltrace))
                 ((unless (vl-select-case sel1.select :index))
                  ;; final select is a field access, so not a bitselect
                  (mv nil x indices))
                 ((mv type type-ss) (vl-seltrace-type/ss (cdr x.seltrace) x))
                 ((unless (vl-datatype-index-is-bitselect type type-ss))
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
                  (list* (svex::svex-fix bitselect-index) (svex-int 1) rest-indices)))
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
    (implies (not (member v (svex::svexlist-vars indices)))
             (not (member v (svex::svexlist-vars new-indices))))))

  
  


(define vl-operandinfo-to-svex ((x vl-operandinfo-p)
                                (indices svex::svexlist-p)
                                (ss vl-scopestack-p))
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
  :guard-hints (("goal" :in-theory (enable vl-operandinfo-index-count)))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex svex::svex-p))
  (b* (((mv err x indices) (vl-operandinfo-to-svex-preproc x indices))
       ((when err) (mv err (svex-x)))
       ((vl-operandinfo x))
       ((unless (vl-hidtrace-resolved-p x.hidtrace))
        (mv (vmsg "Unresolved hid indices") (svex-x)))
       ((when (vl-partselect-case x.part :none))
        ;; Bitselect was taken care of by preproc.  Just remains to convert the seltrace.
        (vl-seltrace-to-svex-vector x.seltrace indices
                                    (vl-seltrace-unres-count x.seltrace)
                                    x ss))
       ((vl-plusminus->partselect x.part))
       ((mv err baseexpr)
        (vl-seltrace-to-svex-vector x.seltrace (cddr indices)
                                    (vl-seltrace-unres-count x.seltrace)
                                    x ss))
       ((when err) (mv err (svex-x)))
       ((mv arrtype arrtype-ss) (vl-seltrace-type/ss x.seltrace x))
       ((mv err ?caveat ?basetype dim ?basess) (vl-datatype-remove-dim arrtype arrtype-ss))
       ((when err) (mv err (svex-x)))
       ((when (vl-packeddimension-case dim :unsized))
        (mv (vmsg "Unsized dimension") (svex-x)))
       ((vl-range dimrange) (vl-packeddimension->range dim))
       ((unless (vl-range-resolved-p dimrange))
        (mv (vmsg "Unresolved dimension") (svex-x)))
       (dim-msb (vl-resolved->val dimrange.msb))
       (dim-lsb (vl-resolved->val dimrange.lsb))
       (downp (<= dim-lsb dim-msb))
       ((list base-svex width-svex) indices)
       (sel-lsb (if downp
                    (if x.part.minusp
                        ;; base is the msb, compute the lsb
                        (svex::svcall + base-svex
                                      (svex::svcall + (svex-int 1)
                                                    (svex::svcall svex::u- width-svex)))
                      ;; base is the lsb
                      base-svex)
                  (if x.part.minusp
                      base-svex
                    ;; base is the msb, compute the lsb
                    (svex::svcall + base-svex
                                  (svex::svcall + (svex-int -1) width-svex)))))
       ((mv err shift-amt)
        (vl-datatype-index-shift-amount arrtype sel-lsb arrtype-ss))
       ((when err) (mv err (svex-x)))

       ((mv err size) (vl-datatype-size x.type x.ss))
       ((when err) (mv err (svex-x)))
       ((unless size)
        (mv (vmsg "Unsizable datatype ~a0" x.type) (svex-x))))

    (mv nil
        (svex::svex-reduce-consts
         (svex::svcall svex::concat
                       (svex-int size)
                       (svex::svex-lsb-shift shift-amt baseexpr)
                       (svex-x)))))
  ///
  
  (local (defthm member-svex-vars-of-car
           (implies (not (member v (svex::svexlist-vars x)))
                    (not (member v (svex::svex-vars (car x)))))
           :hints(("Goal" :in-theory (enable svex::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cadr
           (implies (not (member v (svex::svexlist-vars x)))
                    (not (member v (svex::svex-vars (cadr x)))))
           :hints(("Goal" :in-theory (enable svex::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cdr
           (implies (not (member v (svex::svexlist-vars x)))
                    (not (member v (svex::svexlist-vars (cdr x)))))
           :hints(("Goal" :in-theory (enable svex::svexlist-vars)))))


  (local (in-theory (disable len consp-by-len member-equal)))

  (defret vars-of-vl-operandinfo-to-svex
    (implies (svex::svarlist-addr-p (svex::svexlist-vars indices))
             (svex::svarlist-addr-p (svex::svex-vars svex)))))








(define vl-simple-id-name ((x vl-scopeexpr-p))
  :short "If x is a simple name with no scoping, return the name, otherwise nil."
  :returns (name maybe-stringp :rule-classes :type-prescription)
  (vl-scopeexpr-case x
    :end (vl-hidexpr-case x.hid
           :end x.hid.name
           :otherwise nil)
    :otherwise nil)
  ///
  (defret stringp-of-vl-simple-id-name
    (iff (stringp name) name)))


(define vl-$bits-call-to-svex ((x vl-expr-p)
                               (ss vl-scopestack-p))
  :guard (vl-expr-case x :vl-call)
  :returns (mv (warnings vl-warninglist-p)
               (svex svex::svex-p))
  (b* (((vl-call x) (vl-expr-fix x))
       (warnings nil)
       ((when x.typearg)
        (b* (((when (consp x.args))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Too many arguments to ~a0"
                         :args (list x))
                  (svex-x)))
             ((mv err size) (vl-datatype-size x.typearg ss))
             ((when (or err (not size)))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Couldn't size datatype in ~a0: ~@1"
                         :args (list x (or err "unsizable datatype")))
                  (svex-x))))
          (mv (ok) (svex-int size))))
       ((when (< (len x.args) 1))
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Need an argument in ~a0"
                   :args (list x))
            (svex-x)))
       ((when (> (len x.args) 1))
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Too many arguments in ~a0"
                   :args (list x))
            (svex-x)))
       ((mv warnings size) (vl-expr-selfsize x ss))
       ((unless size)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't size expression in ~a0"
                   :args (list x))
            (svex-x))))
    (mv (ok) (svex-int size)))
  ///
  (defret vars-of-vl-$bits-call-to-svex
    (svex::svarlist-addr-p (svex::svex-vars svex))))


(define vl-function-pair-inputs-with-actuals ((inputs vl-portdecllist-p)
                                              (args svex::svexlist-p))
  :guard (equal (len inputs) (len args))
  :returns (sigma svex::svex-alist-p)
  :guard-hints (("goal" :in-theory (enable svex::name-p)))
  (if (atom inputs)
      nil
    (cons (cons #!svex
                (make-svar
                 :name (make-address
                        :path (make-path-wire
                               :name #!vl (vl-portdecl->name (car inputs)))))
                (svex::svex-fix (car args)))
          (vl-function-pair-inputs-with-actuals (cdr inputs) (cdr args))))
  ///
  (more-returns
   (sigma :name vars-of-vl-function-pair-inputs-with-actuals
          (implies (not (member v (svex::svexlist-vars args)))
                   (not (member v (svex::svex-alist-vars sigma))))
          :hints(("Goal" :in-theory (enable svex::svex-alist-vars))))))


(fty::deflist vl-datatypelist :elt-type vl-datatype
  ///
  (defthm vl-datatypelist-fix-of-repeat
    (equal (vl-datatypelist-fix (repeat n x))
           (repeat n (vl-datatype-fix x)))
    :hints(("Goal" :in-theory (enable repeat)))))

(define vl-datatypelist-check-usertypes ((x vl-datatypelist-p)
                                         (ss vl-scopestack-p))
  :returns (err (iff (vl-msg-p err) err))
  (if (atom x)
      nil
    (or (vl-datatype-check-usertypes (car x) ss)
        (vl-datatypelist-check-usertypes (cdr x) ss)))
  ///
  (defthm vl-datatypelist-check-usertypes-of-repeat
    (implies (not (vl-datatype-check-usertypes x ss))
             (not (vl-datatypelist-check-usertypes (repeat n x) ss)))
    :hints(("Goal" :in-theory (enable repeat)))))

(defprojection vl-portdecllist->types ((x vl-portdecllist-p))
  :returns (types vl-datatypelist-p)
  (vl-portdecl->type x))

(defprojection vl-structmemberlist->types ((x vl-structmemberlist-p))
  :returns (types vl-datatypelist-p)
  (vl-structmember->type x)
  ///
  (defret vl-datatypelist-check-usertypes-of-vl-structmemberlist->types
    (implies (not (vl-structmemberlist-check-usertypes x ss :rec-limit 1000))
             (not (vl-datatypelist-check-usertypes types ss)))
    :hints(("Goal" :in-theory (enable vl-datatypelist-check-usertypes
                                      vl-structmemberlist-check-usertypes)))))


(local (in-theory (disable nfix)))

(define vl-unaryop-to-svex ((op vl-unaryop-p)
                            (arg svex::svex-p)
                            (arg-size natp)
                            (size natp)
                            (signedness vl-exprtype-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex svex::svex-p))
  (b* ((op (vl-unaryop-fix op))
       (body
        (case op
          (:vl-unary-plus   (svex::svex-fix arg))
          (:vl-unary-minus  (svex::svcall svex::u- arg))
          (:vl-unary-bitnot (svex::svcall svex::bitnot arg))
          (:vl-unary-lognot (svex::svcall svex::bitnot (svex::svcall svex::uor arg)))
          (:vl-unary-bitand (svex::svcall svex::uand   (svex::svcall svex::signx
                                                                     (svex-int (lnfix arg-size))
                                                                     arg)))
          (:vl-unary-nand   (svex::svcall svex::bitnot
                                          (svex::svcall svex::uand
                                                        (svex::svcall svex::signx
                                                                      (svex-int (lnfix arg-size))
                                                                      arg))))
          (:vl-unary-bitor  (svex::svcall svex::uor     arg))
          (:vl-unary-nor    (svex::svcall svex::bitnot  (svex::svcall svex::uor    arg)))
          (:vl-unary-xor    (svex::svcall svex::uxor    (svex::svcall svex::zerox
                                                                      (svex-int (lnfix arg-size))
                                                                      arg)))
          (:vl-unary-xnor   (svex::svcall svex::bitnot
                                          (svex::svcall svex::uxor
                                                        (svex::svcall svex::zerox
                                                                      (svex-int (lnfix arg-size))
                                                                      arg)))))))
    (mv (and (not body)
             (vmsg "Operator not implemented: ~s0" (vl-unaryop-string op)))
        (if body
            (svex-extend signedness size body)
          (svex-x))))
  ///
  (defret vars-of-vl-unaryop-to-svex
    (implies (not (member v (svex::svex-vars arg)))
             (not (member v (svex::svex-vars svex))))))

(define vl-binaryop-to-svex ((op vl-binaryop-p)
                             (left svex::svex-p)
                             (right svex::svex-p)
                             (left-size natp)
                             (right-size natp)
                             (size natp)
                             (signedness vl-exprtype-p))
  (declare (ignorable right-size))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex svex::svex-p))
  (b* ((op (vl-binaryop-fix op))
       (body
        (case op
          (:vl-binary-plus    (svex::svcall +            left right))
          (:vl-binary-minus   (svex::svcall svex::b-     left right))
          (:vl-binary-times   (svex::svcall *            left right))
          (:vl-binary-div     (svex::svcall /            left right))
          (:vl-binary-rem     (svex::svcall svex::%      left right))
          (:vl-binary-eq      (svex::svcall svex::==     left right))
          (:vl-binary-neq     (svex::svcall svex::bitnot (svex::svcall svex::==     left right)))
          (:vl-binary-ceq     (svex::svcall svex::==     left right))
          (:vl-binary-cne     (svex::svcall svex::bitnot (svex::svcall svex::==     left right)))
          (:vl-binary-wildeq  (svex::svcall svex::==?    left right))
          (:vl-binary-wildneq (svex::svcall svex::bitnot (svex::svcall svex::==?    left right)))
          (:vl-binary-logand  (svex::svcall svex::bitand (svex::svcall svex::uor    left)
                                                         (svex::svcall svex::uor    right)))
          (:vl-binary-logor   (svex::svcall svex::bitor  (svex::svcall svex::uor    left)
                                                         (svex::svcall svex::uor    right)))
          (:vl-binary-lt      (svex::svcall svex::<      left right))
          (:vl-binary-lte     (svex::svcall svex::bitnot (svex::svcall svex::<      right left)))
          (:vl-binary-gt      (svex::svcall svex::<      right left))
          (:vl-binary-gte     (svex::svcall svex::bitnot (svex::svcall svex::<      left right)))
          (:vl-binary-bitand  (svex::svcall svex::bitand left right))
          (:vl-binary-bitor   (svex::svcall svex::bitor  left right))
          (:vl-binary-xor     (svex::svcall svex::bitxor left right))
          (:vl-binary-xnor    (svex::svcall svex::bitnot (svex::svcall svex::bitxor left right)))
          (:vl-binary-shr     (svex::svcall svex::rsh
                                            right
                                            (svex::svcall svex::zerox
                                                          (svex-int (lnfix left-size))
                                                          left)))
          (:vl-binary-shl     (svex::svcall svex::lsh    right left))
          (:vl-binary-ashr    (svex::svcall svex::rsh    right left))
          (:vl-binary-ashl    (svex::svcall svex::lsh    right left))
          (:vl-implies        (svex::svcall svex::bitor
                                            (svex::svcall svex::bitnot
                                                          (svex::svcall svex::uor    left))
                                            (svex::svcall svex::uor    right)))
          (:vl-equiv          (svex::svcall svex::bitnot
                                            (svex::svcall svex::bitxor
                                                          (svex::svcall svex::uor    left)
                                                          (svex::svcall svex::uor    right))))
          (otherwise          nil))))
    (mv (and (not body)
             (vmsg "Operator not implemented: ~s0" (vl-binaryop-string op)))
        (if body
            (svex-extend signedness size body)
          (svex-x))))
  ///
  (defret vars-of-vl-binaryop-to-svex
    (implies (and (not (member v (svex::svex-vars left)))
                  (not (member v (svex::svex-vars right))))
             (not (member v (svex::svex-vars svex))))))


(define svex-concat-list-aux ((widths nat-listp "the widths of the expressions remaining in x")
                              (x svex::svexlist-p "the less-significant expressions, most-significant first")
                              (acc svex::svex-p "the final svex for the more-significant part"))
  :guard (eql (len widths) (len x))
  :guard-hints (("goal" :in-theory (enable len)))
  :returns (concat svex::svex-p)
  (if (atom x)
      (svex::svex-fix acc)
    (svex-concat-list-aux
     (cdr widths) (cdr x)
     (svex::svex-concat (car widths) (car x) acc)))
  ///
  (defthm vars-of-svex-concat-list-aux
    (implies (and (not (member v (svex::svexlist-vars x)))
                  (not (member v (svex::svex-vars acc))))
             (not (member v (svex::svex-vars (svex-concat-list-aux widths x
                                                                   acc)))))))

(define svex-concat-list ((widths nat-listp) (x svex::svexlist-p))
  ;; Because Verilog concats go MSB to LSB, we do this tail-recursively,
  ;; accumulating terms onto the MSBs.
  ;; x and widths are therefore both MSB-first.
  :guard (eql (len widths) (len x))
  :guard-hints (("goal" :in-theory (enable len)))
  :returns (concat svex::svex-p)
  (if (atom x)
      (svex-x) ;; no elements in the concat -- bad case
    (svex-concat-list-aux (cdr widths) (cdr x)
                          ;; This plays really nicely with the garbage convention: note
                          ;; that we don't have to fix this up at all.
                          (car x)))
  ///
  (defthm vars-of-svex-concat-list
    (implies (not (member v (svex::svexlist-vars x)))
             (not (member v (svex::svex-vars (svex-concat-list widths x)))))))


(define svex-repeat-aux ((n natp)
                         (width natp)
                         (x svex::svex-p)
                         (acc svex::svex-p))
  :returns (concat svex::svex-p)
  (if (zp n)
      (svex::svex-fix acc)
    (svex-repeat-aux (1- n) width x (svex::svex-concat (lnfix width) x acc)))
  ///
  (defret vars-of-svex-repeat-aux
    (implies (and (not (member v (svex::svex-vars x)))
                  (not (member v (svex::svex-vars acc))))
             (not (member v (svex::svex-vars concat))))))

(define svex-repeat ((n natp) (width natp) (x svex::svex-p))
  :returns (concat svex::svex-p)
  (if (zp n)
      (svex-x)
    (svex-repeat-aux (1- n) width x x))
  ///
  (defret vars-of-svex-repeat
    (implies (not (member v (svex::svex-vars x)))
             (not (member v (svex::svex-vars concat))))))

(define svex-multiconcat ((n natp) (x svex::svexlist-p) (widths nat-listp))
  :guard (eql (len x) (len widths))
  :returns (concat svex::svex-p)
  (svex-repeat n (sum-nats widths) (svex-concat-list widths x))
  ///
  (defret vars-of-svex-multiconcat
    (implies (not (member v (svex::svexlist-vars x)))
             (not (member v (svex::svex-vars concat))))))

(define vl-compare-datatypes ((a vl-datatype-p)
                              (a-ss vl-scopestack-p)
                              (b vl-datatype-p)
                              (b-ss vl-scopestack-p))
  :returns (err (iff (vl-msg-p err) err))
  (b* ((a (vl-datatype-fix a))
       (b (vl-datatype-fix b))
       (a-ss (vl-scopestack-fix a-ss))
       (b-ss (vl-scopestack-fix b-ss))
       ((unless (equal a b))
        (vmsg "Mismatching datatypes: ~a0, ~a1" a b))
       ((when (hons-equal a-ss b-ss))
        nil)
       ((unless (and (vl-datatype-case a :vl-usertype)
                     (vl-datatype-case b :vl-usertype)))
        (vmsg "Mismatching datatypes: ~a0, ~a1" a b))
       ((vl-usertype a))
       ((vl-usertype b))
       ;; BOZO could require this as guard with
       ;; (not (vl-datatype-check-usertypes ...))
       ((mv err a a-ss) (vl-usertype-resolve a.name a-ss))
       ((when err) err)
       ((mv err b b-ss) (vl-usertype-resolve b.name b-ss))
       ((when err) err))
    (if (and (equal a b)
             (hons-equal a-ss b-ss))
        nil
      (vmsg "Mismatching datatypes: ~a0, ~a1" a b))))




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
              :type (vmsg "Datatype key ~a0 not valid for array patterns" key.type)
              :default nil)))
    (or err
        (vl-check-array-assignpat-keys (cdr pairs) range))))

(fty::defalist vl-svex-keyvallist :key-type vl-patternkey :val-type svex::svex-p
  ///
  (defthm vl-svex-keyvallist-p-of-pairlis
    (implies (and (vl-keyvallist-p x)
                  (svex::svexlist-p vals)
                  (equal (len x) (len vals)))
             (vl-svex-keyvallist-p (pairlis$ (alist-keys x) vals)))
    :hints(("Goal" :in-theory (enable alist-keys vl-keyvallist-p pairlis$)
            :induct (pairlis$ x vals)))))

(define vl-svex-keyvallist-vars ((x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  (b* ((x (vl-svex-keyvallist-fix x)))
    (if (atom x)
        nil
      (append (svex::svex-vars (cdar x))
              (vl-svex-keyvallist-vars (cdr x)))))
  ///
  (defthm vl-svex-keyvallist-vars-of-pairlis$
    (implies (and (not (member v (svex::svexlist-vars vals)))
                  (equal (len keys) (len vals)))
             (not (member v (vl-svex-keyvallist-vars (pairlis$ keys vals)))))
    :hints(("Goal" :in-theory (enable pairlis$)))))

(define vl-svex-keyval-default-lookup ((x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  :returns (ans (implies ans (svex::svex-p ans)))
  (b* ((x (vl-svex-keyvallist-fix x))
       ((when (atom x)) nil)
       (key (caar x))
       ((when (vl-patternkey-case key :default)) (cdar x)))
    (vl-svex-keyval-default-lookup (cdr x)))
  ///
  (defret vars-of-vl-svex-keyval-default-lookup
    (implies (and ans
                  (not (member v (vl-svex-keyvallist-vars x))))
             (not (member v (svex::svex-vars ans))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))


(define vl-svex-keyval-index-lookup ((n natp)
                                     (x vl-svex-keyvallist-p))
  :measure (len (vl-svex-keyvallist-fix x))
  :returns (ans (implies ans (svex::svex-p ans)))
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
             (not (member v (svex::svex-vars ans))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))

(define vl-array-assignpat-keyval-resolve ((lsb natp)
                                           (msb natp)
                                           (x vl-svex-keyvallist-p))
  :measure (abs (- (nfix lsb) (nfix msb)))
  ;; BOZO only returning one of the errors...
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex-membs svex::svexlist-p
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
             (not (member v (svex::svexlist-vars svex-membs))))
    :hints(("Goal" :in-theory (enable vl-svex-keyvallist-vars)))))


(define vl-simple-idexpr-name ((x vl-expr-p))
  :returns (name (iff (stringp name) name))
  (vl-expr-case x
    :vl-index (and (vl-partselect-case x.part :none)
                   (atom x.indices)
                   (vl-simple-id-name x.scope))
    :otherwise nil))

(define vl-check-struct-assignpat-keys ((pairs vl-keyvallist-p)
                                        (membs vl-structmemberlist-p))
  :returns (err (iff (vl-msg-p err) err))
  :measure (vl-keyvallist-count pairs)
  (b* ((pairs (vl-keyvallist-fix pairs))
       ((when (atom pairs)) nil)
       (key (caar pairs))
       (err (vl-patternkey-case key
              :expr (b* ((name (vl-simple-idexpr-name key.key))
                         ((unless name)
                          (vmsg "Bad expression for struct assignment pattern key: ~a0" key.key))
                         ((unless (vl-find-structmember name membs))
                          (vmsg "Not a field name: ~a0" key.key)))
                      nil)
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
                :expr (equal (vl-simple-idexpr-name key.key)
                             (string-fix name))
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

(defprod vl-svexconf
  :short "Static configuration object for expr to svex conversion."
  ((ss vl-scopestack-p
       "The scopestack at the source location of the expression.")
   (fns svex::svex-alist-p "Function definition table")))

(defines vl-expr-to-svex
  :ruler-extenders :all
  :verify-guards nil
  :prepwork ((local (in-theory (disable not max 
                                        acl2::member-of-cons
                                        member-equal
                                        true-listp
                                        vl-warninglist-p-when-not-consp
                                        vl-warninglist-p-when-subsetp-equal
                                        svex::svexlist-p-when-not-consp
                                        default-car
                                        acl2::repeat-when-zp
                                        svex::svex-alist-p-when-not-consp
                                        svex::svarlist-addr-p-when-subsetp-equal
                                        acl2::member-when-atom
                                        cons-equal))))
  (define vl-expr-to-svex-selfdet ((x vl-expr-p)
                                   (ctxsize maybe-natp)
                                   (conf vl-svexconf-p))
    :short "Translates a VL expression to svex in a self-determined context, perhaps
            with a context size."
    :long "<p>This function sign- or zero-extends the result so that other
functions can assume all bits of it are good.</p>"
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex))))
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
         ((wmv warnings signedness) (vl-expr-typedecide x conf.ss))
         ((unless signedness)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Couldn't decide signedness of expression ~a0."
                     :args (list x))
              (svex-x)
              nil))
         ((wmv warnings size) (vl-expr-selfsize x conf.ss))
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
                                  (signedness vl-exprtype-p)
                                  (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-expr-count x) 6)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
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
         ((wmv warnings size) (vl-expr-selfsize x conf.ss))
         ((unless size)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Sizing of ~a0 failed unexpectedly."
                     :args (list x))
              (svex-x)))
         ((wmv warnings svex)
          (vl-expr-to-svex-opaque x conf)))
      (mv warnings (svex-extend signedness size svex))))

  (define vl-expr-to-svex-transparent ((x vl-expr-p)
                                       (size natp)
                                       (signedness vl-exprtype-p)
                                       (conf vl-svexconf-p))
    :guard (equal (vl-expr-opacity x) :transparent)
    :measure (two-nats-measure (vl-expr-count x) 4)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
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
             ((wmv warnings right-svex)
              (if (member x.op '(:vl-binary-power
                                 :vl-binary-shl
                                 :vl-binary-shr
                                 :vl-binary-ashl
                                 :vl-binary-ashr))
                  ;; Transparent only in the first operand.
                  (b* (((wmv warnings right-svex &)
                        (vl-expr-to-svex-selfdet x.right nil conf)))
                    (mv warnings right-svex))
                ;; Transparent in both operands.
                (vl-expr-to-svex-vector x.right size signedness conf)))
             ((wmv err svex)
              (vl-binaryop-to-svex x.op left-svex right-svex size size size signedness)))
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
              (svex::svcall svex::? test-svex then-svex else-svex)))

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
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (warnings nil)
         ((vl-svexconf conf)))
      (vl-expr-case x

        :vl-value
        (b* (((mv err svex) (vl-value-to-svex x.val)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to convert expression ~a0: ~@1"
                         :args (list x err))
                (ok))
              svex))

        :vl-index
        (b* (((wmv warnings svex & &)
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
             ((wmv warnings left-size) (vl-expr-selfsize x.left conf.ss))
             ((wmv warnings right-size) (vl-expr-selfsize x.right conf.ss))
             ((wmv warnings left-type) (vl-expr-typedecide x.left conf.ss))
             ((wmv warnings right-type) (vl-expr-typedecide x.right conf.ss))
             ((unless (and left-size right-size left-type right-type))
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Failed to find size and signedness of expression ~a0"
                         :args (list (if (and left-size left-type)
                                             x.right
                                           x.left)))
                  (svex-x)))
             ;; Size each under the max size
             (arg-size (max left-size right-size))
             (arg-type (vl-exprtype-max left-type right-type))
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
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Not yet supported: ~a0"
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
                 ((unless (equal simple-name "$bits"))
                  (mv (fatal :type :vl-expr-to-svex-fail
                             :msg "Unsupported system call: ~a0"
                             :args (list x))
                      (svex-x))))
              (vl-$bits-call-to-svex x conf.ss))
          (b* (((wmv warnings svex & &)
                (vl-funcall-to-svex x conf)))
            (mv warnings svex)))

        :vl-cast
        ;; If we get here, we've already gotten the size/signedness of the cast
        ;; type and decided it's OK as a vector type.  However, the inner
        ;; expression might not be a vector expression -- e.g. the type could
        ;; be a packed struct and the inner expression an assignment pattern
        ;; creating that struct.  So we have to use vl-expr-to-svex-datatyped
        ;; here.
        (b* ((err (vl-datatype-check-usertypes x.to conf.ss))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in cast ~a0: ~@1"
                         :args (list x err))
                  (svex-x))))
          (vl-expr-to-svex-datatyped x.expr x.to conf.ss conf))

        :vl-pattern
        (b* (((unless x.pattype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Untyped assignment pattern: ~a0"
                         :args (list x))
                  (svex-x)))
             (err (vl-datatype-check-usertypes x.pattype conf.ss))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in pattern ~a0: ~@1"
                         :args (list x err))
                  (svex-x))))
          (vl-assignpat-to-svex x.pat x.pattype conf.ss conf x))
        :otherwise
        (mv (ok) (prog2$ (impossible) (svex-x))))))

  (define vl-index-expr-to-svex ((x vl-expr-p)
                                 (conf vl-svexconf-p))
    :guard (vl-expr-case x :vl-index)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex))))
                 (type vl-maybe-datatype-p)
                 (type-ss vl-scopestack-p))
    :measure (two-nats-measure (vl-expr-count x) 2)    
    (b* ((warnings nil)
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv (ok) (svex-x) nil nil))
         ((vl-svexconf conf))
         (x (vl-expr-fix x))
         ((mv err opinfo) (vl-index-expr-typetrace x conf.ss))
         ((when err)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to convert expression ~a0: ~@1"
                     :args (list x err))
              (svex-x) nil nil))
         ((vl-operandinfo opinfo))
         ((wmv warnings svex-indices ?sizes)
          (vl-exprlist-to-svex-selfdet
           (vl-operandinfo->indices opinfo) conf))
         ((mv err svex)
          (vl-operandinfo-to-svex opinfo svex-indices conf.ss)))
      (mv (if err
              (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to convert expression ~a0: ~@1"
                     :args (list x err))
            (ok))
          svex
          opinfo.type opinfo.ss))
    ///
    (defret vl-index-expr-to-svex-type-ok
      (implies type
               (not (vl-datatype-check-usertypes type type-ss)))
      :hints (("goal" :expand ((vl-index-expr-to-svex x conf))))))

  (define vl-funcall-to-svex ((x vl-expr-p)
                              (conf vl-svexconf-p))
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex))))
                 (type vl-maybe-datatype-p)
                 (type-ss vl-scopestack-p))
    :guard (vl-expr-case x :vl-call)
    :measure (two-nats-measure (vl-expr-count x) 2)    
    (b* ((warnings nil)
         ((unless (mbt (vl-expr-case x :vl-call)))
          (impossible) ;; need this case for measure
          (mv (ok) (svex-x) nil nil))
         ((vl-svexconf conf))
         ((vl-call x) (vl-expr-fix x))
         ((mv err trace context ?tail)
          (vl-follow-scopeexpr x.name conf.ss))
         ((when err)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to find function ~a0"
                     :args (list x))
              (svex-x) nil nil))
         ((vl-hidstep lookup) (car trace))
         ((unless (eq (tag lookup.item) :vl-fundecl))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "In function call ~a0, function name does not ~
                        refer to a fundecl but instead ~a1"
                     :args (list x lookup.item))
              (svex-x) nil nil))
         ((unless (vl-hidtrace-resolved-p trace))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "In function call ~a0, function name has ~
                         unresolved indices??"
                     :args (list x))
              (svex-x) nil nil))
         (path (vl-hidtrace-to-path trace nil))
         ((mv ?err addr) (vl-scopecontext-to-addr context conf.ss path))
         ;; Ignore the error here because we really just want to generate a fully
         ;; scoped name for the function.
         (fnname (svex::make-svar :name addr))
         (expr (svex::svex-lookup fnname conf.fns))
         ((unless expr)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Function not found: ~a0"
                     :args (list x))
              (svex-x) nil nil))
         ((vl-fundecl decl) lookup.item)
         ((unless (eql (len decl.portdecls) (len x.args)))
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Bad arity for function call: ~a0"
                     :args (list x))
              (svex-x) nil nil))
         (types (vl-portdecllist->types decl.portdecls))
         (type-err (vl-datatypelist-check-usertypes types lookup.ss))
         ((when type-err)
          (mv (fatal :type :vl-expr-to-svex-fail
                     :msg "Failed to resolve usertypes in portlist for ~
                           function call ~a0: ~@1"
                     :args (list x type-err))
              (svex-x) nil nil))
         ((wmv warnings args-svex)
          (vl-exprlist-to-svex-datatyped
           x.args
           types
           lookup.ss ;; conf.ss for all of the portdecl types, from function declaration context
           conf))
         (comp-alist (vl-function-pair-inputs-with-actuals decl.portdecls args-svex))
         ((with-fast comp-alist))
         (ans (svex::svex-subst-memo expr comp-alist)))
      (clear-memoize-table 'svex::svex-subst-memo)
      (mv (ok) ans decl.rettype lookup.ss)))

  (define vl-expr-to-svex-datatyped ((x vl-expr-p)
                                     (type vl-datatype-p)
                                     (type-ss vl-scopestack-p)
                                     (conf vl-svexconf-p))
    :guard (not (vl-datatype-check-usertypes type type-ss))
    :measure (two-nats-measure (vl-expr-count x) 16)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
    (b* ((x (vl-expr-fix x))
         (warnings nil)
         ((vl-svexconf conf)) 
         (opacity (vl-expr-opacity x)) 
         (packedp (vl-datatype-packedp type type-ss))
         ((when (and packedp
                     (not (eq opacity :special))
                     (not (vl-expr-case x :vl-pattern))))
          ;; A non-special opacity generally means the expression is
          ;; vector-like, and I think that if the datatype is packed we get the
          ;; right results by simply treating the expression as a vector with
          ;; the given size.  We may need to add exceptions to this.
          (b* (((mv err size) (vl-datatype-size type type-ss))
               ((when (or err (not size)))
                (mv (fatal :type :vl-expr-to-svex-fail
                           :msg "Couldn't size packed datatype ~a0"
                           :args (list (vl-datatype-fix type)))
                    (svex-x)))
               ((wmv warnings svex &)
                (vl-expr-to-svex-selfdet x size conf)))
            (mv warnings svex))))

      (vl-expr-case x
        :vl-index
        (b* (((wmv warnings svex itype itype-ss)
              (vl-index-expr-to-svex x conf))
             ((unless itype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Couldn't find type for expression: ~a0"
                         :args (list x))
                  svex))
             (err (vl-compare-datatypes type type-ss itype itype-ss)))
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
              (vl-expr-to-svex-datatyped x.then type type-ss conf))
             ((wmv warnings else-svex)
              (vl-expr-to-svex-datatyped x.else type type-ss conf)))
          (mv (ok)
              (svex::svcall svex::? test-svex then-svex else-svex)))

        :vl-call
        (b* (((when x.systemp)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "System call ~a0 supposed to return unpacked type ~a1"
                         :args (list x (vl-datatype-fix type)))
                  (svex-x)))
             ((wmv warnings svex ftype ftype-ss)
              (vl-funcall-to-svex x conf))
             ((unless ftype)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Couldn't find type for expression: ~a0"
                         :args (list x))
                  svex))
             (err (vl-compare-datatypes type type-ss ftype ftype-ss)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x ftype (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-cast
        (b* ((err (vl-datatype-check-usertypes x.to conf.ss))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in cast ~a0: ~@1"
                         :args (list x err))
                  (svex-x)))
             ((wmv warnings svex)
              (vl-expr-to-svex-datatyped x.expr x.to conf.ss conf))
             (err (vl-compare-datatypes type type-ss x.to conf.ss)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x x.to (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-mintypmax
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support mintypmax expressions: ~a0."
                   :args (list x))
            (svex-x))

        :vl-pattern
        (b* (((unless x.pattype)
              (vl-assignpat-to-svex x.pat type type-ss conf x))
             (err (vl-datatype-check-usertypes x.pattype conf.ss))
             ((when err)
              (mv (fatal :type :vl-expr-to-svex-fail
                         :msg "Usertypes not resolved in pattern ~a0: ~@1"
                         :args (list x err))
                  (svex-x)))
             ((wmv warnings svex)
              (vl-assignpat-to-svex x.pat x.pattype conf.ss conf x))
             (err (vl-compare-datatypes type type-ss x.pattype conf.ss)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Type mismatch: ~a0 has type ~a1 but ~
                               should be ~a2. More: ~@3"
                         :args (list x x.pattype (vl-datatype-fix type) err))
                (ok))
              svex))

        :vl-special
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support ~a0."
                   :args (list x))
            (svex-x))

        :vl-stream
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Don't yet support ~a0."
                   :args (list x))
            (svex-x))

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

  (define vl-assignpat-to-svex ((x vl-assignpat-p)
                                (type vl-datatype-p)
                                (type-ss vl-scopestack-p)
                                (conf vl-svexconf-p)
                                (orig-x vl-expr-p))
    :guard (not (vl-datatype-check-usertypes type type-ss))
    :measure (two-nats-measure (vl-assignpat-count x) 16)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         ((mv type type-ss) (vl-maybe-usertype-resolve type type-ss))
         ;; Makes sure type is not just a bare usertype.  If the result is a
         ;; usertype, it at least has an array dimension.
         ((when (or (consp (vl-datatype->udims type))
                    (consp (vl-datatype->pdims type))))
          ;; Array.
          (b* (((mv ?err ?caveat slottype dim slot-ss)
                (vl-datatype-remove-dim type type-ss))
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
            (vl-array-assignpat-to-svex x slottype slot-ss range conf orig-x))))
      (vl-datatype-case type
        :vl-struct
        (vl-struct-assignpat-to-svex x type.members type-ss conf orig-x)
        :otherwise
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Bad type ~a0 for assignment pattern ~a1"
                   :args (list type orig-x))
            (svex-x)))))


  (define vl-array-assignpat-to-svex ((x vl-assignpat-p)
                                      (slottype vl-datatype-p)
                                      (slot-ss vl-scopestack-p)
                                      (range vl-range-p)
                                      (conf vl-svexconf-p)
                                      (orig-x vl-expr-p))
    :guard (and (vl-range-resolved-p range)
                (not (vl-datatype-check-usertypes slottype slot-ss)))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         (slottype (vl-datatype-fix slottype))
         (subexprs (vl-assignpat-case x
                     :positional x.vals
                     :keyval (alist-vals x.pairs)
                     :repeat x.vals))
         ((mv err slotsize) (vl-datatype-size slottype slot-ss))
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
           slot-ss
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
                                              (type-ss vl-scopestack-p)
                                              (conf vl-svexconf-p)
                                              (orig-x vl-expr-p))
    :guard (not (vl-structmemberlist-check-usertypes membs type-ss :rec-limit 1000))
    :measure (two-nats-measure (vl-keyvallist-count x)
                               (len membs))
    ;; BOZO only returning one of the errors...
    :returns (mv (warnings vl-warninglist-p)
                 (svex-membs
                  (and (svex::svexlist-p svex-membs)
                       (equal (len svex-membs) (len membs))
                       (svex::svarlist-addr-p (svex::svexlist-vars svex-membs)))
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
               first m1.type type-ss conf)
            (mv (fatal :type :vl-expr-to-svex-fail
                       :msg "No entry for struct member ~s1 in ~
                                  assignment pattern ~a1"
                       :args (list m1.name orig-x))
                (svex-x))))
         ((wmv warnings rest)
          (vl-struct-assignpat-keyval-resolve
           x (cdr membs) type-ss conf orig-x)))
      (mv warnings
          (cons first rest))))

  (define vl-struct-assignpat-to-svex ((x vl-assignpat-p)
                                       (membs vl-structmemberlist-p)
                                       (type-ss vl-scopestack-p)
                                       (conf vl-svexconf-p)
                                       (orig-x vl-expr-p))
    :measure (two-nats-measure (vl-assignpat-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svex (and (svex::svex-p svex) (svex::svarlist-addr-p (svex::svex-vars svex)))))
    (b* ((orig-x (vl-expr-fix orig-x))
         (warnings nil)
         ((mv err widths) (vl-structmemberlist-sizes membs type-ss :rec-limit 1000))
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
              (vl-exprlist-to-svex-datatyped x.vals types type-ss conf)))
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
             ((mv err svex-membs)
              (vl-struct-assignpat-keyval-resolve
               x.pairs membs type-ss conf orig-x)))
          (mv (if err
                  (fatal :type :vl-expr-to-svex-fail
                         :msg "Bad key/val assignment pattern ~a0: ~@1"
                         :args (list orig-x err))
                (ok))
              (svex-concat-list widths svex-membs))))))

  (define vl-exprlist-to-svex-datatyped ((x vl-exprlist-p)
                                         (types vl-datatypelist-p)
                                         (type-ss vl-scopestack-p)
                                         (conf vl-svexconf-p))
    :guard (and (equal (len types) (len x))
                (not (vl-datatypelist-check-usertypes types type-ss)))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svexes
                  (and (svex::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (svex::svarlist-addr-p (svex::svexlist-vars svexes)))))
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil))
         ((wmv warnings first)
          (vl-expr-to-svex-datatyped
           (car x) (car types) type-ss conf))
         ((wmv warnings rest)
          (vl-exprlist-to-svex-datatyped
           (cdr x) (cdr types) type-ss conf)))
      (mv warnings (cons first rest))))

  (define vl-exprlist-to-svex-selfdet ((x vl-exprlist-p)
                                       (conf vl-svexconf-p))
    :measure (two-nats-measure (vl-exprlist-count x) 10)
    :returns (mv (warnings vl-warninglist-p)
                 (svexes
                  (and (svex::svexlist-p svexes)
                       (equal (len svexes) (len x))
                       (true-listp svexes)
                       (svex::svarlist-addr-p (svex::svexlist-vars svexes))))
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
                   '(:expand ((vl-datatypelist-check-usertypes types type-ss)
                              (:free (rec-limit)
                               (vl-structmemberlist-check-usertypes membs type-ss))
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
       (expr (vl-idexpr "a" nil))
       (sel-expr (change-vl-index expr
                                  :part (vl-range->partselect
                                         (make-vl-range :msb (vl-make-index sel-msb)
                                                        :lsb (vl-make-index sel-lsb)))))
       ((wmv warnings svex size)
        (vl-expr-to-svex-selfdet sel-expr nil ss nil 'test-partselect nil)))
    (mv warnings
        (car (svex::svexlist-rewrite-fixpoint (list svex)))
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
                             (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (svex::lhs-p svex)
                          (svex::svarlist-addr-p (svex::lhs-vars svex))))
               (type vl-maybe-datatype-p)
               (type-ss vl-scopestack-p))
  (b* ((warnings nil)
       (conf (make-vl-svexconf :ss ss :fns nil))
       ((wmv warnings svex type type-ss)
        (vl-expr-case x
          :vl-index (vl-index-expr-to-svex x conf)
          :vl-concat (b* (((wmv warnings svex size)
                           (vl-expr-to-svex-selfdet x nil conf))
                          ((unless (posp size))
                           (mv warnings svex nil nil)))
                       (mv warnings svex
                           (make-vl-coretype :name :vl-logic
                                             :pdims (list (vl-range->packeddimension
                                                           (make-vl-range
                                                            :msb (vl-make-index (1- size))
                                                            :lsb (vl-make-index 0)))))
                           (make-vl-scopestack-null)))
          :otherwise (mv (fatal :type :vl-expr-to-svex-fail
                                :msg "Bad LHS expression: ~a0"
                                :args (list (vl-expr-fix x)))
                         (svex-x) nil nil)))
       ((unless type)
        (mv warnings nil type type-ss))
       ((mv err size) (vl-datatype-size type type-ss))
       ((when (or err (not size)))
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't size the datatype ~a0 of ~
                                    LHS expression ~a1: ~@2"
                   :args (list type (vl-expr-fix x) err))
            nil nil nil))
       (lhssvex (svex::svex-concat size
                                   (svex::svex-lhsrewrite svex 0 size)
                                   (svex::svex-z)))
       ((unless (svex::lhssvex-p lhssvex))
        (mv (fatal :type :vl-expr->svex-lhs-fail
                   :msg "Not a supported LHS expression: ~a0"
                   :args (list (vl-expr-fix x)))
            nil nil nil)))
    (mv warnings (svex::svex->lhs lhssvex) type type-ss))
  ///
  (defret vl-expr-to-svex-lhs-type-size-ok
    (implies type
             (not (mv-nth 0 (vl-datatype-size type type-ss))))
    :hints(("Goal" :in-theory (enable vl-datatype-size)))))


(define vl-expr-to-svex-untyped ((x vl-expr-p)
                                 (ss vl-scopestack-p)
                                 (fns svex::svex-alist-p))
  :short "Convert an expression to svex, and return its datatype."
  :long "<p>In some cases we need to convert an expression and also check what
type it is returning.  For example, if the expression is the port connection of
an instance array, we know the type of a single port but we don't know whether
all instances' ports are receiving the whole expression, or whether the bits of
the expression are being distributed across the instances.  To determine that,
we need to get the type of the expression.</p>"
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (svex::svex-p svex)
                          (svex::svarlist-addr-p (svex::svex-vars svex))))
               (type vl-maybe-datatype-p)
               (type-ss vl-scopestack-p))
  (b* ((conf (make-vl-svexconf :ss ss :fns fns))
       (warnings nil))
    (vl-expr-case x
      :vl-index (vl-index-expr-to-svex x conf)
      :otherwise (b* (((wmv warnings svex size)
                       (vl-expr-to-svex-selfdet x nil conf))
                      ((unless (posp size))
                       (mv warnings svex nil nil)))
                   (mv warnings svex
                       (make-vl-coretype :name :vl-logic
                                         :pdims (list (vl-range->packeddimension
                                                       (make-vl-range
                                                        :msb (vl-make-index (1- size))
                                                        :lsb (vl-make-index 0)))))
                       (make-vl-scopestack-null)))))
  ///
  (defret vl-expr-to-svex-untyped-type-ok
    (implies type
             (not (vl-datatype-check-usertypes type type-ss)))
    :hints(("Goal" :in-theory (enable vl-datatype-check-usertypes)))))

(define vl-expr-to-svex-typed ((x vl-expr-p)
                               (type vl-datatype-p)
                               (type-ss vl-scopestack-p)
                               (ss vl-scopestack-p)
                               (fns svex::svex-alist-p))
  :short "Convert an expression to svex, given the datatype it should have."
  :guard (not (vl-datatype-check-usertypes type type-ss))
  :returns (mv (warnings vl-warninglist-p)
               (svex (and (svex::svex-p svex)
                          (svex::svarlist-addr-p (svex::svex-vars svex)))))
  (b* ((conf (make-vl-svexconf :ss ss :fns fns)))
    (vl-expr-to-svex-datatyped x type type-ss conf)))


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

(define vl-4vec-to-value ((x svex::4vec-p)
                          (width posp)
                          &key
                          ((signedness vl-exprtype-p) ':vl-signed))
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (in-theory (disable unsigned-byte-p acl2::loghead)))
             (local (defthm 4vec->lower-of-4vec-zero-ext
                      (implies (natp n)
                               (unsigned-byte-p n (svex::4vec->lower (svex::4vec-zero-ext (svex::2vec n) x))))
                      :hints(("Goal" :in-theory (e/d (svex::2vec-p svex::2vec svex::2vec->val svex::4vec-zero-ext))))))
             (local (defthm 4vec->lower-of-4vec-zero-ext-bounds
                      (implies (natp n)
                               (and (<= 0 (svex::4vec->lower (svex::4vec-zero-ext (svex::2vec n) x)))
                                    (< (svex::4vec->lower (svex::4vec-zero-ext (svex::2vec n) x)) (expt 2 n))))
                      :hints(("Goal" :use 4vec->lower-of-4vec-zero-ext
                              :in-theory (e/d (unsigned-byte-p)
                                              (4vec->lower-of-4vec-zero-ext)))))))
  :returns (val vl-value-p)
  (b* ((width (lposfix width))
       (trunc (svex::4vec-zero-ext (svex::2vec width) x))
       ((when (svex::2vec-p trunc))
        (b* ((val (svex::2vec->val trunc)))
          (make-vl-constint :origwidth width
                            :origtype signedness
                            :wasunsized t
                            :value val)))
       (val (vl-upperlower-to-bitlist (svex::4vec->upper trunc)
                                      (svex::4vec->lower trunc)
                                      width)))
    (make-vl-weirdint :bits val
                      :origtype signedness
                      :wasunsized t)))
             
       


(define vl-expr-consteval ((x vl-expr-p)
                           (conf vl-svexconf-p))
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
        (vl-expr-to-svex-selfdet x nil conf))
       ((when (or (vl-some-warning-fatalp warnings)
                  (not size)
                  (eql size 0)))
        (mv warnings nil (vl-expr-fix x)))
       (svex (svex::svex-reduce-consts svex))
       (val (svex::svex-case svex
              :quote svex.val
              :otherwise nil))
       ((unless val)
        (mv warnings nil (vl-expr-fix x)))
       (new-x (make-vl-value :val (vl-4vec-to-value val size))))
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

(define vl-range-resolve-indices ((x vl-range-p)
                                  (conf vl-svexconf-p))
  :verify-guards nil
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-range-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-range-fix x))))))
  (b* ((warnings nil)
       ((vl-range x) (vl-range-fix x))
       ((wmv warnings changedp1 new-msb)
        (vl-expr-consteval x.msb conf))
       ((wmv warnings changedp2 new-lsb)
        (vl-expr-consteval x.lsb conf))
       (changedp (or changedp1 changedp2)))
    (mv warnings
        changedp
        (mbe :logic (change-vl-range x :msb new-msb :lsb new-lsb)
             :exec (if changedp
                       (change-vl-range x :msb new-msb :lsb new-lsb)
                     x))))
  ///
  (verify-guards vl-range-resolve-indices))

(define vl-plusminus-resolve-indices ((x vl-plusminus-p)
                                  (conf vl-svexconf-p))
  :verify-guards nil
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-plusminus-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-plusminus-fix x))))))
  (b* ((warnings nil)
       ((vl-plusminus x) (vl-plusminus-fix x))
       ((wmv warnings changedp1 new-base)
        (vl-expr-consteval x.base conf))
       ((wmv warnings changedp2 new-width)
        (vl-expr-consteval x.width conf))
       (changedp (or changedp1 changedp2)))
    (mv warnings
        changedp
        (mbe :logic (change-vl-plusminus x :base new-base :width new-width)
             :exec (if changedp
                       (change-vl-plusminus x :base new-base :width new-width)
                     x))))
  ///
  (verify-guards vl-plusminus-resolve-indices))

(define vl-streamexpr-resolve-indices ((x vl-streamexpr-p)
                                       (conf vl-svexconf-p))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-streamexpr-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-streamexpr-fix x))))))
  (b* ((warnings nil)
       ((vl-streamexpr x) (vl-streamexpr-fix x))
       ((wmv warnings changedp new-part)
        (vl-arrayrange-case x.part
          :none (mv (ok) nil x.part)
          :range
          (b* (((wmv warnings changedp new-range)
                (vl-range-resolve-indices x.part.range conf)))
            (mv warnings changedp
                (mbe :logic (vl-range->arrayrange new-range)
                     :exec (if changedp
                               (vl-range->arrayrange new-range)
                             x.part))))
          :plusminus
          (b* (((wmv warnings changedp new-plusminus)
                (vl-plusminus-resolve-indices x.part.plusminus conf)))
            (mv warnings changedp
                (mbe :logic (vl-plusminus->arrayrange new-plusminus)
                     :exec (if changedp
                               (vl-plusminus->arrayrange new-plusminus)
                             x.part))))
          :index
          (b* (((wmv warnings changedp new-expr)
                (vl-expr-consteval x.part.expr conf)))
            (mv warnings changedp
                (mbe :logic (vl-expr->arrayrange new-expr)
                     :exec (if changedp
                               (vl-expr->arrayrange new-expr)
                             x.part)))))))
    (mv warnings
        changedp
        (mbe :logic (change-vl-streamexpr x :part new-part)
             :exec (if changedp
                       (change-vl-streamexpr x :part new-part)
                     x)))))
          

(define vl-streamexprlist-resolve-indices ((x vl-streamexprlist-p)
                                           (conf vl-svexconf-p))
  :verify-guards nil
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-streamexprlist-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-streamexprlist-fix x))))
                      :hints (("goal" :induct t)
                              (and stable-under-simplificationp
                                   '(:expand ((vl-streamexprlist-fix x)))))))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil (vl-streamexprlist-fix x)))
       ((wmv warnings changedp1 new-x1)
        (vl-streamexpr-resolve-indices (car x) conf))
       ((wmv warnings changedp2 new-x2)
        (vl-streamexprlist-resolve-indices (cdr x) conf))
       (changedp (or changedp1 changedp2)))
    (mv warnings changedp
        (mbe :logic (cons new-x1 new-x2)
             :exec (if changedp
                       (cons new-x1 new-x2)
                     x))))
  ///
  (verify-guards vl-streamexprlist-resolve-indices))

(define vl-packeddimension-resolve-indices ((x vl-packeddimension-p)
                                            (conf vl-svexconf-p))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-packeddimension-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-packeddimension-fix x))))))
  (b* ((warnings nil))
    (vl-packeddimension-case x
      :unsized (mv (ok) nil (vl-packeddimension-fix x))
      :range (b* (((wmv warnings changedp new-range)
                   (vl-range-resolve-indices x.range conf)))
               (mv warnings changedp
                   (vl-range->packeddimension new-range))))))

(define vl-packeddimensionlist-resolve-indices ((x vl-packeddimensionlist-p)
                                           (conf vl-svexconf-p))
  :verify-guards nil
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-packeddimensionlist-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-packeddimensionlist-fix x))))
                      :hints (("goal" :induct t)
                              (and stable-under-simplificationp
                                   '(:expand ((vl-packeddimensionlist-fix x)))))))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil (vl-packeddimensionlist-fix x)))
       ((wmv warnings changedp1 new-x1)
        (vl-packeddimension-resolve-indices (car x) conf))
       ((wmv warnings changedp2 new-x2)
        (vl-packeddimensionlist-resolve-indices (cdr x) conf))
       (changedp (or changedp1 changedp2)))
    (mv warnings changedp
        (mbe :logic (cons new-x1 new-x2)
             :exec (if changedp
                       (cons new-x1 new-x2)
                     x))))
  ///
  (verify-guards vl-packeddimensionlist-resolve-indices))



(defines vl-datatype-resolve-indices
  (define vl-datatype-resolve-indices ((x vl-datatype-p)
                                       (conf vl-svexconf-p))
  :verify-guards nil
  :measure (vl-datatype-count x)
  ;; :hints((and stable-under-simplificationp
  ;;             '(:expand ((vl-datatype-count x)
  ;;                        (vl-structmemberlist-count x)))))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-datatype-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-datatype-fix x))))))
  (b* ((warnings nil)
       (x (vl-datatype-fix x))
       ((wmv warnings changedp1 new-pdims)
        (vl-packeddimensionlist-resolve-indices (vl-datatype->pdims x) conf))
       ((wmv warnings changedp2 new-udims)
        (vl-packeddimensionlist-resolve-indices (vl-datatype->udims x) conf))
       (changedp (or changedp1 changedp2)))
    (vl-datatype-case x
      :vl-coretype
      (mv warnings
          changedp
          (mbe :logic (change-vl-coretype x :pdims new-pdims :udims new-udims)
               :exec (if changedp
                         (change-vl-coretype x :pdims new-pdims :udims new-udims)
                       x)))
      :vl-struct
      (b* (((wmv warnings changedp1 new-members)
            (vl-structmemberlist-resolve-indices x.members conf))
           (changedp (or changedp1 changedp)))
        (mv warnings
          changedp
          (mbe :logic (change-vl-struct
                       x :members new-members :pdims new-pdims :udims new-udims)
               :exec (if changedp
                         (change-vl-struct
                          x :members new-members :pdims new-pdims :udims new-udims)
                       x))))
      :vl-union
      (b* (((wmv warnings changedp1 new-members)
            (vl-structmemberlist-resolve-indices x.members conf))
           (changedp (or changedp1 changedp)))
        (mv warnings
          changedp
          (mbe :logic (change-vl-union
                       x :members new-members :pdims new-pdims :udims new-udims)
               :exec (if changedp
                         (change-vl-union
                          x :members new-members :pdims new-pdims :udims new-udims)
                       x))))
      :vl-enum
      (b* (((vl-enumbasetype x.basetype))
           ((wmv warnings changedp1 new-dim)
            (if x.basetype.dim
                (vl-packeddimension-resolve-indices x.basetype.dim conf)
              (mv warnings nil x.basetype.dim)))
           (new-basetype (mbe :logic
                              (change-vl-enumbasetype x.basetype :dim new-dim)
                              :exec
                              (if changedp1
                                  (change-vl-enumbasetype x.basetype :dim new-dim)
                                x.basetype)))
           (changedp (or changedp1 changedp)))
        (mv warnings
            changedp
            (mbe :logic (change-vl-enum
                         x :basetype new-basetype 
                         :pdims new-pdims :udims new-udims)
                 :exec (if changedp
                           (change-vl-enum
                            x :basetype new-basetype
                            :pdims new-pdims :udims new-udims)
                         x))))
      :vl-usertype
      (mv warnings
          changedp
          (mbe :logic (change-vl-usertype x :pdims new-pdims :udims new-udims)
               :exec (if changedp
                         (change-vl-usertype x :pdims new-pdims :udims new-udims)
                       x))))))

  (define vl-structmemberlist-resolve-indices ((x vl-structmemberlist-p)
                                               (conf vl-svexconf-p))
    :verify-guards nil
    :measure (vl-structmemberlist-count x)
    :returns (mv (warnings1 vl-warninglist-p)
                 (changedp)
                 (new-x (and (vl-structmemberlist-p new-x)
                             (implies (not changedp)
                                      (equal new-x (vl-structmemberlist-fix x))))))
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil (vl-structmemberlist-fix x)))
         ((vl-structmember x1) (car x))
         ((wmv warnings changedp1 new-type1)
          (vl-datatype-resolve-indices x1.type conf))
         (memb1 (mbe :logic (change-vl-structmember x1 :type new-type1)
                     :exec (if changedp1
                               (change-vl-structmember x1 :type new-type1)
                             x1)))
         ((wmv warnings changedp2 new-x2)
          (vl-structmemberlist-resolve-indices (cdr x) conf))
         (changedp (or changedp1 changedp2)))
      (mv warnings changedp
          (mbe :logic (cons memb1 new-x2)
               :exec (if changedp
                         (cons memb1 new-x2)
                       x)))))
    ///
    (verify-guards vl-structmemberlist-resolve-indices)
    (deffixequiv-mutual vl-datatype-resolve-indices))


(define vl-patternkey-resolve-indices ((x vl-patternkey-p)
                                       (conf vl-svexconf-p))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-patternkey-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-patternkey-fix x))))))
  (b* ((warnings nil))
    (vl-patternkey-case x
      :expr (b* (((wmv warnings changedp new-key)
                  (vl-expr-consteval x.key conf)))
              (mv warnings
                  changedp
                  (mbe :logic (change-vl-patternkey-expr x :key new-key)
                       :exec (if changedp
                                 (change-vl-patternkey-expr x :key new-key)
                               x))))
      :type (b* (((wmv warnings changedp new-type)
                  (vl-datatype-resolve-indices x.type conf)))
              (mv warnings
                  changedp
                  (mbe :logic (change-vl-patternkey-type x :type new-type)
                       :exec (if changedp
                                 (change-vl-patternkey-type x :type new-type)
                               x))))
      :default (mv (ok) nil (vl-patternkey-fix x)))))

(define vl-keyvallist-resolve-indices ((x vl-keyvallist-p)
                                       (conf vl-svexconf-p))
  :prepwork ((local (defthm consp-car-when-vl-keyvallist-p
                      (implies (vl-keyvallist-p x)
                               (equal (consp (car x)) (consp x))))))
                                    
  :verify-guards nil
  :measure (vl-keyvallist-count x)
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-keyvallist-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-keyvallist-fix x))))))
  (b* ((warnings nil)
       (x (vl-keyvallist-fix x)))
    (if (atom x)
        (mv (ok) nil x)
      (b* (((wmv warnings changedp key1)
            (vl-patternkey-resolve-indices (caar x) conf))
           (car (mbe :logic (cons key1 (cdar x))
                     :exec (if changedp
                               (cons key1 (cdar x))
                             (car x))))
           ((wmv warnings changedp2 rest)
            (vl-keyvallist-resolve-indices (cdr x) conf))
           (changedp (or changedp changedp2)))
        (mv warnings
            changedp
            (mbe :logic (cons car rest)
                 :exec (if changedp
                           (cons car rest)
                         x))))))
  ///
  (verify-guards vl-keyvallist-resolve-indices))


(define vl-assignpat-resolve-indices ((x vl-assignpat-p)
                                      (conf vl-svexconf-p))
  :returns (mv (warnings1 vl-warninglist-p)
               (changedp)
               (new-x (and (vl-assignpat-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-assignpat-fix x))))))
  (b* ((warnings nil))
    (vl-assignpat-case x
      :positional (mv (ok) nil (vl-assignpat-fix x))
      :keyval (b* (((wmv warnings changedp pairs)
                    (vl-keyvallist-resolve-indices x.pairs conf)))
                (mv warnings changedp
                    (mbe :logic (change-vl-assignpat-keyval x :pairs pairs)
                         :exec (if changedp
                                   (change-vl-assignpat-keyval x :pairs pairs)
                                 x))))
      :repeat (b* (((wmv warnings changedp reps)
                    (vl-expr-consteval x.reps conf)))
                (mv warnings changedp
                    (mbe :logic (change-vl-assignpat-repeat x :reps reps)
                         :exec (if changedp
                                   (change-vl-assignpat-repeat x :reps reps)
                                 x)))))))
                 




(defines vl-expr-resolve-indices
  (define vl-expr-resolve-indices ((x vl-expr-p)
                                   (conf vl-svexconf-p))
    :verify-guards nil
    :returns (mv (warnings1 vl-warninglist-p)
                 (changedp)
                 (new-x (and (vl-expr-p new-x)
                             (implies (not changedp)
                                      (equal new-x (vl-expr-fix x))))))
    :measure (vl-expr-count x)
    :short "Return an expression equivalent to @('x'), but with certain subexpressions
            reduced to constants when possible."
    (b* ((warnings nil)
         ((wmv warnings changedp subexprs)
          (vl-exprlist-resolve-indices (vl-expr->subexprs x) conf))
         (x (mbe :logic (vl-expr-update-subexprs x subexprs)
                 :exec (if changedp
                           (vl-expr-update-subexprs x subexprs)
                         x))))
      (vl-expr-case x
        :vl-index
        ;; All subexpressions are indices and should be resolved if possible.
        (b* (((wmv warnings changedp2 subexprs)
              (vl-exprlist-consteval subexprs conf))
             (changedp (or changedp changedp2))
             (x (mbe :logic (vl-expr-update-subexprs x subexprs)
                     :exec (if changedp
                               (vl-expr-update-subexprs x subexprs)
                             x))))
          (mv warnings
              changedp
              x))
        :vl-multiconcat
        (b* (((wmv warnings changedp2 new-reps)
              (vl-expr-consteval x.reps conf)))
          (mv warnings
              (or changedp changedp2)
              (mbe :logic (change-vl-multiconcat x :reps new-reps)
                   :exec (if changedp2
                             (change-vl-multiconcat x :reps new-reps)
                           x))))
        :vl-stream
        (b* (((wmv warnings changedp2 new-size)
              (if x.size
                  (vl-expr-consteval x.size conf)
                (mv warnings nil nil)))
             ((wmv warnings changedp3 new-parts)
              (vl-streamexprlist-resolve-indices x.parts conf)))
          (mv warnings
              (or changedp changedp2 changedp3)
              (mbe :logic (change-vl-stream
                           x :size new-size :parts new-parts)
                   :exec (if (or changedp2 changedp3)
                             (change-vl-stream
                              x :size new-size :parts new-parts)
                           x))))
        :vl-call
        (b* (((wmv warnings changedp2 new-type)
              (if x.typearg
                  (vl-datatype-resolve-indices x.typearg conf)
                (mv warnings nil x.typearg))))
          (mv warnings
              (or changedp changedp2)
              (mbe :logic (change-vl-call x :typearg new-type)
                   :exec (if changedp2
                             (change-vl-call x :typearg new-type)
                           x))))
        :vl-cast
        (b* (((wmv warnings changedp2 new-type)
              (vl-datatype-resolve-indices x.to conf)))
          (mv warnings
              (or changedp changedp2)
              (mbe :logic (change-vl-cast x :to new-type)
                   :exec (if changedp2
                             (change-vl-cast x :to new-type)
                           x))))

        :vl-pattern
        (b* (((wmv warnings changedp2 new-type)
              (if x.pattype
                  (vl-datatype-resolve-indices x.pattype conf)
                (mv warnings nil x.pattype)))
             ((wmv warnings changedp3 new-pat)
              (vl-assignpat-resolve-indices x.pat conf))
             (changedp1 (or changedp2 changedp3)))
          (mv warnings
              (or changedp changedp1)
              (mbe :logic (change-vl-pattern x :pattype new-type :pat new-pat)
                   :exec (if changedp1
                             (change-vl-pattern x :pattype new-type :pat new-pat)
                           x))))
        :otherwise
        (mv warnings changedp x))))

  (define vl-exprlist-resolve-indices ((x vl-exprlist-p)
                                       (conf vl-svexconf-p))
    :verify-guards nil
    :returns (mv (warnings1 vl-warninglist-p)
                 (changedp)
                 (new-x (and (vl-exprlist-p new-x)
                             (implies (not changedp)
                                      (equal new-x (vl-exprlist-fix x)))
                             (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) nil (vl-exprlist-fix x)))
         ((wmv warnings changedp1 x1)
          (vl-expr-resolve-indices (car x) conf))
         ((wmv warnings changedp2 x2)
          (vl-exprlist-resolve-indices (cdr x) conf))
         (changedp (or changedp1 changedp2)))
      (mv warnings changedp
          (mbe :logic (cons x1 x2)
               :exec (if changedp
                         (cons x1 x2)
                       x)))))
  ///
  (local (in-theory (disable vl-expr-resolve-indices
                             vl-exprlist-resolve-indices)))
  (verify-guards vl-expr-resolve-indices)
  (deffixequiv-mutual vl-expr-resolve-indices))

