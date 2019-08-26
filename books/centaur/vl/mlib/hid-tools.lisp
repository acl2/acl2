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
;; (include-book "datatype-tools")
(include-book "scopestack")
(include-book "mocktype")
(include-book "expr-tools")
(include-book "arithclass")
(include-book "coretypes")
(include-book "elabindex")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable tag-reasoning)))
(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))

(local (defthm equal-of-cons-rewrite
         (equal (equal x (cons a b))
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))

(defthm vl-exprlist-count-of-append
  (equal (vl-exprlist-count (append a b))
         (+ -1 (vl-exprlist-count a)
            (vl-exprlist-count b)))
  :hints(("Goal" :in-theory (enable vl-exprlist-count append))))

(defthm vl-exprlist-count-of-rev
  (equal (vl-exprlist-count (rev x))
         (vl-exprlist-count x))
  :hints(("Goal" :in-theory (enable vl-exprlist-count rev))))



(defthm vl-genelement-kind-by-tag
  (implies (and (vl-genelement-p x)
                (equal (tag x) foo)
                (syntaxp (quotep foo)))
           (equal (vl-genelement-kind x) foo))
  :hints(("Goal" :in-theory (enable tag vl-genelement-kind vl-genelement-p))))


(defxdoc hid-tools
  :parents (mlib)
  :short "Functions for working with hierarchical identifiers."

  :long "<p>Perhaps the most fundamental operation for a hierarchical
identifier is figure out what it refers to.  This turns out to be a
surprisingly challenging and nuanced process.</p>

<p>Our top-level routine for following hierarchical identifiers is @(see
vl-follow-hidexpr).  It is meant to make looking up hierarchical identifiers
convenient despite these complications.</p>

<p>We now describe some of these challenges and how @(see vl-follow-hidexpr)
deals with them.</p>

<dl>

<dt>Datatypes versus Scopes</dt>

<dd>Challenge: The same syntax is used to refer to both data structure members
like @('myinst.opcode') and also to scopes like @('mysubmod.mywire').  However,
structures and scopes are very different and need to be traversed in different
ways.</dd>

<dd>Our Approach: @(see vl-follow-hidexpr) follows only the scope-based part of
the HID.  However, as one of our return values, we provide the tail of the
hierarchical index that leads into this variable.  For instance, in a case like
@('foo.bar.myinst.opcode') where @('myinst') is an @('instruction_t') structure
variable, we will follow only until the declaration of @('myinst') and then we
will return @('myinst.opcode') as the tail.</dd>


<dt>Unclear Destination</dt>

<dd>Challenge: Depending on the kind of analysis being done, we might want to
continue or stop resolving at certain points.  For instance, if we are trying
to size a hierarchical identifier like @('myinterface.ready'), we probably want
to follow through the interface all the way to the @('ready') signal.  However,
for light-weight variable use analysis, we may want to stop as soon as we hit
an interface.</dd>

<dd>Our Approach: @(see vl-follow-hidexpr) follows the HID as far as possible,
but returns a @(see vl-hidtrace-p) that includes not only the final declaration
we arrive at, but also all intermediate points along the way.  If you only care
about the final destination (e.g., the @('ready') signal for sizing or similar)
then you can get this final destination from the first @(see vl-hidstep-p) in
the trace.  But if you also want to know, e.g., that @('myinterface') has been
used, this information can easily be extracted from the rest of the trace.</dd>


<dt>Unresolved Parameters</dt>

<dd>Challenge: Because of parameters, we may not be able to tell whether the
indices in a hierarchical identifier are valid.  For instance, if there is an
array of module instances like @('mymod myarr [width-1:0] (...)') and we are
trying to follow a hierarchical reference like @('foo.bar.myarr[7].baz'), then
we will not know whether this is valid until we have resolved @('width').</dd>

<dd>In some applications, e.g., for @(see vl-lint), it may be best to allow
these potentially invalid indices.  After all, we \"know\" that this reference
is either invalid or is a reference to @('baz') within @('mymod').  In that
case, we may well wish to assume that the index will be valid and just go on
and find @('baz').</dd>

<dd>However, some other applications have more stringent soundness constraints.
If we are writing transforms that are meant to build conservative, safe, formal
models of the Verilog code, we may instead want to insist that all of the
indices have been resolved and cause an error if this is not the case.</dd>

<dd>Our Approach: @(see vl-follow-hidexpr) always tries to check that indices
are in bounds and to cause errors when indices are clearly out of bounds.  If
we encounter indices that are potentially out of bounds, then we can do one of
two things:

<ul>
<li>By default, we are permissive and assume the index will be in bounds.</li>
<li>However, if @(':strictp') is enabled, we will cause an error.</li>
</ul></dd>

<dd>As a special note: we always require generate array indices to be resolved.
See @(see vl-follow-hidexpr) for additional discussion.</dd>

<dt>Error reporting</dt>

<dd>Challenge: A HID may be invalid in many different ways.  Any part of the
HID may try to refer to a name that does not exist, and any index along the HID
might be invalid.  If an error occurs, we should provide enough detail to
understand the problem.</dd>

<dd>Our Approach: In the case of any error, @(see vl-follow-hidexpr) returns a
message.  Callers should put this message in the appropriate context so
that the end-user can understand the nature and location of the problem.</dd>

</dl>")

(local (xdoc::set-default-parents hid-tools))


(defprod vl-hidstep
  :short "A single step along the way of a hierarchical identifier."
  :long "<p>See @(see hid-tools).  Some routines for following hids produce
traces of the items they encounter along the way.  A <b>hidstep</b> structure
represents a single step along a HID.</p>"
  :tag :vl-hidstep
  :layout :tree
  ((name stringp "Name from the hid")
   (index vl-maybe-expr-p "Instance array/genarray index, if present")
   (item vl-scopeitem-p  "The item encountered along the path of the HID.")
   (ss   vl-scopestack-p "The scope where this item was found.")
   (elabpath vl-elabtraversal-p "Reversed instructions to get to this scope
                                 from the original scope.")))

(fty::deflist vl-hidtrace
  :elt-type vl-hidstep
  :short "A list of @(see vl-hidstep) structures, typically all of the steps
encountered along a HID.")

(define vl-scopeexpr->hid ((x vl-scopeexpr-p))
  :returns (hid vl-hidexpr-p)
  :short "Finds the hidexpr nested inside the scopeexpr."
  :measure (vl-scopeexpr-count x)
  (vl-scopeexpr-case x
    :end x.hid
    :colon (vl-scopeexpr->hid x.rest))
  ///
  (defret count-of-vl-scopeexpr->hid
    (< (vl-hidexpr-count hid)
       (vl-scopeexpr-count x))
    :rule-classes :linear))

(define vl-scopeexpr-replace-hid ((x vl-scopeexpr-p)
                                  (new-hid vl-hidexpr-p))
  :returns (new-x vl-scopeexpr-p)
  :short "Replaces the hidexpr nested inside the scopeexpr."
  :measure (vl-scopeexpr-count x)
  :verify-guards nil
  (vl-scopeexpr-case x
    :end (change-vl-scopeexpr-end x :hid new-hid)
    :colon (change-vl-scopeexpr-colon x :rest (vl-scopeexpr-replace-hid x.rest new-hid)))
  ///
  (verify-guards vl-scopeexpr-replace-hid))

(define vl-subhid-p ((inner vl-hidexpr-p)
                     (outer vl-hidexpr-p))
  :measure (vl-hidexpr-count outer)
  (if (vl-hidexpr-equiv inner outer)
      (vl-hidexpr-case outer
        :end t
        :dot (stringp (vl-hidindex->name outer.first)))
    (vl-hidexpr-case outer
      :dot (vl-subhid-p inner outer.rest)
      :otherwise nil)))

(define vl-hid-prefix-for-subhid ((outer vl-hidexpr-p)
                                  (inner vl-hidexpr-p))
  :guard (vl-subhid-p inner outer)
  :returns (prefix-hid vl-hidexpr-p)
  :measure (vl-hidexpr-count outer)
  :verify-guards nil
  :short "Given a hid and a suffix, such as @('a.b.c.d') and @('c.d'), return the
          hid without the suffix, i.e. @('a.b')."
  (vl-hidexpr-case outer
    :end (vl-hidexpr-fix outer) ;; must be the inner one since it's the last
    :dot (if (vl-hidexpr-equiv inner outer)
             (make-vl-hidexpr-end :name (vl-hidindex->name outer.first))
           (make-vl-hidexpr-dot
            :first outer.first
            :rest (vl-hid-prefix-for-subhid outer.rest inner))))
  ///
  (verify-guards vl-hid-prefix-for-subhid
    :hints (("goal" :expand ((vl-subhid-p inner outer)
                             (vl-subhid-p inner inner))))))


(define vl-follow-hidexpr-error
  :short "Report an error while following a HID."
  ((short vl-msg-p         "Brief description of the error.")
   (ss    vl-scopestack-p "Detailed context for the error.")
   &key
   ((origx vl-scopeexpr-p      "Original, full HID being resolved.") 'origx)
   ((x     vl-hidexpr-p    "Current place in the HID.")          'x))
  :returns (msg vl-msg-p)
  :long "<p>This is smart in a few ways: it distinguishes between ordinary
identifiers and hierarchical identifiers in the error type, and avoids
providing excessive context if we haven't gotten anywhere down into the HID
yet.</p>"
  (b* ((x     (vl-hidexpr-fix x))
       (origx (vl-scopeexpr-fix origx))
       (short (vl-msg-fix short))
       (endp (vl-scopeexpr-case origx :end))
       ((when (and endp
                   (equal x (vl-scopeexpr-end->hid origx))))
        ;; Omit detailed context since we haven't gotten anywhere yet.
        (vmsg "error resolving ~a1: ~@2."
              nil origx short)))
    (vmsg "error resolving ~a1: ~@2.~%~
                           (Failed to resolve ~a3 in ~s4)."
          nil origx short x (vl-scopestack->path ss))))

(define vl-follow-hidexpr-dimcheck
  :short "Check an array index against the corresponding array bounds."
  ((name    stringp        "Name being the array, for better errors.")
   (index   vl-expr-p      "An index into an array.")
   (dim     vl-dimension-p "Bounds from the corresponding declaration.")
   &key
   (strictp booleanp "Require indices to be resolved?"))
  :returns (err (iff (vl-msg-p err) err))
  :long "<p>In strict mode, we require that the @('index') and the array
dimensions all be resolved and that the index be in range.</p>

<p>In non-strict mode, we tolerate unresolved indices and declaration bounds.
Note that we still do bounds checking if the indices and array bounds happen to
be resolved.</p>"

  (b* ((dim (vl-dimension-fix dim)))
    (vl-dimension-case dim
      (:unsized
       ;; Bounds checking doesn't make sense in this case, so we'll just regard
       ;; this as fine.  BOZO we may want to revisit this.  This, and later
       ;; cases, are potentially OK in dynamic/runtime contexts, but not so
       ;; much in static/generate contexts.
       nil)
      (:star
       ;; An associative dimension without a type, I don't think there is any
       ;; bounds requirement here?
       nil)
      (:datatype
       (if strictp
           ;; BOZO eventually implement this.  Need to somehow look up the
           ;; datatype size?  Do we have enough info to do this here?
           (vmsg "unimplemented: check dimension against datatype-based associative
                  dimension ~a0" dim)
         nil))
      (:queue
       (if strictp
           ;; BOZO eventually implement this.
           (vmsg "unimplemented: check dimension against queue dimension ~a0" dim)
         nil))
      (:range
       (b* (((unless (vl-expr-resolved-p index))
             (if strictp
                 (vmsg "unresolved array index")
               nil))
            ((unless (vl-range-resolved-p dim.range))
             (if strictp
                 (vmsg "unresolved bounds on declaration of ~s0" (string-fix name))
               nil))
            (idxval (vl-resolved->val index))
            (msbval (vl-resolved->val dim.msb))
            (lsbval (vl-resolved->val dim.lsb))
            (minval (min msbval lsbval))
            (maxval (max msbval lsbval))
            ((unless (and (<= minval idxval)
                          (<= idxval maxval)))
             (vmsg "array index ~x0 out of bounds (~x1 to ~x2)"
                   idxval minval maxval)))
         nil)))))

(define vl-follow-hidexpr-dimscheck-aux
  :parents (vl-follow-hidexpr-dimscheck)
  :short "Main loop to check each index/dimension pair."
  :prepwork ((local (defthm vl-exprlist-fix-of-atom
                      (implies (not (consp x))
                               (equal (vl-exprlist-fix x) nil)))))
  ((name    stringp)
   (indices vl-exprlist-p)
   (dims    vl-dimensionlist-p)
   &key
   (strictp booleanp))
  :guard (same-lengthp indices dims)
  :returns (err (iff (vl-msg-p err) err))
  (if (atom indices)
      nil
    (or (vl-follow-hidexpr-dimcheck name (car indices) (car dims) :strictp strictp)
        (vl-follow-hidexpr-dimscheck-aux name (cdr indices) (cdr dims) :strictp strictp))))

(define vl-follow-hidexpr-dimscheck
  :short "Check array indices against the corresponding array bounds."
  ((name    stringp)
   (indices vl-exprlist-p
            "Indices from the HID piece we're following.  I.e., if we are
             resolving @('foo[3][4][5].bar'), this would be @('(3 4 5)')
             as an expression list.")
   (dims    vl-dimensionlist-p
            "Corresponding dimensions from the declaration, i.e., if @('foo')
             is declared as a @('logic [7:0][15:0][3:0]'), then this would
             be the list of @('([7:0] [15:0] [3:0])').")
   &key
   (strictp booleanp
            "Should we require every index to be resolved?")
   (direct-okp booleanp
               "Is it OK to directly refer to the whole array?"))
  :returns
  (err (iff (vl-msg-p err) err))
  (b* ((name (string-fix name))
       ((when (atom dims))
        (if (atom indices)
            nil
          (vmsg "indexing into non-array ~s0" name)))
       ((when (atom indices))
        (if direct-okp
            nil
          (vmsg "no indices given for array ~s0" name)))
       ((when (same-lengthp indices dims))
        (vl-follow-hidexpr-dimscheck-aux name indices dims
                                         :strictp strictp))
       (found (len indices))
       (need  (len dims))
       ((when (< found need))
        (vmsg "too many indices for array ~s0" name)))
    (vmsg "not enough indices for array ~s0" name)))

(define vl-genblocklist-find-block
  :short "Find the block from a generate array corresponding to some index."
  ((idx integerp)
   (x   vl-genblocklist-p))
  :returns (blk (iff (vl-genblock-p blk) blk))
  (cond ((atom x)
         nil)
        ((eql (vl-genblock->name (car x)) (lifix idx))
         (vl-genblock-fix (car x)))
        (t
         (vl-genblocklist-find-block idx (cdr x)))))

(local (defthm stringp-when-hidname-and-not-$root
         (implies (vl-hidname-p x)
                  (equal (equal x :vl-$root)
                         (not (stringp x))))
         :hints(("Goal" :in-theory (enable vl-hidname-p)))))

(local (defthm nesting-level-of-vl-scopestack-find-item/context
         (<= (vl-scopestack-nesting-level
              (mv-nth 1 (vl-scopestack-find-item/context name ss)))
             (vl-scopestack-nesting-level ss))
         :hints(("Goal" :in-theory (enable vl-scopestack-find-item/context
                                           vl-scopestack-nesting-level)))
         :rule-classes :linear))

(local (defthm maybe-stringp-of-vl-scopestack-find-item/context-pkg-name
         (maybe-stringp
          (mv-nth 2 (vl-scopestack-find-item/context name ss)))
         :hints(("Goal" :in-theory (enable maybe-stringp)))
         :rule-classes :type-prescription))

(define vl-scopestack-find-elabpath ((ss vl-scopestack-p)
                                     (context-ss vl-scopestack-p)
                                     (pkg-name maybe-stringp))
  :guard (<= (vl-scopestack-nesting-level context-ss)
             (vl-scopestack-nesting-level ss))
  :returns (elabpath vl-elabtraversal-p)
  (if pkg-name
      (list (vl-elabinstruction-push-named (vl-elabkey-package pkg-name))
            (vl-elabinstruction-root))
    (b* ((levels-up (- (vl-scopestack-nesting-level ss)
                       (vl-scopestack-nesting-level context-ss))))
      (list (vl-elabinstruction-pop levels-up)))))

(define vl-scopestack-find-item/ss/path ((name stringp)
                                         (ss vl-scopestack-p))
  :returns (mv (item (iff (vl-scopeitem-p item) item))
               (item-ss vl-scopestack-p)
               (elabpath vl-elabtraversal-p
                         "Reversed instructions to get from the SS to the item location."))
  (b* (((mv item context-ss pkg-name) (vl-scopestack-find-item/context name ss))
       (elabpath (vl-scopestack-find-elabpath ss context-ss pkg-name))
       ((unless pkg-name)
        (mv item context-ss elabpath))
       (design (vl-scopestack->design context-ss))
       (pkg (and design (cdr (hons-get pkg-name (vl-design-scope-package-alist-top design)))))
       (item-ss (and pkg (vl-scopestack-push pkg (vl-scopestack-init design)))))
    (mv item item-ss elabpath))
  ///
  (defthm tag-of-vl-scopestack-find-item/ss/path-forward
    (b* (((mv item ?item-ss ?item-path) (vl-scopestack-find-item/ss/path name ss)))
    (implies item
             (or (equal (tag item) :vl-modinst)
                 (equal (tag item) :vl-gateinst)
                 (equal (tag item) :vl-genloop)
                 (equal (tag item) :vl-genif)
                 (equal (tag item) :vl-gencase)
                 (equal (tag item) :vl-genbegin)
                 (equal (tag item) :vl-genarray)
                 (equal (tag item) :vl-genbase)
                 (equal (tag item) :vl-genvar)
                 (equal (tag item) :vl-interfaceport)
                 (equal (tag item) :vl-paramdecl)
                 (equal (tag item) :vl-vardecl)
                 (equal (tag item) :vl-fundecl)
                 (equal (tag item) :vl-taskdecl)
                 (equal (tag item) :vl-typedef)
                 (equal (tag item) :vl-dpiimport)
                 (equal (tag item) :vl-modport))))
  :rule-classes ((:forward-chaining))
  :hints(("Goal"
          :use ((:instance tag-when-vl-scopeitem-p-forward
                 (x (b* (((mv item ?item-ss ?path)
                          (vl-scopestack-find-item/ss/path name ss)))
                      item))))))))




(define vl-scopedef-interface-p ((x vl-scopedef-p))
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :hooks nil
  (mbe :logic (vl-interface-p x)
       :exec (eq (tag x) :vl-interface)))


#||
(trace$ #!vl (vl-follow-hidexpr-aux-fn
              :entry (list 'vl-follow-hidexpr-aux
                           (with-local-ps (vl-pp-hidexpr x))
                           (vl-scopestack->hashkey ss))
              :exit (b* (((list ?err ?new-trace ?tail)))
                      (list 'vl-follow-hidexpr-aux
                            (and err (with-local-ps (vl-cw "~@0" err)))
                            ;; (with-local-ps (vl-pp-hidexpr tail))
                            ))))

||#
(with-output
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil)
          :term nil)
  :off (event)
  (define vl-follow-hidexpr-aux
    :parents (vl-follow-hidexpr)
    :short "Core routine for following hierarchical identifiers."
    ((x     vl-hidexpr-p    "HID expression fragment that we are following.")
     (trace vl-hidtrace-p   "Accumulator for the trace until now.")
     (ss    vl-scopestack-p "Current scopestack we're working from.")
     &key
     (strictp booleanp)
     ((elabpath vl-elabtraversal-p) 'elabpath)
     ((origx vl-scopeexpr-p      "Original version of X, for better error messages.") 'origx))
    :returns
    (mv (err     (iff (vl-msg-p err) err)
                 "A @(see vl-msg-p) on any error.")
        (new-trace vl-hidtrace-p
                   "On success, a nonempty trace that records all the items we
                  went through to resolve this HID.  The @(see car) of the
                  trace is the final item and scopestack.")
        (tail    vl-hidexpr-p
                 "Remainder of @('x') after arriving at the declaration."))
    :long "<p>See @(see vl-follow-hidexpr) for detailed discussion.  This
@('-aux') function does most of the work, but for instance it doesn't deal with
top-level hierarchical identifiers.</p>"
    :measure (vl-hidexpr-count x)
    :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                        (implies (or (vl-module-p x)
                                     (vl-interface-p x))
                                 (vl-scope-p x))))
               (local (in-theory (disable double-containment
                                          ;tag-reasoning
                                          )))

               (local (defthm vl-maybe-expr-p-of-car-exprlist
                        (implies (vl-exprlist-p x)
                                 (vl-maybe-expr-p (car x))))))
    :hooks ((:fix
             :hints(("Goal"
                     :expand ((:free (trace ss strictp elabpath) (vl-follow-hidexpr-aux x trace ss :strictp strictp :elabpath elabpath))
                              (:free (trace ss strictp elabpath) (vl-follow-hidexpr-aux (vl-expr-fix x) trace ss :strictp strictp :elabpath elabpath)))))))
    (b* ((trace (vl-hidtrace-fix trace))
         (x     (vl-hidexpr-fix x))
         ((mv name1 indices rest kind)
          (vl-hidexpr-case x
            :end (mv x.name nil nil :end)
            :dot (b* (((vl-hidindex x.first)))
                   (mv x.first.name x.first.indices x.rest :dot))))

         ((when (eq name1 :vl-$root))
          (mv (vl-follow-hidexpr-error (vmsg "$root is not yet supported") ss)
              trace x))

         ((mv item item-ss item-path) (vl-scopestack-find-item/ss/path name1 ss))
         ((unless item)
          (mv (vl-follow-hidexpr-error (vmsg "item not found") ss)
              trace x))
         (elabpath (vl-elabpaths-append item-path elabpath))

         ((when (or (eq (tag item) :vl-vardecl)
                    (eq (tag item) :vl-paramdecl)
                    (eq (tag item) :vl-genvar)))
          ;; Found the declaration we want.  We aren't going to go any further:
          ;; there may be additional HID indexing stuff left, but if so it's just
          ;; array or structure indexing for the tail.

          (b* ((trace (cons (make-vl-hidstep :name name1
                                             :item item
                                             ;; No indices -- they belong to
                                             ;; the variable
                                             :ss item-ss
                                             :elabpath elabpath)
                            trace)))
            (mv nil trace x)))

         ;; From here on out, if the trace is good and the index exists, the
         ;; trace includes that index.
         (trace (cons (make-vl-hidstep :name name1
                                       :item item
                                       :index (car indices)
                                       :ss item-ss
                                       :elabpath elabpath)
                      trace))

         ((when (or (eq (tag item) :vl-fundecl)
                    (eq (tag item) :vl-taskdecl)))
          (if (eq kind :end)
              ;; Plain reference to, e.g., foo.bar.myfun.  This is OK -- you
              ;; might be writing something like ``logic foo = submod.fn(arg)''
              (mv nil trace x)
            ;; Indexed or dotted reference like foo.bar.myfun[3] or
            ;; foo.bar.myfun[3].baz or foo.bar.myfun.baz, none of which seem to
            ;; really be reasonable as things to refer to hierarchically.
            (mv (vl-follow-hidexpr-error (vmsg
                                          (if (eq (tag item) :vl-fundecl)
                                              "hierarchical reference into function"
                                            "hierarchical reference into task"))
                                         item-ss)
                trace x)))

         ((when (eq (tag item) :vl-dpiimport))
          (if (eq kind :end)
              ;; Plain reference to, e.g., foo.bar.myfun.  Seems OK.
              (mv nil trace x)
            ;; Indexed or dotted reference like foo.bar.myfun[3] or
            ;; foo.bar.myfun[3].baz or foo.bar.myfun.baz, seems too hard.
            (mv (vl-follow-hidexpr-error (vmsg "hierarchical reference into DPI import") item-ss)
                trace x)))

         ((when (eq (tag item) :vl-modport))
          (if (eq kind :end)
              ;; Plain reference to, e.g., myinterface.mymodport.  This would
              ;; not make any sense, but note (25.5, Section 718) that when you
              ;; instantiate a submodule that takes interfaces, you can do a
              ;; really awful thing where you choose the modport to use *at
              ;; instantiation time* instead of at module declaration time.
              ;; That is, you can write things like:
              ;;
              ;;    mymod myinst (.mybus(mybus.consumer), ...)
              ;;
              ;; And in this case, the mybus.consumer is going to be a
              ;; hierarchical reference to a modport.
              (mv nil trace x)
            ;; Indexed or dotted reference like foo.bar.mymodport[3] or
            ;; foo.bar.mymodport[3].baz or foo.bar.mymodport.baz; doesn't
            ;; seem like this probably makes any sense?
            (mv (vl-follow-hidexpr-error (vmsg "hierarchical reference into modport") item-ss)
                trace x)))

         ((when (eq (tag item) :vl-modinst))
          (b* (((vl-modinst item))
               (dims    (and item.range (list (vl-range->dimension item.range))))
               (ifacep  (let ((def (vl-scopestack-find-definition item.modname ss)))
                          (and def (vl-scopedef-interface-p def))))
               ;; Start by checking for sensible array indexing.
               (err (vl-follow-hidexpr-dimscheck
                     name1 indices dims
                     :strictp strictp
                     ;; It seems OK to refer directly to an interface.
                     :direct-okp ifacep))
               ((when err)
                (mv (vl-follow-hidexpr-error err item-ss)
                    trace x))
               ((when (eq kind :end))
                ;; Reference to foo.bar.myinst with no more indexing into myinst.
                ;; This might not make a lot of sense for a module instance, but
                ;; it probably *does* make sense for an interface instance.  It
                ;; seems reasonable to just say this is OK and let the caller
                ;; figure out what to do with the module instance.
                (mv nil trace x))
               ;; Else we're indexing through the instance.  We need to go look
               ;; up the submodule and recur.
               ((mv mod mod-ss)
                (vl-scopestack-find-definition/ss item.modname item-ss))
               ((unless mod)
                (mv (vl-follow-hidexpr-error (vmsg "reference through missing module ~s0" item.modname) item-ss)
                    trace x))
               (modtag (tag mod))
               ((when (eq modtag :vl-udp))
                (mv (vl-follow-hidexpr-error (vmsg "reference through primitive ~s0" item.modname) item-ss)
                    trace x))
               ((unless (or (eq modtag :vl-module)
                            (eq modtag :vl-interface)))
                (mv (vl-follow-hidexpr-error
                     (vmsg "module instance ~s0 of ~s1: invalid type ~x2???"
                           name1 item.modname modtag)
                     item-ss)
                    trace x))
               (mod-path (list (vl-elabinstruction-push-named (vl-elabkey-def item.modname))
                               (vl-elabinstruction-root)))
               (next-ss
                ;; The MOD-SS is just the scopestack for where the module is
                ;; defined, which in practice will be the top level scope.
                ;; The next part of the HID needs to be looked up from within
                ;; MOD, so we need to actually go into the module.
                (vl-scopestack-push mod mod-ss)))
            (vl-follow-hidexpr-aux rest trace next-ss :strictp strictp :elabpath mod-path)))

         ((when (eq (tag item) :vl-interfaceport))
          ;; BOZO.  We don't yet implement the access restrictions described in
          ;; SystemVerilog-2012 Section 25.7.  For example:
          ;;
          ;; interface myInterface ;
          ;;   wire [3:0] a, b, c;
          ;;   modport blah (input a, output b);
          ;; endinterface
          ;;
          ;; module useInterface(myInterface.blah iface) ;
          ;;   assign iface.b = iface.a;                     // <-- this is legal
          ;;   assign iface.c = iface.a;                     // <-- not legal: shouldn't see "c"
          ;; endmodule
          ;;
          ;; NCVerilog reports the access of iface.c as a hierarchical name
          ;; component lookup failure.  VCS reports that c can't be accessed
          ;; from interface "iface" of modport "blah", and suggests checking
          ;; whether the signal is declared in the modport.  It seems likely
          ;; that we could possibly implement this here if we were smart enough
          ;; to look at the modport (if any) and prohibit names that aren't
          ;; mentioned in it.
          (b* (((vl-interfaceport item))
               (err (vl-follow-hidexpr-dimscheck
                     name1 indices item.udims :strictp strictp :direct-okp t))
               ((when err)
                ;; BOZO.  What kind of index checking do we want to do?  Probably
                ;; it is ok to index only partly into an interface port, because
                ;; if it's okay to have an array of interfaces coming in, then
                ;; it's probably ok to stick an array of interfaces into a
                ;; submodule, etc.  So maybe we need to just check that we have
                ;; no more indices than are allowed, and then check ranges on any
                ;; indices that we do happen to have...
                (mv (vl-follow-hidexpr-error err item-ss)
                    trace x))
               ((when (eq kind :end))
                ;; Stopping at this interface port.  Unlike module instances,
                ;; this seems OK.  The interface port itself acts like a
                ;; variable.
                (mv nil trace x))
               ((mv iface iface-ss)
                (vl-scopestack-find-definition/ss item.ifname item-ss))
               ((unless iface)
                (mv (vl-follow-hidexpr-error (vmsg "reference through missing interface ~s0" item.ifname)
                                             item-ss)
                    trace x))
               (iftag (tag iface))
               ((unless (eq iftag :vl-interface))
                (mv (vl-follow-hidexpr-error
                     (vmsg "interface port ~s0 of interface ~s1: invalid type ~x2???"
                           name1 item.ifname iftag)
                     item-ss)
                    trace x))
               (next-ss (vl-scopestack-push iface iface-ss))
               (iface-path (list (vl-elabinstruction-push-named (vl-elabkey-def item.ifname))
                                 (vl-elabinstruction-root))))
            (vl-follow-hidexpr-aux rest trace next-ss
                                   :strictp strictp
                                   :elabpath iface-path)))

         ((when (eq (tag item) :vl-genbegin))
          (b* (((when (consp indices))
                ;; Doesn't make any sense: this is a single, named generate
                ;; block, not an array, so we shouldn't try to index into it.
                (mv (vl-follow-hidexpr-error "array indices on reference to generate block" item-ss)
                    trace x))
               ((when (eq kind :end))
                ;; Doesn't make any sense: referring to foo.bar.myblock all by
                ;; itself.
                (mv (vl-follow-hidexpr-error "reference to generate block" item-ss)
                    trace x))
               ;; Else we have something like foo.bar.myblock.mywire or whatever.
               ;; This is fine, we just need to go into the generate block.
               (genblob (vl-sort-genelements (vl-genblock->elems (vl-genbegin->block item))
                                             :scopetype :vl-genblock
                                             :id name1))
               (next-ss (vl-scopestack-push genblob item-ss))
               (next-path (cons (vl-elabinstruction-push-named (vl-elabkey-item name1))
                                elabpath)))
            (vl-follow-hidexpr-aux rest trace next-ss
                                   :strictp strictp :elabpath next-path)))

         ((when (eq (tag item) :vl-genarray))
          (b* (((when (eq kind :end))
                ;; Doesn't make any sense.  Either this is a raw reference to the
                ;; array like foo.bar.mygenarray, or is an indexed reference to
                ;; something like foo.bar.mygenarray[3], but in either case it
                ;; would be referring to a whole generate block or to an array of
                ;; generate blocks, not something inside those blocks.
                (mv (vl-follow-hidexpr-error "reference to generate array" item-ss)
                    trace x))
               ((unless (consp indices))
                ;; Something like foo.bar.mygenarray.baz, but mygenarray is an
                ;; array so this doesn't make any sense.
                (mv (vl-follow-hidexpr-error "reference through generate array must have an array index"
                                             item-ss)
                    trace x))
               ((unless (atom (rest indices)))
                ;; Something like foo.bar.mygenarray[3][4].baz, but we should
                ;; only ever have single-dimensional generate arrays, right?
                (mv (vl-follow-hidexpr-error "too many indices through generate array" item-ss)
                    trace x))
               (index-expr (first indices))
               ((unless (vl-expr-resolved-p index-expr))
                ;; Something like foo.bar.mygenarray[width-1].baz.  We tolerate
                ;; this in the case of module instances, but for generates it is
                ;; not safe because we could have something like:
                ;;
                ;;     genvar i;
                ;;     for(i = 1; i < 10; ++i) begin : mygenarray
                ;;        wire [i-1:0] baz;
                ;;        ...
                ;;     end
                ;;
                ;; in which case the actual declaration of baz depends on the
                ;; particular block of the generate that we happen to be in.
                (mv (vl-follow-hidexpr-error "unresolved index into generate array" item-ss)
                    trace x))
               (blocknum (vl-resolved->val index-expr))
               (block    (vl-genblocklist-find-block blocknum
                                                     (vl-genarray->blocks item)))
               ((unless block)
                ;; Something like foo.bar.mygenarray[8].baz when the array only
                ;; goes from 3:7 or whatever.
                (mv (vl-follow-hidexpr-error (vmsg "invalid index into generate array: ~x0" blocknum)
                                             item-ss)
                    trace x))

               ;; Our discipline is that we're going to treat
               ;;   - The array as a whole, and
               ;;   - The individual block for this index
               ;;
               ;; as BOTH being scope levels.  We are therefore going to:
               ;;   - push both onto the scope stack
               ;;   - represent both in the elabscopes traversal we're constructing
               ;;
               ;; This discipline is meant to ensure consistency between the
               ;; scopestack view, elabscopes view, and SV view of the scope
               ;; hierarchy.
               (array-scope
                ;; From the scopestack perspective, the scope for the array
                ;; won't actually have anything in it.  (In elabscopes and SV
                ;; it will have all of the sub-blocks.)
                (vl-sort-genelements nil
                                     :scopetype :vl-genarray
                                     :id name1))
               (block-scope
                (vl-sort-genelements (vl-genblock->elems block)
                                     :scopetype :vl-genarrayblock
                                     ;; This "name" is actually an integer, the
                                     ;; index of the block.
                                     :id blocknum))
               (next-ss (vl-scopestack-push block-scope
                         (vl-scopestack-push array-scope item-ss)))
               (next-path (list* (vl-elabinstruction-push-named (vl-elabkey-index blocknum))
                                 (vl-elabinstruction-push-named (vl-elabkey-item name1))
                                elabpath)))
            (vl-follow-hidexpr-aux rest trace next-ss :strictp strictp :elabpath next-path)))

         ((when (eq (tag item) :vl-typedef))
          (b* (((when (eq kind :end))
                ;; This seems ok; we might refer to a type by name in a few
                ;; places.  It may or may not be ok to refer to foo.bar_t, but
                ;; it's definitely ok to refer to foopkg::bar_t.
                (mv nil trace x)))
            ;; I don't think this makes sense?  Can you refer to a type name?  BOZO
            ;; maybe this makes sense for things like $bits(mystruct_t.foo) or
            ;; something like that?  If so it may still be that we don't want to
            ;; deal with this in the aux function, but rather it should be
            ;; something that the top-level wrapper deals with.
            (mv (vl-follow-hidexpr-error "hierarchical reference through typedef" item-ss)
                trace x)))

         ((when (or (eq (tag item) :vl-genif)
                    (eq (tag item) :vl-gencase)
                    (eq (tag item) :vl-genloop)
                    (eq (tag item) :vl-genbase)))
          ;; I don't think any of these are supposed to have names and,
          ;; accordingly, it shouldn't make sense to have looked one up.
          (mv (vl-follow-hidexpr-error (vmsg "hierarchical reference to ~x0" (tag item))
                                       item-ss)
              trace x))

         ((when (eq (tag item) :vl-gateinst))
          ;; Since gate instances are "opaque" there is clearly no way we can go
          ;; through a gate instance.  Moreover, we don't think a gate instance
          ;; could be meaningfully addressed in any other way.  So, we just
          ;; regard any reference to a gate as invalid.
          (mv (vl-follow-hidexpr-error "hierarchical reference to gate instance" item-ss)
              trace x)))

      (mv (impossible) trace x))
    ///
    (more-returns
     (new-trace (implies (or (consp trace)
                             (not err))
                         (consp new-trace))
                :name consp-of-vl-follow-hidexpr-aux.new-trace))

    (defret vl-follow-hidexpr-no-index-on-first
      (implies (not err)
               (not (vl-hidstep->index (car new-trace)))))

    (defthm context-irrelevance-of-vl-follow-hidexpr-aux
      (implies (syntaxp (not (equal origx  (list 'quote (with-guard-checking :none (vl-scopeexpr-fix nil))))))
               (b* (((mv err1 trace1 tail1) (vl-follow-hidexpr-aux x trace ss
                                                                   :elabpath elabpath
                                                                   :strictp strictp
                                                                   :origx origx))
                    ((mv err2 trace2 tail2) (vl-follow-hidexpr-aux x trace ss
                                                                   :elabpath elabpath
                                                                   :strictp strictp
                                                                   :origx (vl-scopeexpr-fix nil))))
                 (and (equal trace1 trace2)
                      (equal tail1 tail2)
                      (iff err1 err2))))
      :hints ((acl2::just-induct-and-expand
               (vl-follow-hidexpr-aux x trace ss
                                      :elabpath elabpath
                                      :strictp strictp
                                      :origx origx)
               :expand-others
               ((:free (ctx strictp origx)
                 (vl-follow-hidexpr-aux x trace ss
                                        :elabpath elabpath
                                        :strictp strictp
                                        :origx origx))))))

    (defret count-of-vl-follow-hidexpr-aux.tail
      (<= (vl-hidexpr-count tail)
          (vl-hidexpr-count x))
      :rule-classes :linear)

    (local (defthm vl-hidname-stringp-when-not-$root
             (implies (vl-hidname-p x)
                      (equal (equal x :vl-$root)
                             (not (stringp x))))
             :hints(("Goal" :in-theory (enable vl-hidname-p)))))

    (defret vl-subhid-p-of-vl-follow-hidexpr-aux
      (implies (not err)
               (vl-subhid-p tail x))
      :hints(("Goal" :in-theory (enable vl-subhid-p)
              :induct (vl-follow-hidexpr-aux x trace ss :elabpath elabpath :strictp strictp :origx origx))))))


(deftagsum vl-select
  :layout :tree
  (:field ((name stringp "The name of the field we're selecting")))
  (:index ((val  vl-expr-p "The index we're selecting"))))

(defprod vl-selstep
  ((select vl-select-p   "The field or index being selected")
   (type vl-datatype-p   "The datatype of the element we've selected")
   (caveat               "Signedness caveat for this indexing operation.  Signals
                          a disagreement between implementations on the signedness
                          of the result.  See @(see vl-datatype-remove-dim).  Only
                          important if this is the outermost selstep.")
   ;; (ss vl-scopestack-p   "The scopestack in which the datatype was declared or
   ;;                        typedef'd")
   )
  :layout :tree)

(fty::deflist vl-seltrace :elt-type vl-selstep :elementp-of-nil nil)


(define vl-seltrace-index-count ((x vl-seltrace-p))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (b* (((vl-selstep x1) (car x)))
         (vl-select-case x1.select :field 0 :index 1))
       (vl-seltrace-index-count (cdr x)))))

(define vl-seltrace->indices ((x vl-seltrace-p))
  :returns (indices vl-exprlist-p)
  (if (atom x)
      nil
    (b* (((vl-selstep x1) (car x)))
      (vl-select-case x1.select
        :field (vl-seltrace->indices (cdr x))
        :index (cons x1.select.val (vl-seltrace->indices (cdr x))))))
  ///
  (defret len-of-vl-seltrace->indices
    (equal (len indices) (vl-seltrace-index-count x))
    :hints(("Goal" :in-theory (enable vl-seltrace-index-count))))

  (defthm vl-seltrace-indices-of-append
    (equal (vl-seltrace->indices (append x y))
           (append (vl-seltrace->indices x)
                   (vl-seltrace->indices y))))

  (defthm vl-seltrace-indices-of-rev
    (equal (vl-seltrace->indices (rev x))
           (rev (vl-seltrace->indices x)))))

(deftagsum vl-scopecontext
  (:local     ((levels natp :rule-classes :type-prescription
                       "How many levels up from the current scope was the item found")))
  (:root      ())
  (:package   ((pkg vl-package-p)))
  (:module    ((mod vl-module-p)))
  (:interface ((iface vl-interface-p)))
  :layout :tree)


(local (defthm top-level-design-elements-are-modules-or-interfaces
         (implies (and (member-equal name (vl-design-toplevel design))
                       (not (member-equal name (vl-modulelist->names (vl-design->mods design)))))
                  (member-equal name (vl-interfacelist->names (vl-design->interfaces design))))
         :hints(("Goal" :in-theory (enable vl-design-toplevel)))))

(local (defthm vl-scope-p-when-vl-interface-p-unbounded
         (implies (vl-interface-p x)
                  (vl-scope-p x))))

(local (defthm vl-scope-p-when-vl-module-p-unbounded
         (implies (vl-module-p x)
                  (vl-scope-p x))))

#||

(trace$ #!vl (vl-follow-hidexpr-fn
              :entry (list 'vl-follow-hidexpr
                           (with-local-ps (vl-pp-hidexpr x))
                           (vl-scopestack->hashkey ss))
              :exit (b* (((list ?err ?trace ?context ?tail) values))
                      (list 'vl-follow-hidexpr
                            (and err (with-local-ps (vl-cw "~@0" err)))))))

||#


(define vl-follow-hidexpr
  :short "Follow a HID to find the associated declaration."
  ((x       vl-hidexpr-p       "Hierarchical identifier to follow.")
   (ss      vl-scopestack-p "Scopestack where the HID originates.")
   &key
   ((origx vl-scopeexpr-p      "Original version of X, for better error messages.") 'origx)
   (strictp booleanp "Require all array indices and bounds to be resolved?")
   ((elabpath vl-elabtraversal-p) 'nil))
  :guard-debug t
  :returns
  (mv (err   (iff (vl-msg-p err) err)
             "A message on any error.")
      (trace vl-hidtrace-p
             "On success: a non-empty trace that records all the items we went
              through to resolve this HID.  The @(see car) of the trace is the
              final declaration for this HID.")
      (context (implies (not err) (vl-scopecontext-p context))
               "On success, a scopecontext object describing where this hid is
                rooted.")
      (tail  vl-hidexpr-p
             "On success: the remainder of @('x') after arriving at the
              declaration.  This may include array indexing or structure
              indexing."))

  :long "<p>Prerequisite: see @(see hid-tools) for considerable discussion
about the goals and design of this function.</p>

<p>This is our top-level routine for following hierarchical identifiers.  It
understands how to resolve both top-level hierarchical identifiers like
@('topmodule.foo.bar') and downward identifiers like
@('submodname.foo.bar').</p>

<p>We try to follow @('x'), which must be a proper @(see vl-hidexpr-p), to
whatever @(see vl-scopeitem) it refers to.  This can fail for many reasons,
e.g., any piece of @('x') might refer to a name that doesn't exist, might have
inappropriate array indices, etc.  In case of failure, @('err') is a good @(see
vl-msg-p) and the other results are <b>not sensible</b> and should not be
relied on.</p>

<h5>Trace</h5>

<p>We return a @(see vl-hidtrace-p) that records, in ``backwards'' order, the
steps that we took to resolve @('x').  That is: if we are resolving
@('foo.bar.baz'), then the first step in the trace will be the declaration for
@('baz'), and the last step in the trace will be the lookup for @('foo').  In
other words, the first step in the trace corresponds to the ``final''
declaration that @('x') refers to.  Many applications won't care about the rest
of the trace beyond its first step.  However, the rest of the trace may be
useful if you are trying to deal with, e.g., all of the interfaces along the
hierarchical identifier.</p>

<h5>Tail</h5>

<p>The trace we return stops at variable declarations.  This may be confusing
because, in Verilog, the same @('.') syntax is used to index through the module
hierarchy and to index through structures.  To make this concrete, suppose we
have something like:</p>

@({
     typedef struct { logic fastMode; ...; } opcode_t;
     typedef struct { opcode_t opcode; ... } instruction_t;

     module bar (...) ;
       instruction_t instruction1;
       ...
     endmodule

     module foo (...) ;
       bar mybar(...) ;
       ...
     endmodule

     module main (...) ;
       foo myfoo(...) ;
       ...
       $display(\"fastMode is %b\", myfoo.mybar.instruction1.opcode.fastMode);
     endmodule
})

<p>When we follow @('myfoo.mybar.instruction1.opcode.fastMode'), our trace will
<b>only go to @('instruction1')</b>, because the @('.opcode.fastMode') part is
structure indexing, not scope indexing.</p>

<p>To account for this, we return not only the @('trace') but also the
@('tail') of the hierarchical identifier that remains where we stop.  For
instance, in this case the @('tail') would be
@('instruction1.opcode.fastMode').</p>"

  (b* ((x     (vl-hidexpr-fix x))
       ((mv name1 indices rest kind)
        (vl-hidexpr-case x
          :end (mv x.name nil nil :end)
          :dot (b* (((vl-hidindex x.first)))
                 (mv x.first.name x.first.indices x.rest :dot))))

       (trace nil)

       ((when (eq name1 :vl-$root))
        (mv (vl-follow-hidexpr-error "$root isn't supported yet" ss)
            trace nil x))

       ((mv item ctx-ss pkg-name) (vl-scopestack-find-item/context name1 ss))
       ((when item)
        (b* (((mv err trace tail)
              ;; Starting from the original SS, don't get an elabpath from the lookup above
              (vl-follow-hidexpr-aux x nil ss :strictp strictp :elabpath elabpath))
             ((when err) (mv err trace nil tail))
             ((mv err context)
              (cond (pkg-name
                     (b* ((pkg (vl-scopestack-find-package pkg-name ss))
                          ((unless pkg)
                           (mv (vmsg "Programming error: found item in ~
                                      package ~s0 but couldn't find package"
                                     pkg-name)
                               nil)))
                       (mv nil (make-vl-scopecontext-package :pkg pkg))))
                    ((vl-scopestack-case ctx-ss :global)
                     (mv nil (make-vl-scopecontext-root)))
                    (t (mv nil
                           (make-vl-scopecontext-local
                            :levels (- (vl-scopestack-nesting-level ss)
                                       (vl-scopestack-nesting-level ctx-ss))))))))
          (mv err trace context tail)))

       ((when (eq kind :end))
        ;; Item was not found AND it is not of the form foo.bar, so we do NOT
        ;; want to interpret it as any sort of reference to a top-level module.
        (mv (vl-follow-hidexpr-error "item not found" ss) trace nil x))

       ;; Otherwise, might be a valid reference into a top-level module?
       (design   (vl-scopestack->design ss))
       ((unless design)
        ;; We must be using a phony scopestack.  We have no way of knowing what
        ;; the top-level modules are so we have no idea if this is valid.
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace nil x))

       (toplevel (vl-design-toplevel design))
       ((unless (member-equal name1 toplevel))
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace nil x))

       ;; Successfully found a top-level module with the first index name.
       ((when (consp indices))
        ;; Something like topmod[3].foo.bar, doesn't make any sense.
        (mv (vl-follow-hidexpr-error "array indices into top level module" ss)
            trace nil x))

       (topdef     (or (vl-find-module name1 (vl-design->mods design))
                       (vl-find-interface name1 (vl-design->interfaces design))))
       (topdef-ss  (vl-scopestack-init design))

       ;; BOZO how should the fact that we have followed a top-level hierarchical
       ;; identifier present itself in the trace?  We would like to perhaps add a
       ;; trace step along the lines of:
       ;;
       ;;   (cons (make-vl-hidstep :item mod :ss mod-ss) trace)
       ;;
       ;; But that is not possible because the ITEM for a trace needs to be a
       ;; scopeitem, and a module is not a scopeitem.
       ;;
       ;; We might eventually want to extend the notion of traces to be able to
       ;; record this sort of thing.  For now, out of sheer pragmatism, I think
       ;; it seems pretty reasonable to just not bother to record the first
       ;; step.
       (next-ss (vl-scopestack-push topdef topdef-ss))
       (elabpath (list (vl-elabinstruction-push-named (vl-elabkey-def name1))
                       (vl-elabinstruction-root)))

       ((mv err trace tail)
        (vl-follow-hidexpr-aux rest trace next-ss
                               :strictp strictp :elabpath elabpath))

       (context (if (eq (tag topdef) :vl-module)
                    (make-vl-scopecontext-module :mod topdef)
                  (make-vl-scopecontext-interface :iface topdef))))
    (mv err trace context tail))
  ///
  (defret consp-of-vl-follow-hidexpr.trace
    (implies (not err)
             (consp trace)))

  (defret count-of-vl-follow-hidexpr.tail
    (<= (vl-hidexpr-count tail)
        (vl-hidexpr-count x))
    :rule-classes :linear)

  (local (defthm vl-hidname-stringp-when-not-$root
           (implies (vl-hidname-p x)
                    (equal (equal x :vl-$root)
                           (not (stringp x))))
           :hints(("Goal" :in-theory (enable vl-hidname-p)))))

  (defret vl-subhid-p-of-vl-follow-hidexpr
    (implies (not err)
             (vl-subhid-p tail x))
    :hints(("Goal" :in-theory (enable vl-subhid-p)))))

#||

(trace$ #!vl (vl-follow-scopeexpr-fn
              :entry (list 'vl-follow-scopeexpr
                           (with-local-ps (vl-pp-scopeexpr x))
                           (vl-scopestack->hashkey ss))
              :exit (b* (((list ?err ?trace ?context ?tail) values))
                      (list 'vl-follow-scopeexpr
                            (and err (with-local-ps (vl-cw "~@0" err)))))))

||#

(define vl-follow-scopeexpr
  :short "Follow a scope expression to find the associated declaration."
  ((x vl-scopeexpr-p "Scope expression to follow.")
   (ss      vl-scopestack-p "Scopestack where the lookup originates.")
   &key
   (strictp booleanp "Require all array indices and bounds to be resolved?"))
  :returns
  (mv (err   (iff (vl-msg-p err) err)
             "A message for any error.")
      (trace vl-hidtrace-p
             "On success: a non-empty trace that records all the items we went
              through to resolve this HID.  The @(see car) of the trace is the
              final declaration for this HID.")
      (context (implies (not err) (vl-scopecontext-p context))
               "On success, a scopecontext showing where the hid is found.")
      (tail  vl-hidexpr-p
             "On success: the remainder of @('x') after arriving at the
              declaration.  This may include array indexing or structure
              indexing."))
  (vl-scopeexpr-case x
    :end
    (vl-follow-hidexpr x.hid ss :strictp strictp :origx x :elabpath nil)

    :colon
    (b* ((x (vl-scopeexpr-fix x))
         ((unless (stringp x.first))
          (mv (vmsg "~a0: The scope modifier '~x1' is not yet supported."
                    x
                    (case x.first
                      (:vl-local "local")
                      (:vl-$unit "$unit")
                      (otherwise "??UNKNOWN??")))
              nil nil (vl-scopeexpr->hid x)))
         ((mv package pkg-ss) (vl-scopestack-find-package/ss x.first ss))
         ((unless package)
          (mv (vmsg "~a0: Package ~s1 not found.."
                    x x.first)
              nil nil (vl-scopeexpr->hid x)))
         (pkg-ss (vl-scopestack-push package pkg-ss))
         ((unless (vl-scopeexpr-case x.rest :end))
          (mv (vmsg "~a0: Multiple levels of :: operators are ~
                                     not yet supported."
                    x)
              nil nil (vl-scopeexpr->hid x)))
         (elabpath (list (vl-elabinstruction-push-named (vl-elabkey-package x.first))
                         (vl-elabinstruction-root)))
         ((mv err trace context tail)
          (vl-follow-hidexpr
           (vl-scopeexpr-end->hid x.rest)
           pkg-ss  :strictp strictp :origx x :elabpath elabpath))
         ((when err) (mv err trace context tail))
         ((unless (vl-scopecontext-case context :local))
          (mv nil trace context tail)))
      (mv nil trace (make-vl-scopecontext-package :pkg package) tail)))
  ///
  (defret consp-of-vl-follow-scopeexpr.trace
    (implies (not err)
             (consp trace)))

  (defret count-of-vl-follow-scopeexpr.tail
    (< (vl-hidexpr-count tail)
       (vl-scopeexpr-count x))
    :rule-classes :linear)

  (defret vl-subhid-p-of-vl-follow-scopeexpr
    (implies (not err)
             (vl-subhid-p tail (vl-scopeexpr->hid x)))
    :hints(("Goal" :in-theory (enable vl-scopeexpr->hid)))))


;; ------




(defines vl-datatype-usertype-resolve


  (define vl-datatype-usertype-resolve ((x vl-datatype-p)
                                        (ss vl-scopestack-p)
                                        &key
                                        ((scopes vl-elabscopes-p) 'nil)
                                        ((rec-limit natp) '1000))
    :verify-guards nil
    :measure (two-nats-measure rec-limit (vl-datatype-count x))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (new-x vl-datatype-p))
    (b* ((x (vl-datatype-fix x)))
      (vl-datatype-case x
        :vl-coretype (mv nil x)
        :vl-struct (b* (((mv err members)
                         (vl-structmemberlist-usertype-resolve
                          x.members ss :scopes scopes :rec-limit rec-limit)))
                     (mv err (change-vl-struct x :members members)))
        :vl-union  (b* (((mv err members)
                         (vl-structmemberlist-usertype-resolve
                          x.members ss :scopes scopes :rec-limit rec-limit)))
                     (mv err (change-vl-union x :members members)))
        :vl-enum   (b* (((mv err basetype)
                         (vl-datatype-usertype-resolve
                          x.basetype ss :scopes scopes :rec-limit rec-limit)))
                     (mv err (change-vl-enum x :basetype basetype)))
        :vl-usertype (b* (((when (and x.res (vl-datatype-resolved-p x.res)))
                           (mv nil x))
                          ((mv err def)
                           (vl-usertype-lookup x.name ss :scopes scopes :rec-limit rec-limit)))
                       (mv err (change-vl-usertype x :res def))))))

  (define vl-structmemberlist-usertype-resolve ((x vl-structmemberlist-p)
                                                (ss vl-scopestack-p)
                                                &key
                                                ((scopes vl-elabscopes-p) 'nil)
                                                ((rec-limit natp) '1000))
    :measure (two-nats-measure rec-limit (vl-structmemberlist-count x))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (new-x vl-structmemberlist-p))
    (b* (((when (atom x)) (mv nil nil))
         ((mv err1 type1)
          (vl-datatype-usertype-resolve
           (vl-structmember->type (car x)) ss :scopes scopes :rec-limit rec-limit))
         ((mv err2 rest)
          (vl-structmemberlist-usertype-resolve (cdr x) ss :scopes scopes :rec-limit
                                                rec-limit)))
      (mv (or err1 err2)
          (cons (change-vl-structmember (car x) :type type1) rest))))

  (define vl-usertype-lookup ((x vl-scopeexpr-p "The usertype name to look up")
                              (ss vl-scopestack-p)
                              &key
                              ((scopes vl-elabscopes-p) 'nil)
                              ((rec-limit natp) '1000))
  :short "Looks up a usertype name and returns its definition if successful."
  :measure (two-nats-measure rec-limit 0)
  :returns (mv (err (iff (vl-msg-p err) err)
                    "Error message if unsuccessful")
               (type (and (vl-maybe-datatype-p type)
                          (implies (not err)
                                   (vl-datatype-p type)))
                     "Fully resolved type, if successful"))
  (b* ((x (vl-scopeexpr-fix x))
       (scopes (vl-elabscopes-fix scopes))
       (hid (vl-scopeexpr->hid x))
       ;; BOZO Maybe we should use a different type than scopeexpr for a usertype name
       ((unless (vl-hidexpr-case hid :end))
        (mv (vmsg "Type names cannot be specified with dotted ~
                                   paths, only package scopes: ~a1"
                  nil x)
            nil))
       ((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x ss))
       ((when err)
        (mv err nil))
       ((vl-hidstep ref) (car trace))
       (name1 (vl-hidexpr-name1 tail))
       ((when (eq name1 :vl-$root))
        (mv (vmsg "$root is not supported") nil))
       ;; Check whether there is elaboration info stored for the type as
       ;; well. If so, use that item instead of the one found in the
       ;; scopestack by follow-scopeexpr.
       (ref-scopes (vl-elabscopes-traverse (rev ref.elabpath) scopes :allow-empty t))
       (info (vl-elabscopes-item-info name1 ref-scopes :allow-empty t))
       (item (or info ref.item))
       
       ((when (eq (tag item) :vl-typedef))
        (b* (((vl-typedef item) item)
             ((when info)
              (if (vl-datatype-resolved-p item.type)
                  (mv nil item.type)
                (mv (vmsg "Programming error: unresolved type ~s0 stored in elaboration"
                          name1) nil)))
             ((when (zp rec-limit))
              (mv (vmsg "Recursion limit ran out looking up ~
                                      usertype ~a0" x)
                  nil)))
          (vl-datatype-usertype-resolve item.type ref.ss
                                        :rec-limit (1- rec-limit)
                                        :scopes ref-scopes)))
       ((when (eq (tag item) :vl-paramdecl))
        (b* (((vl-paramdecl item) item))
          (vl-paramtype-case item.type
            :vl-typeparam
            ;; Note: I think it would be wrong to recur on the parameter type
            ;; here, because it could be overridden with a type from outside
            ;; the module, in which case we don't know what scope it came from.
            (if (and item.type.default
                     (vl-datatype-resolved-p item.type.default))
                (mv nil item.type.default)
              (mv (vmsg "Reference to unresolved type parameter ~a0" item)
                  nil))
            :otherwise
            (mv (vmsg "Reference to data parameter ~a0 as type" item)
                nil)))))
    (mv (vmsg "Didn't find a typedef ~a1, instead found ~a2"
              nil x item)
        nil)))


  ///
  (verify-guards vl-datatype-usertype-resolve-fn)

  (defthm vl-datatype-usertype-resolve-nonnil
    (mv-nth 1 (vl-datatype-usertype-resolve
               x ss :scopes scopes :rec-limit rec-limit))
    :hints (("goal" :use ((:instance
                           (:theorem
                            (implies (not x)
                                     (not (vl-datatype-p x))))
                           (x (mv-nth 1 (vl-datatype-usertype-resolve
                                         x ss :scopes scopes :rec-limit rec-limit)))))
             :in-theory (disable vl-datatype-usertype-resolve)))
    :rule-classes
    ((:type-prescription :typed-term (mv-nth 1 (vl-datatype-usertype-resolve
                                                x ss :scopes scopes :rec-limit rec-limit)))))

  (defthm vl-usertype-lookup-nonnil
    (b* (((mv err res) (vl-usertype-lookup x ss :scopes scopes :rec-limit rec-limit)))
      (implies (not err)
               res))
    :hints (("goal" :use ((:instance return-type-of-vl-usertype-lookup.type))
             :in-theory (disable return-type-of-vl-usertype-lookup.type)))
    :rule-classes
    ((:type-prescription :typed-term (mv-nth 1 (vl-usertype-lookup
                                                x ss :scopes scopes :rec-limit rec-limit)))))

  (defthm-vl-datatype-usertype-resolve-flag
    (defthm vl-datatype-resolved-p-of-vl-datatype-usertype-resolve
      (b* (((mv err new-x)
            (vl-datatype-usertype-resolve x ss :scopes scopes :rec-limit rec-limit)))
        (implies (not err)
                 (vl-datatype-resolved-p new-x)))
      :hints('(:expand ((vl-datatype-resolved-p x))))
      :flag vl-datatype-usertype-resolve)
    (defthm vl-structmemberlist-resolved-p-of-vl-structmemberlist-usertype-resolve
      (b* (((mv err new-x)
            (vl-structmemberlist-usertype-resolve x ss :scopes scopes :rec-limit rec-limit)))
        (implies (not err)
                 (vl-structmemberlist-resolved-p new-x)))
      ;; :hints('(:in-theory (enable vl-structmemberlist-resolved-p)))
      :flag vl-structmemberlist-usertype-resolve)
    (defthm vl-datatype-resolved-p-of-vl-usertype-lookup
      (b* (((mv err type)
            (vl-usertype-lookup x ss :scopes scopes :rec-limit rec-limit)))
        (implies (not err)
                 (vl-datatype-resolved-p type)))
      :flag vl-usertype-lookup))

  (deffixequiv-mutual vl-datatype-usertype-resolve))



(define vl-datatype->structmembers ((x vl-datatype-p))
  :short "Finds the struct members of x when it is a struct or union."
  :returns (mv ok (members vl-structmemberlist-p))
  (vl-datatype-case x
    :vl-struct (mv t x.members)
    :vl-union  (mv t x.members)
    :otherwise (mv nil nil))
  ///
  (defthm vl-structmemberlist-resolved-p-of-vl-datatype->structmembers
    (implies (vl-datatype-resolved-p x)
             (vl-structmemberlist-resolved-p
              (mv-nth 1 (vl-datatype->structmembers x))))
    :hints(("Goal" :in-theory (enable vl-datatype->structmembers)))))

(define vl-find-structmember ((name stringp) (membs vl-structmemberlist-p))
  :returns (memb (iff (vl-structmember-p memb) memb))
  (if (atom membs)
      nil
    (if (equal (string-fix name) (vl-structmember->name (car membs)))
        (vl-structmember-fix (car membs))
      (vl-find-structmember name (cdr membs))))
  ///
  (defthm vl-datatype-resolved-p-of-find-structmember
    (implies (and (vl-structmemberlist-resolved-p members)
                  (vl-find-structmember name members))
             (vl-datatype-resolved-p
              (vl-structmember->type (vl-find-structmember name members))))
    :hints(("Goal" :in-theory (enable vl-structmemberlist-resolved-p)))))






(define vl-datatype-select-ok ((x vl-datatype-p))
  :parents (datatype-tools)
  :short "Determines whether this datatype can be selected."
  :long "<p>The input datatype should not have packed or unpacked dimensions;
if it does, then it's definitely OK to index into it (though it's only a
select if it's the last packed dimension).  The input datatype should have
usertypes resolved.</p>"
  :guard (vl-datatype-resolved-p x)
  :returns (ok)
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-datatype-count x)
  (b* ((x (vl-maybe-usertype-resolve x)))
    (or (consp (vl-datatype->pdims x))
        (consp (vl-datatype->udims x))
        (vl-datatype-case x
          (:vl-coretype
           (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name)))
             ;; Checks whether this is an integer atom type.  If it's an integer
             ;; vector type, it's only selectable if it has dims.
             (and xinfo.size (not (eql xinfo.size 1)))))
          (:vl-struct x.packedp)
          (:vl-union  x.packedp)
          (:vl-enum
           ;; NOTE: This is a little nonsensical, but simulators seem to treat enums
           ;; as if they were always 1-dimensional vectors, even in the case of
         ;;    typedef enum logic {a, b} foo ;
           ;; which you might think would be a 0-dimensional thing.
           t)
          (:vl-usertype (impossible))))))




(define vl-datatype-dims-count ((x vl-datatype-p))
  :short "Gives the number of packed plus unpacked dimensions on a datatype."
  :returns (ndims natp :rule-classes :type-prescription)
  (+ (len (vl-datatype->udims x))
     (len (vl-datatype->pdims x))))


(define vl-datatype-set-unsigned ((x vl-datatype-p))
  :short "Removes any explicit signed indicator from a datatype."
  :long "<p>This is rather specific in purpose and generally shouldn't be used.
The case where it is useful is when we are indexing into an (explicitly signed)
packed array; this means that the whole array is signed, but not the selected
parts.  So we strip the signed qualifier off of the type when we index into
packed dimensions.  (This doesn't apply to usertypes that are defined as signed
types!  If we index down to such a type, it IS signed, but any packed array of
such a type is not.  So we don't need to descend into usertypes or somehow mark
them as unsigned.  We just have to know that a usertype with one or more packed
dimensions counts as unsigned.)</p>"
  :returns (new-x vl-datatype-p)
  (vl-datatype-case x
    :vl-coretype (mbe :logic (change-vl-coretype x :signedp nil)
                      :exec (if x.signedp (change-vl-coretype x :signedp nil) x))
    :vl-struct   (mbe :logic (change-vl-struct   x :signedp nil)
                      :exec (if x.signedp (change-vl-struct   x :signedp nil) x))
    :vl-union    (mbe :logic (change-vl-union    x :signedp nil)
                      :exec (if x.signedp (change-vl-union    x :signedp nil) x))
    :otherwise   (vl-datatype-fix x))
  ///
  (defret vl-datatype-resolved-p-of-set-unsigned
    (implies (vl-datatype-resolved-p x)
             (vl-datatype-resolved-p new-x))))

;; (define vl-datatype-indexing-dimension ((x vl-datatype-p)
;;                                         (ss vl-scopestack-p))
;;   :returns (dim (iff (vl-packeddimension-p dim) dim))
;;   (b* ((udims (vl-datatype->udims x))
;;        ((when (consp udims)) (car udims))
;;        (pdims (vl-datatype->pdims x))
;;        ((when (consp pdims)) (car pdims))




(define vl-datatype-remove-dim ((x vl-datatype-p))
  :short "Get the type of a variable of type @('x') after an indexing
operation is applied to it."
  :long "
<p>The caveat flag returned identifies a case where implementations disagree on
the signedness of the resulting type.  This caveat occurs when we have packed
dimensions on a usertype that is declared as signed.  In this case, if we index
into an object down to the usertype, NCV treats the resulting object as signed,
but VCS treats it as unsigned.  The SV spec seems to say NCV's interpretation
is correct: from Sec. 7.4.1, Packed Arrays:</p>

<blockquote> If a packed array is declared as signed, then the array viewed as
a single vector shall be signed. The individual elements of the array are
unsigned unless they are of a named type declared as signed. A partselect of a
packed array shall be unsigned.</blockquote>

<p>An example:</p>

@({
  typedef logic signed [3:0] squad;

  squad [3:0] b;
  assign b = 16'hffff;

  logic [7:0] btest;
  assign btest = b[1];
 })

<p>In NCVerilog, btest has the value @('ff'), indicating that @('b[1]') is
considered signed; in VCS, btest has the value @('0f'), indicating that
@('b[1]') is considered unsigned.</p>"
  :prepwork
  ((local (in-theory (disable not equal-of-cons-rewrite
                              equal-of-vl-usertype
                              acl2::len-when-atom
                              acl2::true-listp-of-nthcdr
                              acl2::true-listp-when-string-listp-rewrite
                              acl2::true-listp-when-symbol-listp-rewrite
                              acl2::nfix-when-not-natp
                              acl2::zp-open
                              acl2::consp-under-iff-when-true-listp
                              acl2::list-fix-under-iff
                              acl2::append-when-not-consp
                              acl2::list-fix-when-len-zero
                              acl2::take-of-len-free
                              double-containment))))


  :guard (vl-datatype-resolved-p x)
  :returns (mv (err (iff (vl-msg-p err) err)  "Error message on failure")
               (caveat-flag "Indicates caveat about possible signedness ambiguities")
               (new-x (implies (not err) (vl-datatype-p new-x))
                      "Datatype after indexing")
               (dim   (implies (not err) (vl-dimension-p dim))
                      "Dimension removed from the datatype"))
  (b* ((x (vl-maybe-usertype-resolve x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        ;; Still have unpacked dimensions, so just strip off one unpacked dimension.
        (mv nil nil
            (vl-datatype-update-udims (cdr udims) x)
            (car udims)))
       (pdims (vl-datatype->pdims x))
       ((when (consp pdims))
        (b* ((x (vl-datatype-set-unsigned x))
             ((when (or (vl-datatype-case x :vl-usertype)
                        (consp (cdr pdims))))
              ;; (unless (and (eql n np)
              ;;              (not (vl-datatype-case x :vl-usertype))))
              (mv nil nil
                  (vl-datatype-update-dims
                   (cdr pdims)
                   nil ;; no udims
                   x)
                  (car pdims)))
             (new-x (vl-datatype-update-dims nil nil x))
             ((mv & arithclass) (vl-datatype-arithclass new-x))
             (caveat-flag (vl-arithclass-equiv arithclass :vl-signed-int-class)))
          (mv nil caveat-flag new-x (car pdims))))

       ((unless (vl-datatype-packedp x))
        (mv (vmsg "Index applied to non-packed, non-array type ~a0" x)
            nil nil nil))
       ((mv err size) (vl-datatype-size x))
       ((when err)
        (mv err nil nil nil))
       ((unless (posp size))
        (mv (vmsg "Index applied to ~s0 packed type: ~a1"
                  (if size "unsizeable" "zero-sized") x)
            nil nil nil))
       ((when (and (vl-datatype-case x :vl-coretype)
                   (eql size 1)))
        (mv (vmsg "Index applied to bit type ~a0" x) nil nil nil))
       (dim (vl-range->dimension (make-vl-range :msb (vl-make-index (1- size))
                                                :lsb (vl-make-index 0)))))
    (mv nil nil
        *vl-plain-old-logic-type* dim))
  ///
  (defret vl-datatype-resolved-p-of-remove-dim
    (implies (and (not err)
                  (vl-datatype-resolved-p x))
             (vl-datatype-resolved-p new-x)))

  (defret no-error-when-pdims
    (implies (consp (vl-datatype->pdims x))
             (not err))
    :hints(("Goal" :in-theory (enable vl-maybe-usertype-resolve))))

  (defret no-error-when-udims
    (implies (consp (vl-datatype->udims x))
             (not err))
    :hints(("Goal" :in-theory (enable vl-maybe-usertype-resolve)))))


(define vl-selstep-usertypes-ok ((x vl-selstep-p))
  (b* (((vl-selstep x)))
    (vl-datatype-resolved-p x.type)))

(define vl-seltrace-usertypes-ok ((x vl-seltrace-p))
  (if (atom x)
      t
    (and (vl-selstep-usertypes-ok (car x))
         (vl-seltrace-usertypes-ok (cdr x))))
  ///
  (defthm vl-seltrace-usertypes-ok-of-append
    (implies (and (vl-seltrace-usertypes-ok x)
                  (vl-seltrace-usertypes-ok y))
             (vl-seltrace-usertypes-ok (append x y))))
  (defthm vl-seltrace-usertypes-ok-of-rev
    (implies (vl-seltrace-usertypes-ok x)
             (vl-seltrace-usertypes-ok (rev x))))
  (defthm vl-datatype-resolved-p-of-first-seltrace
    (implies (and (vl-seltrace-usertypes-ok x)
                  (consp x))
             (vl-datatype-resolved-p
              (vl-selstep->type (car x))))
    :hints(("Goal" :in-theory (enable vl-selstep-usertypes-ok)))))


(define vl-follow-array-indices ((x vl-exprlist-p)
                                 (type vl-datatype-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (trace vl-seltrace-p))
  :guard (vl-datatype-resolved-p type)
  (b* (((when (atom x)) (mv nil nil))
       ((mv err caveat newtype &)
        (vl-datatype-remove-dim type))
       ((when err) (mv err nil))
       ((mv err rest) (vl-follow-array-indices (cdr x) newtype))
       ((when err) (mv err nil)))
    (mv nil (cons (make-vl-selstep
                   :select (make-vl-select-index :val (car x))
                   :type   newtype
                   :caveat caveat)
                  rest)))
  ///
  (defret vl-seltrace-usertypes-ok-of-follow-array-indices
    (implies (vl-datatype-resolved-p type)
             (vl-seltrace-usertypes-ok trace))
    :hints(("Goal" :in-theory (enable vl-seltrace-usertypes-ok
                                      vl-selstep-usertypes-ok))))

  (defret true-listp-of-vl-follow-array-indices-trace
    (true-listp trace)
    :rule-classes :type-prescription)

  (defret vl-seltrace->indices-of-vl-follow-array-indices
    (implies (not err)
             (equal (vl-seltrace->indices trace)
                    (vl-exprlist-fix x)))
    :hints(("Goal" :in-theory (enable vl-seltrace->indices))))

  (defret consp-of-vl-follow-array-indices
    (implies (not err)
             (equal (consp trace)
                    (consp x))))

  (defret len-of-vl-follow-array-indices
    (implies (not err)
             (equal (len trace)
                    (len x)))))

(define vl-hidexpr-index-count ((x vl-hidexpr-p))
  :returns (nunres natp :rule-classes :type-prescription)
  :measure (vl-hidexpr-count x)
  (vl-hidexpr-case x
    :end 0
    :dot (+ (len (vl-hidindex->indices x.first))
            (vl-hidexpr-index-count x.rest))))

(define vl-scopeexpr-index-count ((x vl-scopeexpr-p))
  :returns (nunres natp :rule-classes :type-prescription)
  :measure (vl-scopeexpr-count x)
  (vl-scopeexpr-case x
    :end (vl-hidexpr-index-count x.hid)
    :colon (vl-scopeexpr-index-count x.rest)))



(define vl-follow-data-selects ((x vl-hidexpr-p)
                                (type vl-datatype-p)
                                (trace vl-seltrace-p "Accumulator"))

  :short "Given a HID expression denoting a variable of the input type, create
          a trace showing the type of each field select/indexing operation."
  :long "<p>Implementation notes: This function only </p>"

  :returns (mv (err (iff (vl-msg-p err) err))
               (seltrace vl-seltrace-p))
  :measure (vl-hidexpr-count x)
  :guard (vl-datatype-resolved-p type)
  :verify-guards nil

  ;; Resolve the type and dims.
  (b* ((type (vl-datatype-fix type))

       ;; (name1 (vl-hidexpr-case x
       ;;          :end x.name
       ;;          :dot (vl-hidindex->name x.first)))
       ;; (frame (make-vl-selstep
       ;;         :select (make-vl-select-field :name name1)
       ;;         :type type
       ;;         :ss ss))
       ;; (trace (cons frame (vl-seltrace-fix trace)))
       (trace (vl-seltrace-fix trace))

       ((when (vl-hidexpr-case x :end))
        ;; We just have an ID.  It has already been added to the trace (or else
        ;; it is just a plain variable and the outer hidtrace has its type info).
        (mv nil trace))

       ;; Cancel the indices of the first element of the HID with the unpacked
       ;; and packed dims of the type.

       ;; Note: We have at least one more dot in this HID, so if we don't have
       ;; a struct or union at the end of this, we have a problem.
       ((vl-hidexpr-dot x))

       ((mv err rev-idxtrace)
        (vl-follow-array-indices (vl-hidindex->indices x.first) type))

       ((when err) (mv err nil))


       (trace (revappend rev-idxtrace trace))

       (type
        (if (consp rev-idxtrace)
            (vl-selstep->type (car trace))
          type))

       (type (vl-maybe-usertype-resolve type))

       ;; Next we're going to dot-index into the datatype, so get its
       ;; structmembers, making sure it's a struct.
       ((mv ok members) (vl-datatype->structmembers type))
       (nextname (vl-hidexpr-case x.rest
                   :end x.rest.name
                   :dot (vl-hidindex->name x.rest.first)))

       ;; Look up the member corresponding to the next name in the hid.
       ((unless (and ok
                     (atom (vl-datatype->udims type))
                     (atom (vl-datatype->pdims type))))
        (mv (vmsg "Dot-indexing (field ~s0) into a non-struct/union datatype: ~a1"
                  nextname
                  type
                  ;; BOZO what was this doing
                  ;; (vl-datatype-update-dims (append-without-guard
                  ;;                           (vl-datatype->udims type)
                  ;;                           (vl-datatype->pdims type))
                  ;;                          nil type)
                  )
            nil))
       ((when (eq nextname :vl-$root))
        (mv (vmsg "Can't use $root to index into a data structure: ~a0"
                  (vl-hidexpr-fix x))
            nil))
       (member (vl-find-structmember nextname members))
       ((unless member)
        (mv (vmsg "Dot-indexing failed: struct/union member ~
                                   ~s0 not found in type ~a1"
                  nextname (vl-datatype-fix type))
            nil))
       (membtype (vl-structmember->type member))
       (next-frame (make-vl-selstep
                    :select (make-vl-select-field :name nextname)
                    :type membtype))
       (trace (cons next-frame trace)))
    (vl-follow-data-selects x.rest membtype trace))
  ///




  (verify-guards vl-follow-data-selects)

  (defret vl-seltrace-usertypes-ok-of-vl-follow-data-selects
    (implies (and (vl-datatype-resolved-p type)
                  (vl-seltrace-usertypes-ok trace))
             (vl-seltrace-usertypes-ok seltrace))
    :hints(("Goal" :in-theory (enable vl-seltrace-usertypes-ok
                                      vl-selstep-usertypes-ok))))

  (local (in-theory (disable acl2::car-of-append
                             acl2::consp-under-iff-when-true-listp)))

  (defret vl-seltrace-indices-of-vl-follow-data-selects
    (implies (not err)
             (equal (vl-seltrace->indices seltrace)
                    (revappend (vl-hidexpr->subexprs x)
                               (vl-seltrace->indices trace))))
    :hints(("Goal" :in-theory (enable vl-seltrace->indices
                                      vl-hidexpr->subexprs)))))




(define vl-partselect-width ((x vl-partselect-p))
  :guard (not (vl-partselect-case x :none))
  :returns (mv (err (iff (vl-msg-p err) err))
               (width (implies (not err) (posp width)) :rule-classes :type-prescription))
  (b* ((x (vl-partselect-fix x)))
    (vl-partselect-case x
      :range
      (b* (((unless (and (vl-expr-resolved-p x.msb)
                         (vl-expr-resolved-p x.lsb)))
            (mv (vmsg "Unresolved partselect: ~a0"
                      x)
                nil))
           (msb (vl-resolved->val x.msb))
           (lsb (vl-resolved->val x.lsb)))
        ;; BOZO We might want to check here whether the msb/lsb are
        ;; correctly ascending/descending.  Not the core mission, though.
        (mv nil (+ 1 (abs (- msb lsb)))))
      :plusminus
      (b* (((unless (vl-expr-resolved-p x.width))
            (mv (vmsg "Unresolved partselect width: ~a0"
                      x)
                nil))
           (width (vl-resolved->val x.width))
           ((when (<= width 0))
            (mv (vmsg "Non-positive-width partselect not allowed: ~a0"
                      x)
                nil)))
        (mv nil width))
      :otherwise (mv (vmsg "Impossible") (impossible)))))


(defprod vl-operandinfo
  ((orig-expr  vl-expr-p         "The original index expression, for error messages etc")
   (context  vl-scopecontext-p  "The context in which the HID base was found")
   (prefixname vl-scopeexpr-p    "The scopeexpr, not including the possible data selects.")
   (declname stringp            "The name of the variable or parameter")
   (hidtrace vl-hidtrace-p      "The follow-hids trace, i.e. the trace of instances/blocks
                                 in which the base variable is located")
   (hidtype  vl-datatype-p      "The datatype of the final element of the hidtrace.")
   (seltrace vl-seltrace-p      "The select trace, i.e. the types/scopestacks of
                                 all the fields/indices we've selected into")
   (part     vl-partselect-p    "The final partselect")
   (type     vl-datatype-p      "The final datatype of the object, after
                                 partselecting."))
  :layout :tree)

(define vl-operandinfo-usertypes-ok ((x vl-operandinfo-p))
  (b* (((vl-operandinfo x)))
    (and (vl-datatype-resolved-p x.type)
         (vl-seltrace-usertypes-ok x.seltrace)
         (vl-datatype-resolved-p x.hidtype)
         (consp x.hidtrace)))
  ///
  (defthm vl-operandinfo-usertypes-ok-implies
    (implies (vl-operandinfo-usertypes-ok x)
             (b* (((vl-operandinfo x)))
               (and (vl-datatype-resolved-p x.type)
                    (vl-seltrace-usertypes-ok x.seltrace)
                    (vl-datatype-resolved-p x.hidtype)
                    (consp x.hidtrace))))))

(define vl-operandinfo-index-count ((x vl-operandinfo-p))
  :returns (count natp :rule-classes :type-prescription)
  ;; Gives the number of indices
  (b* (((vl-operandinfo x)))
    (+ (vl-seltrace-index-count x.seltrace)
       (vl-partselect-case x.part
         :none 0
         :otherwise 2))))

(define vl-operandinfo->indices ((x vl-operandinfo-p))
  :returns (indices vl-exprlist-p)
  (b* (((vl-operandinfo x)))
    (append (vl-partselect-case x.part
              :none nil
              :range (list x.part.msb x.part.lsb)
              :plusminus (list x.part.base x.part.width))
            (vl-seltrace->indices x.seltrace)))
  ///
  (defret len-of-vl-operandinfo->indices
    (equal (len indices) (vl-operandinfo-index-count x))
    :hints(("Goal" :in-theory (enable vl-operandinfo-index-count)))))





(define vl-datatype-resolve-selects ((type vl-datatype-p)
                                     (tail vl-hidexpr-p)
                                     (indices vl-exprlist-p)
                                     (part vl-partselect-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (seltrace (implies (not err) (vl-seltrace-p seltrace)))
               (finaltype (implies (not err) (vl-datatype-p finaltype))))
  :guard (vl-datatype-resolved-p type)
  (b* (((mv err seltrace) (vl-follow-data-selects tail type nil))
       ((when err) (mv err nil nil))
       (type (vl-datatype-fix type))
       (seltype (if (consp seltrace)
                    (b* (((vl-selstep selstep) (car seltrace)))
                      selstep.type)
                  type))
       ((mv err rev-idxtrace)
        (vl-follow-array-indices indices seltype))
       ((when err) (mv err nil nil))

       (seltrace (revappend rev-idxtrace seltrace))
       (seltype (if (consp seltrace)
                    (b* (((vl-selstep selstep) (car seltrace)))
                      selstep.type)
                  type))

       ((when (vl-partselect-case part :none))
        (mv nil seltrace seltype))

       ((mv err ?caveat single-type &)
        (vl-datatype-remove-dim seltype))
       ((when err) (mv err nil nil))

       ((mv err width) (vl-partselect-width part))
       ((when err) (mv err nil nil))
       (new-dim (vl-range->dimension
                 (make-vl-range :msb (vl-make-index (1- width))
                                :lsb (vl-make-index 0))))

       (packedp (vl-datatype-packedp seltype))
       (psel-type (if packedp
                      (vl-datatype-update-pdims
                       (cons new-dim (vl-datatype->pdims single-type))
                       single-type)
                    (vl-datatype-update-udims
                     (cons new-dim
                           (vl-datatype->udims single-type))
                     single-type))))
    (mv nil seltrace psel-type))
  ///
  (defret vl-seltrace-usertypes-ok-of-vl-datatype-resolve-selects
    (implies (and (not err)
                  (vl-datatype-resolved-p type))
             (vl-seltrace-usertypes-ok seltrace)))

  (defret vl-datatype-resolved-p-of-vl-datatype-resolve-selects
    (implies (and (not err)
                  (vl-datatype-resolved-p type))
             (vl-datatype-resolved-p finaltype)))

  (defret vl-seltrace-count-of-vl-datatype-resolve-selects
    (implies (not err)
             (< (vl-exprlist-count
                 (vl-seltrace->indices seltrace))
                (+ (vl-exprlist-count indices)
                   (vl-hidexpr-count tail))))
    :rule-classes :linear))






#||

(trace$ #!vl (vl-index-expr-typetrace
              :entry (list 'vl-index-expr-typetrace
                           (with-local-ps (vl-pp-expr x))
                           (vl-scopestack->hashkey ss))
              :exit (b* (((list err ?opinfo) values))
                      (list 'vl-index-expr-typetrace
                          (and err (with-local-ps (vl-cw "~@0" err)))))))

||#


(define vl-index-expr-typetrace
  ((x vl-expr-p
      "An index expression, i.e. a possibly-package-scoped, possibly-hierarchical
       identifier with 0 or more array selects and a possible partselect.")
   (ss vl-scopestack-p
       "Scopestack where @('x') is referenced.")
   (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (err (iff (vl-msg-p err) err)
                    "Success indicator, we fail if we can't follow the HID or
                         this isn't an appropriate expression.")
               (opinfo (implies (not err) (vl-operandinfo-p opinfo))))
  (b* (((vl-index x) (vl-expr-fix x))
       (ss (vl-scopestack-fix ss))
       ((mv err hidtrace context tail) (vl-follow-scopeexpr x.scope ss))
       ((when err) (mv err nil))
       ((vl-hidstep hidstep) (car hidtrace))

       ;; Suppose x is foo.bar.baz.fum[0][1][3:2].
       ;; Suppose foo.bar is the actual vardecl, and .baz.fum are selects into it.
       ;; We want to see if foo.bar has a cached resolved type.

       (decl-scopes (vl-elabscopes-traverse (rev hidstep.elabpath) scopes))
       ;; This is the scope in which bar is declared.
       (name1 (vl-hidexpr-name1 tail)) ;; bar
       ((when (eq name1 :vl-$root))
        (mv (vmsg "$root is not supported") nil))

       (info (vl-elabscopes-item-info name1 decl-scopes))

       ((mv err type)
        (b* ((item (or info hidstep.item)))
          (case (tag item)
            (:vl-vardecl (b* ((type1 (vl-vardecl->type item)))
                           (vl-datatype-usertype-resolve type1 hidstep.ss :scopes decl-scopes)))
            (:vl-paramdecl (b* (((vl-paramdecl decl) item))
                             (vl-paramtype-case decl.type
                               :vl-explicitvalueparam
                               (if (vl-datatype-resolved-p decl.type.type)
                                   (mv nil decl.type.type)
                                 (mv (vmsg "Reference to parameter with unresolved type: ~a0"
                                           x)
                                     nil))
                               :otherwise (mv (vmsg "Bad parameter reference: ~a0" x)
                                              nil))))
            ((:vl-modinst :vl-interfaceport)
             (b* (((unless (vl-hidexpr-case tail :end))
                   (mv (vmsg "Programming error resolving ~a0: Thought that if
                              vl-follow-scopexpr ended up at a modinst or interfaceport,
                              then we should have no indexing operations on the
                              final element.  But we ended up with ~a1."
                             x (make-vl-index :scope (make-vl-scopeexpr-end :hid tail)))
                       nil))
                  ((mv err member)
                   (if (eq (tag item) :vl-modinst)
                       (vl-modinst-interface-mockmember item hidstep.ss :reclimit 100)
                     (vl-interfaceport-mockmember item hidstep.ss :reclimit 100)))
                  ((when err)
                   (mv (vmsg "Error creating mock type for ~a0: ~@1" item err)
                       nil))
                  (type (vl-structmember->type member))
                  ((unless (vl-datatype-resolved-p type))
                   (mv (vmsg "Mocktype for interface instance ~a0 was unresolved: ~a1"
                             item type)
                       nil)))
               (mv nil type)))

            (otherwise
             (mv (vmsg "~a0: instead of a vardecl, found ~a1" x item) nil)))))

       ((when err) (mv err nil))



       ;; Compute foo.bar.
       (prefix-name (vl-scopeexpr-replace-hid
                     x.scope
                     (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))

       ((mv err seltrace final-type)
        (vl-datatype-resolve-selects type tail x.indices x.part))

       ((when err) (mv err nil)))

    (mv nil (make-vl-operandinfo
             :orig-expr x
             :context context
             :prefixname prefix-name
             :declname name1
             :hidtrace hidtrace
             :hidtype type
             :seltrace seltrace
             :part x.part
             :type final-type)))



    ;;    ((mv err seltrace) (vl-follow-data-selects tail type nil))
    ;;    ((when err) (mv err nil))
    ;;    (seltype (if (consp seltrace)
    ;;                 (b* (((vl-selstep selstep) (car seltrace)))
    ;;                   selstep.type)
    ;;               type))
    ;;    ((mv err rev-idxtrace)
    ;;     (vl-follow-array-indices x.indices seltype))
    ;;    ((when err) (mv err nil))

    ;;    (seltrace (revappend rev-idxtrace seltrace))
    ;;    (seltype (if (consp seltrace)
    ;;                 (b* (((vl-selstep selstep) (car seltrace)))
    ;;                   selstep.type)
    ;;               type))

    ;;    (prefix-name (vl-scopeexpr-replace-hid
    ;;                  x.scope
    ;;                  (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))




    ;;    ((when (vl-partselect-case x.part :none))
    ;;     (mv nil (make-vl-operandinfo
    ;;              :context context
    ;;              :prefixname prefix-name
    ;;              :hidtrace hidtrace
    ;;              :hidtype type
    ;;              :seltrace seltrace
    ;;              :part x.part
    ;;              :type seltype)))

    ;;    ((mv err ?caveat single-type &)
    ;;     (vl-datatype-remove-dim seltype))
    ;;    ((when err) (mv err nil))

    ;;    ((mv err width) (vl-partselect-width x.part))
    ;;    ((when err) (mv err nil))
    ;;    (new-dim (vl-range->packeddimension
    ;;              (make-vl-range :msb (vl-make-index (1- width))
    ;;                             :lsb (vl-make-index 0))))

    ;;    (packedp (vl-datatype-packedp seltype))
    ;;    (psel-type (if packedp
    ;;                   (vl-datatype-update-pdims
    ;;                    (cons new-dim (vl-datatype->pdims single-type))
    ;;                    single-type)
    ;;                 (vl-datatype-update-udims
    ;;                  (cons new-dim (vl-datatype->udims single-type))
    ;;                  single-type))))
    ;; (mv nil (make-vl-operandinfo
    ;;          :context context
    ;;          :prefixname prefix-name
    ;;          :hidtrace hidtrace
    ;;          :hidtype type
    ;;          :seltrace seltrace
    ;;          :part x.part
    ;;          :type psel-type)))
  ///
  (defret vl-seltrace-usertypes-ok-of-vl-index-expr-typetrace
    (implies (not err)
             (vl-seltrace-usertypes-ok (vl-operandinfo->seltrace opinfo))))

  (defret consp-hidtrace-of-vl-index-expr-typetrace
    (implies (not err)
             (consp (vl-operandinfo->hidtrace opinfo))))

  ;; (defret vl-hidtrace-top-is-vardecl-or-paramdecl-of-vl-index-expr-typetrace
  ;;   (implies (and (not err)
  ;;                 (not (equal (tag (vl-hidstep->item (car (vl-operandinfo->hidtrace opinfo))))
  ;;                             :vl-paramdecl)))
  ;;            (equal (tag (vl-hidstep->item (car (vl-operandinfo->hidtrace opinfo))))
  ;;                   :vl-vardecl)))

  (defret vl-datatype-usertypes-ok-of-vl-index-expr-typetrace-type
    (implies (not err)
             (vl-datatype-resolved-p (vl-operandinfo->type opinfo))))

  (defret vl-operandinfo-usertypes-ok-of-vl-index-expr-typetrace
    (implies (not err)
             (vl-operandinfo-usertypes-ok opinfo))
    :hints(("Goal" :in-theory (enable vl-operandinfo-usertypes-ok))))

  (defret follow-scopeexpr-when-vl-index-expr-type
    (implies (not err)
             (b* (((vl-index x)))
               (not (mv-nth 0 (vl-follow-scopeexpr x.scope ss))))))


  (defret index-count-of-vl-index-expr-typetrace
    (implies (and (not err)
                  (equal (vl-expr-kind x) :vl-index))
             (< (vl-exprlist-count (vl-operandinfo->indices opinfo))
                (vl-expr-count x)))
    :hints(("Goal" :in-theory (enable vl-operandinfo->indices
                                      vl-exprlist-count
                                      vl-partselect-count
                                      vl-plusminus-count
                                      vl-range-count)
            :expand ((vl-expr-count x))))
    :rule-classes :linear))





(define vl-hidindex-resolved-p ((x vl-hidindex-p))
  :returns (bool)
  :short "Determines if every index in a @(see vl-hidindex-p) is resolved."
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  (vl-exprlist-resolved-p (vl-hidindex->indices x))
  ///
  ;; (defthm vl-hidindex-resolved-p-when-atom
  ;;   (implies (vl-atom-p x)
  ;;            (vl-hidindex-resolved-p x)))

  (deffixequiv vl-hidindex-resolved-p))


(define vl-hidexpr-resolved-p ((x vl-hidexpr-p))
  ;; :prepwork ((local (in-theory (enable vl-nonatom->op-when-hidindex-resolved-p))))
  :returns (bool)
  :short "Determines if every index throughout a @(see vl-hidexpr-p) is resolved."
  :guard-debug t
  :measure (vl-hidexpr-count x)
  (vl-hidexpr-case x
    :end t
    :dot (and (vl-hidindex-resolved-p x.first)
              (vl-hidexpr-resolved-p x.rest)))
  ///
  (defthm vl-hidexpr-resolved-p-when-endp
    (implies (vl-hidexpr-case x :end)
             (vl-hidexpr-resolved-p x)))

  (defthm vl-hidexpr-resolved-p-of-vl-hidexpr-dot
    ;; Really I should be using something like a of-cons rule here, but without
    ;; a constructor...
    (equal (vl-hidexpr-resolved-p (make-vl-hidexpr-dot :first first :rest rest))
           (and (vl-hidindex-resolved-p first)
                (vl-hidexpr-resolved-p rest)))
    :hints (("goal" :Expand
             ((vl-hidexpr-resolved-p (make-vl-hidexpr-dot :first first :rest rest))))))

  (defthm vl-hidexpr-resolved-p-implies-dot
    (implies (and (vl-hidexpr-resolved-p x)
                  (vl-hidexpr-case x :dot))
             (and (vl-hidindex-resolved-p (vl-hidexpr-dot->first x))
                  (vl-hidexpr-resolved-p (vl-hidexpr-dot->rest x))))))

(define vl-scopeexpr-resolved-p ((x vl-scopeexpr-p))
  :measure (vl-scopeexpr-count x)
  (vl-scopeexpr-case x
    :end (vl-hidexpr-resolved-p x.hid)
    :colon (vl-scopeexpr-resolved-p x.rest)))



(define vl-flatten-hidindex-aux ((indices vl-exprlist-p)
                                 acc)
  :guard (vl-exprlist-resolved-p indices)
  :parents (vl-flatten-hidindex)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom indices))
        acc)
       (acc (cons #\[ acc))
       (idx (vl-resolved->val (car indices)))
       (acc (if (< idx 0) (cons #\- acc) acc))
       (acc (revappend (str::natchars (abs idx)) acc))
       (acc (cons #\] acc)))
    (vl-flatten-hidindex-aux (cdr indices) acc)))

(define vl-flatten-hidindex ((x vl-hidindex-p))
  :guard (vl-hidindex-resolved-p x)
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a @(see vl-hidindex-p) into a string like @('\"bar[3][4][5]\"')."
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  :guard-hints(("Goal" :in-theory (enable vl-hidindex-resolved-p)))
  (b* ((name    (vl-hidindex->name x))
       (name    (if (eq name :vl-$root)
                    "$root"
                  name))
       (indices (vl-hidindex->indices x))
       ((when (atom indices))
        name)
       (acc nil)
       (acc (str::revappend-chars name acc))
       (acc (vl-flatten-hidindex-aux indices acc)))
    (str::rchars-to-string acc)))

(define vl-flatten-hidexpr ((x vl-hidexpr-p))
  :guard (vl-hidexpr-resolved-p x)
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a hierarchical identifier expression into a string like
@('foo.bar[3][4][5].baz')."
  :measure (vl-hidexpr-count x)
  (vl-hidexpr-case x
    :end x.name
    :dot
    (cat (vl-flatten-hidindex x.first)
         "."
         (vl-flatten-hidexpr x.rest))))
