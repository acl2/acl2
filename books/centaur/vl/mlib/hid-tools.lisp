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
(include-book "expr-tools")
(include-book "coretypes")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (in-theory (enable tag-reasoning)))
(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))

(local (defthm equal-of-cons-rewrite
         (equal (equal x (cons a b))
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))


(defthm vl-genelement-kind-by-tag
  (implies (and (vl-genelement-p x)
                (equal (tag x) foo)
                (syntaxp (quotep foo)))
           (equal (vl-genelement-kind x) foo))
  :hints(("Goal" :in-theory (enable tag vl-genelement-kind vl-genelement-p))))



(defxdoc following-hids
  :parents (hid-tools)
  :short "Functions for following hierarchical identifiers."

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

<dd>Tools that want to descend into structures will need to do so using the
appropriate functions; for instance @(see BOZO) and @(see BOZO).</dd>


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

<dd>In some applications, e.g., for @(see lint)-like tools, it may be best to
allow these potentially invalid indices.  After all, we \"know\" that this
reference is either invalid or is a reference to @('baz') within @('mymod').
In that case, we may well wish to assume that the index will be valid and just
go on and find @('baz').</dd>

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

(local (xdoc::set-default-parents following-hids))


(defprod vl-hidstep
  :short "A single step along the way of a hierarchical identifier."
  :long "<p>Some routines for @(see following-hids) produce traces of the items
they encounter along the way.  A <b>hidstep</b> structure represents a single
step along a HID.</p>"
  :tag :vl-hidstep
  :layout :tree
  ((name stringp "Name from the hid")
   (index vl-maybe-expr-p "Instance array/genarray index, if present")
   (item vl-scopeitem-p  "The item encountered along the path of the HID.")
   (ss   vl-scopestack-p "The scope where this item was found.")))

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
  ((name    stringp              "Name being the array, for better errors.")
   (index   vl-expr-p            "An index into an array.")
   (dim     vl-packeddimension-p "Bounds from the corresponding declaration.")
   &key
   (strictp booleanp "Require indices to be resolved?"))
  :returns (err (iff (vl-msg-p err) err))
  :long "<p>In strict mode, we require that the @('index') and the array
dimensions all be resolved and that the index be in range.</p>

<p>In non-strict mode, we tolerate unresolved indices and declaration bounds.
Note that we still do bounds checking if the indices and array bounds happen to
be resolved.</p>"

  (b* ((dim (vl-packeddimension-fix dim))
       ((when (vl-packeddimension-case dim :unsized))
        ;; Bounds checking doesn't make sense in this case, so we'll just
        ;; regard this as fine.
        nil)
       (dim (vl-packeddimension->range dim))
       ((unless (vl-expr-resolved-p index))
        (if strictp
            (vmsg "unresolved array index")
          nil))
       ((unless (vl-range-resolved-p dim))
        (if strictp
            (vmsg "unresolved bounds on declaration of ~s0" (string-fix name))
          nil))
       ((vl-range dim))
       (idxval (vl-resolved->val index))
       (msbval (vl-resolved->val dim.msb))
       (lsbval (vl-resolved->val dim.lsb))
       (minval (min msbval lsbval))
       (maxval (max msbval lsbval))
       ((unless (and (<= minval idxval)
                     (<= idxval maxval)))
        (vmsg "array index ~x0 out of bounds (~x1 to ~x2)"
              idxval minval maxval)))
    nil))

(define vl-follow-hidexpr-dimscheck-aux
  :parents (vl-follow-hidexpr-dimscheck)
  :short "Main loop to check each index/dimension pair."
  :prepwork ((local (defthm vl-exprlist-fix-of-atom
                      (implies (not (consp x))
                               (equal (vl-exprlist-fix x) nil)))))
  ((name    stringp)
   (indices vl-exprlist-p)
   (dims    vl-packeddimensionlist-p)
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
   (dims    vl-packeddimensionlist-p
            "Corresponding dimensions from the declaration, i.e., if @('foo')
             is declared as a @('logic [7:0][15:0][3:0]'), then this would
             be the list of @('([7:0] [15:0] [3:0])').")
   &key
   (strictp booleanp
            "Should we require every index to be resolved?"))
  :returns
  (err (iff (vl-msg-p err) err))
  (b* ((name (string-fix name))
       ((when (atom dims))
        (if (atom indices)
            nil
          (vmsg "indexing into non-array ~s0" name)))
       ((when (atom indices))
        (vmsg "no indices given for array ~s0" name))
       ((when (same-lengthp indices dims))
        (vl-follow-hidexpr-dimscheck-aux name indices dims
                                         :strictp strictp))
       (found (len indices))
       (need  (len dims))
       ((when (< found need))
        (vmsg "too many indices for array ~s0" name)))
    (vmsg "not enough indices for array ~s0" name)))

(define vl-genarrayblocklist-find-block
  :short "Find the block from a generate array corresponding to some index."
  ((idx integerp)
   (x   vl-genarrayblocklist-p))
  :returns (blk (iff (vl-genarrayblock-p blk) blk))
  (cond ((atom x)
         nil)
        ((eql (vl-genarrayblock->index (car x)) (lifix idx))
         (vl-genarrayblock-fix (car x)))
        (t
         (vl-genarrayblocklist-find-block idx (cdr x)))))

(local (defthm stringp-when-hidname-and-not-$root
         (implies (vl-hidname-p x)
                  (equal (equal x :vl-$root)
                         (not (stringp x))))
         :hints(("Goal" :in-theory (enable vl-hidname-p)))))

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
                                          tag-reasoning)))

               (local (defthm vl-maybe-expr-p-of-car-exprlist
                        (implies (vl-exprlist-p x)
                                 (vl-maybe-expr-p (car x))))))
    :hooks ((:fix
             :hints(("Goal"
                     :expand ((:free (trace ss strictp) (vl-follow-hidexpr-aux x trace ss :strictp strictp))
                              (:free (trace ss strictp) (vl-follow-hidexpr-aux (vl-expr-fix x) trace ss :strictp strictp)))))))
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

         ((mv item item-ss) (vl-scopestack-find-item/ss name1 ss))
         ((unless item)
          (mv (vl-follow-hidexpr-error (vmsg "item not found") ss)
              trace x))

         ((when (or (eq (tag item) :vl-vardecl)
                    (eq (tag item) :vl-paramdecl)))
          ;; Found the declaration we want.  We aren't going to go any further:
          ;; there may be additional HID indexing stuff left, but if so it's just
          ;; array or structure indexing for the tail.
          
          (b* ((trace (cons (make-vl-hidstep :name name1
                                             :item item
                                             ;; No indices -- they belong to
                                             ;; the variable
                                             :ss item-ss)
                            trace)))
            (mv nil trace x)))

         ;; From here on out, if the trace is good and the index exists, the
         ;; trace includes that index.
         (trace (cons (make-vl-hidstep :name name1
                                       :item item
                                       :index (car indices)
                                       :ss item-ss)
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

         ((when (eq (tag item) :vl-modinst))
          (b* (((vl-modinst item))
               (dims    (and item.range (list (vl-range->packeddimension item.range))))
               ;; Start by checking for sensible array indexing.
               (err (vl-follow-hidexpr-dimscheck name1 indices dims :strictp strictp))
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
               (next-ss
                ;; The MOD-SS is just the scopestack for where the module is
                ;; defined, which in practice will be the top level scope.
                ;; The next part of the HID needs to be looked up from within
                ;; MOD, so we need to actually go into the module.
                (vl-scopestack-push mod mod-ss)))
            (vl-follow-hidexpr-aux rest trace next-ss :strictp strictp)))

         ((when (eq (tag item) :vl-interfaceport))
          (b* (((vl-interfaceport item))
               ((when (or (consp indices)
                          (consp item.udims)))
                ;; BOZO.  What kind of index checking do we want to do?  Probably
                ;; it is ok to index only partly into an interface port, because
                ;; if it's okay to have an array of interfaces coming in, then
                ;; it's probably ok to stick an array of interfaces into a
                ;; submodule, etc.  So maybe we need to just check that we have
                ;; no more indices than are allowed, and then check ranges on any
                ;; indices that we do happen to have...
                (mv (vl-follow-hidexpr-error "BOZO implement support for interface arrays." item-ss)
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
               (next-ss (vl-scopestack-push iface iface-ss)))
            (vl-follow-hidexpr-aux rest trace next-ss
                                   :strictp strictp)))

         ((when (eq (tag item) :vl-genblock))
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
               (genblob (vl-sort-genelements (vl-genblock->elems item)
                                             :scopetype :vl-genblock
                                             :name (vl-genblock->name item)))
               (next-ss (vl-scopestack-push genblob item-ss)))
            (vl-follow-hidexpr-aux rest trace next-ss
                                   :strictp strictp)))

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
               (block    (vl-genarrayblocklist-find-block blocknum
                                                          (vl-genarray->blocks item)))
               ((unless block)
                ;; Something like foo.bar.mygenarray[8].baz when the array only
                ;; goes from 3:7 or whatever.
                (mv (vl-follow-hidexpr-error (vmsg "invalid index into generate array: ~x0" blocknum)
                                             item-ss)
                    trace x))
               (genblob (vl-sort-genelements (vl-genarrayblock->elems block)
                                             :scopetype :vl-genarrayblock
                                             :name (vl-genarray->name item)))
               (next-ss (vl-scopestack-push genblob item-ss)))
            (vl-follow-hidexpr-aux rest trace next-ss :strictp strictp)))

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
                                                                   :strictp strictp
                                                                   :origx origx))
                    ((mv err2 trace2 tail2) (vl-follow-hidexpr-aux x trace ss
                                                                   :strictp strictp
                                                                   :origx (vl-scopeexpr-fix nil))))
                 (and (equal trace1 trace2)
                      (equal tail1 tail2)
                      (iff err1 err2))))
      :hints ((acl2::just-induct-and-expand
               (vl-follow-hidexpr-aux x trace ss
                                      :strictp strictp
                                      :origx origx)
               :expand-others
               ((:free (ctx strictp origx)
                 (vl-follow-hidexpr-aux x trace ss
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
              :induct (vl-follow-hidexpr-aux x trace ss :strictp strictp :origx origx))))))

(deftagsum vl-scopecontext
  (:local ((levels natp :rule-classes :type-prescription
                   "How many levels up from the current scope was the item found")))
  (:root  ())
  (:package ((pkg vl-package-p)))
  (:module  ((mod vl-module-p))))

(deftagsum vl-select
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
   ))

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
         
  

(defprod vl-operandinfo
  ((orig-expr  vl-expr-p         "The original index expression, for error messages etc")
   (context  vl-scopecontext-p  "The context in which the HID base was found")
   (prefixname vl-scopeexpr-p    "The scopeexpr, not including the possible data selects.")
   (hidtrace vl-hidtrace-p      "The follow-hids trace, i.e. the trace of instances/blocks
                                 in which the base variable is located")
   (hidtype  vl-datatype-p      "The datatype of the final element of the hidtrace.")
   (seltrace vl-seltrace-p      "The select trace, i.e. the types/scopestacks of
                                 all the fields/indices we've selected into")
   (part     vl-partselect-p    "The final partselect")
   (type     vl-datatype-p      "The final datatype of the object, after
                                 partselecting.")))
              

(local (defthm nesting-level-of-vl-scopestack-find-item/context
         (<= (vl-scopestack-nesting-level
              (mv-nth 1 (vl-scopestack-find-item/context name ss)))
             (vl-scopestack-nesting-level ss))
         :hints(("Goal" :in-theory (enable vl-scopestack-find-item/context
                                           vl-scopestack-nesting-level)))
         :rule-classes :linear))

(define vl-follow-hidexpr
  :short "Follow a HID to find the associated declaration."
  ((x       vl-hidexpr-p       "Hierarchical identifier to follow.")
   (ss      vl-scopestack-p "Scopestack where the HID originates.")
   &key
   ((origx vl-scopeexpr-p      "Original version of X, for better error messages.") 'origx)
   (strictp booleanp "Require all array indices and bounds to be resolved?"))
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

  :long "<p>Prerequisite: see @(see following-hids) for considerable discussion
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
              (vl-follow-hidexpr-aux x nil ss :strictp strictp))
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

       (mods     (vl-design->mods design))
       (toplevel (vl-modulelist-toplevel mods))
       ((unless (member-equal name1 toplevel))
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace nil x))

       ;; Successfully found a top-level module with the first index name.
       ((when (consp indices))
        ;; Something like topmod[3].foo.bar, doesn't make any sense.
        (mv (vl-follow-hidexpr-error "array indices into top level module" ss)
            trace nil x))

       (mod     (vl-find-module name1 mods))
       (mod-ss  (vl-scopestack-init design))

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
       (next-ss (vl-scopestack-push mod mod-ss))

       ((mv err trace tail)
        (vl-follow-hidexpr-aux rest trace next-ss
                               :strictp strictp))

       (context (make-vl-scopecontext-module :mod mod)))
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
    (vl-follow-hidexpr x.hid ss :strictp strictp :origx x)

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
         ((mv err trace context tail)
          (vl-follow-hidexpr
           (vl-scopeexpr-end->hid x.rest)
           pkg-ss  :strictp strictp :origx x))
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

(defxdoc datatype-tools
  :parents (mlib)
  :short "Functions for working with datatypes.")

(local (xdoc::set-default-parents datatype-tools))



(defines vl-datatype-resolved-p
  (define vl-datatype-resolved-p ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      :vl-coretype t
      :vl-struct (vl-structmemberlist-resolved-p x.members)
      :vl-union  (vl-structmemberlist-resolved-p x.members)
      :vl-enum   (vl-datatype-resolved-p x.basetype)
      :vl-usertype (and x.res
                        (vl-datatype-resolved-p x.res))))

  (define vl-structmemberlist-resolved-p ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        t
      (and (vl-datatype-resolved-p (vl-structmember->type (car x)))
           (vl-structmemberlist-resolved-p (cdr x)))))
  ///
  (deffixequiv-mutual vl-datatype-resolved-p)

  (defthm vl-datatype-resolved-p-of-make-coretype
    (vl-datatype-resolved-p (vl-coretype name signedp pdims udims)))

  (defthm vl-datatype-resolved-p-of-make-struct
    (equal (vl-datatype-resolved-p
            (vl-struct packedp signedp members pdims udims))
           (vl-structmemberlist-resolved-p members))
    :hints (("goal" :expand ((vl-datatype-resolved-p
                              (vl-struct packedp signedp members pdims udims))))))

  (defthm vl-datatype-resolved-p-of-make-union
    (equal (vl-datatype-resolved-p
            (vl-union packedp signedp taggedp members pdims udims))
           (vl-structmemberlist-resolved-p members))
    :hints (("Goal" :expand ((vl-datatype-resolved-p
                              (vl-union packedp signedp taggedp members pdims udims))))))
  
  (defthm vl-datatype-resolved-p-of-make-enum
    (equal (vl-datatype-resolved-p
            (vl-enum basetype items pdims udims))
           (vl-datatype-resolved-p basetype))
    :hints (("goal" :expand (vl-datatype-resolved-p
            (vl-enum basetype items pdims udims)))))

  (defthm vl-datatype-resolved-p-of-make-usertype
    (equal (vl-datatype-resolved-p
            (vl-usertype name res pdims udims))
           (and res (vl-datatype-resolved-p res)))
    :hints (("Goal" :expand (vl-datatype-resolved-p
            (vl-usertype name res pdims udims)))))

  (defthm vl-structmemberlist-resolved-p-of-struct-members
    (implies (and (vl-datatype-case x :vl-struct)
                  (vl-datatype-resolved-p x))
             (vl-structmemberlist-resolved-p (vl-struct->members x))))

  (defthm vl-structmemberlist-resolved-p-of-union-members
    (implies (and (vl-datatype-case x :vl-union)
                  (vl-datatype-resolved-p x))
             (vl-structmemberlist-resolved-p (vl-union->members x))))

  (defthm vl-datatype-resolved-p-of-enum-basetype
    (implies (and (vl-datatype-case x :vl-enum)
                  (vl-datatype-resolved-p x))
             (vl-datatype-resolved-p (vl-enum->basetype x))))

  (defthm vl-datatype-resolved-p-of-usertype-basetype
    (implies (and (vl-datatype-case x :vl-usertype)
                  (vl-datatype-resolved-p x))
             (and (vl-datatype-resolved-p (vl-usertype->res x))
                  (vl-usertype->res x))))

  (defthm vl-structmemberlist-resolved-p-of-cons
    (equal (vl-structmemberlist-resolved-p (cons a b))
           (and (vl-datatype-resolved-p (vl-structmember->type a))
                (vl-structmemberlist-resolved-p b))))

  (defthm vl-datatype-resolved-p-of-car-structmember-type
    (implies (vl-structmemberlist-resolved-p x)
             (vl-datatype-resolved-p (vl-structmember->type (car x)))))

  (defthm vl-structmemberlist-resolved-p-of-cdr
    (implies (vl-structmemberlist-resolved-p x)
             (vl-structmemberlist-resolved-p (cdr x))))

  (defthm vl-datatype-resolved-p-of-update-dims
    (implies (vl-datatype-resolved-p x)
             (vl-datatype-resolved-p (vl-datatype-update-dims pdims udims x)))
    :hints(("Goal" :in-theory (enable vl-datatype-update-dims)))))

(fty::defalist vl-typeoverride :key-type vl-scopeexpr :val-type vl-datatype
  :short "Alist mapping names to datatypes, used to store resolutions of parameter
          types that have been computed but not yet put in the design."
  :long "<p>The names may be of various different kinds of objects, meaning
slightly different things:</p>

<ul>
<li>A value parameter name maps to the type of the parameter value</li>
<li>A type parameter name maps to the resolved type that is that parameter's value</li>
<li>A typedef name maps to the resolved type</li>
<li>A function name maps to the resolved return type of the function.</li>
</ul>")

(defines vl-datatype-usertype-resolve
  (define vl-datatype-usertype-resolve ((x vl-datatype-p)
                                        (ss vl-scopestack-p)
                                        &key
                                        ((typeov vl-typeoverride-p) 'nil)
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
                          x.members ss :typeov typeov :rec-limit rec-limit)))
                     (mv err (change-vl-struct x :members members)))
        :vl-union  (b* (((mv err members)
                         (vl-structmemberlist-usertype-resolve
                          x.members ss :typeov typeov :rec-limit rec-limit)))
                     (mv err (change-vl-union x :members members)))
        :vl-enum   (b* (((mv err basetype)
                         (vl-datatype-usertype-resolve
                          x.basetype ss :typeov typeov :rec-limit rec-limit)))
                     (mv err (change-vl-enum x :basetype basetype)))
        :vl-usertype (b* (((when (and x.res (vl-datatype-resolved-p x.res)))
                           (mv nil x))
                          ((mv err def)
                           (vl-usertype-lookup x.name ss :typeov typeov :rec-limit rec-limit)))
                       (mv err (change-vl-usertype x :res def))))))

  (define vl-structmemberlist-usertype-resolve ((x vl-structmemberlist-p)
                                                (ss vl-scopestack-p)
                                                &key
                                                ((typeov vl-typeoverride-p) 'nil)
                                                ((rec-limit natp) '1000))
    :measure (two-nats-measure rec-limit (vl-structmemberlist-count x))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (new-x vl-structmemberlist-p))
    (b* (((when (atom x)) (mv nil nil))
         ((mv err1 type1)
          (vl-datatype-usertype-resolve
           (vl-structmember->type (car x)) ss :typeov typeov :rec-limit rec-limit))
         ((mv err2 rest)
          (vl-structmemberlist-usertype-resolve (cdr x) ss :typeov typeov :rec-limit
                                                rec-limit)))
      (mv (or err1 err2)
          (cons (change-vl-structmember (car x) :type type1) rest))))

  (define vl-usertype-lookup ((x vl-scopeexpr-p "The usertype name to look up")
                              (ss vl-scopestack-p)
                              &key
                              ((typeov vl-typeoverride-p) 'nil)
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
       (typeov (vl-typeoverride-fix typeov))
       (hid (vl-scopeexpr->hid x))
       ;; BOZO Maybe we should use a different type than scopeexpr for a usertype name
       ((unless (vl-hidexpr-case hid :end))
        (mv (vmsg "Type names cannot be specified with dotted ~
                                   paths, only package scopes: ~a1"
                  nil x)
            nil))
       (look (hons-get x typeov))
       ((when look)
        (if (vl-datatype-resolved-p (cdr look))
            (mv nil (cdr look))
          (mv (vmsg "Programming error: unresolved override type") nil)))
       ((mv err trace ?context ?tail)
        (vl-follow-scopeexpr x ss))
       ((when err)
        (mv err nil))
       ((vl-hidstep ref) (car trace))
       ((when (eq (tag ref.item) :vl-typedef))
        (b* (((vl-typedef item) ref.item)
             ((when (zp rec-limit))
              (mv (vmsg "Recursion limit ran out looking up ~
                                      usertype ~a0" x)
                  nil)))
          (vl-datatype-usertype-resolve item.type ref.ss
                                        :typeov nil ;; different scope!
                                        :rec-limit (1- rec-limit))))
       ((when (eq (tag ref.item) :vl-paramdecl))
        (b* (((vl-paramdecl item) ref.item))
          (vl-paramtype-case item.type
            :vl-typeparam 
            (if (and item.type.default
                     (vl-datatype-resolved-p item.type.default))
                (mv nil item.type.default)
              (mv (vmsg "Reference to unresolved type parameter ~a0" item)
                  nil))
            :otherwise
            (mv (vmsg "Reference to data parameter ~a0 as type" item)
                nil)))))
    (mv (vmsg "Didn't find a typedef ~a1, instead found ~a2"
              nil x ref.item)
        nil)))


  ///
  (verify-guards vl-datatype-usertype-resolve-fn)

  (defthm vl-datatype-usertype-resolve-nonnil
    (mv-nth 1 (vl-datatype-usertype-resolve
               x ss :typeov typeov :rec-limit rec-limit))
    :hints (("goal" :use ((:instance
                           (:theorem
                            (implies (not x)
                                     (not (vl-datatype-p x))))
                           (x (mv-nth 1 (vl-datatype-usertype-resolve
                                         x ss :typeov typeov :rec-limit rec-limit)))))
             :in-theory (disable vl-datatype-usertype-resolve)))
    :rule-classes
    ((:type-prescription :typed-term (mv-nth 1 (vl-datatype-usertype-resolve
                                                x ss :typeov typeov :rec-limit rec-limit)))))

  (defthm vl-usertype-lookup-nonnil
    (b* (((mv err res) (vl-usertype-lookup x ss :typeov typeov :rec-limit rec-limit)))
      (implies (not err)
               res))
    :hints (("goal" :use ((:instance return-type-of-vl-usertype-lookup-fn.type))
             :in-theory (disable return-type-of-vl-usertype-lookup-fn.type)))
    :rule-classes
    ((:type-prescription :typed-term (mv-nth 1 (vl-usertype-lookup
                                                x ss :typeov typeov :rec-limit rec-limit)))))

  (defthm-vl-datatype-usertype-resolve-flag
    (defthm vl-datatype-resolved-p-of-vl-datatype-usertype-resolve
      (b* (((mv err new-x)
            (vl-datatype-usertype-resolve x ss :typeov typeov :rec-limit rec-limit)))
        (implies (not err)
                 (vl-datatype-resolved-p new-x)))
      :hints('(:expand ((vl-datatype-resolved-p x))))
      :flag vl-datatype-usertype-resolve)
    (defthm vl-structmemberlist-resolved-p-of-vl-structmemberlist-usertype-resolve
      (b* (((mv err new-x)
            (vl-structmemberlist-usertype-resolve x ss :typeov typeov :rec-limit rec-limit)))
        (implies (not err)
                 (vl-structmemberlist-resolved-p new-x)))
      ;; :hints('(:in-theory (enable vl-structmemberlist-resolved-p)))
      :flag vl-structmemberlist-usertype-resolve)
    (defthm vl-datatype-resolved-p-of-vl-usertype-lookup
      (b* (((mv err type)
            (vl-usertype-lookup x ss :typeov typeov :rec-limit rec-limit)))
        (implies (not err)
                 (vl-datatype-resolved-p type)))
      :flag vl-usertype-lookup))

  (deffixequiv-mutual vl-datatype-usertype-resolve))



;; (define vl-usertype-resolve ((x vl-scopeexpr-p "The usertype name to look up")
;;                              (ss vl-scopestack-p)
;;                              &key ((rec-limit natp) '1000))
;;   :short "Looks up a usertype name recursively, stopping and and returning its
;;           definition when it is a non-usertype or has dimensions."

;;   :returns (mv (err (iff (vl-msg-p err) err)
;;                     "Error message if unsuccessful")
;;                (type (iff (vl-datatype-p type) (not err))
;;                      "Resolved type, if successful")
;;                (scope vl-scopestack-p
;;                       "Scopestack for the context in which the type was defined
;;                        (only sensible if successful)"))
;;   :measure (nfix rec-limit)
;;   (b* (((mv err def new-ss)
;;         (vl-usertype-lookup x ss))
;;        ((when err) (mv err def new-ss))
;;        ((unless (vl-datatype-case def :vl-usertype))
;;         (mv nil def new-ss))
;;        ((vl-usertype def))
;;        ((when (or (consp def.pdims) (consp def.udims)))
;;         (mv nil def new-ss))
;;        ((when (zp rec-limit))
;;         (mv (vmsg "Recursion limit ran out looking up usertype ~a0" def) nil new-ss)))
;;     (vl-usertype-resolve def.name new-ss :rec-limit (1- rec-limit)))
;;   ///
;;   (defret vl-usertype-resolve-result-has-dims
;;     (implies (and (not err)
;;                   (vl-datatype-case type :vl-usertype)
;;                   (not (consp (vl-datatype->udims type))))
;;              (consp (vl-datatype->pdims type)))))








;; (define vl-usertype-resolve ((x vl-datatype-p)
;;                              (ss vl-scopestack-p)
;;                              (rec-limit natp))
;;   :guard (vl-datatype-case x :vl-usertype)
;;   :short "Resolves a datatype of usertype kind to a concrete
;; datatype, i.e. anything but a user typename."
;;   :long "<p>The input is guarded to be a usertype.  If it is defined as another
;; usertype (possibly with packed/unpacked dimensions), then we recur until it is
;; defined as something other than a usertype.  However, the final type may still
;; have usertypes within it, i.e. as struct/union member types.</p>

;; <p>Also returns the scopestack representing the scope in which the
;; final type declaration was found.</p>

;; <p>This function is strict with respect to packed vs. unpacked dimensions;
;; i.e., if a usertype is defined as having unpacked dimensions, it will warn if
;; any packed dimensions are applied to that type.  Arguably this check should be
;; done elsewhere, in which case this function could ignore the distinction
;; between packed and unpacked dimensions.  However, it is important to preserve
;; the order of dimensions, and it's not clear how to handle cases that mix the
;; two: packed dimensions are always treated as \"inner\" or \"most rapidly
;; varying\" dimensions.  So if we have (illegal) nested typedefs that place
;; unpacked dimensions inside of packed dimensions, we have no way to express that
;; as a single, usertype-free datatype, unless we change some packed dimensions
;; into unpacked ones or vice versa:</p>

;; @({
;;  typedef logic t1 [5:1];  // unpacked dimension
;;  typedef t1 [3:0] t2;     // packed dimension applied to unpacked datatype

;;  typedef logic [3:0] t3 [5:1];  // not the same as t2

;;  typedef logic [5:1] [3:0] t4;  // same dimensions as t2, but all dimensions packed
;;  typedef logic t5 [5:1] [3:0];  // same dimensions as t2, but all dimensions unpacked
;;  })

;; <p>We don't have this problem for the (also illegal) case where packed
;; dimensions are applied to an unpacked structure or union, so we don't warn in
;; this case; this should be checked separately.</p>"

;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (type vl-datatype-p)
;;                (scope vl-scopestack-p))
;;   :measure (nfix rec-limit)
;;   :verify-guards nil
;;   (b* ((ss (vl-scopestack-fix ss))
;;        (x (vl-datatype-fix x))
;;        ((vl-usertype x))
;;        ((when (zp rec-limit))
;;         (mv (vmsg "Rec-limit ran out: recursively defined ~
;;                                        datatype? ~a1"
;;                   nil x.name)
;;             x ss))
;;        ((unless (vl-hidexpr-case (vl-scopeexpr->hid x.name) :end))
;;         (mv (vmsg "Type names cannot be specified with dotted ~
;;                                    paths, only package scopes: ~a1"
;;                   nil x.name)
;;             x ss))
;;        ((mv err trace ?tail)
;;         (vl-follow-scopeexpr x.name ss))
;;        ((when err)
;;         (mv err x ss))
;;        ((vl-hidstep ref) (car trace))
;;        ((unless (eq (tag ref.item) :vl-typedef))
;;         (mv (vmsg "Didn't find a typedef ~a1, instead ~
;;                                        found ~a2"
;;                   nil x.name ref.item)
;;             x ss))
;;        ((vl-typedef item) ref.item)
;;        ((mv warning subtype final-ss)
;;         (if (vl-datatype-case item.type :vl-usertype)
;;             (vl-usertype-resolve item.type ref.ss (1- rec-limit))
;;           (mv nil item.type ref.ss)))
;;        ((when warning)
;;         (mv warning x ss))
;;        (sub-udims (vl-datatype->udims subtype))
;;        ((when (and (consp x.pdims) (consp (vl-datatype->udims item.type))))
;;         ;; Bad case: we have unpacked dimensions from the inner call but
;;         ;; we're trying to add packed ones.  Warn and return x.
;;         (mv (vmsg "Usertype ~a1 was declared with packed ~
;;                                    dimensions, but its definition ~a2 already ~
;;                                    has unpacked dimensions."
;;                   x item.type)
;;             x ss))
;;        (subtype (mbe :logic (vl-datatype-update-dims
;;                              (append-without-guard x.pdims (vl-datatype->pdims subtype))
;;                              (append-without-guard x.udims sub-udims)
;;                              subtype)
;;                      :exec
;;                      (if (or x.udims x.pdims)
;;                          (vl-datatype-update-dims
;;                           (append-without-guard x.pdims (vl-datatype->pdims subtype))
;;                           (append-without-guard x.udims sub-udims)
;;                           subtype)
;;                        subtype))))
;;     (mv nil subtype final-ss))
;;   ///

;;   (verify-guards vl-usertype-resolve))




;; (defines vl-datatype-usertype-elim
;;   :verify-guards nil
;;   (define vl-datatype-usertype-elim ((x vl-datatype-p)
;;                                      (ss vl-scopestack-p)
;;                                      &key
;;                                      ((rec-limit natp) '1000))
;;     :measure (two-nats-measure rec-limit (vl-datatype-count x))
;;     :returns (mv (err (iff (vl-msg-p err) err))
;;                  (type vl-datatype-p))
;;     :prepwork ((local (in-theory (disable nfix))))

;;     :short "Resolves all usertypes within a datatype, recursively."
;;     :long "<p>A recursion limit is needed in case a usertype is defined in
;; terms of itself.</p>

;; <p>Always returns a datatype; however, when a warning is present, it may still
;; contain usertypes.</p>

;; <p>An example to work through: suppose we want to resolve the usertype memchunk
;; into a usertype-free datatype --</p>

;; @({
;;   typedef logic [3:0] mynibble;
;;   typedef mynibble [7:0] my32;
;;   typedef my32 [0:3] membank [63:0];
;;   // error: since membank now has unpacked dims, we can't give it more packed dims:
;;   // typedef membank [3:0] memchunk;
;;   // this works:
;;   typedef membank memchunk [3:0];
;;  })"
;;     (b* ((x (vl-datatype-fix x)))
;;       (vl-datatype-case x
;;         :vl-coretype (mv nil x)
;;         :vl-enum (mv nil x) ;; bozo 
;;         :vl-usertype
;;         (b* (((mv warning newx newss) (vl-usertype-resolve x ss))
;;              ((when warning) (mv warning newx))
;;              ((when (zp rec-limit))
;;               (mv (vmsg "Recursion limit ran out: ~a1"
;;                         nil x.name)
;;                   newx)))
;;           (vl-datatype-usertype-elim newx newss :rec-limit (1- rec-limit)))
;;         :vl-struct
;;         (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss))
;;              (newx (change-vl-struct x :members members)))
;;           (mv warning newx))
;;         :vl-union
;;         (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss))
;;              (newx (change-vl-union x :members members)))
;;           (mv warning newx)))))
;;   (define vl-structmembers-usertype-elim ((x vl-structmemberlist-p)
;;                                           (ss vl-scopestack-p)
;;                                           &key
;;                                           ((rec-limit natp) 'rec-limit))
;;     :measure (two-nats-measure rec-limit (vl-structmemberlist-count x))
;;     :returns (mv (err (iff (vl-msg-p err) err))
;;                  (newx vl-structmemberlist-p))
;;     (b* (((when (atom x)) (mv nil nil))
;;          ((mv warning type1) (vl-datatype-usertype-elim
;;                               (vl-structmember->type (car x)) ss
;;                               rec-limit))
;;          (first (change-vl-structmember (car x) :type type1))
;;          ((when warning) (mv warning (cons first (vl-structmemberlist-fix (cdr x)))))
;;          ((mv warning membs2) (vl-structmembers-usertype-elim (cdr x) ss rec-limit)))
;;       (mv warning (cons first membs2))))
;;   ///
;;   (deffixequiv-mutual vl-datatype-usertype-elim)

;;   (verify-guards vl-datatype-usertype-elim))


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


(define vl-packeddimensionlist-resolved-p ((x vl-packeddimensionlist-p))
  :short "Returns true if all sized packed dimensions are resolved."
  (b* (((when (atom x)) t)
       (x1 (car x)))
    (and (vl-packeddimension-case x1
           :unsized t
           :range (vl-range-resolved-p x1.range))
         (vl-packeddimensionlist-resolved-p (cdr x)))))

(define vl-packeddimensionlist-total-size ((x vl-packeddimensionlist-p))
  :short "Given a packeddimensionlist like [5:0][3:1][0:8], multiplies the
dimensions together to get the total number of bits, or returns nil if there
are unsized dimensions."
  :guard (vl-packeddimensionlist-resolved-p x)
  :verify-guards nil
  :returns (size maybe-posp :rule-classes :type-prescription)
  (b* (((when (atom x)) 1)
       (rest (vl-packeddimensionlist-total-size (cdr x)))
       ((unless rest) nil)
       (first (car x))
       ((when (vl-packeddimension-case first :unsized)) nil)
       (range (vl-packeddimension->range first)))
    (* (vl-range-size range) rest))
  ///
  (verify-guards vl-packeddimensionlist-total-size
    :hints (("goal" :in-theory (enable vl-packeddimensionlist-resolved-p)))))


(define vl-packeddimension-size ((x vl-packeddimension-p))
  :returns (mv (unresolved-flg)
               (size maybe-posp :rule-classes :type-prescription))
  (if (vl-packeddimension-case x :unsized)
      (mv nil nil)
    (b* ((range (vl-packeddimension->range x)))
      (if (vl-range-resolved-p range)
          (mv nil (vl-range-size range))
        (mv t nil)))))

(define vl-maybe-packeddimension-size ((x vl-maybe-packeddimension-p))
  :returns (mv (unresolved-flg)
               (size maybe-posp :rule-classes :type-prescription))
  (if x
      (vl-packeddimension-size x)
    (mv nil nil)))

(fty::deflist maybe-nat-list :elt-type maybe-natp)
              

(defines vl-datatype-size
  :prepwork ((local (in-theory (disable all-equalp
                                        stringp-when-true-listp
                                        default-*-1
                                        integerp-when-natp
                                        natp-when-posp
                                        rationalp-implies-acl2-numberp
                                        acl2::member-when-atom
                                        acl2::posp-redefinition
                                        rationalp-when-integerp
                                        double-containment
                                        member-equal-when-member-equal-of-cdr-under-iff
                                        equal-of-cons-rewrite)))
             (std::set-returnspec-mrec-default-hints
              ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world))))
  (define vl-datatype-size ((x vl-datatype-p "The datatype to size"))
    :short "Computes the number of bits in the datatype."
    :long "<p>This works for unpacked datatypes as well as packed ones; you
should check separately that the datatype is packed if that is what you want.
Returns nil without error if given a datatype that has no fixed bit size,
e.g. if it contains a real number or has unsized dimensions.  We produce an
error message if a usertype is not found, if the recursion limit runs out, or
if unresolved dimensions are present.</p>"

    :measure (vl-datatype-count x)
    :guard (vl-datatype-resolved-p x)
    :returns (mv (err (iff (vl-msg-p err) err))
                 (size maybe-natp :rule-classes :type-prescription))
    :verify-guards nil
    (b* ((x (vl-datatype-fix x))
         (udims (vl-datatype->udims x))
         (pdims (vl-datatype->pdims x))
         ((unless (vl-packeddimensionlist-resolved-p udims))
          (mv (vmsg "Unresolved unpacked dimensions: ~a0"
                    (vl-datatype-update-dims nil (append-without-guard udims pdims)
                                             x))
              nil))
         ((unless (vl-packeddimensionlist-resolved-p pdims))
          (mv (vmsg "Unresolved packed dimensions: ~a0" x)
              nil))
         (udim-size (vl-packeddimensionlist-total-size udims))
         (pdim-size (vl-packeddimensionlist-total-size pdims))
         (dim-size (and udim-size pdim-size (* udim-size pdim-size))))

      (vl-datatype-case x
        (:vl-coretype
         (b* (((vl-coredatatype-info typinfo) (vl-coretypename->info x.name)))
           (mv nil (and typinfo.size dim-size
                        (* typinfo.size dim-size)))))

        (:vl-struct
         (b* (((mv err widths) (vl-structmemberlist-sizes x.members))
              ((when err) (mv err nil))
              ((when (member nil widths)) (mv nil nil)))
           (mv nil (and dim-size (* (sum-nats widths) dim-size)))))

        (:vl-union
         (b* (((mv err widths) (vl-structmemberlist-sizes x.members))
              ((when err) (mv err nil))
              ((when (member nil widths)) (mv nil nil)))
           (mv nil (and dim-size (* (max-nats widths) dim-size)))))

        (:vl-enum
         (b* (((mv err sub-size)
               (vl-datatype-size x.basetype))
              ((when (or err (not sub-size)))
               (mv err nil)))
           (mv nil (and dim-size (* sub-size dim-size)))))

        (:vl-usertype
         (b* (((unless (mbt (and x.res t)))
               (mv (vmsg "Usertype unresolved: ~a0" x) nil))
              ((mv err sub-size)
               (vl-datatype-size x.res))
              ((when (or err (not sub-size)))
               (mv err nil)))
           (mv nil (and dim-size (* sub-size dim-size))))))))

  (define vl-structmemberlist-sizes ((x vl-structmemberlist-p))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (sizes maybe-nat-list-p))
    :guard (vl-structmemberlist-resolved-p x)
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((mv err1 size1) (vl-datatype-size (vl-structmember->type (car x))))
         ((mv err2 size2) (vl-structmemberlist-sizes (cdr x))))
      (mv (or err1 err2) (cons size1 size2)))
    ///
    (defret len-of-vl-structmemberlist-sizes
      (equal (len sizes)
             (len x))
      :hints (("goal" :induct (len x)
               :expand ((vl-structmemberlist-sizes x)))))
    (defret true-listp-of-vl-structmemberlist-sizes
      (true-listp sizes)
      :hints (("goal" :induct (len x)
               :expand ((vl-structmemberlist-sizes x))))
      :rule-classes :type-prescription))
  ///
  (local (defthm nat-listp-when-maybe-nat-list-p
           (implies (and (maybe-nat-list-p x)
                         (not (member nil x)))
                    (nat-listp x))
           :hints(("Goal" :in-theory (enable maybe-nat-list-p)))))
  
  (verify-guards vl-datatype-size)
  (deffixequiv-mutual vl-datatype-size))


(define vl-maybe-usertype-resolve ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :returns (new-x vl-datatype-p)
  :measure (vl-datatype-count x)
  (b* ((x (vl-datatype-fix x))
       ((when (or (consp (vl-datatype->pdims x))
                  (consp (vl-datatype->udims x))))
        x))
    (vl-datatype-case x
      :vl-usertype (if x.res
                       (vl-maybe-usertype-resolve x.res)
                     x)
      :otherwise x))
  ///
  (defret vl-datatype-count-of-vl-maybe-usertype-resolve
    (<= (vl-datatype-count new-x)
        (vl-datatype-count x))
    :rule-classes :linear)

  (defret vl-datatype-resolved-p-of-vl-maybe-usertype-resolve
    (implies (vl-datatype-resolved-p x)
             (vl-datatype-resolved-p new-x)))

  (local (defret vl-maybe-usertype-resolve-nonnil
           new-x
           :rule-classes :type-prescription))

  (defret not-usertype-of-vl-maybe-usertype-resolve
    (implies (and (not (consp (vl-datatype->pdims new-x)))
                  (not (consp (vl-datatype->udims new-x)))
                  (vl-datatype-resolved-p x))
             (not (equal (vl-datatype-kind new-x)  :vl-usertype)))
    :rule-classes
    ((:forward-chaining :trigger-terms
      ((vl-datatype-kind (vl-maybe-usertype-resolve x)))))))




(define vl-datatype-packedp ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :short "Decide whether the datatype is packed or not."
  :long "<p>A shallow check; e.g. we don't check for invalid things such as a
packed struct with a member that's an unpacked array.</p>

<p>Note that the question of whether something is packed is subtly different
from the question of whether you can select from it: namely, simple bit types
such as @('logic') are packed but not selectable.</p>"
  :returns (packedp)
  (b* ((x (vl-maybe-usertype-resolve x))
       ((when (consp (vl-datatype->udims x))) nil)
       ((when (consp (vl-datatype->pdims x))) t))
    (vl-datatype-case x
      :vl-coretype
      (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name)))
        (and xinfo.size t))
      :vl-struct x.packedp
      :vl-union x.packedp
      :vl-enum t
      :vl-usertype (impossible))))


(define vl-datatype-signedness ((x vl-datatype-p))
  :short "Decide whether the datatype is signed or not."
  :long "<p>Returns NIL if there isn't an appropriate signedness, as in an
unpacked or non-integer type.  This function never fails, as such, but in some
cases where implementations disagree on the correct signedness, we return a
flag to signal that there is a caveat about that signedness.</p>

<p>This caveat occurs when we have packed dimensions on a usertype that is
declared as signed.  In this case, NCV treats the array as unsigned, but VCS
treats it as signed.  The SV spec only touches on this to say (from Sec. 7.4.1,
Packed Arrays):</p>

<blockquote> If a packed array is declared as signed, then the array viewed as
a single vector shall be signed. The individual elements of the array are
unsigned unless they are of a named type declared as signed. A partselect of a
packed array shall be unsigned.</blockquote>

<p>An example:</p>

@({
  typedef logic signed [3:0] squad;

  squad [3:0] b;
  assign b = 16'hffff;

  logic [20:0] btest;
  assign btest = b;
 })

<p>In NCVerilog, btest has the value @('0ffff'), indicating that @('b') (as a
whole) is considered unsigned; in VCS, btest has the value @('fffff'),
indicating that @('b') is considered signed.</p>

"
  :guard (vl-datatype-resolved-p x)
  :measure (vl-datatype-count x)
  :returns (mv (caveat-flag)
               (signedness vl-maybe-exprtype-p))
  (b* (((when (consp (vl-datatype->udims x))) (mv nil nil)))
    (vl-datatype-case x
      :vl-coretype (b* (((vl-coredatatype-info typinfo) (vl-coretypename->info x.name)))
                     (mv nil (and typinfo.takes-signingp
                                  (if x.signedp :vl-signed :vl-unsigned))))
      :vl-struct (mv nil (and x.packedp (if x.signedp :vl-signed :vl-unsigned)))
      :vl-union (mv nil (and x.packedp (if x.signedp :vl-signed :vl-unsigned)))
      :vl-enum (vl-datatype-signedness x.basetype)
      :vl-usertype (b* (((unless (mbt (and x.res t))) (mv nil nil))
                        ((mv caveat ans1) (vl-datatype-signedness x.res))
                        ((when (and (consp (vl-datatype->pdims x))
                                    (eq ans1 :vl-signed)))
                         (mv t :vl-unsigned)))
                     (mv caveat ans1)))))






;; (defines vl-datatype-check-resolved
;;   (define vl-datatype-check-resolved ((x vl-datatype-p)
;;                                       (packedp))
;;     :returns (err (iff (vl-msg-p err) err))
;;     :measure (vl-datatype-count x)
;;     :short "Returns an explanatory message if the datatype has a problem that would
;;             prevent its size from being measured."
;;     :long "<p>Packedp indicates whether we require it to be a packed (i.e.,
;; vector) datatype.</p>"

;;     (b* ((x (vl-datatype-fix x))
;;          (udims (vl-datatype->udims x))
;;          ((when (and packedp (consp udims)))
;;           (vmsg "~a0: unpacked dimensions in packed context" x))
;;          ((unless (vl-packeddimensionlist-resolved-p udims))
;;           (vmsg "~a0 has unresolved unpacked dimensions" x))
;;          (pdims (vl-datatype->pdims x))
;;          ((unless (vl-packeddimensionlist-resolved-p pdims))
;;           (vmsg "~a0 has unresolved packed dimensions" x))
;;          (packedp (or (consp pdims) packedp)))
;;       (vl-datatype-case x
;;         :vl-coretype
;;         (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name))
;;              ((when (and packedp (not xinfo.size)))
;;               (vmsg "~a0: non-packed coretype" x)))
;;           nil)
;;         :vl-struct
;;         (b* (((unless (consp x.members))
;;               (vmsg "~a0: empty struct" x))
;;              ((when (and packedp (not x.packedp)))
;;               (vmsg "~a0: unpacked struct in packed context" x))
;;              (packedp (or packedp x.packedp)))
;;           (vl-structmemberlist-check-resolved x.members packedp))
;;         :vl-union
;;         (b* (((unless (consp x.members))
;;               (vmsg "~a0: empty union" x))
;;              ((when (and packedp (not x.packedp)))
;;               (vmsg "~a0: unpacked union" x))
;;              (packedp (or packedp x.packedp)))
;;           (vl-structmemberlist-check-resolved x.members packedp))
;;         :vl-enum
;;         (vmsg "~a0: enum types not yet supported" x)
;;         :vl-usertype
;;         (vmsg "~a0: datatype not resolved" x))))

;;   (define vl-structmemberlist-check-resolved ((x vl-structmemberlist-p)
;;                                               (packedp))
;;     :returns (err (iff (vl-msg-p err) err))
;;     :measure (vl-structmemberlist-count x)
;;     (if (atom x)
;;         nil
;;       (or (vl-datatype-check-resolved (vl-structmember->type (car x)) packedp)
;;           (vl-structmemberlist-check-resolved (cdr x) packedp))))
;;   ///
;;   (deffixequiv-mutual vl-datatype-check-resolved)
;;   (deffixequiv-mutual vl-datatype-check-resolved
;;     :args ((packedp booleanp)))


;;   (defthm-vl-datatype-check-resolved-flag
;;     (defthm vl-datatype-check-resolved-packed-implies-any
;;       (implies (and (syntaxp (not (equal packedp ''t)))
;;                     (not (vl-datatype-check-resolved x t)))
;;                (not (vl-datatype-check-resolved x packedp)))
;;       :flag vl-datatype-check-resolved)
;;     (defthm vl-structmemberlist-check-resolved-packed-implies-any
;;       (implies (and (syntaxp (not (equal packedp ''t)))
;;                     (not (vl-structmemberlist-check-resolved x t)))
;;                (not (vl-structmemberlist-check-resolved x packedp)))
;;       :flag vl-structmemberlist-check-resolved))

;;   (defthm-vl-datatype-check-resolved-flag
;;     (defthm vl-datatype-check-resolved-implies-unpacked
;;       (implies (not (vl-datatype-check-resolved x packedp))
;;                (not (vl-datatype-check-resolved x nil)))
;;       :flag vl-datatype-check-resolved)
;;     (defthm vl-structmemberlist-check-resolved-implies-unpacked
;;       (implies (not (vl-structmemberlist-check-resolved x packedp))
;;                (not (vl-structmemberlist-check-resolved x nil)))
;;       :flag vl-structmemberlist-check-resolved)))

;; (define vl-datatype-resolved-p ((x vl-datatype-p)
;;                                 (packedp))
;;   :enabled t
;;   (not (vl-datatype-check-resolved x packedp)))

;; (define vl-structmemberlist-resolved-p ((x vl-structmemberlist-p)
;;                                         (packedp))
;;   :enabled t
;;   (not (vl-structmemberlist-check-resolved x packedp)))


;; (defines vl-packed-datatype-size
;;   :verify-guards nil
;;   :prepwork ((local (defthm posp-sum-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (sum-nats x)))
;;                       :hints(("Goal" :in-theory (enable sum-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-max-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (max-nats x)))
;;                       :hints(("Goal" :in-theory (enable max-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-product
;;                       (implies (and (posp x) (posp y))
;;                                (posp (* x y)))))
;;              (local (in-theory (disable equal-of-cons-rewrite))))
;;   (define vl-packed-datatype-size
;;     :short "Get the size for any packed data type."
;;     :long "<p>The type should be fully resolved (i.e. no usertypes) and be
;; packed or we'll fail.</p>"
;;     ((x vl-datatype-p))
;;     :guard (vl-datatype-resolved-p x t)
;;     :returns
;;     (size    posp :rule-classes :type-prescription)
;;     :measure (vl-datatype-count x)
;;     (b* ((x (vl-datatype-fix x)))

;;       (vl-datatype-case x

;;         (:vl-coretype
;;          (b* ((totalsize (vl-packeddimensionlist-total-size x.pdims))
;;               ((vl-coredatatype-info typinfo) (vl-coretypename->info x.name)))
;;            (lposfix (* typinfo.size totalsize))))

;;         (:vl-struct
;;          (b* ((widths (vl-packed-structmemberlist-sizes x.members))
;;               (packedsize (vl-packeddimensionlist-total-size x.pdims)))
;;            (lposfix (* packedsize (sum-nats widths)))))

;;         (:vl-union
;;          (b* ((widths (vl-packed-structmemberlist-sizes x.members))
;;               (packedsize (vl-packeddimensionlist-total-size x.pdims)))
;;            (lposfix (* packedsize (max-nats widths)))))
;;         (:otherwise (lposfix (impossible))))))

;;   (define vl-packed-structmemberlist-sizes ((x vl-structmemberlist-p))
;;     :guard (vl-structmemberlist-resolved-p x t)
;;     :returns (sizes   (pos-listp sizes))
;;     :measure (vl-structmemberlist-count x)
;;     (if (atom x)
;;         nil
;;       (cons (vl-packed-datatype-size (vl-structmember->type (car x)))
;;             (vl-packed-structmemberlist-sizes (cdr x)))))
;;   ///
;;   (defthm-vl-packed-datatype-size-flag
;;     (defthm len-of-vl-packed-structmemberlist-sizes
;;       (b* ((sizes (vl-packed-structmemberlist-sizes x)))
;;         (equal (len sizes) (len x)))
;;       :hints ('(:expand ((vl-packed-structmemberlist-sizes x))))
;;       :flag vl-packed-structmemberlist-sizes)
;;     :skip-others t)

;;   (local (defthm nat-listp-when-pos-listp
;;            (implies (pos-listp x)
;;                     (nat-listp x))
;;            :hints(("Goal" :in-theory (enable nat-listp)))))

;;   (local (defthm posp-not-equal-0
;;            (implies (posp x)
;;                     (not (Equal x 0)))))

;;   (verify-guards vl-packed-datatype-size
;;     :hints(("Goal" :in-theory (enable vl-datatype-resolved-p
;;                                       vl-structmemberlist-resolved-p)
;;             :expand ((vl-datatype-check-resolved x t)
;;                      (vl-structmemberlist-check-resolved x t)))))

;;   (deffixequiv-mutual vl-packed-datatype-size))



;; (defines vl-datatype-size
;;   :verify-guards nil
;;   :prepwork ((local (defthm posp-sum-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (sum-nats x)))
;;                       :hints(("Goal" :in-theory (enable sum-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-max-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (max-nats x)))
;;                       :hints(("Goal" :in-theory (enable max-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-product
;;                       (implies (and (posp x) (posp y))
;;                                (posp (* x y)))))
;;              (local (in-theory (disable equal-of-cons-rewrite))))
;;   (define vl-datatype-size
;;     ((x vl-datatype-p))
;;     :short "Get the size for any datatype, even unpacked, that is made up of packed
;;             elements."
;;     :long "<p>We return NIL if there are non-bit datatypes like @('real').</p>"
;;     :guard (vl-datatype-resolved-p x nil)
;;     :returns
;;     (size    maybe-posp :rule-classes :type-prescription)
;;     :measure (vl-datatype-count x)
;;     (b* ((x (vl-datatype-fix x))
;;          (x.pdims (vl-datatype->pdims x))
;;          (x.udims (vl-datatype->udims x))
;;          (pdimsize (vl-packeddimensionlist-total-size x.pdims))
;;          (udimsize (vl-packeddimensionlist-total-size x.udims)))

;;       (vl-datatype-case x

;;         (:vl-coretype
;;          (b* (((vl-coredatatype-info typinfo) (vl-coretypename->info x.name))
;;               ((unless typinfo.size) nil))
;;            (lposfix (* typinfo.size pdimsize udimsize))))

;;         (:vl-struct
;;          (b* ((widths (vl-structmemberlist-sizes x.members))
;;               ((when (member nil widths)) nil))
;;            (lposfix (* (sum-nats widths) pdimsize udimsize))))

;;         (:vl-union
;;          (b* ((widths (vl-structmemberlist-sizes x.members))
;;               ((when (member nil widths)) nil))
;;            (lposfix (* (max-nats widths) pdimsize udimsize))))
;;         ;; BOZO enums
;;         (:otherwise nil))))

;;   (define vl-structmemberlist-sizes ((x vl-structmemberlist-p))
;;     :guard (vl-structmemberlist-resolved-p x nil)
;;     :returns (sizes   maybe-pos-list-p)
;;     :measure (vl-structmemberlist-count x)
;;     (if (atom x)
;;         nil
;;       (cons (vl-datatype-size (vl-structmember->type (car x)))
;;             (vl-structmemberlist-sizes (cdr x)))))
;;   ///
;;   (defthm-vl-datatype-size-flag
;;     (defthm len-of-vl-structmemberlist-sizes
;;       (b* ((sizes (vl-structmemberlist-sizes x)))
;;         (equal (len sizes) (len x)))
;;       :hints ('(:expand ((vl-structmemberlist-sizes x))))
;;       :flag vl-structmemberlist-sizes)
;;     :skip-others t)

;;   (local (defthm nat-listp-when-pos-listp
;;            (implies (pos-listp x)
;;                     (nat-listp x))
;;            :hints(("Goal" :in-theory (enable nat-listp)))))

;;   (local (defthm posp-not-equal-0
;;            (implies (posp x)
;;                     (not (Equal x 0)))))

;;   (local (defthm pos-listp-when-not-member-nil
;;            (implies (and (maybe-pos-list-p x)
;;                          (not (member nil x)))
;;                     (pos-listp x))
;;            :hints(("Goal" :in-theory (enable member)))))

;;   (verify-guards vl-datatype-size
;;     :hints(("Goal" :in-theory (enable vl-datatype-resolved-p
;;                                       vl-structmemberlist-resolved-p)
;;             :expand ((vl-datatype-check-resolved x nil)
;;                      (vl-structmemberlist-check-resolved x nil)))))

;;   (deffixequiv-mutual vl-datatype-size))






;; (defines vl-datatype-size
;;   :verify-guards nil
;;   :prepwork ((local (defthm posp-sum-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (sum-nats x)))
;;                       :hints(("Goal" :in-theory (enable sum-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-max-nats-of-pos-listp
;;                       (implies (and (pos-listp x) (consp x))
;;                                (posp (max-nats x)))
;;                       :hints(("Goal" :in-theory (enable max-nats)))
;;                       :rule-classes (:rewrite :type-prescription)))
;;              (local (defthm posp-product
;;                       (implies (and (posp x) (posp y))
;;                                (posp (* x y)))))
;;              (local (in-theory (disable equal-of-cons-rewrite not))))
;;   (define vl-datatype-size
;;     :short "Get the size for a data type, including unpacked dimensions."
;;     :long "<p>The type should be fully resolved (i.e. no usertypes) or we'll fail.</p>"
;;     ((x vl-datatype-p))
;;     :returns
;;     (mv (err (iff (vl-msg-p err) err))
;;         (size    (implies (not err) (posp size)) :rule-classes :type-prescription))
;;     :measure (vl-datatype-count x)
;;     (b* (((fun (fail reason args)) 
;;           (mv (make-vl-msg :msg reason
;;                            :args args)
;;               nil))
;;          ((fun (success width)) (mv nil width))
;;          (x (vl-datatype-fix x)))

;;       (vl-datatype-case x

;;         (:vl-coretype
;;          (b* ((udim-size (vl-packeddimensionlist-total-size x.udims))
;;               (pdim-size (vl-packeddimensionlist-total-size x.pdims))
;;               ((unless (and udim-size pdim-size))
;;                (fail "Dimensions of vector type ~a0 not resolvd"
;;                    (list x)))
              
;;               ((vl-coredatatype-info typinfo) (vl-coretypename->info x.name))
;;               ((unless typinfo.size)
;;                ;; Something like a real, shortreal, void, realtime, chandle, etc.
;;                (fail "bad coretype ~a0" (list x))))
;;            (success (* typinfo.size pdim-size udim-size))))

;;         (:vl-struct
;;          (b* (;; bozo is there a correct thing to do for a struct with no members?
;;               ((unless (consp x.members)) (fail "empty struct: ~a0" (list x)))
;;               ((mv warning widths) (vl-structmemberlist-sizes x.members))
;;               ((when warning) (mv warning nil))
;;               (packedsize (vl-packeddimensionlist-total-size x.pdims))
;;               (unpackedsize (vl-packeddimensionlist-total-size x.udims))
;;               ((unless (and packedsize unpackedsize))
;;                (fail "Dimensions of struct type ~a0 not resolvd"
;;                      (list x))))
;;            (success (* packedsize unpackedsize (sum-nats widths)))))

;;         (:vl-union
;;          (b* (;; bozo is there a correct thing to do for a union with no members?
;;               ((unless (consp x.members)) (fail "empty union: ~a0" (list x)))
;;               ((mv warning widths) (vl-structmemberlist-sizes x.members))
;;               ((when warning) (mv warning nil))
;;               (packedsize (vl-packeddimensionlist-total-size x.pdims))
;;               (unpackedsize (vl-packeddimensionlist-total-size x.udims))
;;               ((unless (and packedsize unpackedsize))
;;                (fail "Dimensions of union type ~a0 not resolvd"
;;                      (list x))))
;;            (success (* packedsize unpackedsize (max-nats widths)))))

;;         (:vl-enum ;; need to compute size from the base type?
;;          (fail "bozo: implement enum range" nil))

;;         (:vl-usertype
;;          (fail "unresolved usertype: ~a0" (list x.name))))))

;;   (define vl-structmemberlist-sizes ((x vl-structmemberlist-p))
;;     :returns (mv (err (iff (vl-msg-p err) err))
;;                  (sizes   (and (pos-listp sizes)
;;                                (implies (not err)
;;                                         (equal (consp sizes) (consp x))))))
;;     :measure (vl-structmemberlist-count x)
;;     (b* (((when (atom x)) (mv nil nil))
;;          ((vl-structmember first) (vl-structmember-fix (car x)))
;;          ((mv warning size) (vl-datatype-size first.type))
;;          ((when warning) (mv warning nil))
;;          ((mv warning rest) (vl-structmemberlist-sizes (cdr x)))
;;          ((when warning) (mv warning nil)))
;;       (mv nil (cons size rest))))
;;   ///
;;   (defthm-vl-datatype-size-flag
;;     (defthm len-of-vl-structmemberlist-sizes
;;       (b* (((mv warning sizes) (vl-structmemberlist-sizes x)))
;;         (implies (not warning)
;;                  (equal (len sizes) (len x))))
;;       :flag vl-structmemberlist-sizes)
;;     :skip-others t)

;;   (local (defthm nat-listp-when-pos-listp
;;            (implies (pos-listp x)
;;                     (nat-listp x))
;;            :hints(("Goal" :in-theory (enable nat-listp)))))

;;   (verify-guards vl-datatype-size)

;;   (deffixequiv-mutual vl-datatype-size))









;; (define vl-datatype-exprtype
;;   :parents (datatype-tools vl-expr-typedecide)
;;   :short "Get the self-determined signedness of a datatype."
;;   ((x vl-datatype-p))
;;   :returns
;;   (type vl-maybe-exprtype-p
;;         "On success: the self-determined signedness (exprtype) of this expression.
;;           Note that some expressions (e.g., real numbers, unpacked types) have
;;          exprtype NIL.")
;;   :long "<p>BOZO This is tricky with packed arrays etc.; I'm not sure we've
;; taken time yet to understand all the rules.</p>"
;;   (b* (((when (consp (vl-datatype->udims x)))
;;         nil))
;;     (vl-datatype-case x

;;       (:vl-coretype
;;        (b* (((vl-coredatatype-info typinfo) (vl-coretypename->info x.name))
;;             ((when typinfo.takes-signingp)
;;              (success (if x.signedp :vl-signed :vl-unsigned))))
;;          (success nil)))

;;       (:vl-enum ;; just need to look at the base type, right?
;;        (fail "bozo: implement enum typing"))
      
;;       (:vl-struct ;; just need to look at signedp and packed?
;;        (b* (((unless x.packedp)
;;              (fail "non-packed struct")
;;              ;; Can we just say unpacked stuff is always unsigned?
;;              ))
;;          (success (if x.signedp :vl-signed :vl-unsigned))))

;;       (:vl-union ;; just need to look at signedp and packed?
;;        (b* (((unless x.packedp)
;;              (fail "non-packed union")
;;              ;; Can we just say unpacked stuff is always unsigned?
;;              ))
;;          (success (if x.signedp :vl-signed :vl-unsigned))))

;;       (:vl-usertype
;;        ;; BOZO maybe some day extend this to be able to do lookups, but maybe
;;        ;; just depend on usertype-elim
;;        (fail "vl-datatype-exprtype can't handle unresolved usertypes")))))


(define vl-datatype-select-ok ((x vl-datatype-p))
  :parents (datatype-tools)
  :short "Determines whether this datatype can be selected."
  :long "<p>The input datatype should not have packed or unpacked dimensions;
if it does, then it's definitely OK to index into it (though it's only a
select if it's the last packed dimension).  The input datatype should have
usertypes resolved.</p>"
  :guard (vl-datatype-resolved-p x)
  :returns (ok)
  :measure (vl-datatype-count x)
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
               (dim   (implies (not err) (vl-packeddimension-p dim))
                      "Dimension removed from the datatype"))
  (b* ((x (vl-maybe-usertype-resolve x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        (mv nil nil
            (vl-datatype-update-udims
             (cdr udims) x)
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
             ((mv & signedness) (vl-datatype-signedness new-x)))
          (mv nil (eq signedness :vl-signed) new-x (car pdims))))
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
       (dim (vl-range->packeddimension (make-vl-range :msb (vl-make-index (1- size))
                                                      :lsb (vl-make-index 0)))))
    (mv nil nil
        (make-vl-coretype :name :vl-logic) dim))
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





;; (define vl-datatype-remove-dims ((n natp)
;;                                  (x vl-datatype-p)
;;                                  (ss vl-scopestack-p))
;;   :short "Get the type of a variable of type @('x') after @('n') indexing
;; operations are applied to it."
;;   :long "
;; <p>The caveat flag returned identifies a case where implementations disagree on
;; the signedness of the resulting type.  This caveat occurs when we have packed
;; dimensions on a usertype that is declared as signed.  In this case, if we index
;; into an object down to the usertype, NCV treats the resulting object as signed,
;; but VCS treats it as unsigned.  The SV spec seems to say NCV's interpretation
;; is correct: from Sec. 7.4.1, Packed Arrays:</p>

;; <blockquote> If a packed array is declared as signed, then the array viewed as
;; a single vector shall be signed. The individual elements of the array are
;; unsigned unless they are of a named type declared as signed. A partselect of a
;; packed array shall be unsigned.</blockquote>

;; <p>An example:</p>

;; @({
;;   typedef logic signed [3:0] squad;

;;   squad [3:0] b;
;;   assign b = 16'hffff;

;;   logic [7:0] btest;
;;   assign btest = b[1];
;;  })

;; <p>In NCVerilog, btest has the value @('ff'), indicating that @('b[1]') is
;; considered signed; in VCS, btest has the value @('0f'), indicating that
;; @('b[1]') is considered unsigned.</p>"
;;   :prepwork
;;   ((local (in-theory (disable not equal-of-cons-rewrite
;;                               equal-of-vl-usertype
;;                               acl2::len-when-atom
;;                               acl2::true-listp-of-nthcdr
;;                               acl2::true-listp-when-string-listp-rewrite
;;                               acl2::true-listp-when-symbol-listp-rewrite
;;                               acl2::nfix-when-not-natp
;;                               acl2::zp-open
;;                               acl2::consp-under-iff-when-true-listp
;;                               acl2::list-fix-under-iff
;;                               acl2::append-when-not-consp
;;                               acl2::list-fix-when-len-zero
;;                               acl2::take-of-len-free
;;                               double-containment))))


;;   :guard (not (vl-datatype-check-usertypes x ss))
;;   :returns (mv (err (iff (vl-msg-p err) err)  "Error message on failure")
;;                (caveat-flag "Indicates caveat about possible signedness ambiguities")
;;                (new-x (implies (not err) (vl-datatype-p new-x))
;;                       "Datatype after indexing")
;;                (dims  vl-packeddimensionlist-p)
;;                (new-ss vl-scopestack-p "Scopestack where the most recently looked-up
;;                                         usertype was defined -- this is the scopestack
;;                                         needed to look up the next usertype that
;;                                         might remain in the new type."))
;;   :measure (two-nats-measure
;;             n
;;             (if (and (vl-datatype-case x :vl-usertype)
;;                      (not (consp (vl-datatype->udims x)))
;;                      (not (consp (vl-datatype->pdims x))))
;;                 1 0))
;;   (b* ((x (vl-datatype-fix x))
;;        (ss (vl-scopestack-fix ss))
;;        (udims (list-fix (vl-datatype->udims x)))
;;        (pdims (list-fix (vl-datatype->pdims x)))
;;        (nu (len udims))
;;        (n (lnfix n))
;;        ((when (<= n nu))
;;         (mv nil nil
;;             (vl-datatype-update-udims
;;              (nthcdr n udims) x)
;;             (take n udims)
;;             ss))
;;        (n (- n nu))
;;        (np (len pdims))
;;        ((when (<= n np))
;;         (b* ((x (vl-datatype-set-unsigned x))
;;              (dims (append udims (take n pdims)))
;;              ((when (or (vl-datatype-case x :vl-usertype)
;;                         (< n np)))
;;               ;; (unless (and (eql n np)
;;               ;;              (not (vl-datatype-case x :vl-usertype))))
;;               (mv nil nil
;;                   (vl-datatype-update-dims
;;                    (nthcdr n pdims)
;;                    nil ;; no udims
;;                    x)
;;                   dims
;;                   ss))
;;              (new-x (vl-datatype-update-dims nil nil x))
;;              ((mv & signedness) (vl-datatype-signedness new-x ss)))
;;           (mv nil (eq signedness :vl-signed) new-x dims ss)))
;;        (n (- n np)))
;;     (vl-datatype-case x
;;       :vl-usertype
;;       (b* (((mv err def new-ss) (vl-usertype-resolve x.name ss))
;;            ((when err) (mv err nil nil (append udims pdims) new-ss))
;;            ((mv err caveat new-x rest-dims new-ss)
;;             (vl-datatype-remove-dims n def new-ss)))
;;         (mv err caveat new-x (append udims pdims rest-dims) new-ss))
;;       :otherwise
;;       (b* ((x (vl-datatype-update-dims nil nil x))
;;            ((unless (vl-datatype-packedp x ss))
;;             (mv (vmsg "Index applied to non-packed, non-array type ~a0" x)
;;                 nil nil (append udims pdims) ss))
;;            ((unless (eql n 1))
;;             (mv (vmsg "Too many indices applied to packed non-array ~a0" x) nil nil (append udims pdims) ss))
;;            ((mv err size) (vl-datatype-size x ss))
;;            ((when err)
;;             (mv err nil nil (append udims pdims) ss))
;;            ((unless (posp size))
;;             (mv (vmsg "Index applied to ~s0 packed type: ~a1"
;;                       (if size "unsizeable" "zero-sized") x)
;;                 nil nil (append udims pdims) ss))
;;            ((when (and (vl-datatype-case x :vl-coretype)
;;                        (eql size 1)))
;;             (mv (vmsg "Index applied to bit type ~a0" x) nil nil (append udims pdims) ss))
;;            (dim (vl-range->packeddimension (make-vl-range :msb (vl-make-index (1- size))
;;                                                           :lsb (vl-make-index 0)))))
;;         (mv nil nil
;;             (make-vl-coretype :name :vl-logic)
;;             (append udims pdims (list dim))
;;             ss))))
;;   ///
;;   (defret vl-datatype-check-usertypes-of-remove-dims
;;     (implies (and (not (vl-datatype-check-usertypes x ss :rec-limit rec-limit))
;;                   (not err))
;;              (not (vl-datatype-check-usertypes new-x new-ss :rec-limit rec-limit)))
;;     :hints (("goal" :induct t :in-theory (enable vl-datatype-check-usertypes))))

;;   (defret vl-datatype-remove-dims-true-listp-dims
;;     (true-listp dims)
;;     :rule-classes :type-prescription)

;;   (defret vl-datatype-remove-dims-dims-length
;;     (implies (not err)
;;              (equal (len dims)
;;                     (nfix n))))

;;   (verify-guards vl-datatype-remove-dims
;;     :hints ((and stable-under-simplificationp
;;                  '(:expand ((:free (rec-limit)
;;                              (vl-datatype-check-usertypes x ss :rec-limit rec-limit)))))))


;;   (local
;;    (defthm vl-datatype-update-dims-compose
;;      (equal (vl-datatype-update-dims
;;              pdims udims
;;              (vl-datatype-update-dims
;;               pdims1 udims1 x))
;;             (vl-datatype-update-dims
;;              pdims udims x))
;;      :hints(("Goal" :in-theory (enable vl-datatype-update-dims)))))


;;   (local (Defthm append-of-nil
;;            (equal (append nil x) x)
;;            :hints(("Goal" :in-theory (enable append)))))

;;   (local (defthm list-fix-of-nthcdr
;;            (equal (list-fix (nthcdr n x))
;;                   (nthcdr n (list-fix x)))))
;;   (local (in-theory (disable acl2::nthcdr-of-list-fix)))

;;   (local (defthm append-take-take-nthcdr
;;            (equal (append (take n a)
;;                           (take m (nthcdr n a)))
;;                   (take (+ (nfix n) (nfix m)) a))
;;            :hints (("goal" :induct (nthcdr n a)
;;                     :in-theory (enable acl2::take-redefinition nthcdr)))))

;;   (local (defthm append-take-nthcdr
;;            (implies (<= (nfix n) (len a))
;;                     (equal (append (take n a)
;;                                    (nthcdr n a))
;;                            a))
;;            :hints (("goal" :induct (nthcdr n a)
;;                     :in-theory (enable acl2::take-redefinition nthcdr len)))))

;;   (local (defthm append-take-take-nthcdr-1
;;            (equal (append (take n a)
;;                           (take m (nthcdr n a))
;;                           x)
;;                   (append (take (+ (nfix n) (nfix m)) a) x))
;;            :hints (("goal" :induct (nthcdr n a)
;;                     :in-theory (enable acl2::take-redefinition nthcdr)))))

;;   (local (defthm append-take-nthcdr-1
;;            (implies (<= (nfix n) (len a))
;;                     (equal (append (take n a)
;;                                    (nthcdr n a)
;;                                    x)
;;                            (append a x)))
;;            :hints (("goal" :induct (nthcdr n a)
;;                     :in-theory (enable acl2::take-redefinition nthcdr len)))))

;;   (local (in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1)))
;;   ;; (local (defthm nfix-linear
;;   ;;          (<= 0 (nfix n))
;;   ;;          :rule-classes :linear))

;;   (local (defthm vl-datatype-kind-of-set-unsigned
;;            (equal (vl-datatype-kind (vl-datatype-set-unsigned x))
;;                   (vl-datatype-kind x))
;;            :hints(("Goal" :in-theory (enable vl-datatype-set-unsigned)))))

;;   (local (defthm packedp-update-dims-of-set-unsigned
;;            (equal (vl-datatype-packedp
;;                    (vl-datatype-update-dims
;;                     pdims udims (vl-datatype-set-unsigned x))
;;                    ss)
;;                   (vl-datatype-packedp
;;                    (vl-datatype-update-dims
;;                     pdims udims x)
;;                    ss))
;;            :hints(("Goal" :in-theory (enable vl-datatype-packedp
;;                                              vl-datatype-update-dims
;;                                              vl-datatype-set-unsigned)))))

;;   (local (defthm size-update-dims-of-set-unsigned
;;            (b* (((mv err1 size1)
;;                  (vl-datatype-size
;;                    (vl-datatype-update-dims
;;                     pdims udims (vl-datatype-set-unsigned x))
;;                    ss))
;;                 ((mv err2 size2)
;;                  (vl-datatype-size
;;                   (vl-datatype-update-dims
;;                    pdims udims x)
;;                   ss)))
;;              (and (iff err1 err2)
;;                   (equal size1 size2)))
;;            :hints(("Goal" :in-theory (enable vl-datatype-size
;;                                              vl-datatype-update-dims
;;                                              vl-datatype-set-unsigned)))))

;;   (local (defthm vl-usertype->name-of-update-dims
;;            (equal (vl-usertype->name (vl-datatype-update-dims pdims udims x))
;;                   (vl-usertype->name x))
;;            :hints(("Goal" :in-theory (enable vl-datatype-update-dims
;;                                              vl-usertype->name-when-wrong-kind)))))

;;   (local (defthm vl-usertype->name-of-set-unsigned
;;            (equal (vl-usertype->name (vl-datatype-set-unsigned x))
;;                   (vl-usertype->name x))
;;            :hints(("Goal" :in-theory (enable vl-datatype-set-unsigned
;;                                              vl-usertype->name-when-wrong-kind)))))

;;   (local (defthm vl-datatype-set-unsigned-of-update-dims
;;            (Equal (vl-datatype-set-unsigned
;;                    (vl-datatype-update-dims pdims udims x))
;;                   (vl-datatype-update-dims pdims udims (vl-datatype-set-unsigned x)))
;;            :hints(("Goal" :in-theory (enable vl-datatype-set-unsigned
;;                                              vl-datatype-update-dims)))))

;;   (local (Defthm vl-datatype-set-unsigned-idempotent
;;            (equal (vl-datatype-set-unsigned (vl-datatype-set-unsigned x))
;;                   (vl-datatype-set-unsigned x))
;;            :hints(("Goal" :in-theory (enable vl-datatype-set-unsigned)))))

;;   (local (in-theory (disable vl-datatype-fix-when-vl-coretype
;;                              vl-datatype-fix-when-vl-struct
;;                              vl-datatype-fix-when-vl-union
;;                              vl-datatype-fix-when-vl-enum
;;                              vl-datatype-fix-when-vl-usertype)))

;;   (local (defthm <=-when-equal
;;            (implies (equal a b)
;;                     (<= a b))))

;;   (defthm vl-datatype-remove-dims-compose
;;     (b* (((mv err ?caveat new-x dims new-ss)
;;           (vl-datatype-remove-dims (+ (nfix n) (nfix m)) x ss))
;;          ((mv err1 ?caveat1 new-x1 dims1 new-ss1)
;;           (vl-datatype-remove-dims n x ss))
;;          ((mv err2 ?caveat2 new-x2 dims2 new-ss2)
;;           (vl-datatype-remove-dims m new-x1 new-ss1)))
;;       (implies (not err)
;;                (and (not err1)
;;                     (not err2)
;;                     ;; (equal caveat2 caveat)
;;                     (equal new-x2 new-x)
;;                     (equal new-ss2 new-ss)
;;                     (list-equiv (append dims1 dims2) dims))))
;;     :hints (("goal" :induct (vl-datatype-remove-dims n x ss)
;;              :in-theory (disable (:d vl-datatype-remove-dims))
;;              :expand ((:free (n) (vl-datatype-remove-dims n x ss))
;;                       (:free (x ss)
;;                        (vl-datatype-remove-dims 1 x ss))
;;                       ;; (:free (x) (vl-datatype-size (vl-datatype-update-dims nil nil x) ss))
;;                       ))
;;             ;; (and stable-under-simplificationp
;;             ;;      '(:in-theory (enable 
;;             ;;                     vl-datatype-update-dims
;;             ;;                     vl-datatype-set-unsigned
;;             ;;                     vl-datatype-packedp)))
;;             (and stable-under-simplificationp
;;                  '(:expand ((:free (x ss)
;;                              (vl-datatype-remove-dims m x ss)))))
;;             )))


;; (define vl-hidindex-datatype-resolve-dims ((x vl-hidindex-p)
;;                                            (type vl-datatype-p))
;;   :short "Given the indices of some expression, e.g. foo[5][3], and the
;; datatype of foo, return the datatype of the whole expression."

;;   :long "<p>Note: we don't check whether indices are in bounds or anything,
;; just whether the number of indices is less than or equal the number of
;; total (unpacked plus packed) dimensions.</p>

;; <p>We produce a non-fatal warning because we're not sure in what contexts this
;; will be used.</p>

;; <p>Example: Suppose our datatype is from a typedef</p>

;; @({
;;     typedef bit [3:0] [4:2] foo [0:6] [0:8];
;; })

;; <p>that is, it has one unpacked dimension @('[0:6]') and two packed dimensions.
;; Suppose our expression is @('bar[5][7][2]'), where bar is of type foo.  Then we
;; should return @('bit[4:2]') as our resolved datatype, with no unpacked
;; dimensions, because the first two indices correspond to the unpacked dimension
;; and the second to the first packed dimension.  On the other hand if we had
;; @('bar[5]'), we should return @('bit') with packed dimensions @('[3:0][4:2]')
;; and unpacked dimension @('[0:8]').</p>"
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (type1 (iff (vl-datatype-p type1) (not warning))))
;;   (b* ((idxcount (len (vl-hidindex->indices x)))
;;        (type (vl-datatype-fix type))
;;        (x (vl-hidindex-fix x))
;;        (unpacked-dims (vl-datatype->udims type))
;;        (packed-dims (vl-datatype->pdims type))
;;        (nunpacked (len unpacked-dims))
;;        ((when (<= idxcount nunpacked))
;;         (mv nil (vl-datatype-update-udims
;;                  (nthcdr idxcount (list-fix unpacked-dims)) type)))
;;        (remaining-idxcount (- idxcount nunpacked))
;;        ((unless (<= remaining-idxcount (len packed-dims)))
;;         (mv (make-vl-warning :type :vl-too-many-indices
;;                              :msg "Too many indices on expression ~a0 ~
;;                                    relative to dimensions of type ~a1."
;;                              :args (list x type)
;;                              :fn __function__)
;;             nil))
;;        (type (vl-datatype-update-dims
;;               (nthcdr remaining-idxcount (list-fix packed-dims))
;;               nil ;; udims
;;               type)))
;;     (mv nil type)))


;; Have a HID, and know (for the base name) the type (unresolved) and unpacked
;; dims.

;; Resolve the type.
;; If the hid is an ID, return the type and dims.

;; Resolve the indices of the base part against the unpacked/packed dims.  If we
;; end up still having dims remaining, fail.

;; If the type is not a struct or union type, fail.

;; Find the next name in the HID among the structmembers.  If not found, fail.

;; Recur with the rest of the HID and the type/unpacked dims of the member.


;; (define vl-hidexpr-traverse-datatype ((x vl-hidexpr-p)
;;                                       (type vl-datatype-p)
;;                                       (ss vl-scopestack-p))
;;   :measure (vl-hidexpr-count x)
;;   :guard (not (vl-datatype-check-usertypes type ss))
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (final-type (implies (not err) (vl-datatype-p final-type))))
;;   (b* (((mv type ss)
;;         (if (vl-datatype-case type :vl-usertype)
;;             (b* (((mv & type ss) (vl-usertype-resolve type ss)))
;;               (mv type ss))
;;           (mv type ss)))
;;        ((mv name1 indices rest)
;;         (vl-hidexpr-case x
;;           :end (mv x.name nil nil)
;;           :dot (b* (((vl-hidindex x.first)))
;;                  (mv x.first.name x.first.indices x.rest))))
;;        ((mv ok members) (vl-datatype->structmembers baretype))
;;        ((unless (and (atom (vl-datatype->udims type))
;;                      (atom (vl-datatype->pdims type))
;;                      ok))
;;         (mv (vmsg "Can't get field ~s0 from non-struct/union type ~a1"
;;                   name1 type)
;;             nil))
;;        (member (vl-find-structmember name1 members))
;;        ((unless member)
;;         (mv (vmsg "Dot-indexing failed: struct/union member ~
;;                                    ~s0 not found in type ~a1"
;;                   nextname (vl-datatype-fix baretype))
;;             nil))
;;        (membtype (vl-structmember->type member))



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
                  (vl-datatype-update-dims (append-without-guard
                                            (vl-datatype->udims type)
                                            (vl-datatype->pdims type))
                                           nil type))
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



;; (define vl-hidexpr-traverse-datatype ((x vl-hidexpr-p)
;;                                       (type vl-datatype-p)
;;                                       (ss vl-scopestack-p))
;;   :parents (hid-tools)
;;   :short "Given a HID expression that indexes into a datatype, find the type
;;           of the expression."
;;   :long " <p>A helpful invariant to remember when thinking about this function:
;; The type input of a given call of this function belong to the base (leftmost)
;; variable in the HID.</p>

;; <p>Example: Suppose we have the following type declarations</p>
;; @({
;;  typedef struct packed { logic [3:0] foo; } [4:0] foostruct;
;;  typedef union { foostruct [5:0] bar; logic [2:0] baz; } bunion [0:6];
;;  typedef struct { bunion fa [0:8], logic [1:0] ba; } bstruct;
;;  bstruct myvar [8:0];
;; })

;; <p>For this example, we'll write a type with both packed an unpacked dimensions
;; with an underscore between the packed and unpacked dims.</p>

;; <p>A bunion is a type consisting of an unpacked array of 7 elements
;; each of which may either be a packed array of 6 foostructs (a packed structure
;; containing one 4-bit logic field) or a 3-bit logic; a bstruct is a struct
;; containing an unpacked array of 9 bunions and an additional 2-bit logic field;
;; and myvar is an unpacked array of 9 bstructs.</p>

;; <p>Suppose our expression is @('myvar[1].fa[8][4].bar[3][4].foo').</p>

;; <ul>

;; <li>First, before calling this function we look up the type of myvar.  We get a
;; vardecl, which has a type @('bstruct _ [8:0]'). Then we're ready to run.</li>

;; <li>Outermost call: We resolve the type bstruct to its struct definition.  We
;; cancel our index with the single array dimension, leaving just the struct.  We
;; find the element fa inside the struct, and
;; recur on the remainder of our expression, @('fa[8][4].bar[3][4].foo'), with the
;; structmember's type, @('bunion _ [0:8]').</li>

;; <li> We resolve the bunion type to the union, and append the unpacked
;; dimensions of the type and the element to get @('[0:8][0:6]').  We then check
;; the indices from the expression against this type and unpacked dimensions,
;; which results in just the bare union type (the definition of bunion, but
;; without its unpacked dimension @('[0:6]')).  We find the element bar inside the
;; union and recur: @('bar[3][4].foo'), type @('foostruct[5:0]').</li>

;; <li> We resolve the type foostruct to its struct type, and append the packed
;; dimensions to get @('[5:0][4:0]').  We then check the indices from the
;; expression, which results in cancelling out the dimension to obtain just the
;; bare struct.  We find the element foo of the struct and recur on that.</li>

;; <li>Finally, we have just the atom @('foo') as our expression, so we return the
;; type @('logic[3:0]').</li> </ul>"
;;   :measure (vl-hidexpr-count x)
;;   :guard (not (vl-datatype-check-usertypes type ss))
;;   :verify-guards nil
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (restype (iff (vl-datatype-p restype) (not err)))
;;                (dims vl-packeddimensionlist-p
;;                      "Dimensions of indices along the way")
;;                (final-ss vl-scopestack-p "Scopestack in which the last usertype was found"))

;;   ;; Resolve the type and dims.
;;   (b* ((type (vl-datatype-fix type))
;;        (ss (vl-scopestack-fix ss))
;;        ((when (vl-hidexpr-case x :end))
;;         ;; We just have an ID.  Return the resolved type.
;;         (mv nil type nil ss))

;;        ;; Cancel the indices of the first element of the HID with the unpacked
;;        ;; and packed dims of the type.

;;        ;; Note: We have at least one more dot in this HID, so if we don't have
;;        ;; a struct or union at the end of this, we have a problem.
;;        ((vl-hidexpr-dot x))
;;        (nindices (len (vl-hidindex->indices x.first)))
       
;;        ((mv err ?caveat idxtype dims ss)
;;         ;; Ignore the caveat because we're going dot-index into the new type at
;;         ;; least once more.
;;         (vl-datatype-remove-dims nindices type ss))
;;        ((when err) (mv err nil nil ss))

;;        ((mv baretype ss) (vl-maybe-usertype-resolve idxtype ss))

;;        ;; Next we're going to dot-index into the datatype, so get its
;;        ;; structmembers, making sure it's a struct.
;;        ((mv ok members) (vl-datatype->structmembers baretype))
;;        ((unless (and ok
;;                      (atom (vl-datatype->udims baretype))
;;                      (atom (vl-datatype->pdims baretype))))
;;         (mv (vmsg "Dot-indexing (field ~s0) into a non-struct/union datatype: ~a1"
;;                   (vl-datatype-update-dims (append-without-guard
;;                                             (vl-datatype->udims baretype)
;;                                             (vl-datatype->pdims baretype))
;;                                            nil baretype))
;;             nil nil ss))

;;        ;; Look up the member corresponding to the next name in the hid.
;;        (nextname (vl-hidexpr-case x.rest
;;                    :end x.rest.name
;;                    :dot (vl-hidindex->name x.rest.first)))
;;        (member (vl-find-structmember nextname members))
;;        ((unless member)
;;         (mv (vmsg "Dot-indexing failed: struct/union member ~
;;                                    ~s0 not found in type ~a1"
;;                   nextname (vl-datatype-fix baretype))
;;             nil nil ss))
;;        (membtype (vl-structmember->type member))
;;        ((mv err type rest-dims ss)
;;         (vl-hidexpr-traverse-datatype x.rest membtype ss)))
;;     (mv err type (append dims rest-dims) ss))
;;   ///

;;   (defret true-listp-dims-of-vl-hidexpr-traverse-datatype
;;     (true-listp dims)
;;     :rule-classes :type-prescription)

;;   (defret len-dims-of-vl-hidexpr-traverse-datatype
;;     (implies (not err)
;;              (equal (len dims)
;;                     (vl-hidexpr-index-count x)))
;;     :hints(("Goal" :in-theory (enable vl-hidexpr-index-count))))

;;   ;; bozo move these two theorems
;;   (defthm vl-structmemberlist-check-usertypes-of-vl-datatype->structmembers
;;     (b* (((mv ok members) (vl-datatype->structmembers x)))
;;       (implies (and (not (vl-datatype-check-usertypes x ss :rec-limit rec-limit))
;;                     ok)
;;                (not (vl-structmemberlist-check-usertypes members ss :rec-limit rec-limit))))
;;     :hints(("Goal" :in-theory (enable vl-datatype->structmembers
;;                                       vl-datatype-check-usertypes))))
  
;;   (defthm vl-datatype-check-usertypes-of-find-structmember
;;     (implies (and (not (vl-structmemberlist-check-usertypes members ss :rec-limit rec-limit))
;;                   (vl-find-structmember name members))
;;              (not (vl-datatype-check-usertypes
;;                    (vl-structmember->type (vl-find-structmember name members))
;;                    ss :rec-limit rec-limit)))
;;     :hints(("Goal" :in-theory (enable vl-structmemberlist-check-usertypes
;;                                       vl-find-structmember))))

;;   (verify-guards vl-hidexpr-traverse-datatype)

;;   (defret vl-datatype-check-usertypes-of-vl-hidexpr-traverse-datatype
;;     (implies (and (not (vl-datatype-check-usertypes type ss :rec-limit rec-limit))
;;                   (not err))
;;              (not (vl-datatype-check-usertypes restype final-ss :rec-limit rec-limit)))))

;; (define vl-scopeexpr-find-type ((x   vl-scopeexpr-p)
;;                                 (ss  vl-scopestack-p))
;;   :parents (hid-tools)
;;   :short "Looks up a HID in a scopestack and looks for a declaration, returning
;;           the type if found, and the scopestack relative to that type."
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (type (iff (vl-datatype-p type) (not err)))
;;                (dims vl-packeddimensionlist-p)
;;                (type-ss vl-scopestack-p))
;;   (b* ((x (vl-scopeexpr-fix x))
;;        (ss (vl-scopestack-fix ss))
;;        ((mv err trace tail) (vl-follow-scopeexpr x ss))
;;        ((when err) (mv err nil nil ss))
;;        ((vl-hidstep step1) (car trace))
;;        ((when (eq (tag step1.item) :vl-vardecl))
;;         ;; check its datatype
;;         (b* (((vl-vardecl step1.item))
;;              (err (vl-datatype-check-usertypes step1.item.type step1.ss))
;;              ((when err) (mv err nil nil step1.ss)))
;;           (vl-hidexpr-traverse-datatype tail step1.item.type step1.ss))))
;;     (mv (vmsg "Failed to find a type for ~s1 because we ~
;;                                didn't find a vardecl but rather a ~x2"
;;               nil x (tag step1.item))
;;         nil nil ss))
;;   ///
;;   (defret true-listp-dims-of-vl-scopeexpr-find-type
;;     (true-listp dims)
;;     :rule-classes :type-prescription)

;;   (defret len-dims-of-vl-scopeexpr-find-type
;;     (implies (not err)
;;              (equal (len dims)
;;                     (vl-hidexpr-index-count (mv-nth 2 (vl-follow-scopeexpr x ss)))))
;;     :hints(("Goal" :in-theory (enable vl-scopeexpr-index-count))))

;;   (defret vl-datatype-check-usertypes-of-vl-scopeexpr-find-type
;;     (implies (not err)
;;              (not (vl-datatype-check-usertypes type type-ss))))

;;   (defret follow-scopeexpr-when-vl-scopeexpr-find-type
;;     (implies (not err)
;;              (not (mv-nth 0 (vl-follow-scopeexpr x ss))))))


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
           ((when (eql width 0))
            (mv (vmsg "Zero-width partselect not allowed: ~a0"
                      x)
                nil)))
        (mv nil width))
      :otherwise (mv (vmsg "Impossible") (impossible)))))
  

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




(defthm vl-exprlist-count-of-append
  (equal (vl-exprlist-count (append a b))
         (+ -1 (vl-exprlist-count a)
            (vl-exprlist-count b)))
  :hints(("Goal" :in-theory (enable vl-exprlist-count append))))

(defthm vl-exprlist-count-of-rev
  (equal (vl-exprlist-count (rev x))
         (vl-exprlist-count x))
  :hints(("Goal" :in-theory (enable vl-exprlist-count rev))))


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
       (new-dim (vl-range->packeddimension
                 (make-vl-range :msb (vl-make-index (1- width))
                                :lsb (vl-make-index 0))))

       (packedp (vl-datatype-packedp seltype))
       (psel-type (if packedp
                      (vl-datatype-update-pdims
                       (cons new-dim (vl-datatype->pdims single-type))
                       single-type)
                    (vl-datatype-update-udims
                     (cons new-dim (vl-datatype->udims single-type))
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









(define vl-index-expr-typetrace
  ((x vl-expr-p
      "An index expression, i.e. a possibly-package-scoped, possibly-hierarchical
       identifier with 0 or more array selects and a possible partselect.")
   (ss vl-scopestack-p
       "Scopestack where @('x') is referenced.")
   (typeov vl-typeoverride-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (err (iff (vl-msg-p err) err)
                    "Success indicator, we fail if we can't follow the HID or
                         this isn't an appropriate expression.")
               (opinfo (implies (not err) (vl-operandinfo-p opinfo))))
  :prepwork ((local (defthm natp-abs
                      (implies (integerp x)
                               (natp (abs x)))
                      :rule-classes :type-prescription))
             (local (in-theory (disable abs))))
  (b* (((vl-index x) (vl-expr-fix x))
       (ss (vl-scopestack-fix ss))
       ((mv err hidtrace context tail) (vl-follow-scopeexpr x.scope ss))
       ((when err) (mv err nil))
       ((vl-hidstep hidstep) (car hidtrace))

       ;; Suppose x is foo.bar.baz.fum[0][1][3:2].
       ;; Suppose foo.bar is the actual vardecl, and .baz.fum are selects into it.
       ;; We want to see if foo.bar has a cached resolved type.

       ;; Compute foo.bar.
       (prefix-name (vl-scopeexpr-replace-hid
                     x.scope
                     (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))

       ((mv err type)
        (b* ((look (hons-get prefix-name (vl-typeoverride-fix typeov)))
             ((when look)
              (if (vl-datatype-resolved-p (cdr look))
                  (mv nil (cdr look))
                (mv (vmsg "Programming error: Type override was unresolved")
                    nil))))
          (case (tag hidstep.item)
            (:vl-vardecl (b* ((type1 (vl-vardecl->type hidstep.item)))
                           (vl-datatype-usertype-resolve type1 hidstep.ss :typeov typeov)))
            (:vl-paramdecl (b* (((vl-paramdecl decl) hidstep.item))
                             (vl-paramtype-case decl.type
                               :vl-explicitvalueparam
                               (if (vl-datatype-resolved-p decl.type.type)
                                   (mv nil decl.type.type)
                                 (mv (vmsg "Reference to parameter with unresolved type: ~a0"
                                           x)
                                     nil))
                               :otherwise (mv (vmsg "Bad parameter reference: ~a0" x)
                                              nil))))
            (otherwise
             (mv (vmsg "~a0: instead of a vardecl, found ~a1" x hidstep.item) nil)))))
       ((when err) (mv err nil))

       ((mv err seltrace final-type)
        (vl-datatype-resolve-selects type tail x.indices x.part))

       ((when err) (mv err nil)))

    (mv nil (make-vl-operandinfo
             :orig-expr x
             :context context
             :prefixname prefix-name
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

;; (define vl-index-expr-typetrace
;;   ((x vl-expr-p
;;       "An index expression, i.e. a possibly-package-scoped, possibly-hierarchical
;;        identifier with 0 or more array selects and a possible partselect.")
;;    (ss vl-scopestack-p
;;        "Scopestack where @('x') is referenced."))
;;   :guard (vl-expr-case x :vl-index)
;;   :returns (mv (err (iff (vl-msg-p err) err)
;;                     "Success indicator, we fail if we can't follow the HID or
;;                          this isn't an appropriate expression.")
;;                (caveat-flg)
;;                (type (implies (not err) (vl-datatype-p type))
;;                      "The type of the resulting expression after all indexing
;;                       is done.")
;;                (dims vl-packeddimensionlist-p
;;                      "Dimensions corresponding to the array indices in the expression")
;;                (type-ss vl-scopestack-p
;;                         "Scopestack relative to the type returned."))
;;   :prepwork ((local (defthm natp-abs
;;                       (implies (integerp x)
;;                                (natp (abs x)))
;;                       :rule-classes :type-prescription))
;;              (local (in-theory (disable abs))))
;;   (b* (((vl-index x) (vl-expr-fix x))
;;        (ss (vl-scopestack-fix ss))
;;        ((mv warning type sdims type-ss) (vl-scopeexpr-find-type x.scope ss))
;;        ((when warning) (mv warning nil nil nil ss))
;;        (has-partselect (vl-partselect-case x.part
;;                          :none nil
;;                          :otherwise t))
;;        ((mv err caveat-flg reduced-type idims reduced-ss)
;;         (vl-datatype-remove-dims (len x.indices) type type-ss))
;;        ((when err) (mv err nil nil nil reduced-ss))
       
;;        ((unless has-partselect)
;;         (mv nil
;;             caveat-flg
;;             reduced-type
;;             (append sdims idims)
;;             reduced-ss))

;;        ;; Take off one more dimension, and then add a dimension the width of
;;        ;; the partselect.
       
;;        ;; Caveat-flag doesn't apply because implementations seem to agree that
;;        ;; partselects are always unsigned.
;;        ((mv err ?caveat-flg single-type psdims single-ss)
;;         (vl-datatype-remove-dims 1 reduced-type reduced-ss))
;;        ((when err)
;;         (mv err nil nil nil single-ss))

;;        ((mv err width)
;;         (vl-partselect-width x.part))
;;        ((when err) (mv err nil nil nil single-ss))

;;        (new-dim (vl-range->packeddimension
;;                  (make-vl-range
;;                   :msb (vl-make-index (1- width))
;;                   :lsb (vl-make-index 0))))

;;        (dims (append sdims idims psdims))

;;        ;; The result is now width many elements of
;;        ;; type single-type.  So we add a dimension [width-1:0] back onto
;;        ;; reduced-type.  However, we need to know whether it should be an
;;        ;; unpacked or packed dimension: the way to determine this is whether
;;        ;; the last dimension selected was packed or unpacked.
;;        (packedp (vl-datatype-packedp reduced-type reduced-ss))

;;        ((when packedp)
;;         (mv nil nil
;;             (vl-datatype-update-pdims
;;              (cons new-dim (vl-datatype->pdims single-type))
;;              single-type)
;;             dims
;;             single-ss)))
;;     (mv nil nil
;;         (vl-datatype-update-udims
;;          (cons new-dim (vl-datatype->udims single-type))
;;          single-type)
;;         dims
;;         single-ss))
;;   ///
;;   (defret vl-datatype-check-usertypes-of-vl-index-expr-type
;;     (implies (not err)
;;              (not (vl-datatype-check-usertypes type type-ss))))

;;   (defret true-listp-dims-of-vl-index-expr-type
;;     (true-listp dims)
;;     :rule-classes :type-prescription)

;;   (defret len-dims-of-vl-index-expr-type
;;     (implies (not err)
;;              (equal (len dims)
;;                     (b* (((vl-index x)))
;;                       (+ (len x.indices)
;;                          (vl-partselect-case x.part :none 0 :otherwise 1)
;;                          (vl-hidexpr-index-count
;;                           (mv-nth 2 (vl-follow-scopeexpr x.scope ss))))))))

;;   (defret follow-scopeexpr-when-vl-index-expr-type
;;     (implies (not err)
;;              (b* (((vl-index x)))
;;                (not (mv-nth 0 (vl-follow-scopeexpr x.scope ss)))))))

#||

(trace$ #!vl
        (vl-index-find-type
         :entry
         (list 'vl-index-find-type (with-local-ps (vl-pp-expr x))
               ;; (if (equal (vl-pps-expr x) "popcounts[30]")
               ;;     (break$)
               ;;   nil)
               )
         :exit
         (cons 'vl-index-find-type
               (b* (((list warning type) values))
                 (list type
                       (with-local-ps
                         (if warning
                             (vl-print-warnings (list warning))
                           (vl-ps-seq (vl-pp-datatype type)
                                      (vl-print " udims: ")
                                      (vl-pp-packeddimensionlist
                                       (vl-datatype->udims type))))))))))

||#

;; (define vl-index-find-type
;;   ((x vl-expr-p "Should be a hid (perhaps just an ID), perhaps with some indexing
;;                  operators applied to it, i.e., bitselect or index operators but
;;                  not part-select operators.  So for instance: @('foo, foo.bar,
;;                  foo.bar[3], foo.bar[3][4][5]')")
;;    (ss vl-scopestack-p "Scopestack where @('x') occurs.")
;;    (ctx acl2::any-p))
;;   :returns (mv (err (iff (vl-msg-p err) err)
;;                         "Success indicator, we fail if we can't follow the HID or
;;                          this isn't an appropriate expression.")
;;                (type (implies (not warning) (vl-datatype-p type))
;;                      "The type of the resulting expression after all indexing
;;                       is done."))
;;   :prepwork ((local (in-theory (disable default-car
;;                                         vl-hidexpr-p-when-id-atom
;;                                         vl-nonatom->op-when-vl-hidindex-p))))
;;   :verify-guards nil
;;   :measure (vl-expr-count x)
;;   (b* ((x (vl-expr-fix x))
;;        ((when (or (vl-atom-p x)
;;                   (not (member (vl-nonatom->op x)
;;                                '(:vl-index :vl-bitselect)))))
;;         (b* (((unless (vl-hidexpr-p x))
;;               (mv (make-vl-warning
;;                    :type :vl-bad-index-expr
;;                    :msg "~a0: An index operator was applied to a bad subexpression, ~a1."
;;                    :args (list ctx x)
;;                    :fn __function__)
;;                   nil))
;;              ((mv warning type) (vl-hidexpr-find-type x ss ctx))
;;              ((when warning) (mv warning nil)))
;;           (mv nil type)))
;;        ((vl-nonatom x))
;;        ((mv warning sub-type) (vl-index-find-type (first x.args) ss ctx))
;;        ((when warning) (mv warning nil))
;;        (udims (vl-datatype->udims sub-type))
;;        ((when (consp udims))
;;         ;; We could check here that the index is in bounds, but maybe that
;;         ;; should more appropriately be done elsewhere.
;;         (mv nil (vl-datatype-update-udims (cdr udims) sub-type)))
;;        (pdims (vl-datatype->pdims sub-type))
;;        ((when (consp pdims))
;;         ;; An index operator applied to packed dimensions makes the datatype unsigned.
;;         (mv nil (vl-datatype-update-pdims (cdr pdims) (vl-datatype-set-unsigned sub-type))))
;;        ;; If there are no dimensions, the index has to be a bitselect; check
;;        ;; whether this is ok.
;;        ((when (vl-datatype-bitselect-ok sub-type))
;;         ;; We have a bitselect of some packed non-array type.  The result is
;;         ;; therefore an unsigned single bit.
;;         (mv nil
;;             (make-vl-coretype :name :vl-logic))))
;;     (mv (make-vl-warning :type :vl-bad-indexing-operator
;;                          :msg "~a0: Can't apply an index operator to ~a1 because ~
;;                                it has no dimensions; its type is ~a2."
;;                          :args (list ctx (first x.args) sub-type)
;;                          :fn __function__)
;;         nil))

;;   ///
;;   (verify-guards vl-index-find-type
;;     :hints(("Goal" :in-theory (e/d (acl2::member-of-cons)
;;                                    (vl-index-find-type)))))

;;   (defthm context-irrelevance-of-vl-index-find-type
;;     (implies (syntaxp (not (equal ctx ''nil)))
;;              (b* (((mv err1 type1) (vl-index-find-type x ss ctx))
;;                   ((mv err2 type2) (vl-index-find-type x ss nil)))
;;                (and (iff err1 err2)
;;                     (equal type1 type2))))))



;; (define vl-partselect-type-top-dimension-replacement ((dim vl-packeddimension-p)
;;                                                       (x vl-expr-p)
;;                                                       (ctx vl-context-p))
;;   :guard-hints ((and stable-under-simplificationp
;;                      '(:in-theory (enable acl2::member-of-cons))))
;;   :guard (and (not (vl-atom-p x))
;;               (member (vl-nonatom->op x)
;;                       '(:vl-select-colon
;;                         :vl-select-pluscolon
;;                         :vl-select-minuscolon
;;                         :vl-partselect-colon
;;                         :vl-partselect-pluscolon
;;                         :vl-partselect-minuscolon)))
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (range (implies (not warning) (vl-range-p range))))

;;   (b* (((vl-nonatom x))
;;        (x  (vl-expr-fix x))
;;        (dim (vl-packeddimension-fix dim))
;;        (ctx (vl-context-fix ctx))
;;        ((when (or (eq dim :vl-unsized-dimension)
;;                   (not (vl-range-resolved-p dim))))
;;         (mv (make-vl-warning :type :vl-partselect-type-unresolved
;;                              :msg "~a0: Couldn't find type of ~a1 because the ~
;;                                    most significant dimension of the type of ~
;;                                    ~a2 was unsized or non-constant."
;;                              :args (list ctx x (first x.args))
;;                              :fn __function__)
;;             nil))
;;        ((unless (and (vl-expr-resolved-p (third x.args))
;;                      (or (not (member x.op '(:vl-partselect-colon
;;                                              :vl-select-colon)))
;;                          (vl-expr-resolved-p (second x.args)))))
;;         (mv (make-vl-warning :type :vl-partselect-indices-unresolved
;;                              :msg "~a0: Couldn't find type of ~a1 because the ~
;;                                    partselect has non-constant indices."
;;                              :args (list ctx x)
;;                              :fn __function__)
;;             nil))
;;        ((when (member x.op '(:vl-select-colon :vl-partselect-colon)))
;;         (mv nil (make-vl-range :msb (second x.args) :lsb (third x.args))))
;;        (width (vl-resolved->val (third x.args)))
;;        ((unless (posp width))
;;         (mv (make-vl-warning :type :vl-partselect-indices-unresolved
;;                              :msg "~a0: Zero width in partselect operator?"
;;                              :args (list ctx x)
;;                              :fn __function__)
;;             nil))
;;        ((unless (vl-expr-resolved-p (second x.args)))
;;         (mv nil (make-vl-range :msb (vl-make-index (1- width)) :lsb (vl-make-index 0))))
;;        ;; The second argument is resolved, so set the range as specified.
;;        (m-or-lsb (vl-resolved->val (second x.args)))
;;        (backward-range-p (< (vl-resolved->val (vl-range->msb dim))
;;                             (vl-resolved->val (vl-range->lsb dim))))
;;        (greater-idx (if (member x.op '(:vl-select-pluscolon :vl-partselect-pluscolon))
;;                         (+ m-or-lsb width -1)
;;                       m-or-lsb))
;;        (lesser-idx (if (member x.op '(:vl-select-pluscolon :vl-partselect-pluscolon))
;;                        m-or-lsb
;;                      (+ m-or-lsb (- width) 1)))
;;        ((when (< lesser-idx 0))
;;         (mv (make-vl-warning :type :vl-partselect-index-error
;;                              :msg "~a0: Partselect ~s1 operator yields negative index: ~a2"
;;                              :args (list ctx (if (eq x.op :vl-partselect-pluscolon)
;;                                                   "+:" "-:")
;;                                          x)
;;                              :fn __function__)
;;             nil))
;;        (range (make-vl-range :msb (vl-make-index (if backward-range-p lesser-idx greater-idx))
;;                              :lsb (vl-make-index (if backward-range-p greater-idx lesser-idx)))))
;;     (mv nil range))
;;   ///
;;   (defthm context-irrelevance-of-vl-partselect-type-top-dimension-replacement
;;     (implies (syntaxp (not (equal ctx (list 'quote (with-guard-checking :none (vl-context-fix nil))))))
;;              (and (equal (mv-nth 1 (vl-partselect-type-top-dimension-replacement dim x ctx))
;;                          (mv-nth 1 (vl-partselect-type-top-dimension-replacement dim x nil)))
;;                   (iff (mv-nth 0 (vl-partselect-type-top-dimension-replacement dim x ctx))
;;                        (mv-nth 0 (vl-partselect-type-top-dimension-replacement dim x nil)))))))



;; (define vl-partselect-expr-type ((x vl-expr-p)
;;                                  (ss vl-scopestack-p)
;;                                  (ctx vl-context-p "context"))
;;   :guard (not (eq (vl-expr-kind x) :atom))
;;   :guard-hints (("goal" :in-theory (enable acl2::member-of-cons)))
;;   :returns (mv (err (iff (vl-msg-p err) err))
;;                (type (implies (not warning) (vl-datatype-p type))))
;;   :prepwork ((local (in-theory (disable default-car default-cdr
;;                                         vl-expr-resolved-p-of-car-when-vl-exprlist-resolved-p
;;                                         vl-hidexpr-p-when-id-atom
;;                                         vl-nonatom->op-when-vl-hidindex-p))))
;;   :measure (vl-expr-count x)
;;   (b* ((ctx (vl-context-fix ctx))
;;        ((vl-nonatom x) (vl-expr-fix x))
;;        ((unless (member x.op
;;                         '(:vl-select-colon
;;                           :vl-select-pluscolon
;;                           :vl-select-minuscolon
;;                           :vl-partselect-colon
;;                           :vl-partselect-pluscolon
;;                           :vl-partselect-minuscolon)))
;;         (mv (make-vl-warning :type :vl-programming-error
;;                              :msg "~a0: called vl-partselect-selfsize on non-partselect expr ~a1"
;;                              :args (list ctx x)
;;                              :fn __function__)
;;             nil))
;;        ((mv warning sub-type) (vl-index-find-type (first x.args) ss ctx))
;;        ((when warning) (mv warning nil))
;;        (udims (vl-datatype->udims sub-type))
;;        (pdims (vl-datatype->pdims sub-type))
;;        ((unless (or (consp udims) (consp pdims)))
;;         (b* (((unless (vl-datatype-bitselect-ok sub-type))
;;               (mv (make-vl-warning
;;                    :type :vl-bad-indexing-operator
;;                    :msg "~a0: Can't apply an index operator to ~a1 because it ~
;;                          has no dimensions; its type is ~a2."
;;                    :args (list ctx (first x.args) sub-type)
;;                    :fn __function__)
;;                   nil))
;;              ((mv warning size) (vl-datatype-size sub-type))
;;              ((when warning) (mv warning nil))
;;              ;; The type is some packed thing, and we have its size.  As long
;;              ;; as the partselect is in range, we'll just return a new logic
;;              ;; with the correct dimension on it.
;;              (range (make-vl-range :msb (vl-make-index (1- size))
;;                                    :lsb (vl-make-index 0)))
;;              ((mv warning new-dim1)
;;               (vl-partselect-type-top-dimension-replacement range x ctx))
;;              ((when warning) (mv warning nil))
;;              (new-type (make-vl-coretype :name :vl-logic
;;                                          :pdims (list new-dim1))))
;;           (mv nil new-type)))
;;        (dim1 (if (consp udims) (car udims) (car pdims)))
;;        ((mv warning new-dim1)
;;         (vl-partselect-type-top-dimension-replacement dim1 x ctx))
;;        ((when warning) (mv warning nil))
;;        (new-type (vl-datatype-update-dims
;;                   (if (consp udims) pdims (cons new-dim1 (cdr pdims)))
;;                   (and (consp udims) (cons new-dim1 (cdr udims)))
;;                   sub-type))
;;        ;; packed types become unsigned
;;        (new-type (if (consp udims) new-type (vl-datatype-set-unsigned new-type))))
;;     (mv nil new-type))
;;   ///
;;   (defthm context-irrelevance-of-vl-partselect-expr-type
;;     (implies (syntaxp (not (equal ctx (list 'quote (with-guard-checking :none (vl-context-fix nil))))))
;;              (and (equal (mv-nth 1 (vl-partselect-expr-type x ss ctx))
;;                          (mv-nth 1 (vl-partselect-expr-type x ss nil)))
;;                   (iff (mv-nth 0 (vl-partselect-expr-type x ss ctx))
;;                        (mv-nth 0 (vl-partselect-expr-type x ss nil)))))))












;; 99% sure this is deprecated

;; (define vl-hid-range
;;   :short "Try to look up a range for a HID, which may have been installed by
;; @(see vl-expr-follow-hids)."
;;  ((x vl-expr-p  "This should generally be the top-level HID expression."))
;;  :guard (not (vl-atom-p x))
;;  :returns (mv (successp booleanp :rule-classes :type-prescription)
;;               (range vl-maybe-range-p
;;                      :hints(("Goal" :in-theory (disable (force))))))
;;   (b* ((atts (vl-nonatom->atts x))
;;        ((unless (assoc-equal "VL_HID_RESOLVED_RANGE_P" atts))
;;         (mv nil nil))
;;        (left  (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_LEFT" atts)))
;;        (right (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_RIGHT" atts)))
;;        ((when (and (not left) (not right)))
;;         ;; It's resolved, there's just no range.
;;         (mv t nil))
;;        ((unless (and left right))
;;         ;; Maybe this should be a programming error?
;;         (mv nil nil))
;;        ;; Dumb hackery for unconditional return theorem
;;        (left (mbe :logic (if (vl-expr-p left)
;;                              left
;;                            (vl-make-index 0))
;;                   :exec left))
;;        (right (mbe :logic (if (vl-expr-p right)
;;                               right
;;                             (vl-make-index 0))
;;                    :exec right))
;;        (range (make-vl-range :msb left :lsb right)))
;;     (mv t range))
;;   ///
;;   (defthm vl-hid-range-of-copy-atts
;;     (equal (vl-hid-range (vl-nonatom op (vl-nonatom->atts x) args fw ft))
;;            (vl-hid-range x))))

;; (define vl-hid-rangeatts
;;   :short "Extend the attributes for a HID with range information."
;;   ;; BOZO we should probably be using this in vl-expr-follow-hids.
;;   ((range vl-maybe-range-p)
;;    (atts vl-atts-p "the rest of the atts"))
;;   :guard (vl-maybe-range-resolved-p range)
;;   :returns (new-atts vl-atts-p)
;;   (b* ((atts (vl-atts-fix atts))
;;        (atts (if range
;;                  (list* (cons "VL_HID_RESOLVED_RANGE_LEFT" (vl-range->msb range))
;;                         (cons "VL_HID_RESOLVED_RANGE_RIGHT" (vl-range->lsb range))
;;                         atts)
;;                (list* (cons "VL_HID_RESOLVED_RANGE_LEFT" nil)
;;                       (cons "VL_HID_RESOLVED_RANGE_RIGHT" nil)
;;                       atts))))
;;     (cons (list "VL_HID_RESOLVED_RANGE_P") atts))
;;   ///
;;   (defthm vl-hid-range-of-vl-hid-rangeatts
;;     (implies range
;;              (equal (vl-hid-range (vl-nonatom op (vl-hid-rangeatts range atts) args fw ft))
;;                     (mv t (vl-range-fix range))))
;;     :hints(("Goal" :in-theory (e/d (vl-hid-range))))))

;; (define vl-hid-width
;;   :short "Try to return the width of a HID, using range attribute information
;; that may have been installed by @(see vl-expr-follow-hids)."
;;   ((x vl-expr-p))
;;   :guard (not (vl-atom-p x))
;;   :enabled t
;;   :guard-hints (("goal" :in-theory (enable vl-hid-range
;;                                            vl-maybe-range-resolved-p
;;                                            vl-maybe-range-size
;;                                            vl-range-resolved-p
;;                                            vl-range-size
;;                                            vl-width-from-difference
;;                                            )))
;;   :returns (width maybe-posp :rule-classes :type-prescription)
;;   (mbe :logic (b* (((mv ok range) (vl-hid-range x)))
;;                 (and ok
;;                      (vl-maybe-range-resolved-p range)
;;                      (vl-maybe-range-size range)))
;;        :exec
;;        (b* ((atts (vl-nonatom->atts x))
;;             ((unless (assoc-equal "VL_HID_RESOLVED_RANGE_P" atts))
;;              nil)
;;             (left (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_LEFT" atts)))
;;             (right (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_RIGHT" atts)))
;;             ((unless (or (and (not left) (not right))
;;                          (and left (vl-expr-resolved-p left)
;;                               right (vl-expr-resolved-p right))))
;;              nil))
;;          (if left
;;              (vl-width-from-difference
;;               (- (vl-resolved->val left) (vl-resolved->val right)))
;;            1))))






(define vl-hidindex-resolved-p ((x vl-hidindex-p))
  :returns (bool)
  :short "Determines if every index in a @(see vl-hidindex-p) is resolved."
  :measure (vl-expr-count x)
  (vl-exprlist-resolved-p (vl-hidindex->indices x))
  ;; (b* (((when (vl-atom-p x))
  ;;       t)
  ;;      ((vl-nonatom x) x))
  ;;   (and (mbt (eq x.op :vl-index))
  ;;        (vl-hidindex-resolved-p (first x.args))
  ;;        (vl-expr-resolved-p (second x.args))))
  ///
  ;; (defthm vl-hidindex-resolved-p-when-atom
  ;;   (implies (vl-atom-p x)
  ;;            (vl-hidindex-resolved-p x)))

  (deffixequiv vl-hidindex-resolved-p)

  ;; (defthm vl-hidindex-resolved-p-of-make-vl-nonatom
  ;;   (implies (and (force (vl-hidindex-resolved-p (first args)))
  ;;                 (force (vl-expr-resolved-p (second args))))
  ;;            (vl-hidindex-resolved-p (make-vl-nonatom :op :vl-index
  ;;                                                     :args args
  ;;                                                     :atts atts
  ;;                                                     :finalwidth finalwidth
  ;;                                                     :finaltype finaltype)))
  ;;   :hints(("Goal"
  ;;           :in-theory (e/d (vl-arity-fix) ((force)))
  ;;           :expand ((:free (atts args finalwidth finaltype)
  ;;                     (vl-hidindex-resolved-p (make-vl-nonatom :op :vl-index
  ;;                                                              :args args
  ;;                                                              :atts atts
  ;;                                                              :finalwidth finalwidth
  ;;                                                              :finaltype finaltype)))))))

  ;; (defthmd vl-nonatom->op-when-hidindex-resolved-p
  ;;   (implies (and (vl-hidindex-resolved-p x)
  ;;                 (force (not (vl-atom-p x))))
  ;;            (equal (vl-nonatom->op x) :vl-index)))

  ;; (defthm vl-hidindex-resolved-p-of-arg1-when-vl-hidindex-resolved-p
  ;;   (implies (and (vl-hidindex-resolved-p x)
  ;;                 (force (not (vl-atom-p x))))
  ;;            (vl-hidindex-resolved-p (first (vl-nonatom->args x)))))

  ;; (defthm vl-expr-resolved-p-of-arg2-when-vl-hidindex-resolved-p
  ;;   (implies (and (vl-hidindex-resolved-p x)
  ;;                 (force (not (vl-atom-p x))))
  ;;            (vl-expr-resolved-p (second (vl-nonatom->args x)))))
  )


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
                  (vl-hidexpr-resolved-p (vl-hidexpr-dot->rest x)))))

  ;; (defthm vl-hidexpr-resolved-p-when-atom
  ;;   (implies (vl-atom-p x)
  ;;            (vl-hidexpr-resolved-p x)))

  ;; (defthm vl-hidindex-resolved-p-of-arg1-when-vl-hidexpr-resolved-p
  ;;   (implies (and (vl-hidexpr-resolved-p x)
  ;;                 (force (not (vl-atom-p x))))
  ;;            (vl-hidindex-resolved-p (first (vl-nonatom->args x)))))

  ;; (defthm vl-hidexpr-resolved-p-of-arg2-when-vl-hidexpr-resolved-p
  ;;   (implies (and (vl-hidexpr-resolved-p x)
  ;;                 (force (not (vl-atom-p x))))
  ;;            (vl-hidexpr-resolved-p (second (vl-nonatom->args x)))))

  ;; (defthm vl-hidexpr-resolved-p-of-make-vl-nonatom-for-dot
  ;;   (implies (and (force (vl-hidindex-resolved-p (first args)))
  ;;                 (force (vl-hidexpr-resolved-p (second args))))
  ;;            (vl-hidexpr-resolved-p (make-vl-nonatom :op :vl-hid-dot
  ;;                                                    :args args
  ;;                                                    :atts atts
  ;;                                                    :finalwidth finalwidth
  ;;                                                    :finaltype finaltype)))
  ;;   :hints(("Goal"
  ;;           :expand (:free (atts args finalwidth finaltype)
  ;;                     (vl-hidexpr-resolved-p (make-vl-nonatom :op :vl-hid-dot
  ;;                                                             :args args
  ;;                                                             :atts atts
  ;;                                                             :finalwidth finalwidth
  ;;                                                             :finaltype finaltype)))
  ;;           :in-theory (e/d (vl-arity-fix) ((force))))))
  )

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
       (acc (revappend (str::natchars (vl-resolved->val (car indices))) acc))
       (acc (cons #\] acc)))
    (vl-flatten-hidindex-aux (cdr indices) acc)))

(define vl-flatten-hidindex ((x vl-hidindex-p))
  :guard (vl-hidindex-resolved-p x)
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a @(see vl-hidindex-p) into a string like @('\"bar[3][4][5]\"')."
  :measure (vl-expr-count x)
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

;; (define vl-explode-hidindex
;;   :short "Explode a (resolved) @(see vl-hidindex-p) into a flat list of
;;           its components."
;;   ((x vl-expr-p "The hidindex to explode, e.g., @('foo[3][4][5]')"))
;;   :guard (and (vl-hidindex-p x)
;;               (vl-hidindex-resolved-p x))
;;   :returns (pieces true-listp :rule-classes :type-prescription
;;                    "A flat, mixed list of strings and numbers, e.g.,
;;                    @('(\"foo\" 3 4 5)').")
;;   :measure (vl-expr-count x)
;;   (b* (((when (vl-atom-p x))
;;         (list (vl-hidname->name x)))
;;        ((vl-nonatom x) x)
;;        (from (vl-explode-hidindex (first x.args)))
;;        (idx  (vl-resolved->val (second x.args))))
;;     (append from (list idx))))

;; (define vl-explode-hid
;;   :short "Explode a (resolved) @(see vl-hidexpr-p) into a flat list of its
;;           components."
;;   ((x vl-expr-p "The hidexpr to explode, e.g., foo.bar[2][3].baz."))
;;   :guard (and (vl-hidexpr-p x)
;;               (vl-hidexpr-resolved-p x))
;;   :returns
;;   (pieces true-listp :rule-classes :type-prescription
;;           "A flat, mixed list of strings and numbers, e.g.,
;;            @('(\"foo\" \"bar\" 2 3 \"baz\")').")
;;   :measure (vl-expr-count x)
;;   (b* (((when (vl-atom-p x))
;;         (list (vl-hidname->name x)))
;;        ((vl-nonatom x) x))
;;     (append (vl-explode-hidindex (first x.args))
;;             (vl-explode-hid (second x.args)))))
