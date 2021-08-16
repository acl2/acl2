; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
(include-book "datatype-tools")
(include-book "expr-tools")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
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

(defxdoc hid-tools
  :parents (mlib)
  :short "Functions for recognizing and following well-formed hierarchical
identifiers, scoped identifiers, and indexing expressions."

  :long "<h3>VL Terminology</h3>

<p>SystemVerilog provides a very rich syntax for referring to objects in
different scopes and throughout the module hierarchy.  To deal with this rich
syntax, we will need a bit of jargon.  These terms are well-defined notions in
VL, but may not necessarily be found or used in the same way in the
Verilog/SystemVerilog standards.</p>

<p><u>Identifiers.</u> We say the following expressions are just
<b>identifiers</b>.  Note that the Verilog/SystemVerilog standards sometimes
distinguish between plain and escaped identifiers.  While our @(see lexer)
needs to understand these as different notions, internally there is no
difference.</p>

@({
    foo
    \\foo$bar
})

<p>Note that any indexing/selection operations after an identifier is
<b>not</b> part of the identifier.  For instance, @('foo[3]') and @('foo[3:0]')
are not identifiers: they are index/selection operations applied to the
identifier @('foo').  (This may seem obvious, but we draw your attention to it
because it is less obvious for hierarchical identifiers.)</p>

<p><u>Hierarchical identifiers</u>.  Identifiers can be chained together,
perhaps with indexing, to form <b>hierarchical identifiers</b>.  Here are
examples of hierarchical identifiers:</p>

@({
    foo                     // any ID is a HID
    \\foo$bar

    foo.bar                 // fancier HIDs
    foo.bar.baz

    foo.bar[3].baz          // Verilog-2005 or SystemVerilog-2012
    foo.bar[3][4].baz       // SystemVerilog-2012
})

<p>Hierarchical identifiers may have internal indexing expressions.  However,
any subsequent indexing/selection operations are <b>not</b> part of the HID
itself.  For instance, we say that @('foo.bar[3].baz[2]') and
@('foo.bar[3].baz[3:0]') are <b>not</b> a hierarchical identifiers.  Instead,
these are indexing/selection operators applied to a HID.</p>

<p><u>Scope expressions</u>.  Hierarchical identifiers can be prefixed with
scoping operations, e.g., for packages.  Here are some examples of scope
expressions:</p>

@({
     foo                             // any ID is a scope expression
     \\foo$bar

     foo.bar                         // any HID is a scope expression
     foo.bar.baz
     foo.bar[3].baz
     foo.bar[3][4].baz

     mypkg::foo                      // fancier scope expressions
     mypkg::foo.bar
     $unit::foo::bar.baz[3].beep
})

<p>As with ordinary identifiers and hierarchical identifiers, scope expressions
do <b>not</b> have any indexing/selection operators.  For example,
@('mypkg::foo[3]') is not a scope expression, but is instead an indexing
operator applied to the scope expression @('mypkg::foo').</p>

<p><u>Index expressions</u>.  Scope expressions can be indexed into by some
number of individual bit/array-indexing operations.  Here are some examples of
index expressions:</p>

@({
     foo                             // any ID is an index expression
     \\foo$bar

     foo.bar                         // any HID is an index expression
     foo.bar.baz
     foo.bar[3].baz
     foo.bar[3][4].baz

     mypkg::foo                      // any scope expression is an index expression
     mypkg::foo.bar
     $unit::foo::bar.baz[3].beep

     foo[3]                          // fancier index expressions
     foo[3][4][5]
     foo.bar[3]
     mypkg::foo[3][4][5]
     $unit::foo::bar.baz[3].beep[2][1][0]
})

<p>Note that an index expression does <b>not</b> have any part/range selects in
it.  That is, an expression like @('foo[3][5:0]') is not an index expression;
instead it is a part-selection operator applied to the index expression
@('foo[3]').</p>

<p>Note that part/range selection operations, like @('foo[3:0]'), are just an
ordinary operator and we do not give them any special designation.  Why, then,
do we give special treatment to indexing?  In short, part-selection is simpler
than indexing because there can be at most a single part-select.  In contrast,
there can be many levels of array indexing, and so typically indexing needs to
be handled recursively.</p>

<h3>Low Level Representation</h3>

<p>VL internally represents hierarchical identifiers as compound @(see
vl-expr-p) objects.  To understand the structure, consider a very complex index
expression such as:</p>

@({
     ape::bat::cat.dog[3][2][1].elf[7][6][5]
})

<p>We expect to represent this sort of expression by nesting operations as
suggested by the parentheses below.  This arrangement matches the jargon
above.</p>

@({
    Indexing is the outermost operation:

      (((  ape::bat::cat.dog[3][2][1].elf     )[7] )[6] )[5]
           ------------------------------   -------------------
                    a scopexpr              recursive indexing


    Followed by scoping:

                 ape::(bat::         (cat.dog[3][2][1].elf)  )
           ---------------------      --------------------
             recursive scoping              a hidexpr


    Followed by hierarchy:

                         cat . ((dog [3][2][1]) . elf)
                               -----------------------
                                    sub hidexpr

    With hierarchical indexing going from outermost to innermost:

                               ((dog [3])[2])[1]
                               -----------------
                                  a hidindex
})

<p>Where each @('.') is represented by a @(':vl-hid-dot') operator, each
@('[]') by a @(':vl-index') operator, each @('::') by a @(':vl-scope')
operator, and the names are represented as @(see vl-hidpiece-p) atoms.</p>

<h3>Abstract Representation</h3>

<p>The low-level @(see vl-expr-p) representation is not very strongly typed and
permits nonsensical expressions like @('foo.5.bar.(1+2)'), which should never
be produced by our parser or by well-behaving internal VL code.  Because of
this, most functions for working with HIDs should not and do not use the
internal representation directly.</p>

<p>Instead, in @(see abstract-hids), we set up wrapper functions that provide
an interface for working with hierarchical identifier expressions at a somewhat
higher level.  These wrapper functions include stronger recognizers that ensure
that an expression is a well-formed hierarchical identifier, scope expression,
or index expression that meets our usual expectations.  It also provides
convenient accessor functions for traversing well-formed expressions.</p>

<h3>Following HIDs</h3>

<p>For many kinds of transformation and analysis, the fundamental operation on
hierarchical, scoped, or indexed expressions is to follow them to what they
refer to.  To do this correctly requires an detailed understanding of both the
concepts above and also @(see scopestack)s for looking up identifiers.</p>

<p>Due to this complexity, most code throughout VL should never try to follow
hierarchical identifiers on its own.  Instead, most code should be make use of
the high-level functions described in @(see following-hids).</p>")



(defsection abstract-hids
  :parents (hid-tools)
  :short "Recognizers for certain kinds of HID expressions."

  :long "<p>We now develop wrapper functionality that allows us to treat
hierarchical, scope, and index expressions in a sensible way.  Note that these
are technical terms with precise meanings; see @(see hid-tools) for
background.</p>

<p>Quick guide, working bottom up:</p>

<dl>

<dt>@(see vl-hidname-p)</dt>
<dd>A single ID or HIDPIECE atom without any indices or dots.</dd>
<dd>Examples: @('bar'), @('\\foo$bar')</dd>
<dd>@(see vl-hidname->name) gets the name as a string.</dd>

<dt>@(see vl-hidindex-p)</dt>
<dd>A single ID with perhaps some indices.</dd>
<dd>Examples: @('bar'), @('bar[1]'), @('bar[3][5]').</dd>
<dd>@(see vl-hidindex->name) gets the name as a string.</dd>
<dd>@(see vl-hidindex->indices) gets the indices as an expression list.</dd>

<dt>@(see vl-hidexpr-p)</dt>
<dd>A full HID with dots and interior indices, but no \"external\" indices.</dd>
<dd>Examples: @('foo'), @('foo.bar'), @('foo[3].bar')</dd>
<dd>@(see vl-hidexpr->endp) says whether there's a dot.</dd>
<dd>@(see vl-hidexpr->first) gets the first hidindex, e.g., @('foo[3]') for
@('foo[3].bar').  In the @('endp') case this is just the whole expression.</dd>
<dd>@(see vl-hidexpr->rest) gets the rest.  Can't be used in the endp case.</dd>

<dt>@(see vl-scopename-p)</dt>
<dd>Name of a scope.  For instance, @(':vl-local'), @(':vl-$unit'), or a string.</dd>

<dt>@(see vl-scopeexpr-p)</dt>
<dd>Extends hidexprs with scope operators.</dd>
<dd>Example: @('ape::bat::cat.dog[3].elf')</dd>
<dd>@(see vl-scopeexpr->scopes) lists the scope names, e.g., @('ape'), @('bat').</dd>
<dd>@(see vl-scopeexpr->hid) gets the hidexpr, i.e., @('cat.dog[3].elf')</dd>

<dt>@(see vl-indexexpr-p)</dt>
<dd>Extends scopeexprs with indexing operators.</dd>
<dd>Example: @('foo::bar.baz[3][4][5]')</dd>
<dd>@(see vl-indexexpr->scopeexpr) gets the scope expression.</dd>
<dd>@(see vl-indexexpr->indices) gets the indices as an expression list.</dd>

</dl>

<p>Note that none of these functions places any restrictions on the expressions
that can occur in index positions.  That is, expressions like
@('foo[width-1].bar') are perfectly acceptable.</p>")

;; Compatibility wrappers for old function names.  BOZO eventually remove these.
(defmacro vl-hidexpr-dot-p (x) `(not (vl-hidexpr->endp ,x)))
(defmacro vl-hidexpr-first-index (x) `(vl-hidexpr->first ,x))
(defmacro vl-hidexpr-rest (x) `(vl-hidexpr->rest ,x))

(local (xdoc::set-default-parents abstract-hids))

(def-ruleset! vl-hid-legacy-thms nil)

(defmacro defthm-hid-legacy (name &rest args)
  ;; BOZO there are lots of theorems that shouldn't really need to be around if
  ;; we're using the abstraction correctly.  I mark these with
  ;; defthm-hid-legacy so we can disable them and try to stop using them
  ;; eventually.
  `(progn (defthmd ,name . ,args)
          (add-to-ruleset vl-hid-legacy-thms '(,name))))

(define vl-hidname-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes simple name expression: either a hidpiece or an id."
  (and (vl-atom-p x)
       (b* (((vl-atom x) x))
         (or (vl-fast-hidpiece-p x.guts)
             (vl-fast-id-p x.guts))))
  ///
  (defthm vl-hidname-p-when-vl-idexpr-p
    ;; Even though this sort of breaks the abstraction, I think it's pretty
    ;; reasonable until/unless we want to add an explicit HIDNAME constructor.
    (implies (vl-idexpr-p x)
             (vl-hidname-p x))
    :hints(("Goal" :in-theory (enable vl-idexpr-p))))

  (defthm vl-hidname-p-when-vl-atom
    ;; Even though this sort of breaks the abstraction, I think it's pretty
    ;; reasonable until/unless we want to add an explicit HIDNAME constructor.
    (implies (and (vl-atom-p x)
                  (or (vl-hidpiece-p (vl-atom->guts x))
                      (vl-id-p (vl-atom->guts x))))
             (vl-hidname-p x))))

(define vl-hidname->name ((x vl-expr-p))
  :guard (vl-hidname-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :short "Get the name from a @(see vl-hidname-p) as a string."
  :prepwork ((local (in-theory (enable vl-hidname-p))))
  :inline t
  :guard-hints(("Goal" :in-theory (enable vl-id-p
                                          vl-hidpiece-p
                                          vl-id->name
                                          vl-hidpiece->name)))
  (b* (((vl-atom x)))
    ;; The use of MBE here is completely minor.  If we change the
    ;; vl-id/vl-hidpiece representation it'll have to go away.  For now it
    ;; gives us a really nice executable definition.
    (mbe :logic
         (if (vl-fast-hidpiece-p x.guts)
             (vl-hidpiece->name x.guts)
           (vl-id->name x.guts))
         :exec
         (cdr x.guts))))


(define vl-hidindex-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed index expressions into hierarchical identifier
pieces, e.g., the @('bar[3][4][5]') part of @('foo.bar[3][4][5].baz')."
  :measure (vl-expr-count x)
  (b* (((when (vl-atom-p x))
        (vl-hidname-p x))
       ((vl-nonatom x) x))
    (and (vl-op-equiv x.op :vl-index)
         (vl-hidindex-p (first x.args))))
  ///
  (defthm-hid-legacy vl-hidname-p-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (vl-atom-p x))
             (vl-hidname-p x)))

  (defthm-hid-legacy vl-nonatom->op-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-nonatom->op x) :vl-index))
    :rule-classes ((:rewrite) (:forward-chaining)))

  (defthm-hid-legacy arity-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-op-arity (vl-nonatom->op x)) 2)))

  (defthm-hid-legacy len-of-vl-nonatom->args-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (and ;; blah, so gross....
              (equal (len (vl-nonatom->args x)) 2)
              (consp (vl-nonatom->args x))
              (consp (cdr (vl-nonatom->args x))))))

  (deffixequiv vl-hidindex-p)

  (defthm vl-hidindex-p-of-make-vl-atom
    ;; This is probably fine unless/until we want to add a HIDINDEX
    ;; constructor.
    (equal (vl-hidindex-p (make-vl-atom :guts guts
                                        :finalwidth finalwidth
                                        :finaltype finaltype))
           (or (vl-hidpiece-p (vl-atomguts-fix guts))
               (vl-id-p (vl-atomguts-fix guts))))
    :hints(("Goal" :in-theory (enable vl-hidname-p))))

  (defthm vl-hidindex-p-of-make-vl-nonatom
    ;; This is probably fine unless/until we want to add a HIDINDEX
    ;; constructor.
    (implies (force (vl-hidindex-p (first args)))
             (vl-hidindex-p (make-vl-nonatom :op :vl-index
                                             :args args
                                             :atts atts
                                             :finalwidth finalwidth
                                             :finaltype finaltype)))
    :hints(("Goal"
            :in-theory (enable vl-arity-fix)
            :expand ((:free (atts args finalwidth finaltype)
                      (vl-hidindex-p
                       (make-vl-nonatom :op :vl-index
                                        :args args
                                        :atts atts
                                        :finalwidth finalwidth
                                        :finaltype finaltype)))))))

  (defthm not-vl-hidindex-p-by-op
    (implies (and (not (eq (vl-nonatom->op x) :vl-index))
                  (force (not (vl-atom-p x))))
             (not (vl-hidindex-p x)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm-hid-legacy vl-hidindex-p-of-first-of-vl-nonatom->args-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-p (first (vl-nonatom->args x))))))

;; (local (in-theory (enable vl-nonatom->op-when-vl-hidindex-p)))

(define vl-hidindex->name ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :short "For instance, @('bar[3][4][5]') &rarr; @('bar')."
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-hidindex-p))))
  (b* (((when (vl-atom-p x))
        (vl-hidname->name x))
       ((vl-nonatom x) x))
    (vl-hidindex->name (first x.args))))

(define vl-hidindex->indices-exec ((x   vl-expr-p)
                                   (acc vl-exprlist-p))
  :guard (vl-hidindex-p x)
  :returns (indices vl-exprlist-p)
  :parents (vl-hidindex->indices)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-hidindex-p))))
  (b* ((acc (vl-exprlist-fix acc))
       ((when (vl-atom-p x))
        acc)
       ((vl-nonatom x) x))
    (vl-hidindex->indices-exec (first x.args)
                               (cons (vl-expr-fix (second x.args))
                                     acc))))

(define vl-hidindex->indices ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (indices vl-exprlist-p)
  :short "For instance, @('bar[3][4][5]') &rarr; @('(3 4 5)')."
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-hidindex-p))))
  :inline t
  :verify-guards nil
  (mbe :logic
       (b* (((when (vl-atom-p x))
             nil)
            ((vl-nonatom x) x))
         (append (vl-hidindex->indices (first x.args))
                 (list (vl-expr-fix (second x.args)))))
       :exec
       (vl-hidindex->indices-exec x nil))
  ///
  (local (defthm vl-hidindex->indices-exec-removal
           (implies (vl-hidindex-p x)
                    (equal (vl-hidindex->indices-exec x acc)
                           (append (vl-hidindex->indices x)
                                   (vl-exprlist-fix acc))))
           :hints(("Goal" :in-theory (enable vl-hidindex->indices-exec)))))

  (verify-guards vl-hidindex->indices$inline)

  (defthm vl-hidindex->indices-when-vl-atom-p
    (implies (vl-atom-p x)
             (equal (vl-hidindex->indices x)
                    nil)))

  (local (defthm l0
           (equal (vl-exprlist-count (append x y))
                  (+ -1
                     (vl-exprlist-count x)
                     (vl-exprlist-count y)))
           :hints(("Goal" :in-theory (enable append vl-exprlist-count)))))

  (defthm vl-exprlist-count-of-vl-hidindex->indices-weak
    (implies (vl-hidindex-p x)
             (<= (vl-exprlist-count (vl-hidindex->indices x))
                 (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :induct (vl-hidindex-p x)
            :in-theory (enable vl-hidindex->indices vl-hidindex-p vl-exprlist-count))))

  (defthm vl-exprlist-count-of-vl-hidindex->indices-strong
    (implies (and (vl-hidindex-p x)
                  (not (vl-atom-p x)))
             (< (vl-exprlist-count (vl-hidindex->indices x))
                (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :induct (vl-hidindex-p x)
            :in-theory (enable vl-hidindex->indices vl-hidindex-p vl-exprlist-count)))))

(define vl-hidindex-count-indices ((x vl-expr-p))
  :guard (vl-hidindex-p x)
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (vl-expr-count x)
  :returns (idxcount natp :rule-classes :type-prescription)
  :verify-guards nil
  :enabled t
  :prepwork ((local (in-theory (enable vl-hidindex-p))))
  (mbe :logic
       (len (vl-hidindex->indices x))
       :exec
       (if (vl-atom-p x)
           0
         (+ 1 (vl-hidindex-count-indices (first (vl-nonatom->args x))))))
  ///
  (verify-guards vl-hidindex-count-indices
    :hints(("Goal" :in-theory (enable vl-hidindex->indices-exec
                                      vl-hidindex->indices)))))

(local
 (defsection hidindex-sanity-checks

   (defconst *bar345*
     (b* ((bar (vl-idexpr "bar" nil nil))
          (bar3 (make-vl-nonatom :op :vl-index
                                 :args (list bar (vl-make-index 3))))
          (bar34 (make-vl-nonatom :op :vl-index
                                  :args (list bar3 (vl-make-index 4))))
          (bar345 (make-vl-nonatom :op :vl-index
                                   :args (list bar34 (vl-make-index 5)))))
       bar345))

   (assert! (vl-hidindex-p *bar345*))
   (assert! (equal (vl-hidindex->name *bar345*) "bar"))
   (assert! (equal (vl-hidindex->indices *bar345*)
                   (list (vl-make-index 3)
                         (vl-make-index 4)
                         (vl-make-index 5))))))

(define vl-hidexpr-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed hierarchical identifier expressions."
  :measure (vl-expr-count x)
  :long "<p>Examples:</p>

@({
     foo
     foo.bar
     foo[1].bar
     foo[1][2][3].bar.baz
})

<p>Note that a @('hidexpr') does <i>not</i> allow for subsequent indexing.  For
instance:</p>

@({
      foo.bar[3]   <--- not a HIDEXPR.

    Instead, this is a :vl-index or :vl-bitselect operator with:

         arg1 == foo.bar   (a hid)
         arg2 == 3
})"
  (b* (((when (vl-atom-p x))
        (vl-hidname-p x))
       ((vl-nonatom x) x))
    (and (vl-op-equiv x.op :vl-hid-dot)
         (vl-hidindex-p (first x.args))
         (vl-hidexpr-p (second x.args))))
  ///
  (deffixequiv vl-hidexpr-p)

  (defthm vl-hidpiece-p-of-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (vl-atom-p x))
             (vl-hidname-p x)))

  (defthm vl-nonatom->op-when-vl-hidexpr-p-forward
    (implies (and (vl-hidexpr-p x)
                  (not (vl-atom-p x)))
             (equal (vl-nonatom->op x) :vl-hid-dot))
    :rule-classes :forward-chaining)

  (defthm not-vl-hidexpr-p-by-op
    (implies (and (not (eq (vl-nonatom->op x) :vl-hid-dot))
                  (force (not (vl-atom-p x))))
             (not (vl-hidexpr-p x))))

  (defthm-hid-legacy vl-op-arity-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-op-arity (vl-nonatom->op x))
                    2))
    :hints(("Goal"
            :cases ((equal (vl-nonatom->op x) :vl-hid-dot)
                    (equal (vl-nonatom->op x) :vl-index)))))

  (defthm-hid-legacy len-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x)))
                  (force (vl-expr-p x)))
             (and ;; blah, so gross....
              (equal (len (vl-nonatom->args x)) 2)
              (consp (vl-nonatom->args x))
              (consp (cdr (vl-nonatom->args x))))))

  (defthm-hid-legacy vl-hidindex-p-of-first-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-p (first (vl-nonatom->args x)))))

  (defthm-hid-legacy vl-hidexpr-p-of-second-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidexpr-p (second (vl-nonatom->args x)))))

  (defthm vl-hidexpr-p-of-vl-atom
    (equal (vl-hidexpr-p (make-vl-atom :guts guts
                                       :finalwidth finalwidth
                                       :finaltype finaltype))
           (let ((guts (vl-atomguts-fix guts)))
             (or (vl-hidpiece-p guts)
                 (vl-id-p guts))))
    :hints(("goal" :in-theory (enable vl-hidname-p))))

  (defthm vl-hidexpr-p-of-vl-nonatom-dot
    (implies (and (equal op :vl-hid-dot)
                  (force (vl-hidindex-p (first args)))
                  (force (vl-hidexpr-p (second args))))
             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype)))
    :hints(("Goal"
            :in-theory (enable vl-arity-fix)
            :expand ((:free (args atts finalwidth finaltype)
                      (vl-hidexpr-p
                       (make-vl-nonatom :op :vl-hid-dot
                                        :args args
                                        :atts atts
                                        :finalwidth finalwidth
                                        :finaltype finaltype)))))))

  (defthm vl-hidexpr-p-when-id-atom
    (implies (and (equal (vl-expr-kind x) :atom)
                  (vl-id-p (vl-atom->guts x)))
             (vl-hidexpr-p x))))

(define vl-hidexpr->endp ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (endp booleanp :rule-classes :type-prescription)
  :inline t
  (vl-atom-p x)
  ///
  (defthm vl-hidname-p-when-vl-hidexpr->endp
    (implies (and (vl-hidexpr->endp x)
                  (vl-hidexpr-p x))
             (vl-hidname-p x))
    :rule-classes ((:rewrite :backchain-limit-lst 1)
                   (:forward-chaining :trigger-terms ((vl-hidexpr->endp x))))))

(define vl-hidexpr->first
  :short "Get the leftmost @(see vl-hidindex-p) in a hid expression."
  ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (first (and (vl-expr-p first)
                       (implies (vl-hidexpr-p x)
                                (vl-hidindex-p first)))
                  :hints(("Goal"
                          :in-theory (enable vl-hidindex-p)
                          :expand ((vl-hidexpr-p x)))))
  :long "<p>Examples:</p>
@({
     foo           --> foo
     foo.bar       --> foo
     foo[3].bar    --> foo[3]
     foo[3][4].bar --> foo[3][4]
})"
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  (if (and (not (vl-atom-p x))
           (eq (vl-nonatom->op x) :vl-hid-dot))
      (first (vl-nonatom->args x))
    (vl-expr-fix x)))

(define vl-hidexpr->rest ((x vl-expr-p))
  :guard (and (vl-hidexpr-p x)
              (not (vl-hidexpr->endp x)))
  :returns (rest (and (vl-expr-p rest)
                      (implies (and (vl-hidexpr-p x)
                                    (not (vl-hidexpr->endp x)))
                               (vl-hidexpr-p rest))))
  :prepwork ((local (in-theory (enable vl-hidexpr-p
                                       vl-hidexpr->endp))))
  (vl-expr-fix (second (vl-nonatom->args x)))
  ///
  (defthm vl-expr-count-of-vl-hidexpr->rest
    (implies (not (vl-hidexpr->endp x))
             (< (vl-expr-count (vl-hidexpr->rest x))
                (vl-expr-count x)))
    :rule-classes :linear)

  (defthm vl-expr-count-of-vl-hidexpr-pieces
    (implies (and (vl-hidexpr-p x)
                  (not (vl-hidexpr->endp x)))
             (< (+ (vl-expr-count (vl-hidexpr->first x))
                   (vl-expr-count (vl-hidexpr->rest x)))
                (vl-expr-count x)))
    :rule-classes :linear
    :hints(("Goal"
            :expand ((vl-expr-count x)
                     (vl-exprlist-count (vl-nonatom->args x))
                     (vl-exprlist-count (cdr (vl-nonatom->args x))))
            :in-theory (enable vl-hidexpr-p
                               vl-hidexpr->endp
                               vl-hidexpr->first
                               vl-hidexpr->rest)))))



(define vl-hidexpr-collect-indices
  :short "Collect all expressions from index positions in a hid expression,
e.g., for @('foo[3][4].bar[5].baz'), we would return a list of expressions for
@('3 4 5')."
  ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (indices vl-exprlist-p)
  :measure (vl-expr-count x)
  (if (vl-hidexpr->endp x)
      nil
    (append (vl-hidindex->indices (vl-hidexpr->first x))
            (vl-hidexpr-collect-indices (vl-hidexpr->rest x))))
  ///
  (defthm vl-hidexpr-collect-indices-when-endp
    (implies (vl-hidexpr->endp x)
             (equal (vl-hidexpr-collect-indices x)
                    nil)))

  (local (in-theory (enable vl-hidexpr-collect-indices)))

  (local (defthm l0
           (equal (vl-exprlist-count (append x y))
                  (+ -1
                     (vl-exprlist-count x)
                     (vl-exprlist-count y)))
           :hints(("Goal" :in-theory (enable vl-exprlist-count append)))))

  (defthm vl-exprlist-count-of-vl-hidexpr-collect-indices-weak
    (implies (vl-hidexpr-p x)
             (<= (vl-exprlist-count (vl-hidexpr-collect-indices x))
                 (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :induct (vl-hidexpr-collect-indices x))))

  (defthm vl-exprlist-count-of-vl-hidexpr-collect-indices-strong
    (implies (and (vl-hidexpr-p x)
                  (not (vl-hidexpr->endp x)))
             (< (vl-exprlist-count (vl-hidexpr-collect-indices x))
                (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-exprlist-count-of-vl-hidexpr-collect-indices-equal
    (implies (and (vl-hidexpr-p x)
                  (case-split (not (vl-hidexpr->endp x))))
             (equal (equal (vl-exprlist-count (vl-hidexpr-collect-indices x))
                           (vl-expr-count x))
                    nil))))



(define vl-scopename-p (x)
  :short "Recognizes names that can be used in scope operators."
  :long "<p>This is an abstraction that is mostly intended to serve as a return
type for @(see vl-scopeexpr->scopes).</p>"
  :returns bool
  (or (eq x :vl-local)
      (eq x :vl-$unit)
      (stringp x)))

(define vl-scopename-fix ((x vl-scopename-p))
  :returns (name vl-scopename-p)
  :inline t
  (mbe :logic (if (vl-scopename-p x)
                  x
                :vl-local)
       :exec x)
  ///
  (defthm vl-scopename-fix-when-vl-scopename-p
    (implies (vl-scopename-p x)
             (equal (vl-scopename-fix x) x))))

(fty::deffixtype vl-scopename
  :pred vl-scopename-p
  :fix vl-scopename-fix
  :equiv vl-scopename-equiv
  :define t
  :forward t)

(fty::deflist vl-scopenamelist :elt-type vl-scopename)


(define vl-fast-keyguts-p ((x vl-atomguts-p))
  :enabled t
  :inline t
  (mbe :logic (vl-keyguts-p (vl-atomguts-fix x))
       :exec (eq (tag x) :vl-keyguts)))

(define vl-scopeatom-p ((x vl-expr-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (and (vl-atom-p x)
       (or (vl-hidname-p x)
           (let* ((guts (vl-atom->guts x)))
             (and (vl-fast-keyguts-p guts)
                  (let ((type (vl-keyguts->type guts)))
                    (or (vl-keygutstype-equiv type :vl-$unit)
                        (vl-keygutstype-equiv type :vl-local))))))))

(define vl-scopeatom->name ((x vl-expr-p))
  :guard (vl-scopeatom-p x)
  :returns (name vl-scopename-p)
  :prepwork ((local (in-theory (enable vl-scopeatom-p
                                       vl-scopename-p
                                       vl-scopename-fix))))
  (b* ((x (vl-expr-fix x)))
    (if (vl-hidname-p x)
        (vl-hidname->name x)
      (vl-scopename-fix (vl-keyguts->type (vl-atom->guts x))))))

(define vl-scopeexpr-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed hierarchical scope expressions."
  :long "<p>Example: @('foo::bar::a.b[1][2].c').</p>"
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  (b* (((when (vl-atom-p x))
        (mbe :logic (vl-hidexpr-p x)
             :exec (vl-hidname-p x)))
       ((vl-nonatom x) x)
       ((when (vl-op-equiv x.op :vl-scope))
        (and (vl-scopeatom-p (first x.args))
             (vl-scopeexpr-p (second x.args)))))
    (vl-hidexpr-p x)))

(define vl-scopeexpr->scopes ((x vl-expr-p))
  :guard (vl-scopeexpr-p x)
  :returns (names vl-scopenamelist-p)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-scopeexpr-p))))
  (b* (((when (vl-atom-p x))
        nil)
       ((vl-nonatom x) x)
       ((when (vl-op-equiv x.op :vl-scope))
        (cons (vl-scopeatom->name (first x.args))
              (vl-scopeexpr->scopes (second x.args)))))
    nil))

(define vl-scopeexpr->hid ((x vl-expr-p))
  :guard (vl-scopeexpr-p x)
  :returns (hid vl-expr-p)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-scopeexpr-p))))
  (b* ((x (vl-expr-fix x))
       ((when (vl-atom-p x))
        x)
       ((vl-nonatom x) x)
       ((when (vl-op-equiv x.op :vl-scope))
        (vl-scopeexpr->hid (second x.args))))
    x)
  ///
  (defret vl-hidexpr-p-of-vl-scopeexpr->hid
    (implies (vl-scopeexpr-p x)
             (vl-hidexpr-p hid))))


(define vl-indexexpr-p ((x vl-expr-p))
  :returns (bool)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-scopeexpr-p
                                       vl-hidexpr-p))))
  (b* (((when (vl-atom-p x))
        (mbe :logic (vl-scopeexpr-p x)
             :exec (vl-hidname-p x)))
       ((vl-nonatom x))
       ((when (or (vl-op-equiv x.op :vl-index)
                  (vl-op-equiv x.op :vl-bitselect)))
        (vl-indexexpr-p (first x.args))))
    (vl-scopeexpr-p x)))

(define vl-indexexpr->scopeexpr ((x vl-expr-p))
  :guard (vl-indexexpr-p x)
  :returns (scopeexpr vl-expr-p)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-indexexpr-p))))
  (b* ((x (vl-expr-fix x))
       ((when (vl-atom-p x))
        x)
       ((vl-nonatom x))
       ((when (or (vl-op-equiv x.op :vl-index)
                  (vl-op-equiv x.op :vl-bitselect)))
        (vl-indexexpr->scopeexpr (first x.args))))
    x)
  ///
  (defret vl-scopeexpr-p-of-vl-indexexpr->scopeexpr
    (implies (vl-indexexpr-p x)
             (vl-scopeexpr-p (vl-indexexpr->scopeexpr x)))))

(define vl-indexexpr->indices-exec ((x   vl-expr-p)
                                    (acc vl-exprlist-p))
  :guard (vl-indexexpr-p x)
  :returns (indices vl-exprlist-p)
  :parents (vl-indexexpr->indices)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-indexexpr-p))))
  (b* ((acc (vl-exprlist-fix acc))
       ((when (vl-atom-p x))
        acc)
       ((vl-nonatom x) x)
       ((when (or (vl-op-equiv x.op :vl-index)
                  (vl-op-equiv x.op :vl-bitselect)))
        (vl-indexexpr->indices-exec (first x.args)
                                    (cons (vl-expr-fix (second x.args))
                                          acc))))
    acc))

(define vl-indexexpr->indices ((x vl-expr-p))
  :guard (vl-indexexpr-p x)
  :returns (indices vl-exprlist-p)
  :measure (vl-expr-count x)
  :prepwork ((local (in-theory (enable vl-indexexpr-p))))
  :verify-guards nil
  :inline t
  (mbe :logic
       (b* (((when (vl-atom-p x))
             nil)
            ((vl-nonatom x))
            ((when (or (vl-op-equiv x.op :vl-index)
                       (vl-op-equiv x.op :vl-bitselect)))
             (append (vl-indexexpr->indices (first x.args))
                     (list (second x.args)))))
         nil)
       :exec
       (vl-indexexpr->indices-exec x nil))
  ///
  (local (in-theory (enable vl-indexexpr->indices-exec)))
  (defthm vl-indexexpr->indices-exec-removal
    (equal (vl-indexexpr->indices-exec x acc)
           (append (vl-indexexpr->indices x)
                   (vl-exprlist-fix acc))))
  (verify-guards vl-indexexpr->indices$inline))



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
appropriate functions.  These are largely missing in VL2014 but are being
developed for the newer @(see vl::vl).</dd>


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
warning.  We have worked to make this warning include appropriate context so
that the end-user can understand the nature and location of the problem.</dd>

</dl>")

(local (xdoc::set-default-parents following-hids))

;; BOZO it seems like many of the warnings here ought to be fatal.

(defprod vl-hidstep
  :short "A single step along the way of a hierarchical identifier."
  :long "<p>Some routines for @(see following-hids) produce traces of the items
they encounter along the way.  A <b>hidstep</b> structure represents a single
step along a HID.</p>"
  :tag :vl-hidstep
  :layout :tree
  ((item vl-scopeitem-p  "Some item encountered along the path of the HID.")
   (ss   vl-scopestack-p "The scope where this item was found.")))

(fty::deflist vl-hidtrace
  :elt-type vl-hidstep
  :short "A list of @(see vl-hidstep) structures, typically all of the steps
encountered along a HID.")

(define vl-follow-hidexpr-error
  :short "Report an error while following a HID."
  ((short stringp         "Brief description of the error.")
   (ss    vl-scopestack-p "Detailed context for the error.")
   &key
   ((ctx   acl2::any-p  "Original context for this HID.")     'ctx)
   ((origx vl-expr-p    "Original, full HID being resolved.") 'origx)
   ((x     vl-expr-p    "Current place in the HID.")          'x))
  :returns (warning vl-warning-p)
  :long "<p>This is smart in a few ways: it distinguishes between ordinary
identifiers and hierarchical identifiers in the error type, and avoids
providing excessive context if we haven't gotten anywhere down into the HID
yet.</p>"
  (b* ((x     (vl-expr-fix x))
       (origx (vl-expr-fix origx))
       (short (string-fix short))
       (type  (if (vl-idexpr-p origx)
                  :vl-bad-identifier
                :vl-bad-hid))
       ((when (equal x origx))
        ;; Omit detailed context since we haven't gotten anywhere yet.
        (make-vl-warning :type type
                         :msg "~a0: error resolving ~a1: ~s2."
                         :args (list ctx origx short)
                         :fn __function__)))
    (make-vl-warning :type type
                     :msg "~a0: error resolving ~a1: ~s2.~%~
                           (Failed to resolve ~a3 in ~s4)."
                     :args (list ctx origx short x (vl-scopestack->path ss))
                     :fn __function__)))

(define vl-follow-hidexpr-dimcheck
  :short "Check an array index against the corresponding array bounds."
  ((name    stringp              "Name being the array, for better errors.")
   (index   vl-expr-p            "An index into an array.")
   (dim     vl-packeddimension-p "Bounds from the corresponding declaration.")
   &key
   (strictp booleanp "Require indices to be resolved?"))
  :returns (err maybe-stringp :rule-classes :type-prescription)
  :long "<p>In strict mode, we require that the @('index') and the array
dimensions all be resolved and that the index be in range.</p>

<p>In non-strict mode, we tolerate unresolved indices and declaration bounds.
Note that we still do bounds checking if the indices and array bounds happen to
be resolved.</p>"

  (b* ((dim (vl-packeddimension-fix dim))
       ((when (eq dim :vl-unsized-dimension))
        ;; Bounds checking doesn't make sense in this case, so we'll just
        ;; regard this as fine.
        nil)
       ((unless (vl-expr-resolved-p index))
        (if strictp
            "unresolved array index"
          nil))
       ((unless (vl-range-resolved-p dim))
        (if strictp
            (cat "unresolved bounds on declaration of " name)
          nil))
       ((vl-range dim))
       (idxval (vl-resolved->val index))
       (msbval (vl-resolved->val dim.msb))
       (lsbval (vl-resolved->val dim.lsb))
       (minval (min msbval lsbval))
       (maxval (max msbval lsbval))
       ((unless (and (<= minval idxval)
                     (<= idxval maxval)))
        (cat "array index " (str::natstr idxval) " out of bounds ("
             (str::natstr minval) " to " (str::natstr maxval) ")")))
    nil))

(define vl-follow-hidexpr-dimscheck-aux
  :parents (vl-follow-hidexpr-dimscheck)
  :short "Main loop to check each index/dimension pair."
  ((name    stringp)
   (indices vl-exprlist-p)
   (dims    vl-packeddimensionlist-p)
   &key
   (strictp booleanp))
  :guard (same-lengthp indices dims)
  :returns (err maybe-stringp :rule-classes :type-prescription)
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
  (err maybe-stringp :rule-classes :type-prescription)
  (b* (((when (atom dims))
        (if (atom indices)
            nil
          (cat "indexing into non-array " name)))
       ((when (atom indices))
        (cat "no indices given for array " name))
       ((when (same-lengthp indices dims))
        (vl-follow-hidexpr-dimscheck-aux name indices dims
                                         :strictp strictp))
       (found (len indices))
       (need  (len dims))
       ((when (< found need))
        (cat "too many indices for array " name)))
    (cat "not enough indices for array " name)))

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

(define vl-follow-hidexpr-aux
  :parents (vl-follow-hidexpr)
  :short "Core routine for following hierarchical identifiers."
  ((x     vl-expr-p       "HID expression fragment that we are following.")
   (trace vl-hidtrace-p   "Accumulator for the trace until now.")
   (ss    vl-scopestack-p "Current scopestack we're working from.")
   &key
   (strictp booleanp)
   ((origx vl-expr-p      "Original version of X, for better error messages.") 'origx)
   ((ctx   acl2::any-p    "Original context, for better error messages.")      'ctx))
  :guard (vl-hidexpr-p x)
  :returns
  (mv (err     (iff (vl-warning-p err) err)
               "A @(see vl-warning-p) on any error.")
      (new-trace vl-hidtrace-p
                 "On success, a nonempty trace that records all the items we
                  went through to resolve this HID.  The @(see car) of the
                  trace is the final item and scopestack.")
      (tail    vl-expr-p
               "Remainder of @('x') after arriving at the declaration."))
  :long "<p>See @(see vl-follow-hidexpr) for detailed discussion.  This
@('-aux') function does most of the work, but for instance it doesn't deal with
top-level hierarchical identifiers.</p>"
  :measure (vl-expr-count x)
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (or (vl-module-p x)
                                   (vl-interface-p x))
                               (vl-scope-p x)))))
  :hooks ((:fix
           :hints(("Goal"
                   :expand ((:free (trace ss strictp) (vl-follow-hidexpr-aux x trace ss :strictp strictp))
                            (:free (trace ss strictp) (vl-follow-hidexpr-aux (vl-expr-fix x) trace ss :strictp strictp)))))))
  (b* ((trace (vl-hidtrace-fix trace))
       (x     (vl-expr-fix x))
       (idx1  (vl-hidexpr->first x))
       (name1 (vl-hidindex->name idx1))

       ((mv item item-ss) (vl-scopestack-find-item/ss name1 ss))
       ((unless item)
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace x))

       (trace (cons (make-vl-hidstep :item item :ss item-ss) trace))

       ((when (or (eq (tag item) :vl-vardecl)
                  (eq (tag item) :vl-paramdecl)))
        ;; Found the declaration we want.  We aren't going to go any further:
        ;; there may be additional HID indexing stuff left, but if so it's just
        ;; array or structure indexing for the tail.
        (mv nil trace x))

       ((when (or (eq (tag item) :vl-fundecl)
                  (eq (tag item) :vl-taskdecl)))
        (if (vl-hidexpr->endp x)
            ;; Plain reference to, e.g., foo.bar.myfun.  This is OK -- you
            ;; might be writing something like ``logic foo = submod.fn(arg)''
            (mv nil trace x)
          ;; Indexed or dotted reference like foo.bar.myfun[3] or
          ;; foo.bar.myfun[3].baz or foo.bar.myfun.baz, none of which seem to
          ;; really be reasonable as things to refer to hierarchically.
          (mv (vl-follow-hidexpr-error (if (eq (tag item) :vl-fundecl)
                                           "hierarchical reference into function"
                                         "hierarchical reference into task")
                                       item-ss)
              trace x)))

       ((when (eq (tag item) :vl-modinst))
        (b* (((vl-modinst item))
             (indices (vl-hidindex->indices idx1))
             (dims    (and item.range (list item.range)))
             ;; Start by checking for sensible array indexing.
             (err (vl-follow-hidexpr-dimscheck name1 indices dims :strictp strictp))
             ((when err)
              (mv (vl-follow-hidexpr-error err item-ss)
                  trace x))
             ((when (vl-hidexpr->endp x))
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
              (mv (vl-follow-hidexpr-error (cat "reference through missing module " item.modname) item-ss)
                  trace x))
             (modtag (tag mod))
             ((when (eq modtag :vl-udp))
              (mv (vl-follow-hidexpr-error (cat "reference through primitive " item.modname) item-ss)
                  trace x))
             ((unless (or (eq modtag :vl-module)
                          (eq modtag :vl-interface)))
              (mv (vl-follow-hidexpr-error (cat "module instance " name1 " of " item.modname
                                                ": invalid type " (if (symbolp modtag)
                                                                      (symbol-name modtag)
                                                                    "???"))
                                           item-ss)
                  trace x))
             (next-ss
              ;; The MOD-SS is just the scopestack for where the module is
              ;; defined, which in practice will be the top level scope.
              ;; The next part of the HID needs to be looked up from within
              ;; MOD, so we need to actually go into the module.
              (vl-scopestack-push mod mod-ss)))
          (vl-follow-hidexpr-aux (vl-hidexpr->rest x) trace next-ss :strictp strictp)))

       ((when (eq (tag item) :vl-interfaceport))
        (b* (((vl-interfaceport item))
             (indices (vl-hidindex->indices idx1))
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
             ((when (vl-hidexpr->endp x))
              ;; Stopping at this interface port.  Unlike module instances,
              ;; this seems OK.  The interface port itself acts like a
              ;; variable.
              (mv nil trace x))
             ((mv iface iface-ss)
              (vl-scopestack-find-definition/ss item.ifname item-ss))
             ((unless iface)
              (mv (vl-follow-hidexpr-error (cat "reference through missing interface " item.ifname)
                                           item-ss)
                  trace x))
             (iftag (tag iface))
             ((unless (eq iftag :vl-interface))
              (mv (vl-follow-hidexpr-error (cat "interface port " name1 " of interface " item.ifname
                                                ": invalid type " (if (symbolp iftag)
                                                                      (symbol-name iftag)
                                                                    "???"))
                                           item-ss)
                  trace x))
             (next-ss (vl-scopestack-push iface iface-ss)))
          (vl-follow-hidexpr-aux (vl-hidexpr->rest x) trace next-ss
                                 :strictp strictp)))

       ((when (eq (tag item) :vl-genblock))
        (b* ((indices (vl-hidindex->indices idx1))
             ((when (consp indices))
              ;; Doesn't make any sense: this is a single, named generate
              ;; block, not an array, so we shouldn't try to index into it.
              (mv (vl-follow-hidexpr-error "array indices on reference to generate block" item-ss)
                  trace x))
             ((when (vl-hidexpr->endp x))
              ;; Doesn't make any sense: referring to foo.bar.myblock all by
              ;; itself.
              (mv (vl-follow-hidexpr-error "reference to generate block" item-ss)
                  trace x))
             ;; Else we have something like foo.bar.myblock.mywire or whatever.
             ;; This is fine, we just need to go into the generate block.
             (genblob (vl-sort-genelements (vl-genblock->elems item)))
             (next-ss (vl-scopestack-push genblob item-ss)))
          (vl-follow-hidexpr-aux (vl-hidexpr->rest x) trace next-ss
                                 :strictp strictp)))

       ((when (eq (tag item) :vl-genarray))
        (b* (((when (vl-hidexpr->endp x))
              ;; Doesn't make any sense.  Either this is a raw reference to the
              ;; array like foo.bar.mygenarray, or is an indexed reference to
              ;; something like foo.bar.mygenarray[3], but in either case it
              ;; would be referring to a whole generate block or to an array of
              ;; generate blocks, not something inside those blocks.
              (mv (vl-follow-hidexpr-error "reference to generate array" item-ss)
                  trace x))
             (indices (vl-hidindex->indices idx1))
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
              (mv (vl-follow-hidexpr-error (cat "invalid index into generate array: " (str::natstr blocknum))
                                           item-ss)
                  trace x))
             (genblob (vl-sort-genelements (vl-genarrayblock->elems block)))
             (next-ss (vl-scopestack-push genblob item-ss)))
          (vl-follow-hidexpr-aux (vl-hidexpr->rest x) trace next-ss :strictp strictp)))

       ((when (eq (tag item) :vl-typedef))
        ;; I don't think this makes sense?  Can you refer to a type name?  BOZO
        ;; maybe this makes sense for things like $bits(mystruct_t.foo) or
        ;; something like that?  If so it may still be that we don't want to
        ;; deal with this in the aux function, but rather it should be
        ;; something that the top-level wrapper deals with.
        (mv (vl-follow-hidexpr-error "hierarchical reference to typedef" item-ss)
            trace x))

       ((when (eq (tag item) :vl-modport))
        ;; I don't think it makes any sense to have a hierarchical reference to
        ;; a modport, so let's disallow that for now.  BOZO we may want to just
        ;; remove modports from scopeitems altogether.  If so we can remove
        ;; this case.
        (mv (vl-follow-hidexpr-error "hierarchical reference to modports" item-ss)
            trace x))

       ((when (or (eq (tag item) :vl-genif)
                  (eq (tag item) :vl-gencase)
                  (eq (tag item) :vl-genloop)
                  (eq (tag item) :vl-genbase)))
        ;; I don't think any of these are supposed to have names and,
        ;; accordingly, it shouldn't make sense to have looked one up.
        (mv (vl-follow-hidexpr-error (cat "hierarchical reference to " (symbol-name (tag item)))
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
              :name consp-of-vl-follow-hidexpr-aux.new-trace)
   (tail vl-hidexpr-p :hyp (vl-hidexpr-p x)))

  (defthm context-irrelevance-of-vl-follow-hidexpr-aux
    (implies (syntaxp (or (not (equal ctx (list 'quote nil)))
                          (not (equal origx  (list 'quote (with-guard-checking :none (vl-expr-fix nil)))))))
             (b* (((mv err1 trace1 tail1) (vl-follow-hidexpr-aux x trace ss
                                                              :ctx ctx
                                                              :strictp strictp
                                                              :origx origx))
                  ((mv err2 trace2 tail2) (vl-follow-hidexpr-aux x trace ss
                                                              :ctx nil
                                                              :strictp strictp
                                                              :origx (vl-expr-fix nil))))
               (and (equal trace1 trace2)
                    (equal tail1 tail2)
                    (iff err1 err2))))
    :hints ((acl2::just-induct-and-expand
             (vl-follow-hidexpr-aux x trace ss
                                    :ctx ctx
                                    :strictp strictp
                                    :origx origx)
             :expand-others
             ((:free (ctx strictp origx)
               (vl-follow-hidexpr-aux x trace ss
                                    :ctx ctx
                                    :strictp strictp
                                    :origx origx)))))))

(define vl-follow-hidexpr
  :short "Follow a HID to find the associated declaration."
  ((x       vl-expr-p       "Hierarchical identifier to follow.")
   (ss      vl-scopestack-p "Scopestack where the HID originates.")
   (ctx     acl2::any-p     "Context for better error messages.")
   &key
   (strictp booleanp "Require all array indices and bounds to be resolved?"))
  :guard (vl-hidexpr-p x)
  :guard-debug t
  :returns
  (mv (err   (iff (vl-warning-p err) err)
             "A warning on any error.")
      (trace vl-hidtrace-p
             "On success: a non-empty trace that records all the items we went
              through to resolve this HID.  The @(see car) of the trace is the
              final declaration for this HID.")
      (tail  vl-expr-p
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
vl-warning-p) and the other results are <b>not sensible</b> and should not be
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

  (b* ((x     (vl-expr-fix x))
       (idx1  (vl-hidexpr->first x))
       (name1 (vl-hidindex->name idx1))

       (origx x)
       (trace nil)

       ((mv item &) (vl-scopestack-find-item/ss name1 ss))
       ((when item)
        ;; Item is found in the current scope so this is an ordinary, not
        ;; top-level hierarchical identifier.  Go ahead and just use our
        ;; downward lookup code.
        (vl-follow-hidexpr-aux x nil ss
                               :strictp strictp
                               :ctx ctx))

       ;; BOZO eventually this may need to be extended to deal with $root,
       ;; $unit, etc.  Maybe also scopes if we decide to try to implement
       ;; scope operators like foo::bar.baz...
       ((when (vl-hidexpr->endp x))
        ;; Item was not found AND it is not of the form foo.bar, so we do NOT
        ;; want to interpret it as any sort of reference to a top-level module.
        (mv (vl-follow-hidexpr-error "item not found" ss) trace x))

       ;; Otherwise, might be a valid reference into a top-level module?
       (design   (vl-scopestack->design ss))
       ((unless design)
        ;; We must be using a phony scopestack.  We have no way of knowing what
        ;; the top-level modules are so we have no idea if this is valid.
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace x))

       (mods     (vl-design->mods design))
       (toplevel (vl-modulelist-toplevel mods))
       ((unless (member-equal name1 toplevel))
        (mv (vl-follow-hidexpr-error "item not found" ss)
            trace x))

       ;; Successfully found a top-level module with the first index name.
       (indices (vl-hidindex->indices idx1))
       ((when (consp indices))
        ;; Something like topmod[3].foo.bar, doesn't make any sense.
        (mv (vl-follow-hidexpr-error "array indices into top level module" ss)
            trace x))

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
       (next-ss (vl-scopestack-push mod mod-ss)))
    (vl-follow-hidexpr-aux (vl-hidexpr->rest x) trace next-ss
                           :strictp strictp
                           :ctx ctx))
  ///
  (more-returns
   (trace (implies (not err)
                   (consp trace))
          :name consp-of-vl-follow-hidexpr.trace)
   (tail vl-hidexpr-p :hyp (vl-hidexpr-p x)))

  (defthm context-irrelevance-of-vl-follow-hidexpr
    (implies (syntaxp (not (equal ctx (list 'quote nil))))
             (b* (((mv err1 trace1 tail1) (vl-follow-hidexpr x ss ctx :strictp strictp))
                  ((mv err2 trace2 tail2) (vl-follow-hidexpr x ss nil :strictp strictp)))
               (and (equal trace1 trace2)
                    (equal tail1 tail2)
                    (iff err1 err2))))))



(define vl-hidindex-datatype-resolve-dims ((x vl-expr-p)
                                           (type vl-datatype-p))
  :short "Given a hidindex expression, e.g. foo[5][3], and the datatype and
unpacked dimensions corresponding to foo, return the datatype and unpacked
dimensions corresponding to the whole expression."

  :long "<p>Note: we don't check whether indices are in bounds or anything,
just whether the number of indices is less than or equal the number of
total (unpacked plus packed) dimensions.</p>

<p>We produce a non-fatal warning because we're not sure in what contexts this
will be used.</p>

<p>Example: Suppose our datatype is from a typedef</p>

@({
    typedef bit [3:0] [4:2] foo [0:6] [0:8];
})

<p>that is, it has one unpacked dimension @('[0:6]') and two packed dimensions.
Suppose our expression is @('bar[5][7][2]'), where bar is of type foo.  Then we
should return @('bit[4:2]') as our resolved datatype, with no unpacked
dimensions, because the first two indices correspond to the unpacked dimension
and the second to the first packed dimension.  On the other hand if we had
@('bar[5]'), we should return @('bit') with packed dimensions @('[3:0][4:2]')
and unpacked dimension @('[0:8]').</p>"
  :guard (vl-hidindex-p x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type1 (iff (vl-datatype-p type1) (not warning))))
  (b* ((idxcount (vl-hidindex-count-indices x))
       (type (vl-datatype-fix type))
       (x (vl-expr-fix x))
       (unpacked-dims (vl-datatype->udims type))
       (packed-dims (vl-datatype->pdims type))
       (nunpacked (len unpacked-dims))
       ((when (<= idxcount nunpacked))
        (mv nil (vl-datatype-update-udims
                 (nthcdr idxcount (list-fix unpacked-dims)) type)))
       (remaining-idxcount (- idxcount nunpacked))
       ((unless (<= remaining-idxcount (len packed-dims)))
        (mv (make-vl-warning :type :vl-too-many-indices
                             :msg "Too many indices on expression ~a0 ~
                                   relative to dimensions of type ~a1 (with ~
                                   ~x2 additional unpacked dimensions)."
                             :args (list x type (len unpacked-dims))
                             :fn __function__)
            nil))
       (type (vl-datatype-update-dims
              (nthcdr remaining-idxcount (list-fix packed-dims))
              nil ;; udims
              type)))
    (mv nil type)))


;; Have a HID, and know (for the base name) the type (unresolved) and unpacked
;; dims.

;; Resolve the type.
;; If the hid is an ID, return the type and dims.

;; Resolve the indices of the base part against the unpacked/packed dims.  If we
;; end up still having dims remaining, fail.

;; If the type is not a struct or union type, fail.

;; Find the next name in the HID among the structmembers.  If not found, fail.

;; Recur with the rest of the HID and the type/unpacked dims of the member.


(define vl-hidexpr-traverse-datatype ((x vl-expr-p)
                                      (type vl-datatype-p))
  :parents (hid-tools)
  :short "Given a dotted expression that indexes into a datatype, find the type of the expression."
  :long " <p>A helpful invariant to remember when thinking about this function:
The type and unpacked dimensions of a given call of this function belong to the
base (leftmost) variable in the HID.</p>

<p>Also note: the datatype should be fully usertype-resolved, as by
vl-datatype-usertype-elim.</p>

<p>BOZO Rewrite this documentation under the new assumption that the datatypes
are pre-resolved.</p>

<p>Example: Suppose we have the following type declarations</p>
@({
 typedef struct packed { logic [3:0] foo; } [4:0] foostruct;
 typedef union { foostruct [5:0] bar; logic [2:0] baz; } bunion [0:6];
 typedef struct { bunion fa [0:8], logic [1:0] ba; } bstruct;
 bstruct myvar [8:0];
})

<p>For this example, we'll write a type with both packed an unpacked dimensions
with an underscore between the packed and unpacked dims.</p>

<p>A bunion is a type consisting of an unpacked array of 7 elements
each of which may either be a packed array of 6 foostructs (a packed structure
containing one 4-bit logic field) or a 3-bit logic; a bstruct is a struct
containing an unpacked array of 9 bunions and an additional 2-bit logic field;
and myvar is an unpacked array of 9 bstructs.</p>

<p>Suppose our expression is @('myvar[1].fa[8][4].bar[3][4].foo').</p>

<ul>

<li>First, before calling this function we look up the type of myvar.  We get a
vardecl, which has a type @('bstruct _ [8:0]'). Then we're ready to run.</li>

<li>Outermost call: We resolve the type bstruct to its struct definition.  We
cancel our index with the single array dimension, leaving just the struct.  We
find the element fa inside the struct, and
recur on the remainder of our expression, @('fa[8][4].bar[3][4].foo'), with the
structmember's type, @('bunion _ [0:8]').</li>

<li> We resolve the bunion type to the union, and append the unpacked
dimensions of the type and the element to get @('[0:8][0:6]').  We then check
the indices from the expression against this type and unpacked dimensions,
which results in just the bare union type (the definition of bunion, but
without its unpacked dimension @('[0:6]')).  We find the element bar inside the
union and recur: @('bar[3][4].foo'), type @('foostruct[5:0]').</li>

<li> We resolve the type foostruct to its struct type, and append the packed
dimensions to get @('[5:0][4:0]').  We then check the indices from the
expression, which results in cancelling out the dimension to obtain just the
bare struct.  We find the element foo of the struct and recur on that.</li>

<li>Finally, we have just the atom @('foo') as our expression, so we return the
type @('logic[3:0]').</li> </ul>"
  :guard (vl-hidexpr-p x)
  :measure (vl-expr-count x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (restype (iff (vl-datatype-p restype) (not warning))))
  ;; Resolve the type and dims.
  (b* ((type (vl-datatype-fix type))
       ((when (vl-hidexpr->endp x))
        ;; We have at just an ID.  Return the resolved type.
        (mv nil type))

       ;; Cancel the indices of the first element of the HID with the unpacked
       ;; and packed dims of the type.
       (idx1 (vl-hidexpr->first x))
       ((mv warning baretype)
        (vl-hidindex-datatype-resolve-dims idx1 type))
       ((when warning) (mv warning nil))
       ((when (or (consp (vl-datatype->udims baretype))
                  (consp (vl-datatype->pdims baretype))))
        (mv (make-vl-warning :type :vl-hid-datatype-fail
                             :msg "Not enough indices in dotted selector ~a0: ~
                                   extra ~s1 dimensions."
                             :args (list
                                    (vl-expr-fix x)
                                    (if (consp (vl-datatype->udims baretype))
                                        "unpacked" "packed"))
                             :fn __function__)
            nil))

       ;; Next we're going to dot-index into the datatype, so get its
       ;; structmembers, making sure it's a struct.
       ((mv ok members) (vl-datatype->structmembers baretype))
       ((unless ok)
        (mv (make-vl-warning :type :vl-hid-datatype-fail
                             :msg "Dot-indexing into a datatype that isn't a ~
                                   struct or union: ~a0"
                             :args (list (vl-datatype-fix baretype))
                             :fn __function__)
            nil))

       ;; Look up the member corresponding to the next name in the hid.
       (next-hid (vl-hidexpr->rest x))
       (nextname (vl-hidindex->name (vl-hidexpr->first next-hid)))
       (member (vl-find-structmember nextname members))
       ((unless member)
        (mv (make-vl-warning :type :vl-structindex-fail
                             :msg "Dot-indexing failed: struct/union member ~
                                   ~s0 not found in type ~a1"
                             :args (list nextname (vl-datatype-fix baretype))
                             :fn __function__)
            nil))
       (membtype (vl-structmember->type member)))
    (vl-hidexpr-traverse-datatype next-hid membtype)))

(define vl-hidexpr-find-type ((x   vl-expr-p)
                              (ss  vl-scopestack-p)
                              (ctx acl2::any-p))
  :parents (hid-tools)
  :short "Looks up a HID in a scopestack and looks for a declaration, returning the type and dimensionlist if found."
  :guard (vl-hidexpr-p x)
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (iff (vl-datatype-p type) (not warning))))
  (b* ((x (vl-expr-fix x))
       ((mv err trace tail) (vl-follow-hidexpr x ss ctx))
       ((when err) (mv err nil))
       ((vl-hidstep step1) (car trace))
       ((when (eq (tag step1.item) :vl-vardecl))
        ;; check its datatype
        (b* (((vl-vardecl step1.item))
             ((mv warning res-type)
              (vl-datatype-usertype-elim step1.item.type step1.ss 1000))
             ((when warning) (mv warning nil)))
          (vl-hidexpr-traverse-datatype tail res-type))))
    (mv (make-vl-warning :type (if (vl-idexpr-p x)
                                   :vl-identifier-type-fail
                                 :vl-hidexpr-type-fail)
                         :msg "~a0: Failed to find a type for ~s1 because we ~
                               didn't find a vardecl but rather a ~x2"
                         :args (list ctx x (tag step1.item))
                         :fn __function__)
        nil))
  ///
  (defthm context-irrelevance-of-vl-hidexpr-find-type
    (implies (syntaxp (not (equal ctx ''nil)))
             (b* (((mv err1 type1) (vl-hidexpr-find-type x ss ctx))
                  ((mv err2 type2) (vl-hidexpr-find-type x ss nil)))
               (and (iff err1 err2)
                    (equal type1 type2))))))






(define vl-ss-find-hidexpr-range ((x vl-expr-p)
                                  (ss vl-scopestack-p))
  :guard (vl-hidexpr-p x)
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (range    vl-maybe-range-p))
  (b* (((mv warning type) (vl-hidexpr-find-type x ss (vl-expr-fix x)))
       ((when warning) (mv warning nil)))
    (vl-datatype-range-conservative type)))

(define vl-ss-find-hidexpr-range!! ((x vl-expr-p)
                                    (ss vl-scopestack-p))
  :short "The exclamation marks are there to get your attention."
  :long "<p>This finds the range of the datatype of the given hid, using @(see
vl-datatype-range).  In code that is not aware of multidimensional
arrays/vectors, you should use @(see vl-ss-find-hidexpr-range) (without the
exclamation marks) instead; it finds the datatype range using @(see
vl-datatype-range-conservative) which will correctly produce warnings when the
datatype is multidimensional.</p>"
  :guard (vl-hidexpr-p x)
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (range    vl-maybe-range-p))
  (b* (((mv warning type) (vl-hidexpr-find-type x ss (vl-expr-fix x)))
       ((when warning) (mv warning nil)))
    (vl-datatype-range type)))



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

(define vl-index-find-type
  ((x vl-expr-p "Should be a hid (perhaps just an ID), perhaps with some indexing
                 operators applied to it, i.e., bitselect or index operators but
                 not part-select operators.  So for instance: @('foo, foo.bar,
                 foo.bar[3], foo.bar[3][4][5]')")
   (ss vl-scopestack-p "Scopestack where @('x') occurs.")
   (ctx acl2::any-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning)
                        "Success indicator, we fail if we can't follow the HID or
                         this isn't an appropriate expression.")
               (type (implies (not warning) (vl-datatype-p type))
                     "The type of the resulting expression after all indexing
                      is done."))
  :prepwork ((local (in-theory (disable default-car
                                        vl-hidexpr-p-when-id-atom
                                        vl-nonatom->op-when-vl-hidindex-p))))
  :verify-guards nil
  :measure (vl-expr-count x)
  (b* ((x (vl-expr-fix x))
       ((when (or (vl-atom-p x)
                  (not (member (vl-nonatom->op x)
                               '(:vl-index :vl-bitselect)))))
        (b* (((unless (vl-hidexpr-p x))
              (mv (make-vl-warning
                   :type :vl-bad-index-expr
                   :msg "~a0: An index operator was applied to a bad subexpression, ~a1."
                   :args (list ctx x)
                   :fn __function__)
                  nil))
             ((mv warning type) (vl-hidexpr-find-type x ss ctx))
             ((when warning) (mv warning nil)))
          (mv nil type)))
       ((vl-nonatom x))
       ((mv warning sub-type) (vl-index-find-type (first x.args) ss ctx))
       ((when warning) (mv warning nil))
       (udims (vl-datatype->udims sub-type))
       ((when (consp udims))
        ;; We could check here that the index is in bounds, but maybe that
        ;; should more appropriately be done elsewhere.
        (mv nil (vl-datatype-update-udims (cdr udims) sub-type)))
       (pdims (vl-datatype->pdims sub-type))
       ((when (consp pdims))
        ;; An index operator applied to packed dimensions makes the datatype unsigned.
        (mv nil (vl-datatype-update-pdims (cdr pdims) (vl-datatype-set-unsigned sub-type))))
       ;; If there are no dimensions, the index has to be a bitselect; check
       ;; whether this is ok.
       ((when (vl-datatype-bitselect-ok sub-type))
        ;; We have a bitselect of some packed non-array type.  The result is
        ;; therefore an unsigned single bit.
        (mv nil
            (make-vl-coretype :name :vl-logic))))
    (mv (make-vl-warning :type :vl-bad-indexing-operator
                         :msg "~a0: Can't apply an index operator to ~a1 because ~
                               it has no dimensions; its type is ~a2."
                         :args (list ctx (first x.args) sub-type)
                         :fn __function__)
        nil))

  ///
  (verify-guards vl-index-find-type
    :hints(("Goal" :in-theory (e/d (acl2::member-of-cons)
                                   (vl-index-find-type)))))

  (defthm context-irrelevance-of-vl-index-find-type
    (implies (syntaxp (not (equal ctx ''nil)))
             (b* (((mv err1 type1) (vl-index-find-type x ss ctx))
                  ((mv err2 type2) (vl-index-find-type x ss nil)))
               (and (iff err1 err2)
                    (equal type1 type2))))))



(define vl-partselect-type-top-dimension-replacement ((dim vl-packeddimension-p)
                                                      (x vl-expr-p)
                                                      (ctx vl-context-p))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable acl2::member-of-cons))))
  :guard (and (not (vl-atom-p x))
              (member (vl-nonatom->op x)
                      '(:vl-select-colon
                        :vl-select-pluscolon
                        :vl-select-minuscolon
                        :vl-partselect-colon
                        :vl-partselect-pluscolon
                        :vl-partselect-minuscolon)))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (range (implies (not warning) (vl-range-p range))))

  (b* (((vl-nonatom x))
       (x  (vl-expr-fix x))
       (dim (vl-packeddimension-fix dim))
       (ctx (vl-context-fix ctx))
       ((when (or (eq dim :vl-unsized-dimension)
                  (not (vl-range-resolved-p dim))))
        (mv (make-vl-warning :type :vl-partselect-type-unresolved
                             :msg "~a0: Couldn't find type of ~a1 because the ~
                                   most significant dimension of the type of ~
                                   ~a2 was unsized or non-constant."
                             :args (list ctx x (first x.args))
                             :fn __function__)
            nil))
       ((unless (and (vl-expr-resolved-p (third x.args))
                     (or (not (member x.op '(:vl-partselect-colon
                                             :vl-select-colon)))
                         (vl-expr-resolved-p (second x.args)))))
        (mv (make-vl-warning :type :vl-partselect-indices-unresolved
                             :msg "~a0: Couldn't find type of ~a1 because the ~
                                   partselect has non-constant indices."
                             :args (list ctx x)
                             :fn __function__)
            nil))
       ((when (member x.op '(:vl-select-colon :vl-partselect-colon)))
        (mv nil (make-vl-range :msb (second x.args) :lsb (third x.args))))
       (width (vl-resolved->val (third x.args)))
       ((unless (posp width))
        (mv (make-vl-warning :type :vl-partselect-indices-unresolved
                             :msg "~a0: Zero width in partselect operator?"
                             :args (list ctx x)
                             :fn __function__)
            nil))
       ((unless (vl-expr-resolved-p (second x.args)))
        (mv nil (make-vl-range :msb (vl-make-index (1- width)) :lsb (vl-make-index 0))))
       ;; The second argument is resolved, so set the range as specified.
       (m-or-lsb (vl-resolved->val (second x.args)))
       (backward-range-p (< (vl-resolved->val (vl-range->msb dim))
                            (vl-resolved->val (vl-range->lsb dim))))
       (greater-idx (if (member x.op '(:vl-select-pluscolon :vl-partselect-pluscolon))
                        (+ m-or-lsb width -1)
                      m-or-lsb))
       (lesser-idx (if (member x.op '(:vl-select-pluscolon :vl-partselect-pluscolon))
                       m-or-lsb
                     (+ m-or-lsb (- width) 1)))
       ((when (< lesser-idx 0))
        (mv (make-vl-warning :type :vl-partselect-index-error
                             :msg "~a0: Partselect ~s1 operator yields negative index: ~a2"
                             :args (list ctx (if (eq x.op :vl-partselect-pluscolon)
                                                  "+:" "-:")
                                         x)
                             :fn __function__)
            nil))
       (range (make-vl-range :msb (vl-make-index (if backward-range-p lesser-idx greater-idx))
                             :lsb (vl-make-index (if backward-range-p greater-idx lesser-idx)))))
    (mv nil range))
  ///
  (defthm context-irrelevance-of-vl-partselect-type-top-dimension-replacement
    (implies (syntaxp (not (equal ctx (list 'quote (with-guard-checking :none (vl-context-fix nil))))))
             (and (equal (mv-nth 1 (vl-partselect-type-top-dimension-replacement dim x ctx))
                         (mv-nth 1 (vl-partselect-type-top-dimension-replacement dim x nil)))
                  (iff (mv-nth 0 (vl-partselect-type-top-dimension-replacement dim x ctx))
                       (mv-nth 0 (vl-partselect-type-top-dimension-replacement dim x nil)))))))



(define vl-partselect-expr-type ((x vl-expr-p)
                                 (ss vl-scopestack-p)
                                 (ctx vl-context-p "context"))
  :guard (not (eq (vl-expr-kind x) :atom))
  :guard-hints (("goal" :in-theory (enable acl2::member-of-cons)))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (implies (not warning) (vl-datatype-p type))))
  :prepwork ((local (in-theory (disable default-car default-cdr
                                        vl-expr-resolved-p-of-car-when-vl-exprlist-resolved-p
                                        vl-hidexpr-p-when-id-atom
                                        vl-nonatom->op-when-vl-hidindex-p))))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  (b* ((ctx (vl-context-fix ctx))
       ((vl-nonatom x) (vl-expr-fix x))
       ((unless (member x.op
                        '(:vl-select-colon
                          :vl-select-pluscolon
                          :vl-select-minuscolon
                          :vl-partselect-colon
                          :vl-partselect-pluscolon
                          :vl-partselect-minuscolon)))
        (mv (make-vl-warning :type :vl-programming-error
                             :msg "~a0: called vl-partselect-selfsize on non-partselect expr ~a1"
                             :args (list ctx x)
                             :fn __function__)
            nil))
       ((mv warning sub-type) (vl-index-find-type (first x.args) ss ctx))
       ((when warning) (mv warning nil))
       (udims (vl-datatype->udims sub-type))
       (pdims (vl-datatype->pdims sub-type))
       ((unless (or (consp udims) (consp pdims)))
        (b* (((unless (vl-datatype-bitselect-ok sub-type))
              (mv (make-vl-warning
                   :type :vl-bad-indexing-operator
                   :msg "~a0: Can't apply an index operator to ~a1 because it ~
                         has no dimensions; its type is ~a2."
                   :args (list ctx (first x.args) sub-type)
                   :fn __function__)
                  nil))
             ((mv warning size) (vl-datatype-size sub-type))
             ((when warning) (mv warning nil))
             ;; The type is some packed thing, and we have its size.  As long
             ;; as the partselect is in range, we'll just return a new logic
             ;; with the correct dimension on it.
             (range (make-vl-range :msb (vl-make-index (1- size))
                                   :lsb (vl-make-index 0)))
             ((mv warning new-dim1)
              (vl-partselect-type-top-dimension-replacement range x ctx))
             ((when warning) (mv warning nil))
             (new-type (make-vl-coretype :name :vl-logic
                                         :pdims (list new-dim1))))
          (mv nil new-type)))
       (dim1 (if (consp udims) (car udims) (car pdims)))
       ((mv warning new-dim1)
        (vl-partselect-type-top-dimension-replacement dim1 x ctx))
       ((when warning) (mv warning nil))
       (new-type (vl-datatype-update-dims
                  (if (consp udims) pdims (cons new-dim1 (cdr pdims)))
                  (and (consp udims) (cons new-dim1 (cdr udims)))
                  sub-type))
       ;; packed types become unsigned
       (new-type (if (consp udims) new-type (vl-datatype-set-unsigned new-type))))
    (mv nil new-type))
  ///
  (defthm context-irrelevance-of-vl-partselect-expr-type
    (implies (syntaxp (not (equal ctx (list 'quote (with-guard-checking :none (vl-context-fix nil))))))
             (and (equal (mv-nth 1 (vl-partselect-expr-type x ss ctx))
                         (mv-nth 1 (vl-partselect-expr-type x ss nil)))
                  (iff (mv-nth 0 (vl-partselect-expr-type x ss ctx))
                       (mv-nth 0 (vl-partselect-expr-type x ss nil)))))))












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






(define vl-hidindex-resolved-p ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (bool)
  :short "Determines if every index in a @(see vl-hidindex-p) is resolved."
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
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


(define vl-hidexpr-resolved-p ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  ;; :prepwork ((local (in-theory (enable vl-nonatom->op-when-hidindex-resolved-p))))
  :returns (bool)
  :short "Determines if every index throughout a @(see vl-hidexpr-p) is resolved."
  :guard-debug t
  :measure (vl-expr-count x)
  (if (vl-hidexpr->endp x)
      t
    (and (vl-hidindex-resolved-p (vl-hidexpr->first x))
         (vl-hidexpr-resolved-p (vl-hidexpr->rest x))))
  ///
  (defthm vl-hidexpr-resolved-p-when-endp
    (implies (vl-hidexpr->endp x)
             (vl-hidexpr-resolved-p x)))

  (defthm vl-hidexpr-resolved-p-when-not-endp
    ;; Really I should be using something like a of-cons rule here, but without
    ;; a constructor...
    (implies (not (vl-hidexpr->endp x))
             (equal (vl-hidexpr-resolved-p x)
                    (and (vl-hidindex-resolved-p (vl-hidexpr->first x))
                         (vl-hidexpr-resolved-p (vl-hidexpr->rest x)))))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

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



(define vl-flatten-hidindex-aux ((indices (and (vl-exprlist-p indices)
                                               (vl-exprlist-resolved-p indices)))
                                 acc)
  :parents (vl-flatten-hidindex)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom indices))
        acc)
       (acc (cons #\[ acc))
       (acc (revappend (str::nat-to-dec-chars (vl-resolved->val (car indices))) acc))
       (acc (cons #\] acc)))
    (vl-flatten-hidindex-aux (cdr indices) acc)))

(define vl-flatten-hidindex ((x vl-expr-p))
  :guard (and (vl-hidindex-p x)
              (vl-hidindex-resolved-p x))
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a @(see vl-hidindex-p) into a string like @('\"bar[3][4][5]\"')."
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (vl-expr-count x)
  :guard-hints(("Goal" :in-theory (enable vl-hidindex-resolved-p)))
  (b* ((name    (vl-hidindex->name x))
       (indices (vl-hidindex->indices x))
       ((when (atom indices))
        name)
       (acc nil)
       (acc (str::revappend-chars name acc))
       (acc (vl-flatten-hidindex-aux indices acc)))
    (str::rchars-to-string acc)))

(define vl-flatten-hidexpr ((x vl-expr-p))
  :guard (and (vl-hidexpr-p x)
              (vl-hidexpr-resolved-p x))
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a hierarchical identifier expression into a string like
@('foo.bar[3][4][5].baz')."
  :measure (vl-expr-count x)
  (if (vl-hidexpr->endp x)
      (vl-hidname->name x)
    (cat (vl-flatten-hidindex (vl-hidexpr->first x))
         "."
         (vl-flatten-hidexpr (vl-hidexpr->rest x)))))

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
