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
(include-book "../../mlib/allexprs")
(include-book "../../mlib/scopestack")
(include-book "../../mlib/fmt")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defconst *vl-shadowcheck-debug*
  ;; Can be redefined to enable some debugging messages.
  nil)

(defmacro vl-shadowcheck-debug (msg &rest args)
  `(if *vl-shadowcheck-debug*
       (vl-cw-ps-seq (vl-cw ,msg . ,args))
     nil))


(defsection deltemps
  :parents (shadowcheck)
  :short "Delete the @('loaditems') and @('parse-temps') fields from parsed
  structures.  This is a final cleaning step in @(see shadowcheck).")

(local (xdoc::set-default-parents deltemps))

(fty::defvisitor-template deltemps ((x :object))
  :returns (new-x :update)
  :prod-fns ((vl-blockstmt (loaditems (lambda (x) (declare (ignore x)) nil)))
             (vl-fundecl   (loaditems (lambda (x) (declare (ignore x)) nil)))
             (vl-taskdecl  (loaditems (lambda (x) (declare (ignore x)) nil)))
             (vl-module    (parse-temps (lambda (x) (declare (ignore x)) nil)))
             (vl-interface (parse-temps (lambda (x) (declare (ignore x)) nil))))
  :fnname-template <type>-deltemps)

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitors vl-design-deltemps
  :template deltemps
  :types (vl-design))



(defsection nameclash
  :parents (shadowcheck)
  :short "Check scopes for name clashes.")

(local (xdoc::set-default-parents nameclash))

(define vl-scopeitem->loc ((x vl-scopeitem-p))
  :returns (loc vl-location-p)
  :prepwork ((local (in-theory (enable vl-scopeitem-p tag-reasoning))))
  (let ((x (vl-scopeitem-fix x)))
    (case (tag x)
      ((:vl-genloop :vl-genif :vl-gencase :vl-genbegin :vl-genarray :vl-genbase)
       (vl-genelement->loc x))
      ((:vl-interfaceport)
       (vl-interfaceport->loc x))
      (t
       (vl-modelement->loc x)))))

(define vl-nameclash-collect-local-decls ((name  stringp)
                                          (alist vl-scopeitem-alist-p))
  :returns (items vl-scopeitemlist-p)
  :hooks nil
  (b* (((when (atom alist))
        nil)
       ((cons key val) (car alist))
       ((when (streqv key name))
        (cons (vl-scopeitem-fix val) (vl-nameclash-collect-local-decls name (cdr alist)))))
    (vl-nameclash-collect-local-decls name (cdr alist))))

(define vl-nameclash-collect-import-decls ((name  stringp)
                                           (alist vl-importresult-alist-p))
  :returns (items vl-importlist-p)
  :hooks nil
  (b* (((when (atom alist))
        nil)
       ((cons key val) (car alist))
       ((when (streqv key name))
        ;; Forge an import statement so we can easily print it
        (cons (b* (((vl-importresult val)))
                (make-vl-import :pkg val.pkg-name
                                :part name
                                :loc val.loc))
              (vl-nameclash-collect-import-decls name (cdr alist)))))
    (vl-nameclash-collect-import-decls name (cdr alist))))

(define vl-nameclash-warning-summary ((name    stringp)
                                      (locals  vl-scopeitem-alist-p)
                                      (imports vl-importresult-alist-p))
  :returns (summary stringp :rule-classes :type-prescription)
  ;; This should be rare, don't care about performance
  (b* ((name        (string-fix name))
       (locals      (vl-scopeitem-alist-fix locals))
       (imports     (vl-importresult-alist-fix imports))
       (localdecls  (vl-nameclash-collect-local-decls name locals))
       (importdecls (vl-nameclash-collect-import-decls name imports))
       (clashdecls  (append localdecls importdecls))
       ((unless (<= 2 (len clashdecls)))
        (raise "Programming error -- not actually a name clash? ~x0~%" name)
        "")
       (decl1 (first clashdecls))
       (decl2 (second clashdecls))
       (decl1.loc (if (eq (tag decl1) :vl-import)
                      (vl-import->loc decl1)
                    (vl-scopeitem->loc decl1)))
       (decl2.loc (if (eq (tag decl2) :vl-import)
                      (vl-import->loc decl2)
                    (vl-scopeitem->loc decl2))))
    (with-local-ps
      (vl-ps-update-autowrap-col 100)
      (vl-ps-update-autowrap-ind 10)
      (vl-print "name clash for ")
      (vl-print-str name)
      (vl-println ":")
      (vl-indent 6)
      (vl-print "  // From ")
      (vl-print-loc decl1.loc)
      (vl-println "")
      (vl-indent 6)
      (vl-cw "~a0~%" decl1)
      (vl-indent 6)
      (vl-print "  // From ")
      (vl-print-loc decl2.loc)
      (vl-println "")
      (vl-indent 6)
      (vl-cw "~a0~%" decl2)
      (if (atom (cddr clashdecls))
          ps
        (vl-ps-seq (vl-println "")
                   (vl-indent 6)
                   (vl-print "  // And ")
                   (vl-print-nat (- (len clashdecls) 2))
                   (vl-print " more (not shown).")))))

  :prepwork
  ((local (in-theory (enable tag-reasoning)))

   (local (defthm tag-when-vl-scopeitem-p
            (implies (vl-scopeitem-p x)
                     (not (equal (tag x) :vl-import)))))

   (local (defthm tag-of-car-when-vl-importlist-p
            (implies (vl-importlist-p x)
                     (equal (tag (car x))
                            (if (consp x)
                                :vl-import
                              nil)))))

   (local (in-theory (enable len)))))

(define vl-make-nameclash-warning ((scopename vl-maybe-scopeid-p)
                                   (clashname stringp "Some name that has a clash in this scope.")
                                   (locals    vl-scopeitem-alist-p)
                                   (imports   vl-importresult-alist-p)
                                   (warnings  vl-warninglist-p))
  :returns (new-warning vl-warninglist-p)
  (b* ((scopename (vl-maybe-scopeid-fix scopename)))
    (fatal :type :vl-name-clash
           :msg "In ~@0: ~s1"
           :args (list (cond ((stringp scopename) (vmsg scopename))
                             ((integerp scopename)
                              ;; this shouldn't happen
                              (vmsg "generate loop ~x0" scopename))
                             (t (vmsg "Unnamed scope")))
                       (vl-nameclash-warning-summary clashname locals imports)))))

(define vl-make-nameclash-warnings ((scopename  vl-maybe-scopeid-p)
                                    (clashnames string-listp "The names that have clashes in this scope.")
                                    (locals     vl-scopeitem-alist-p)
                                    (imports    vl-importresult-alist-p)
                                    (warnings   vl-warninglist-p))
  :returns (new-warning vl-warninglist-p)
  (b* (((when (atom clashnames))
        (ok))
       (warnings (vl-make-nameclash-warning scopename (car clashnames) locals imports warnings)))
    (vl-make-nameclash-warnings scopename (cdr clashnames) locals imports warnings)))

(define vl-strip-locs-from-importresult-alist ((x vl-importresult-alist-p))
  :returns (new-x vl-importresult-alist-p)
  :hooks nil
  (b* (((when (atom x))
        nil)
       ((cons key val) (car x)))
    (cons (cons (string-fix key)
                (change-vl-importresult val :loc *vl-fakeloc*))
          (vl-strip-locs-from-importresult-alist (cdr x)))))


(defsection generate-block-nameclash-items
  :parents (vl-scope-nameclash-warnings)
  :short "Special detection of name clashes involving generate block names."
  :long "<p>Here we are trying to defend against NOT OK things such as:</p>

@({
     wire foo;
     if (version == 1)
     begin : foo
       ...
     end
})

<p>Note that the above is NOT OK even if @('version != 1'), i.e., even if the
block is not going to exist after elaboration.  See failtest/gen1*.v for many
informative and related tests.</p>

<p>For everything else, our nameclash handling basically works as follows.  For
any arbitrary scope, check for name clashes by:</p>

<ul>
<li>collecting up its scopeitem-alist, then</li>
<li>checking it for duplicate keys.</li>
</ul>

<p>This works for almost everything (wire names, module instance names, port
names, etc.), but our scopeitem-alist building code only collects the names
from top-level named genblocks and genarrays.  This makes perfect sense in
post-elaboration contexts where any conditional generates have been eliminated,
but it isn't right for us here because it doesn't get things like @('foo')
above.  That is, it doesn't get any named blocks that occur as loop bodies, or
under if/case constructs.</p>

<p>That's actually good.  It's needs to be OK to have things like this:</p>

@({
    if (version == 1)
    begin : foo
      ...
    end
    else if (version == 2)
    begin : foo              <--- no name clash with foo from above
      ...
    end
})

<p>So if scopeitem-alist collection was ``smarter'' and somehow dived down into
the if/else blocks, we might think that there was a name clash for @('foo'),
which there isn't.</p>

<p>Anyway, our goal here is basically to augment the scopeitem-alist that we
would normally produce with a supplemental scopeitem alist that accounts for
the named blocks within any if/case/loop generate constructs.</p>"
  :autodoc nil

  (local (xdoc::set-default-parents generate-block-nameclash-items))

  (define vl-scope->raw-generates ((x vl-scope-p))
    :short "Get the raw list of generate statements from any scope."
    :returns (generates vl-genelementlist-p)
    (let ((x (vl-scope-fix x)))
      (case (tag x)
        (:vl-interface  (vl-interface->generates x))
        (:vl-module     (vl-module->generates x))
        (:vl-genblob    (vl-genblob->generates x))
        (:vl-blockscope nil)
        (:vl-design     nil)
        (:vl-package    nil)
        (:vl-scopeinfo  nil)
        (otherwise      (impossible)))))

  (define vl-delete-duplicated-genelement-blocknames ((alist vl-scopeitem-alist-p))
    :returns (filtered-alist vl-scopeitem-alist-p)
    (b* ((alist (vl-scopeitem-alist-fix alist))
         (names (alist-keys alist))
         (dupes (duplicated-members names)))
      (vl-remove-keys dupes alist))
    :prepwork
    ((local (defthm vl-scopeitem-alist-p-of-vl-remove-keys
              (implies (vl-scopeitem-alist-p alist)
                       (vl-scopeitem-alist-p (vl-remove-keys keys alist)))
              :hints(("Goal" :in-theory (enable vl-remove-keys)))))))

  (defines vl-genelementlist->nameclash-scopeitem-alist
    :verify-guards nil
    (define vl-genelementlist->nameclash-scopeitem-alist ((x       vl-genelementlist-p)
                                                          (nestedp booleanp))
      :returns (alist vl-scopeitem-alist-p)
      :measure (vl-genelementlist-count x)
      (if (atom x)
          nil
        (append (vl-genelement->nameclash-scopeitem-alist (car x) nestedp)
                (vl-genelementlist->nameclash-scopeitem-alist (cdr x) nestedp))))

    (define vl-genelement->nameclash-scopeitem-alist ((x       vl-genelement-p)
                                                      (nestedp booleanp))
      :returns (alist vl-scopeitem-alist-p)
      :measure (vl-genelement-count x)
      (b* ((x (vl-genelement-fix x)))
        (vl-genelement-case x
          :vl-genbase
          nil
          :vl-genarray
          ;; These shouldn't even be introduced until after elaboration, so we
          ;; shouldn't need to worry about them.  Could cause a warning here.
          nil
          :vl-genbegin
          ;; If we aren't nested in some if/case/loop context, then the name
          ;; should be picked up for us by the ordinary scopeitem-alist
          ;; construction.  If we are nested, then get the name.  No need to dive
          ;; into the body because of course the begin/end creates its own scope.
          (and nestedp
               (let ((name (vl-genblock->name x.block)))
                 (and (stringp name)
                      (list (cons name x)))))
          :vl-genif
          ;; Collect the block names that are visible in this scope, then
          ;; delete any duplicates (because, if present, they're in different
          ;; if branches.)
          (vl-delete-duplicated-genelement-blocknames
           (append (vl-genblock-under-cond->nameclash-scopeitem-alist x.then)
                   (vl-genblock-under-cond->nameclash-scopeitem-alist x.else)))
          :vl-gencase
          ;; Similar to the genif case.
          (vl-delete-duplicated-genelement-blocknames
           (append (vl-gencaselist->nameclash-scopeitem-alist x.cases)
                   (vl-genblock-under-cond->nameclash-scopeitem-alist x.default)))
          :vl-genloop
          ;; Just want to get the body's name, if any.  I considered also getting
          ;; the generate variable name in the case of x.genvarp, however that
          ;; doesn't seem correct.  For instance, consider cosims/generate10; we
          ;; find that it's OK to do:
          ;;    for(genvar i = ...) ...;
          ;;    for(genvar i = ...) ...;
          ;; So it doesn't seem like such a genvar should be considered to take
          ;; part in the scope that is outside the for loop.
          (let ((name (vl-genblock->name x.body)))
            (and (stringp name)
                 (list (cons name x)))))))

    (define vl-genblock-under-cond->nameclash-scopeitem-alist ((x vl-genblock-p))
      :returns (alist vl-scopeitem-alist-p)
      :measure (vl-genblock-count x)
      (b* (((vl-genblock x))
           ((when (stringp x.name))
            ;; Get this block's name, but don't need to go inside the block
            ;; because it is a new scope.
            (list (cons x.name (make-vl-genbegin :block x))))
           ((when x.condnestp)
            ;; Special case where this block doesn't introduce a scope.  Just
            ;; collect block names from inside its elements.
            (vl-genelementlist->nameclash-scopeitem-alist x.elems t)))
        ;; Else, this is an unnamed block that nevertheless creates its own
        ;; scope, so we don't need to do anything.
        nil))

    (define vl-gencaselist->nameclash-scopeitem-alist ((x vl-gencaselist-p))
      :returns (alist vl-scopeitem-alist-p)
      :measure (vl-gencaselist-count x)
      (b* ((x (vl-gencaselist-fix x))
           ((when (atom x))
            nil)
           ((cons ?exprs1 block1) (car x)))
        (append (vl-genblock-under-cond->nameclash-scopeitem-alist block1)
                (vl-gencaselist->nameclash-scopeitem-alist (cdr x)))))
    ///
    (verify-guards vl-genelementlist->nameclash-scopeitem-alist)
    (deffixequiv-mutual vl-genelementlist->nameclash-scopeitem-alist)))



(define vl-scope-nameclash-warnings ((x        vl-scope-p)
                                     (design   vl-design-p)
                                     (warnings vl-warninglist-p))
  :short "Top level function for checking a scope for name clashes."
  :returns (warnings vl-warninglist-p)
  (b* ((x      (vl-scope-fix x))
       (design (vl-design-fix design))
       ((vl-scopeinfo info)
        ;; We use the aux function directly because we don't actually need
        ;; these alists to be fast.  (We explicitly need to consider shadowed
        ;; pairs to detect duplicates.)
        (vl-scope->scopeinfo-aux x design))
       (tricky-generate-stuff (vl-genelementlist->nameclash-scopeitem-alist (vl-scope->raw-generates x)
                                                                            nil))
       (locals (append tricky-generate-stuff info.locals))
       (locally-declared-names  (alist-keys locals))
       (directly-imported-names
        ;; Subtle.  We don't want to complain about multiple imports of some
        ;; name from the same package, e.g., "import foo::bar; import
        ;; foo::bar;" should only count as a single import.  So, instead of
        ;; blindly collecting all of the imported names, first eliminate any
        ;; redundant imports.  This is slightly tricky because we need to
        ;; ignore locations, so strip them out first.
        (alist-keys (mergesort (vl-strip-locs-from-importresult-alist info.imports))))
       (dupes (duplicated-members (append locally-declared-names directly-imported-names)))
       ((unless dupes)
        (ok)))
    (vl-make-nameclash-warnings
     ;; BOZO consider working harder to provide "Unnamed scope at filename:line..." or similar
     (vl-scope->id x)
     dupes locals info.imports warnings))

  :prepwork
  ((local (defthm string-listp-of-alist-keys-when-vl-scopeitem-alist-p
            (implies (vl-scopeitem-alist-p x)
                     (string-listp (alist-keys x)))
            :hints(("Goal" :induct (len x)))))

   (local (defthm string-listp-of-alist-keys-when-vl-importresult-alist-p
            (implies (vl-importresult-alist-p x)
                     (string-listp (alist-keys x)))
            :hints(("Goal" :induct (len x)))))))



(defxdoc shadowcheck
  :parents (make-implicit-wires)
  :short "Sanity check to detect undeclared identifiers, name clashes, and
tricky kinds of global name shadowing that we don't support."

  :long "<p>In some Verilog tools, top-level and imported declarations can
sometimes be shadowed by local declarations for only part of a module.  For
instance,</p>

@({
    parameter foo = 1;

    module m ();
      logic [3:0] a = foo;     // references the global foo
      parameter foo = 2;
      logic [3:0] b = foo;     // references the local foo
    endmodule
})

<p>Throughout VL we generally abstract away from the parse order and expect to
be able to traverse scopes in a simple set-like way; see @(see scopestack).
This approach makes supporting this kind of lexical shadowing a challenge.  To
avoid any problems due to this kind of shadowing, we implement a special check
to prohibit globals from being used before they are locally declared.</p>

<p>This checking depends on the parse order.  It occurs as part of the @(see
make-implicit-wires) transform.  Note that we do this checking after we have
already introduced implicit wires, so we can assume that implicit wires have
explicit declarations.</p>")

(local (xdoc::set-default-parents shadowcheck))

(defprod vl-lexscope-entry
  :parents (vl-lexscope)
  :tag :vl-lexscope-entry
  :layout :tree
  :short "Information about a single name in a lexical scope."
  ((decl       any-p
               "Non-nil indicates that there has been (at least one) explicit
                declaration of this name in this scope.  In this case,
                @('decl') is the corresponding declaration; it might be a @(see
                vl-portdecl), a @(see vl-vardecl), a @(see vl-fundecl), etc.")
   (direct-pkg maybe-stringp
               :rule-classes :type-prescription
               "When non-nil, this entry is directly import from the package
                name @('direct-pkg'), i.e., @('import foo::bar').")
   (wildpkgs   string-listp
               "This entry is imported via @('import foo::*') statements from
                each of packages named in @('wildpkgs').")
   (genblockp booleanp
              :rule-classes :type-prescription
              "Non-nil indicates that this is a generate block and therefore
               may not be present in the scopestack.")))

(fty::defalist vl-lexscope
  :short "Representation of a single, partial, lexical scope."
  :long "<p>We always expect lexscopes to be fast alists.</p>"
  :key-type stringp
  :val-type vl-lexscope-entry)

(define vl-empty-lexscope ()
  :returns (scope vl-lexscope-p)
  :parents (vl-lexscope)
  :short "Create a new, empty lexical scope."
  :inline t
  nil)

(define vl-lexscope-find ((name  stringp)
                          (scope vl-lexscope-p))
  :returns (entry (iff (vl-lexscope-entry-p entry) entry))
  :parents (vl-lexscope)
  :short "Look up a name in a (single) lexical scope."
  :inline t
  (cdr (hons-get (string-fix name) (vl-lexscope-fix scope)))
  :prepwork
  ((local (defthm l0
            (implies (vl-lexscope-p scope)
                     (iff (cdr (hons-assoc-equal name scope))
                          (hons-assoc-equal name scope)))
            :hints(("Goal" :induct (len scope)))))))

(fty::deflist vl-lexscopes
  :elt-type vl-lexscope-p
  :short "A stack of lexical scopes.")

(define vl-lexscopes-enter-new-scope ((scopes vl-lexscopes-p))
  :parents (vl-lexscopes)
  :returns (scopes vl-lexscopes-p)
  :short "Push a new scope onto the lexical scope stack."
  :long "<p>This should be called when entering a module, function, block, etc.</p>"
  :inline t
  (cons (vl-empty-lexscope)
        (vl-lexscopes-fix scopes)))

(define vl-lexscopes-exit-scope ((scopes vl-lexscopes-p))
  :returns (scopes vl-lexscopes-p)
  :parents (vl-lexscopes)
  :short "Pop the current scope off of the lexical scope stack and free fast alists."
  :long "<p>This should be called when exiting a module, function, block, etc.</p>"
  (b* ((scopes (vl-lexscopes-fix scopes))
       ((when (atom scopes))
        (raise "Expected at least one lexscope."))
       ((cons head tail) scopes))
    (fast-alist-free head)
    tail))

(define vl-lexscopes-find ((name   stringp)
                           (scopes vl-lexscopes-p))
  :returns (mv (entry (iff (vl-lexscope-entry-p entry) entry)
                      "Entry for this name, if it is declared.")
               (tail  vl-lexscopes-p
                      "The tail of @('scopes') starting with the scope for this
                       name."))
  :parents (vl-lexscopes)
  :short "Recursively look up a name, going from inner to outer lexical scopes."
  :measure (len scopes)
  (b* ((name   (string-fix name))
       (scopes (vl-lexscopes-fix scopes))
       ((when (atom scopes))
        (mv nil nil))
       (entry (vl-lexscope-find name (car scopes)))
       ((when entry)
        (mv entry scopes)))
    (vl-lexscopes-find name (cdr scopes))))


(define vl-lexscopes-declare-name ((name     stringp)
                                   (decl     any-p)
                                   (scopes   vl-lexscopes-p)
                                   (warnings vl-warninglist-p)
                                   &key (genblockp booleanp))
  :returns (mv (scopes   vl-lexscopes-p)
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a local declaration."
  (b* ((name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom scopes))
        (raise "Expected at least one scope.")
        (mv scopes warnings))

       (scope1 (car scopes))
       (entry  (vl-lexscope-find name scope1))

       ((unless entry)
        ;; Completely new declaration, can't possibly conflict with anything.
        ;; No information to merge.  Just add a new entry to the scope.
        (mv (cons (hons-acons name
                              (make-vl-lexscope-entry :decl       decl
                                                      :direct-pkg nil
                                                      :wildpkgs   nil
                                                      :genblockp genblockp)
                              scope1)
                  (cdr scopes))
            warnings))

       ((vl-lexscope-entry entry))

       ;; We don't try to defend against multiple local declarations.  We will
       ;; check that separately, at the whole-scope level, where it is easy to
       ;; do so correctly.  It would be complicated to do it here, for modules,
       ;; because of, e.g., the allowed overlap between port and variable
       ;; declarations.
       ;;
       ;; We also don't try defend against conflicts with wildcard imports
       ;; here.  That's only a problem if a multiply imported name is actually
       ;; used.  So we'll check for that when names are used.
       ;;
       ;; However, we can at least try to defend against conflicts between
       ;; local declarations and direct imports of the same name.
       (warnings
        (if entry.direct-pkg
            (fatal :type :vl-name-clash
                   :msg "~a0: can't declare ~s1 after importing it from ~s2."
                   :args (list decl name entry.direct-pkg))
          (ok)))

       ;; The new entry we construct should preserve information if possible.
       ;; In the case of multiple declarations, we'll arbitrarily choose to
       ;; keep the earliest declaration.
       (new-entry  (change-vl-lexscope-entry entry :decl (or entry.decl decl)))
       (new-scope1 (hons-acons name new-entry scope1))
       (new-scopes (cons new-scope1 (cdr scopes))))
    (mv new-scopes warnings)))


(define vl-lexscopes-direct-import-name ((pkgname  stringp "Name of the package being imported from.")
                                         (name     stringp "Name being directly imported from the package.")
                                         (scopes   vl-lexscopes-p)
                                         (ctx      vl-import-p)
                                         (warnings vl-warninglist-p))
  :returns (mv (scopes   vl-lexscopes-p)
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a direct import of a single name."
  (b* ((pkgname  (string-fix pkgname))
       (name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (ctx      (vl-import-fix ctx))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom scopes))
        (raise "Expected at least one scope.")
        (mv scopes warnings))

       (scope1   (car scopes))
       (entry    (vl-lexscope-find name scope1))
       ((unless entry)
        ;; Completely new declaration, can't possibly conflict with anything.
        ;; No information to merge.  Just add a new entry to the scope.
        (mv (cons (hons-acons name
                              (make-vl-lexscope-entry :direct-pkg pkgname
                                                      :decl nil
                                                      :wildpkgs nil)
                              scope1)
                  (cdr scopes))
            warnings))

       ((vl-lexscope-entry entry))

       (warnings
        (if entry.decl
            (fatal :type :vl-name-clash
                   :msg "~a0: can't import ~s1 after locally declaring it (~a2)."
                   :args (list ctx name entry.decl))
          warnings))

       (warnings
        (if (and entry.direct-pkg
                 ;; It seems pretty reasonable to redundantly
                 ;;   import foo::bar;
                 ;;   import foo::bar;
                 ;; and tools like NCVerilog and VCS accept this without complaint.
                 (not (equal entry.direct-pkg pkgname)))
            (fatal :type :vl-name-clash
                   :msg "~a0: can't import ~s1 from ~s2 after previously importing ~
                         it from ~s3."
                   :args (list ctx name pkgname entry.direct-pkg))
          warnings))

       (new-entry
        (if (or entry.decl entry.direct-pkg)
            ;; This is redundant or a fatal error, so it doesn't really matter
            ;; what we do.  We'll arbitrarily say the previous declaration
            ;; wins.
            entry
          (change-vl-lexscope-entry entry :direct-pkg pkgname)))

       (new-scope1 (hons-acons name new-entry scope1))
       (new-scopes (cons new-scope1 (cdr scopes))))
    (mv new-scopes warnings)))


(define vl-lexscopes-wild-import-name ((pkgname  stringp "Name of the package being imported from.")
                                       (name     stringp "Single name declared in the package.")
                                       (scopes   vl-lexscopes-p)
                                       (ctx      vl-import-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (scopes   vl-lexscopes-p)
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a wildcard import of a single name."
  (declare (ignorable ctx))
  (b* ((pkgname  (string-fix pkgname))
       (name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom scopes))
        (raise "Expected at least one scope.")
        (mv scopes warnings))

       (scope1   (car scopes))
       (entry    (vl-lexscope-find name scope1))
       ((unless entry)
        ;; Completely new declaration, can't possibly conflict with anything.
        ;; No information to merge.  Just add a new entry to the scope.
        (mv (cons (hons-acons name
                              (make-vl-lexscope-entry :decl nil
                                                      :direct-pkg nil
                                                      :wildpkgs (list pkgname))
                              scope1)
                  (cdr scopes))
            warnings))

       ((vl-lexscope-entry entry))
       ((when (member-equal pkgname entry.wildpkgs))
        ;; Already imported from this package, so noop.
        (mv scopes warnings))
       ;; I don't think we want to warn about anything here.  Just extend the
       ;; list of wild packages.
       (new-entry  (change-vl-lexscope-entry entry :wildpkgs (cons pkgname entry.wildpkgs)))
       (new-scope1 (hons-acons name new-entry scope1))
       (new-scopes (cons new-scope1 (cdr scopes))))
    (mv new-scopes warnings)))


(local
 (defsection string-listp-of-alist-keys-of-vl-package-scope-item-alist

   (local (defthm l0
            (equal (string-listp (alist-keys (vl-typedeflist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-typedeflist-alist)))))

   (local (defthm l1
            (equal (string-listp (alist-keys (vl-taskdecllist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-taskdecllist-alist)))))

   (local (defthm l2
            (equal (string-listp (alist-keys (vl-fundecllist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-fundecllist-alist)))))

   (local (defthm l3
            (equal (string-listp (alist-keys (vl-vardecllist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-vardecllist-alist)))))

   (local (defthm l4
            (equal (string-listp (alist-keys (vl-paramdecllist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-paramdecllist-alist)))))

   (local (defthm l5
            (equal (string-listp (alist-keys (vl-dpiimportlist-alist x acc)))
                   (string-listp (alist-keys acc)))
            :hints(("Goal" :in-theory (enable vl-dpiimportlist-alist)))))

   (defthm string-listp-of-alist-keys-of-vl-package-scope-item-alist
     (equal (string-listp (alist-keys (vl-package-scope-item-alist x acc)))
            (string-listp (alist-keys acc)))
     :hints(("Goal" :in-theory (enable vl-package-scope-item-alist))))))


(define vl-lexscopes-wild-import-names ((pkgname  stringp      "Name of the package being imported from.")
                                        (pkg-item-alist "Goofy, we only care about the names, but we take
                                                         the whole alist to reuse @(see vl-package-scope-item-alist).")
                                        (scopes   vl-lexscopes-p)
                                        (ctx      vl-import-p)
                                        (warnings vl-warninglist-p))
  :guard   (string-listp (alist-keys pkg-item-alist))
  :returns (mv (scopes   vl-lexscopes-p)
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a wildcard import of a list of names."
  (declare (ignorable ctx))
  (b* (((when (atom pkg-item-alist))
        (mv (vl-lexscopes-fix scopes) (vl-warninglist-fix warnings)))
       ((when (atom (car pkg-item-alist)))
        (vl-lexscopes-wild-import-names pkgname (cdr pkg-item-alist) scopes ctx warnings))
       ((mv scopes warnings)
        (vl-lexscopes-wild-import-name pkgname (caar pkg-item-alist) scopes ctx warnings)))
    (vl-lexscopes-wild-import-names pkgname (cdr pkg-item-alist) scopes ctx warnings)))

(local (defthm stringp-when-vl-importpart-p
         (implies (vl-importpart-p x)
                  (equal (stringp x)
                         (not (equal x :vl-import*))))
         :hints(("Goal" :in-theory (enable vl-importpart-p)))))

(define vl-lexscopes-do-import ((x        vl-import-p)
                                (scopes   vl-lexscopes-p)
                                (warnings vl-warninglist-p)
                                (design   vl-design-p))
  :returns (mv (scopes   vl-lexscopes-p)
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a package import."
  (b* (((vl-import x) (vl-import-fix x))
       (scopes        (vl-lexscopes-fix scopes))
       (warnings      (vl-warninglist-fix warnings))

       ((when (atom scopes))
        (raise "Expected at least one scope.")
        (mv scopes warnings))

       (pkg      (vl-find-package x.pkg (vl-design->packages design)))
       (warnings (if pkg
                     warnings
                   (fatal :type :vl-bad-import
                          :msg "~a0: trying to import from undefined package ~s1."
                          :args (list x x.pkg))))

       (pkg-item-alist (and pkg (vl-package-scope-item-alist-top pkg)))

       ((unless (eq x.part :vl-import*))
        (b* ((item     (hons-get x.part pkg-item-alist))
             (warnings (if item
                           warnings
                         (fatal :type :vl-bad-import
                                :msg "~a0: no declaration of ~s1 in package ~s2."
                                :args (list x x.part x.pkg)))))
          ;; If the item wasn't found, it doesn't really matter what we do
          ;; because we caused a fatal error already.  It seems basically
          ;; reasonable to pretend that we imported it successfully, so we can
          ;; check subsequent uses of it.
          (vl-lexscopes-direct-import-name x.pkg x.part scopes x warnings))))

    (vl-lexscopes-wild-import-names x.pkg pkg-item-alist scopes x warnings)))


(defprod vl-shadowcheck-state
  :tag :vl-shadowcheck-state
  :layout :tree
  ((lexscopes vl-lexscopes-p
              "Lexical scopes, current up to this point.")
   (ss        vl-scopestack-p
              "Proper scopestack with all implicit variables already added to it, and
               updated with whatever scopes we've descended through pushed onto it.")
   (design    vl-design-p
              "Original design.")))

(define vl-shadowcheck-push-scope ((x        vl-scope-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  ;; Like vl-scopestack-push but for shadowcheck states.
  ;;  - Extends the scopestack by doing a push
  ;;  - Extends the lexscopes with a new, empty scope
  ;;  - Checks the new scope for name clashes
  (b* (((vl-shadowcheck-state st))
       (st (change-vl-shadowcheck-state st
                                        :lexscopes (vl-lexscopes-enter-new-scope st.lexscopes)
                                        :ss        (vl-scopestack-push x st.ss)))
       (warnings (vl-scope-nameclash-warnings x (vl-shadowcheck-state->design st) warnings)))
    (mv st warnings)))

(define vl-shadowcheck-pop-scope ((st vl-shadowcheck-state-p))
  :returns (st vl-shadowcheck-state-p)
  (b* (((vl-shadowcheck-state st)))
    (change-vl-shadowcheck-state st
                                 :lexscopes (vl-lexscopes-exit-scope st.lexscopes)
                                 :ss        (vl-scopestack-pop st.ss))))

(define vl-shadowcheck-declare-name ((name     stringp)
                                     (decl     any-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p)
                                     &key
                                     (genblockp booleanp))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-shadowcheck-state st))
       (- (vl-shadowcheck-debug "    vl-shadowcheck-declare-name: ~s0 for ~a1.~%" name decl))
       ((mv lexscopes warnings)
        (vl-lexscopes-declare-name name decl st.lexscopes warnings :genblockp genblockp))
       ;; I don't think we need to particularly do any cross-checking here.  By
       ;; extending the lexscope we will have checked for import/decl
       ;; conflicts, and we should be checking for redeclaration conflicts
       ;; elsewhere, so what else is there to do?
       (st (change-vl-shadowcheck-state st :lexscopes lexscopes)))
    (mv st warnings)))

(define vl-shadowcheck-declare-names ((names    string-listp)
                                      (decl     any-p)
                                      (st       vl-shadowcheck-state-p)
                                      (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-state-fix st) (vl-warninglist-fix warnings)))
       ((mv st warnings) (vl-shadowcheck-declare-name (car names) decl st warnings)))
    (vl-shadowcheck-declare-names (cdr names) decl st warnings)))

(define vl-shadowcheck-import ((x        vl-import-p)
                               (st       vl-shadowcheck-state-p)
                               (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-shadowcheck-state st))
       (- (vl-shadowcheck-debug "    vl-shadowcheck-import: importing ~a0.~%" x))
       ((mv lexscopes warnings)
        (vl-lexscopes-do-import x st.lexscopes warnings st.design))
       ;; I don't think there's anything else to check here?
       (st (change-vl-shadowcheck-state st :lexscopes lexscopes)))
    (mv st warnings)))

(define vl-shadowcheck-reference-name ((name     stringp)
                                       (ctx      any-p)
                                       (st       vl-shadowcheck-state-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((name                      (string-fix name))
       ((vl-shadowcheck-state st) (vl-shadowcheck-state-fix st))

       (- (vl-shadowcheck-debug "    vl-shadowcheck-reference-name: ~s0 for ~a1.~%" name ctx))

       ((mv entry tail) (vl-lexscopes-find name st.lexscopes))
       ((unless entry)
        ;; Reference to something that isn't lexically defined.  I think it
        ;; seems reasonable to complain about this now?  This might not be
        ;; quite right if we need to be allowed to refer to things that we
        ;; aren't consider items, like $bits(foo_t) or similar.
        (mv st
            (warn :type :vl-warn-undeclared
                   :msg "~a0: reference to undeclared identifier ~s1.~%"
                   :args (list ctx name))))
       ((vl-lexscope-entry entry))

       ((when (and (not entry.decl)
                   (not entry.direct-pkg)
                   (>= (len entry.wildpkgs) 2)))
        (mv st
            (fatal :type :vl-bad-import
                   :msg "~a0: the name ~s1 is imported by multiple wildcard ~
                         imports: ~&2."
                   :args (list ctx name entry.wildpkgs))))

       ((mv item scopestack-at-import pkg-name)
        (vl-scopestack-find-item/context name st.ss))
       ((unless (or item pkg-name))
        (if entry.genblockp
            ;; If it's the name of a generate block (in a loop/if/case) then it
            ;; won't be found in the scopestack.
            (mv st (ok))
          (mv st
              (fatal :type :vl-programming-error
                     :msg "~a0: scopestack can't resolve ~s1 but it is found ~
                         in the lexical scope, so how could that happen? ~x2."
                     :args (list ctx name entry)))))

       ((unless pkg-name)
        ;; Scopestack doesn't think this is imported from a package.
        (b* (((unless entry.decl)
              ;; Lexscope thinks it's imported from a package.  Wtf.
              (mv st (warn :type :vl-tricky-scope
                            :msg "~a0: the name ~s1 has complex scoping that ~
                                  we do not support.  Lexically it appears to ~
                                  be imported from a package, but there is a ~
                                  subsequent declaration (~a2) which makes ~
                                  scoping confusing."
                            :args (list ctx name item))))

             ;; Nobody thinks this is imported from a package.  That means
             ;; it comes from the local scope or some superior scope.  Make
             ;; sure that scopestack and lexscope agree on which scope it
             ;; is coming from, i.e., scopestack isn't getting it from the
             ;; local scope while lexscope is looking above.  ("Shadowed")
             (ss-level  (vl-scopestack-nesting-level scopestack-at-import))
             (lex-level (len tail))
             ((when (and entry.genblockp (< ss-level lex-level)))
              ;; This is OK -- we have a genblock in this scope and the name is
              ;; also bound in a superior scope.
              (mv st (ok)))

             ((unless (equal ss-level lex-level))
              (mv st
                  (warn :type :vl-tricky-scope
                        :msg "~a0: the name ~s1 has complex scoping that we ~
                               do not support.  Lexical level ~x2, scopestack ~
                               level ~x3."
                        :args (list ctx name lex-level ss-level))))

             ((when entry.genblockp)
              ;; Scopestack has an entry for this but it's also a generate
              ;; block.
              (mv st (warn :type :vl-tricky-scope
                           :msg "~a0: the name ~s1 is bound to ~a2 but it is ~
                                 also the name of a generate block in the ~
                                 same scope."
                           :args (list ctx name item)))))

          ;; Looks like a match.
          (mv st (ok))))

       ;; Scopestack thinks the item comes from a package.
       ;; If scopestack gave us ITEM, it's the actual item from that package
       ;; If ITEM is nil, then either:
       ;;  - we found an import of foo::bar, but either bar isn't defined in
       ;;    that package, or foo doesn't exist.
       ;;  - we found an import of foo::*, but foo doesn't exist.
       ((when entry.genblockp)
        (mv st (warn :type :vl-tricky-scope
                     :msg "~a0: the name ~s1 might be imported from package ~
                           ~s2 (item: ~a3), but it is also the name of a ~
                           generate block."
                     :args (list ctx name pkg-name item))))

       ((when entry.decl)
        (mv st (fatal :type :vl-programming-error
                      :msg "~a0: scopestack thinks ~s1 is imported from ~s2 ~
                            but lexically it seems to be locally declared, ~
                            ~a3."
                      :args (list ctx name pkg-name entry.decl))))

       ((when entry.direct-pkg)
        ;; Lexically we think it's imported from foo::bar.  Scopestack also
        ;; thinks it comes from a package.
        (b* (((unless (equal entry.direct-pkg pkg-name))
              (mv st (warn :type :vl-tricky-scope
                            :msg "~a0: scopestack thinks ~s1 is imported from ~
                                  ~s2, but lexically it is directly imported from ~s3."
                            :args (list ctx name pkg-name entry.direct-pkg)))))
          ;; Otherwise, we're totally ok.  We know there's no local declaration
          ;; lexically, scopestack says it comes from the same package, etc.
          (mv st (ok))))

       ;; The only other case is that there's some import foo::*.  We've
       ;; already checked above that there aren't multiple such imports.
       ((unless (consp entry.wildpkgs))
        (mv st (fatal :type :vl-programming-error
                      :msg "~a0: name ~s1 has a lexscope entry with no local ~
                            declaration, direct package, or wild packages.  ~
                            How did this happen?"
                      :args (list ctx name))))

       (lex-pkg (and (mbt (equal (len entry.wildpkgs) 1)) ;; because we checked above
                     (first entry.wildpkgs)))
       ((unless (equal lex-pkg pkg-name))
        (mv st (warn :type :vl-tricky-scope
                      :msg "~a0: scopestack thinks ~s1 is imported from ~s2, ~
                            but lexically it is wildly imported from ~s3."
                      :args (list ctx name pkg-name lex-pkg)))))

    ;; If we get here, all package sanity checks pass.  We're good to go.
    (mv st (ok))))


(define vl-shadowcheck-reference-scopeexpr ((x        vl-scopeexpr-p)
                                            (ctx      any-p)
                                            (st       vl-shadowcheck-state-p)
                                            (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((st (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings)))
    (vl-scopeexpr-case x
      :colon (mv st warnings) ;; No warnings about package-scoped stuff
      :end
      (vl-hidexpr-case x.hid
        :end (vl-shadowcheck-reference-name x.hid.name ctx st warnings)
        :dot
        (b* ((name (vl-hidindex->name x.hid.first))
             ((unless (stringp name))
              ;; don't check $root
              (mv st warnings))
             ((vl-shadowcheck-state st))
             ((when (vl-scopestack-find-definition name st.ss))
              ;; Might be a hierarchical reference to a top-level definition
              (mv st warnings)))
          (vl-shadowcheck-reference-name name ctx st warnings))))))

(define vl-shadowcheck-reference-names ((names    string-listp)
                                        (ctx      any-p)
                                        (st       vl-shadowcheck-state-p)
                                        (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings)
        (vl-shadowcheck-reference-name (car names) ctx st warnings)))
    (vl-shadowcheck-reference-names (cdr names) ctx st warnings)))





(define vl-expr->maybe-subtype ((x vl-expr-p))
  :returns (subtype vl-maybe-datatype-p)
  (vl-expr-case x
    :vl-literal nil
    :vl-index nil
    :vl-unary nil
    :vl-binary nil
    :vl-qmark nil
    :vl-concat nil
    :vl-multiconcat nil
    :vl-mintypmax nil
    :vl-call x.typearg
    :vl-stream nil
    :vl-cast nil
    :vl-inside nil
    :vl-tagged nil
    :vl-pattern x.pattype
    :vl-special nil
    :vl-eventexpr nil)
  ///
  (defret vl-maybe-datatype-count-of-vl-expr->maybe-subtype
    (< (vl-maybe-datatype-count subtype)
       (vl-expr-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :expand ((vl-expr-count x))))))

(defines vl-shadowcheck-expr
  :verify-guards nil

;; Intuitive goal: check all the names that are referenced by an expression, so
;; that we can make sure that when we look them up in the scopestack, we find
;; the same thing as in the lexscopes.  For example, if the expression is a +
;; b, then we want to check the names "a" and "b".
;;
;; Complicating this, what if our expression is foo.bar + b?  This might be
;; referring to a top-level module foo, or it might refer to a submodule of the
;; current module.  It seems that hierarchical identifiers are generally
;; resolved non-lexically, i.e., we may look at the whole local scope and
;; finding things that occur afterward; also foo might refer to a top-level
;; module or be some upward hierarchical reference.  So, at least for now,
;; don't check hierarchical names for checking shadowing.

  (define vl-shadowcheck-expr ((x        vl-expr-p)
                               (ctx      any-p)
                               (st       vl-shadowcheck-state-p)
                               (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-expr-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((mv st warnings)
          (vl-expr-case x
            :vl-index
            (vl-shadowcheck-reference-scopeexpr x.scope ctx st warnings)
            :otherwise
            (mv st warnings)))
         ((mv st warnings)
          (vl-shadowcheck-maybe-datatype (vl-expr->maybe-subtype x) ctx st warnings)))
      (vl-shadowcheck-exprlist (vl-expr->subexprs x) ctx st warnings)))

  (define vl-shadowcheck-maybe-expr ((x        vl-maybe-expr-p)
                                     (ctx      any-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-maybe-expr-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((unless x)
          (mv st warnings)))
      (vl-shadowcheck-expr x ctx st warnings)))

  (define vl-shadowcheck-exprlist ((x        vl-exprlist-p)
                                   (ctx      any-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-exprlist-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((mv st warnings) (vl-shadowcheck-expr (car x) ctx st warnings)))
      (vl-shadowcheck-exprlist (cdr x) ctx st warnings)))

  (define vl-shadowcheck-datatype ((x        vl-datatype-p)
                                   (ctx      any-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-datatype-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings)))
      (vl-datatype-case x
        :vl-coretype
        (b* (((mv st warnings) (vl-shadowcheck-dimensionlist x.pdims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.udims ctx st warnings)))
          (mv st warnings))
        :vl-struct
        (b* (((mv st warnings) (vl-shadowcheck-dimensionlist x.pdims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.udims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-structmemberlist x.members ctx st warnings)))
          (mv st warnings))
        :vl-union
        (b* (((mv st warnings) (vl-shadowcheck-dimensionlist x.pdims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.udims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-structmemberlist x.members ctx st warnings)))
          (mv st warnings))
        :vl-enum
        (b* (((mv st warnings) (vl-shadowcheck-dimensionlist x.pdims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.udims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-enumitemlist x.items ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-datatype x.basetype ctx st warnings)))
          (mv st warnings))
        :vl-usertype
        (b* (((mv st warnings)
              (if (vl-idscope-p x.name)
                  (vl-shadowcheck-reference-name (vl-idscope->name x.name) ctx st warnings)
                (mv st warnings)))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.pdims ctx st warnings))
             ((mv st warnings) (vl-shadowcheck-dimensionlist x.udims ctx st warnings)))
          (mv st warnings)))))

  (define vl-shadowcheck-maybe-datatype ((x        vl-maybe-datatype-p)
                                         (ctx      any-p)
                                         (st       vl-shadowcheck-state-p)
                                         (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-maybe-datatype-count x)
    (b* ((x        (vl-maybe-datatype-fix x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((unless x)
          (mv st warnings)))
      (vl-shadowcheck-datatype x ctx st warnings)))

  (define vl-shadowcheck-structmemberlist ((x        vl-structmemberlist-p)
                                           (ctx      any-p)
                                           (st       vl-shadowcheck-state-p)
                                           (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-structmemberlist-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((mv st warnings) (vl-shadowcheck-structmember (car x) ctx st warnings)))
      (vl-shadowcheck-structmemberlist (cdr x) ctx st warnings)))

  (define vl-shadowcheck-structmember ((x        vl-structmember-p)
                                       (ctx      any-p)
                                       (st       vl-shadowcheck-state-p)
                                       (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((mv st warnings) (vl-shadowcheck-datatype x.type ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-maybe-expr x.rhs ctx st warnings)))
      (mv st warnings)))

  (define vl-shadowcheck-dimensionlist ((x        vl-dimensionlist-p)
                                        (ctx      any-p)
                                        (st       vl-shadowcheck-state-p)
                                        (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-dimensionlist-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((mv st warnings) (vl-shadowcheck-dimension (car x) ctx st warnings)))
      (vl-shadowcheck-dimensionlist (cdr x) ctx st warnings)))

  (define vl-shadowcheck-dimension ((x        vl-dimension-p)
                                    (ctx      any-p)
                                    (st       vl-shadowcheck-state-p)
                                    (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-dimension-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings)))
      (vl-dimension-case x
        :unsized  (mv st warnings)
        :star     (mv st warnings)
        :range    (vl-shadowcheck-range x.range ctx st warnings)
        :queue    (vl-shadowcheck-maybe-expr x.maxsize ctx st warnings)
        :datatype (vl-shadowcheck-datatype x.type ctx st warnings))))

  (define vl-shadowcheck-range ((x        vl-range-p)
                                (ctx      any-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-range-count x)
    (b* (((vl-range x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((mv st warnings) (vl-shadowcheck-expr x.msb ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-expr x.lsb ctx st warnings)))
      (mv st warnings)))

  (define vl-shadowcheck-maybe-range ((x        vl-maybe-range-p)
                                      (ctx      any-p)
                                      (st       vl-shadowcheck-state-p)
                                      (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-maybe-range-count x)
    (b* ((x        (vl-maybe-range-fix x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((unless x)
          (mv st warnings)))
      (vl-shadowcheck-range x ctx st warnings)))

  (define vl-shadowcheck-enumitemlist ((x        vl-enumitemlist-p)
                                       (ctx      any-p)
                                       (st       vl-shadowcheck-state-p)
                                       (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-enumitemlist-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((mv st warnings) (vl-shadowcheck-enumitem (car x) ctx st warnings)))
      (vl-shadowcheck-enumitemlist (cdr x) ctx st warnings)))

  (define vl-shadowcheck-enumitem ((x        vl-enumitem-p)
                                   (ctx      any-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-enumitem-count x)
    (b* (((vl-enumitem x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((mv st warnings) (vl-shadowcheck-maybe-range x.range ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-maybe-expr x.value ctx st warnings)))
      (mv st warnings)))

  ///
  (deffixequiv-mutual vl-shadowcheck-expr)
  (verify-guards vl-shadowcheck-expr))

(define vl-shadowcheck-portdecl ((x        vl-portdecl-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-portdecl x)  (vl-portdecl-fix x))
       ((mv st warnings) (vl-shadowcheck-datatype x.type x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-vardecl ((x        vl-vardecl-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-vardecl x)   (vl-vardecl-fix x))
       ((mv st warnings) (vl-shadowcheck-datatype x.type x st warnings))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-vardecl-allexprs x) x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-modport ((x        vl-modport-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-modport x)   (vl-modport-fix x))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-modport-allexprs x) x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-typedef ((x        vl-typedef-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-typedef x)   (vl-typedef-fix x))
       ((mv st warnings) (vl-shadowcheck-datatype x.type x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-paramtype ((x        vl-paramtype-p)
                                  (ctx      any-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (vl-paramtype-case x
    :vl-implicitvalueparam
    (b* (((mv st warnings) (vl-shadowcheck-maybe-range x.range ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-maybe-expr x.default ctx st warnings)))
      (mv st warnings))
    :vl-explicitvalueparam
    (b* (((mv st warnings) (vl-shadowcheck-datatype x.type ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-maybe-expr x.default ctx st warnings)))
      (mv st warnings))
    :vl-typeparam
    (vl-shadowcheck-maybe-datatype x.default ctx st warnings)))

(define vl-shadowcheck-paramdecl ((x        vl-paramdecl-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-paramdecl x) (vl-paramdecl-fix x))
       ((mv st warnings) (vl-shadowcheck-paramtype x.type x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-blockitem ((x        vl-blockitem-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl   (vl-shadowcheck-vardecl   x st warnings))
      (:vl-import    (vl-shadowcheck-import    x st warnings))
      (:vl-paramdecl (vl-shadowcheck-paramdecl x st warnings))
      (otherwise     (vl-shadowcheck-typedef   x st warnings)))))

(define vl-shadowcheck-blockitemlist ((x        vl-blockitemlist-p)
                                      (st       vl-shadowcheck-state-p)
                                      (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (vl-warninglist-fix warnings)))
       ((mv st warnings)
        (vl-shadowcheck-blockitem (car x) st warnings)))
    (vl-shadowcheck-blockitemlist (cdr x) st warnings)))

(define vl-shadowcheck-assign ((x        vl-assign-p)
                               (st       vl-shadowcheck-state-p)
                               (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x (vl-assign-fix x))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-assign-allexprs x) x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-gateinst ((x        vl-gateinst-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-gateinst x)  (vl-gateinst-fix x))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-gateinst-allexprs x) x st warnings))
       ((mv st warnings) (if x.name
                             (vl-shadowcheck-declare-name x.name x st warnings)
                           (mv st warnings))))
    (mv st warnings)))

(define vl-shadowcheck-modinst ((x        vl-modinst-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-modinst x)   (vl-modinst-fix x))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-modinst-allexprs x) x st warnings))
       ((mv st warnings) (if x.instname
                             (vl-shadowcheck-declare-name x.instname x st warnings)
                           (mv st warnings))))
    (mv st warnings)))

(define vl-shadowcheck-alias ((x        vl-alias-p)
                              (st       vl-shadowcheck-state-p)
                              (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x                (vl-alias-fix x))
       ((mv st warnings) (vl-shadowcheck-exprlist (vl-alias-allexprs x) x st warnings)))
    (mv st warnings)))


(defines vl-shadowcheck-stmt

  (define vl-shadowcheck-stmt ((x        vl-stmt-p)
                               (ctx      any-p)
                               (st       vl-shadowcheck-state-p)
                               (warnings vl-warninglist-p))
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-stmt-count x)
    (b* ((x        (vl-stmt-fix x))
         (warnings (vl-warninglist-fix warnings))

         ((when (vl-atomicstmt-p x))
          ;; No atomic statements have their own scopes or can introduce any
          ;; declarations, so this is straightforward:
          (vl-shadowcheck-exprlist (vl-stmt-allexprs x) ctx st warnings))

         ((when (eq (vl-stmt-kind x) :vl-forstmt))
          ;; See scopestack for notes about the scoping of for statements.
          (b* (((vl-forstmt x))
               ((mv st warnings) (vl-shadowcheck-push-scope (vl-forstmt->blockscope x) st warnings))
               ((mv st warnings) (vl-shadowcheck-blockitemlist x.initdecls st warnings))
               ((mv st warnings) (vl-shadowcheck-exprlist (vl-compoundstmt->exprs x) ctx st warnings))
               ((mv st warnings) (vl-shadowcheck-stmtlist (vl-compoundstmt->stmts x) ctx st warnings))
               (st               (vl-shadowcheck-pop-scope st)))
            (mv st warnings)))

         ((when (eq (vl-stmt-kind x) :vl-blockstmt))
          ;; See scopestack for notes about the scoping of block statements.
          (b* (((vl-blockstmt x))
               ((mv st warnings) (vl-shadowcheck-push-scope (vl-blockstmt->blockscope x) st warnings))
               ((mv st warnings) (vl-shadowcheck-blockitemlist x.loaditems st warnings))
               ((mv st warnings) (vl-shadowcheck-stmtlist x.stmts ctx st warnings))
               (st               (vl-shadowcheck-pop-scope st)))
            (mv st warnings)))

         ((when (eq (vl-stmt-kind x) :vl-foreachstmt))
          (b* (((vl-foreachstmt x))
               ((mv st warnings) (vl-shadowcheck-push-scope (vl-foreachstmt->blockscope x) st warnings))
               ((mv st warnings) (vl-shadowcheck-blockitemlist x.vardecls st warnings))
               ((mv st warnings) (vl-shadowcheck-stmt x.body ctx st warnings))
               (st               (vl-shadowcheck-pop-scope st)))
            (mv st warnings)))

         ;; No other statement has a scope, but compound statements might have
         ;; block statements inside of them.  See vl-stmt-check-undeclared.  We
         ;; don't use vl-stmt-allexprs here because it grabs exprs from
         ;; sub-statements, which need to be checked only in the sub-scope.
         (local-exprs (append (vl-maybe-delayoreventcontrol-allexprs (vl-compoundstmt->ctrl x))
                              (vl-compoundstmt->exprs x)))
         ((mv st warnings) (vl-shadowcheck-exprlist local-exprs ctx st warnings)))
      ;; Recursively check sub-statements.
      (vl-shadowcheck-stmtlist (vl-compoundstmt->stmts x) ctx st warnings)))

  (define vl-shadowcheck-stmtlist ((x        vl-stmtlist-p)
                                   (ctx      any-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
    :measure (vl-stmtlist-count x)
    :returns (mv (st       vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :verify-guards nil
    (b* (((when (atom x))
          (mv (vl-shadowcheck-state-fix st) (ok)))
         ((mv st warnings)
          (vl-shadowcheck-stmt (car x) ctx st warnings)))
      (vl-shadowcheck-stmtlist (cdr x) ctx st warnings)))

  ///
  (verify-guards vl-shadowcheck-stmt)
  (deffixequiv-mutual vl-shadowcheck-stmt))

(define vl-shadowcheck-always ((x        vl-always-p)
                               (st       vl-shadowcheck-state-p)
                               (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-always x)    (vl-always-fix x))
       ((mv st warnings) (vl-shadowcheck-stmt x.stmt x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-initial ((x        vl-initial-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-initial x)   (vl-initial-fix x))
       ((mv st warnings) (vl-shadowcheck-stmt x.stmt x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-final ((x        vl-final-p)
                              (st       vl-shadowcheck-state-p)
                              (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-final x)     (vl-final-fix x))
       ((mv st warnings) (vl-shadowcheck-stmt x.stmt x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-portdecllist ((x        vl-portdecllist-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-portdecl (car x) st warnings)))
    (vl-shadowcheck-portdecllist (cdr x) st warnings)))


(define vl-shadowcheck-fun/task-loaditem ((x        vl-portdecl-or-blockitem-p)
                                          (st       vl-shadowcheck-state-p)
                                          (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x        (vl-portdecl-or-blockitem-fix x))
       (st       (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings))
       ((when (eq (tag x) :vl-portdecl))
        (vl-shadowcheck-portdecl x st warnings)))
    (vl-shadowcheck-blockitem x st warnings)))

(define vl-shadowcheck-fun/task-loaditems ((x        vl-portdecl-or-blockitem-list-p)
                                           (st       vl-shadowcheck-state-p)
                                           (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((st       (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings))
       ((when (atom x))
        (mv st warnings))
       ((mv st warnings) (vl-shadowcheck-fun/task-loaditem (car x) st warnings)))
    (vl-shadowcheck-fun/task-loaditems (cdr x) st warnings)))

(define vl-shadowcheck-fundecl ((x        vl-fundecl-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (- (vl-shadowcheck-debug "  >> shadowcheck in function ~s0.~%" x.name))
       (- (vl-shadowcheck-debug "  >> checking return type in outer scope:~%"))
       ;; We definitely need to check the return value in the outer scope.
       ((mv st warnings) (vl-shadowcheck-datatype x.rettype x st warnings))

       ;; When should we define the function name?  We definitely need to have
       ;; it defined in the inner scope so that we can assign to it.  I
       ;; originally thought we might want to define it after the declarations,
       ;; but before the statement, because this doesn't seem to make sense:
       ;;
       ;;    function foo ;
       ;;      input a;
       ;;      wire [foo-1:0] temp;   <-- doesn't make any sense to use foo here
       ;;      foo = a;               <-- makes sense to use foo here
       ;;    endfunction
       ;;
       ;; However, it actually DOES seem to make sense to do things like this:
       ;;
       ;;   function [3:0] foo ;
       ;;      input [$bits(foo)-1:0] in;
       ;;      foo = in;
       ;;   endfunction
       ;;
       ;; And this is accepted by tools such as NCVerilog and VCS.  So we will
       ;; go ahead and say that the name is declared immediately upon entry
       ;; into the new scope.
       (- (vl-shadowcheck-debug "  >> pushing into function ~x0.~%" x.name))
       ((mv st warnings) (vl-shadowcheck-push-scope (vl-fundecl->blockscope x) st warnings))

       (- (vl-shadowcheck-debug "  >> declaring function name in the inner scope: ~x0.~%" x.name))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings))

       ;; Local declarations need to get checked in the local scope because they
       ;; can make use of other local parameters, e.g.,
       ;;   function foo ;
       ;;      parameter width = 4;
       ;;      input [width-1:0] in;
       ;;      ...
       ;;   endfunction
       ((mv st warnings) (vl-shadowcheck-fun/task-loaditems x.loaditems st warnings))

       ;; Now check the body, still in the inner scope.
       ((mv st warnings) (vl-shadowcheck-stmt x.body x st warnings))

       (- (vl-shadowcheck-debug "  >> popping out of function ~x0.~%" x.name))
       (st (vl-shadowcheck-pop-scope st))

       ;; Now the function is defined so we can use it in the outer scope.
       (- (vl-shadowcheck-debug "  >> declaring function name in the outer scope: ~x0.~%" x.name))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))

    (mv st warnings)))

(define vl-shadowcheck-taskdecl ((x        vl-taskdecl-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-taskdecl x)   (vl-taskdecl-fix x))
       ((mv st warnings) (vl-shadowcheck-push-scope (vl-taskdecl->blockscope x) st warnings))
       ((mv st warnings) (vl-shadowcheck-fun/task-loaditems x.loaditems st warnings))
       ((mv st warnings) (vl-shadowcheck-stmt x.body x st warnings))
       (st (vl-shadowcheck-pop-scope st))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-dpiimport ((x        vl-dpiimport-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-dpiimport x) (vl-dpiimport-fix x))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))


(define vl-shadowcheck-modelement ((x        vl-modelement-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
  :returns (mv (st vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  :guard-hints(("Goal" :use ((:instance tag-when-vl-modelement-p-forward))))
  (b* ((item     (vl-modelement-fix x))
       (st       (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings))
       (tag      (tag item))
       (- (vl-shadowcheck-debug "  ---- ~a0 ---- ~%" item))
       ((when (or (eq tag :vl-interfaceport)
                  (eq tag :vl-regularport)))
        (mv st
            (fatal :type :vl-programming-error
                   :msg "We shouldn't see ports here, but found ~a0.~%"
                   :args (list item))))
       ((when (eq tag :vl-genvar))
        (b* (((vl-genvar item))
             ((mv st warnings) (vl-shadowcheck-declare-name item.name item st warnings)))
          (mv st warnings)))
       ((when (eq tag :vl-portdecl))   (vl-shadowcheck-portdecl item st warnings))
       ((when (eq tag :vl-vardecl))    (vl-shadowcheck-vardecl item st warnings))
       ((when (eq tag :vl-paramdecl))  (vl-shadowcheck-paramdecl item st warnings))
       ((when (eq tag :vl-assign))     (vl-shadowcheck-assign item st warnings))
       ((when (eq tag :vl-gateinst))   (vl-shadowcheck-gateinst item st warnings))
       ((when (eq tag :vl-modinst))    (vl-shadowcheck-modinst item st warnings))
       ((when (eq tag :vl-always))     (vl-shadowcheck-always item st warnings))
       ((when (eq tag :vl-initial))    (vl-shadowcheck-initial item st warnings))
       ((when (eq tag :vl-final))      (vl-shadowcheck-final item st warnings))
       ((when (eq tag :vl-fundecl))    (vl-shadowcheck-fundecl item st warnings))
       ((when (eq tag :vl-taskdecl))   (vl-shadowcheck-taskdecl item st warnings))
       ((when (eq tag :vl-dpiimport))  (vl-shadowcheck-dpiimport item st warnings))
       ((when (eq tag :vl-import))     (vl-shadowcheck-import item st warnings))
       ((when (eq tag :vl-typedef))    (vl-shadowcheck-typedef item st warnings))
       ((when (eq tag :vl-alias))      (vl-shadowcheck-alias item st warnings))
       ((when (eq tag :vl-modport))    (vl-shadowcheck-modport item st warnings))
       ((when (eq tag :vl-assertion))  (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-cassertion)) (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-property))   (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-sequence))   (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-clkdecl))    (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-gclkdecl))   (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-defaultdisable)) (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-dpiexport))  (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-fwdtypedef)) (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-bind))       (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-class))      (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-covergroup)) (mv st warnings)) ;; BOZO figure out what we want to do here.
       ((when (eq tag :vl-elabtask))   (mv st warnings)) ;; BOZO figure out what we want to do here.
       )
    (impossible)
    (mv st warnings)))


(defines vl-shadowcheck-genelement
  :short "Main function for checking name shadowing."
  :verify-guards nil

  (define vl-shadowcheck-genelement ((x        vl-genelement-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
    :returns (mv (st vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-genelement-count x)
    (b* ((x        (vl-genelement-fix x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings)))
      (vl-genelement-case x
        :vl-genbase  (vl-shadowcheck-modelement x.item st warnings)
        :vl-genbegin (vl-shadowcheck-genblock x.block st warnings)
        :vl-genif
        (b* (((mv st warnings) (vl-shadowcheck-expr x.test x st warnings))
             ((mv st warnings) (vl-shadowcheck-genblock x.then st warnings))
             ((mv st warnings) (vl-shadowcheck-genblock x.else st warnings)))
          (mv st warnings))
        :vl-gencase
        (b* (((mv st warnings) (vl-shadowcheck-expr x.test x st warnings))
             ((mv st warnings) (vl-shadowcheck-gencaselist x.cases x st warnings))
             ((mv st warnings) (vl-shadowcheck-genblock x.default st warnings)))
          (mv st warnings))
        :vl-genloop
        ;; Subtle.  See SystemVerilog-2012 Section 27.4.  The genvar for the
        ;; loop is supposed to be a localparam; it really is a declared item
        ;; and it is not OK to redefine it within the generate block.
        ;;
        ;; We emulate this as directly as we can.
        ;;
        ;;   - On the scopestack side, we create a scope for the body and then
        ;;     explicitly add a paramdecl to it for the genvar.  When we push
        ;;     this scope, our ordinary nameclash warning mechanism should thus
        ;;     be able to see that the genvar is declared and complain if there
        ;;     are any subsequent uses of it.
        ;;
        ;;   - For shadowchecking, we enter the extended scope, add the
        ;;     paramdecl first, check all the loop expressions (so they can
        ;;     refer to the paramdecl), and then check all of the body elements
        ;;     without entering another scope.  We check the elements directly,
        ;;     rather than using vl-shadowcheck-genblock to check the whole
        ;;     body, because (1) we have already pushed a scope and it would
        ;;     not be correct to push another scope, and (2) this nicely avoids
        ;;     having to recur on something like a changed body, which would
        ;;     complicate termination.
        (b* ((var-paramdecl  (make-vl-paramdecl :name x.var
                                                :localp t
                                                :type (make-vl-explicitvalueparam
                                                       :type *vl-plain-old-integer-type*)
                                                :loc x.loc))
             (body-scope     (vl-genblock->genblob x.body))
             (extended-scope (change-vl-genblob body-scope
                                                :paramdecls (cons var-paramdecl (vl-genblob->paramdecls body-scope))))
             ;; Keep generally in sync with vl-shadowcheck-genblock -- we
             ;; basically want to do that, but there are a few extra things we
             ;; need to do inside the block scope here.

             ;; If the loop has a name, regard it as declared in the scope
             ;; where it was defined.
             (name (vl-genblock->name x.body))
             ((mv st warnings) (if (stringp name)
                                   (vl-shadowcheck-declare-name name x st warnings :genblockp t)
                                 (mv st warnings)))
             ((mv st warnings) (vl-shadowcheck-push-scope extended-scope st warnings))
             ((mv st warnings) (vl-shadowcheck-paramdecl var-paramdecl st warnings))
             ((mv st warnings) (vl-shadowcheck-expr x.initval x st warnings))
             ((mv st warnings) (vl-shadowcheck-expr x.continue x st warnings))
             ((mv st warnings) (vl-shadowcheck-expr x.nextval x st warnings))
             ((mv st warnings) (vl-shadowcheck-genelementlist (vl-genblock->elems x.body) st warnings))
             (st (vl-shadowcheck-pop-scope st)))
          (mv st warnings))
        :vl-genarray
        (mv st
            (fatal :type :vl-programming-error
                   :msg "~a0: did not expect to see genarrays in shadowcheck,
                         because they shouldn't exist until after elaboration."
                   :args (list x))))))

  (define vl-shadowcheck-genelementlist ((x        vl-genelementlist-p)
                                         (st       vl-shadowcheck-state-p)
                                         (warnings vl-warninglist-p))
    :returns (mv (st vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-genelementlist-count x)
    (b* ((st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((mv st warnings) (vl-shadowcheck-genelement (car x) st warnings)))
      (vl-shadowcheck-genelementlist (cdr x) st warnings)))

  (define vl-shadowcheck-genblock ((x        vl-genblock-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
    :returns (mv (st vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-genblock-count x)
    (b* (((vl-genblock x) (vl-genblock-fix x))
         (st              (vl-shadowcheck-state-fix st))
         (warnings        (vl-warninglist-fix warnings))

         ;; If the block has a name, regard it as declared in the scope
         ;; outside, (It could be declared again within the block, see for
         ;; instance cosims/generate8).
         ((mv st warnings) (if (stringp x.name)
                               (vl-shadowcheck-declare-name x.name x st warnings :genblockp t)
                             (mv st warnings)))

         ;; Background: see the discussion of implicit wires of how begin/end
         ;; blocks are handled and also the discussion of condnestp in
         ;; vl-genblock.  Since shadowchecking happens after we've gotten rid
         ;; of empty begin/end blocks in make-implicit-wires, we expect that
         ;; any blocks that remain really are scopes, except for the very
         ;; special case condnest case.
         ((mv st warnings) (if x.condnestp
                               (mv st warnings)
                             (vl-shadowcheck-push-scope (vl-genblock->genblob x) st warnings)))
         ((mv st warnings) (vl-shadowcheck-genelementlist x.elems st warnings))
         (st               (if x.condnestp
                               st
                             (vl-shadowcheck-pop-scope st))))
      (mv st warnings)))

  (define vl-shadowcheck-gencaselist ((x        vl-gencaselist-p)
                                      (ctx)
                                      (st       vl-shadowcheck-state-p)
                                      (warnings vl-warninglist-p))
    :returns (mv (st vl-shadowcheck-state-p)
                 (warnings vl-warninglist-p))
    :measure (vl-gencaselist-count x)
    (b* ((x        (vl-gencaselist-fix x))
         (st       (vl-shadowcheck-state-fix st))
         (warnings (vl-warninglist-fix warnings))
         ((when (atom x))
          (mv st warnings))
         ((cons exprs1 block1) (car x))
         ((mv st warnings) (vl-shadowcheck-exprlist exprs1 ctx st warnings))
         ((mv st warnings) (vl-shadowcheck-genblock block1 st warnings)))
      (vl-shadowcheck-gencaselist (cdr x) ctx st warnings)))

  ///
  (verify-guards vl-shadowcheck-genelement)
  (deffixequiv-mutual vl-shadowcheck-genelement))


(define vl-shadowcheck-port ((x        vl-port-p)
                             (st       vl-shadowcheck-state-p)
                             (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x                (vl-port-fix x))
       (varnames         (if (eq (tag x) :vl-interfaceport)
                             (list (vl-interfaceport->name x))
                           (b* ((expr (vl-regularport->expr x)))
                             (and expr (vl-expr-varnames expr)))))
       ((mv st warnings) (vl-shadowcheck-declare-names varnames x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-ports ((x        vl-portlist-p)
                              (st       vl-shadowcheck-state-p)
                              (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-port (car x) st warnings)))
    (vl-shadowcheck-ports (cdr x) st warnings)))


(define vl-shadowcheck-imports ((x        vl-importlist-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-import (car x) st warnings)))
    (vl-shadowcheck-imports (cdr x) st warnings)))

(define vl-shadowcheck-module ((x  vl-module-p)
                               (st vl-shadowcheck-state-p))
  :returns (mv (st    vl-shadowcheck-state-p)
               (new-x vl-module-p))
  ;; BOZO this probably isn't correctly handling ports yet.
  ;; To fix:
  ;;   - Add some tests to linttest/implicit and or linttest/shadowcheck
  ;;   - Review how the parser creates loaditems and parse-temps; I don't think
  ;;     we're even getting everything in one coherent order yet
  ;;   - Figure out the whole ansi portdecl resolution affects all of this
  (b* (((vl-module x)    (vl-module-fix x))
       (x.loaditems (and x.parse-temps
                         (vl-parse-temps->loaditems x.parse-temps)))
       (x.initial-imports
        (and x.parse-temps (vl-parse-temps->imports x.parse-temps)))
       (- (vl-shadowcheck-debug "*** Shadowcheck module ~s0 ***~%" x.name))
       (warnings         x.warnings)
       ((mv st warnings) (vl-shadowcheck-push-scope x st warnings))
       ((mv st warnings) (vl-shadowcheck-imports x.initial-imports st warnings))
       ((mv st warnings) (vl-shadowcheck-ports x.ports st warnings))
       ((mv st warnings) (vl-shadowcheck-genelementlist x.loaditems st warnings))
       (st               (vl-shadowcheck-pop-scope st))
       (new-x            (change-vl-module x :warnings warnings)))
    (mv st new-x)))

(define vl-shadowcheck-modules ((x  vl-modulelist-p)
                                (st vl-shadowcheck-state-p))
  :returns (mv (st    vl-shadowcheck-state-p)
               (new-x vl-modulelist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) nil))
       ((mv st car)  (vl-shadowcheck-module (car x) st))
       ((mv st rest) (vl-shadowcheck-modules (cdr x) st)))
    (mv st (cons car rest))))

(define vl-shadowcheck-interface ((x  vl-interface-p)
                                  (st vl-shadowcheck-state-p))
  :returns (mv (st    vl-shadowcheck-state-p)
               (new-x vl-interface-p))
  ;; BOZO copied from interfaces, probably has the same problems and needs
  ;; the same fixes.
  (b* (((vl-interface x) (vl-interface-fix x))
       (x.loaditems (and x.parse-temps (vl-parse-temps->loaditems x.parse-temps)))
       (- (vl-shadowcheck-debug "*** Shadowcheck interface ~s0 ***~%" x.name))
       (warnings         x.warnings)
       ((mv st warnings) (vl-shadowcheck-push-scope x st warnings))
       ((mv st warnings) (vl-shadowcheck-ports x.ports st warnings))
       ((mv st warnings) (vl-shadowcheck-genelementlist x.loaditems st warnings))
       (st               (vl-shadowcheck-pop-scope st))
       (new-x            (change-vl-interface x :warnings warnings)))
    (mv st new-x)))

(define vl-shadowcheck-interfaces ((x  vl-interfacelist-p)
                                (st vl-shadowcheck-state-p))
  :returns (mv (st    vl-shadowcheck-state-p)
               (new-x vl-interfacelist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) nil))
       ((mv st car)  (vl-shadowcheck-interface (car x) st))
       ((mv st rest) (vl-shadowcheck-interfaces (cdr x) st)))
    (mv st (cons car rest))))


(define vl-shadowcheck-vardecls ((x        vl-vardecllist-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-vardecl (car x) st warnings)))
    (vl-shadowcheck-vardecls (cdr x) st warnings)))

(define vl-shadowcheck-paramdecls ((x        vl-paramdecllist-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-paramdecl (car x) st warnings)))
    (vl-shadowcheck-paramdecls (cdr x) st warnings)))

(define vl-shadowcheck-fundecls ((x        vl-fundecllist-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-fundecl (car x) st warnings)))
    (vl-shadowcheck-fundecls (cdr x) st warnings)))

(define vl-shadowcheck-taskdecls ((x        vl-taskdecllist-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-taskdecl (car x) st warnings)))
    (vl-shadowcheck-taskdecls (cdr x) st warnings)))

(define vl-shadowcheck-declare-typedefs ((x        vl-typedeflist-p)
                                         (st       vl-shadowcheck-state-p)
                                         (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((vl-typedef x1) (vl-typedef-fix (car x)))
       ((mv st warnings) (vl-shadowcheck-declare-name x1.name x1 st warnings)))
    (vl-shadowcheck-declare-typedefs (cdr x) st warnings)))


(define vl-shadowcheck-dpiimports ((x        vl-dpiimportlist-p)
                                   (st       vl-shadowcheck-state-p)
                                   (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-dpiimport (car x) st warnings)))
    (vl-shadowcheck-dpiimports (cdr x) st warnings)))

(define vl-shadowcheck-design ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (warnings x.warnings)

       (st (make-vl-shadowcheck-state :lexscopes (list (vl-empty-lexscope))
                                      :ss        (vl-scopestack-init x)
                                      :design    x))

       ;; It would perhaps be better to construct the initial scopes using the
       ;; program order?  But some simulators allow you to refer to things that
       ;; are defined later, for instance, NCVerilog allows you to write foo::w
       ;; before defining package foo.

       ;; ;; BOZO yes, I think we eventually will want to do this in program order
       ;; ;; instead of in this ad-hoc way we're doing it below.  Unfortunately
       ;; ;; that'll require rejiggering the end of vl-load, and also all the
       ;; ;; transforms in annotate up until here.  At this point we don't even
       ;; ;; have things in program order.

       ;; I think the new nameclash check is stronger than this ad-hoc stuff:
       (warnings (vl-scope-nameclash-warnings x x warnings))

       ;; (itemnames (append (vl-vardecllist->names x.vardecls)
       ;;                    (vl-paramdecllist->names x.paramdecls)
       ;;                    (vl-fundecllist->names x.fundecls)
       ;;                    (vl-taskdecllist->names x.taskdecls)
       ;;                    (vl-typedeflist->names x.typedefs)
       ;;                    (vl-dpiimportlist->names x.dpiimports)))
       ;; (dupes (duplicated-members itemnames))
       ;; (warnings (if (not dupes)
       ;;               (ok)
       ;;             (fatal :type :vl-name-clash
       ;;                    :msg "Name clash among globals: ~&0."
       ;;                    :args (list dupes))))

       ;; Dumb hack: doing the imports first seems less wrong than doing it any
       ;; other way.  As long as there aren't clashes between the global namespace
       ;; and the imported packages, we may be just about OK.
       ((mv st warnings) (vl-shadowcheck-imports          x.imports    st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-typedefs x.typedefs   st warnings))
       ((mv st warnings) (vl-shadowcheck-vardecls         x.vardecls   st warnings))
       ((mv st warnings) (vl-shadowcheck-paramdecls       x.paramdecls st warnings))
       ((mv st warnings) (vl-shadowcheck-fundecls         x.fundecls   st warnings))
       ((mv st warnings) (vl-shadowcheck-taskdecls        x.taskdecls  st warnings))
       ((mv st warnings) (vl-shadowcheck-dpiimports       x.dpiimports st warnings))

       ((mv st mods)       (vl-shadowcheck-modules x.mods st))
       ((mv st interfaces) (vl-shadowcheck-interfaces x.interfaces st))

       (?st (vl-shadowcheck-pop-scope st))
       (-   (vl-scopestacks-free))

       (new-x (change-vl-design x
                                :mods mods
                                :interfaces interfaces
                                :warnings warnings)))

    ;; All done with parse temps, delete them so that the design is
    ;; smaller/cleaner and more regular, and to hopefully prevent inappropriate
    ;; uses of these fields.
    (vl-design-deltemps new-x)))
