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
(include-book "make-implicit-wires")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc shadowcheck
  :parents (annotate)
  :short "Sanity check to prevent tricky kinds of global name shadowing."

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
be able to traverse scopes in a simple set-like way.  This approach makes
supporting this kind of lexical shadowing a challenge.  To avoid any problems
due to this kind of shadowing, we implement a special check to prohibit globals
from being used before they are locally declared.</p>

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
  ((decl       acl2::any-p
               "The actual declaration of this name.")
   (direct-pkg maybe-stringp
               :rule-classes :type-prescription
               "When non-nil, this entry is directly import from the package
                name @('direct-pkg'), i.e., @('import foo::bar').")
   (wildpkgs   string-listp
               "This entry is imported via @('import foo::*') statements from
                each of packages named in @('wildpkgs').")))

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
  :short "Look up a name in a lexical scope."
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
                                   (decl     acl2::any-p)
                                   (scopes   vl-lexscopes-p)
                                   (warnings vl-warninglist-p))
  :guard (consp scopes)
  :returns (mv (new-scopes (and (vl-lexscopes-p new-scopes)
                                (equal (len new-scopes) (len scopes))
                                (iff (consp new-scopes) (consp scopes))))
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a local declaration."
  (b* ((name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (warnings (vl-warninglist-fix warnings))

       (scope1 (car scopes))
       (entry  (vl-lexscope-find name scope1))

       ((unless (mbt (consp scopes)))
        (impossible)
        (mv scopes warnings))

       ((unless entry)
        ;; Completely new declaration, can't possibly conflict with anything.
        ;; No information to merge.  Just add a new entry to the scope.
        (mv (cons (hons-acons name
                              (make-vl-lexscope-entry :decl       decl
                                                      :direct-pkg nil
                                                      :wildpkgs   nil)
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
  :guard (consp scopes)
  :returns (mv (new-scopes (and (vl-lexscopes-p new-scopes)
                                (equal (len new-scopes) (len scopes))
                                (iff (consp new-scopes) (consp scopes))))
               (warnings   vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a direct import of a single name."
  (b* ((pkgname  (string-fix pkgname))
       (name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (ctx      (vl-import-fix ctx))
       (warnings (vl-warninglist-fix warnings))

       ((unless (mbt (consp scopes)))
        (impossible)
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
  :guard (consp scopes)
  :returns (mv (new-scopes (and (vl-lexscopes-p new-scopes)
                                (equal (len new-scopes) (len scopes))
                                (iff (consp new-scopes) (consp scopes))))
               (warnings   vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a wildcard import of a single name."
  (declare (ignorable ctx))
  (b* ((pkgname  (string-fix pkgname))
       (name     (string-fix name))
       (scopes   (vl-lexscopes-fix scopes))
       (warnings (vl-warninglist-fix warnings))

       ((unless (mbt (consp scopes)))
        (impossible)
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

       ;; I don't think we want to warn about anything here.  Just extend the
       ;; list of wild packages.
       (new-entry  (change-vl-lexscope-entry entry :wildpkgs (cons pkgname entry.wildpkgs)))
       (new-scope1 (hons-acons name new-entry scope1))
       (new-scopes (cons new-scope1 (cdr scopes))))
    (mv new-scopes warnings)))


(define vl-lexscopes-wild-import-names ((pkgname  stringp      "Name of the package being imported from.")
                                        (names    string-listp "Names declared in the package.")
                                        (scopes   vl-lexscopes-p)
                                        (ctx      vl-import-p)
                                        (warnings vl-warninglist-p))
  :guard (consp scopes)
  :returns (mv (new-scopes (and (vl-lexscopes-p new-scopes)
                                (equal (len new-scopes) (len scopes))
                                (iff (consp new-scopes) (consp scopes))))
               (warnings   vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a wildcard import of a list of names."
  (declare (ignorable ctx))
  (b* (((when (atom names))
        (mv (vl-lexscopes-fix scopes) (vl-warninglist-fix warnings)))
       ((mv scopes warnings)
        (vl-lexscopes-wild-import-name pkgname (car names) scopes ctx warnings)))
    (vl-lexscopes-wild-import-names pkgname (cdr names) scopes ctx warnings)))


(define vl-lexscopes-do-import ((x        vl-import-p)
                                (scopes   vl-lexscopes-p)
                                (warnings vl-warninglist-p)
                                (design   vl-design-p))
  :guard (consp scopes)
  :returns (mv (new-scopes (and (vl-lexscopes-p new-scopes)
                                (equal (len new-scopes) (len scopes))
                                (iff (consp new-scopes) (consp scopes))))
               (warnings vl-warninglist-p))
  :parents (vl-lexscopes)
  :short "Extend the lexscopes with a package import."
  (b* (((vl-import x) (vl-import-fix x))
       (scopes        (vl-lexscopes-fix x))
       (warnings      (vl-warninglist-fix warnings))

       ((unless (mbt (consp scopes)))
        (impossible)
        (mv scopes warnings))

       (pkg      (vl-find-package import.pkg (vl-design->packages design)))
       (warnings (if pkg
                     warnings
                   (fatal :type :vl-bad-import
                          :msg "~a0: trying to import from undefined package ~s1."
                          :args (list x import.pkg))))

       ((unless (eq import.part :vl-import*))
        (b* ((item     (BOZO-FIND-NONIMPORTED-ITEM-IN-PACKAGE import.part pkg))
             (warnings (if item
                           warnings
                         (fatal :type :vl-bad-import
                                "~a0: no declaration of ~s1 in package ~s2."
                                :args (list x import.part import.pkg)))))
          ;; If the item wasn't found, it doesn't really matter what we do
          ;; because we caused a fatal error already.  It seems basically
          ;; reasonable to pretend that we imported it successfully, so we can
          ;; check subsequent uses of it.
          (vl-lexscopes-direct-import-name import.pkg import.part scopes x warnings)))

       (names (BOZO-GET-ALL-NAMES-IN-PACKAGE pkg)))
    (vl-lexscopes-wild-import-names import.pkg names scopes x warnings)))




(defprod vl-shadowcheck-state
  :tag :vl-shadowcheck-state
  :layout :tree
  ((ss  vl-scopestack-p
        "Proper scopestack with all implicit variables already added to it, and
         updated with whatever scopes we've descended through pushed onto it.")
   (lex vl-lexscopes-p
        "Partial lexical scopestack-like thing, current up to this point.")))


(define vl-shadowcheck-lex-declare-name

(define vl-scopestack-nesting-level ((x vl-scopestack-p))
  :returns (level natp)
  (vl-scopestack-case x
    :null 0
    :global 1
    :local (+ 1 (vl-scopestack-nesting-level x.super))))

(define vl-shadowcheck-reference-name ((name     stringp)
                                       (st       vl-shadowcheck-state-p)
                                       (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (declare (ignore name))
  (b* (((vl-shadowcheck-state st)        (vl-shadowcheck-state-fix st))
       ((mv decl import-lex lex-pkgname) (vl-shadowcheck-lex-find name st.lex))
       ((mv item import-ss  ss-pkgname)  (vl-special-scopestack-find name st.ss))
       (okp (and decl
                 item
                 (equal (vl-lexscope-nesting-level import-lex)
                        (vl-scopestack-nesting-level import-ss))
                 (equal lex-pkgname ss-pkgname)
       
       



    (raise "BOZO implement me")
    (mv st (ok))))

(define vl-shadowcheck-reference-names ((names    string-listp)
                                        (st       vl-shadowcheck-state-p)
                                        (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings)
        (vl-shadowcheck-reference-name (car names) st warnings)))
    (vl-shadowcheck-reference-names (cdr names) st warnings)))

(define vl-shadowcheck-declare-name ((name     stringp)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (declare (ignore name))
  (b* ((st (vl-shadowcheck-state-fix st)))
    (raise "BOZO implement me")
    (mv st (ok))))

(define vl-shadowcheck-portdecl ((x        vl-portdecl-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((declname (vl-portdecl->name x))
       (varnames (vl-exprlist-varnames (vl-portdecl-allexprs x)))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name declname st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-vardecl ((x        vl-vardecl-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((declname (vl-vardecl->name x))
       (varnames (vl-exprlist-varnames (vl-vardecl-allexprs x)))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name declname st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-aux
  :short "Main function for checking for name shadowing."
  ((x        vl-genelementlist-p
             "Module elements to process, should be in the same order in which they
              were parsed.")
   (st       vl-shadowcheck-state-p)
   (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (st           vl-shadowcheck-state-p))
  :measure (len x)
  (b* ((x        (vl-genelementlist-fix x))
       (st       (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom x))
        (mv warnings st))

       ((unless (eq (vl-genelement-kind (car x)) :vl-genbase))
        ;; Ignore generate constructs until unparameterization
        (vl-shadowcheck-aux (cdr x) st warnings))

       (elem (vl-genelement-fix (car x)))
       (item (vl-genbase->item elem))
       (tag  (tag item))

       ((when (eq tag :vl-port))
        ;; We shouldn't see any ports.
        (raise "We shouldn't see ports here.")
        (vl-shadowcheck-aux (cdr x) st warnings))

       ((when (eq tag :vl-portdecl))
        (b* (((mv st warnings) (vl-shadowcheck-portdecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-vardecl))
        (b* (((mv st warnings) (vl-shadowcheck-vardecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ;; BOZO implement everything else
       (warnings (fatal :type :vl-unexpected-modelement
                        :msg "~a0: unexpected kind of module item."
                        :args (list item))))
    (vl-shadowcheck-aux (cdr x) st warnings)))

(define vl-shadowcheck-module ((x  vl-module-p)
                               (st vl-shadowcheck-state-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       (warnings x.warnings)
       (ss (vl-scopestack-push x (vl-shadowcheck-state->ss st)))
       (st (change-vl-shadowcheck-state st :ss ss))
       ((mv warnings ?st) (vl-shadowcheck-aux x.loaditems st warnings)))
    ;; maybe free stuff in st
    (change-vl-module x :warnings warnings)))

(defprojection vl-shadowcheck-modules ((x  vl-modulelist-p)
                                       (st vl-shadowcheck-state-p))
  :returns (new-x vl-modulelist-p)
  (vl-shadowcheck-module x st))

(define vl-shadowcheck-design ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (ss (vl-scopestack-init x))
       (st (make-vl-shadowcheck-state :ss ss))
       (mods (vl-shadowcheck-modules x.mods st)))
    ;; maybe free stuff in st
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))



















(defenum vl-shadowcheck-status-p
  (:vl-unused-superior
   :vl-used-superior
   :vl-local)
  :short "Possible kinds of names for tricky shadowing checking."

  :long "<p>Any names that aren't bound in a @(see vl-shadowcheck-alist-p)
simply haven't been encountered yet.  Every name we have encountered is bound
to an entry that has a status.  The possible statuses of any particular name
are:</p>

<ul>

<li><b>Unused-Superior</b> &mdash; the name exists in some superior (or
imported) scope, but has not yet been declared locally, and has not yet been
referenced locally.  It is generally okay to introduce a new local declaration
that shadows an unused global.</li>

<li><b>Used-Superior</b> means that the name exists in some superior or
imported scope, has not yet been declared locally, and <b>has</b> been
referenced at some point in the current scope.  A basic goal of shadowcheck is
to prevent used globals from becoming shadowed by local declarations.</li>

<li><b>Local</b> means that the name has been declared in the current scope.
The name may or may not be declared in superior scopes.</li>

</ul>")

(defprod vl-shadowcheck-entry
  :tag nil
  :layout :tree
  ((status vl-shadowcheck-status-p "Current status for this name.")
   (ctx    acl2::any-p             "Context that set this name to this status.")))


(fty::defalist vl-shadowcheck-alist
  :short "Fast association list for tracking name shadowing."
  :key-type stringp
  :val-type vl-shadowcheck-entry-p)




(define vl-shadowcheck-init-global-names
  :short "Record that a list of names are declared globally."
  ((names   string-listp)
   (scalist vl-shadowcheck-alist-p)
   (ctx))
  :returns (scalist vl-shadowcheck-alist-p)
  (b* (((when (atom names))
        (vl-shadowcheck-alist-fix scalist))
       (name1   (string-fix (car names)))
       (entry1  (make-vl-shadowcheck-entry :status :vl-unused-superior :ctx ctx))
       (scalist (hons-acons name1 entry1 scalist)))
    (vl-shadowcheck-init-global-names (cdr names) scalist ctx)))


(define vl-shadowcheck-enter-subscope
  :short "Update the shadowcheck alist to enter a new subscope."
  ((scalist vl-shadowcheck-alist-p))
  :returns (subscope-scalist vl-shadowcheck-alist-p
                             "A new fast alist, independent of the original.")

  :long "<p>We modify the shadowcheck alist by changing all local variables to be
considered as unused global variables.Consider a case like:</p>

@({
    parameter foo = 1;
    module m ();
      wire w = foo;
      function myfun (...);
        integer a = w;
        integer foo = 5;
        integer w = ...;
      endfunction
    endmodule
})

<p>To check for acceptable shadowing within @('myfun'), we want to convert
the local variables such as @('w') 




(define vl-shadowcheck-mark-name-used
  :short "Record that a name has been referenced."
  ((name     stringp)
   (scalist  vl-shadowcheck-alist-p)
   (ctx)
   (warnings vl-warninglist-p))
  :returns (mv (scalist  vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* ((name    (string-fix name))
       (scalist (vl-shadowcheck-alist-fix scalist))
       (entry   (cdr (hons-get name scalist)))
       ((unless entry)
        ;; Not a known name.  What's going on here?  I'll issue a warning
        ;; because this seems strange.  I'm not sure if there would be any
        ;; cases where this was actually okay.  BOZO maybe this should this be
        ;; a fatal warning?
        (mv scalist
            (warn :type :vl-undefined-name
                  :msg "~a0: using undefined name ~x1."
                  :args (list ctx name))))
       ((vl-shadowcheck-entry entry))
       ((when (or (eq entry.status :vl-used-superior)
                  (eq entry.status :vl-local)))
        ;; Already used or locally shadowed (in which case there's no conflict
        ;; with the global version so we're fine), so nothing to do.
        (mv scalist (ok)))

       ((when (eq entry.status :vl-unused-superior))
        ;; Otherwise, the name was previously unused, so we need to update it
        ;; to mark it as used.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-used-superior :ctx ctx)
                        scalist)
            (ok))))

    (impossible)
    (mv scalist (ok))))

(define vl-shadowcheck-mark-names-used
  :short "Record that a list of names have been referenced."
  ((names    string-listp)
   (scalist  vl-shadowcheck-alist-p)
   (ctx)
   (warnings vl-warninglist-p))
  :returns (mv (scalist  vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-alist-fix scalist) (ok)))
       ((mv scalist warnings)
        (vl-shadowcheck-mark-name-used (car names) scalist ctx warnings)))
    (vl-shadowcheck-mark-names-used (cdr names) scalist ctx warnings)))


(define vl-shadowcheck-mark-name-shadowed
  :short "Record that a single name has been locally declared."
  ((name     stringp)
   (scalist  vl-shadowcheck-alist-p)
   (ctx)
   (warnings vl-warninglist-p))
  :returns (mv (scalist  vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* ((name    (string-fix name))
       (scalist (vl-shadowcheck-alist-fix scalist))
       (entry   (cdr (hons-get name scalist)))
       ((unless entry)
        ;; Not a global name, so we're just declaring a local name that doesn't
        ;; shadow any global name.  That's totally fine.  We need to mark the
        ;; name as shadowed anyway (i.e., locally declared) so that when we see
        ;; uses of it, we know these uses are to something that has been
        ;; defined.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (ok)))
       ((vl-shadowcheck-entry entry))

       ((when (eq entry.status :vl-local))
        ;; Already locally defined.  This seems like a multiple definition, so
        ;; maybe we should try causing a warning here.  On the other hand,
        ;; checking for multiply defined identifiers can be done later easily
        ;; enough, so maybe this isn't the best place for it and we should
        ;; just do nothing.
        (mv scalist (ok)))

       ((when (eq entry.status :vl-unused-superior))
        ;; Unused global being shadowed by a local declaration.  This is
        ;; totally fine, we just need to mark the name as locally declared.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (ok)))

       ((when (eq entry.status :vl-used-superior))
        ;; Global version was used previously, but is now being locally
        ;; shadowed.  This is the main thing we want to complain about.  We
        ;; rather arbitrarily mark the name as shadowed, which probably doesn't
        ;; really matter for anything but might prevent future warnings about
        ;; this same name.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (fatal :type :vl-tricky-shadowing
                   :msg "~a0: name ~s1 was previously used in this scope ~
                         (~a2), but the superior declaration is now being ~
                         shadowed by a local declaration.  This is tricky and ~
                         seems error prone, so we do not support it."
                   :args (list ctx name entry.ctx)))))

    (impossible)
    (mv scalist (ok))))


(define vl-shadowcheck-mark-names-shadowed
  :short "Record that a list of names have been locally declared."
  ((names    string-listp)
   (scalist  vl-shadowcheck-alist-p)
   (ctx)
   (warnings vl-warninglist-p))
  :returns (mv (scalist  vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-alist-fix scalist) (ok)))
       ((mv scalist warnings)
        (vl-shadowcheck-mark-name-shadowed (car names) scalist ctx warnings)))
    (vl-shadowcheck-mark-names-shadowed (cdr names) scalist ctx warnings)))


(define vl-shadowcheck-mark-name-wild-import
  :short "Record that a name is being imported by an @('import foo::*')."
  ((name     stringp "Name being imported, i.e., something declared in package @('foo').")
   (scalist  vl-shadowcheck-alist-p)
   (ctx      "The import construct.")
   (warnings vl-warninglist-p))
  :returns (mv (scalist vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* ((name    (string-fix name))
       (scalist (vl-shadowcheck-alist-fix scalist))
       (entry   (cdr (hons-get name scalist)))
       ;; See particularly SystemVerilog-2012 Table 26-1 (Page 745), "Scoping
       ;; rules for package importation."

       ((unless entry)
        ;; OK.  No existing declaration of this name.
        ;;
        ;; I think the right thing is to treat the imported symbol as now
        ;; having a global declaration.  This way, we'll warn if we ever try to
        ;; (1) use the imported symbol and then (2) subsequently locally shadow
        ;; it.
        ;;
        ;; BOZO I'm not entirely sure this is right.  Perhaps it should not be
        ;; legal to subsequently redeclare the wire at all.  In that case we
        ;; might want to handle this differently.  (Maybe we should be checking
        ;; for multiple declarations here, too.)
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-unused-superior :ctx ctx)
                        scalist)
            (ok)))
       ((vl-shadowcheck-entry entry))

       ((when (eq entry.status :vl-unused-superior))
        ;; OK?  There is a global declaration of NAME but it hasn't been
        ;; referenced before this import.  I think this is OK and we just want
        ;; the imported symbol to win.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-unused-superior :ctx ctx)
                        scalist)
            (ok)))

       ((when (eq entry.status :vl-used-superior))
        ;; BAD?  There is a global declaration of NAME and it has been
        ;; referenced before this import.  But now we're doing this import.  I
        ;; think this is not okay.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (fatal :type :vl-tricky-shadowing
                   :msg "~a0: name ~s1 was previously used in this scope ~
                         (~a2), but the superior declaration is now being ~
                         shadowed by an import.  This is tricky and seems ~
                         error prone, so we do not support it."
                   :args (list ctx name entry.ctx))))

       ((when (eq entry.status :vl-local))
        ;; OK?  There is a local declaration of NAME before this import.  I
        ;; think this is fine because the local declaration is supposed to win.
        (mv scalist (ok))))

    (impossible)
    (mv scalist (ok))))


(define vl-shadowcheck-mark-names-wild-import
  :short "Record that a list of names are being imported by an @('import foo::*')."
  ((names    string-listp)
   (scalist  vl-shadowcheck-alist-p)
   (ctx      "The import construct.")
   (warnings vl-warninglist-p))
  :returns (mv (scalist vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-alist-fix scalist) (ok)))
       ((mv scalist warnings)
        (vl-shadowcheck-mark-name-wild-import (car names) scalist ctx warnings)))
    (vl-shadowcheck-mark-names-wild-import (cdr names) scalist ctx warnings)))


(define vl-shadowcheck-mark-name-direct-import
  :short "Record that a name is being imported by an @('import foo::bar')."
  ((name     stringp "Name being imported, i.e., @('bar').")
   (scalist  vl-shadowcheck-alist-p)
   (ctx      "The import construct.")
   (warnings vl-warninglist-p))
  :returns (mv (scalist vl-shadowcheck-alist-p)
               (warnings vl-warninglist-p))
  (b* ((name    (string-fix name))
       (scalist (vl-shadowcheck-alist-fix scalist))
       (entry   (cdr (hons-get name scalist)))
       ;; See particularly SystemVerilog-2012 Table 26-1 (Page 745), "Scoping
       ;; rules for package importation."
       ((unless entry)
        ;; OK.  No existing declaration of this name.  This import is as good
        ;; as a local declaration.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (ok)))

       ((vl-shadowcheck-entry entry))

       ((when (eq entry.status :vl-unused-superior))
        ;; OK.  There is some global declaration of this name but we've never
        ;; used it in this scope.  The import is like a local declaration.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (ok)))

       ((when (eq entry.status :vl-used-superior))
        ;; BAD.  There is some global declaration of this name that we've
        ;; already used in this scope.  This import is thus very tricky.
        (mv (hons-acons name
                        (make-vl-shadowcheck-entry :status :vl-local :ctx ctx)
                        scalist)
            (fatal :type :vl-tricky-shadowing
                   :msg "~a0: name ~s1 was previously used in this scope ~
                         (~a2), but the superior declaration is now being ~
                         shadowed by an import.  This is tricky and seems ~
                         error prone, so we do not support it."
                   :args (list ctx name entry.ctx))))

       ((when (eq entry.status :vl-local))
        ;; BAD.  There is already some local declaration of this name and yet
        ;; we are trying to import it explicitly.  This seems to be prohibited
        ;; by the rules in Table 26-1.
        (mv scalist
            (fatal :type :vl-bad-import
                   :msg "~a0: name ~s1 was previously declared in this scope ~
                         (~a2), so importing it is not allowed."
                   :args (list ctx name entry.ctx)))))
    (impossible)
    (mv scalist (ok))))




;; (define vl-shadowcheck-alist-do-import ((import   vl-import-p)
;;                                       (design   vl-design-p)
;;                                       (alist    vl-shadowcheck-alist-p)
;;                                       (warnings vl-warninglist-p))
;;   :returns (mv (new-alist vl-shadowcheck-alist-p)
;;                (warnings  vl-warninglist-p))
;;   (b* (((vl-design design))
;;        ((vl-import import))
;;        (package (vl-find-package import.pkg design.packages))
;;        ((unless package)
;;         (mv alist
;;             (fatal :type :vl-import-fail
;;                    :msg "~a0: can't import from unknown package ~s1."
;;                    :args (list import import.pkg))))
;;        ((names (if


;; (define vl-shadowcheck-alist-init ((design vl-design-p))
;;   :returns (alist vl-shadowcheck-alist-p)
;;   (b* (((vl-design x))
;;        (alist nil)
;;        ;; BOZO -- I'm pretty sure we don't care about shadowed names of
;;        ;;   mods, udps, interfaces, programs, packages, configs
;;        (alist (vl-shadowcheck-alist-init-aux (vl-vardecllist->names x.vardecls) alist))
;;        (alist (vl-shadowcheck-alist-init-aux (vl-taskdecllist->names x.taskdecls) alist))
;;        (alist (vl-shadowcheck-alist-init-aux (vl-fundecllist->names x.fundecls) alist))
;;        (alist (vl-shadowcheck-alist-init-aux (vl-paramdecllist->names x.paramdecls) alist))
;;        ;; I imagine we also don't care about shadowcheck the names of typedefs
;;        ;; or about forward typedefs

;;        ;;
;;        (alist (vl-shadowcheck-alist-init-aux (vl-



;; (define vl-extend-shadowcheck-globals-for-imports
;;   (globals



;; (define vl-check-for-scary-shadowcheck-aux
;;   ((x "Module elements to process, should be in the same order in which they
;;        were parsed."
;;       vl-genelementlist-p)
;;    (globals "Fast alist binding globally declared names to NIL if they have not
;;              yet been used in the current local scope, or to T if they have
;;              been used in the local scope.")
;;    (warnings "Warnings accumulator, may be extended with fatal warnings."
;;              vl-warninglist-p)
;;    (design   "The whole design, for dealing with imports."))
;;   (b* (((when (atom x))
;;         (ok))

;;        ((unless (eq (vl-genelement-kind (car x)) :vl-genbase))
;;         ;; Ignore generate constructs until unparameterization
;;         (vl-check-for-scary-shadowcheck-aux (cdr x) globals warnings))

;;        (elem (vl-genelement-fix (car x)))
;;        (item (vl-genbase->item elem))
;;        (tag  (tag item))

;;        ((when (eq tag :vl-port))
;;         ;; We shouldn't see any ports.
;;         (raise "We shouldn't see ports here.")
;;         (vl-check-for-scary-shadowcheck-aux (cdr x) globals warnings))



;;        ((when (or (eq tag :vl-portdecl)
;;                   (eq tag :vl-vardecl)
;;                   (eq tag :vl-paramdecl)
;;                   (eq
;;         ;; We have to first make sure that there aren't undeclared
;;         ;; identifiers being used in the range, then record that a
;;         ;; declaration was made.  Doing it in this order lets us catch
;;         ;; garbage like input [in:0] in;
;;         (b* (;; Note: We run into trouble here when ports are declared as user-defined types,
;;              ;; i.e. "input foo_t foo" -- we don't want to count foo_t as an undeclared id.
;;              ;; Thinking about it more, it doesn't seem like this is the right place to
;;              ;; be checking for this anyway, so just don't.
;;              ;; (names     (vl-exprlist-names (vl-portdecl-allexprs item)))
;;              ;; (warnings  (vl-warn-about-undeclared-wires item names portdecls decls warnings))
;;              (portdecls (hons-acons (vl-portdecl->name item) item portdecls)))
;;           (vl-make-implicit-wires-aux (cdr x) portdecls decls implicit warnings)))
