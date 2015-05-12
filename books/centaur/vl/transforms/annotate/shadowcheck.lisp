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


(defxdoc shadowcheck
  :parents (make-implicit-wires)
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

(define vl-shadowcheck-push-scope ((x  vl-scope-p)
                                   (st vl-shadowcheck-state-p))
  :returns (st vl-shadowcheck-state-p)
  ;; Like vl-scopestack-push but for shadowcheck states.
  ;;  - Extends the scopestack by doing a push
  ;;  - Extends the lexscopes with a new, empty scope
  (b* (((vl-shadowcheck-state st)))
    (change-vl-shadowcheck-state st
                                 :lexscopes (vl-lexscopes-enter-new-scope st.lexscopes)
                                 :ss        (vl-scopestack-push x st.ss))))

(define vl-shadowcheck-pop-scope ((st vl-shadowcheck-state-p))
  :returns (st vl-shadowcheck-state-p)
  (b* (((vl-shadowcheck-state st)))
    (change-vl-shadowcheck-state st
                                 :lexscopes (vl-lexscopes-exit-scope st.lexscopes)
                                 :ss        (vl-scopestack-pop st.ss))))

(define vl-shadowcheck-declare-name ((name     stringp)
                                     (decl     acl2::any-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-shadowcheck-state st))
       (- (vl-shadowcheck-debug "    vl-shadowcheck-declare-name: ~s0 for ~a1.~%" name decl))
       ((mv lexscopes warnings)
        (vl-lexscopes-declare-name name decl st.lexscopes warnings))
       ;; I don't think we need to particularly do any cross-checking here.  By
       ;; extending the lexscope we will have checked for import/decl
       ;; conflicts, and we should be checking for redeclaration conflicts
       ;; elsewhere, so what else is there to do?
       (st (change-vl-shadowcheck-state st :lexscopes lexscopes)))
    (mv st warnings)))

(define vl-shadowcheck-declare-names ((names    string-listp)
                                      (decl     acl2::any-p)
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
                                       (ctx      acl2::any-p)
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
            (fatal :type :vl-undeclared-identifier
                   :msg "~a0: reference to undeclared identifier ~s1.~%"
                   :args (list ctx name))))
       ((vl-lexscope-entry entry))

       ((when (and (not entry.decl)
                   (not entry.direct-pkg)
                   (>= (len entry.wildpkgs) 2)))
        (mv st
            (fatal :type :vl-illegal-import
                   :msg "~a0: the name ~s1 is imported by multiple wildcard ~
                         imports: ~&2."
                   :args (list ctx name entry.wildpkgs))))

       ((mv item scopestack-at-import pkg-name)
        (vl-scopestack-find-item/context name st.ss))
       ((unless (or item pkg-name))
        (mv st
            (fatal :type :vl-programming-error
                   :msg "~a0: scopestack can't resolve ~s1 but it is found ~
                         in the lexical scope, so how could that happen? ~x2."
                   :args (list ctx name entry))))

       (ss-level  (vl-scopestack-nesting-level scopestack-at-import))
       (lex-level (len tail))
       ((unless (equal ss-level lex-level))
        (mv st
            (fatal :type :vl-tricky-scope
                   :msg "~a0: the name ~s1 has complex scoping that we do not ~
                         support.  Lexical level ~x2, scopestack level ~x3."
                   :args (list ctx name lex-level ss-level))))

       ((unless pkg-name)
        ;; Scopestack doesn't think this is imported from a package.
        (b* (((unless entry.decl)
              ;; Lexscope thinks it's imported from a package.  Wtf.
              (mv st (fatal :type :vl-tricky-scope
                            :msg "~a0: the name ~s1 has complex scoping that ~
                                  we do not support.  Lexically it appears to ~
                                  be imported from a package, but there is a ~
                                  subsequent declaration (~a2) which makes ~
                                  scoping confusing."
                            :args (list ctx name item)))))
          ;; We have a local declaration for it, so we don't think it's
          ;; imported either.  Looks like a match.
          (mv st (ok))))

       ;; Scopestack thinks the item comes from a package.
       ;; If scopestack gave us ITEM, it's the actual item from that package
       ;; If ITEM is nil, then either:
       ;;  - we found an import of foo::bar, but either bar isn't defined in
       ;;    that package, or foo doesn't exist.
       ;;  - we found an import of foo::*, but foo doesn't exist.
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
              (mv st (fatal :type :vl-import-conflict
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
        (mv st (fatal :type :vl-import-conflict
                      :msg "~a0: scopestack thinks ~s1 is imported from ~s2, ~
                            but lexically it is wildly imported from ~s3."
                      :args (list ctx name pkg-name lex-pkg)))))

    ;; If we get here, all package sanity checks pass.  We're good to go.
    (mv st (ok))))

(define vl-shadowcheck-reference-names ((names    string-listp)
                                        (ctx      acl2::any-p)
                                        (st       vl-shadowcheck-state-p)
                                        (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom names))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings)
        (vl-shadowcheck-reference-name (car names) ctx st warnings)))
    (vl-shadowcheck-reference-names (cdr names) ctx st warnings)))

(define vl-shadowcheck-portdecl ((x        vl-portdecl-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-portdecl x)  (vl-portdecl-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-portdecl-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-vardecl ((x        vl-vardecl-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-vardecl x)   (vl-vardecl-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-vardecl-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-typedef ((x        vl-typedef-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-typedef x)   (vl-typedef-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-typedef-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-paramdecl ((x        vl-paramdecl-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-paramdecl x) (vl-paramdecl-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-paramdecl-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-blockitem ((x        vl-blockitem-p)
                                  (st       vl-shadowcheck-state-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl (vl-shadowcheck-vardecl x st warnings))
      (:vl-import  (vl-shadowcheck-import  x st warnings))
      (otherwise   (vl-shadowcheck-paramdecl x st warnings)))))

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
  (b* ((x                (vl-assign-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-assign-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-gateinst ((x        vl-gateinst-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-gateinst x)  (vl-gateinst-fix x))
       (varnames         (mergesort (vl-exprlist-varnames (vl-gateinst-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
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
       (varnames         (mergesort (vl-exprlist-varnames (vl-modinst-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings))
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
       (varnames         (mergesort (vl-exprlist-varnames (vl-alias-allexprs x))))
       ((mv st warnings) (vl-shadowcheck-reference-names varnames x st warnings)))
    (mv st warnings)))


(defines vl-shadowcheck-stmt

  (define vl-shadowcheck-stmt ((x        vl-stmt-p)
                               (ctx      acl2::any-p)
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
          (b* ((varnames (mergesort (vl-exprlist-varnames (vl-stmt-allexprs x)))))
            (vl-shadowcheck-reference-names varnames x st warnings)))

         ((when (eq (vl-stmt-kind x) :vl-forstmt))
          ;; BOZO Need to think about this more carefully.
          (b* (((vl-forstmt x))
               (st (vl-shadowcheck-push-scope (vl-forstmt->blockscope x) st))
               ((mv st warnings) (vl-shadowcheck-blockitemlist x.initdecls st warnings))
               (local-exprs (vl-compoundstmt->exprs x))
               (local-names (vl-exprlist-varnames local-exprs))
               ((mv st warnings) (vl-shadowcheck-reference-names local-names x st warnings))
               ((mv st warnings) (vl-shadowcheck-stmtlist (vl-compoundstmt->stmts x) ctx st warnings))
               (st (vl-shadowcheck-pop-scope st)))
            (mv st warnings)))

         ((when (eq (vl-stmt-kind x) :vl-blockstmt))
          (b* (((vl-blockstmt x))
               (st (vl-shadowcheck-push-scope (vl-blockstmt->blockscope x) st))
               ;; Process declarations for the block, if any
               ((mv st warnings) (vl-shadowcheck-blockitemlist x.loaditems st warnings))
               ;; Process sub-statements, if any
               ((mv st warnings) (vl-shadowcheck-stmtlist x.stmts ctx st warnings))
               (st (vl-shadowcheck-pop-scope st)))
            (mv st warnings)))

         ;; No other statement has a scope, but compound statements might have
         ;; block statements inside of them.  See vl-stmt-check-undeclared.  We
         ;; don't use vl-stmt-allexprs here because it grabs exprs from
         ;; sub-statements, which need to be checked only in the sub-scope.
         (local-exprs (append (vl-maybe-delayoreventcontrol-allexprs (vl-compoundstmt->ctrl x))
                              (vl-compoundstmt->exprs x)))
         (local-names (vl-exprlist-varnames local-exprs))
         ((mv st warnings) (vl-shadowcheck-reference-names local-names x st warnings)))
      ;; Recursively check sub-statements.
      (vl-shadowcheck-stmtlist (vl-compoundstmt->stmts x) ctx st warnings)))

  (define vl-shadowcheck-stmtlist ((x        vl-stmtlist-p)
                                   (ctx      acl2::any-p)
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
  (verify-guards vl-shadowcheck-stmt
    :guard-debug t)
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


(define vl-shadowcheck-portdecllist ((x        vl-portdecllist-p)
                                     (st       vl-shadowcheck-state-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-portdecl (car x) st warnings)))
    (vl-shadowcheck-portdecllist (cdr x) st warnings)))

(define vl-shadowcheck-fundecl ((x        vl-fundecl-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-fundecl x)   (vl-fundecl-fix x))

       ;; BOZO this isn't quite right for the same reasons as in vl-fundecl-check-undeclared.
       (- (vl-shadowcheck-debug "  >> shadowcheck in function ~s0.~%" x.name))
       (- (vl-shadowcheck-debug "  >> checking externally used names in ports, return value~%"))
       (other-names (vl-exprlist-varnames (append (vl-portdecllist-allexprs x.portdecls)
                                                  (vl-datatype-allexprs x.rettype))))
       ((mv st warnings) (vl-shadowcheck-reference-names other-names x st warnings))

       (- (vl-shadowcheck-debug "  >> declaring function name, ~x0.~%" x.name))
       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings))

       (- (vl-shadowcheck-debug "  >> pushing into function ~x0.~%" x.name))
       (st (vl-shadowcheck-push-scope (vl-fundecl->blockscope x) st))
       ((mv st warnings) (vl-shadowcheck-portdecllist x.portdecls st warnings))

       ;; BOZO eventually do something sensible with name in the inner scope,
       ;; and in scopestack.  Perhaps some kind of transform that adds a
       ;; VL_FUNCTION_IMPLICIT declaration for the return value or something.
       ;;
       ;; ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings))

       ((mv st warnings) (vl-shadowcheck-blockitemlist x.parsed-blockitems st warnings))
       ((mv st warnings) (vl-shadowcheck-stmt x.body x st warnings))
       (- (vl-shadowcheck-debug "  >> popping out of function ~x0.~%" x.name))
       (st (vl-shadowcheck-pop-scope st)))
    (mv st warnings)))

(define vl-shadowcheck-taskdecl ((x        vl-taskdecl-p)
                                 (st       vl-shadowcheck-state-p)
                                 (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((vl-taskdecl x)   (vl-taskdecl-fix x))

       (other-names      (vl-exprlist-varnames (vl-portdecllist-allexprs x.portdecls)))
       ((mv st warnings) (vl-shadowcheck-reference-names other-names x st warnings))

       (st (vl-shadowcheck-push-scope (vl-taskdecl->blockscope x) st))
       ((mv st warnings) (vl-shadowcheck-portdecllist x.portdecls st warnings))
       ((mv st warnings) (vl-shadowcheck-blockitemlist x.parsed-blockitems st warnings))
       ((mv st warnings) (vl-shadowcheck-stmt x.body x st warnings))
       (st (vl-shadowcheck-pop-scope st))

       ((mv st warnings) (vl-shadowcheck-declare-name x.name x st warnings)))
    (mv st warnings)))

(define vl-shadowcheck-aux
  :short "Main function for checking for name shadowing."
  ((x        vl-genelementlist-p
             "Module elements to process, should be in the same order in which they
              were parsed.")
   (st       vl-shadowcheck-state-p)
   (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  :measure (len x)
  (b* ((x        (vl-genelementlist-fix x))
       (st       (vl-shadowcheck-state-fix st))
       (warnings (vl-warninglist-fix warnings))

       ((when (atom x))
        (mv st warnings))

       ((unless (eq (vl-genelement-kind (car x)) :vl-genbase))
        ;; Ignore generate constructs until unparameterization
        (vl-shadowcheck-aux (cdr x) st warnings))

       (elem (vl-genelement-fix (car x)))
       (item (vl-genbase->item elem))
       (tag  (tag item))

       (- (vl-shadowcheck-debug "  ---- ~a0 ---- ~%" item))

       ((when (or (eq tag :vl-interfaceport)
                  (eq tag :vl-regularport)))
        ;; We shouldn't see any ports.
        (raise "We shouldn't see ports here.")
        (vl-shadowcheck-aux (cdr x) st warnings))

       ((when (eq tag :vl-portdecl))
        (b* (((mv st warnings) (vl-shadowcheck-portdecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-vardecl))
        (b* (((mv st warnings) (vl-shadowcheck-vardecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-paramdecl))
        (b* (((mv st warnings) (vl-shadowcheck-paramdecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-assign))
        (b* (((mv st warnings) (vl-shadowcheck-assign item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-gateinst))
        (b* (((mv st warnings) (vl-shadowcheck-gateinst item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-modinst))
        (b* (((mv st warnings) (vl-shadowcheck-modinst item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-always))
        (b* (((mv st warnings) (vl-shadowcheck-always item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-initial))
        (b* (((mv st warnings) (vl-shadowcheck-initial item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-fundecl))
        (b* (((mv st warnings) (vl-shadowcheck-fundecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-taskdecl))
        (b* (((mv st warnings) (vl-shadowcheck-taskdecl item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-import))
        (b* (((mv st warnings) (vl-shadowcheck-import item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))

       ((when (eq tag :vl-typedef))
        (b* (((mv st warnings) (vl-shadowcheck-typedef item st warnings)))
          (vl-shadowcheck-aux (cdr x) st warnings)))
        

       ;; BOZO implement everything else
       (warnings (fatal :type :vl-unexpected-modelement
                        :msg "~a0: unexpected kind of module item."
                        :args (list item))))
    (vl-shadowcheck-aux (cdr x) st warnings)))

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

(define vl-shadowcheck-module ((x  vl-module-p)
                               (st vl-shadowcheck-state-p))
  :returns (mv (st    vl-shadowcheck-state-p)
               (new-x vl-module-p))
  (b* (((vl-module x)    (vl-module-fix x))
       (x.loaditems (and x.parse-temps (vl-parse-temps->loaditems x.parse-temps)))
       (- (vl-shadowcheck-debug "*** Shadowcheck module ~s0 ***~%" x.name))
       (warnings         x.warnings)
       (st               (vl-shadowcheck-push-scope x st))
       ((mv st warnings) (vl-shadowcheck-ports x.ports st warnings))
       ((mv st warnings) (vl-shadowcheck-aux x.loaditems st warnings))
       (st               (vl-shadowcheck-pop-scope st))
       (new-x            (change-vl-module x
                                           :warnings warnings
                                           :parse-temps nil)))
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

(define vl-shadowcheck-imports ((x        vl-importlist-p)
                                (st       vl-shadowcheck-state-p)
                                (warnings vl-warninglist-p))
  :returns (mv (st       vl-shadowcheck-state-p)
               (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv (vl-shadowcheck-state-fix st) (ok)))
       ((mv st warnings) (vl-shadowcheck-import (car x) st warnings)))
    (vl-shadowcheck-imports (cdr x) st warnings)))


(define vl-shadowcheck-design ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (warnings x.warnings)

       (st (make-vl-shadowcheck-state :lexscopes (list (vl-empty-lexscope))
                                      :ss        (vl-scopestack-init x)
                                      :design    x))

       ;; It would perhaps be better to construct the initial scopes using the
       ;; program order?  But some simulators allow you to refer to things that
       ;; are defined later, for instance, NCVerilog allows you to write foo::w
       ;; before defining package foo.
       (itemnames (append (vl-vardecllist->names x.vardecls)
                          (vl-paramdecllist->names x.paramdecls)
                          (vl-fundecllist->names x.fundecls)
                          (vl-taskdecllist->names x.taskdecls)
                          (vl-typedeflist->names x.typedefs)))
       (dupes (duplicated-members itemnames))
       (warnings (if (not dupes)
                     (ok)
                   (fatal :type :vl-name-clash
                          :msg "Name clash among globals: ~&0."
                          :args (list dupes))))

       ((mv st warnings) (vl-shadowcheck-declare-typedefs x.typedefs st warnings))
       ((mv st warnings) (vl-shadowcheck-vardecls   x.vardecls st warnings))
       ((mv st warnings) (vl-shadowcheck-paramdecls x.paramdecls st warnings))
       ((mv st warnings) (vl-shadowcheck-fundecls   x.fundecls st warnings))
       ((mv st warnings) (vl-shadowcheck-taskdecls  x.taskdecls st warnings))
       ((mv st warnings) (vl-shadowcheck-imports    x.imports st warnings))

       ((mv st mods) (vl-shadowcheck-modules x.mods st))

       (?st (vl-shadowcheck-pop-scope st))
       (-   (vl-scopestacks-free)))
    (change-vl-design x
                      :mods mods
                      :warnings warnings)))

