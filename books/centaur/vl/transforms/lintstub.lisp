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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "centaur/vl/mlib/expr-tools" :dir :system)
(include-book "centaur/vl/mlib/stmt-tools" :dir :system)
(include-book "centaur/vl/mlib/port-tools" :dir :system)
(include-book "centaur/vl/mlib/filter" :dir :system)
(include-book "centaur/vl/util/namedb" :dir :system)
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))
(local (std::add-default-post-define-hook :fix))
(defxdoc drop-lint-stubs
  :parents (vl-lint)
  :short "(Unsound transform) Replace instances annotated with LINT_IGNORE_INST,
          with an instance intended not to generate uninteresting lint
          warnings."
  :long "<p>The annotated instances are kept, but changed to reference a new
module.  The new module is a rewrite of the original instantiated module, which
may still be used elsewhere.  The new module's name is mangled to make it
unique and its ports are kept the same while its contents are changed so that
it trivially uses all inputs and sets all outputs.</p>

<p>This transform is done after elaboration so that we don't have to worry
about different versions of parameterized modules.</p>

<p>Note: currently missing support for interface ports.</p>")

(define vl-lint-stub-name ((name stringp))
  :returns (new-name stringp :rule-classes :type-prescription)
  (cat "__VL_LINT_STUB__" name))

(define vl-lint-stub-unique-name ((name stringp)
                                  (db vl-namedb-p))
  :returns (mv (new-name stringp :rule-classes :type-prescription)
               (new-db vl-namedb-p))
  (vl-namedb-plain-name (vl-lint-stub-name name)
                        (vl-namedb-fix db)))



;; To make sure all outputs are set, we just assign them all '0.
;; To make sure all inputs are used, we assign a new wire the xor of all their
;; unary xors -- that is, the parity of all input bits.
(defconst *vl-extensional-0* (make-vl-literal :val (make-vl-extint :value :vl-0val)))

(define lint-stub-output-driver ((x vl-portdecl-p))
  :returns (assign vl-assign-p)
  (b* (((vl-portdecl x)))
    (make-vl-assign :lvalue (vl-idexpr x.name)
                    :expr *vl-extensional-0*
                    :loc *vl-fakeloc*)))
       

(defprojection lint-stub-output-drivers ((x vl-portdecllist-p))
  :returns (assigns vl-assignlist-p)
  (lint-stub-output-driver x))



(define lint-stub-input-parity-expr ((x vl-portdecllist-p)
                                     (parity-acc vl-expr-p))
  :returns (parity vl-expr-p)
  (b* (((when (atom x)) (vl-expr-fix parity-acc))
       ((vl-portdecl x1) (car x))
       (parity1 (make-vl-unary :op :vl-unary-xor :arg (vl-idexpr x1.name)))
       (parity-acc (make-vl-binary :op :vl-binary-xor :left parity-acc :right parity1)))
    (lint-stub-input-parity-expr (cdr x) parity-acc)))

(define lint-stub-input-uses ((x vl-portdecllist-p))
  :returns (mv (vardecl vl-vardecl-p)
               (assign vl-assign-p))
  (b* ((inputs (vl-portdecls-with-dir :vl-input x))
       (inouts (vl-portdecls-with-dir :vl-inout x))
       (db (vl-starting-namedb (vl-portdecllist->names x)))
       ((mv new-wire db) (vl-namedb-plain-name "__vl_lint_stub_input_user__" db))
       (- (vl-free-namedb db))
       (vardecl (make-vl-vardecl :name new-wire
                                 :loc *vl-fakeloc*
                                 :type (make-vl-coretype :name :vl-logic)))
       (assign (make-vl-assign :lvalue (vl-idexpr new-wire)
                               :expr (lint-stub-input-parity-expr
                                       inouts
                                       (lint-stub-input-parity-expr
                                        inputs
                                        *vl-extensional-0*))
                               :loc *vl-fakeloc*)))
    (mv vardecl assign)))

(define vl-lint-stub-module ((x vl-module-p)
                             (new-name stringp))
  :returns (new-x vl-module-p)
  :guard-debug t
  (b* (((vl-module x))
       
       (inputs (vl-portdecls-with-dir :vl-input x.portdecls))
       (inouts (vl-portdecls-with-dir :vl-inout x.portdecls))
       (outputs (vl-portdecls-with-dir :vl-output x.portdecls))
       (names (vl-portdecllist->names x.portdecls))

       ;; Use the inputs:
       (db (vl-starting-namedb names))
       ((mv input-user-name db) (vl-namedb-plain-name "__vl_lint_stub_input_user__" db))
       (- (vl-free-namedb db))
       (input-user-vardecl (make-vl-vardecl :name input-user-name
                                            :loc *vl-fakeloc*
                                            :type (make-vl-coretype :name :vl-logic)))
       (input-user-assign (make-vl-assign :lvalue (vl-idexpr input-user-name)
                                          :expr (lint-stub-input-parity-expr
                                                 inouts
                                                 (lint-stub-input-parity-expr
                                                  inputs
                                                  *vl-extensional-0*))
                                          :loc *vl-fakeloc*))

       ;; Drive the outputs:
       (output-assigns (lint-stub-output-drivers (append-without-guard inouts outputs)))

       (port-vardecls (vl-keep-vardecls names x.vardecls)))

    (make-vl-module :name new-name
                    :minloc x.minloc
                    :maxloc x.maxloc
                    :origname new-name
                    :ports x.ports
                    :portdecls x.portdecls
                    :vardecls (cons input-user-vardecl port-vardecls)
                    ;; :modinsts nil
                    :assigns (cons input-user-assign output-assigns)
                    )))


;; NOTE: Unless we fix the defvisitor forms below, the scopestack will just be
;; design-level and not in the modinst's scope -- which is ok for now since we
;; only use it to look up module definitions.
(define vl-modinst-lint-stub ((x vl-modinst-p)
                              (stubs vl-modalist-p)
                              (db vl-namedb-p)
                              (ss vl-scopestack-p))
  :returns (mv (new-x vl-modinst-p)
               (new-stubs vl-modalist-p)
               (new-db vl-namedb-p))
  (b* (((vl-modinst x))
       (stubs (vl-modalist-fix stubs))
       (db (vl-namedb-fix db))
       ((unless (assoc-equal "LINT_IGNORE_INST" x.atts))
        (mv (vl-modinst-fix x)
            stubs db))
       (look (cdr (hons-get x.modname stubs)))
       ((when look)
        (mv (change-vl-modinst x :modname (vl-module->name look))
            stubs db))
       (mod (vl-scopestack-find-definition x.modname ss))
       ((unless (and mod (eq (tag mod) :vl-module)))
        (cw "Error in ~x0: module not found: ~s1~%"
            __function__ x.modname)
        (mv (vl-modinst-fix x) stubs db))
       ((mv new-modname db) (vl-lint-stub-unique-name x.modname db))
       (new-mod (vl-lint-stub-module mod new-modname))
       (new-x (change-vl-modinst x :modname new-modname)))
    (mv new-x
        (hons-acons x.modname new-mod (vl-modalist-fix stubs))
        db)))


;; NOTE: Because we only use the scopestack for looking up module definitions,
;; we don't do anything special with scopes such as genblocks/genarrays.
(fty::defvisitor-template lint-stub ((x :object)
                                     (stubs vl-modalist-p)
                                     (db vl-namedb-p)
                                     (ss vl-scopestack-p))
  :returns (mv (new-x :update)
               (new-stubs (:acc stubs :fix (vl-modalist-fix stubs)) vl-modalist-p)
               (new-db (:acc db :fix (vl-namedb-fix db)) vl-namedb-p))
  :type-fns ((vl-modinst vl-modinst-lint-stub))
  :fnname-template <type>-lint-stub)

(set-bogus-measure-ok t)

(local (in-theory (disable cons-equal
                           member-equal-when-member-equal-of-cdr-under-iff
                           double-containment
                           (tau-system))))

(fty::defvisitors vl-lint-stub
  :types (vl-modulelist)
  :template lint-stub)


(define vl-design-lint-stubs ((x vl-design-p))
  :returns (mv (new-x vl-design-p)
               (stubnames string-listp))
  :prepwork ((local (defthm string-listp-alist-keys-of-scopedef-alist
                      (implies (vl-scopedef-alist-p x)
                               (string-listp (alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (defthm vl-modulelist-p-alist-vals-of-modalist
                      (implies (vl-modalist-p x)
                               (vl-modulelist-p (alist-vals x)))
                      :hints(("Goal" :in-theory (enable alist-vals))))))
  (b* (((vl-design x) (vl-design-fix x))
       (ss (vl-scopestack-init x))
       (db (vl-starting-namedb (alist-keys (vl-scope-definition-alist x))))
       ((mv mods stubs db) (vl-modulelist-lint-stub x.mods nil db ss))
       (stubmods  (alist-vals stubs))
       (- (vl-free-namedb db))
       (new-mods (append-without-guard stubmods mods)))
    (mv (change-vl-design x :mods new-mods)
        (vl-modulelist->names stubmods))))
