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
(include-book "../mlib/scopestack")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/strip")
(include-book "../mlib/fmt")
(include-book "../mlib/print-warnings")
(include-book "../mlib/expr-tools")
(include-book "../mlib/hid-tools")
(include-book "../mlib/reportcard")
(include-book "../mlib/hid-tools")
(include-book "../util/cwtime")
(include-book "../util/sum-nats")
(include-book "../util/merge-indices")
(include-book "typo-detect")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(include-book "std/testing/assert" :dir :system)
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


(defthm vl-scopestack->design-of-vl-scopestack-local
  (equal (vl-scopestack->design (vl-scopestack-local scope ss))
         (vl-scopestack->design ss))
  :hints(("Goal" :expand ((vl-scopestack->design (vl-scopestack-local scope ss))))))

(defthm vl-scopestack->design-of-vl-scopestack-push
  (equal (vl-scopestack->design (vl-scopestack-push scope ss))
         (vl-scopestack->design ss))
  :hints(("Goal" :in-theory (enable vl-scopestack-push))))


(defxdoc lucid
  :parents (vl-lint)
  :short "Check for unused, unset, spurious wires, and multiply driven wires."
  :long "<p>Lucid is a @(see vl-lint) check that scans your design for:</p>

<ul>
<li>Spurious wires&mdash;never used or set anywhere,</li>
<li>Unset variables&mdash;used without being driven (scary),</li>
<li>Unused variables&mdash;driven but never used, and</li>
<li>Multiply driven wires&mdash;which are often not desired.</li>
</ul>

<p>These warnings are often about entire wires, but Lucid also carries out a
bit-level analysis and can often detect when only a portion of a wire is
unused, unset, or multiply driven.</p>

<p>Typically Lucid is invoked as part of @(see vl-lint); its warnings are found
in the file @('vl-lucid.txt').</p>

<p>We have found Lucid to be most useful when refactoring designs and moving
functionality from one module to another.  In these situations, it is often
very easy to accidentally leave some wires (or logic) behind, so seeing what is
undriven or unset can be really handy.</p>")



; State Representation --------------------------------------------------------

(local (xdoc::set-default-parents vl-lucidstate))

(defprod vl-lucidkey
  :layout :tree
  :hons t
  :short "A single key in the lucid database."
  ((item       vl-scopeitem-p "The item we're dealing with.")
   (scopestack vl-scopestack  "The scopestack where this key was found."))
  :long "<p>Keys are honsed, even though this is expensive, so that they can be
used in fast alists.</p>")

(fty::deflist vl-lucidkeylist
  :elt-type vl-lucidkey)

(defprod vl-lucidctx
  :short "Info about a usage/setting of an identifier"
  ((modname   stringp "Name of the module or other top-level construct in which the use/set occurred")
   (elem      vl-ctxelement-p "Element in which it occurred")
   (ss        vl-scopestack-p "Scopestack under which the element was found")
   (portname  maybe-stringp "If passed to an instance port argument, which port?"))
  :layout :tree)



(deftagsum vl-lucidocc
  :short "Record of an occurrence of an identifier."

  (:solo
   :short "A lone instance of an identifier."
   :long "<p>We use this to record occurrences of an identifier all by itself,
e.g., in an assignment like @('assign ... = b + c[3:0]'), we would record a
solo occurrence of @('b').</p>"

   ((ctx vl-lucidctx-p
         "The general context where the usage occurred.  Knowing where the
          occurrence came from is useful when we need to report about multiply
          driven signals.")))

  (:slice
   :short "An indexed occurrence of an identifier."
   :long "<p>We use this to record occurrences of an identifier with a bit- or
part-select.  For individual selects like @('foo[3]'), both left and right will
be the same.</p>"
   ((left  vl-expr-p)
    (right vl-expr-p)
    (ctx   vl-lucidctx-p
           "The general context where the usage occurred.  Knowing where the
            occurrence came from is useful when we need to report about
            multiply driven signals.")))

  (:tail
   :short "An occurrence of an identifier with something fancy."
   :long "<p>We use this to record occurrences of a variable where there is
additional indexing or some kind of struct field referencing.  For instance, if
we have a variable, @('myinst'), which is an @('instruction_t') structure, then
we might have reads or writes of individual fields, like @('myinst.opcode') or
@('myinst.arg1').  We don't currently record what the tail is or analyze it in
any sensible way, but this at least allows us to see that something has been
read/written.</p>"
   ((ctx vl-lucidctx-p
         "The general context where the usage occurred.  Knowing where the
            occurrence came from is useful when we need to report about
            multiply driven signals."))))

(define vl-lucidocc->ctx ((x vl-lucidocc-p))
  :returns (ctx vl-lucidctx-p)
  :inline t
  (vl-lucidocc-case x
    :solo x.ctx
    :slice x.ctx
    :tail x.ctx))

(define vl-lucidocc->ss ((x vl-lucidocc-p))
  :returns (ss vl-scopestack-p)
  :inline t
  (vl-lucidctx->ss (vl-lucidocc->ctx x)))

(fty::deflist vl-lucidocclist
  :elt-type vl-lucidocc)

(defprod vl-lucidval
  :short "Use/set information about a single variable."
  ((used   vl-lucidocclist-p
           "List of occurrences where this variable is used.")
   (set    vl-lucidocclist-p
           "List of occurrences where this variable is set.")
   (errors true-listp
           "Information on any errors related to analyzing this key.")))

(defval *vl-empty-lucidval*
  :parents (vl-lucidval)
  (make-vl-lucidval :used nil
                    :set nil
                    :errors nil))

(fty::defalist vl-luciddb
  :short "The main @(see lucid) database.  Binds keys (scopestack/item pairs)
          to information about how they have been used."
  :key-type vl-lucidkey
  :val-type vl-lucidval
  :count vl-luciddb-count)

(fty::defprod vl-lucidstate
  :parents (lucid)
  :layout :tree
  :short "State for the lucid transform."
  ((db      vl-luciddb-p
            "Main database mapping keys to their use/set occurrences.")

   (modportsp booleanp :rule-classes :type-prescription
              "Should we issue warnings for modports?  It generally will only
               make sense to do this <i>before</i> unparameterization has taken
               place, because unparameterization can change the names of
               interfaces and our argresolve handling drops the arg.modport
               stuff in a way that makes this too hard to handle.")

   (paramsp booleanp :rule-classes :type-prescription
            "Should we issue warnings for parameters?  It generally will only
             make sense to do this <i>before</i> unparameterization has taken
             place, because unparameterization should generally get rid of any
             sensible parameters.")

   (generatesp booleanp :rule-classes :type-prescription
               "Should we include multidrive warnings in generates?  It will
                generally only make sense to do this <i>after</i>
                unparameterization, because until then things like

                @({ if (condition) assign foo = 1;
                    else assign foo = 0; })

                may appear to be multiple assignments to @('foo'), even though
                they never happen at the same time.")

   (warnings vl-warninglist-p)))



; State Initialization --------------------------------------------------------

(local (xdoc::set-default-parents vl-lucidstate-init))

(define vl-scope-luciddb-init-aux
  :parents (vl-scope-luciddb-init)
  ((locals vl-scopeitem-alist-p "The local variables declared in some scope.")
   (ss vl-scopestack-p          "Scopestack for our current location.")
   (db vl-luciddb-p             "Database we're initializing."))
  :returns
  (new-db vl-luciddb-p "Database extended with all the variables in @('locals').")
  :measure (vl-scopeitem-alist-count locals)
  (b* ((locals (vl-scopeitem-alist-fix locals))
       ((when (atom locals))
        (vl-luciddb-fix db))
       ((cons ?name item) (car locals))
       (key (make-vl-lucidkey :item item :scopestack ss))
       (db  (hons-acons key *vl-empty-lucidval* db)))
    (vl-scope-luciddb-init-aux (cdr locals) ss db)))

(define vl-scope-luciddb-init
  :short "Initialize variables for a scope."
  ((x  vl-scope-p      "Current scope we're processing, already added to the scopestack.")
   (ss vl-scopestack-p "Scopestack for our current location.")
   (db vl-luciddb-p    "Database we're initializing."))
  :returns
  (new-db vl-luciddb-p "Database extended with all variables from this scope.")

  :long "<p>The scopeinfo for @('x') has locals, imports, and star-packages,
but we only want the locals: any imports or star-packages are of course
relevant for looking up variables, but those variables will have their own keys
created when we process their packages, etc.</p>"

  (b* ((x      (vl-scope-fix x))
       (info   (vl-scope->scopeinfo x (vl-scopestack->design ss)))
       (locals (vl-scopeinfo->locals info)))
    (vl-scope-luciddb-init-aux locals ss db)))

(defines vl-stmt-luciddb-init

  (define vl-stmt-luciddb-init ((x  vl-stmt-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
    :returns (new-db vl-luciddb-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (vl-luciddb-fix db))
         ((when (vl-stmt-case x :vl-blockstmt))
          ;; NOTE -- This must be kept in sync with vl-stmt-lucidcheck!!
          ;; Obeys the One True Way to process a Block Statement
          (b* ((blockscope (vl-blockstmt->blockscope x))
               (ss         (vl-scopestack-push blockscope ss))
               (db         (vl-scope-luciddb-init blockscope ss db)))
            (vl-stmtlist-luciddb-init (vl-blockstmt->stmts x) ss db)))
         ((when (vl-stmt-case x :vl-forstmt))
          ;; NOTE -- This must be kept in sync with vl-stmt-lucidcheck!!
          ;; Obeys the One True Way to process a For Statement.
          (b* ((blockscope (vl-forstmt->blockscope x))
               (ss         (vl-scopestack-push blockscope ss))
               (db         (vl-scope-luciddb-init blockscope ss db)))
            (vl-stmtlist-luciddb-init (vl-compoundstmt->stmts x) ss db)))
         ((when (vl-stmt-case x :vl-foreachstmt))
          ;; NOTE -- This must be kept in sync with vl-stmt-lucidcheck!!
          ;; Obeys the One True Way to process a Foreach Statement.
          (b* ((blockscope (vl-foreachstmt->blockscope x))
               (ss         (vl-scopestack-push blockscope ss))
               (db         (vl-scope-luciddb-init blockscope ss db)))
            (vl-stmtlist-luciddb-init (vl-compoundstmt->stmts x) ss db))))
      (vl-stmtlist-luciddb-init (vl-compoundstmt->stmts x) ss db)))

  (define vl-stmtlist-luciddb-init ((x  vl-stmtlist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
    :returns (new-db vl-luciddb-p)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (vl-luciddb-fix db))
         (db (vl-stmt-luciddb-init (car x) ss db)))
      (vl-stmtlist-luciddb-init (cdr x) ss db)))
  ///
  (verify-guards vl-stmt-luciddb-init)
  (deffixequiv-mutual vl-stmt-luciddb-init))

(define vl-always-luciddb-init ((x  vl-always-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (vl-stmt-luciddb-init (vl-always->stmt x) ss db))

(define vl-alwayslist-luciddb-init ((x  vl-alwayslist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-always-luciddb-init (car x) ss db)))
    (vl-alwayslist-luciddb-init (cdr x) ss db)))

(define vl-initial-luciddb-init ((x  vl-initial-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (vl-stmt-luciddb-init (vl-initial->stmt x) ss db))

(define vl-initiallist-luciddb-init ((x  vl-initiallist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-initial-luciddb-init (car x) ss db)))
    (vl-initiallist-luciddb-init (cdr x) ss db)))

(define vl-final-luciddb-init ((x  vl-final-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (vl-stmt-luciddb-init (vl-final->stmt x) ss db))

(define vl-finallist-luciddb-init ((x  vl-finallist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-final-luciddb-init (car x) ss db)))
    (vl-finallist-luciddb-init (cdr x) ss db)))

(define vl-fundecl-luciddb-init ((x  vl-fundecl-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((scope (vl-fundecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (db    (vl-scope-luciddb-init scope ss db)))
    (vl-stmt-luciddb-init (vl-fundecl->body x) ss db)))

(define vl-fundecllist-luciddb-init ((x  vl-fundecllist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-fundecl-luciddb-init (car x) ss db)))
    (vl-fundecllist-luciddb-init (cdr x) ss db)))

(define vl-taskdecl-luciddb-init ((x  vl-taskdecl-p)
                                  (ss vl-scopestack-p)
                                  (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((scope (vl-taskdecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (db    (vl-scope-luciddb-init scope ss db)))
    (vl-stmt-luciddb-init (vl-taskdecl->body x) ss db)))

(define vl-taskdecllist-luciddb-init ((x  vl-taskdecllist-p)
                                      (ss vl-scopestack-p)
                                      (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-taskdecl-luciddb-init (car x) ss db)))
    (vl-taskdecllist-luciddb-init (cdr x) ss db)))

(local (defthm vl-genblob-count-of-vl-genblock->genblob-l0*
         (implies (EQUAL (VL-GENELEMENT-KIND X) :VL-GENLOOP)
                  (< (VL-GENBLOB-COUNT (VL-GENBLOCK->GENBLOB (VL-GENLOOP->BODY X)))
                     (VL-GENBLOB-GENERATE-COUNT X)))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :expand ((vl-genblock->genblob (vl-genloop->body x)))))))

(local (defthm vl-genblob-count-of-vl-genblock->genblob-l1*
         (< (VL-GENBLOB-COUNT (VL-GENBLOCK->GENBLOB X))
            (VL-GENBLOB-GENBLOCK-COUNT X))
         ;; BOZO probably we should rework the vl-genblock-count stuff to use
         ;; vl-genblock->genblob instead of calling vl-sort-genelements itself.
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :expand ((vl-genblob-genblock-count x)
                                 (vl-genblock->genblob x))))))

(define vl-lucid-paramdecl-for-genloop ((name     stringp)
                                        (loc      vl-location-p))
  :returns (decl vl-paramdecl-p)
  (make-vl-paramdecl :name name
                     :localp t
                     :type (make-vl-explicitvalueparam :type *vl-plain-old-integer-type*)
                     :loc loc))

(define vl-lucid-genvar-scope ((name    stringp)
                               (loc     vl-location-p))
  :returns (ss vl-scope-p)
  (b* ((genvar (make-vl-genvar :name name :loc loc))
       (blob   (make-vl-genblob :genvars (list genvar)
                                :scopetype :vl-genarray
                                :id (str::cat "<generate-array-" name ">"))))
    blob))

(defines vl-genblob-luciddb-init
  :verify-guards nil

  (define vl-genblob-luciddb-init-subscopes ((x vl-genblob-p)
                                             (ss vl-scopestack-p)
                                             (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-count x) 0)
    ;; Here we assume that
    ;;
    ;;  (1) the scope for the genblob has already been pushed onto the scopestack
    ;;  (2) all local declarations within the scope have already been initialized
    ;;      in the luciddb.
    ;;
    ;; We therefore don't have to do anything more with the vardecls,
    ;; paramdecls, assignments, instances, aliases, modports, etc.  (Those are
    ;; handled by vl-scope-luciddb-init).
    ;;
    ;; However, we *do* need to initialize anything that potentially has
    ;; subscopes, for instance, a function declaration's body has its own scope
    ;; so we need to descend into it.
    (b* ((ss (vl-scopestack-fix ss))
         (db (vl-luciddb-fix db))
         ((vl-genblob x) (vl-genblob-fix x))
         (db (vl-genelementlist-luciddb-init x.generates ss db))
         (db (vl-fundecllist-luciddb-init x.fundecls ss db))
         (db (vl-taskdecllist-luciddb-init x.taskdecls ss db))
         (db (vl-alwayslist-luciddb-init x.alwayses ss db))
         (db (vl-initiallist-luciddb-init x.initials ss db))
         (db (vl-finallist-luciddb-init x.finals ss db)))
      db))

  (define vl-genblob-luciddb-init ((x  vl-genblob-p)
                                   (ss vl-scopestack-p)
                                   (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-count x) 1)
    ;; Fully initialize the database for a genblob that introduces its own scope.
    ;; Pushes a new scope.
    (b* ((x  (vl-genblob-fix x))
         (ss (vl-scopestack-fix ss))
         (db (vl-luciddb-fix db))
         (ss (vl-scopestack-push x ss))
         (db (vl-scope-luciddb-init x ss db))
         (db (vl-genblob-luciddb-init-subscopes x ss db)))
      db))

  (define vl-genblock-luciddb-init ((x  vl-genblock-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-genblock-count x) 0)
    (b* (((vl-genblock x))
         (blob (vl-genblock->genblob x))
         ((when x.condnestp)
          ;; Special case where this block doesn't introduce a scope.  Don't
          ;; push a scope, just go process the elements.
          (vl-genblob-luciddb-init-subscopes blob ss db)))
      (vl-genblob-luciddb-init blob ss db)))

  (define vl-genelementlist-luciddb-init ((x  vl-genelementlist-p)
                                          (ss vl-scopestack-p)
                                          (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-generates-count x) 0)
    (b* (((when (atom x))
          (vl-luciddb-fix db))
         (db (vl-genelement-luciddb-init (car x) ss db)))
      (vl-genelementlist-luciddb-init (cdr x) ss db)))

  (define vl-genelement-luciddb-init ((x  vl-genelement-p)
                                      (ss vl-scopestack-p)
                                      (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-generate-count x) 0)
    (b* ((x  (vl-genelement-fix x))
         (db (vl-luciddb-fix db)))
      (vl-genelement-case x
        :vl-genbase
        (progn$
         ;; We shouldn't encounter these because vl-genblock->genblob should
         ;; properly sort out all the genbases into other kinds of elements.
         (raise "Programming error: should not encounter :vl-genbase, but
                 found ~s0.~%" (with-local-ps (vl-cw "~a0~%" x)))
         db)
        :vl-genbegin
        (vl-genblock-luciddb-init x.block ss db)
        :vl-genif
        (b* ((db (vl-genblock-luciddb-init x.then ss db))
             (db (vl-genblock-luciddb-init x.else ss db)))
          db)
        :vl-genarray
        ;; Note: elaboration adds a parameter declaration for the loop variable
        ;; into each block, so we don't need to do this part.  However, we still
        ;; add a scope for a local genvar, if applicable.  This makes it so that
        ;; lucidcheck can blindly mark the loop variable as used/set and things
        ;; work out whether there's it's defined locally or earlier.
        (b* (((mv ss db)
              (b* (((unless x.genvarp)
                    (mv ss db))
                   (scope (vl-lucid-genvar-scope x.var x.loc))
                   (ss    (vl-scopestack-push scope ss))
                   (db    (vl-scope-luciddb-init scope ss db)))
                (mv ss db))))
          (vl-genblocklist-luciddb-init x.blocks ss db))
        :vl-genloop
        ;; Subtle.  See SystemVerilog-2012 Section 27.4 and also see the
        ;; related case in vl-shadowcheck-genelement.  So before we go into the
        ;; body, we'll create a new scope with the parameter declaration in it.
        ;; ALSO, if this loop has its own local genvar declaration, we'll add
        ;; an extra layer of scope for that, because it just seems like the
        ;; most sensible way to do it.
        (b* ((blob (vl-genblock->genblob x.body))
             ((mv ss db)
              (b* (((unless x.genvarp)
                    (mv ss db))
                   (scope (vl-lucid-genvar-scope x.var x.loc))
                   (ss    (vl-scopestack-push scope ss))
                   (db    (vl-scope-luciddb-init scope ss db)))
                (mv ss db)))
             (var-paramdecl (vl-lucid-paramdecl-for-genloop x.var x.loc))
             (extended-blob (change-vl-genblob blob
                                               :paramdecls (cons var-paramdecl (vl-genblob->paramdecls blob))))
             ;; Use the extended blob to initialize all locals (which will
             ;; result in the paramdecl getting initialized)
             (ss (vl-scopestack-push extended-blob ss))
             (db (vl-scope-luciddb-init extended-blob ss db))
             ;; Now add in any sub-scopes, using the non-extended blob (which
             ;; is legitimate since the paramdecl doesn't introduce subscopes,
             ;; and makes termination easy)
             (db (vl-genblob-luciddb-init-subscopes blob ss db)))
          db)
        :vl-gencase
        (b* ((db (vl-gencaselist-luciddb-init x.cases ss db))
             (db (vl-genblock-luciddb-init x.default ss db)))
          db))))

  (define vl-gencaselist-luciddb-init ((x vl-gencaselist-p)
                                       (ss vl-scopestack-p)
                                       (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-gencaselist-count x) 0)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x))
          (vl-luciddb-fix db))
         ((cons ?exprs block) (car x))
         (db (vl-genblock-luciddb-init block ss db)))
      (vl-gencaselist-luciddb-init (cdr x) ss db)))

  (define vl-genblocklist-luciddb-init ((x vl-genblocklist-p)
                                        (ss vl-scopestack-p)
                                        (db vl-luciddb-p))
    :returns (db vl-luciddb-p)
    :measure (two-nats-measure (vl-genblob-genblocklist-count x) 0)
    (b* (((when (atom x))
          (vl-luciddb-fix db))
         (db (vl-genblock-luciddb-init (car x) ss db)))
      (vl-genblocklist-luciddb-init (cdr x) ss db)))
  ///
  (verify-guards vl-genblob-luciddb-init)
  (deffixequiv-mutual vl-genblob-luciddb-init))

(define vl-module-luciddb-init ((x  vl-module-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((genblob (vl-module->genblob x))
       (db (vl-genblob-luciddb-init genblob ss db)))
    db))

(define vl-modulelist-luciddb-init ((x  vl-modulelist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-module-luciddb-init (car x) ss db)))
    (vl-modulelist-luciddb-init (cdr x) ss db)))

(define vl-package-luciddb-init ((x  vl-package-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((vl-package x) (vl-package-fix x))
       (ss (vl-scopestack-push x ss))
       (db (vl-scope-luciddb-init x ss db))
       (db (vl-fundecllist-luciddb-init x.fundecls ss db))
       (db (vl-taskdecllist-luciddb-init x.taskdecls ss db)))
    db))

(define vl-packagelist-luciddb-init ((x  vl-packagelist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-package-luciddb-init (car x) ss db)))
    (vl-packagelist-luciddb-init (cdr x) ss db)))

(define vl-interface-luciddb-init ((x  vl-interface-p)
                                   (ss vl-scopestack-p)
                                   (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((genblob (vl-interface->genblob x))
       (db (vl-genblob-luciddb-init genblob ss db)))
    db))

(define vl-interfacelist-luciddb-init ((x  vl-interfacelist-p)
                                       (ss vl-scopestack-p)
                                       (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-interface-luciddb-init (car x) ss db)))
    (vl-interfacelist-luciddb-init (cdr x) ss db)))

(define vl-luciddb-init
  :short "Construct the initial @(see lucid) database for a design."
  ((x vl-design-p))
  :returns (db vl-luciddb-p)
  (b* (((vl-design x) (vl-design-fix x))
       (ss   (vl-scopestack-init x))
       (db   nil)
       (db   (vl-scope-luciddb-init x ss db))
       (db   (vl-modulelist-luciddb-init    x.mods        ss db))
       (db   (vl-fundecllist-luciddb-init   x.fundecls    ss db))
       (db   (vl-taskdecllist-luciddb-init  x.taskdecls   ss db))
       (db   (vl-packagelist-luciddb-init   x.packages    ss db))
       (db   (vl-interfacelist-luciddb-init x.interfaces  ss db)))
    db))

(define vl-lucidstate-init
  :parents (lucid)
  :short "Construct the initial @(see lucid) state for a design."
  ((x vl-design-p)
   &key
   ((paramsp booleanp) 't)
   ((modportsp booleanp) 't)
   ((generatesp booleanp) 't))
  :returns (st vl-lucidstate-p)
  (make-vl-lucidstate :db (vl-luciddb-init x)
                      :modportsp modportsp
                      :paramsp paramsp
                      :generatesp generatesp))


; State Debugging -------------------------------------------------------------

(local (xdoc::set-default-parents vl-pps-lucidstate))

(define vl-pp-scope-name ((x vl-scope-p) &key (ps 'ps))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable vl-printable-p))))
  (b* ((x    (vl-scope-fix x))
       (name (vl-scope->id x)))
    (if name
        (vl-print name)
      (vl-ps-seq (vl-print "<unnamed-")
                 (vl-print-str (symbol-name (tag x)))
                 (vl-print ">")))))

(define vl-pp-scopestack-path ((x vl-scopestack-p) &key (ps 'ps))
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null   (vl-print ":null")
    :global (vl-ps-seq (vl-print "$root"))
    :local  (vl-ps-seq (vl-pp-scopestack-path x.super)
                       (vl-print ".")
                       (vl-pp-scope-name x.top))))

(define vl-pps-scopestack-path ((x vl-scopestack-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-scopestack-path x)))

(define vl-lucid-mash-tag ((x stringp))
  :returns (new-x stringp :rule-classes :type-prescription)
  (b* ((x (string-fix x))
       (x (str::strsubst "VL-" "" x))
       (x (str::strsubst "DECL" "" x))
       (x (str::downcase-string x)))
    x)
  ///
  (assert! (equal (vl-lucid-mash-tag "VL-VARDECL") "var"))
  (assert! (equal (vl-lucid-mash-tag "VL-PARAMDECL") "param"))
  (assert! (equal (vl-lucid-mash-tag "VL-FUNDECL") "fun"))
  (assert! (equal (vl-lucid-mash-tag "VL-TASKDECL") "task")))

(define vl-pp-lucidkey ((x vl-lucidkey-p) &key (ps 'ps))
  :prepwork ((local (defthm l0
                      (implies (vl-scopeitem-p x)
                               (symbolp (tag x)))
                      :hints(("Goal" :in-theory (enable vl-scopeitem-p
                                                        tag))))))
  (b* (((vl-lucidkey x) (vl-lucidkey-fix x))
       (name (vl-scopeitem->name x.item)))
    (vl-ps-seq (vl-pp-scopestack-path x.scopestack)
               (if name
                   (vl-ps-seq (vl-print ".")
                              (vl-print name))
                 (vl-ps-seq
                  (vl-print ".<unnamed ")
                  (vl-print-str (vl-lucid-mash-tag (symbol-name (tag x.item))))
                  (vl-cw " ~x0>" x)))
               (vl-print " (")
               (vl-print-str (vl-lucid-mash-tag (symbol-name (tag x.item))))
               (vl-print ")"))))

(define vl-pp-lucidctx ((x vl-lucidctx-p) &key (ps 'ps))
  (b* (((vl-lucidctx x)))
    (vl-ps-seq (vl-print "In ")
               (vl-print-modname x.modname)
               (vl-println? ", ")
               (vl-pp-ctxelement-summary x.elem)
               (vl-print " under scope: ")
               (vl-pp-scopestack-path x.ss))))

(define vl-pp-lucidocc ((x vl-lucidocc-p) &key (ps 'ps))
  (vl-lucidocc-case x
    (:solo   (vl-ps-seq (vl-print "(:solo :ctx ")
                        (vl-pp-lucidctx x.ctx)
                        (vl-print ")")))
    (:slice  (vl-ps-seq (vl-cw "(:slice ~a0 ~a1 :ctx " x.left x.right)
                        (vl-pp-lucidctx x.ctx)
                        (vl-print ")")))
    (:tail  (vl-ps-seq (vl-print "(:tail :ctx ")
                       (vl-pp-lucidctx x.ctx)
                       (vl-print ")")))


    ;(:member (vl-cw "(:field ~s0)"     x.field))
    ))

(define vl-pp-lucidocclist ((x vl-lucidocclist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-lucidocc (car x))
               (vl-print " ")
               (vl-pp-lucidocclist (cdr x)))))

(define vl-pp-lucidval ((x vl-lucidval-p) &key (ps 'ps))
  (b* (((vl-lucidval x)))
    (vl-ps-seq (vl-print "Used: ")
               (if x.used
                   (vl-pp-lucidocclist (mergesort x.used))
                 (vl-print "never"))
               (vl-print "; Set: ")
               (if x.set
                   (vl-pp-lucidocclist (mergesort x.set))
                 (vl-print "never"))
               (if x.errors
                   (vl-cw "; Errors: ~x0~%" x.errors)
                 ps))))

(define vl-pp-luciddb-aux ((x vl-luciddb-p) &key (ps 'ps))
  :measure (vl-luciddb-count x)
  (b* ((x (vl-luciddb-fix x))
       ((when (atom x))
        ps)
       ((cons key val) (car x)))
    (vl-ps-seq (vl-print "  ")
               (vl-pp-lucidkey key)
               (vl-print ": ")
               (vl-indent 40)
               (vl-pp-lucidval val)
               (vl-println "")
               (vl-pp-luciddb-aux (cdr x)))))

(define vl-pp-luciddb ((x vl-luciddb-p) &key (ps 'ps))
  (b* ((x    (vl-luciddb-fix x))
       (copy (fast-alist-fork x nil))
       (-    (fast-alist-free copy)))
    (vl-pp-luciddb-aux copy)))

(define vl-pp-lucidstate ((x vl-lucidstate-p) &key (ps 'ps))
  (b* (((vl-lucidstate x)))
    (vl-ps-seq (vl-println "lucidstate {")
               (vl-pp-luciddb x.db)
               (vl-println "}"))))

(define vl-pps-lucidstate ((x vl-lucidstate-p))
  :parents (lucid)
  :short "Pretty-printer for debugging the lucid state."
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-lucidstate x)))


; State Mutators --------------------------------------------------------------

(local (xdoc::set-default-parents lucid))

(define vl-luciddb-mark ((mtype (member mtype '(:used :set)))
                         (key   vl-lucidkey-p)
                         (occ   vl-lucidocc-p)
                         (db    vl-luciddb-p)
                         (ctx   vl-lucidctx-p))
  :parents (vl-lucidstate-mark)
  :returns (new-db vl-luciddb-p)
  (b* ((db   (vl-luciddb-fix db))
       (occ  (vl-lucidocc-fix occ))
       (key  (vl-lucidkey-fix key))
       (ctx  (vl-lucidctx-fix ctx))

       (val (cdr (hons-get key db)))
       ((unless val)
        ;; BOZO we probably don't expect this to happen, but we'll go ahead and
        ;; mark it as an error.
        (let ((err (list __function__ ctx)))
          (hons-acons key
                      (change-vl-lucidval *vl-empty-lucidval*
                                          :used (list occ)
                                          :errors (list err))
                      db)))

       ((vl-lucidval val))
       (val (if (eq mtype :used)
                (change-vl-lucidval val :used (cons occ val.used))
              (change-vl-lucidval val :set (cons occ val.set))))
       (db  (hons-acons key val db)))
    db))

(define vl-lucidstate-mark ((mtype (member mtype '(:used :set)))
                            (key   vl-lucidkey-p)
                            (occ   vl-lucidocc-p)
                            (st    vl-lucidstate-p)
                            (ctx   vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-lucidstate st))
       (db (vl-luciddb-mark mtype key occ st.db ctx)))
    (change-vl-lucidstate st :db db)))

(define vl-lucid-mark-simple ((mtype (member mtype '(:used :set)))
                              (name  stringp)
                              (ss    vl-scopestack-p)
                              (st    vl-lucidstate-p)
                              (ctx   vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* ((st (vl-lucidstate-fix st))
       ((mv item item-ss)
        (vl-scopestack-find-item/ss name ss))
       ((unless item)
        ;; BOZO eventually turn into a proper bad-id warning
        (cw "Warning: missing item ~s0 in ~x1.~%" name
            (vl-scopestack->path ss))
        st)
       (key (make-vl-lucidkey :item item :scopestack item-ss))
       (occ (make-vl-lucidocc-solo :ctx ctx)))
    (vl-lucidstate-mark mtype key occ st ctx)))

;; (define vl-lucid-mark-slice-used ((name  stringp)
;;                                   (left  vl-expr-p)
;;                                   (right vl-expr-p)
;;                                   (ss    vl-scopestack-p)
;;                                   (st    vl-lucidstate-p)
;;                                   (ctx   acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-slice :left (vl-expr-strip left)
;;                                     :right (vl-expr-strip right))))
;;     (vl-lucidstate-mark-used key occ st ctx)))

;; (define vl-lucid-mark-solo-set ((name stringp)
;;                                 (ss   vl-scopestack-p)
;;                                 (st   vl-lucidstate-p)
;;                                 (ctx  acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-solo)))
;;     (vl-lucidstate-mark-set key occ st ctx)))

;; (define vl-lucid-mark-slice-set ((name  stringp)
;;                                   (left  vl-expr-p)
;;                                   (right vl-expr-p)
;;                                   (ss    vl-scopestack-p)
;;                                   (st    vl-lucidstate-p)
;;                                   (ctx   acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-slice :left (vl-expr-strip left)
;;                                     :right (vl-expr-strip right))))
;;     (vl-lucidstate-mark-set key occ st ctx)))

; Marking Phase ---------------------------------------------------------------

; We're going to look up IDs with vl-follow-hidexpr.
; That will give us a trace.

(define vl-normalize-scopestack ((x vl-scopestack-p))
  :returns (new-x vl-scopestack-p)
  :measure (vl-scopestack-count x)
  :verify-guards nil
  (b* ((x (vl-scopestack-fix x)))
    (vl-scopestack-case x
      :null x
      :global x
      :local
      (vl-scopestack-push (case (tag x.top)
                            (:vl-module (vl-module->genblob x.top))
                            (:vl-interface (vl-interface->genblob x.top))
                            (otherwise x.top))
                          (vl-normalize-scopestack x.super))))
  ///
  (verify-guards vl-normalize-scopestack))

(define vl-lucidst-mark-modport ((ifname stringp)
                                 (mpname stringp)
                                 (ss     vl-scopestack-p)
                                 (st     vl-lucidstate-p)
                                 (ctx    vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  :short "Helper function for marking interface modports as used."
  (b* ((st (vl-lucidstate-fix st))
       (design (vl-scopestack->design ss))
       ((unless design)
        (raise "No design in lucid scopestack?  Something is horribly wrong.")
        st)
       (iface (vl-find-interface ifname (vl-design->interfaces design)))
       ((unless iface)
        (b* ((w (make-vl-warning :type :vl-lucid-error
                                 :msg "While marking modport in ~s0, interface port ~s1 not found."
                                 :args (list (with-local-ps (vl-pp-lucidctx ctx))
                                             (string-fix ifname)))))
          (change-vl-lucidstate st
                                :warnings (cons w (vl-lucidstate->warnings st)))))
       ;; This is a little tricky because we need a normalized scopestack that
       ;; puts us into the right interface, but that's easy enough...
       (temp-ss (vl-scopestack-init design))
       (temp-ss (vl-scopestack-push iface temp-ss))
       (temp-ss (vl-normalize-scopestack temp-ss)))
    (vl-lucid-mark-simple :used mpname temp-ss st ctx)))

(define vl-hidstep-mark-interfaces ((mtype (member mtype '(:used :set)))
                                    (step  vl-hidstep-p)
                                    (st    vl-lucidstate-p)
                                    (ctx   vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-hidstep step))
       ((when (eq (tag step.item) :vl-interfaceport))
        (b* ((key (make-vl-lucidkey
                   :item step.item
                   :scopestack (vl-normalize-scopestack step.ss)))
             (occ (make-vl-lucidocc-solo :ctx ctx)))
          (vl-lucidstate-mark mtype key occ st ctx))))
    (vl-lucidstate-fix st)))

(define vl-hidtrace-mark-interfaces ((mtype  (member mtype '(:used :set)))
                                     (trace  vl-hidtrace-p)
                                     (st     vl-lucidstate-p)
                                     (ctx    vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((when (atom trace))
        (vl-lucidstate-fix st))
       (st (vl-hidstep-mark-interfaces mtype (car trace) st ctx)))
    (vl-hidtrace-mark-interfaces mtype (cdr trace) st ctx)))

(define vl-hidsolo-mark ((mtype        (member mtype '(:used :set)))
                         (force-bogusp booleanp)
                         (x            vl-scopeexpr-p)
                         (ss           vl-scopestack-p)
                         (st           vl-lucidstate-p)
                         (ctx          vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace ?scopectx tail) (vl-follow-scopeexpr x ss))
       ((when err)
        (b* (((vl-lucidstate st)))
          (change-vl-lucidstate st :warnings st.warnings)))
       ;; BOZO consider doing more with tail.  For instance:
       ;;   - Should we record the tail into the OCC that we create?  Could we
       ;;     analyze it in any meaningful way?
       ;;   - Should our state somehow record/track the fields of structs?
       ((cons (vl-hidstep step) rest) trace)
       (key (make-vl-lucidkey
             :item step.item
             :scopestack (vl-normalize-scopestack step.ss)))
       (occ (if (and (not force-bogusp)
                     (vl-hidexpr-case tail :end))
                (make-vl-lucidocc-solo :ctx ctx)
              (make-vl-lucidocc-tail :ctx ctx)))
       (st  (vl-hidtrace-mark-interfaces mtype rest st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

(define vl-hidslice-mark ((mtype  (member mtype '(:used :set)))
                          (hid    vl-scopeexpr-p)
                          (left   vl-expr-p)
                          (right  vl-expr-p)
                          (ss     vl-scopestack-p)
                          (st     vl-lucidstate-p)
                          (ctx    vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace ?scopectx tail) (vl-follow-scopeexpr hid ss))
       ((when err)
        (b* (((vl-lucidstate st)))
          (change-vl-lucidstate st :warnings st.warnings)))
       ((cons (vl-hidstep step) rest) trace)
       (key (make-vl-lucidkey
             :item step.item
             :scopestack (vl-normalize-scopestack step.ss)))
       (occ (if (vl-hidexpr-case tail :end)
                (make-vl-lucidocc-slice :left left
                                        :right right
                                        :ctx ctx)
              ;; Too complicated to handle really.
              (make-vl-lucidocc-tail :ctx ctx)))
       (st  (vl-hidtrace-mark-interfaces mtype rest st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

;; (define vl-rhsatom-lucidcheck ((x   vl-expr-p)
;;                                (ss  vl-scopestack-p)
;;                                (st  vl-lucidstate-p)
;;                                (ctx vl-lucidctx-p))
;;   :guard-hints(("Goal"
;;                 :in-theory (disable tag-when-vl-atomguts-p-forward)
;;                 :use ((:instance tag-when-vl-atomguts-p-forward
;;                        (x (vl-atom->guts (vl-expr-fix x)))))))
;;   :guard (vl-atom-p x)
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((x    (vl-expr-fix x))
;;        (guts (vl-atom->guts x))
;;        (st   (vl-lucidstate-fix st)))
;;     (case (tag guts)
;;       (:vl-funname  (vl-lucid-mark-simple :used (vl-funname->name guts) ss st ctx))
;;       (:vl-typename (vl-lucid-mark-simple :used (vl-typename->name guts) ss st ctx))
;;       (:vl-tagname
;;        ;; BOZO eventually think about how to handle tags.
;;        st)
;;       ((:vl-id :vl-hidpiece)
;;        (progn$ (raise "Should never get here because we should check for hidexpr-p first.")
;;                st))
;;       ((:vl-constint :vl-weirdint :vl-extint :vl-string
;;         :vl-real :vl-keyguts :vl-time :vl-basictype
;;         :vl-sysfunname)
;;        ;; Nothing at all to do for any of these
;;        st)
;;       (otherwise
;;        (progn$ (impossible)
;;                st)))))


(fty::deflist vl-scopeexprlist
  :elt-type vl-scopeexpr
  :parents (vl-scopeexpr))

(defines vl-collect-usertypes
  (define vl-collect-usertypes ((x vl-datatype-p))
    :returns (usertypes vl-scopeexprlist-p)
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      :vl-coretype nil
      :vl-struct (vl-structmemberlist-collect-usertypes x.members)
      :vl-union  (vl-structmemberlist-collect-usertypes x.members)
      :vl-enum   (vl-collect-usertypes x.basetype)
      :vl-usertype (list x.name)))
  (define vl-structmemberlist-collect-usertypes ((x vl-structmemberlist-p))
    :returns (usertypes vl-scopeexprlist-p)
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        nil
      (append (vl-collect-usertypes (vl-structmember->type (car x)))
              (vl-structmemberlist-collect-usertypes (cdr x)))))
  ///
  (deffixequiv-mutual vl-collect-usertypes))

(define vl-scopeexprlist-mark-solo ((mtype (member mtype '(:used :set)))
                                    (x     vl-scopeexprlist-p)
                                    (ss    vl-scopestack-p)
                                    (st    vl-lucidstate-p)
                                    (ctx   vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((when (atom x))
        (vl-lucidstate-fix st))
       (st (vl-hidsolo-mark mtype nil (car x) ss st ctx)))
    (vl-scopeexprlist-mark-solo mtype (cdr x) ss st ctx)))

(defines vl-rhsexpr-lucidcheck

  (define vl-rhsexpr-lucidcheck ((x   vl-expr-p)
                                 (ss  vl-scopestack-p)
                                 (st  vl-lucidstate-p)
                                 (ctx vl-lucidctx-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (b* ((st (vl-rhsexprlist-lucidcheck (vl-expr->subexprs x) ss st ctx)))
      (vl-expr-case x
        :vl-index (b* ((no-indices (atom x.indices))
                       (one-index  (tuplep 1 x.indices))
                       (no-partselect (vl-partselect-case x.part :none))
                       ((when (and no-indices no-partselect))
                        (vl-hidsolo-mark :used nil x.scope ss st ctx))
                       ((when (and one-index no-partselect))
                        (vl-hidslice-mark :used x.scope (first x.indices)
                                          (first x.indices) ss st ctx))
                       ((when (and no-indices
                                   (vl-partselect-case x.part :range)))
                        (b* (((vl-range x.part) (vl-partselect->range x.part))) ;; ugh
                          (vl-hidslice-mark :used x.scope
                                            x.part.msb x.part.lsb ss st ctx)))
                       ((when (and no-indices
                                   (vl-partselect-case x.part :plusminus)))
                        (b* (((vl-plusminus x.part) (vl-partselect->plusminus x.part)) ;; ugh
                             (st (vl-hidsolo-mark :used t x.scope ss st ctx)) ;; "forced bogus"
                             (st (vl-rhsexpr-lucidcheck x.part.base ss st ctx))
                             (st (vl-rhsexpr-lucidcheck x.part.width ss st ctx)))
                          st)))
                    ;; BOZO something fancy like
                    ;;    foo[3][4]
                    ;;    foo[3][4:0]
                    ;; Eventually do something more useful with this.  For now,
                    ;; we will just mark all of FOO as used.
                    (vl-hidsolo-mark :used t x.scope ss st ctx) ;; "forced bogus"
                    )

        :vl-call (b* ((st (vl-hidsolo-mark :used nil x.name ss st ctx))
                      (st (if x.typearg
                              (vl-scopeexprlist-mark-solo
                               :used (vl-collect-usertypes x.typearg)
                               ss st ctx)
                            st)))
                   st)
        :vl-cast (vl-casttype-case x.to
                   :type (vl-scopeexprlist-mark-solo
                          :used (vl-collect-usertypes x.to.type)
                          ss st ctx)
                   :otherwise st)
        :vl-pattern (if x.pattype
                        (vl-scopeexprlist-mark-solo
                          :used (vl-collect-usertypes x.pattype)
                          ss st ctx)
                      st)
        :vl-stream (vl-slicesize-case x.size
                     :type (vl-scopeexprlist-mark-solo
                            :used (vl-collect-usertypes x.size.type)
                            ss st ctx)
                     :otherwise st)

        :otherwise st)))

  (define vl-rhsexprlist-lucidcheck ((x   vl-exprlist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx vl-lucidctx-p))
    :measure (vl-exprlist-count x)
    :returns (new-st vl-lucidstate-p)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-rhsexpr-lucidcheck (car x) ss st ctx)))
      (vl-rhsexprlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-rhsexpr-lucidcheck$notinline)
  (deffixequiv-mutual vl-rhsexpr-lucidcheck))

(define vl-maybe-rhsexpr-lucidcheck ((x   vl-maybe-expr-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (if x
      (vl-rhsexpr-lucidcheck x ss st ctx)
    (vl-lucidstate-fix st)))

(define vl-maybe-rhsexprlist-lucidcheck ((x   vl-maybe-exprlist-p)
                                         (ss  vl-scopestack-p)
                                         (st  vl-lucidstate-p)
                                         (ctx vl-lucidctx-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((when (atom x))
        (vl-lucidstate-fix st))
       (st (vl-maybe-rhsexpr-lucidcheck (car x) ss st ctx)))
    (vl-maybe-rhsexprlist-lucidcheck (cdr x) ss st ctx)))

(defines vl-lhsexpr-lucidcheck

  (define vl-lhsexpr-lucidcheck ((x   vl-expr-p)
                                 (ss  vl-scopestack-p)
                                 (st  vl-lucidstate-p)
                                 (ctx vl-lucidctx-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (vl-expr-case x
      :vl-index (b* ((st
                      ;; We'll mark it as being SET, but first: we also need to
                      ;; mark anything that is used in index expressions as
                      ;; USED.
                      (vl-rhsexprlist-lucidcheck (vl-expr->subexprs x) ss st ctx))
                     (no-indices (atom x.indices))
                     (one-index  (tuplep 1 x.indices))
                     (no-partselect (vl-partselect-case x.part :none))
                     ((when (and no-indices no-partselect))
                      (vl-hidsolo-mark :set nil x.scope ss st ctx))
                     ((when (and one-index no-partselect))
                      (vl-hidslice-mark :set x.scope (first x.indices)
                                        (first x.indices) ss st ctx))
                     ((when (and no-indices
                                 (vl-partselect-case x.part :range)))
                      (b* (((vl-range x.part) (vl-partselect->range x.part))) ;; ugh
                        (vl-hidslice-mark :set x.scope
                                          x.part.msb x.part.lsb ss st ctx)))
                     ((when (and no-indices
                                 (vl-partselect-case x.part :plusminus)))
                      (b* (((vl-plusminus x.part) (vl-partselect->plusminus x.part)) ;; ugh
                           (st (vl-hidsolo-mark :set t x.scope ss st ctx)) ;; "forced bogus"
                           (st (vl-rhsexpr-lucidcheck x.part.base ss st ctx))
                           (st (vl-rhsexpr-lucidcheck x.part.width ss st ctx)))
                        st)))
                  ;; BOZO something fancy like
                  ;;    foo[3][4]
                  ;;    foo[3][4:0]
                  ;; Eventually do something more useful with this.  For now,
                  ;; we will just mark all of FOO as used.
                  (vl-hidsolo-mark :set t x.scope ss st ctx) ;; "forced bogus"
                  )

      ;; :vl-call (b* ((st (vl-hidsolo-mark :used x.name ss st ctx))
      ;;               (st (if x.typearg
      ;;                       (vl-scopeexprlist-mark-solo
      ;;                        :used (vl-collect-usertypes x.typearg)
      ;;                        ss st ctx)
      ;;                     st)))
      ;;            st)
      ;; :vl-cast (vl-casttype-case x.to
      ;;            :type (vl-scopeexprlist-mark-solo
      ;;                   :used (vl-collect-usertypes x.to.type)
      ;;                   ss st ctx)
      ;;            :otherwise st)
      ;; :vl-pattern (if x.pattype
      ;;                 (vl-scopeexprlist-mark-solo
      ;;                  :used (vl-collect-usertypes x.pattype)
      ;;                  ss st ctx)
      ;;               st)
      ;; :vl-stream (vl-slicesize-case x.size
      ;;              :type (vl-scopeexprlist-mark-solo
      ;;                     :used (vl-collect-usertypes x.size.type)
      ;;                     ss st ctx)
      ;;              :otherwise st)

      :otherwise (vl-lhsexprlist-lucidcheck (vl-expr->subexprs x) ss st ctx)))

  (define vl-lhsexprlist-lucidcheck ((x   vl-exprlist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx vl-lucidctx-p))
    :measure (vl-exprlist-count x)
    :returns (new-st vl-lucidstate-p)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-lhsexpr-lucidcheck (car x) ss st ctx)))
      (vl-lhsexprlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-lhsexpr-lucidcheck$notinline)
  (deffixequiv-mutual vl-lhsexpr-lucidcheck))

(defmacro def-vl-lucidcheck (name &key body (guard 't) takes-ctx
                                  (extra-args))
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (fix      (mksym 'vl- name '-fix)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx vl-lucidctx-p)))
                  ,@extra-args)
       :returns (new-st vl-lucidstate-p)
       :guard ,guard
       (b* ((x  (,fix x))
            (ss (vl-scopestack-fix ss))
            (st (vl-lucidstate-fix st)))
         ,body))))

(defmacro def-vl-lucidcheck-list (name &key element takes-ctx extra-args)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (elem-fn  (mksym 'vl- element '-lucidcheck)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx vl-lucidctx-p)))
                  ,@extra-args)
       :returns (new-st vl-lucidstate-p)
       (b* (((when (atom x))
             (vl-lucidstate-fix st))
            (st (,elem-fn (car x) ss st ,@(and takes-ctx '(ctx))
                          ,@(strip-cars extra-args))))
         (,fn (cdr x) ss st ,@(and takes-ctx '(ctx))
              ,@(strip-cars extra-args))))))

(def-vl-lucidcheck range
  :takes-ctx t
  :body
  (b* (((vl-range x))
       (st (vl-rhsexpr-lucidcheck x.msb ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.lsb ss st ctx)))
    st))

(def-vl-lucidcheck-list rangelist :element range :takes-ctx t)

(def-vl-lucidcheck maybe-range
  :takes-ctx t
  :body
  (if x
      (vl-range-lucidcheck x ss st ctx)
    st))


(def-vl-lucidcheck rhs
  :takes-ctx t
  :body
  (vl-rhs-case x
    (:vl-rhsexpr
     (vl-rhsexpr-lucidcheck x.guts ss st ctx))
    (:vl-rhsnew
     (b* ((st (vl-maybe-rhsexpr-lucidcheck x.arrsize ss st ctx))
          (st (vl-rhsexprlist-lucidcheck x.args ss st ctx)))
       st))))

(def-vl-lucidcheck enumitem
  :takes-ctx t
  :body
  (b* (((vl-enumitem x))
       ;; BOZO what are the scoping rules for enum items?  We may need to mark
       ;; their names as set.  But probably for any of this to work we would
       ;; need scopestack to understand enum items, etc...
       (st (vl-maybe-range-lucidcheck x.range ss st ctx))
       (st (vl-maybe-rhsexpr-lucidcheck x.value ss st ctx)))
    st))

(def-vl-lucidcheck-list enumitemlist :element enumitem :takes-ctx t)

(defines vl-datatype-lucidcheck

  (define vl-datatype-lucidcheck ((x   vl-datatype-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-datatype-count x)
    :verify-guards nil
    (b* ((st (vl-lucidstate-fix st)))
      (vl-datatype-case x
        :vl-coretype
        (b* ((st (vl-dimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.udims ss st ctx)))
          st)

        :vl-struct
        (b* ((st (vl-dimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.udims ss st ctx)))
          (vl-structmemberlist-lucidcheck x.members ss st ctx))

        :vl-union
        (b* ((st (vl-dimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.udims ss st ctx)))
          (vl-structmemberlist-lucidcheck x.members ss st ctx))

        :vl-enum
        (b* ((st (vl-datatype-lucidcheck x.basetype ss st ctx))
             (st (vl-enumitemlist-lucidcheck x.items ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.udims ss st ctx)))
          st)

        :vl-usertype
        (b* ((st (vl-hidsolo-mark :used nil x.name ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-dimensionlist-lucidcheck x.udims ss st ctx)))
          st))))

  (define vl-structmember-lucidcheck ((x   vl-structmember-p)
                                      (ss  vl-scopestack-p)
                                      (st  vl-lucidstate-p)
                                      (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x))
         (st (vl-lucidstate-fix st))
         (st (vl-datatype-lucidcheck x.type ss st ctx))
         (st (vl-maybe-rhsexpr-lucidcheck x.rhs ss st ctx)))
      st))

  (define vl-structmemberlist-lucidcheck ((x   vl-structmemberlist-p)
                                          (ss  vl-scopestack-p)
                                          (st  vl-lucidstate-p)
                                          (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-structmember-lucidcheck (car x) ss st ctx)))
      (vl-structmemberlist-lucidcheck (cdr x) ss st ctx)))

  (define vl-dimension-lucidcheck ((x   vl-dimension-p)
                                   (ss  vl-scopestack-p)
                                   (st  vl-lucidstate-p)
                                   (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-dimension-count x)
    (b* ((st (vl-lucidstate-fix st)))
      (vl-dimension-case x
        :unsized  st
        :star     st
        :range    (vl-range-lucidcheck x.range ss st ctx)
        :queue    (vl-maybe-rhsexpr-lucidcheck x.maxsize ss st ctx)
        :datatype (vl-datatype-lucidcheck x.type ss st ctx))))

  (define vl-dimensionlist-lucidcheck ((x vl-dimensionlist-p)
                                       (ss  vl-scopestack-p)
                                       (st  vl-lucidstate-p)
                                       (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-dimensionlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-dimension-lucidcheck (car x) ss st ctx)))
      (vl-dimensionlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-datatype-lucidcheck)
  (deffixequiv-mutual vl-datatype-lucidcheck))

(def-vl-lucidcheck delaycontrol
  :takes-ctx t
  :body
  (b* (((vl-delaycontrol x)))
    (vl-rhsexpr-lucidcheck x.value ss st ctx)))

(def-vl-lucidcheck evatom
  :takes-ctx t
  :body
  (b* (((vl-evatom x)))
    (vl-rhsexpr-lucidcheck x.expr ss st ctx)))

(def-vl-lucidcheck-list evatomlist :element evatom :takes-ctx t)

(def-vl-lucidcheck eventcontrol
  :takes-ctx t
  :body
  (b* (((vl-eventcontrol x)))
    (vl-evatomlist-lucidcheck x.atoms ss st ctx)))

(def-vl-lucidcheck repeateventcontrol
  :takes-ctx t
  :body
  (b* (((vl-repeateventcontrol x))
       (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
       (st (vl-eventcontrol-lucidcheck x.ctrl ss st ctx)))
    st))

(def-vl-lucidcheck delayoreventcontrol
  :takes-ctx t
  :body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-lucidcheck x ss st ctx))
    (:vl-eventcontrol (vl-eventcontrol-lucidcheck x ss st ctx))
    (otherwise        (vl-repeateventcontrol-lucidcheck x ss st ctx))))

(def-vl-lucidcheck maybe-delayoreventcontrol
  :takes-ctx t
  :body
  (if x
      (vl-delayoreventcontrol-lucidcheck x ss st ctx)
    st))

(def-vl-lucidcheck gatedelay
  :takes-ctx t
  :body
  (b* (((vl-gatedelay x))
       (st (vl-rhsexpr-lucidcheck x.rise ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.fall ss st ctx))
       (st (vl-maybe-rhsexpr-lucidcheck x.rise ss st ctx)))
    st))

(def-vl-lucidcheck maybe-gatedelay
  :takes-ctx t
  :body
  (if x
      (vl-gatedelay-lucidcheck x ss st ctx)
    st))

(define vl-basic-lucidctx ((ss   vl-scopestack-p)
                           (elem vl-ctxelement-p))
  :returns (ctx vl-lucidctx-p)
  (make-vl-lucidctx :modname (vl-scopestack->path ss)
                    :ss ss
                    :elem elem))

(def-vl-lucidcheck paramdecl
  :body
  (b* (((vl-paramdecl x))
       (ctx (vl-basic-lucidctx ss x)))
    (vl-paramtype-case x.type
      (:vl-implicitvalueparam
       (b* (((unless x.type.default)
             ;; No initial value, nothing to do.
             st)
            ;; Initial value, so the parameter itself is set.
            ;; Furthermore, we also need to mark the variables that are
            ;; used in the initial value expression as being used.
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st ctx)))
         st))
      (:vl-explicitvalueparam
       (b* ((st (vl-datatype-lucidcheck x.type.type ss st ctx))
            ((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st ctx)))
         st))
      (:vl-typeparam
       (b* (((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-datatype-lucidcheck x.type.default ss st ctx)))
         st)))))

(def-vl-lucidcheck-list paramdecllist :element paramdecl)


(def-vl-lucidcheck vardecl
  :body
  (b* (((vl-vardecl x))
       (ctx (vl-basic-lucidctx ss x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
       (st (vl-datatype-lucidcheck x.type ss st ctx))
       (st (if x.initval
               ;; Initial value, so this variable is set and we also need to
               ;; mark all variables used in the rhs as being used.
               (b* ((st (vl-rhs-lucidcheck x.initval ss st ctx))
                    (st (vl-lucid-mark-simple :set x.name ss st ctx)))
                 st)
             st)))
    st))

(def-vl-lucidcheck-list vardecllist :element vardecl)


(defines vl-stmt-lucidcheck

  (define vl-stmt-lucidcheck ((x   vl-stmt-p)
                              (ss  vl-scopestack-p)
                              (st  vl-lucidstate-p)
                              (ctx vl-lucidctx-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x  (vl-stmt-fix x))
         (st (vl-lucidstate-fix st)))
      (vl-stmt-case x

        :vl-nullstmt
        st

        :vl-assignstmt
        (b* ((st (vl-lhsexpr-lucidcheck x.lvalue ss st ctx))
             (st (vl-rhs-lucidcheck x.rhs ss st ctx))
             (st (vl-maybe-delayoreventcontrol-lucidcheck x.ctrl ss st ctx)))
          st)

        :vl-assertstmt
        (vl-assertion-lucidcheck x.assertion ss st ctx)

        :vl-cassertstmt
        (vl-cassertion-lucidcheck x.cassertion ss st ctx)

        :vl-deassignstmt
        ;; It isn't really clear what to do here.  In some sense, the
        ;; expression being deassigned ought to sort of be an lvalue.  But it
        ;; doesn't really make sense to regard a deassignment as "setting" the
        ;; variable.  It also doesn't really make sense to regard it as "using"
        ;; the variable.  I think for now I'm just not going to do anything at
        ;; all with deassignment statements.
        st

        :vl-callstmt
        ;; Typically this should be naming an task.  We'll treat the is as a
        ;; right hand side so that it gets marked as "used".  Arguments to the
        ;; task will also be marked as used.  BOZO this maybe isn't quite right
        ;; -- if the task has outputs then maybe we need to be marking them as
        ;; set instead of used??
        (b* ((st (vl-hidsolo-mark :used nil x.id ss st ctx))
             (st (if x.typearg
                     (vl-datatype-lucidcheck x.typearg ss st ctx)
                   st))
             (st (vl-maybe-rhsexprlist-lucidcheck x.args ss st ctx)))
          st)

        :vl-disablestmt
        ;; This is a little bit like the deassignment case.  It isn't really
        ;; clear whether we should regard tasks that are being disabled as
        ;; used.  I think for now we'll just ignore them.
        st

        :vl-breakstmt
        ;; Nothing to do here, I'm pretty sure.
        st

        :vl-continuestmt
        ;; Nothing to do here, I'm pretty sure.
        st

        :vl-returnstmt
        (if x.val
            (vl-rhsexpr-lucidcheck x.val ss st ctx)
          st)

        :vl-eventtriggerstmt
        ;; I think this is similar to the enable case?
        (b* ((st (vl-rhsexpr-lucidcheck x.id ss st ctx)))
          st)

        :vl-casestmt
        (b* ((st (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st (vl-caselist-lucidcheck x.caselist ss st ctx))
             (st (vl-stmt-lucidcheck x.default ss st ctx)))
          st)

        :vl-ifstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.truebranch ss st ctx))
             (st (vl-stmt-lucidcheck x.falsebranch ss st ctx)))
          st)

        :vl-foreverstmt
        (b* ((st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-waitstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-whilestmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-dostmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-forstmt
        ;; NOTE -- this must be kept in sync with vl-stmt-luciddb-init!
        (b* ((ss (vl-scopestack-push (vl-forstmt->blockscope x) ss))
             (st (vl-vardecllist-lucidcheck x.initdecls ss st))
             (st (vl-stmtlist-lucidcheck x.initassigns ss st ctx))
             (st (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st (vl-stmtlist-lucidcheck x.stepforms ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-foreachstmt
        ;; NOTE -- this must be kept in sync with vl-stmt-luciddb-init!
        (b* ((ss (vl-scopestack-push (vl-foreachstmt->blockscope x) ss))
             (st (vl-vardecllist-lucidcheck x.vardecls ss st))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-repeatstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-timingstmt
        (b* ((st (vl-delayoreventcontrol-lucidcheck x.ctrl ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-blockstmt
        (b* ((ss
              ;; NOTE -- this must be kept in sync with vl-stmt-luciddb-init!
              (vl-scopestack-push (vl-blockstmt->blockscope x) ss))
             ;; (st (vl-importlist-lucidcheck x.imports ss st))
             (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
             (st (vl-vardecllist-lucidcheck x.vardecls ss st))
             (st (vl-stmtlist-lucidcheck x.stmts ss st ctx)))
          st))))

  (define vl-assertion-lucidcheck ((x   vl-assertion-p)
                                   (ss  vl-scopestack-p)
                                   (st  vl-lucidstate-p)
                                   (ctx vl-lucidctx-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-assertion-count x)
    ;; This actually seems pretty easy to support.
    (b* (((vl-assertion x))
         (st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
         (st (vl-stmt-lucidcheck x.success ss st ctx))
         (st (vl-stmt-lucidcheck x.failure ss st ctx)))
      st))

  (define vl-cassertion-lucidcheck ((x   vl-cassertion-p)
                                    (ss  vl-scopestack-p)
                                    (st  vl-lucidstate-p)
                                    (ctx vl-lucidctx-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-cassertion-count x)
    ;; BOZO we should go through the condition and try to mark wires in the
    ;; sequence as used, etc.  But we'd basically need to collect up the
    ;; expressions to do that, and at the moment there are other things to do.
    (b* (((vl-cassertion x))
         (st (vl-stmt-lucidcheck x.success ss st ctx))
         (st (vl-stmt-lucidcheck x.failure ss st ctx)))
      st))

  (define vl-stmtlist-lucidcheck ((x   vl-stmtlist-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx vl-lucidctx-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-stmt-lucidcheck (car x) ss st ctx)))
      (vl-stmtlist-lucidcheck (cdr x) ss st ctx)))

  (define vl-caselist-lucidcheck ((x  vl-caselist-p)
                                  (ss vl-scopestack-p)
                                  (st vl-lucidstate-p)
                                  (ctx vl-lucidctx-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (vl-lucidstate-fix st))
         ((cons exprs stmt) (car x))
         ;; Treat the match expressions like right-hand sides because they are
         ;; being read but not assigned to.
         (st (vl-rhsexprlist-lucidcheck exprs ss st ctx))
         (st (vl-stmt-lucidcheck stmt ss st ctx)))
      (vl-caselist-lucidcheck (cdr x) ss st ctx)))
  ///
  (verify-guards vl-stmt-lucidcheck)
  (deffixequiv-mutual vl-stmt-lucidcheck))

(def-vl-lucidcheck always
  :body
  (b* (((vl-always x))
       (ctx (vl-basic-lucidctx ss x)))
    (vl-stmt-lucidcheck x.stmt ss st ctx)))

(def-vl-lucidcheck-list alwayslist :element always)

(def-vl-lucidcheck initial
  :body
  (b* (((vl-initial x))
       (ctx (vl-basic-lucidctx ss x)))
    (vl-stmt-lucidcheck x.stmt ss st ctx)))

(def-vl-lucidcheck-list initiallist :element initial)

(def-vl-lucidcheck final
  :body
  (b* (((vl-final x))
       (ctx (vl-basic-lucidctx ss x)))
    (vl-stmt-lucidcheck x.stmt ss st ctx)))

(def-vl-lucidcheck-list finallist :element final)

(encapsulate nil
  (local (in-theory (enable (tau-system))))
  (def-vl-lucidcheck portdecl
    :body
    (b* (((vl-portdecl x))
         (ctx (vl-basic-lucidctx ss x))
         (st  (vl-datatype-lucidcheck x.type ss st ctx)))
      (case x.dir
        (:vl-input
         ;; We "pretend" that input ports are set because they ought to be set by
         ;; the superior module, function call, or task invocation.
         (vl-lucid-mark-simple :set x.name ss st ctx))
        (:vl-output
         ;; We "pretend" that output ports are used because they ought to be used
         ;; the superior module, function call, or task invocation.
         (vl-lucid-mark-simple :used x.name ss st ctx))
        (:vl-inout
         ;; We don't pretend that inout ports are used or set, because they ought
         ;; to be both used and set within the submodule at some point in time.
         ;; (Otherwise they may as well be just an input or just an output.)
         st)))))

(def-vl-lucidcheck-list portdecllist :element portdecl)



(def-vl-lucidcheck interfaceport
  ;; Unlike regular ports, I think we want to not mark an interface port as
  ;; being used or set.  The smarts for an interface port will mostly be in our
  ;; reporting code.  If the thing is never used or set anywhere at all, we'll
  ;; not report it as an error.  But it's perfectly OK for a module to only
  ;; read from an interface, or to only write to it.
  :body
  (b* (((vl-interfaceport x))
       (ctx (vl-basic-lucidctx ss x))
       (st  (vl-dimensionlist-lucidcheck x.udims ss st ctx))
       ((unless x.modport)
        st))
    (vl-lucidst-mark-modport x.ifname x.modport ss st ctx)))

(def-vl-lucidcheck-list interfaceportlist :element interfaceport)


(defines vl-stmt-has-nonempty-return

  (define vl-stmt-has-nonempty-return ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    (if (vl-atomicstmt-p x)
        (vl-stmt-case x
          :vl-returnstmt (if x.val t nil)
          :otherwise nil)
      (vl-stmtlist-has-some-nonempty-return (vl-compoundstmt->stmts x))))

  (define vl-stmtlist-has-some-nonempty-return ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (or (vl-stmt-has-nonempty-return (car x))
          (vl-stmtlist-has-some-nonempty-return (cdr x)))))

  ///
  (deffixequiv-mutual vl-stmt-has-nonempty-return))

(def-vl-lucidcheck fundecl
  ;; We mark input ports as SET and output ports as USED since otherwise we
  ;; could end up thinking that inputs aren't set, which would be silly.  We
  ;; also mark the return value as being USED, since it is "used" by whoever
  ;; calls the function.
  :body
  (b* (((vl-fundecl x))
       (ctx (vl-basic-lucidctx ss x))
       (st (vl-datatype-lucidcheck x.rettype ss st ctx))
       ;; Subtle.  Before pushing the function's scope, we mark it as "set".
       ;; This doesn't make a whole lot of sense: what does it mean for a
       ;; function to be set?  But if we regard it as meaning, "it has a
       ;; defined value", then the very act of defining the function is kind of
       ;; like setting it.
       (st    (vl-lucid-mark-simple :set x.name ss st ctx))
       (scope (vl-fundecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       ;; Now that we've pushed the function scope, mark the function's name
       ;; (i.e., the return value) as used, because we're imagining that it
       ;; is "used" by whoever calls the function.
       (st    (vl-lucid-mark-simple :used x.name ss st ctx))
       ;; Mark all inputs to the function as set, because we're imagining
       ;; that they're set by the caller.
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       ;; (st (vl-importlist-lucidcheck x.imports ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st))
       ;; Seems easier to handle this here than inside the statement
       ;; processing stuff.
       (st (if (vl-stmt-has-nonempty-return x.body)
               (vl-lucid-mark-simple :set x.name ss st ctx)
             st)))
    (vl-stmt-lucidcheck x.body ss st ctx)))

(def-vl-lucidcheck-list fundecllist :element fundecl)

(def-vl-lucidcheck dpiimport
  :body
  (b* (((vl-dpiimport x))
       (ctx (vl-basic-lucidctx ss x))
       ;; We mark the function as set to act like it's been defined by the
       ;; C program.
       (st (vl-lucid-mark-simple :set x.name ss st ctx))
       (st (if x.rettype
               (vl-datatype-lucidcheck x.rettype ss st ctx)
             st))
       ;; BOZO -- we don't look at the ports.  This might require inventing a
       ;; pretend scope or something horrible.
       )
    st))

(def-vl-lucidcheck-list dpiimportlist :element dpiimport)

(def-vl-lucidcheck dpiexport
  :body
  (b* (((vl-dpiexport x))
       (ctx (vl-basic-lucidctx ss x))
       ;; We mark he function as used since it might be used by the C program.
       (st (vl-lucid-mark-simple :used x.name ss st ctx)))
    st))

(def-vl-lucidcheck-list dpiexportlist :element dpiexport)

(def-vl-lucidcheck taskdecl
  :body
  (b* (((vl-taskdecl x))
       (ctx (vl-basic-lucidctx ss x))
       ;; Subtle.  Mark the task itself as set.  See comments in fundecl
       ;; handling for an explanation.
       (st    (vl-lucid-mark-simple :set x.name ss st ctx))
       (scope (vl-taskdecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       ;; (st (vl-importlist-lucidcheck x.imports ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st)))
    (vl-stmt-lucidcheck x.body ss st ctx)))

(def-vl-lucidcheck-list taskdecllist :element taskdecl)

(def-vl-lucidcheck assign
  :body
  (b* (((vl-assign x))
       (ctx (vl-basic-lucidctx ss x))
       (st (vl-lhsexpr-lucidcheck x.lvalue ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx)))
    st))

(def-vl-lucidcheck-list assignlist :element assign)

(def-vl-lucidcheck typedef
  :body
  (b* (((vl-typedef x))
       (ctx (vl-basic-lucidctx ss x))
       (st (vl-lucid-mark-simple :set x.name ss st ctx))
       (st (vl-datatype-lucidcheck x.type ss st ctx)))
    st))

(def-vl-lucidcheck-list typedeflist :element typedef)


(define vl-string-expr->value ((x vl-expr-p))
  :returns (str maybe-stringp :rule-classes :type-prescription)
  (vl-expr-case x
    :vl-literal
    (vl-value-case x.val
      :vl-string x.val.value
      :otherwise nil)
    :otherwise nil))

(local (defthm alistp-when-vl-atts-p-rewrite
         (implies (vl-atts-p x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable (tau-system))))))

(def-vl-lucidcheck plainarg
  :takes-ctx t
  :body
  (b* (((vl-plainarg x))
       (ctx (change-vl-lucidctx ctx :portname x.portname))
       ((unless x.expr)
        st)
       ;; See argresolve's vl-unhierarchicalize-interfaceport stuff, which
       ;; converts fancy interfaceport arguments like myinterface.mymodport
       ;; into just myinterface.  In this case, we want to mark the modport as
       ;; being used.  Argresolve leaves us some attributes that we can use to
       ;; carry out this marking.  (BOZO: this might not work quite right after
       ;; unparameterizing interfaces, because the interface name may be
       ;; different.)
       (mpname (let ((look (cdr (assoc-equal "VL_REMOVED_EXPLICIT_MODPORT" x.atts))))
                 (and look (vl-string-expr->value look))))
       (ifname (and mpname
                    (let ((look (cdr (assoc-equal "VL_INTERFACE_NAME" x.atts))))
                      (and look (vl-string-expr->value look)))))
       (st (if ifname
               (vl-lucidst-mark-modport ifname mpname ss st ctx)
             st)))
    (case x.dir
      (:vl-input
       ;; Inputs are like RHSes, they're used not set.
       (vl-rhsexpr-lucidcheck x.expr ss st ctx))
      (:vl-output
       ;; Outputs are like LHSes, they're set not used.
       (vl-lhsexpr-lucidcheck x.expr ss st ctx))
      (otherwise
       ;; INOUT or interface port or error computing direction: treat it as if
       ;; it were both used and set.  BOZO maybe we should cause an error if
       ;; not determined?
       (b* ((st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
            (st (vl-lhsexpr-lucidcheck x.expr ss st ctx)))
         st)))))

(def-vl-lucidcheck-list plainarglist :element plainarg :takes-ctx t)

(def-vl-lucidcheck gateinst
  :body
  (b* (((vl-gateinst x))
       (ctx (vl-basic-lucidctx ss x))
       (st (vl-maybe-range-lucidcheck x.range ss st ctx))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
       (st (vl-plainarglist-lucidcheck x.args ss st ctx)))
    st))

(def-vl-lucidcheck-list gateinstlist :element gateinst)


; Parameter value lists like #(width = 1).  These are all like right-hand side uses.

(def-vl-lucidcheck paramvalue
  :takes-ctx t
  :body (vl-paramvalue-case x
          :expr (vl-rhsexpr-lucidcheck x.expr ss st ctx)
          :type (vl-datatype-lucidcheck x.type ss st ctx)))

(def-vl-lucidcheck-list paramvaluelist :element paramvalue :takes-ctx t)

(def-vl-lucidcheck maybe-paramvalue
  :takes-ctx t
  :body (if x
            (vl-paramvalue-lucidcheck x ss st ctx)
          st))

(def-vl-lucidcheck namedparamvalue
  :takes-ctx t
  :body (b* (((vl-namedparamvalue x)))
          (vl-maybe-paramvalue-lucidcheck x.value ss st ctx)))

(def-vl-lucidcheck-list namedparamvaluelist :element namedparamvalue :takes-ctx t)

(def-vl-lucidcheck paramargs
  :takes-ctx t
  :body
  (vl-paramargs-case x
    (:vl-paramargs-named
     (vl-namedparamvaluelist-lucidcheck x.args ss st ctx))
    (:vl-paramargs-plain
     (vl-paramvaluelist-lucidcheck x.args ss st ctx))))


(define vl-lucid-instmod-find-port-dir ((name stringp)
                                        (inst-ss vl-scopestack-p))
  :returns (dir vl-maybe-direction-p)
  (b* (((unless (vl-scopestack-case inst-ss :local)) nil)
       (scope (vl-scopestack-local->top inst-ss))
       (portdecl (vl-scope-find-portdecl-fast name scope))
       ((unless portdecl) nil))
    (vl-portdecl->dir portdecl)))

; Port lists.  These are tricky because they can be inputs or outputs or undetermined.

(def-vl-lucidcheck namedarg
  ;; HACK.  We treat named args as if they were inouts, which will possibly
  ;; under-report things but shouldn't cause spurious warnings.
  :takes-ctx t
  :extra-args ((inst-ss vl-scopestack-p "Scopestack of the instantiated module/interface."))
  :body
  (b* (((vl-namedarg x))
       (ctx (change-vl-lucidctx ctx :portname x.name))
       (dir (vl-lucid-instmod-find-port-dir x.name inst-ss))
       ((unless x.expr)
        st))
    (case dir
      (:vl-input
       (vl-rhsexpr-lucidcheck x.expr ss st ctx))
      (:vl-output
       (vl-lhsexpr-lucidcheck x.expr ss st ctx))
      (otherwise
       ;; INOUT or interface port or error computing direction: treat it as if
       ;; it were both used and set.  BOZO maybe we should cause an error if
       ;; not determined?
       (b* ((st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
            (st (vl-lhsexpr-lucidcheck x.expr ss st ctx)))
         st)))))

(def-vl-lucidcheck-list namedarglist :element namedarg :takes-ctx t
  :extra-args ((inst-ss vl-scopestack-p "Scopestack of the instantiated module/interface.")))

(def-vl-lucidcheck arguments
  :takes-ctx t
  :extra-args ((inst-ss vl-scopestack-p "Scopestack of the instantiated module/interface."))
  :body
  (vl-arguments-case x
    :vl-arguments-plain
    (vl-plainarglist-lucidcheck x.args ss st ctx)
    :vl-arguments-named
    (vl-namedarglist-lucidcheck x.args ss st ctx inst-ss)))

(encapsulate nil
  (local (DEFTHM VL-SCOPE-P-WHEN-VL-MODULE-P-strong
           (IMPLIES (VL-MODULE-P X) (VL-SCOPE-P X))))
  (local (DEFTHM VL-SCOPE-P-WHEN-VL-INTERFACE-P-strong
           (IMPLIES (VL-INTERFACE-P X) (VL-SCOPE-P X))))
  (def-vl-lucidcheck modinst
    :body
    (b* (((vl-modinst x))
         (ctx (vl-basic-lucidctx ss x))
         (st (vl-maybe-range-lucidcheck x.range ss st ctx))
         (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
         (st (vl-paramargs-lucidcheck x.paramargs ss st ctx))
         (mod (vl-scopestack-find-definition x.modname ss))
         (inst-ss (and mod
                       (member (tag mod) '(:vl-module :vl-interface))
                       (vl-scopestack-push mod (vl-scopestack->toplevel ss))))
         (st (vl-arguments-lucidcheck x.portargs ss st ctx inst-ss)))
      st)))

(def-vl-lucidcheck-list modinstlist :element modinst)

(def-vl-lucidcheck modport
  :body
  (let* ((x  (vl-modport-fix x))
         (ss (vl-scopestack-fix ss)))
    ;; Do we actually want to do anything with modports?  I think probably
    ;; not?  That is, if someone writes:
    ;;
    ;;     interface foo;
    ;;        logic [3:0] bar;
    ;;        modport producer (output bar);
    ;;     endinterface
    ;;
    ;; then we probably don't want to consider BAR as used or set or anything
    ;; like that.  It's only when some other module actually refers to BAR via
    ;; the interface that we should regard it as used/set.  Right?
    (declare (ignore x ss))
    st))

(def-vl-lucidcheck-list modportlist :element modport)

(def-vl-lucidcheck alias
  :body
  (let* ((x (vl-alias-fix x))
         (ss (vl-scopestack-fix ss)))
    (declare (ignore x ss))
    ;; BOZO supporting aliases will be difficult.  For now ignore them.
    st))

(def-vl-lucidcheck-list aliaslist :element alias)

(defines vl-genblob-lucidcheck
  :verify-guards nil

  (define vl-genblob-lucidcheck-aux ((x vl-genblob-p)
                                     (ss vl-scopestack-p)
                                     (st vl-lucidstate-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-count x) 0)
    ;; Assumes the scope for the genblob has already been pushed onto the
    ;; scopestack.  This is a stupid hack that helps with the genloop case.
    (b* (((vl-genblob x) (vl-genblob-fix x))
         (ss (vl-scopestack-fix ss))
         (st (vl-lucidstate-fix st))
         (st (vl-portdecllist-lucidcheck  x.portdecls  ss st))
         (st (vl-assignlist-lucidcheck    x.assigns    ss st))
         (st (vl-aliaslist-lucidcheck     x.aliases    ss st))
         (st (vl-vardecllist-lucidcheck   x.vardecls   ss st))
         (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
         (st (vl-fundecllist-lucidcheck   x.fundecls   ss st))
         (st (vl-taskdecllist-lucidcheck  x.taskdecls  ss st))
         (st (vl-modinstlist-lucidcheck   x.modinsts   ss st))
         (st (vl-gateinstlist-lucidcheck  x.gateinsts  ss st))
         (st (vl-alwayslist-lucidcheck    x.alwayses   ss st))
         (st (vl-initiallist-lucidcheck   x.initials   ss st))
         (st (vl-finallist-lucidcheck     x.finals     ss st))
         (st (vl-typedeflist-lucidcheck   x.typedefs   ss st))
         ;; Nothing to do for imports, they just affect the scopestack.
         ;; Nothing to do for fwdtypedefs
         (st (vl-modportlist-lucidcheck   x.modports   ss st))
         ;; Nothing to do for genvars, they just affect the scopestack
         ;; BOZO add assertions
         ;; BOZO add cassertions
         ;; BOZO add properties
         ;; BOZO add sequences
         (st (vl-dpiimportlist-lucidcheck x.dpiimports ss st))
         (st (vl-dpiexportlist-lucidcheck x.dpiexports ss st))
         (st (vl-genelementlist-lucidcheck x.generates  ss st))
         ;; BOZO anything to do for normal ports?
         (st (vl-interfaceportlist-lucidcheck x.ifports ss st)))
      st))

  (define vl-genblob-lucidcheck ((x  vl-genblob-p)
                                 (ss vl-scopestack-p)
                                 (st vl-lucidstate-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-count x) 1)
    ;; Pushes the scope and checks everything within it.
    (b* ((x  (vl-genblob-fix x))
         (ss (vl-scopestack-fix ss))
         (st (vl-lucidstate-fix st))
         (ss (vl-scopestack-push x ss))
         (st (vl-genblob-lucidcheck-aux x ss st)))
      st))

  (define vl-genelementlist-lucidcheck ((x  vl-genelementlist-p)
                                        (ss vl-scopestack-p)
                                        (st vl-lucidstate-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-generates-count x) 0)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-genelement-lucidcheck (car x) ss st)))
      (vl-genelementlist-lucidcheck (cdr x) ss st)))

  (define vl-genblock-lucidcheck ((x  vl-genblock-p)
                                  (ss vl-scopestack-p)
                                  (st vl-lucidstate-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-genblock-count x) 0)
    (b* (((vl-genblock x))
         (blob (vl-genblock->genblob x))
         ((when x.condnestp)
          ;; Special case where the block doesn't introduce a scope.  Don't
          ;; push a scope, just go process the elements.
          (vl-genblob-lucidcheck-aux blob ss st)))
      (vl-genblob-lucidcheck (vl-genblock->genblob x) ss st)))

  (define vl-genelement-lucidcheck ((x vl-genelement-p)
                                    (ss vl-scopestack-p)
                                    (st vl-lucidstate-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-generate-count x) 0)
    (b* ((x  (vl-genelement-fix x))
         (ss (vl-scopestack-fix ss))
         (st (vl-lucidstate-fix st)))
      (vl-genelement-case x
        :vl-genbase
        ;; We shouldn't encounter these because vl-genblock->genblob should
        ;; properly sort out all the genbases into the other fields.
        (progn$
         (raise "Programming error: should not encounter :vl-genbase, but
                 found ~s0.~%" (with-local-ps (vl-cw "~a0~%" x)))
         st)
        :vl-genbegin
        (vl-genblock-lucidcheck x.block ss st)
        :vl-genif
        ;; For IF generate constructs we should also consider the names used in
        ;; the TEST expression as being used.
        (b* ((ctx (vl-basic-lucidctx ss x))
             (st (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st (vl-genblock-lucidcheck x.then ss st)))
          (vl-genblock-lucidcheck x.else ss st))
        :vl-genarray
        ;; Note: elaboration adds a parameter declaration for the loop variable
        ;; into each block, so we don't need to fudge the scope.  However, we
        ;; still add a scope for a local genvar if applicable, to match
        ;; luciddb-init.
        (b* ((ctx (vl-basic-lucidctx ss x))
             (ss  (b* (((unless x.genvarp)
                        ss)
                       (scope (vl-lucid-genvar-scope x.var x.loc))
                       (ss    (vl-scopestack-push scope ss)))
                    ss))
             ;; Mark the genvar as used and set (important in case it's outside the loop body.)
             (st  (vl-lucid-mark-simple :used x.var ss st ctx))
             (st  (vl-lucid-mark-simple :set x.var ss st ctx)))
          (vl-genblocklist-lucidcheck x.var x.blocks ss st ctx))
        :vl-genloop
        ;; Subtle.  See SystemVerilog-2012 Section 27.4 and also see the
        ;; related case in vl-shadowcheck-genelement.  We'll create a new scope
        ;; with the parameter declaration in it.
        (b* ((ctx (vl-basic-lucidctx ss x))
             (ss  (b* (((unless x.genvarp)
                        ss)
                       (scope (vl-lucid-genvar-scope x.var x.loc))
                       (ss    (vl-scopestack-push scope ss)))
                    ss))
             ;; Mark the genvar as used and set (important in case it's outside the loop body.)
             (st  (vl-lucid-mark-simple :used x.var ss st ctx))
             (st  (vl-lucid-mark-simple :set x.var ss st ctx))
             (st  (vl-rhsexpr-lucidcheck x.initval ss st ctx))
             (st  (vl-rhsexpr-lucidcheck x.continue ss st ctx))
             (st  (vl-rhsexpr-lucidcheck x.nextval ss st ctx))
             (blob (vl-genblock->genblob x.body))
             (var-paramdecl (vl-lucid-paramdecl-for-genloop x.var x.loc))
             (extended-blob (change-vl-genblob blob
                                               :paramdecls (cons var-paramdecl (vl-genblob->paramdecls blob))))
             (ss (vl-scopestack-push extended-blob ss))
             ;; Mark the parameter as used and set inside the loop body.
             (st (vl-lucid-mark-simple :used x.var ss st ctx))
             (st (vl-lucid-mark-simple :set x.var ss st ctx)))
          (vl-genblob-lucidcheck-aux blob ss st))
        :vl-gencase
        (b* ((ctx (vl-basic-lucidctx ss x))
             (st  (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st  (vl-gencaselist-lucidcheck x.cases ss st ctx)))
          (vl-genblock-lucidcheck x.default ss st)))))

  (define vl-gencaselist-lucidcheck ((x   vl-gencaselist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-gencaselist-count x) 0)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x))
          (vl-lucidstate-fix st))
         ((cons exprs block) (car x))
         (st (vl-rhsexprlist-lucidcheck exprs ss st ctx))
         (st (vl-genblock-lucidcheck block ss st)))
      (vl-gencaselist-lucidcheck (cdr x) ss st ctx)))

  (define vl-genblocklist-lucidcheck ((var stringp)
                                      (x   vl-genblocklist-p)
                                      (ss  vl-scopestack-p)
                                      (st  vl-lucidstate-p)
                                      (ctx vl-lucidctx-p))
    :returns (st vl-lucidstate-p)
    :measure (two-nats-measure (vl-genblob-genblocklist-count x) 0)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (blob1 (vl-genblock->genblob (car x)))
         ;; Push the scopestack manually and use the aux function so that
         ;; we can regard the loop parameter as used and set.
         (st (b* ((ss (vl-scopestack-push blob1 ss))
                  (st (vl-genblob-lucidcheck-aux blob1 ss st))
                  (st (vl-lucid-mark-simple :used var ss st ctx))
                  (st (vl-lucid-mark-simple :set var ss st ctx)))
               st)))
      (vl-genblocklist-lucidcheck var (cdr x) ss st ctx)))
  ///
  (verify-guards vl-genblob-lucidcheck)
  (deffixequiv-mutual vl-genblob-lucidcheck))


(def-vl-lucidcheck module
  :body
  (b* ((genblob (vl-module->genblob x))
       (st (vl-genblob-lucidcheck genblob ss st)))
    st))

(def-vl-lucidcheck-list modulelist :element module)

(def-vl-lucidcheck interface
  :body
  (b* ((genblob (vl-interface->genblob x))
       (st (vl-genblob-lucidcheck genblob ss st)))
    st))

(def-vl-lucidcheck-list interfacelist :element interface)

(def-vl-lucidcheck package
  :body
  (b* (((vl-package x))
       (ss (vl-scopestack-push x ss))
       (st (vl-fundecllist-lucidcheck   x.fundecls   ss st))
       (st (vl-taskdecllist-lucidcheck  x.taskdecls  ss st))
       (st (vl-typedeflist-lucidcheck   x.typedefs   ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck   x.vardecls   ss st))
       (st (vl-dpiimportlist-lucidcheck x.dpiimports ss st))
       (st (vl-dpiexportlist-lucidcheck x.dpiexports ss st)))
    st))

(def-vl-lucidcheck-list packagelist :element package)


(define vl-design-lucidcheck-main ((x  vl-design-p)
                                   (ss vl-scopestack-p)
                                   (st vl-lucidstate-p))
  :returns (new-st vl-lucidstate-p)
  :ignore-ok t
  :irrelevant-formals-ok t
  (b* (((vl-design x))
       (st (vl-modulelist-lucidcheck x.mods ss st))
       ;; BOZO add udps
       (st (vl-interfacelist-lucidcheck x.interfaces ss st))
       ;; BOZO add programs
       (st (vl-packagelist-lucidcheck x.packages ss st))
       ;; BOZO add configs
       (st (vl-vardecllist-lucidcheck x.vardecls ss st))
       (st (vl-fundecllist-lucidcheck x.fundecls ss st))
       (st (vl-taskdecllist-lucidcheck x.taskdecls ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       ;; Nothing to do for imports, they just affect the scopestack
       (st (vl-dpiimportlist-lucidcheck x.dpiimports ss st))
       (st (vl-dpiexportlist-lucidcheck x.dpiexports ss st))
       ;; Nothing to do for fwdtypedefs
       (st (vl-typedeflist-lucidcheck x.typedefs ss st)))
    st))

; Analysis of Marks -----------------------------------------------------------

(define vl-scopestack-top-level-name ((ss vl-scopestack-p))
  :returns (name maybe-stringp :rule-classes :type-prescription)
  :measure (vl-scopestack-count ss)
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local
    (or (vl-scopestack-top-level-name ss.super)
        (let ((id (vl-scope->id ss.top)))
          (and (stringp id) id)))))

(define vl-lucid-some-solo-occp ((x vl-lucidocclist-p))
  :returns (solop booleanp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (or (eq (vl-lucidocc-kind (car x)) :solo)
        (vl-lucid-some-solo-occp (cdr x)))))

(define vl-lucid-first-solo-occ ((x vl-lucidocclist-p))
  :returns (occ? (and (iff (vl-lucidocc-p occ?) (vl-lucid-some-solo-occp x))
                      (iff occ?                 (vl-lucid-some-solo-occp x))))
  :prepwork ((local (in-theory (enable vl-lucid-some-solo-occp))))
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :solo)
         (vl-lucidocc-fix (car x)))
        (t
         (vl-lucid-first-solo-occ (cdr x)))))

(define vl-lucid-collect-solo-occs ((x vl-lucidocclist-p))
  :returns (solos vl-lucidocclist-p)
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :solo)
         (cons (vl-lucidocc-fix (car x))
               (vl-lucid-collect-solo-occs (cdr x))))
        (t
         (vl-lucid-collect-solo-occs (cdr x))))
  ///
  (local (in-theory (enable vl-lucid-some-solo-occp)))
  (more-returns
   (solos (iff solos (vl-lucid-some-solo-occp x))
          :name vl-lucid-collect-solo-occs-under-iff)
   (solos (equal (consp solos) (if solos t nil))
          :name consp-of-vl-lucid-collect-solo-occs)))





(define ints-from ((a integerp)
                   (b integerp))
  :guard (<= a b)
  :measure (nfix (- (ifix b) (ifix a)))
  :parents (utilities)
  :short "@(call ints-from) enumerates the integers from @('[a, b)')."

  (let ((a (lifix a))
        (b (lifix b)))
    (if (mbe :logic (zp (- b a))
             :exec (= a b))
        nil
      (cons a (ints-from (+ 1 a) b))))

  ///

  (defthm true-listp-of-ints-from
    (true-listp (ints-from a b))
    :rule-classes :type-prescription)

  (defthm integer-listp-of-ints-from
    (integer-listp (ints-from a b)))

  (defthm consp-of-ints-from
    (equal (consp (ints-from a b))
           (< (ifix a) (ifix b))))

  (defthm ints-from-self
    (equal (ints-from a a)
           nil))

  (defthm member-equal-ints-from
    (iff (member-equal x (ints-from a b))
         (and (integerp x)
              (<= (ifix a) x)
              (< x (ifix b)))))

  ;; (defthm all-at-least-of-ints-from
  ;;     (all-at-least (ints-from a b) a)
  ;;     :hints(("Goal"
  ;;             :use ((:functional-instance all-by-membership
  ;;                                         (all-hyp  (lambda ()  t))
  ;;                                         (all-list (lambda ()  (ints-from a b)))
  ;;                                         (all      (lambda (x) (all-at-least x a)))
  ;;                                         (pred     (lambda (x) (<= a x))))))))

  (defthm no-duplicatesp-equal-of-ints-from
    (no-duplicatesp-equal (ints-from a b)))


  ;; (defthm empty-intersection-with-ints-from-when-too-small
  ;;     (implies (and (all-less-than x max)
  ;;                   (<= max a))
  ;;              (not (intersectp-equal x (ints-from a b))))
  ;;     :hints(("Goal"
  ;;             :in-theory (disable empty-intersection-by-bounds)
  ;;             :use ((:instance empty-intersection-by-bounds
  ;;                              (x x)
  ;;                              (x-max max)
  ;;                              (y (ints-from a b))
  ;;                              (y-min a))))))

  ;; (defthm all-less-than-of-ints-from
  ;;   (all-less-than (ints-from a b) b))

  (local (include-book "std/basic/arith-equivs" :dir :system))

  (deffixequiv ints-from)

  (encapsulate
   ()
   (local (defun ind (k a b)
            (declare (xargs :measure (nfix (- (ifix b) (ifix a)))))
            (if (zp (- (ifix b) (ifix a)))
                (list k a b)
              (ind (+ -1 k) (+ 1 (ifix a)) b))))

   (defthm take-of-ints-from
     (equal (take k (ints-from a b))
            (if (< (ifix k) (nfix (- (ifix b) (ifix a))))
                (ints-from a (+ (ifix a) (ifix k)))
              (append (ints-from a b)
                      (replicate (- (ifix k) (nfix (- (ifix b) (ifix a)))) nil))))
     :hints(("Goal"
             :induct (ind k a b)
             :in-theory (enable acl2::take ints-from repeat))
            (and stable-under-simplificationp
                 '(:in-theory (enable nfix repeat))))))


  (encapsulate
   ()
   (local (defun ind (k a b)
            (declare (xargs :measure (nfix (- (ifix b) (ifix a)))))
            (if (zp (- (ifix b) (ifix a)))
                (list k a b)
              (ind (+ -1 k) (+ 1 (ifix a)) b))))

   (defthm nthcdr-of-ints-from
     (equal (nthcdr k (ints-from a b))
            (if (< (nfix k) (nfix (- (ifix b) (ifix a))))
                (ints-from (+ (ifix a) (nfix k)) b)
              nil))
     :hints(("Goal"
             :induct (ind k a b)
             :in-theory (enable ints-from))
            (and stable-under-simplificationp
                 '(:in-theory (enable nfix))))))

  (defthm len-of-ints-from
    (equal (len (ints-from a b))
           (nfix (- (ifix b) (ifix a))))
    :hints(("Goal" :in-theory (enable ints-from))))

  (defthm car-of-ints-from
    (equal (car (ints-from a b))
           (if (< (ifix a) (ifix b))
               (ifix a)
             nil))
    :hints(("Goal" :in-theory (enable ints-from))))

  (encapsulate
   ()
   (local (defun ind (n a b)
            (declare (xargs :measure (nfix (- (ifix b) (ifix a)))))
            (if (zp (- (ifix b) (ifix a)))
                (list n a b)
              (ind (+ -1 n) (+ 1 (ifix a)) b))))

   (defthm nth-of-ints-from
     (equal (nth n (ints-from a b))
            (if (< (nfix n) (nfix (- (ifix b) (ifix a))))
                (+ (ifix a) (nfix n))
              nil))
     :hints(("Goal"
             :induct (ind n a b)
             :do-not '(generalize fertilize)
             :in-theory (enable nth ints-from)))))

  (defthm setp-of-ints-from
    (setp (ints-from a b))
    :hints(("Goal" :in-theory (enable set::primitive-rules
                                      << lexorder alphorder)))))

;; Performance BOZO - we would probably be better off using something like
;; sparse bitsets here, but that would require developing something like
;; nats-from that produces a sparse bitset.  That's fine but might take an hour
;; or two of work.

(defconst *vl-lucid-too-many-bits* (expt 2 20))

(define vl-lucid-range->bits ((x vl-range-p)
                              (ctx any-p))
  :guard (vl-range-resolved-p x)
  :returns (bits (and (integer-listp bits)
                      (setp bits)))
  (b* (((vl-range x))
       (msb (vl-resolved->val x.msb))
       (lsb (vl-resolved->val x.lsb))
       (min (min msb lsb))
       (max (max msb lsb))
       ((unless (< max (+ min *vl-lucid-too-many-bits*)))
        (vl-cw-ps-seq
         (vl-cw "; ~a0: Whoops, range [~x1:~x2] has too many bits; fudging.~%" ctx msb lsb))
        nil))
    ;; We add one to max because nats-from enumerates [a, b)
    (ints-from min (+ 1 max))))

(deflist vl-lucid-all-slices-p (x)
  :guard (vl-lucidocclist-p x)
  (eq (vl-lucidocc-kind x) :slice))

(define vl-lucid-resolved-slice-p ((x vl-lucidocc-p))
  :guard (equal (vl-lucidocc-kind x) :slice)
  :returns (resolvedp booleanp :rule-classes :type-prescription)
  (b* (((vl-lucidocc-slice x)))
    (and (vl-expr-resolved-p x.left)
         (vl-expr-resolved-p x.right))))

(define vl-lucid-resolved-slice->bits ((x vl-lucidocc-p)
                                       (ctx any-p))
  :guard (and (equal (vl-lucidocc-kind x) :slice)
              (vl-lucid-resolved-slice-p x))
  :returns (indices (and (integer-listp indices)
                         (setp indices)))
  :prepwork ((local (in-theory (enable vl-lucid-resolved-slice-p))))
  (b* (((vl-lucidocc-slice x))
       (msb (vl-resolved->val x.left))
       (lsb (vl-resolved->val x.right))
       (min (min msb lsb))
       (max (max msb lsb))
       ((unless (< max (+ min *vl-lucid-too-many-bits*)))
        (vl-cw-ps-seq
         (vl-cw "; ~a0: Whoops, range [~x1:~x2] has too many bits; fudging.~%" ctx msb lsb))
        nil))
    ;; We add one to max because nats-from enumerates [a, b)
    (ints-from min (+ 1 max))))

(deflist vl-lucid-all-slices-resolved-p (x)
  :guard (and (vl-lucidocclist-p x)
              (vl-lucid-all-slices-p x))
  (vl-lucid-resolved-slice-p x))

(define vl-lucid-resolved-slices->bits ((x vl-lucidocclist-p)
                                        (ctx any-p))
  :guard (and (vl-lucid-all-slices-p x)
              (vl-lucid-all-slices-resolved-p x))
  :returns (indices (and (integer-listp indices)
                         (setp indices)))
  (if (atom x)
      nil
    (union (vl-lucid-resolved-slice->bits (car x) ctx)
           (vl-lucid-resolved-slices->bits (cdr x) ctx))))

(define vl-lucid-valid-bits-for-datatype ((x   vl-datatype-p)
                                          (ss  vl-scopestack-p)
                                          (ctx any-p))
  :returns (mv (simple-p booleanp :rule-classes :type-prescription)
               (bits     (and (integer-listp bits)
                              (setp bits))))
  (b* (((mv err x) (vl-datatype-usertype-resolve x ss
                                                 :rec-limit 1000
                                                 :scopes (vl-elabscopes-init-ss ss)))
       ((when err)
        ;; Some kind of error resolving the user-defined data types, let's
        ;; not try to analyze this at all.
        (mv nil nil)))
    (vl-datatype-case x
      (:vl-coretype
       (case x.name
         ((:vl-logic :vl-reg :vl-bit)
          ;; Integer vector types.  We'll support one packed dimension here,
          ;; i.e., we're looking for things like wire [3:0] w;
          (b* (((when (consp x.udims))
                (mv nil nil))
               ((when (atom x.pdims))
                ;; No packed or unpacked dimensions.  Single bit.
                (mv t '(0)))
               ((unless (and (atom (cdr x.pdims))
                             (b* ((dim (first x.pdims)))
                               (vl-dimension-case dim :range))
                             (vl-range-resolved-p
                              (vl-dimension->range (first x.pdims)))))
                ;; Too many or unresolved dimensions -- too hard.
                (mv nil nil)))
            (mv t (vl-lucid-range->bits (vl-dimension->range (first x.pdims))
                                        ctx))))

         ((:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer :vl-time)
          ;; Integer atom types.  If there aren't any dimensions then it still
          ;; makes sense to treat them as bits.
          (if (or (consp x.pdims)
                  (consp x.udims))
              (mv nil nil)
            (case x.name
              (:vl-byte     (mv t (nats-from 0 8)))
              (:vl-shortint (mv t (nats-from 0 16)))
              (:vl-int      (mv t (nats-from 0 32)))
              (:vl-longint  (mv t (nats-from 0 64)))
              (:vl-integer  (mv t (nats-from 0 32)))
              (:vl-time     (mv t (nats-from 0 64)))
              (otherwise    (mv (impossible) nil)))))

         (otherwise
          ;; Something trickier like a string, c handle, event, void, real, etc.
          ;; Too hard, don't consider it.
          (mv nil nil))))
      (:vl-struct
       ;; Probably don't want to deal with structs yet
       (mv nil nil))
      (:vl-union
       ;; BOZO eventually maybe try to do something with unions
       (mv nil nil))
      (:vl-enum
       ;; BOZO eventually maybe try to do something with enums
       (mv nil nil))
      (:vl-usertype
       ;; This shouldn't happen because usertype-elim should have gotten
       ;; rid of it.
       (mv nil nil)))))

(define vl-lucid-valid-bits-for-decl ((item (or (vl-paramdecl-p item)
                                                (vl-vardecl-p item)))
                                      (ss   vl-scopestack-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (mv (simple-p booleanp :rule-classes :type-prescription)
               (bits     (and (integer-listp bits)
                              (setp bits))))
  (b* ((datatype-for-indexing
        (b* (((when (eq (tag item) :vl-vardecl))
              (vl-vardecl->type item))
             (paramtype (vl-paramdecl->type item)))
          (vl-paramtype-case paramtype
            (:vl-implicitvalueparam
             ;; This is a really hard case.  I'm going to not try to support
             ;; it, under the theory that we're going to be doing lucid
             ;; checking after unparameterization, and at that point most
             ;; parameters should be used in simple ways.
             nil)
            (:vl-explicitvalueparam paramtype.type)
            (:vl-typeparam
             ;; Doesn't make any sense to try to index into a type.
             nil))))
       ((when datatype-for-indexing)
        (vl-lucid-valid-bits-for-datatype datatype-for-indexing ss item)))
    ;; Else, too hard to do any kind of indexing
    (mv nil nil)))

(define vl-pp-merged-index ((x vl-merged-index-p) &key (ps 'ps))
  :prepwork ((local (in-theory (enable vl-merged-index-p))))
  (cond ((consp x)
         (vl-ps-seq (vl-print "[")
                    (vl-print (cdr x))
                    (vl-print ":")
                    (vl-print (car x))
                    (vl-print "]")))
        (x
         (vl-print x))
        (t
         (vl-print "NIL"))))

(define vl-pp-merged-index-list ((x vl-merged-index-list-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-merged-index (car x))
               (if (consp (cdr x))
                   (if (consp (cddr x))
                       (vl-print ", ")
                     (vl-print " and "))
                 ps)
               (vl-pp-merged-index-list (cdr x)))))

(define vl-lucid-pp-bits ((x (and (integer-listp x) (setp x))) &key (ps 'ps))
  (b* (;; X are indices from low to high.
       ;; They need to be in that order for merging to work.  So merge them
       ;; in low to high order.
       (merged (vl-merge-contiguous-indices x))
       ;; For printing we want them in high to low order, so reverse them.
       (merged (rev merged)))
    ;; Now turn them into nice looking strings.
    (vl-pp-merged-index-list merged))
  :prepwork
  ((local (defthm l0
            (implies (integer-listp x)
                     (vl-maybe-integer-listp x))
            :hints(("Goal" :induct (len x))))))
  )

(define vl-lucid-summarize-bits ((x (and (integer-listp x)
                                         (setp x))))
  :returns (summary stringp :rule-classes :type-prescription)
  (with-local-ps (vl-lucid-pp-bits x))
  ///
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3)) "[3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3 5 6 7)) "[7:5] and [3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 4 6 7 11)) "11, [7:6], 4 and [2:1]")))



; Identifying Multiple Drivers ------------------------------------------------
;
; Since we are collecting up the lists of all sets and uses of variables, we
; can analyze the list of SETs for a particular variable to try to see if it is
; multiply driven.
;
; A variable is not necessarily multiply driven just because there are multiple
; SETs.  For instance, if someone writes:
;
;   assign foo[1] = ...;
;   assign foo[2] = ...;
;
; Then we'll end up with two slice occurrences for foo, but foo obviously
; doesn't have multiple drivers because these sets are to disjoint slices.  So
; we need to do a sort of bit-level analysis here.
;
; Meanwhile, there are also certain kinds of multiple drivers that we do want
; to allow.  For instance, consider:
;
;    always @(posedge clk)
;    begin
;       foo = 0;
;       if (condition) foo = 1;
;    end
;
; This is all basically reasonable and foo isn't really being multiply driven.
; But this will create two separate SET occurrences for foo.  So, we'll need to
; take care to sort of collapse any SETs that occur in the same always block,
; function declaration, or task declaration.
;
; Also, we definitely don't really want to regard initial or final statements
; as any sort of real SETs, because something like this is perfectly fine:
;
;    initial foo = 0;
;    always @(posedge clk) foo = foo_in;

(define vl-lucidocclist-drop-initials/finals ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Remove all occurrences that are from @('initial') statements."
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       (elem (vl-lucidctx->elem (vl-lucidocc->ctx (car x))))
       (initial-p (mbe :logic (vl-initial-p elem)
                       :exec (eq (tag elem) :vl-initial)))
       (final-p (mbe :logic (vl-final-p elem)
                       :exec (eq (tag elem) :vl-final)))
       ((when (or initial-p final-p))
        (vl-lucidocclist-drop-initials/finals (cdr x))))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-initials/finals (cdr x)))))

(define vl-inside-true-generate-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-true-generate-p ss.super)
               (and (mbe :logic (vl-genblob-p ss.top)
                         :exec (eq (tag ss.top) :vl-genblob))
                    ;; Pretty gross hack.  When we turn modules into genblobs
                    ;; they have a name.  When we turn real generates into
                    ;; genblobs (vl-sort-genelements) they don't.  So, we're
                    ;; only in a "true" generate if there is no name.
                    (member (vl-genblob->scopetype ss.top)
                            '(:vl-genblock
                              :vl-genarrayblock
                              :vl-anonymous-scope))))))

(define vl-lucidocclist-drop-generates ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Removes all occurrences that are inside of @('generate') blocks."
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       ((when (vl-inside-true-generate-p (vl-lucidocc->ss (car x))))
        (vl-lucidocclist-drop-generates (cdr x))))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-generates (cdr x)))))



;; Module instances.

(define vl-lucid-plainarg-nicely-resolved-p ((x vl-plainarg-p))
  (b* (((vl-plainarg x)))
    (if x.dir
        t
      nil)))

(deflist vl-lucid-plainarglist-nicely-resolved-p (x)
  :guard (vl-plainarglist-p x)
  (vl-lucid-plainarg-nicely-resolved-p x))

(define vl-lucid-modinst-nicely-resolved-p ((x vl-modinst-p))
  (b* (((vl-modinst x)))
    (vl-arguments-case x.portargs
      (:vl-arguments-named nil)
      (:vl-arguments-plain (vl-lucid-plainarglist-nicely-resolved-p x.portargs.args)))))

(define vl-lucidocclist-drop-bad-modinsts ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Removes occurrences from unresolved module instances."
  :long "<p>The problem we are solving here happens when there is a buggy
module instance.</p>

<p>Suppose a module being instanced has a parse error, or that we hit some
problem resolving the arguments of the instance, for whatever reason.  In this
case, for lucid's usual use/set checking, the right thing to do (to suppress
false positives) is to pretend each argument to the module is both used and
set.</p>

<p>However, for multidrive warnings this is counterproductive and causes us to
think inputs are driven!  So, for multidrive detection, drop module instances
whose arguments are not sensibly resolved.</p>"
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       (elem      (vl-lucidctx->elem (vl-lucidocc->ctx (car x))))
       (modinst-p (mbe :logic (vl-modinst-p elem)
                       :exec (eq (tag elem) :vl-modinst)))
       ((when (and modinst-p
                   (not (vl-lucid-modinst-nicely-resolved-p elem))))
        ;; Skip it because it is a very bad modinst.
        (vl-lucidocclist-drop-bad-modinsts (cdr x))))
    ;; Else everything is peachy.
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-bad-modinsts (cdr x)))))

(define vl-lucid-scopestack-subscope-p ((a vl-scopestack-p)
                                        (b vl-scopestack-p))
  :short "Determine if scopestack @('a') occurs within scopestack @('b')."
  :measure (vl-scopestack-count b)
  (b* ((a (vl-scopestack-fix a))
       (b (vl-scopestack-fix b)))
    (or (hons-equal a b)
        (vl-scopestack-case b
          :null nil
          :global nil
          :local (vl-lucid-scopestack-subscope-p a b.super)))))

(define vl-lucidocclist-drop-foreign-writes ((x       vl-lucidocclist-p)
                                             (decl-ss vl-scopestack-p))
  :returns (new-s vl-lucidocclist-p)
  (b* (((when (atom x))
        nil)
       (ss1 (vl-lucidocc->ss (car x)))
       ((unless (vl-lucid-scopestack-subscope-p ss1 decl-ss))
        ;; Foreign, drop it.
        (vl-lucidocclist-drop-foreign-writes (cdr x) decl-ss)))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-foreign-writes (cdr x) decl-ss))))


; Grouping up always/fundecls/taskdecls

(fty::defalist vl-lucidmergealist
  ;; Alist used to group up always/fundecl/taskdecl writes to the same variable
  :key-type vl-lucidctx-p
  :val-type vl-lucidocclist-p
  :count vl-lucidmergealist-count)

(define vl-lucid-filter-merges
  :short "Group up occurrences into those to be merged (into a merge alist) and
          those not to be merged (into a regular list)."
  ((x       vl-lucidocclist-p    "Occurrences to filter.")
   (merge   vl-lucidmergealist-p "Accumulator for occs to merge (always blocks, function decls, tasks.).")
   (regular vl-lucidocclist-p    "Accumulator for occs not to merge (continuous assigns, instances)."))
  :returns
  (mv (merge   vl-lucidmergealist-p)
      (regular vl-lucidocclist-p))
  :measure (len x)
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* ((x       (vl-lucidocclist-fix x))
       (merge   (vl-lucidmergealist-fix merge))
       (regular (vl-lucidocclist-fix regular))
       ((when (atom x))
        (mv merge regular))
       (occ1   (car x))
       (ctx1   (vl-lucidocc->ctx occ1))
       (elem1  (vl-lucidctx->elem ctx1))
       (mergep (or (mbe :logic (vl-fundecl-p elem1)  :exec (eq (tag elem1) :vl-fundecl))
                   (mbe :logic (vl-taskdecl-p elem1) :exec (eq (tag elem1) :vl-taskdecl))
                   (mbe :logic (vl-always-p elem1)   :exec (eq (tag elem1) :vl-always))))
       ((unless mergep)
        (vl-lucid-filter-merges (cdr x) merge (cons (car x) regular)))
       (others (cdr (hons-get ctx1 merge)))
       (merge  (hons-acons ctx1 (cons occ1 others) merge)))
    (vl-lucid-filter-merges (cdr x) merge regular)))

(define vl-lucid-do-merges1 ((occs vl-lucidocclist-p "Some sets that all occur in the same always/function/task."))
  :returns (merged-occs vl-lucidocclist-p "Merged together occurrences, if any.")
  (b* ((solo (vl-lucid-first-solo-occ occs))
       ((when solo)
        ;; Doesn't matter what else happens, this block writes to all of foo,
        ;; so consider it as a write to all of foo.
        (list solo))
       ((when (atom occs))
        nil))
    ;; BOZO eventually we should do something smarter here to try to merge
    ;; together any bits we can tell are used.  Maybe we need a new kind of occ
    ;; for that.  For now, we'll just arbitrarily return the first occurrence,
    ;; which may make our analysis a bit incomplete.
    (list (vl-lucidocc-fix (car occs)))))

(define vl-lucid-do-merges ((merge vl-lucidmergealist-p))
  :returns (merged vl-lucidocclist-p)
  :short "Combine the occurrences in the merge alist into single occurrences."
  :measure (vl-lucidmergealist-count merge)
  (b* ((merge (vl-lucidmergealist-fix merge))
       ((when (atom merge))
        nil)
       ((cons ?ctx1 occs1) (first merge)))
    (append (vl-lucid-do-merges1 occs1)
            (vl-lucid-do-merges (rest merge)))))

(define vl-lucidocclist-merge-blocks ((x vl-lucidocclist-p))
  :returns (merged vl-lucidocclist-p)
  :parents (vl-lucid-multidrive-detect)
  :short "Combine together the writes to a variable that occur in the same
          always block."
  (b* (((mv merge-alist regular) (vl-lucid-filter-merges x nil nil))
       (merge-alist (fast-alist-clean merge-alist)))
    (fast-alist-free merge-alist)
    (append (vl-lucid-do-merges merge-alist)
            regular)))

(define vl-pp-lucid-multidrive-summary ((occs vl-lucidocclist-p) &key (ps 'ps))
  (if (atom occs)
      ps
    (vl-ps-seq (vl-indent 4)
               (vl-print " - ")
               (vl-pp-ctxelement-summary (vl-lucidctx->elem (vl-lucidocc->ctx (car occs)))
                                         :withloc t)
               (vl-println "")
               (vl-pp-lucid-multidrive-summary (cdr occs)))))

(define vl-lucid-multidrive-summary ((occs vl-lucidocclist-p))
  :returns (summary stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-lucid-multidrive-summary occs)))


; Heuristic for identifying transistor-style drivers.
;
; In some cases, a particular driver looks like a transistory sort of thing
; and we will not want to issue warnings about multiple drivers.
;  - Gate instances of transistor-style gates like tran gates, pullups, bufifs, nmos, etc.
;  - Assignments that are often used to make one-hot muxes, like
;      assign foo = condition ? foo : 1'bz;

(define vl-lucid-z-expr-p ((x vl-expr-p))
  ;; Recognizes: any width `Z`, `foo ? bar : Z`, or `foo ? Z : bar`
  (or (vl-zatom-p x)
      (vl-expr-case x
        :vl-qmark (or (vl-zatom-p x.then)
                      (vl-zatom-p x.else))
        :otherwise nil)))

(define vl-lucid-z-assign-p ((x vl-assign-p))
  (vl-lucid-z-expr-p (vl-assign->expr x)))

(define vl-lucid-z-gateinst-p ((x vl-gateinst-p))
  (b* (((vl-gateinst x) x))
    (member x.type
            '(:vl-cmos :vl-rcmos :vl-bufif0 :vl-bufif1 :vl-notif0 :vl-notif1
              :vl-nmos :vl-pmos :vl-rnmos :vl-rpmos :vl-tranif0 :vl-tranif1
              :vl-rtranif1 :vl-rtranif0 :vl-tran :vl-rtran :vl-pulldown
              :vl-pullup))))

(define vl-lucidocc-transistory-p ((x vl-lucidocc-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (b* ((elem (vl-lucidctx->elem (vl-lucidocc->ctx x)))
       (tag  (tag elem)))
    (or (and (mbe :logic (vl-gateinst-p elem) :exec (eq tag :vl-gateinst))
             (vl-lucid-z-gateinst-p elem))
        (and (mbe :logic (vl-assign-p elem) :exec (eq tag :vl-assign))
             (vl-lucid-z-assign-p elem)))))

(define vl-lucidocclist-some-transistory-p ((x vl-lucidocclist-p))
  (if (atom x)
      nil
    (or (vl-lucidocc-transistory-p (car x))
        (vl-lucidocclist-some-transistory-p (cdr x)))))



; Bit-level analysis.  This is potentially pretty inefficient but I don't think
; we have to worry much about it, because it will only be inefficient when
; there are lots of writes to the same variable.

(define vl-lucid-collect-resolved-slices ((x vl-lucidocclist-p))
  :returns (resolved (and (vl-lucidocclist-p resolved)
                          (vl-lucid-all-slices-p resolved)
                          (vl-lucid-all-slices-resolved-p resolved)))
  (b* (((when (atom x))
        nil)
       ((when (and (eq (vl-lucidocc-kind (car x)) :slice)
                   (vl-lucid-resolved-slice-p (car x))))
        (cons (vl-lucidocc-fix (car x))
              (vl-lucid-collect-resolved-slices (cdr x)))))
    (vl-lucid-collect-resolved-slices (cdr x))))

(define vl-lucid-slices-append-bits ((x vl-lucidocclist-p)
                                     (ctx any-p))
  :guard (and (vl-lucid-all-slices-p x)
              (vl-lucid-all-slices-resolved-p x))
  :returns (bits integer-listp)
  (if (atom x)
      nil
    (append (vl-lucid-resolved-slice->bits (car x) ctx)
            (vl-lucid-slices-append-bits (cdr x) ctx)))
  ///
  (more-returns
   (bits true-listp :rule-classes :type-prescription)))

(define vl-lucid-pp-multibits
  ((badbits  setp              "The set of multiply driven bits.")
   (occs     vl-lucidocclist-p "Occs which may or may not drive these bits.")
   (ctx      any-p)
   &key (ps 'ps))
  :guard (and (integer-listp badbits)
              (vl-lucid-all-slices-p occs)
              (vl-lucid-all-slices-resolved-p occs))
  (b* (((when (atom occs))
        ps)
       (occbits (vl-lucid-resolved-slice->bits (car occs) ctx))
       (overlap (intersect occbits badbits))
       ((unless overlap)
        (vl-lucid-pp-multibits badbits (cdr occs) ctx)))
    ;; Else, there is some overlap here:
    (vl-ps-seq (vl-indent 4)
               (if (vl-plural-p overlap)
                   (vl-print " - Bits ")
                 (vl-print " - Bit "))
               (vl-lucid-pp-bits overlap)
               (vl-print ": ")
               (vl-pp-ctxelement-summary (vl-lucidctx->elem (vl-lucidocc->ctx (car occs)))
                                         :withloc t)
               (vl-println "")
               (vl-lucid-pp-multibits badbits (cdr occs) ctx))))

(define vl-inside-interface-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-interface-p ss.super)
               (mbe :logic (vl-interface-p ss.top)
                    :exec (eq (tag ss.top) :vl-interface)))))

(define vl-inside-blockscope-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-blockscope-p ss.super)
               (mbe :logic (vl-blockscope-p ss.top)
                    :exec (eq (tag ss.top) :vl-blockscope)))))


(defsection vl-custom-suppress-multidrive-p
  :short "Mechanism for custom suppression of multidrive warnings."
  :long "<p>We use this at Centaur to suppress multidrive warnings within
certain modules that we know are not RTL designs.</p>

<p>This is an attachable function that should return @('t') when you want
to suppress warnings.  It can inspect:</p>

<ul>
<li>@('ss') - the scopestack for the declaration.</li>
<li>@('item') - the variable or parameter declaration itself.</li>
<li>@('set') - the list of places where the variable was set.</li>
</ul>

<p>This suppression is done in addition to the default heuristics.  That is,
your function can focus just on the additional rules you want to add, and
doesn't have to recreate the default heuristics.</p>"

  (encapsulate
    (((vl-custom-suppress-multidrive-p * * *) => *
      :formals (ss item set)
      :guard (and (vl-scopestack-p ss)
                  (or (vl-paramdecl-p item)
                      (vl-vardecl-p item))
                  (vl-lucidocclist-p set))))

    (local (defun vl-custom-suppress-multidrive-p (ss item set)
             (declare (ignorable ss item set))
             nil))

    (defthm booleanp-of-vl-custom-suppress-multidrive-p
      (booleanp (vl-custom-suppress-multidrive-p ss item set))
      :rule-classes :type-prescription))

  (define vl-custom-suppress-multidrive-p-default ((ss    vl-scopestack-p)
                                                   (item  (or (vl-paramdecl-p item)
                                                              (vl-vardecl-p item)))
                                                   (set   vl-lucidocclist-p))
    (declare (ignorable ss item set))
    nil)

  (defattach vl-custom-suppress-multidrive-p
    vl-custom-suppress-multidrive-p-default))

(define vl-lucidocclist-remove-tails ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :tail)
         (vl-lucidocclist-remove-tails (cdr x)))
        (t
         (cons (vl-lucidocc-fix (car x))
               (vl-lucidocclist-remove-tails (cdr x))))))

(define vl-lucid-multidrive-detect
  ((ss    vl-scopestack-p)
   (item  (or (vl-paramdecl-p item)
              (vl-vardecl-p item)))
   (set   vl-lucidocclist-p)
   (genp  booleanp "Consider occurrences from generates?"))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (warnings vl-warninglist-p)
  (b* ((ss  (vl-scopestack-fix ss))
       (set (vl-lucidocclist-fix set))

       ((when (or (atom set)
                  (atom (cdr set))))
        ;; No driver or at most one driver, so there are not multiple drivers.
        nil)
       ;; Clean up the list of sets by:
       ;;
       ;;  1. Eliminating any sets from initial/final blocks
       ;;
       ;;  2. Merging together any writes that happen in the same always block,
       ;;     function declaration, or task declaration, so that we don't
       ;;     complain about things like:
       ;;
       ;;       always @(posedge clk) begin
       ;;         foo = 0;
       ;;         if (whatever) foo = 1;
       ;;       end
       ;;
       ;;  3. Drop occurrences from "bad" module instances (where we could have
       ;;     accidentally think that inputs are being driven)
       ;;
       ;;  4. Drop generates if we have been told to ignore them.
       ;;
       ;;  5. Drop "foreign writes" -- writes that occur from a scopestack other
       ;;     than where the variable is declared.  Without this, we get into
       ;;     problems due to things like this:
       ;;
       ;;        submod inst1 (...);
       ;;        submod inst2 (...);
       ;;        always @(...) begin
       ;;           assign inst1.foo = 1;
       ;;           assign inst2.foo = 1;
       ;;        end
       ;;
       ;;     The problem is that this looks like two drivers onto submod.foo.
       ;;
       ;;  6. Drop TAIL occurrences, because they might be things like foo[3-:0]
       ;;     that we don't understand.
       (set (vl-lucidocclist-drop-initials/finals set))
       (set (vl-lucidocclist-merge-blocks set))
       (set (vl-lucidocclist-drop-bad-modinsts set))
       (set (vl-lucidocclist-drop-foreign-writes set ss))
       (set (if genp set (vl-lucidocclist-drop-generates set)))
       (set (vl-lucidocclist-remove-tails set))

       ((when (or (atom set)
                  (atom (cdr set))))
        nil)

       ((when (and (eq (tag item) :vl-vardecl)
                   (not (member (vl-vardecl->nettype item) '(nil :vl-wire :vl-uwire)))))
        ;; This has a fancy net type such as TRI, TRIREG, WOR, WAND, SUPPLY,
        ;; etc., which suggests that this is a transistor-level design rather
        ;; than an RTL level design.
        ;;
        ;;  - We certainly do not want to issue any warnings about nets such as
        ;;    TRI/WAND/WOR since those net types strongly indicate that
        ;;    multiple drivers are expected.
        ;;
        ;;  - BOZO I don't know whether or not it ever makes sense to be driving
        ;;    a supply1/supply0 wire.  But I think that even if this doesn't make
        ;;    sense, it's nothing we want to be issuing warnings about.
        nil)

       ((when (vl-lucidocclist-some-transistory-p set))
        ;; Something that is driving this wire looks like a transistor or like
        ;; it sometimes may drive Z values onto the wire.  We therefore do NOT
        ;; want to issue any warnings.
        nil)

       ((mv simple-p ?valid-bits)
        (vl-lucid-valid-bits-for-decl item ss))
       ((unless simple-p)
        ;; Something like an array or fancy structure that is just going to be
        ;; too hard for us to warn about.  (BOZO some day we might try to
        ;; improve the scope of what we can check.)
        nil)

       ((when (vl-inside-interface-p ss))
        ;; This variable is declared somewhere within an interface.  It's fine
        ;; for there to be multiple uses/sets of it, because there may be many
        ;; instances of the interface throughout the design.
        nil)

       ((when (vl-inside-blockscope-p ss))
        ;; This variable is defined in a block scope, i.e., a function, task, or
        ;; begin/end block.  Such variables are used in procedural code and are
        ;; hence not anything we want to give multidrive warnings about.
        nil)

       ((when (vl-custom-suppress-multidrive-p ss item set))
        ;; The user wants to exclude this warning.
        nil)

       (name     (if (eq (tag item) :vl-vardecl)
                     (vl-vardecl->name item)
                   (vl-paramdecl->name item)))

       (solos (vl-lucid-collect-solo-occs set))
       ((when (and (consp solos)
                   (consp (cdr solos))))
        (list (make-vl-warning :type :vl-lucid-multidrive
                               :msg "~w0 has multiple drivers:~%~s1"
                               :args (list name (vl-lucid-multidrive-summary solos)
                                           item)
                               :fn __function__)))

       ;; If we get this far, there aren't any whole-wire conflicts.  Let's see
       ;; if we can find any bit-level conflicts.

       (resolved (vl-lucid-collect-resolved-slices set))
       (allbits  (vl-lucid-slices-append-bits resolved item))

       ((when (and (consp solos)
                   (consp allbits)))
        ;; There is a write to the entire wire, and also some writes to individual
        ;; bits.  So, we want to warn about any of these allbits.
        (list (make-vl-warning
               :type :vl-lucid-multidrive
               :msg "~w0 has multiple drivers:~%~s1"
               :args (list name
                           (with-local-ps
                             (vl-indent 4)
                             (vl-print " - Full: ")
                             (vl-pp-ctxelement-summary (vl-lucidctx->elem (vl-lucidocc->ctx (car solos)))
                                                       :withloc t)
                             (vl-println "")
                             (vl-lucid-pp-multibits (mergesort allbits) resolved item))
                           item)
               :fn __function__)))

       ;; Otherwise, there aren't any writes to the whole wire, but there may
       ;; still be overlaps between the individual bits, so check for
       ;; duplicates.
       (dupes   (duplicated-members allbits))
       ((unless (consp dupes))
        ;; No bits are obviously duplicated.
        nil))
    (list (make-vl-warning
           :type :vl-lucid-multidrive
           :msg "~w0 has multiple drivers on some bits:~%~s1"
           :args (list name (with-local-ps
                              (vl-lucid-pp-multibits (mergesort dupes) resolved item))
                       item)
           :fn __function__))))

(define vl-lucid-check-uses-are-spurious-instances ((name stringp)
                                                    (used vl-lucidocclist-p)
                                                    (db vl-luciddb-p)
                                                    (clk natp))
  :returns (mv just-passed-to-a-spurious-instance
               (warnings vl-warninglist-p))
  :prepwork ((local (DEFTHM VL-SCOPE-P-WHEN-VL-MODULE-P-strong
                      (IMPLIES (VL-MODULE-P X) (VL-SCOPE-P X))))
             (local (DEFTHM VL-SCOPE-P-WHEN-VL-INTERFACE-P-strong
                      (IMPLIES (VL-INTERFACE-P X) (VL-SCOPE-P X)))))
  :measure (acl2::two-nats-measure clk (len used))
  :verify-guards nil
  (b* (((when (atom used)) (mv t nil))
       (name (string-fix name))
       (db (vl-luciddb-fix db))
       ((mv rest-just-passed warnings)
        (vl-lucid-check-uses-are-spurious-instances name (cdr used) db clk))
       ((unless rest-just-passed) (mv nil warnings))
       (occ (car used))
       ((vl-lucidctx ctx) (vl-lucidocc->ctx occ))
       ((unless (and (eq (tag ctx.elem) :vl-modinst)
                     ctx.portname))
        (mv nil warnings))
       (modname (vl-modinst->modname ctx.elem))
       (mod (vl-scopestack-find-definition modname ctx.ss))
       ((unless (and mod (member (tag mod) '(:vl-module :vl-interface))))
        ;; ??? Not really our job to warn about this here, but what else can we do?
        (mv nil
            (warn :type :vl-lucid-programming-error
                  :msg "Confused -- it seems ~s0 is used in instance ~s1 (path:
                        ~s2) but can't find module/interface ~s3"
                  :args (list name (vl-modinst->instname ctx.elem) (vl-scopestack->path ctx.ss) modname))))
       (key-ss (vl-normalize-scopestack
                (vl-scopestack-push mod (vl-scopestack->toplevel ctx.ss))))
       (key-item (vl-scopestack-find-item ctx.portname key-ss))
       ((unless key-item)
        ;; Blah, technically we could have no item here because of port renaming junk
        (mv nil
            (warn :type :vl-lucid-programming-error
                  :msg "Confused -- it seems ~s0 is connected to port ~s1 of instance ~s2 (path:
                        ~s3) but can't find a declaration of that name in ~s4"
                  :args (list name ctx.portname (vl-modinst->instname ctx.elem)
                              (vl-scopestack->path ctx.ss) modname))))
       (key (make-vl-lucidkey :item key-item
                              :scopestack key-ss))
       (lookup (cdr (hons-get key db)))
       ((unless (and lookup
                     (consp (vl-lucidval->used lookup))))
        ;; Not used.
        (mv t nil))

       ;; Now check whether all of those uses are spurious.
       ((when (zp clk))
        (mv nil
            (warn :type :vl-lucid-spurious-instances-loop
                  :msg "Recursion limit ran out when looking for spurious instances for ~s0"
                  :args (list name)))))
    ;; The port is used, but check whether all of its uses are spurious instances as well.
    (vl-lucid-check-uses-are-spurious-instances ctx.portname (vl-lucidval->used lookup)
                                                db (1- clk)))
  ///
  (verify-guards vl-lucid-check-uses-are-spurious-instances))

(define vl-lucid-warning-type ((warning symbolp)
                               &key (tag 'tag))
  :returns (type symbolp :rule-classes :type-prescription)
  (if (eq tag :vl-vardecl)
      (intern$ (cat (symbol-name warning) "-VARIABLE")
               "KEYWORD")
    (mbe :logic (acl2::symbol-fix warning)
         :exec warning)))

(define vl-scopestack-is-portdecl-p ((name stringp "Name of some variable in this scopestack.")
                                     (ss   vl-scopestack-p))
  :returns (portdecl-p booleanp :rule-classes :type-prescription)
  ;; Variables and ports overlap, so it seems like a good way to figure this
  ;; out is to start by looking up the variable itself and finding the scope
  ;; that it comes from.  Then, check if it's also a port in that particular
  ;; scope.
  (b* (((mv item item-ss) (vl-scopestack-find-item/ss name ss)))
    (and item
         (vl-scopestack-case item-ss
           :null nil
           :global nil
           :local (if (vl-scope-find-portdecl-fast name item-ss.top)
                      t
                    nil)))))

(define vl-lucid-dissect-var-main
  ((ss         vl-scopestack-p)
   (item       (or (vl-paramdecl-p item)
                   (vl-vardecl-p item)))
   (used       vl-lucidocclist-p)
   (set        vl-lucidocclist-p)
   (db         vl-luciddb-p)
   (genp       booleanp))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (mv (warnings vl-warninglist-p)
               (possible-typop booleanp :rule-classes :type-prescription
                               "Is this wire a typo-detection candidate?  (Our
                                idea is to focus on wires that are introduced
                                implicitly and either unset or unused.)"))
  (b* ((used     (vl-lucidocclist-fix used))
       (set      (vl-lucidocclist-fix set))
       (tag      (tag item))
       (vartype  (if (eq tag :vl-vardecl)
                     (if (vl-scopestack-is-portdecl-p (vl-vardecl->name item) ss)
                         "Port"
                       "Variable")
                   "Parameter"))
       (name     (if (eq tag :vl-vardecl)
                     (vl-vardecl->name item)
                   (vl-paramdecl->name item)))

       (warnings (vl-lucid-multidrive-detect ss item set genp))

       ((when (and (atom used) (atom set)))
        ;; No uses and no sets of this variable.  It seems best, in this case,
        ;; to issue only a single warning about this spurious variable, rather
        ;; than separate unused/unset warnings.
        (mv (warn :type (vl-lucid-warning-type :vl-lucid-spurious)
                  :msg "~s0 ~w1 is never used or set anywhere. (~s2)"
                  :args (list vartype name
                              (with-local-ps (vl-pp-scopestack-path ss))))
            ;; I don't think we want to regard this as a typo candidate either,
            ;; since the goal of that is to find typos in wires that actually
            ;; *are* being used or set.
            nil))

       (used-solop (vl-lucid-some-solo-occp used))
       (set-solop  (vl-lucid-some-solo-occp set))
       ((when (and used-solop set-solop))
        ;; The variable is both used and set in full somewhere, so there is
        ;; clearly nothing we need to warn about and we don't need to do any
        ;; further bit-level analysis.
        (mv warnings nil))

       ((mv simplep valid-bits)
        (vl-lucid-valid-bits-for-decl item ss))

       ;; Try to warn about any unused bits
       (warnings
        (b* (((when (atom used))
              ;; No uses of this variable at all.  No need to do any special
              ;; bit-level analysis.
              (warn :type (vl-lucid-warning-type :vl-lucid-unused)
                    :msg "~s0 ~w1 is set but is never used. (~s2)"
                    :args (list vartype name
                                (with-local-ps (vl-pp-scopestack-path ss))
                                item)))
             ((when used-solop)
              ;; The variable is used somewhere all by itself without any
              ;; indexing, so there's no reason to do any bit-level analysis.
              warnings)
             ((unless (and simplep
                           (vl-lucid-all-slices-p used)
                           (vl-lucid-all-slices-resolved-p used)))
              ;; We found uses of the variable but we don't understand what the
              ;; valid bits are or what some of these indices are referring to,
              ;; so this is too hard and we're not going to try to issue any
              ;; warnings.
              warnings)
             ;; Otherwise, we *do* understand all the uses of this variable
             ;; so we can figure out which bits are used.
             (used-bits   (vl-lucid-resolved-slices->bits used item))
             (unused-bits (difference valid-bits used-bits))
             ((unless unused-bits)
              ;; All of the bits get used somewhere so this is fine.
              warnings))
          (warn :type (vl-lucid-warning-type :vl-lucid-unused)
                :msg "~s0 ~w1 has some bits that are never used: ~s2. (~s3)"
                :args (list vartype name
                            (vl-lucid-summarize-bits unused-bits)
                            (with-local-ps (vl-pp-scopestack-path ss))
                            item))))

       ;; Try to warn about any unset bits
       (warnings
        (b* (((when (atom set))
              (b* (((wmv just-passed-to-spurious-instances warnings)
                    (vl-lucid-check-uses-are-spurious-instances name used db 100))
                   ((when just-passed-to-spurious-instances)
                    (warn :type :vl-lucid-spurious-port
                          :msg "~s0 ~w1 is never set and is only passed to module instances where it is not used. (~s2)"
                          :args (list vartype name (with-local-ps (vl-pp-scopestack-path ss))
                                      item))))
                (warn :type (vl-lucid-warning-type :vl-lucid-unset)
                      :msg "~s0 ~w1 is used but is never initialized. (~s2)"
                      :args (list vartype name
                                  (with-local-ps (vl-pp-scopestack-path ss))
                                  item))))
             ((when set-solop)
              warnings)
             ((unless (and simplep
                           (vl-lucid-all-slices-p set)
                           (vl-lucid-all-slices-resolved-p set)))
              warnings)
             (set-bits    (vl-lucid-resolved-slices->bits set item))
             (unset-bits  (difference valid-bits set-bits))
             ((unless unset-bits)
              warnings))
          (warn :type (vl-lucid-warning-type :vl-lucid-unset)
                :msg "~s0 ~w1 has some bits that are never set: ~s2. (~s3)"
                :args (list vartype name
                            (vl-lucid-summarize-bits unset-bits)
                            (with-local-ps (vl-pp-scopestack-path ss))
                            item))))

       (typop (and
               ;; If the variable is totally unused, or totally unset, and is
               ;; implicit, then it seems like a good chance that it might be a
               ;; typo.
               (or (atom used) (atom set))
               (eq (tag item) :vl-vardecl)
               (consp (assoc-equal "VL_IMPLICIT" (vl-vardecl->atts item))))))

    (mv warnings typop)))

(fty::defalist vl-typocandidates
  :key-type vl-scopestack-p
  :val-type string-listp
  :short "Binds top-level module names to lists of wires that might be typos
          inside them.")

(define vl-add-typo-candidate ((ss      vl-scopestack-p     "Scope where this potential typo occurs.")
                               (varname stringp             "Variable that we think may be misspelled.")
                               (typos   vl-typocandidates-p "Fast alist to extend."))
  :returns (new-typos vl-typocandidates-p)
  (b* ((ss      (vl-scopestack-fix ss))
       (varname (string-fix varname))
       (typos   (vl-typocandidates-fix typos))
       (old     (cdr (hons-get ss typos))))
    (hons-acons ss (cons varname old) typos)))

(define vl-scopestack->topname ((ss vl-scopestack-p))
  ;; The top-level design element to blame, from the scopestack, for any
  ;; warnings.  If there isn't any containing element, we'll just blame
  ;; the whole :design.
  :returns (key vl-reportcardkey-p)
  (or (vl-scopestack-top-level-name ss)
      :design))

(define vl-lucid-dissect-pair ((key        vl-lucidkey-p)
                               (val        vl-lucidval-p)
                               (reportcard vl-reportcard-p)
                               (st         vl-lucidstate-p)
                               (typos      vl-typocandidates-p))
  :returns (mv (reportcard vl-reportcard-p)
               (typos      vl-typocandidates-p))
  (b* ((reportcard (vl-reportcard-fix reportcard))
       (typos (vl-typocandidates-fix typos))
       ((vl-lucidstate st))
       ((vl-lucidkey key))
       ((vl-lucidval val))
       (topname (vl-scopestack->topname key.scopestack))

       (sequential-udp-p
        ;; Stupid way to look this up -- it would be nicer to just look in the
        ;; scopestack, but we turn modules into genblobs when we process them,
        ;; and genblobs don't have atts for some reason...
        (b* ((dfn (and (stringp topname)
                       (vl-scopestack-find-definition topname key.scopestack))))
          (and (eq (tag dfn) :vl-module)
               (consp (assoc-equal "VL_SEQUENTIAL_UDP" (vl-module->atts dfn))))))

       ((when sequential-udp-p)
        ;; See vl-udp-to-module: we threw away everything in the UDP so we
        ;; can't give any kind of sensible warnings.  So don't warn about
        ;; anything here.
        (mv reportcard typos))

       ((when val.errors)
        ;; We won't warn about anything else.
        (b* ((w (make-vl-warning
                 :type :vl-lucid-error
                 :msg "Error computing use/set information for ~s0.  Debugging details: ~x1."
                 :args (list (with-local-ps (vl-pp-lucidkey key))
                             val.errors)
                 :fatalp nil
                 :fn __function__)))
          (mv (vl-extend-reportcard topname w reportcard)
              typos))))

    (case (tag key.item)

      (:vl-fundecl
       (b* (((when (vl-lucid-some-solo-occp val.used))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Function ~w0 is never used. (~s1)"
                                :args (list (vl-fundecl->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-genvar
       ;; We'll do a particularly dumb analysis here and only see if the
       ;; variable has any sets/uses.
       (b* ((usedp (consp val.used))
            (setp  (consp val.set))
            ((when (and usedp setp))
             ;; Everything's good.
             (mv reportcard typos))
            (name (vl-genvar->name key.item))
            (path (with-local-ps (vl-pp-scopestack-path key.scopestack)))
            (w (cond ((and (not usedp) (not setp))
                      (make-vl-warning :type :vl-lucid-spurious
                                       :msg "Genvar ~w0 is never used or set anywhere. (~s1)"
                                       :args (list name path key.item)
                                       :fn __function__
                                       :fatalp nil))
                     ((and usedp (not setp))
                      (make-vl-warning :type :vl-lucid-unset
                                       :msg "Genvar ~w0 is never set. (~s1)"
                                       :args (list name path key.item)
                                       :fn __function__
                                       :fatalp nil))
                     (t
                      (make-vl-warning :type :vl-lucid-unused
                                       :msg "Genvar ~w0 is never used. (~s1)"
                                       :args (list name path key.item)
                                       :fn __function__
                                       :fatalp nil)))))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-modport
       (b* (((unless st.modportsp)
             ;; Don't do any analysis of modports unless it's permitted.
             (mv reportcard typos))
            ((when (vl-lucid-some-solo-occp val.used))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Modport ~s0 is never used. (~s1)"
                                :args (list (vl-modport->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-dpiimport
       (b* (((when (vl-lucid-some-solo-occp val.used))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "DPI imported function ~w0 is never used. (~s1)"
                                :args (list (vl-dpiimport->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-taskdecl
       (b* (((when (vl-lucid-some-solo-occp val.used))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Task ~w0 is never used. (~s1)"
                                :args (list (vl-taskdecl->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-typedef
       (b* (((when (vl-lucid-some-solo-occp val.used))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Type ~w0 is never used. (~s1)"
                                :args (list (vl-typedef->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-vardecl
       (b* (((mv warnings possible-typop)
             (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set st.db st.generatesp))
            (typos (if possible-typop
                       (vl-add-typo-candidate key.scopestack (vl-vardecl->name key.item) typos)
                     typos)))
         (mv (vl-extend-reportcard-list topname warnings reportcard)
             typos)))

      (:vl-paramdecl
       (b* (((unless st.paramsp)
             ;; Don't do any analysis of parameters unless it's permitted.
             (mv reportcard typos))
            ((mv warnings ?possible-typop)
             (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set st.db st.generatesp)))
         (mv (vl-extend-reportcard-list topname warnings reportcard)
             ;; We don't extend typos because we're looking for accidental
             ;; wire name uses and don't expect them to be parameters
             typos)))

      (:vl-interfaceport
       (b* (((when (or val.used val.set))
             ;; Used or set anywhere at all is good enough for an interface.
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-spurious
                                :msg "Interface port ~w0 is never mentioned. (~s1)"
                                :args (list (vl-interfaceport->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (:vl-modinst
       (b* (((vl-modinst key.item))
            (mod (vl-scopestack-find-definition key.item.modname key.scopestack))
            ((unless (eq (tag mod) :vl-interface))
             ;; Something like a UDP or a module instance.  We have no
             ;; expectation that this should be used anywhere.
             (mv reportcard typos))
            ;; Interface port.  We expect that this is at least used or set
            ;; somewhere.  It probably doesn't necessarily need to be both used
            ;; and set.
            ((when (or val.used val.set))
             (mv reportcard typos))
            (w (make-vl-warning :type :vl-lucid-spurious
                                :msg "Interface ~w0 is never mentioned. (~s1)"
                                :args (list key.item.instname
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack))
                                            key.item)
                                :fn __function__
                                :fatalp nil)))
         (mv (vl-extend-reportcard topname w reportcard)
             typos)))

      (otherwise
       ;; Other kinds of items include, for instance, modinsts, gateinsts,
       ;; generate statements, etc.  We don't have anything sensible to say
       ;; about those.
       (mv reportcard typos)))))

(define vl-lucid-dissect-database ((db         vl-luciddb-p "Already shrunk.")
                                   (reportcard vl-reportcard-p)
                                   (st         vl-lucidstate-p)
                                   (typos      vl-typocandidates-p))
  :returns (mv (reportcard vl-reportcard-p)
               (typos      vl-typocandidates-p))
  :measure (vl-luciddb-count db)
  (b* ((db    (vl-luciddb-fix db))
       (typos (vl-typocandidates-fix typos))
       ((when (atom db))
        (mv (vl-reportcard-fix reportcard)
            typos))
       ((cons key val) (car db))
       ((mv reportcard typos) (vl-lucid-dissect-pair key val reportcard st typos)))
    (vl-lucid-dissect-database (cdr db) reportcard st typos)))

(define vl-lucid-dissect ((st vl-lucidstate-p))
  :returns (mv (reportcard vl-reportcard-p)
               (typos      vl-typocandidates-p))
  (b* (((vl-lucidstate st))
       (copy (fast-alist-fork st.db nil))
       (-    (fast-alist-free copy)))
    (vl-lucid-dissect-database copy nil st nil)))


(define vl-scopestack->flat-transitive-names-slow ((ss vl-scopestack-p))
  ;; Collect a flat list of all names visible from some scope, so that we can
  ;; check possible typos against them to see if they are heuristically
  ;; similar.
  :returns (names (and (string-listp names)
                       (setp names)))
  :measure (vl-scopestack-count ss)
  :verify-guards nil
  (vl-scopestack-case ss
    :null nil
    :global (set::mergesort (vl-scope-namespace ss.design ss.design))
    :local (set::union (set::mergesort (vl-scope-namespace ss.top (vl-scopestack->design ss)))
                       (vl-scopestack->flat-transitive-names-slow ss.super)))
  :prepwork
  ((local (defthm l0
            (implies (vl-scopedef-alist-p x)
                     (string-listp (alist-keys x)))
            :hints(("Goal" :induct (len x))))))
  ///
  (verify-guards vl-scopestack->flat-transitive-names-slow)
  (memoize 'vl-scopestack->flat-transitive-names-slow))

;; (trace$ vl-possible-typo-warnings)
;; (trace$ (vl-lucid-dissect-pair
;;          :entry (list 'vl-lucid-dissect-pair (with-local-ps (vl-pp-lucidkey key)))
;;          :exit (b* (((list reportcard typos) values))
;;                  (list 'vl-lucid-dissect-pair :typos (alist-vals typos)))))


(define vl-possible-typo-warnings ((typo-alist alistp))
  ;; Horrible old legacy code bridge
  :guard (and (vl-string-keys-p typo-alist)
              (vl-string-list-values-p typo-alist))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom typo-alist))
        nil)
       ((cons badwire good-alternatives) (car typo-alist))
       (w (make-vl-warning
           :type :vl-warn-possible-typo
           :msg "Possible typo: implicit wire ~s0 looks like ~&1."
           :args (list badwire good-alternatives)
           :fn   __function__
           :fatalp nil)))
    (cons w (vl-possible-typo-warnings (cdr typo-alist)))))

(define vl-lucid-typo-detect1
  ((ss             vl-scopestack-p    "Scope where these possible typos occur.")
   (possible-typos string-listp       "Names of suspiciously unused/unset implicit wires.")
   (reportcard     vl-reportcard-p    "Reportcard to extend with actual warnings."))
  :returns (reportcard vl-reportcard-p)
  :verbosep t
  (b* ((possible-typos (set::mergesort (string-list-fix possible-typos)))
       (good-names (set::difference (vl-scopestack->flat-transitive-names-slow ss) possible-typos))
       (typo-alist (typo-detect possible-typos good-names))
       (warnings   (vl-possible-typo-warnings typo-alist))
       (topname    (vl-scopestack->topname ss))
       (reportcard (vl-extend-reportcard-list topname warnings reportcard)))
    reportcard))

;; (trace$ (vl-lucid-typo-detect
;;          :entry (list 'vl-lucid-typo-detect (alist-vals candidates)
;;                       :start-rc-len (len reportcard))
;;          :exit (list 'vl-lucid-typo-detect
;;                      :exit-rc-len (len value))))

(define vl-lucid-typo-detect ((candidates vl-typocandidates-p "Already cleaned so we can recur through them.")
                              (reportcard vl-reportcard-p     "So we can attach any real warnings."))
  :returns (reportcard vl-reportcard-p)
  :measure (len (vl-typocandidates-fix candidates))
  (b* ((candidates (vl-typocandidates-fix candidates))
       ((when (atom candidates))
        (vl-reportcard-fix reportcard))
       ((cons ss possible-typos) (car candidates))
       (reportcard (vl-lucid-typo-detect1 ss possible-typos reportcard)))
    (vl-lucid-typo-detect (cdr candidates) reportcard)))

(define vl-design-lucid ((x vl-design-p)
                         &key
                         ((modportsp booleanp) 't)
                         ((paramsp booleanp) 't)
                         ((generatesp booleanp) 't)
                         ((typosp booleanp) 't))
  :returns (new-x vl-design-p)
  (b* ((x  (cwtime (hons-copy (vl-design-fix x))
                   :name vl-design-lucid-hons
                   :mintime 1))
       (ss (vl-scopestack-init x))
       (st (cwtime (vl-lucidstate-init x
                                       :modportsp modportsp
                                       :paramsp paramsp
                                       :generatesp generatesp)))
       (st (cwtime (vl-design-lucidcheck-main x ss st)))
       ((mv reportcard typo-candidates) (cwtime (vl-lucid-dissect st)))

       (reportcard (b* (((unless typosp)
                         reportcard)
                        (typo-candidates (fast-alist-free (fast-alist-clean typo-candidates))))
                     (cwtime (vl-lucid-typo-detect typo-candidates reportcard)))))

    (clear-memoize-table 'vl-scopestack->flat-transitive-names-slow)
    (vl-scopestacks-free)

    ;; Just debugging
    ;;(vl-cw-ps-seq (vl-pp-lucidstate st))
    ;;(vl-cw-ps-seq (vl-print-reportcard reportcard :elide nil))

    (vl-apply-reportcard x reportcard)))
