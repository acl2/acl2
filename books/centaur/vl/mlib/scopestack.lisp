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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "blocks")
(include-book "find")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable acl2::consp-under-iff-when-true-listp)))

; Matt K.: Avoid ACL2(p) error (the job died after vl-maybe-scopeitem-p).
(set-waterfall-parallelism nil)

; Matt K. addition: Important for speed, given the change after v8-0 to keep
; LET expressions in right-hand sides of rewrite rules.
(add-default-hints '('(:do-not '(preprocess))) :at-end t)

(defxdoc scopestack
  :parents (mlib)
  :short "Scopestacks deal with namespaces in SystemVerilog by tracking the
bindings of names in scopes.  They provide a straightforward, correct way to
look up identifiers."

  :long "<h3>Namespaces in SystemVerilog</h3>

<p>SystemVerilog has a complicated system of namespaces, but it mostly boils
down to a few categories of names for things:</p>

<ul>

<li><b>items,</b> (our name), including nets/variables, parameters,
instances (of modules, gates, UDPs, and interfaces), typedefs, functions,
tasks, and named generate blocks;</li>

<li><b>definitions,</b> including module, UDP, interface, and program
declarations;</li>

<li><b>ports</b>;</li>

<li>and <b>packages</b>.</li>

</ul>

<p>The items are the most complicated.  Packages occur only at the global
scope.  Ports only occur in modules and interfaces.  In principle the
SystemVerilog spec allows for nested modules and interfaces, but most
implementations don't support this and neither do we, so definitions can only
occur at the global scope.  In contrast, to look for an item, we first look in
the most local scope; if it isn't found there, we search subsequent nested
scopes until we get to the global scope.</p>


<h3>Scopestacks</h3>

<p>A scopestack is a structure that holds representations of nested scopes.
Each scope may be one of several types, namely the types on the left-hand
column of the table @(see *vl-scopes->items*):</p>

@(`(:code (alist-keys *vl-scopes->items*))`)

<p>Whenever we search a scope, we call a @(see memoize)d function that turns
that scope representation into a fast alist, in which we look up the name.
That way, subsequent lookups in the same scope will be constant-time.  This
design means that you may occasionally need to free up memory associated with
scopestacks; see @(see vl-scopestacks-free).</p>


<h5>Construction and Maintenance</h5>

<ul>
<li>@('nil') is an empty scopestack (without even the global design scope).</li>

<li>@('(vl-scopestack-init design)') creates a scopestack with only the global
scope of the design visible.</li>

<li>@('(vl-scopestack-push scope ss)') pushes a new nested scope onto the
scopestack.  Typically you will need to call this function as you \"enter\" a
new scope, e.g., as your analysis or transformation descends into a particular
module, function, etc.</li>

<li>@('(vl-scopestack-pop ss)') removes the innermost scope from the
scopestack, but this is <b>rarely needed</b> because scopestacks are
applicative.</li>

<li>@('(vl-scopestacks-free)') clears the memoization tables associated with
scopestacks, which in CCL also will allow their associated fast-alists to be
garbage collected.  We don't currently have a mechanism free these fast alists
otherwise.</li>

</ul>


<h5>Accessing Items</h5>

<p>The interface for accessing items is more complex than for definitions and
packages because items may be found in multiple scopes.</p>

<ul>

<li>@('(vl-scopestack-find-item name ss)') searches the scopestack for the
given name (a string).  The declaration of the item is returned as a @(see
vl-scopeitem).  The more specific type of the declaration, e.g., @(see
vl-vardecl), @(see vl-modinst), etc., can be determined by examining its
tag.</li>

<li>@('(vl-scopestack-find-item/ss name ss)') returns @('(mv item new-ss)'),
where item is the same as returned by @('vl-scopestack-find-item') and
@('new-ss') is the scopestack visible from that item's declaration.  For
instance, if you are deep within a bunch of nested begin/end blocks, the
@('new-ss') you get back might be for some superior block, the whole module, or
the scopestack for some entirely different package where the @('item') is
declared..</li>

<li>@('(vl-scopestack-find-item/context name ss)') returns @('(mv item ctx-ss
package)').  Here @('item') is the same as above.  The @('ctx-ss') is similar
to the @('new-ss') above <b>but</b> packages are handled differently.  In
particular, @('ctx-ss') here is always the scopestack for some superior scope
where the item was found.  If @('item') is imported from a package, then
 <ul>
    <li>@('ctx-ss') refers to, e.g., the module where the item was imported into, whereas</li>
    <li>@('new-ss') refers to the package that the item was imported from</li>
 </ul>
The separate @('package') return value is a maybe-string that gives the name
of the package where the item was imported from, if applicable.</li>

</ul>


<h5>Accessing Non-Items</h5>

<ul>

<li>@('(vl-scopestack-find-definition name ss)') is similar to -find-item, but
finds a definition instead of an item.  The @('definition/ss') and
@('definition/context') versions also exist, but aren't as informative since
the definition can (currently) only exist at the global scope.</li>

<li>@('(vl-scopestack-find-package name ss)'), similar.</li>

<li>@('(vl-scope-find-portdecl-fast name scope)') is similar, but acts only on a
scope, not a stack of them, since searching beyond the local module for a port
doesn't make much sense.</li>

</ul>")


; Notes about scoping and generate statements.  BOZO NONE OF THIS IS IMPLEMENTED YET.
;
; You can basically ignore generate/endgenerate.  They don't introduce scopes
; or matter at all really.  SystemVerilog-2012, Section 27.3: "The keywords
; 'generate' and 'endgenerate' may be used to define a generate region.  A
; generate region is a textual span in the module description where generate
; constructs may appear.  Use of generate regions is optional.  There is no
; semantic difference in the module when a generate region is used..."
;
; Unnamed begin/end blocks DO NOT introduce scopes.  We try to get rid of them
; during make-implicit-wires (BOZO not yet implemented).
;
; A named "begin : foo .... end" style generate block DOES introduce a scope;
; wires declared inside it do not become visible to the rest of the module
; without hierarchical references.
;
; The conditional "if ... else ..." style generate construct DOES introduce new
; scopes for the separate branches.  Wires declared in these branches do not
; become visible to the rest of the module that follows the generate.  Except
; that there's allegedly a special case, see 27.5 (page 755), where if you nest
; if/else/if things inside of each other, then they don't count as extra scope
; levels.  This is actually apparently quite complicated.  See especially the
; comments after Example 1.
;
; The conditional "case ... " style generate construct DOES introduce new
; scopes for each separate branch.  Wires declared in these branches do not
; become visible to the rest of the module that follows the generate.
;
; A for-loop introduces several blocks, each of which has its own scope.
; Within each such scope, the genvar is to be defined as a parameter, but it
; only exists during elaboration and does not exist any more after elaboration.
; If the for loop's body has the form "begin : foo .... end", then you can
; refer into it with indexed hierarchical references, i.e., foo[0].wirename.




(defsection scopestack-constants
  :parents (scopestack)
  :short "Meta-information about the kinds of scopes and the kinds of elements
they can contain."

  :long "<p>These tables are used to generate most of the scopestack code.  The
format for each entry is:</p>

@({
     (scope-name  feature-list  element-list)
})

<p>The @('feature-list') is a list of keywords that are used in the templates.</p>

<p>The @('element-list') contains information about the items.  Its entries can
be as simple as field names, or can be lists of the form @('(name [keyword
options])'), where the options account for various kinds of departures from
convention.  Current keywords:</p>

<ul>

<li>@(':name foo') denotes that the accessor for the name of the item is
@('vl-itemtype->foo'), rather than the default @('vl-itemtype->name').</li>

<li>@(':acc foo') denotes that the accessor for the items within the scope is
@('vl-scopetype->foo'), rather than the default @('vl-scopetype->items').</li>

<li>@(':maybe-stringp t') denotes that the name accessor might return @('nil'),
rather than a string.</li>

<li>@(':sum-type t') denotes that the item actually encompasses two or more
item types.</li>

<li>@(':transsum t') denotes that the item is a transparent (tag-based) sum
type.</li>

</ul>"

  (local (xdoc::set-default-parents scopestack-constants))

  (defval *vl-scopes->pkgs*
    :short "Information about which scopes can contain packages."
    :long "<p>This is kind of silly because packages can only occur at the design
level.  If for some reason we ever wanted to allow packages to be nested in
other kinds of scopes (e.g., compilation units?) we could add them here.</p>"
    '((design       ()
                    package)))

  (defval *vl-scopes->items*
    :short "Information about the kinds of items in each scope."
    :long "<p>Note that this is only for items, i.e., it's not for definitions,
  ports, packages, etc.</p>"
    '((interface (:import)
                 ;; NOTE: if you add more things here, you also need to extend genblob!
                 paramdecl vardecl fundecl taskdecl typedef dpiimport
                 (modinst :name instname :maybe-stringp t)
                 ;; no gateinsts in interfaces
                 genvar
                 ;; BOZO our handling of genelements as scope items is probably
                 ;; not very sensible yet.  We *do* at least look up things like
                 ;; begin/end blocks and named loops, which is good.  But we should
                 ;; probably also support things like if/case statements whose blocks
                 ;; may be named.  But that's really hard -- how are we to collect
                 ;; those names?  And conflicts are OK, e.g.,
                 ;;    case (version) 1 : foo ... 2 : foo ... endcase
                 ;; is fine and has two sub generate blocks both named foo.  So
                 ;; what does it mean to look up one of these and how do we want
                 ;; to handle that?
                 (genelement :name blockname :maybe-stringp t :sum-type t :acc generates)
                 (interfaceport :acc ifports)
                 modport
                 ;; We don't include the dpi exports here because, unlike
                 ;; imports which are "defined" by the C code, exports are just
                 ;; things we're making available to the C code, which isn't
                 ;; relevant to much of anything else.
                 )
      (module (:import)
              ;; NOTE: if you add more things here, you also need to extend genblob!
              paramdecl vardecl fundecl taskdecl typedef dpiimport
              (modinst :name instname :maybe-stringp t)
              (gateinst :maybe-stringp t)
              genvar
              (genelement :name blockname :maybe-stringp t :sum-type t :acc generates)
              (interfaceport :acc ifports))
      (genblob (:import)
               vardecl paramdecl fundecl taskdecl typedef dpiimport
               (modinst :name instname :maybe-stringp t)
               (gateinst :maybe-stringp t)
               genvar
               (genelement :name blockname :maybe-stringp t :sum-type t :acc generates)
               (interfaceport :acc ifports)
               modport
               )

      ;; fwdtypedefs could be included here, but we hope to have resolved them all
      ;;             to proper typedefs by the end of loading, so we omit them.

      ;; Functions, Tasks, and Statements are all grouped together into Blockscopes.
      (blockscope   (:import)
                    vardecl paramdecl typedef)
      (design       (:import)
                    paramdecl vardecl fundecl taskdecl typedef dpiimport)
      (package      (:import)
                    paramdecl vardecl fundecl taskdecl typedef dpiimport)))

  (defval *vl-scopes->defs*
    :short "Information about the kinds of definitions in each scope."
    :long "<p>This is kind of silly because we currently only support definitions
at the top level.  However, if we ever want to allow, e.g., nested modules,
then we will need to extend this.</p>"
    '((design ()
              (module :acc mods) udp interface program
              (class :acc classes))))

  (defval *vl-scopes->portdecls*
    :parents (scopestack-constants)
    :short "Information about the kinds of scopes that have port declarations."
    :long "<p>BOZO do we want to add function/task ports here?</p>"
    '((interface () portdecl)
      (module    () portdecl)
      (genblob   () portdecl))))



(defprod vl-blockscope
  :short "Abstract representation of a scope that just has @(see vl-blockitem)s
in it, such as a function, task, or block statement."
  :parents (scopestack)
  :tag :vl-blockscope
  :layout :tree
  ((imports    vl-importlist-p    "Package imports in this scope.")
   (paramdecls vl-paramdecllist-p "Parameter declarations in this scope.")
   (vardecls   vl-vardecllist-p   "Variable declarations in this scope.")
   (typedefs   vl-typedeflist-p   "Type declarations in this scope.")
   (scopetype  vl-scopetype-p     "Kind of block responsible for this")

   (name  maybe-stringp :rule-classes :type-prescription
          "Just a debugging aide.  This lets us see the name of this scope when
           we want to print scopes, etc.")))

(define vl-fundecl->blockscope ((x vl-fundecl-p))
  ;; The One True Way to process a Function:
  ;;
  ;;  1. Process the return type (in the outer scope).
  ;;  2. Push the function onto the scopestack.
  ;;  3. Process the rest of the function (including the ports) in the inner scope.
  ;;
  ;; You might worry that this isn't correct in general, and you would be
  ;; right.  Consider something like:
  ;;
  ;;    typedef logic [1:0] mytype_t;
  ;;
  ;;    function foo (input mytype_t A);
  ;;      typedef logic [3:0] mytype_t;
  ;;      ...
  ;;    endfunction
  ;;
  ;; Here, the type of input A should be the [1:0] version of mytype_t from the
  ;; outer scope.  But according to the One True Way, we'll push the inner
  ;; scope before processing the ports, so we'd find the [3:0] version instead!
  ;;
  ;; But stop worrying.  Shadowcheck is responsible for making sure that this
  ;; can't happen.  If someone writes the above, then Shadowcheck will flag it
  ;; with a fatal warning saying that the scoping is too tricky for us to get
  ;; right.  So throughout the rest of VL, our official position is that the
  ;; ports are to be processed in the inner scope.  This allows us to support
  ;; reasonable functions like:
  ;;
  ;;     function bar;
  ;;       typedef logic mytype_t;
  ;;       input mytype_t a;
  ;;       ...
  ;;    endfunction
  :returns (scope vl-blockscope-p)
  :parents (vl-blockscope vl-scopestack-push)
  (b* (((vl-fundecl x)))
    (make-vl-blockscope :vardecls x.vardecls
                        :imports x.imports
                        :paramdecls x.paramdecls
                        :typedefs x.typedefs
                        :scopetype :vl-fundecl
                        :name  x.name)))

(define vl-taskdecl->blockscope ((x vl-taskdecl-p))
  ;; The One True Way to process a Task:
  ;;
  ;;   1. Push the task onto the scopestack.
  ;;   2. Process it.
  ;;
  ;; See the comments in vl-fundecl->blockscope.  Again, Shadowcheck is
  ;; responsible for rejecting any tasks whose scoping is so tricky that the
  ;; above is not correct.
  :returns (scope vl-blockscope-p)
  :parents (vl-blockscope vl-scopestack-push)
  (b* (((vl-taskdecl x)))
    (make-vl-blockscope :vardecls x.vardecls
                        :imports x.imports
                        :paramdecls x.paramdecls
                        :typedefs x.typedefs
                        :scopetype :vl-taskdecl
                        :name  x.name)))

(define vl-blockstmt->blockscope ((x vl-stmt-p))
  ;; The One True Way to process a Block Statement:
  ;;
  ;;   1. Push the block statement onto the scopestack.
  ;;   2. Process it.
  ;;
  ;; See the comments in vl-fundecl->blockscope for more information.
  :guard (vl-stmt-case x :vl-blockstmt)
  :returns (scope vl-blockscope-p)
  :parents (vl-blockscope vl-scopestack-push)
  (b* (((vl-blockstmt x)))
    (make-vl-blockscope :vardecls x.vardecls
                        :imports x.imports
                        :paramdecls x.paramdecls
                        :typedefs x.typedefs
                        :scopetype :vl-blockstmt
                        :name  x.name)))

(define vl-forstmt->blockscope ((x vl-stmt-p))
  ;; The One True Way to process a For Statement:
  ;;
  ;;   1. Push it onto the scopestack.
  ;;   2. Process it.
  ;;
  ;; Note that this means that something like this involves 2 scopes; an outer
  ;; scope for I and an inner scope for J.
  ;;
  ;;    for(int i = 0; i < 10; ++i)
  ;;      begin
  ;;       int j = i;
  ;;       ...
  ;;      end
  ;;
  ;; So we need to push a scope when we enter the for loop, and then later push
  ;; another scope when we enter the begin/end block.
  ;;
  ;; Note that VCS and NCVerilog agree that:
  ;;
  ;; for (int i=0; i<10; i++)
  ;;   begin
  ;;     int i = 15;
  ;;     $display("i: %d", i);
  ;;   end
  ;;
  ;; Should print i: 15 ten times.  That seems like it can only happen if there
  ;; are indeed two separate scopes in play here.
  :guard (vl-stmt-case x :vl-forstmt)
  :returns (scope vl-blockscope-p)
  :parents (vl-blockscope vl-scopestack-push)
  (b* (((vl-forstmt x)))
    (make-vl-blockscope :vardecls x.initdecls
                        :scopetype :vl-forstmt)))

(define vl-foreachstmt->blockscope ((x vl-stmt-p))
  :guard (vl-stmt-case x :vl-foreachstmt)
  :returns (scope vl-blockscope-p)
  :parents (vl-blockscope vl-scopestack-push)
  (b* (((vl-foreachstmt x)))
    (make-vl-blockscope :vardecls x.vardecls
                        :scopetype :vl-foreachstmt)))


;; Notes on name spaces -- from SV spec 3.13
;; SV spec lists 8 namespaces:

;; a) Definitions name space:
;;      module
;;      primitive
;;      program
;;      interface
;; declarations outside all other declarations
;; (meaning: not in a package? as well as not nested.
;; Global across compilation units.

;; b) Package name space: all package IDs.  Global across compilation units.

;; c) Compilation-unit scope name space:
;;     functions
;;     tasks
;;     checkers
;;     parameters
;;     named events
;;     netdecls
;;     vardecls
;;     typedefs
;;  defined outside any other containing scope.  Local to compilation-unit
;;  scope (as the name suggests).

;; d) Text macro namespace: local to compilation unit, global within it.
;;    This works completely differently from the others; we'll ignore it here
;;    since we take care of them in the preprocessor.

;; e) Module name space:
;;     modules
;;     interfaces
;;     programs
;;     checkers
;;     functions
;;     tasks
;;     named blocks
;;     instance names
;;     parameters
;;     named events
;;     netdecls
;;     vardecls
;;     typedefs
;;  defined within the scope of a particular
;;     module
;;     interface
;;     package
;;     program
;;     checker
;;     primitive.

;; f) Block namespace:
;;     named blocks
;;     functions
;;     tasks
;;     parameters
;;     named events
;;     vardecl (? "variable type of declaration")
;;     typedefs
;;  within
;;     blocks (named or unnamed)
;;     specifys
;;     functions
;;     tasks.

;; g) Port namespace:  ports within
;;     modules
;;     interfaces
;;     primitives
;;     programs

;; h) Attribute namespace, also separate.

;; Notes on scope rules, from SV spec 23.9.

;; Elements that define new scopes:
;;       Modules
;;       Interfaces
;;       Programs
;;       Checkers
;;       Packages
;;       Classes
;;       Tasks
;;       Functions
;;       begin-end blocks (named or unnamed)
;;       fork-join blocks (named or unnamed)
;;       Generate blocks

;; An identifier shall be used to declare only one item within a scope.
;; However, perhaps this doesn't apply to global/compilation-unit scope, since
;; ncverilog and vcs both allow, e.g., a module and a wire of the same name
;; declared at the top level of a file.  We can't check this inside a module
;; since neither allows nested modules, and modules aren't allowed inside
;; packages.

;; This is supposed to be true of generate blocks even if they're not
;; instantiated; as an exception, different (mutually-exclusive) blocks of a
;; conditional generate can use the same name.

;; Search for identifiers referenced (without hierarchical path) within a task,
;; function, named block, generate block -- work outward to the
;; module/interface/program/checker boundary.  Search for a variable stops at
;; this boundary; search for a task, function, named block, or generate block
;; continues to higher levels of the module(/task/function/etc) hierarchy
;; (not the lexical hierarchy!).

;; Hierarchical names

(local
 (defsection-progn template-substitution-helpers

   (defun scopes->typeinfos (scopes)
     (declare (xargs :mode :program))
     (if (atom scopes)
         nil
       (union-equal (cddar scopes)
                    (scopes->typeinfos (cdr scopes)))))

   (defun typeinfos->tmplsubsts (typeinfos)
     ;; returns a list of conses (features . strsubst-alist)
     (declare (xargs :mode :program))
     (if (atom typeinfos)
         nil
       (cons (b* ((kwds (and (consp (car typeinfos)) (cdar typeinfos)))
                  (type (if (consp (car typeinfos)) (caar typeinfos) (car typeinfos)))
                  (acc (let ((look (cadr (assoc-keyword :acc kwds))))
                         (if look
                             (symbol-name look)
                           (cat (symbol-name type) "S"))))
                  (name (let ((look (cadr (assoc-keyword :name kwds))))
                          (if look (symbol-name look) "NAME")))
                  (maybe-stringp (cadr (assoc-keyword :maybe-stringp kwds)))
                  (sum-type      (cadr (assoc-keyword :sum-type      kwds)))
                  (transsum      (cadr (assoc-keyword :transsum      kwds))))
               (make-tmplsubst :features (append (and maybe-stringp '(:maybe-stringp))
                                                 (and sum-type      '(:sum-type))
                                                 (and transsum      '(:transsum)))
                               :strs
                               `(("__TYPE__" ,(symbol-name type) . vl-package)
                                 ("__ACC__" ,acc . vl-package)
                                 ("__NAME__" ,name . vl-package))))
             (typeinfos->tmplsubsts (cdr typeinfos)))))

   (defun scopes->tmplsubsts (scopes)
     (declare (xargs :mode :program))
     (if (atom scopes)
         nil
       (cons (make-tmplsubst :strs `(("__TYPE__" ,(symbol-name (caar scopes)) . vl-package))
                             :atoms `((__items__ . ,(cddar scopes)))
                             :features (append (cadar scopes)
                                               (and (cddar scopes) '(:has-items))))
             (scopes->tmplsubsts (cdr scopes)))))))

(defsection scope-items

  (local (xdoc::set-default-parents vl-scopeitem))

  (make-event ;; Definition of vl-scopeitem type
   (let ((substs (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->items*))))
     `(progn

        (deftranssum vl-scopeitem
          :parents (scopestack)
          :short "Recognizer for Verilog structures that can occur as scope
                  <b>items</b>."

          :long "<p>See @(see scopestack).  The items are only a subset of
                 Verilog declarations like parameter declarations, module
                 instances, etc., i.e., the kinds of things that can be found
                 by @(see vl-scopestack-find-item).  It does not, e.g., for
                 definitions, packages, etc.</p>"

          ,(template-append '((:@ (not :transsum) vl-__type__)) substs)
          ///
          ,@(template-append '((:@ :transsum
                                (defthm vl-scopeitem-p-when-vl-__type__-p
                                  (implies (vl-__type__-p x)
                                           (vl-scopeitem-p x))
                                  :hints(("Goal" :in-theory (enable vl-__type__-p))))))
                             substs))

        (fty::deflist vl-scopeitemlist
          :elt-type vl-scopeitem-p
          :elementp-of-nil nil
          ///
          . ,(template-proj
              '(defthm vl-scopeitemlist-p-when-vl-__type__list-p
                 (implies (vl-__type__list-p x)
                          (vl-scopeitemlist-p x))
                 :hints (("goal" :induct (vl-scopeitemlist-p x)
                          :expand ((vl-__type__list-p x)
                                   (vl-scopeitemlist-p x))
                          :in-theory (enable (:i vl-scopeitemlist-p)))))
              substs)))))

  (fty::defalist vl-scopeitem-alist
    :parents (vl-scopeitem)
    :key-type stringp
    :val-type vl-scopeitem-p
    :count vl-scopeitem-alist-count)

  (defoption vl-maybe-scopeitem vl-scopeitem-p))


(defsection import-results

  ;; BOZO seems too specific to go into top-level docs
  (local (xdoc::set-default-parents scopestack))

  (defprod vl-importresult
    :tag :vl-importresult
    :layout :tree
    :short "Information about an item that was imported from another package."
    ((item     vl-maybe-scopeitem-p
               "The item we imported, if any.")
     (pkg-name stringp
               :rule-classes :type-prescription
               "The package we imported it from.")
     (loc      vl-location-p
               "Location of the import statement.  Useful for name clash
                reporting.")))

  (fty::defalist vl-importresult-alist
    :key-type stringp
    :val-type vl-importresult))


(defsection scope-definitions

  (local (xdoc::set-default-parents vl-scopedef))

  (make-event ;; Definition of vl-scopedef type
   (let ((substs (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->defs*))))
     `(progn
        (deftranssum vl-scopedef
          :parents (scopestack)
          :short "Recognizer for Verilog structures that can occur as scope
                  <b>definitions</b>."
          :long "<p>See @(see scopestack).  These are for global definitions like
                 modules, user-defined primitives, etc.</p>"

          ,(template-proj 'vl-__type__ substs))

        (fty::deflist vl-scopedeflist
          :elt-type vl-scopedef-p
          :elementp-of-nil nil
          ///
          . ,(template-proj
              '(defthm vl-scopedeflist-p-when-vl-__type__list-p
                 (implies (vl-__type__list-p x)
                          (vl-scopedeflist-p x))
                 :hints (("goal" :induct (vl-scopedeflist-p x)
                          :expand ((vl-__type__list-p x)
                                   (vl-scopedeflist-p x))
                          :in-theory (enable (:i vl-scopedeflist-p)))))
              substs)))))

  (fty::defalist vl-scopedef-alist
    :key-type stringp
    :val-type vl-scopedef-p))

(local (xdoc::set-default-parents scopestack))

(local ;; For each searchable type foo, we get:
 ;;                  - vl-find-foo: linear search by name in a list of foos
 ;;                  - vl-foolist-alist: fast alist binding names to foos.
 (defconst *scopeitem-alist/finder-template*
   '(progn
      (defthm vl-__scopetype__-alist-p-of-vl-__type__list-alist
        (equal (vl-__scopetype__-alist-p (vl-__type__list-alist x acc))
               (vl-__scopetype__-alist-p acc))
        :hints(("Goal" :in-theory (enable vl-__type__list-alist
                                          vl-__scopetype__-alist-p)))))))

(make-event ;; Definition of scopeitem alists/finders
 (b* ((itemsubsts (acl2::tmplsubsts-add-strsubsts
                   (acl2::tmplsubsts-add-features
                    (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->items*))
                    '(:scopetype))
                   `(("__SCOPETYPE__" "SCOPEITEM" . vl-package))))
      (defsubsts (acl2::tmplsubsts-add-strsubsts
                  (acl2::tmplsubsts-add-features
                   (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->defs*))
                   '(:scopetype))
                  `(("__SCOPETYPE__" "SCOPEDEF" . vl-package))))
      ;(pkgsubsts (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->pkgs*)))
      ;(portsubsts (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->portdecls*)))
      (events (template-proj *scopeitem-alist/finder-template*
                             (append itemsubsts defsubsts
                                     ;;pkgsubsts portsubsts
                                     ))))
   `(progn . ,events)))



;; ;; Now we define:
;; ;; - how to look up a package name in the global design
;; ;; - how to look up a scopeitem in a package, not considering its imports
;; ;; - how to look up a name in a list of import statements.
;; ;; These don't involve the scopestack yet: in each case we know in which scope
;; ;; to find the item.  This works and doesn't need some gross recursive
;; ;; implementation because the following isn't allowed:
;; ;; package bar;
;; ;;   parameter barparam = 13032;
;; ;; endpackage
;; ;; package foo;
;; ;;   import bar::barparam;
;; ;; endpackage
;; ;; module baz ();
;; ;;   import foo::barparam; // fail -- barparam isn't exported by foo.
;; ;; endmodule

;; ;; We then use the above functions to define other scopestack functions resolve
;; ;; imports.


;; (define vl-design->package-alist ((x vl-design-p))
;;   :enabled t
;;   (vl-packagelist-alist (vl-design->packages x) nil)
;;   ///
;;   (memoize 'vl-design->package-alist))

;; (define vl-design-find-package ((name stringp) (x vl-design-p))
;;   :returns (res (iff (vl-package-p res) res))
;;   (mbe :logic (vl-find-package (string-fix name) (vl-design->packages x))
;;        :exec (cdr (hons-get (string-fix name) (vl-design->package-alist x)))))




(local
 (defun def-scopetype-find (scope importp itemtypes resultname resulttype scopeitemtype)
   (declare (xargs :mode :program))
   (b* ((substs (typeinfos->tmplsubsts itemtypes))
        ((unless itemtypes) '(value-triple nil))
        (template
          `(progn
             (define vl-__scope__-scope-find-__result__
               :ignore-ok t
               :parents (scopestack)
               ((name  stringp)
                (scope vl-__scope__-p))
               :returns (item    (iff (__resulttype__ item) item))
               (b* (((vl-__scope__ scope))
                    (?name (string-fix name)))
                 (or . ,(template-proj
                                  '(vl-find-__type__ name scope.__acc__)
                                  substs))))

             (define vl-__scope__-scope-__result__-alist
               :parents (vl-__scope__-scope-find-__result__)
               :ignore-ok t
               ((scope vl-__scope__-p)
                acc)
               :returns (alist (:@ :scopeitemtype
                                (implies (vl-__scopeitemtype__-alist-p acc)
                                         (vl-__scopeitemtype__-alist-p alist))
                                :hints(("Goal" :in-theory (enable vl-__scopeitemtype__-alist-p)))))
               (b* (((vl-__scope__ scope))
                    . ,(reverse
                        (template-proj
                         '(acc (vl-__type__list-alist scope.__acc__ acc))
                         substs)))
                 acc)
               ///
               (local (in-theory (enable vl-__scope__-scope-find-__result__)))
               (defthm vl-__scope__-scope-__result__-alist-lookup-acc-elim
                 (implies (syntaxp (not (equal acc ''nil)))
                          (equal (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope acc))
                                 (or (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))
                                     (hons-assoc-equal name acc)))))
               (defthm vl-__scope__-scope-__result__-alist-correct
                 (implies (stringp name)
                          (equal (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))
                                 (b* ((item (vl-__scope__-scope-find-__result__ name scope)))
                                   (and item
                                        (cons name item))))))
               ;; (defthmd vl-__scope__-scope-__result__-alist-correct2
               ;;   (implies (stringp name)
               ;;            (equal (vl-__scope__-scope-find-__result__ name scope)
               ;;                   (let ((look (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))))
               ;;                     (mv (consp look) (cdr look))))))
               ))))
     (template-subst-top template
                               (make-tmplsubst
                                :features
                                (append (and importp '(:import))
                                        (and scopeitemtype '(:scopeitemtype)))
                                :strs
                                `(("__SCOPE__" ,(symbol-name scope) . vl-package)
                                  ("__RESULT__" ,(symbol-name resultname) . vl-package)
                                  ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package)
                                  ("__SCOPEITEMTYPE__" ,(symbol-name scopeitemtype) . vl-package))
                                :pkg-sym 'vl-package)))))


(make-event ;; Definition of vl-design-scope-find-package vl-design-scope-package-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->pkgs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find
                   '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'package 'vl-package-p 'package))
               substs))))


(make-event ;; Definitions of e.g. vl-module-scope-find-item and vl-module-scope-item-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->items*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'item 'vl-scopeitem-p 'scopeitem))
               substs))))

(make-event ;; Definitions of e.g. vl-design-scope-find-definition and vl-design-scope-definition-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->defs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'definition 'vl-scopedef-p 'scopedef))
               substs))))


(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->portdecls*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'portdecl 'vl-portdecl-p 'portdecl))
               substs))))


(define vl-package-scope-item-alist-aux ((x vl-package-p))
  :parents (vl-package-scope-item-alist-top)
  :short "Memoized version."
  :enabled t
  (make-fast-alist (vl-package-scope-item-alist x nil))
  ///
  (memoize 'vl-package-scope-item-alist-aux))

(define vl-package-scope-item-alist-top ((x vl-package-p))
  :enabled t
  :long "<p>The @('-aux') function is memoized.  In a single-threaded context,
there would be no need to call @(see make-fast-alist) again.  But for
multi-threaded code, e.g., the @(see vl-server), the alist may only be fast in
some threads.  Calling @('make-fast-alist') again corrects for this and should
be very cheap in the single-threaded case.</p>"
  (mbe :logic (vl-package-scope-item-alist x nil)
       :exec (make-fast-alist (vl-package-scope-item-alist-aux x))))



(define vl-design-scope-package-alist-aux ((x vl-design-p))
  :parents (vl-design-scope-package-alist-top)
  :short "Memoized version."
  :enabled t
  (make-fast-alist (vl-design-scope-package-alist x nil))
  ///
  (memoize 'vl-design-scope-package-alist-aux))

(define vl-design-scope-package-alist-top ((x vl-design-p))
  :enabled t
  (mbe :logic (vl-design-scope-package-alist x nil)
       :exec (make-fast-alist (vl-design-scope-package-alist-aux x))))



(defprod vl-scopeinfo
  ((locals  vl-scopeitem-alist-p "Locally defined names bound to their declarations")
   (imports vl-importresult-alist-p
            "Explicitly imported names bound to import result, i.e. package-name and declaration)")
   (star-packages string-listp "Names of packages imported with *")
   (id            vl-maybe-scopeid)
   (scopetype vl-scopetype-p :default ':vl-anonymous-scope))
  :layout :tree
  :tag :vl-scopeinfo)

(make-event ;; Definition of vl-scope type
 (let ((subst (scopes->tmplsubsts *vl-scopes->items*)))
   `(progn
      (deftranssum vl-scope
        :short "Recognizer for a syntactic element that can have named elements within it."
        (,@(template-proj 'vl-__type__ subst)
         ;; [Jared] allowing scopeinfos to be scopes is a little weird, but see
         ;; for instance transforms/unparam/top for a place where this is useful.
         vl-scopeinfo))

      (defthm vl-scope-p-tag-forward
        ;; BOZO is this better than the rewrite rule we currently add?
        (implies (vl-scope-p x)
                 (or ,@(template-proj '(equal (tag x) :vl-__type__) subst)
                     (equal (tag x) :vl-scopeinfo)))
        :rule-classes :forward-chaining))))

; Matt K. addition: Undo the added add-default-hints above to avoid failure in
; next event.
(remove-default-hints '('(:do-not '(preprocess))))

(define vl-scope->scopetype ((x vl-scope-p))
  :returns (type vl-scopetype-p
                 :hints(("Goal" :in-theory (enable vl-scopetype-p))))
  :prepwork ((local (defthm vl-scope-fix-forward
                      (vl-scope-p (vl-scope-fix x))
                      :rule-classes
                      ((:forward-chaining :trigger-terms ((vl-scope-fix x)))))))
  (b* ((x (vl-scope-fix x))
       (tag (tag x)))
    (case tag
      (:vl-genblob (vl-genblob->scopetype x))
      (:vl-blockscope (vl-blockscope->scopetype x))
      (:vl-scopeinfo (vl-scopeinfo->scopetype x))
      (otherwise
       ;; (:vl-interface :vl-module :vl-design :vl-package
       tag))))

(define vl-scope->id ((x vl-scope-p))
  :returns (name vl-maybe-scopeid-p :rule-classes :type-prescription)
  (b* ((x (vl-scope-fix x)))
    (case (tag x)
      (:vl-interface  (vl-interface->name x))
      (:vl-module     (vl-module->name x))
      (:vl-genblob    (vl-genblob->id x))
      (:vl-blockscope (vl-blockscope->name x))
      (:vl-package    (vl-package->name x))
      (:vl-scopeinfo  (vl-scopeinfo->id x))
      ;; bozo does this make sense?
      (:vl-design     "Design Root")
      ;; Don't know a name for a scopeinfo
      (otherwise      (impossible)))))




(define vl-scopeinfo-make-fast ((x vl-scopeinfo-p))
  :parents (vl-scopeinfo-p)
  :short "Ensure that the fast alists in a @(see vl-scopeinfo) are indeed fast alists."
  :enabled t
  :hooks nil
  (mbe :logic x
       :exec (b* (((vl-scopeinfo x)))
               (change-vl-scopeinfo x
                                    :locals (make-fast-alist x.locals)
                                    :imports (make-fast-alist x.imports)))))


;; (make-event ;; Definition of vl-package-scope-find-nonimported-item
;;  (b* ((substs (scopes->tmplsubsts (list (assoc 'package *vl-scopes->items*)))))
;;    `(progn . ,(template-proj
;;                '(make-event
;;                  (def-scopetype-find '__type__ nil
;;                    '__items__ 'nonimported-item 'vl-scopeitem-p))
;;                substs))))



;; Now, we want a function for looking up imported names.  This must first look
;; for the name explicitly imported, then implicitly.

;; What do we do when we find an import of a name from a package that doesn't
;; contain that name?  This should be an error, but practially speaking I think
;; we want to check for these in one place and not disrupt other code with
;; error handling.  So in this case we just don't find the item.
(define vl-importlist-find-explicit-item ((name stringp)
                                          (x vl-importlist-p)
                                          (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package)
                        :hints nil)
               (item (iff (vl-scopeitem-p item) item)
                     :hints nil)
               (loc "Location of the actual import statement."
                    (iff (vl-location-p loc) loc)
                    :hints nil))
  (b* (((when (atom x)) (mv nil nil nil))
       ((vl-import x1) (car x))
       ((when (and (stringp x1.part)
                   (equal x1.part (string-fix name))))
        ;; if we don't have a design, I think we still want to say we found the
        ;; item, just not what it is.
        (b* ((package (and design (vl-design-scope-find-package x1.pkg design))))
          ;; regardless of whether the package exists or has the item, return found
          (mv x1.pkg (and package (vl-package-scope-find-item name package)) x1.loc))))
    (vl-importlist-find-explicit-item name (cdr x) design))
  ///
  (more-returns
   (package :name maybe-string-type-of-vl-importlist-find-explicit-item-package
            (or (stringp package) (not package))
            :rule-classes :type-prescription))

  (more-returns
   (package :name package-when-item-of-vl-importlist-find-explicit-item-package
            (implies item package)))

  (more-returns
   (loc :name loc-when-item-of-vl-importlist-find-explicit-item-package
        (implies package loc))))




;; (local
;;  (defthm equal-of-vl-importlist-find-explicit-item
;;    (equal (equal (vl-importlist-find-explicit-item name scope design) x)
;;           (and (consp x)
;;                (consp (cdr x))
;;                (not (cddr x))
;;                (equal (mv-nth 0 (vl-importlist-find-explicit-item name scope design))
;;                       (mv-nth 0 x))
;;                (equal (mv-nth 1 (vl-importlist-find-explicit-item name scope design))
;;                       (mv-nth 1 x))))
;;    :hints(("Goal" :in-theory (enable mv-nth-expand-to-conses
;;                                      equal-of-cons
;;                                      vl-importlist-find-explicit-item)))))

(define vl-importlist->explicit-item-alist ((x      vl-importlist-p)
                                            (design vl-maybe-design-p)
                                            acc)
  :returns (alist (implies (vl-importresult-alist-p acc)
                           (vl-importresult-alist-p alist)))
  (b* (((when (atom x)) acc)
       ((vl-import x1) (car x))
       ((unless (stringp x1.part))
        (vl-importlist->explicit-item-alist (cdr x) design acc))
        ;; if we don't have a design, it seems like returning the package but
        ;; not the item is the best way to go here, since we might have
        ;; imported the name from the package but can't find out.
       (package (and design (cdr (hons-get x1.pkg (vl-design-scope-package-alist-top design)))))
       (item    (and package (cdr (hons-get x1.part (vl-package-scope-item-alist-top package))))))
    (hons-acons x1.part (make-vl-importresult :item item
                                              :pkg-name x1.pkg
                                              :loc x1.loc)
                (vl-importlist->explicit-item-alist (cdr x) design acc)))
  ///
  (defthm vl-importlist->explicit-item-alist-lookup-acc-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (equal (hons-assoc-equal name (vl-importlist->explicit-item-alist x design acc))
                    (or (hons-assoc-equal name (vl-importlist->explicit-item-alist x design nil))
                        (hons-assoc-equal name acc)))))
  (defthm vl-importlist->explicit-item-alist-correct
    (implies (stringp name)
             (equal (hons-assoc-equal name (vl-importlist->explicit-item-alist x design nil))
                    (b* (((mv pkg item loc) (vl-importlist-find-explicit-item name x design)))
                      (and pkg
                           (cons name (make-vl-importresult :item item
                                                            :pkg-name pkg
                                                            :loc loc))))))
    :hints(("Goal" :in-theory (enable vl-importlist-find-explicit-item)))))

(define vl-importlist-find-implicit-item ((name stringp) (x vl-importlist-p) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-import x1) (car x))
       ((unless (eq x1.part :vl-import*))
        (vl-importlist-find-implicit-item name (cdr x) design))
       (package (and design (vl-design-scope-find-package x1.pkg design)))
       ((unless package) (mv x1.pkg nil))
       (item (vl-package-scope-find-item (string-fix name) package)))
    (if item
        (mv x1.pkg item)
      (vl-importlist-find-implicit-item name (cdr x) design)))
  ///
  (more-returns
   (package :name maybe-string-type-of-vl-importlist-find-implicit-item-package
          (or (stringp package) (not package))
          :rule-classes :type-prescription)))


(define vl-importlist->star-packages ((x vl-importlist-p))
  :returns (packages string-listp)
  (b* (((when (atom x)) nil)
       ((vl-import x1) (car x)))
    (if (eq x1.part :vl-import*)
        (cons x1.pkg (vl-importlist->star-packages (cdr x)))
      (vl-importlist->star-packages (cdr x)))))


(define vl-import-stars-find-item ((name stringp) (packages string-listp) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  :verbosep t
  (b* (((when (atom packages)) (mv nil nil))
       (pkg (string-fix (car packages)))
       (package (and design (cdr (hons-get pkg (vl-design-scope-package-alist-top design)))))
       ((unless package) (mv pkg nil))
       (item (cdr (hons-get (string-fix name)
                            (vl-package-scope-item-alist-top package))))
       ((when item) (mv pkg item)))
    (vl-import-stars-find-item name (cdr packages) design))
  ///
  (defthm vl-import-stars-find-item-correct
    (equal (vl-import-stars-find-item name (vl-importlist->star-packages x) design)
           (vl-importlist-find-implicit-item name x design))
    :hints(("Goal" :in-theory (enable vl-importlist-find-implicit-item
                                      vl-importlist->star-packages)))))


(local (defthm alist-keys-of-vl-scopeitem-alist
         (implies (vl-scopeitem-alist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable vl-scopeitem-alist-p
                                           alist-keys)))))

(local (defthm alist-keys-of-vl-importresult-alist
         (implies (vl-importresult-alist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable vl-importresult-alist-p
                                           alist-keys)))))

(local (defthm alist-keys-of-vl-scopedef-alist
         (implies (vl-scopedef-alist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable vl-scopedef-alist-p
                                           alist-keys)))))

(local (defthm alist-keys-of-vl-package-alist
         (implies (vl-package-alist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable vl-package-alist-p
                                           alist-keys)))))

(local (defthm alist-keys-of-vl-portdecl-alist
         (implies (vl-portdecl-alist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable vl-portdecl-alist-p
                                           alist-keys)))))

(local (defthm string-listp-of-append
         (implies (and (string-listp a)
                       (string-listp b))
                  (string-listp (append a b)))))



(local (defthm cdr-of-lookup-in-scopeitem-alist
         (implies (vl-scopeitem-alist-p x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable vl-scopeitem-alist-p)))))

(local (defthm cdr-of-lookup-in-importresult-alist
         (implies (vl-importresult-alist-p x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable vl-importresult-alist-p)))))

(define vl-import-stars-itemnames ((packages string-listp)
                                   (design vl-maybe-design-p))
  :returns (names string-listp)
  (b* (((when (atom packages)) nil)
       (pkg (string-fix (Car packages)))
       (package (and design (cdr (hons-get pkg (vl-design-scope-package-alist-top design)))))
       ((unless package) nil))
    (append (alist-keys (vl-package-scope-item-alist-top package))
            (vl-import-stars-itemnames (cdr packages) design)))

  :prepwork
  ((local (defthm lookup-of-non-string-in-scopeitem-alist
            (implies (and (not (stringp name))
                          (string-listp (alist-keys x)))
                     (not (hons-assoc-equal name x)))
            :hints(("Goal" :in-theory (enable alist-keys))))))

  ///

  (local (defthm stringp-when-member
           (implies (member name (vl-import-stars-itemnames packages design))
                    (stringp name))
           :hints (("goal" :use ((:instance string-listp-of-vl-import-stars-itemnames))))
           :rule-classes :forward-chaining))

  (defthm vl-import-stars-itemname-present-when-lookup
    (iff (member name (vl-import-stars-itemnames packages design))
         (and (stringp name)
              (mv-nth 1 (vl-import-stars-find-item name packages design))))
    :hints(("Goal" :in-theory (e/d (vl-import-stars-find-item)
                                   (vl-package-scope-item-alist-correct))))))







(define vl-scopeinfo-find-item ((name stringp) (x vl-scopeinfo-p) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  (b* (((vl-scopeinfo x))
       (name (string-fix name))
       (local-item (cdr (hons-get name x.locals)))
       ((when local-item) (mv nil local-item))
       (import-item (cdr (hons-get name x.imports)))
       ((when import-item) (mv (vl-importresult->pkg-name import-item)
                               (vl-importresult->item import-item))))
    (vl-import-stars-find-item name x.star-packages design)))


(define vl-scopeinfo->itemnames ((x vl-scopeinfo-p) (design vl-maybe-design-p))
  :returns (names string-listp)
  (b* (((vl-scopeinfo x)))
    (append (alist-keys x.locals)
            (alist-keys x.imports)
            (vl-import-stars-itemnames x.star-packages design)))
  ///

  (defthm vl-scopeinfo->itemnames-present-when-lookup
    (implies (and (mv-nth 1 (vl-scopeinfo-find-item name x design))
                  (stringp name))
             (member name (vl-scopeinfo->itemnames x design)))
    :hints(("Goal" :in-theory (enable vl-scopeinfo-find-item)))))










;; (fty::deflist vl-scopelist :elt-type vl-scope :elementp-of-nil nil)

(local (defthm type-of-vl-scope-fix
         (consp (vl-scope-fix x))
         :hints (("goal" :use ((:instance consp-when-vl-scope-p
                                (x (vl-scope-fix x))))
                  :in-theory (disable consp-when-vl-scope-p)))
         :rule-classes :type-prescription))


(fty::defflexsum vl-scopestack
  (:null :cond (atom x)
   :shape (eq x nil)
   :ctor-body nil)
  (:global :cond (eq (car x) :global)
   :fields ((design :type vl-design-p :acc-body (Cdr x)))
   :ctor-body (cons :global design))
  (:local :cond t
   :fields ((top :type vl-scope-p :acc-body (car x))
            (super :type vl-scopestack-p :acc-body (cdr x)))
   :ctor-body (cons top super)))

(define vl-scopestack->design ((x vl-scopestack-p))
  :returns (design (iff (vl-design-p design) design))
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null nil
    :global x.design
    :local (vl-scopestack->design x.super))
  ///
  (more-returns
   (design :name vl-maybe-design-p-of-vl-scopestack->design
           (vl-maybe-design-p design))))

(define vl-scopestack->toplevel ((x vl-scopestack-p))
  :returns (top vl-scopestack-p)
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :local (vl-scopestack->toplevel x.super)
    :otherwise (vl-scopestack-fix x)))

(define vl-scopestack-push ((scope vl-scope-p) (x vl-scopestack-p))
  ;; The One True Way to process a Module.
  ;;
  ;;   1. Push the module onto the scopestack.
  ;;   2. Process it.
  ;;
  ;; That is, you should NOT try to process anything (e.g., the ports or
  ;; parameters) outside of the module's scope.
  ;;
  ;; This may seem wrong to you, but see the comments in vl-fundecl->blockscope
  ;; and note that Shadowcheck is responsible for making sure that any module
  ;; for which this wouldn't work correctly gets flagged with fatal warnings
  ;; that say the scoping is too tricky.
  :returns (x1 vl-scopestack-p)
  (progn$
   ;; [Jared] I'm curious about whether we ever do this.  If so it might screw
   ;; up some of the stuff in Lucid.
   (or (not (eq (tag scope) :vl-design))
       (cw "Note: pushing whole design onto scopestack.~%"))
   (make-vl-scopestack-local :top scope :super x)))

(define vl-scopestack-pop ((x vl-scopestack-p))
  :returns (super vl-scopestack-p)
  (vl-scopestack-case x
    :local x.super
    :otherwise (vl-scopestack-fix x)))

(define vl-scopestack-init
  :short "Create an initial scope stack for an entire design."
  ((design vl-design-p))
  :returns (ss vl-scopestack-p)
  (make-vl-scopestack-global :design design))


(define vl-scopestack-nesting-level ((x vl-scopestack-p))
  :returns (level natp)
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null 0
    :global 1
    :local (+ 1 (vl-scopestack-nesting-level x.super))))


(local (defthm vl-maybe-design-p-when-iff
         (implies (iff (vl-design-p x) x)
                  (vl-maybe-design-p x))))


(local
 (defun def-vl-scope-find-item (table result resulttype stackp importsp)
   (declare (xargs :mode :program))
   (b* ((substs (scopes->tmplsubsts table))
        (template
          `(progn
             (define vl-scope-find-item
               :short "Look up a plain identifier to find an item in a scope."
               ((name  stringp)
                (scope vl-scope-p)
                (design vl-maybe-design-p))
               :returns (mv (pkg-name    (iff (stringp pkg-name) pkg-name)
                                         "The name of the package where the item was found, if applicable.")
                            (item  (iff (vl-scopeitem-p item) item)
                                   "The declaration object for the given name, if found."))
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (:@ (not :import)
                           (mv nil (vl-__type__-scope-find-__result__ name scope)))
                          (:@ :import
                           (b* (((vl-__type__ scope :quietp t))
                                (item (vl-__type__-scope-find-__result__ name scope))
                                ((when item) (mv nil item))
                                ((mv pkg item ?loc)
                                 (vl-importlist-find-explicit-item name scope.imports design))
                                ((when (or pkg item)) (mv pkg item)))
                             (vl-importlist-find-implicit-item name scope.imports design))))))
                      substs)
                   (:vl-scopeinfo
                    (vl-scopeinfo-find-item name scope design))
                   (otherwise (mv nil nil))))
               ///
               (more-returns
                (pkg-name :name maybe-string-type-of-vl-scope-find-item-pkg-name
                          (or (stringp pkg-name) (not pkg-name))
                          :rule-classes :type-prescription)))


             (define vl-scope->scopeinfo-aux
               :parents (vl-scope->scopeinfo)
               :short "Memoized version."
               ((scope  vl-scope-p)
                (design vl-maybe-design-p))
               :returns (scopeinfo vl-scopeinfo-p)
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (b* (((vl-__type__ scope :quietp t)))
                            (make-vl-scopeinfo
                             :scopetype (vl-scope->scopetype scope)
                             :id (vl-scope->id scope)
                             :locals (make-fast-alist
                                      (vl-__type__-scope-__result__-alist scope nil))
                             (:@ :import
                              :imports (make-fast-alist
                                        (vl-importlist->explicit-item-alist scope.imports design nil))
                              :star-packages (vl-importlist->star-packages scope.imports)))))))
                      substs)
                   (:vl-scopeinfo (vl-scopeinfo-fix scope))
                   (otherwise (make-vl-scopeinfo))))
               ///
               (local (in-theory (enable vl-scope-find-item
                                         vl-scopeinfo-find-item)))
               (defthm vl-scope->scopeinfo-aux-correct
                 (implies (stringp name)
                          (equal (vl-scopeinfo-find-item name (vl-scope->scopeinfo-aux scope design) design)
                                 (vl-scope-find-item name scope design)))
                 :hints (("goal" :expand ((vl-import-stars-find-item name nil design)))))
               (memoize 'vl-scope->scopeinfo-aux))

             (define vl-scope->scopeinfo
               :short "Make a fast lookup table for items in a scope.  Memoized"
               ((scope  vl-scope-p)
                (design vl-maybe-design-p))
               :returns (scopeinfo vl-scopeinfo-p)
               (vl-scopeinfo-make-fast (vl-scope->scopeinfo-aux scope design))
               ///
               (defthm vl-scope->scopeinfo-correct
                 (implies (stringp name)
                          (equal (vl-scopeinfo-find-item name (vl-scope->scopeinfo scope design) design)
                                 (vl-scope-find-item name scope design)))
                 :hints (("goal" :expand ((vl-import-stars-find-item name nil design))))))

             (define vl-scope-find-item-fast
               :short "Like @(see vl-scope-find-item), but uses a fast lookup table."
               ((name stringp)
                (scope vl-scope-p)
                (design vl-maybe-design-p))
               :enabled t
               (mbe :logic (vl-scope-find-item name scope design)
                    :exec (vl-scopeinfo-find-item name (vl-scope->scopeinfo scope design) design )))

             ,@(and stackp
                    `((define vl-scopestack-find-item/context
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :hints (("goal" :expand ((vl-scopestack-fix ss))))
                        :guard-hints (("goal" :expand ((vl-scopestack-p ss))))
                        :short "Find an item declaration and information about where it was declared."
                        :returns (mv (item (iff (vl-scopeitem-p item) item)
                                           "The item declaration, if found")
                                     (item-ss vl-scopestack-p
                                              "The scopestack for the context in
                                               which the item was found")
                                     (pkg-name (iff (stringp pkg-name) pkg-name)
                                               "The package from which the item
                                                was imported, if applicable."))
                        :measure (vl-scopestack-count ss)
                        (b* ((ss (vl-scopestack-fix ss)))
                          (vl-scopestack-case ss
                            :null (mv nil nil nil)
                            :global (b* (((mv pkg-name item)
                                          (vl-scope-find-item-fast name ss.design
                                                                   ss.design)))
                                      (mv item (vl-scopestack-fix ss) pkg-name))
                            :local (b* ((design (vl-scopestack->design ss))
                                        ((mv pkg-name item)
                                         (vl-scope-find-item-fast name ss.top design))
                                        ((when (or pkg-name item))
                                         (mv item ss pkg-name)))
                                     (vl-scopestack-find-item/context name ss.super)))))

                      (define vl-scopestack-find-item
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (item (iff (vl-scopeitem-p item) item)
                                       "The item declaration, if found.")
                        (b* (((mv item & &) (vl-scopestack-find-item/context name ss)))
                          item))

                      (define vl-scopestack-find-item/ss
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (mv (item (iff (__resulttype__ item) item)
                                       "The item declaration, if found.")
                                     (item-ss vl-scopestack-p
                                              "The scopestack for the context
                                               in which the item was declared."))
                        (b* (((mv item context-ss pkg-name)
                              (vl-scopestack-find-item/context name ss))
                             ((unless pkg-name) (mv item context-ss))
                             (design (vl-scopestack->design context-ss))
                             (pkg (and design (cdr (hons-get pkg-name (vl-design-scope-package-alist-top design)))))
                             ((unless pkg) ;; this should mean item is already nil
                              (mv item nil))
                             (pkg-ss (vl-scopestack-push pkg (vl-scopestack-init design))))
                          (mv item pkg-ss)))

                      (define vl-scopestack-find-item/ss/package
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (mv (item (iff (__resulttype__ item) item)
                                           "The item declaration, if found.")
                                     (item-ss vl-scopestack-p
                                              "The scopestack for the context
                                               in which the item was declared.")
                                     (context-ss vl-scopestack-p
                                                 "The scopestack for the context
                                                  in which the item was found (possibly
                                                  imported).")
                                     (pkg-name (iff (stringp pkg-name) pkg-name)
                                               "If the item was imported, the name
                                                of the package it was imported
                                                from."))
                        (b* (((mv item context-ss pkg-name)
                              (vl-scopestack-find-item/context name ss))
                             ((unless pkg-name) (mv item context-ss context-ss nil))
                             (design (vl-scopestack->design context-ss))
                             (pkg (and design (cdr (hons-get pkg-name (vl-design-scope-package-alist-top design)))))
                             ((unless pkg) ;; this should mean item is already nil
                              (mv item nil context-ss pkg-name))
                             (pkg-ss (vl-scopestack-push pkg (vl-scopestack-init design))))
                          (mv item pkg-ss context-ss pkg-name))))))))
     (template-subst-top template
                         (make-tmplsubst
                          :features (and importsp '(:import))
                          :strs `(("__RESULT__" ,(symbol-name result) . vl-package)
                                  ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package))
                          :pkg-sym 'vl-package)))))

(local (defthm maybe-scopeitem-when-iff
         (implies (or (vl-scopeitem-p x)
                      (not x))
                  (vl-maybe-scopeitem-p x))
         ))

(make-event
#||
  (define vl-scope-find-item ...)
  (define vl-scope-item-alist ...)
  (define vl-scope-find-item-fast ...)
  (define vl-scopestack-find-item ...)
||#

 (def-vl-scope-find-item *vl-scopes->items* 'item 'vl-scopeitem-p t t))

(defthm tag-of-vl-scopestack-find-item/ss-forward
  (b* (((mv item ?item-ss) (vl-scopestack-find-item/ss name ss)))
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
                 (x (b* (((mv item ?item-ss)
                          (vl-scopestack-find-item/ss name ss)))
                      item)))))))

(local
 (defun def-vl-scope-find (table result resulttype stackp)
   (declare (xargs :mode :program))
   (b* ((substs (scopes->tmplsubsts table))
        (template
          `(progn
             (define vl-scope-find-__result__
               :short (cat "Look up a plain identifier to find a "
                           (str::downcase-string (symbol-name '__result__))
                           " in a scope.")
               ((name  stringp)
                (scope vl-scope-p))
               :returns (__result__ (iff (vl-__resulttype__-p __result__) __result__))
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (vl-__type__-scope-find-__result__ name scope))))
                      substs)
                   (otherwise nil))))

             (define vl-scope-__result__-alist-aux
               :parents (vl-scope-__result__-alist)
               :short "Memoized core."
               ((scope vl-scope-p))
               :returns (alist vl-__resulttype__-alist-p)
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (b* (((vl-__type__ scope :quietp t)))
                            (make-fast-alist
                             (vl-__type__-scope-__result__-alist scope nil))))))
                      substs)
                   (otherwise nil)))
               ///
               (local (in-theory (enable vl-scope-find-__result__)))
               (defthm vl-scope-__result__-alist-aux-correct
                 (implies (stringp name)
                          (equal (cdr (hons-assoc-equal name (vl-scope-__result__-alist-aux scope)))
                                 (vl-scope-find-__result__ name scope (:@ :import design))))
                 :hints (("goal" :expand ((vl-import-stars-find-item name nil design)))))
               (memoize 'vl-scope-__result__-alist-aux))

             (define vl-scope-__result__-alist
               :short (cat "Make a fast lookup table for "
                           (str::downcase-string (symbol-name '__result__))
                           "s in a scope.  Memoized.")
               ((scope vl-scope-p))
               :returns (alist vl-__resulttype__-alist-p)
               (make-fast-alist (vl-scope-__result__-alist-aux scope))
               ///
               (defthm vl-scope-__result__-alist-correct
                 (implies (stringp name)
                          (equal (cdr (hons-assoc-equal name (vl-scope-__result__-alist scope)))
                                 (vl-scope-find-__result__ name scope (:@ :import design))))))

             (define vl-scope-find-__result__-fast
               :short (cat "Like @(see VL-SCOPE-FIND-" (symbol-name '__result__) "), but uses a fast lookup table")
               ((name stringp)
                (scope vl-scope-p))
               :enabled t
               (mbe :logic (vl-scope-find-__result__ name scope)
                    :exec (cdr (hons-get name (vl-scope-__result__-alist scope)))))

             ,@(and stackp
                    `((define vl-scopestack-find-__result__/ss
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :hints (("goal" :expand ((vl-scopestack-fix ss))))
                        :guard-hints (("goal" :expand ((vl-scopestack-p ss))))
                        :returns (mv (__result__ (iff (vl-__resulttype__-p __result__) __result__)
                                                 "The declaration, if found")
                                     (__result__-ss vl-scopestack-p
                                                    "The scopestack showing the
                                                     context of the declaration"))
                        :short (cat "Find a "
                                    (str::downcase-string (symbol-name '__definition__))
                                    ", as well as info about where it was found.")
                        :measure (vl-scopestack-count ss)
                        (b* ((ss (vl-scopestack-fix ss)))
                          (vl-scopestack-case ss
                            :null (mv nil nil)
                            :global (b* ((__result__
                                          (vl-scope-find-__result__-fast name ss.design)))
                                      (mv __result__ (vl-scopestack-fix ss)))
                            :local (b* ((__result__
                                         (vl-scope-find-__result__-fast name ss.top))
                                        ((when __result__)
                                         (mv __result__ ss)))
                                     (vl-scopestack-find-__result__/ss name ss.super)))))

                      (define vl-scopestack-find-__result__
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (__result__ (iff (vl-__resulttype__-p __result__) __result__))
                        (b* (((mv __result__ &) (vl-scopestack-find-__result__/ss name ss)))
                          __result__)))))))
     (template-subst-top template
                         (make-tmplsubst
                          :strs `(("__RESULT__" ,(symbol-name result) . vl-package)
                                  ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package))
                          :pkg-sym 'vl-package)))))





(make-event
 #||
 (define vl-scope-find-definition ...)
 (define vl-scope-definition-alist ...)
 (define vl-scope-find-definition-fast ...)
 (define vl-scopestack-find-definition ...)
 ||#
 (def-vl-scope-find *vl-scopes->defs* 'definition 'scopedef t))

(defthm tag-of-vl-scopestack-find-definition/ss-forward
  (b* (((mv def ?def-ss) (vl-scopestack-find-definition/ss name ss)))
    (implies def
             (or (equal (tag def) :vl-module)
                 (equal (tag def) :vl-udp)
                 (equal (tag def) :vl-interface)
                 (equal (tag def) :vl-program)
                 (equal (tag def) :vl-class))))
  :rule-classes ((:forward-chaining))
  :hints(("Goal"
          :use ((:instance tag-when-vl-scopedef-p-forward
                 (x (b* (((mv def ?def-ss)
                          (vl-scopestack-find-definition/ss name ss)))
                      def)))))))


(make-event
#||
  (define vl-scope-find-package ...)
  (define vl-scope-package-alist ...)
  (define vl-scope-find-package-fast ...)
  (define vl-scopestack-find-package ...)
||#
 (def-vl-scope-find *vl-scopes->pkgs* 'package 'package t))

(make-event
#||
  (define vl-scope-find-portdecl ...)
  (define vl-scope-portdecl-alist ...)
  (define vl-scope-find-portdecl-fast ...)
||#
 (def-vl-scope-find *vl-scopes->portdecls* 'portdecl 'portdecl nil))




(define vl-scopestacks-free ()
  :parents (scopestack)
  :short "Frees memoization tables associated with scopestacks."
  :long "<p>You should generally call this function, e.g., at the end of any
transform that has used scopestacks.</p>"
  (progn$ (clear-memoize-table 'vl-scope->scopeinfo-aux)
          (clear-memoize-table 'vl-scope-definition-alist-aux)
          (clear-memoize-table 'vl-scope-package-alist-aux)
          (clear-memoize-table 'vl-scope-portdecl-alist-aux)
          (clear-memoize-table 'vl-design-scope-package-alist-aux)
          (clear-memoize-table 'vl-package-scope-item-alist-aux)
          (clear-memoize-table 'vl-design-toplevel)
          ))



; Scopestack debugging
(define vl-scopeitem->name ((x vl-scopeitem-p))
  :returns (name maybe-stringp :rule-classes :type-prescription)
  :prepwork
  ((local (defthm crock
         (implies (vl-genelement-p x)
                  (equal (tag x) (vl-genelement-kind x)))
         :hints(("Goal" :in-theory (enable vl-genelement-p
                                           vl-genelement-kind
                                           tag))))))
  :guard-hints(("Goal" :in-theory (enable vl-scopeitem-p)))
  (b* ((x (vl-scopeitem-fix x)))
    (case (tag x)
      (:vl-modinst    (vl-modinst->instname x))
      (:vl-gateinst   (vl-gateinst->name x))
      (:vl-genbegin   (b* ((name (vl-genblock->name (vl-genbegin->block x))))
                        (and (stringp name) name)))
      (:vl-genarray   (vl-genarray->name x))
      (:vl-genvar     (vl-genvar->name x))
      ((:vl-genloop :vl-genif :vl-gencase :vl-genbase) nil)
      (:vl-interfaceport (vl-interfaceport->name x))
      (:vl-paramdecl     (vl-paramdecl->name x))
      (:vl-vardecl       (vl-vardecl->name x))
      (:vl-fundecl       (vl-fundecl->name x))
      (:vl-taskdecl      (vl-taskdecl->name x))
      (:vl-dpiimport     (vl-dpiimport->name x))
      (:vl-modport       (vl-modport->name x))
      (otherwise         (vl-typedef->name x)))))


(define vl-scopestack->hashkey ((x vl-scopestack-p))
  :short "Produce a honsed, hopefully-unique hash key for this scope."
  :long "<p>Uses the names of the scopes, so: if any scope is not named, it
causes a hard error; and if the name of each scope isn't unique within its
parent scope, then the hash key won't be unique.</p>

<p>Running @(see addnames) before using this should ensure that scopes are
named, and the names generated should be unique.</p>"
  :returns (key)
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null nil
    :global (hons :root nil)
    :local (b* ((super (vl-scopestack->hashkey x.super)))
             (hons (or (vl-scope->id x.top)
                       (raise "Unnamed scope under ~x0: ~x1~%"
                              (rev super)
                              x.top))
                   super))))



(define vl-scopestack->path-aux ((x vl-scopestack-p) rchars)
  :measure (vl-scopestack-count x)
  :returns (rchars character-listp :hyp (character-listp rchars))
  (vl-scopestack-case x
    :null   (str::revappend-chars ":null" rchars)
    :global (str::revappend-chars "$root" rchars)
    :local  (b* ((rchars (vl-scopestack->path-aux x.super rchars))
                 (id (vl-scope->id x.top)))
              (cond ((stringp id)
                     (b* ((rchars (cons #\. rchars)))
                       (str::revappend-chars id rchars)))
                    ((integerp id)
                     (b* ((rchars (cons #\[ rchars))
                          (rchars (if (< id 0) (cons #\- rchars) rchars))
                          (rchars (str::revappend-nat-to-dec-chars (abs id) rchars))
                          (rchars (cons #\] rchars)))
                       rchars))
                    (t ;; (not id)
                     (str::revappend-chars
                      (cat "<unnamed-" (symbol-name (vl-scope->scopetype x.top)) ">")
                      rchars))))))

(define vl-scopestack->path
  :short "Debugging aide: get the current path indicated by a scopestack."
  ((x vl-scopestack-p))
  :returns (path stringp :rule-classes :type-prescription)
  :long "<p>This vaguely corresponds to Verilog syntax, but is generally only
useful or meant for debugging purposes.</p>"
  (b* ((rchars (vl-scopestack->path-aux x nil)))
    (str::rchars-to-string rchars)))



; Definition of vl-design-toplevel
;
; For resolving top-level hierarchical identifiers like topmod.foo.bar, we need
; to be able to know the top-level module names.  After developing the HID
; lookup code, we decided that the scopestack code seemed like an appropriate
; place for vl-design-toplevel, and decided to memoize it and free it alongside
; of the other scopestack memo tables in vl-scopestacks-free.

(define vl-bindlist->modinsts ((x vl-bindlist-p))
  :returns (modinsts vl-modinstlist-p)
  (if (atom x)
      nil
    (append-without-guard (vl-bind->modinsts (car x))
                          (vl-bindlist->modinsts (cdr x)))))

(def-genblob-transform vl-genblob->flatten-modinsts ((acc vl-modinstlist-p))
  ;; Warning: rarely sensible -- returns modinsts from many scopes!
  :no-new-x t
  :returns ((acc vl-modinstlist-p))
  :apply-to-generates vl-generates->flatten-modinsts
  :prepwork ((local (in-theory (disable ;; vl-genelement-p-by-tag-when-vl-scopeitem-p
                                        vl-modinstlist-p-when-not-consp
                                        (tau-system)
                                        append
                                        vl-modinstlist-p-when-subsetp-equal))))
  (vl-generates->flatten-modinsts (vl-genblob->generates x)
                                  (append-without-guard
                                   (vl-bindlist->modinsts (vl-genblob->binds x))
                                   (vl-genblob->modinsts x)
                                   (vl-modinstlist-fix acc))))


(define vl-module->flatten-modinsts ((x vl-module-p))
  :parents (vl-modulelist-everinstanced)
  :short "Gather modinsts from the module, including its generate blocks and bind
          constructs (which don't even belong to it) -- rarely sensible!"
  :returns (modinsts vl-modinstlist-p)
  (b* ((genblob (vl-module->genblob x)))
    (vl-genblob->flatten-modinsts genblob nil)))

(define vl-interface->flatten-modinsts ((x vl-interface-p))
  :parents (vl-interfacelist-everinstanced)
  :short "Gather modinsts from the module, including its generate blocks and bind
          constructs (which don't even belong to it) -- rarely sensible!"
  :returns (modinsts vl-modinstlist-p)
  (b* ((genblob (vl-interface->genblob x)))
    (vl-genblob->flatten-modinsts genblob nil)))

(defprojection vl-interfaceportlist->ifnames ((x vl-interfaceportlist-p))
  :returns (names string-listp)
  (vl-interfaceport->ifname x))


(define vl-modulelist-everinstanced-nrev ((x vl-modulelist-p)
                                          (nrev))
  :parents (vl-modulelist-everinstanced)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (modinsts1 (vl-module->flatten-modinsts (car x)))
       (ifports1  (vl-module->ifports (car x)))
       (nrev      (vl-modinstlist->modnames-nrev modinsts1 nrev))
       (nrev      (vl-interfaceportlist->ifnames-nrev ifports1 nrev)))
    (vl-modulelist-everinstanced-nrev (cdr x) nrev)))

(define vl-modulelist-everinstanced ((x vl-modulelist-p))
  :parents (hierarchy)
  :short "Gather the names of every module and interface ever instanced in a
module list or used in an interface port."

  :long "<p>The returned list typically will contain a lot of duplicates.  This
is fairly expensive, requiring a cons for every single module instance.  We
optimize it to avoid the construction of intermediate lists and to use @(see
nrev).</p>"

  :returns (names string-listp)
  :enabled t
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (modinsts1 (vl-module->flatten-modinsts (car x)))
            (ifports1  (vl-module->ifports (car x))))
         (append (vl-modinstlist->modnames modinsts1)
                 (vl-interfaceportlist->ifnames ifports1)
                 (vl-modulelist-everinstanced (cdr x))))
       :exec
       (if (atom x)
           nil
         (with-local-nrev (vl-modulelist-everinstanced-nrev x nrev))))
  :verify-guards nil
  ///
  (defthm vl-modulelist-everinstanced-nrev-removal
    (equal (vl-modulelist-everinstanced-nrev x nrev)
           (append nrev (vl-modulelist-everinstanced x)))
    :hints(("Goal" :in-theory (enable vl-modulelist-everinstanced-nrev))))

  (verify-guards vl-modulelist-everinstanced))

(define vl-interfacelist-everinstanced-nrev ((x vl-interfacelist-p)
                                             (nrev))
  :parents (vl-interfacelist-everinstanced)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (modinsts1 (vl-interface->flatten-modinsts (car x)))
       (ifports1  (vl-interface->ifports (car x)))
       (nrev      (vl-modinstlist->modnames-nrev modinsts1 nrev))
       (nrev      (vl-interfaceportlist->ifnames-nrev ifports1 nrev)))
    (vl-interfacelist-everinstanced-nrev (cdr x) nrev)))


(define vl-interfacelist-everinstanced ((x vl-interfacelist-p))
  :parents (hierarchy)
  :short "Gather the names of every module and interface ever instanced in a
interface list or used in an interface port."

  :long "<p>The returned list typically will contain a lot of duplicates.  This
is fairly expensive, requiring a cons for every single interface instance.  We
optimize it to avoid the construction of intermediate lists and to use @(see
nrev).</p>"

  :returns (names string-listp)
  :enabled t
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (modinsts1 (vl-interface->flatten-modinsts (car x)))
            (ifports1  (vl-interface->ifports (car x))))
         (append (vl-modinstlist->modnames modinsts1)
                 (vl-interfaceportlist->ifnames ifports1)
                 (vl-interfacelist-everinstanced (cdr x))))
       :exec
       (if (atom x)
           nil
         (with-local-nrev (vl-interfacelist-everinstanced-nrev x nrev))))
  :verify-guards nil
  ///
  (defthm vl-interfacelist-everinstanced-nrev-removal
    (equal (vl-interfacelist-everinstanced-nrev x nrev)
           (append nrev (vl-interfacelist-everinstanced x)))
    :hints(("Goal" :in-theory (enable vl-interfacelist-everinstanced-nrev))))

  (verify-guards vl-interfacelist-everinstanced))



(define vl-design-toplevel
  :parents (hierarchy)
  :short "@(call vl-design-toplevel) gathers the names of any modules or
interfaces that are defined but are never instantiated in a design, and returns
them as an ordered set."
  ((x vl-design-p))
  :returns (names string-listp)
  :long "<p>Memoized. Cleared in @(see vl-scopestacks-free).</p>

<p>Identifying whether a module/interface is a top-level design element is
important for resolving certain hierarchical identifiers and as a starting
point for elaboration.  See in particular @(see vl-follow-hidexpr) and @(see
vl-design-elaborate).</p>

<p>Historically we only looked at top level modules and ignored interfaces.  We
now gather both modules <b>and</b> interfaces that are never used.  One nice
consequence of this is that it means elaboration won't throw away any unused
interfaces, which means we can get their @(see warnings) during @(see vl-lint)
checking.</p>

<p>Note that keeping interfaces here seems to match the behavior of NCVerilog
but not VCS.  When given code such as:</p>

@({
    interface foo ;

      wire ww;

      function bar (input in);
        assign bar = in;
      endfunction

    endinterface

    module mymod ;

      reg r;
      assign foo.ww = r;
      wire w = foo.bar(r);

      initial begin
        r = 0;
        #10;
        $display(\"W is %d\", w);
        $display(\"FOO.WW is %d\", foo.ww);
      end

    endmodule
})

<p>we find that NCV seems to work fine but VCS reports that interface @('foo')
is not instantiated and will be ignored, and then causes ``cross-module
reference errors'' that complain about our uses of @('foo.bar') and
@('foo.ww').  We haven't tried to deeply look at the SystemVerilog standard to
figure out which tool is correct, but it probably doesn't matter much either
way.</p>"

  (b* (((vl-design x))
       (mentioned (union (mergesort (vl-modulelist-everinstanced x.mods))
                         (mergesort (vl-interfacelist-everinstanced x.interfaces))))
       (defined   (union (mergesort (vl-modulelist->names x.mods))
                         (mergesort (vl-interfacelist->names x.interfaces)))))
    (difference defined mentioned))

  ///
  (defthm true-listp-of-vl-design-toplevel
    (true-listp (vl-design-toplevel x))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-design-toplevel
    (setp (vl-design-toplevel x)))

  (memoize 'vl-design-toplevel)

  ;; (defthm vl-find-module-when-member-of-vl-modulelist-toplevel
  ;;   (implies (member name (vl-modulelist-toplevel x))
  ;;            (vl-find-module name x)))

  ;; (defthm vl-has-modules-of-vl-modulelist-toplevel
  ;;   (implies (vl-modulelist-complete-p mods mods)
  ;;            (subsetp-equal (vl-modulelist-toplevel mods)
  ;;                           (vl-modulelist->names mods)))
  ;;   :hints((set-reasoning)))
  )


(define vl-scope-namespace ((x vl-scope-p) (design vl-maybe-design-p))
  :returns (names string-listp)
  (append (alist-keys (vl-scope-portdecl-alist x))
          (alist-keys (vl-scope-package-alist x))
          (alist-keys (vl-scope-definition-alist x))
          (vl-scopeinfo->itemnames (vl-scope->scopeinfo x design) design))
  ///
  (defthm vl-scope-namespace-present-when-item-lookup
    (implies (and (mv-nth 1 (vl-scope-find-item name x design))
                  (stringp name))
             (member name (vl-scope-namespace x design))))

  (local (defthm lookup-in-definition-alist
           (implies (vl-scopedef-alist-p x)
                    (iff (hons-assoc-equal name x)
                         (cdr (hons-assoc-equal name x))))
           :hints(("Goal" :in-theory (enable vl-scopedef-alist-p)))))

  (local (defthm lookup-in-package-alist
           (implies (vl-package-alist-p x)
                    (iff (hons-assoc-equal name x)
                         (cdr (hons-assoc-equal name x))))
           :hints(("Goal" :in-theory (enable vl-package-alist-p)))))

  (local (defthm lookup-in-portdecl-alist
           (implies (vl-portdecl-alist-p x)
                    (iff (hons-assoc-equal name x)
                         (cdr (hons-assoc-equal name x))))
           :hints(("Goal" :in-theory (enable vl-portdecl-alist-p)))))

  (defthm vl-scope-namespace-present-when-definition-lookup
    (implies (and (vl-scope-find-definition name x)
                  (stringp name))
             (member name (vl-scope-namespace x design))))

  (defthm vl-scope-namespace-present-when-package-lookup
    (implies (and (vl-scope-find-package name x)
                  (stringp name))
             (member name (vl-scope-namespace x design))))

  (defthm vl-scope-namespace-present-when-portdecl-lookup
    (implies (and (vl-scope-find-portdecl name x)
                  (stringp name))
             (member name (vl-scope-namespace x design)))))

(defoption vl-maybe-scope vl-scope)

#||

(trace$ #!vl (vl-scopestack-find-item/context
              :entry (list 'vl-scopestack-find-item/context
                           name (vl-scopestack->hashkey name))
              :exit (b* (((list ?item ?ss ?pkg) values))
                      (list 'vl-scopestack-find-item/context
                            (with-local-ps (vl-cw "~a0" item))
                            (vl-scopestack->hashkey ss)
                            pkg))))


||#
