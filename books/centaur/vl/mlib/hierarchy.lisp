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
(include-book "immdeps")
(include-book "centaur/depgraph/toposort" :dir :system)
(include-book "centaur/depgraph/transdeps" :dir :system)
(include-book "centaur/depgraph/invert" :dir :system)
(include-book "filter")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defsection vl-depgraph-p-of-invert
  :parents (vl-depgraph)

  (local (defthm l0
           (implies (and (vl-depgraph-p acc)
                         (stringp parent)
                         (string-listp children))
                    (vl-depgraph-p (depgraph::invert-inner-loop parent children acc)))
           :hints(("Goal" :in-theory (enable depgraph::invert-inner-loop)))))

  (local (defthm l1
           (implies (and (vl-depgraph-p acc)
                         (string-listp nodes)
                         (vl-depgraph-p graph))
                    (vl-depgraph-p (depgraph::invert-outer-loop nodes graph acc)))
           :hints(("Goal" :in-theory (enable depgraph::invert-outer-loop)))))

  (local (defthm l2
           (implies (vl-depgraph-p graph)
                    (string-listp (alist-keys graph)))
           :hints(("Goal" :in-theory (enable vl-depgraph-p)))))

  (local (defthm l3
           (implies (string-listp x)
                    (vl-depgraph-p (pairlis$ x nil)))
           :hints(("Goal" :in-theory (enable pairlis$
                                             vl-depgraph-p)))))

  (defthm vl-depgraph-p-of-invert
    (implies (vl-depgraph-p x)
             (vl-depgraph-p (depgraph::invert x)))
    :hints(("Goal" :in-theory (enable depgraph::invert)))))

(defsection string-listp-of-transdeps
  :parents (vl-depgraph)

  (local (defthm l0
           (implies (vl-depgraph-p x)
                    (string-listp (flatten (alist-vals x))))
           :hints(("Goal" :induct (len x)))))

  (local (defthm l1
           (implies (vl-depgraph-p x)
                    (string-listp (alist-keys x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm string-listp-of-transdeps-allnodes
           (implies (vl-depgraph-p graph)
                    (string-listp (depgraph::transdeps-allnodes graph)))
           :hints(("Goal" :in-theory (enable depgraph::transdeps-allnodes)))))

  (defthm string-listp-of-transdeps
    (implies (and (string-listp nodes)
                  (vl-depgraph-p graph))
             (string-listp (depgraph::transdeps nodes graph)))
    :hints(("Goal"
            :in-theory (disable depgraph::transdeps-subset)
            :use ((:instance depgraph::transdeps-subset
                   (depgraph::nodes nodes)
                   (depgraph::graph graph)))))))


(defxdoc hierarchy
  :parents (mlib)
  :short "Functions for working with the hierarchy of dependencies between
Verilog descriptions."

  :long "<p>In Verilog-2005, the modules in a design form a hierarchy.  Here is
some terminology we'll use regarding this hierarchy:</p>

<ul>

<li>We say that superior modules <i>depend on</i> the modules they
instantiate.</li>

<li>We say that submodules are <i>necessary for</i> the modules that
instantiate them.</li>

<li>We say that modules are <i>missing</i> if they are instantiated but never
defined.</li>

<li>We say that a module list is <i>complete</i> if every module that is ever
instantiated has a definition.</li>

</ul>

<p>SystemVerilog adds many kinds of top-level descriptions besides modules.
For instance, we may have interfaces, packages, programs, and so forth.  There
may also be top-level declarations of parameters, functions, etc., that are not
embedded within any containing package, module, etc.</p>

<p>We can imagine a similar, expanded notion of hierarchy that can be applied
to designs with these other kinds of descriptions.</p>

<p>In the functions below, we take a rather inclusive view of the dependencies
between design elements.  We view the design as containing a directed graph of
dependencies:</p>

<ul>

<li>The nodes are any top-level design elements.  For instance, a node might be
a top-level container such as a module, interface, or package; it also might be
a top-level function declaration, parameter, etc.</li>

<li>The edges in the graph are dependencies from one node to another.  For
instance, we will say a superior module depends on the submodule it
instantiates, an interface depends on any packages it imports, a parameter
depends on the data type it refers to, and so forth.</li>

</ul>

<p>This inclusive view makes collecting dependencies somewhat involved.  We
have to walk through the expressions and check for references to items from
other packages.  We also have to examine the data type of every variable.  The
work of extracting the core dependency graph is done by the @(see immdeps)
functions.</p>

<p>Once we have collected a dependency graph, we can use it for many
purposes.</p>")

(local (xdoc::set-default-parents hierarchy))

(define vl-design-check-complete ((x vl-design-p))
  :returns (new-x vl-design-p)
  :short "Check whether we have definitions for all of the descriptions used
throughout the design."
  :long "<p>This is a basic sanity check for modules, interfaces, etc., to make
sure that all identifiers used within these design elements are defined.  All
of the work is done by @(see immdeps), which creates a @(see vl-reportcard)
with warnings for any undeclared identifiers.</p>"
  :verbosep t
  (b* (((vl-immdepgraph graph) (vl-design-immdeps x)))
    (vl-apply-reportcard x graph.reportcard)))

(define vl-design-downgraph ((x vl-design-p))
  :short "Graph of downward dependencies."
  :returns (graph vl-depgraph-p "Maps, e.g., modules to submodules.")
  (b* (((vl-immdepgraph graph) (vl-design-immdeps x)))
    (make-fast-alist graph.deps))
  ///
  (more-returns (graph depgraph::alist-values-are-sets-p)))

(define vl-design-upgraph ((x vl-design-p))
  :short "Graph of upward dependencies.  Fast alist."
  :returns (graph vl-depgraph-p "Maps, e.g., modules to superior modules.")
  (b* (((vl-immdepgraph graph) (vl-design-immdeps x))
       (upgraph (fast-alist-free (depgraph::invert graph.deps)))
       (upgraph (depgraph::mergesort-alist-values upgraph)))
    (make-fast-alist upgraph))
  ///
  (memoize 'vl-design-upgraph)
  (more-returns (graph depgraph::alist-values-are-sets-p)))

(define vl-collect-dependencies ((names string-listp)
                                 (graph (and (vl-depgraph-p graph)
                                             (depgraph::alist-values-are-sets-p graph))))
  :hooks nil
  :returns (dependencies (and (string-listp dependencies)
                              (setp dependencies))
                         :hyp :fguard)
  (if (atom names)
      nil
    (union (cdr (hons-get names graph))
           (vl-collect-dependencies (cdr names) graph))))

(define vl-dependent-elements-direct
  :parents (hierarchy)
  :short "Gathers the names of all design elements that directly depend on
particular descriptions."
  ((subs   string-listp  "Names of the sub design elements we're interested in.")
   (design vl-design-p   "The design."))
  :returns
  (superiors (and (string-listp superiors)
                  (setp superiors))
             "Names of the superior design elements that directly depend
              on these sub elements.")
  (vl-collect-dependencies (string-list-fix subs)
                           (vl-design-upgraph design)))

(define vl-dependent-elements-transitive
  :parents (hierarchy)
  :short "Gather the names of all design elements that transitively depend
on particular descriptions."
  ((subs   string-listp "Names of the sub design elements we're interested in.")
   (design vl-design-p  "The design."))
  :returns
  (superiors (and (string-listp superiors)
                  (setp superiors))
             "Names of the superior design elements that transitively depend on
              these sub elements.  Always includes everything in @('subs').")
  (depgraph::transdeps (string-list-fix subs)
                       (vl-design-upgraph design)))

(define vl-necessary-elements-direct
  :parents (hierarchy)
  :short "Gathers the names of all design elements that particular descriptions
directly depend on."
  ((superiors string-listp  "Names of the superior design elements we're interested in.")
   (design    vl-design-p   "The design."))
  :returns
  (subs (and (string-listp subs)
             (setp subs))
        "Names of the sub design elements that are directly needed by these
         superior elements.")
  (vl-collect-dependencies (string-list-fix superiors)
                           (vl-design-downgraph design)))

(define vl-necessary-elements-transitive
  :parents (hierarchy)
  :short "Gathers the names of all design elements that particular descriptions
transitively depend on."
  ((superiors string-listp  "Names of the superior design elements we're interested in.")
   (design    vl-design-p   "The design."))
  :returns
  (subs (and (string-listp subs)
             (setp subs))
        "Names of the sub design elements that are transitively needed by these
         superior elements.  Always includes everything in @('superiors').")
  (depgraph::transdeps (string-list-fix superiors)
                       (vl-design-downgraph design)))



(define vl-remove-unnecessary-elements
  :parents (hierarchy)
  :short "Throws away whatever part of the design is not necessary for
particular design elements."
  ((keep string-listp  "Names of top level design elements (modules, interfaces,
                        etc.)  that you want to keep.")
   (design vl-design-p "The design to filter."))
  :returns (trimmed-design vl-design-p)
  (b* ((necessary (vl-necessary-elements-transitive keep design))
       (fal       (make-lookup-alist necessary))
       ((vl-design design))
       (mods       (with-local-nrev (vl-fast-keep-modules    necessary fal design.mods       nrev)))
       (udps       (with-local-nrev (vl-fast-keep-udps       necessary fal design.udps       nrev)))
       (interfaces (with-local-nrev (vl-fast-keep-interfaces necessary fal design.interfaces nrev)))
       (programs   (with-local-nrev (vl-fast-keep-programs   necessary fal design.programs   nrev)))
       (packages   (with-local-nrev (vl-fast-keep-packages   necessary fal design.packages   nrev)))
       (configs    (with-local-nrev (vl-fast-keep-configs    necessary fal design.configs    nrev)))
       (vardecls   (with-local-nrev (vl-fast-keep-vardecls   necessary fal design.vardecls   nrev)))
       (taskdecls  (with-local-nrev (vl-fast-keep-taskdecls  necessary fal design.taskdecls  nrev)))
       (fundecls   (with-local-nrev (vl-fast-keep-fundecls   necessary fal design.fundecls   nrev)))
       (paramdecls (with-local-nrev (vl-fast-keep-paramdecls necessary fal design.paramdecls nrev)))
       (typedefs   (with-local-nrev (vl-fast-keep-typedefs   necessary fal design.typedefs   nrev)))
       ;; Imports are subtle.  If we got rid of a whole package, we don't need the import.  If we
       ;; didn't get rid of the package, we'll keep the import.
       (imports    (with-local-nrev (vl-fast-keep-imports-by-package necessary fal design.imports nrev)))
       (- (fast-alist-free fal)))
    (change-vl-design design
                      :mods       mods
                      :udps       udps
                      :interfaces interfaces
                      :programs   programs
                      :packages   packages
                      :configs    configs
                      :vardecls   vardecls
                      :taskdecls  taskdecls
                      :fundecls   fundecls
                      :paramdecls paramdecls
                      :typedefs   typedefs
                      :imports    imports
                      ;; It seems reasonable to throw away any forward type declarations
                      :fwdtypes   nil)))


(defmacro def-vl-reorder (list name-accessor)
  
  `(define vl-reorder-





;                         DEPENDENCY ORDERING
;
; We now introduce a routine to sort modules into dependency order.
;

(defalist vl-deporder-alistp (x)
  :parents (vl-deporder)
  :short "Alist that associates module names to their levels in the
instantiation hierarchy."
  :long "<p>If a module never instances any submodules, its level is 0.
Otherwise, its level is 1 more than the maximum level of any of its
submodules.</p>"
  :key (stringp x)
  :val (natp x)
  :keyp-of-nil nil
  :valp-of-nil nil)

(defthm string-listp-of-alist-keys-when-vl-deporder-alistp
  (implies (vl-deporder-alistp x)
           (string-listp (alist-keys x)))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-cdr-of-hons-assoc-equal-when-vl-deporder-alistp-one
  (implies (and (member-equal name (alist-keys x))
                (vl-deporder-alistp x))
           (and (integerp (cdr (hons-assoc-equal name x)))
                (<= 0 (cdr (hons-assoc-equal name x)))))
  :hints(("Goal"
          :in-theory (disable NATP-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-VL-DEPORDER-ALISTP)
          :use ((:instance NATP-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-VL-DEPORDER-ALISTP
                 (acl2::k name) (acl2::x x))))))



(defsection vl-maximal-deporder
  :parents (vl-deporder)
  :short "@(call vl-maximal-deporder) returns the maximum level for any module
in @('names'), according to a @(see vl-deporder-alistp)."

  (defund vl-maximal-deporder (names alist)
    (declare (xargs :guard (and (true-listp names)
                                (vl-deporder-alistp alist)
                                (subsetp-equal names (alist-keys alist)))
                    :verify-guards nil))
    (if (atom names)
        0
      (max (cdr (hons-get (car names) alist))
           (vl-maximal-deporder (cdr names) alist))))

  (defthm natp-of-vl-maximal-deporder
    (implies (and (force (true-listp names))
                  (force (vl-deporder-alistp alist))
                  (force (subsetp-equal names (alist-keys alist))))
             (and (integerp (vl-maximal-deporder names alist))
                  (<= 0 (vl-maximal-deporder names alist))))
    :hints(("Goal" :in-theory (enable vl-maximal-deporder))))

  (verify-guards vl-maximal-deporder))



(defsection vl-deporder-pass
  :parents (vl-deporder)
  :short "@(call vl-deporder-pass) extends a partial @(see vl-deporder-alistp)
with entries for the modules whose level is now apparent."

  :long "<p>@('mods') are a list of modules, @('alist') is a partial
@(see vl-deporder-alistp), and @('sorted-cars') are the sorted cars of
alist (which we have precomputed so we don't have to be recomputing it all the
time.).</p>

<p>We walk down the list of modules, processing each in turn.  Suppose we are
processing module @('M').  Then, we consider the modules that @('M')
instantates.  If all of these instantiated modules have their deporder
computed, then the deporder of @('M') 1 more than their @(see
vl-maximal-deporder).  Otherwise, we will wait for a subsequent pass.</p>"

  (defund vl-deporder-pass (mods alist sorted-cars)
    "Returns (MV REMAINING UPDATES)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-deporder-alistp alist)
                                (equal sorted-cars (mergesort (alist-keys alist))))
                    :verify-guards nil))
    (b* (((when (atom mods))
          (mv nil nil))
         ((mv remaining-mods alist-updates)
          (vl-deporder-pass (cdr mods) alist sorted-cars))
         (insts-modnames*
          (vl-necessary-direct-for-module (car mods)))
         ((when (subset insts-modnames* sorted-cars))
          (mv remaining-mods
              (cons (cons (vl-module->name (car mods))
                          (+ 1 (vl-maximal-deporder insts-modnames* alist)))
                    alist-updates))))
      (mv (cons (car mods) remaining-mods)
          alist-updates)))

  (defmvtypes vl-deporder-pass (true-listp true-listp))

  (local (in-theory (enable vl-deporder-pass)))

  (defthm len-of-vl-deporder-pass
    (<= (len (mv-nth 0 (vl-deporder-pass mods alist sorted-cars)))
        (len mods))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-modulelist-p-of-vl-deporder-pass
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 0 (vl-deporder-pass mods alist sorted-cars)))))

  (defthm member-equal-of-vl-deporder-pass
    (implies (member-equal e (alist-keys (mv-nth 1 (vl-deporder-pass mods alist sorted-cars))))
             (member-equal e (vl-modulelist->names mods))))

  (defthm subsetp-equal-of-vl-deporder-pass
    (subsetp-equal (alist-keys (mv-nth 1 (vl-deporder-pass mods alist sorted-cars)))
                   (vl-modulelist->names mods)))

  (defthm vl-deporder-alistp-of-vl-deporder-pass
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-deporder-alistp alist))
                  (force (equal sorted-cars (mergesort (alist-keys alist)))))
             (vl-deporder-alistp (mv-nth 1 (vl-deporder-pass mods alist sorted-cars))))
    :hints(("Goal" :in-theory (enable vl-necessary-direct-for-module))))

  (verify-guards vl-deporder-pass
    :hints(("Goal" :in-theory (enable vl-necessary-direct-for-module))))

  ;; BOZO i broke it.  is this important?
  ;;
  ;; (defcong set-equiv equal (vl-deporder-pass mods alist sorted-cars) 3
  ;;   :hints(("Goal" :in-theory (enable vl-deporder-pass))))

  )



(defsection vl-deporder-pass*
  :parents (vl-deporder)
  :short "@(call vl-deporder-pass*) iterates @(see vl-deporder-pass) to a fixed
point."

  (defund vl-deporder-pass* (mods alist)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-deporder-alistp alist))
                    :measure (len mods)))
    (b* (((mv remaining updates)
          (vl-deporder-pass mods alist (mergesort (alist-keys alist))))
         ((unless remaining)
          (make-fal updates alist))
         ((when (same-lengthp mods remaining))
          (b* ((instanced (mergesort (vl-modulelist-everinstanced mods)))
               (missing (difference instanced
                                    (union (mergesort (alist-keys alist))
                                           (mergesort (vl-modulelist->names
                                                       mods)))))
               ((when missing)
                (er hard? 'vl-deporder-pass*
                    "The following modules are instanced but not defined: ~x0~%"
                    missing)
                alist))
            (er hard? 'vl-deporder-pass*
                "Failed to determine a dependency order for the following ~
                 modules.  We probably have circular dependencies.  ~x0~%"
                (vl-modulelist->names mods))
            alist))
         (alist (make-fal updates alist)))
      (vl-deporder-pass* remaining alist)))

  (local (in-theory (enable vl-deporder-pass*)))

  (defthm vl-deporder-alistp-of-vl-deporder-pass*
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-deporder-alistp alist)))
             (vl-deporder-alistp (vl-deporder-pass* mods alist)))))



(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (subsetp x y)
                          (string-listp y))
                     (equal (string-listp x)
                            (true-listp x)))))

   (local (defthm l1
            (implies (and (set-equiv x y)
                          (true-listp x)
                          (true-listp y))
                     (equal (string-listp x)
                            (string-listp y)))
            :hints(("Goal"
                    :in-theory (disable l0)
                    :use ((:instance l0)
                          (:instance l0 (x y) (y x)))))))

   (defthm string-listp-of-alist-vals-of-mergesort
     (equal (string-listp (alist-vals (mergesort x)))
            (string-listp (alist-vals x)))
     :hints(("Goal" :in-theory (disable mergesort)
             :use ((:instance l1
                    (x (alist-vals x))
                    (y (alist-vals (mergesort x))))))))))


(defsection vl-deporder
  :parents (hierarchy)
  :short "@(call vl-deporder) returns a list of module names in dependency
order."

  (defund vl-deporder (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (b* ((mods (vl-modulelist-fix mods))
         (alist (vl-deporder-pass* mods nil))
         (-     (clear-memoize-table 'vl-necessary-direct-for-module))
         (-     (fast-alist-free alist))
         ((unless (uniquep (alist-keys alist)))
          (er hard? 'vl-deporder-sort "Expected cars to be unique, but found duplicates for ~x0."
              (duplicated-members (alist-keys alist))))
         ;; Now, our alist is a mapping of strings to numbers.  We want to sort
         ;; it so that the lowest numbers come first.  A really stupid way to do
         ;; this is as follows:
         (swap-alist (pairlis$ (alist-vals alist)
                               (alist-keys alist)))
         (sorted     (mergesort swap-alist)))
      (alist-vals sorted)))

  (local (in-theory (enable vl-deporder)))

  (defthm string-listp-of-vl-deporder
    (implies (force (vl-modulelist-p mods))
             (string-listp (vl-deporder mods)))
    :hints(("Goal" :in-theory (disable acl2::strip-cdrs-of-pairlis$))))

  (deffixequiv vl-deporder :args ((mods vl-modulelist-p))))


(define vl-deporder-sort ((mods vl-modulelist-p))
  :parents (hierarchy)
  :short "Reorder modules into a dependency order (lowest-level modules first,
top-level modules at the end of the list.)"

  :returns (sorted-mods vl-modulelist-p)
  :verbosep t

  (b* ((mods     (vl-modulelist-fix mods))
       (order    (vl-deporder mods))
       (allnames (vl-modulelist->names mods))
       ((unless (equal (mergesort order) (mergesort allnames)))
        (prog2$ (raise "Expected all modules to be accounted for.")
                mods))
       (modalist (vl-modalist mods))
       (result   (vl-fast-find-modules order mods modalist)))
    (fast-alist-free modalist)
    result))

