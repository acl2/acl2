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
(include-book "immdeps")
(include-book "centaur/depgraph/toposort" :dir :system)
(include-book "centaur/depgraph/transdeps" :dir :system)
(include-book "centaur/depgraph/invert" :dir :system)
(include-book "filter")
(include-book "reorder")
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
  :short "Graph of downward dependencies.  Fast alist."
  :returns (graph vl-depgraph-p "Maps, e.g., modules to submodules.")
  (b* (((vl-immdepgraph graph) (vl-design-immdeps x)))
    (make-fast-alist graph.deps))
  ///
  (more-returns (graph depgraph::alist-values-are-sets-p)))

(define vl-design-upgraph-aux ((x vl-design-p))
  :parents (vl-design-upgraph)
  :short "Memoized core."
  :enabled t
  (b* (((vl-immdepgraph graph) (vl-design-immdeps x))
       (upgraph (fast-alist-free (depgraph::invert graph.deps)))
       (upgraph (depgraph::mergesort-alist-values upgraph)))
    (make-fast-alist upgraph))
  ///
  (memoize 'vl-design-upgraph-aux))

(define vl-design-upgraph ((x vl-design-p))
  :short "Graph of upward dependencies.  Fast alist."
  :returns (graph vl-depgraph-p "Maps, e.g., modules to superior modules.")
  (make-fast-alist (vl-design-upgraph-aux x))
  ///
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
    (union (cdr (hons-get (car names) graph))
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



(define vl-design-deporder-modules
  :short "Dependency-order sort the modules of a design."
  ((x vl-design-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (new-x vl-design-p))
  (b* (((vl-design x) (vl-design-fix x))
       (downgraph (vl-design-downgraph x))
       ((unless (uniquep (alist-keys downgraph)))
        (mv (cw "Global dependency graph has name clashes: ~x0.~%"
                (duplicated-members (alist-keys downgraph)))
            x))
       ((mv okp deporder) (depgraph::toposort downgraph))
       ((unless okp)
        (mv (cw "Global dependency loop: ~x0.~%" deporder)
            x))
       ((unless (string-listp deporder))
        ;; Shouldn't be possible, so hard error
        (mv (raise "Type error, dependency order should be strings.")
            x))
       (new-mods (vl-reorder-modules deporder x.mods))
       ((unless (equal (mergesort x.mods)
                       (mergesort new-mods)))
        ;; Shouldn't be possible, so hard error
        (mv (raise "Dependency ordering changed the modules somehow??")
            x)))
    (mv t (change-vl-design x :mods new-mods))))

(define vl-hierarchy-free ()
  :short "Free memoize tables associated with @(see hierarchy) functions."
  (progn$
   (clear-memoize-table 'vl-design-immdeps)
   (clear-memoize-table 'vl-design-upgraph-aux)))
