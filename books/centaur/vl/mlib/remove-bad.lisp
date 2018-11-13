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
(include-book "hierarchy")
(include-book "filter")
(local (include-book "../util/arithmetic"))
;(local (include-book "../util/osets"))
;(local (include-book "modname-sets"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))

(defxdoc propagating-errors
  :parents (warnings)
  :short "A mechanism for propagating fatal errors from submodules up to all
modules that rely on these submodules."

  :long "<p>As described in @(see warnings), our @(see transforms) can
sometimes run into severe problems, e.g., we might run into an instance of an
undefined module.  In this case, the transform should typically extend the
module with a fatal warning.</p>

<p>When we are trying to build accurate/sound/correct formal models to analyze,
we generally want to throw away any design elements (e.g., modules, packages,
etc.) that have fatal errors, so that we only produce a model of whatever part
of the design is well-formed and supported.</p>

<p>For various reasons, it's a good idea to throw away any these bad parts of
the design as early as possible.  The main reason for this is that it easier to
identify the root cause of the problem.  Problems tend to snowball.  It's much
better to see a single fatal error from the first transform that hit a problem
than to see dozens errors from different transforms that all have the same
underlying cause.  Throwing out modules early also helps to improve performance
by cutting down the design; there's no point in further transforming stuff
we're going to throw away, anyway.</p>

<p>On the other hand, we can't really just throw bad parts of the design away.
We at least need some way to see what went wrong, so that we can debug it.</p>

<p>Our basic strategy for dealing with this is to imagine two designs,
<b>good</b> and <b>bad</b>.  Initially, we put all of the design elements into
the good design, and the bad design is empty.  We always only try to transform
the good design, and afterward we can move any design elements that had errors
into the bad design.</p>

<p>Moving things into the bad design is tricky because design elements do not
exist in isolation.  When, for instance, some module M has an error, we would
ideally like to remove not only M but also all modules that transitively depend
on M.  Moreover, we also want to make sure that any modules that are killed off
in this transitive way get extended with some kind of warning that explains why
the module is being removed.</p>

<p>Because this is so complicated, we bundle up the process into a function,
@(see vl-design-propagate-errors), which is intended to move any design
elements that (transitively) have errors from @('good') to @('bad').</p>")

(local (xdoc::set-default-parents propagating-errors))

(fty::defalist vl-blamealist
  :parents (propagating-errors)
  :key-type stringp
  :val-type string-listp
  :keyp-of-nil nil
  :valp-of-nil t
  :count vl-blamealist-count
  :short "A record of which submodules are to blame for transitive failures to
  translate modules."

  :long "<h3>Explanation of Blame Alists</h3>

<p>Suppose we are transforming a list of modules, and we run into problems in
some module, @('M').  More generally we might run into a problem with a design
element other than a module, such as an interface, but we'll pretend for the
moment that there are only modules.</p>

<p>Our basic goal for @(see propagating-errors) is to:</p>

<ul>
<li>Add a warning onto @('M') that says why we had the problem, and</li>
<li>Remove @('M') from the list of modules, so that we can continue with the
other modules.</li>
</ul>

<p>But this isn't really good enough.</p>

<p>Besides removing @('M'), we should also remove any dependents (see @(see
hierarchy)) of @('M'), since removing @('M') would cause these modules to be
incomplete.</p>

<p>As we remove these dependent modules, we would also like to annotate them
with warnings explaining that they are being removed because of problems with
@('M').</p>

<p>In general, instead of a single \"bad\" module, imagine that we have a list
of bad modules, @('B1'), ..., @('Bn').  Moreover,</p>

<ul>

<li>Let @('deps(Bi)') be the set of all modules that (transitively) depend on
@('Bi').</li>

<li>Let @('D') be the union over @('deps(Bi)'), i.e., @('D') is the set of all
modules that depend on any bad module)</li>

</ul>

<p>Note that there is no generally reason to think that @('deps(Bi)') is
disjoint from @('deps(Bj)').  If a module @('M') instantiates both @('Bi') and
@('Bj'), then it will be in the dependents for both of them.  So, which one
should be blamed?</p>

<p>Our approach is to blame them both.  To do this, we first construct a
<b>blame alist</b>.</p>

<p>A blame alist includes an entry for every module @('M') in @('D').  That is,
it has an entry for every module that is going to be transitively killed.  In
particular, we want to associate, with each such @('M') with the set of the
\"root problem modules\" that it depends on, i.e., with:</p>

@({
     { Bi : M in deps(Bi) }
})

<p>Once the blame alist is constructed, we can easily use it to annotate each
module in its domain with a warning that says which modules are to blame for
its removal.</p>")

(define vl-blame-alist-aux1 ((bad   stringp         "Name of a module we are currently processing.")
                             (deps  string-listp    "Modules that (transitively) depend on @('bad').")
                             (alist vl-blamealist-p "Partially constructed blame list."))
  :returns (new-alist vl-blamealist-p)
  :parents (vl-blame-alist)
  :short "For each module M in DEPS, additionally blame BAD."
  :measure (len deps)
  (b* ((bad   (string-fix bad))
       (deps  (string-list-fix deps))
       (alist (vl-blamealist-fix alist))
       ((when (atom deps))
        alist)
       (m          (car deps))
       (old-blamed (cdr (hons-get m alist)))
       (new-blamed (cons bad old-blamed))
       (new-alist  (hons-acons m new-blamed alist)))
    (vl-blame-alist-aux1 bad (cdr deps) new-alist)))

(define vl-blame-alist-aux2 ((bads   string-listp    "Names of all the bad modules.")
                             (design vl-design-p     "The design we are processing.")
                             (alist  vl-blamealist-p "Partially constructed blame alist."))
  :returns (new-alist vl-blamealist-p)
  :parents (vl-blame-alist)
  :short "For each Bi in BADS, we compute the transitive dependencies of Bi,
          and then blame Bi for ruining them all."
  (b* (((when (atom bads))
        (vl-blamealist-fix alist))
       (deps  (vl-dependent-elements-transitive (list (car bads)) design))
       (alist (vl-blame-alist-aux1 (car bads) deps alist)))
    (vl-blame-alist-aux2 (cdr bads) design alist))
  ///
  (defthm vl-blame-alist-aux2-when-not-consp
    (implies (not (consp bads))
             (equal (vl-blame-alist-aux2 bads design alist)
                    (vl-blamealist-fix alist)))))

(define vl-blame-alist ((bads   string-listp "Names of bad modules.")
                        (design vl-design-p  "The design we are processing."))
  :returns (blame-alist vl-blamealist-p "Fast alist.")
  :short "Build an alist describing which modules are really to blame for their
          dependents being thrown away."
  ;; BOZO? :guard (uniquep (vl-modulelist->names mods))
  (b* ((bads   (mergesort (string-list-fix bads)))
       (design (vl-design-fix design)))
    (fast-alist-clean
     (vl-blame-alist-aux2 bads design nil))))

(define vl-blame-alist-to-reportcard
  :short "Construct a @(see vl-reportcard) of fatal warnings for a @(see vl-blamealist-p)."
  ((blame-alist vl-blamealist-p
                "Blame alist to process.  We recur through this, so we assume
                 it has already been shrunk, e.g., as in @(see
                 vl-blame-alist).")
   (reportcard  vl-reportcard-p "Report card we are building."))
  :returns (reportcard vl-reportcard-p)
  :measure (vl-blamealist-count blame-alist)
  (b* ((blame-alist (vl-blamealist-fix blame-alist))
       ((when (atom blame-alist))
        (vl-reportcard-fix reportcard))
       ((cons name root-probs) (car blame-alist))
       ;; The blame falls upon everyone mentioned in the blame alist.  But it's
       ;; weird to add a warning saying that a module is to blame for itself.
       ;; So, remove the module itself from the list of root-probs.
       (root-probs (remove-equal name root-probs))
       ((unless root-probs)
        ;; This can happen when, e.g., NAME is the name of a module that has
        ;; its own problems but doesn't depend on anything else.  The module
        ;; will still get thrown out due to whatever made it bad, but it does
        ;; not need to get an extra warning.
        (vl-blame-alist-to-reportcard (cdr blame-alist) reportcard))
       ;; Else, we found someone else to blame, so blame them!
       (warning (make-vl-warning
                 :type :vl-bad-dependency
                 :msg "~m0 (perhaps transitively) depends on other design elements ~
                       that we were not able to process successfully: ~&1."
                 :args (list name root-probs)
                 :fatalp t
                 :fn __function__))
       (reportcard (vl-extend-reportcard name warning reportcard)))
    (vl-blame-alist-to-reportcard (cdr blame-alist) reportcard)))



(define vl-modulelist-zombies
  :parents (vl-design-zombies)
  :short "Identify modules with fatal warnings."
  ((x vl-modulelist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-module->warnings (car x)) suppress-fatals)
         (cons (vl-module->name (car x)) (vl-modulelist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-modulelist-zombies (cdr x) suppress-fatals))))

(define vl-interfacelist-zombies
  :parents (vl-design-zombies)
  :short "Identify interfaces with fatal warnings."
  ((x vl-interfacelist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-interface->warnings (car x)) suppress-fatals)
         (cons (vl-interface->name (car x)) (vl-interfacelist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-interfacelist-zombies (cdr x) suppress-fatals))))

(define vl-packagelist-zombies
  :parents (vl-design-zombies)
  :short "Identify packages with fatal warnings."
  ((x vl-packagelist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-package->warnings (car x)) suppress-fatals)
         (cons (vl-package->name (car x)) (vl-packagelist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-packagelist-zombies (cdr x) suppress-fatals))))

(define vl-udplist-zombies
  :parents (vl-design-zombies)
  :short "Identify udps with fatal warnings."
  ((x vl-udplist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-udp->warnings (car x)) suppress-fatals)
         (cons (vl-udp->name (car x)) (vl-udplist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-udplist-zombies (cdr x) suppress-fatals))))

(define vl-programlist-zombies
  :parents (vl-design-zombies)
  :short "Identify programs with fatal warnings."
  ((x vl-programlist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-program->warnings (car x)) suppress-fatals)
         (cons (vl-program->name (car x)) (vl-programlist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-programlist-zombies (cdr x) suppress-fatals))))

(define vl-classlist-zombies
  :parents (vl-design-zombies)
  :short "Identify classes with fatal warnings."
  ((x vl-classlist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-class->warnings (car x)) suppress-fatals)
         (cons (vl-class->name (car x)) (vl-classlist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-classlist-zombies (cdr x) suppress-fatals))))

(define vl-configlist-zombies
  :parents (vl-design-zombies)
  :short "Identify configs with fatal warnings."
  ((x vl-configlist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-config->warnings (car x)) suppress-fatals)
         (cons (vl-config->name (car x)) (vl-configlist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-configlist-zombies (cdr x) suppress-fatals))))

(define vl-typedeflist-zombies
  :parents (vl-design-zombies)
  :short "Identify typedefs with fatal warnings."
  ((x vl-typedeflist-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-typedef->warnings (car x)) suppress-fatals)
         (cons (vl-typedef->name (car x)) (vl-typedeflist-zombies (cdr x) suppress-fatals)))
        (t
         (vl-typedeflist-zombies (cdr x) suppress-fatals))))

(define vl-design-zombies
  :short "Collect the names of design elements with fatal warnings."
  ((x vl-design-p)
   (suppress-fatals symbol-listp))
  :returns (names string-listp)
  (b* (((vl-design x)))
    (append (vl-modulelist-zombies x.mods suppress-fatals)
            (vl-udplist-zombies x.udps suppress-fatals)
            (vl-interfacelist-zombies x.interfaces suppress-fatals)
            (vl-packagelist-zombies x.packages suppress-fatals)
            (vl-programlist-zombies x.programs suppress-fatals)
            (vl-classlist-zombies x.classes suppress-fatals)
            (vl-configlist-zombies x.configs suppress-fatals)
            (vl-typedeflist-zombies x.typedefs suppress-fatals))))


(define vl-design-filter-zombies
  :parents (vl-design-propagate-errors)
  :short "Move modules and other design elements that have fatal warnings
from the @('good') design into the @('bad') design."
  ((good vl-design-p)
   (bad  vl-design-p)
   (suppress-fatals symbol-listp))
  :returns
  (mv (good-- vl-design-p "Copy of @('good') except that zombies are removed.")
      (bad++  vl-design-p "Extension of @('bad') with zombies from @('good')."))
  (b* (((vl-design good))
       ((vl-design bad))
       ;; Pull all the zombies out of the different kinds of lists
       ((mv bad-mods       good-mods)       (vl-filter-modules    (vl-modulelist-zombies    good.mods suppress-fatals)       good.mods))
       ((mv bad-interfaces good-interfaces) (vl-filter-interfaces (vl-interfacelist-zombies good.interfaces suppress-fatals) good.interfaces))
       ((mv bad-udps       good-udps)       (vl-filter-udps       (vl-udplist-zombies       good.udps suppress-fatals)       good.udps))
       ((mv bad-programs   good-programs)   (vl-filter-programs   (vl-programlist-zombies   good.programs suppress-fatals)   good.programs))
       ((mv bad-classes    good-classes)    (vl-filter-classes    (vl-classlist-zombies     good.classes suppress-fatals)    good.classes))
       ((mv bad-packages   good-packages)   (vl-filter-packages   (vl-packagelist-zombies   good.packages suppress-fatals)   good.packages))
       ((mv bad-configs    good-configs)    (vl-filter-configs    (vl-configlist-zombies    good.configs suppress-fatals)    good.configs))
       ((mv bad-typedefs   good-typedefs)   (vl-filter-typedefs   (vl-typedeflist-zombies   good.typedefs suppress-fatals)   good.typedefs))
       ;; Remove the zombies to create the new good design
       (good (change-vl-design good
                               :mods       good-mods
                               :interfaces good-interfaces
                               :udps       good-udps
                               :programs   good-programs
                               :classes    good-classes
                               :packages   good-packages
                               :configs    good-configs
                               :typedefs   good-typedefs))
       ;; Add the zombies onto the bad design.
       (bad  (change-vl-design bad
                               :mods       (append bad-mods       bad.mods)
                               :interfaces (append bad-interfaces bad.interfaces)
                               :udps       (append bad-udps       bad.udps)
                               :programs   (append bad-programs   bad.programs)
                               :classes    (append bad-classes    bad.classes)
                               :packages   (append bad-packages   bad.packages)
                               :configs    (append bad-configs    bad.configs)
                               :typedefs   (append bad-typedefs   bad.typedefs))))
    (mv good bad)))

(define vl-design-propagate-errors
  :short "Top-level function for @(see propagating-errors).  We identify any
faulty design elements in a @('good') design and move them into a @('bad')
design."
  ((good vl-design-p
         "The good design, which has presumably just been transformed in some way.
          This design may have some \"zombies\" &mdash; design elements with
          fatal warnings.  We will remove these zombies and anything that
          depends on them.")
   (bad  vl-design-p
         "The bad design which holds any faulty design elements.  We will move
          the zombies into this design.")
   (suppress-fatals
          symbol-listp
          "List of warning types that we should never treat as fatal."))
  :returns
  (mv (good-- vl-design-p
              "Cut down version of the good design, with any faulty elements and
               their dependents eliminated.")
      (bad++  vl-design-p
              "Extended version of the bad design, with any faulty elements from
               @('good') moved over into it."))
  ;; BOZO we should probably try to defend against name clashes here.
  (b* ((zombies (vl-design-zombies good suppress-fatals))
       ((unless zombies)
        ;; Optimization: nothing to do, so do nothing.
        (mv (vl-design-fix good)
            (vl-design-fix bad)))

       ;; Else, something to do.  First, figure out all the dependencies of the
       ;; faulty design elements, and add suitable (fatal) warnings to explain
       ;; why they are being thrown away.
       (blame-alist   (vl-blame-alist zombies good))
       (reportcard    (vl-blame-alist-to-reportcard blame-alist nil))
       (good          (vl-apply-reportcard good reportcard)))
    (vl-hierarchy-free)
    (vl-design-filter-zombies good bad suppress-fatals)))

