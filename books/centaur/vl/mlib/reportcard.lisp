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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(define vl-reportcardkey-p (x)
  :parents (vl-reportcard)
  (or (equal x :design)
      (stringp x))
  ///
  (defthm vl-reportcardkey-p-when-stringp
    (implies (stringp x)
             (vl-reportcardkey-p x))))

(define vl-reportcardkey-fix ((x vl-reportcardkey-p))
  :returns (key vl-reportcardkey-p)
  :parents (vl-reportcardkey-p)
  :prepwork ((local (in-theory (enable vl-reportcardkey-p))))
  :inline t
  (mbe :logic (if (equal x :design)
                  x
                (string-fix x))
       :exec x)
  ///
  (defthm vl-reportcardkey-fix-when-vl-reportcardkey-p
    (implies (vl-reportcardkey-p x)
             (equal (vl-reportcardkey-fix x)
                    x))))

(fty::deffixtype vl-reportcardkey
  :pred vl-reportcardkey-p
  :fix  vl-reportcardkey-fix
  :equiv vl-reportcardkey-equiv
  :define t
  :forward t)

(fty::deflist vl-reportcardkeylist
  :elt-type vl-reportcardkey-p
  ///
  (defthm vl-reportcardkeylist-p-when-string-listp
    (implies (string-listp x)
             (vl-reportcardkeylist-p x))
    :hints(("Goal" :induct (len x)))))

(fty::defalist vl-reportcard
  :key-type vl-reportcardkey-p
  :val-type vl-warninglist-p
  :count vl-reportcard-count
  :parents (warnings)
  :short "A (typically fast) alist associating names to warnings."
  :long "<p>A <i>report card</i> associates @(see vl-reportcardkey-p)s to lists
of warnings.  Typically the keys are the names of top-level design
elements (modules, packages, interfaces, ...).  However, as a special case for
warnings about top-level design elements that aren't in any container, e.g.,
top-level parameters or functions, we also allow @(':design') as a key.</p>

<p>There are two common uses for report cards.</p>

<ol>

<li>When transforming modules, we sometimes want to add a warning to some other
module that is \"far away,\" i.e., not the module we're currently rewriting.
It would be somewhat awkward to iteratively update the @(see vl-modulelist-p),
so instead we might create a report card that associates target module names
with the new warnings we want to add to them.  The function @(see
vl-apply-reportcard) can then be used to add these warnings to a design.</li>

<li>Report cards can be useful when we want to print the warnings for a bunch
of modules.  Depending on the context, we might want to associate either the
elaborated (unparameterized) names of modules, or their original names, to
their related warnings.</li>

</ol>")

(local (xdoc::set-default-parents vl-reportcard))

(define vl-extend-reportcard
  :short "Add a single warning to a @(see vl-reportcard-p)."
  ((name       vl-reportcardkey-p "Name of design element to associate the warning with.")
   (warning    vl-warning-p       "Warning to add.")
   (reportcard vl-reportcard-p    "Report card to extend."))
  :returns (new-reportcard vl-reportcard-p)
  (b* ((name         (vl-reportcardkey-fix name))
       (warning      (vl-warning-fix warning))
       (reportcard   (vl-reportcard-fix reportcard))
       (old-warnings (cdr (hons-get name reportcard)))
       (new-warnings (cons warning old-warnings)))
    (hons-acons name new-warnings reportcard)))

(define vl-extend-reportcard-list
  :short "Add a list of warnings to a @(see vl-reportcard-p)."
  ((name       vl-reportcardkey-p "Name of design element to associate all of these warnings with.")
   (warnings   vl-warninglist-p   "List of warnings to add.")
   (reportcard vl-reportcard-p    "Report card to extend."))
  :returns (new-reportcard vl-reportcard-p)
  :long "<p>We add all the warnings at once, i.e., with a single fast-alist
  update.</p>"
  (b* (((when (atom warnings))
        ;; Silly optimization, don't add warnings if there are no warnings.
        (vl-reportcard-fix reportcard))
       (name         (vl-reportcardkey-fix name))
       (warnings     (vl-warninglist-fix warnings))
       (reportcard   (vl-reportcard-fix reportcard))
       (old-warnings (cdr (hons-get name reportcard)))
       (new-warnings (append-without-guard warnings old-warnings)))
    (hons-acons name new-warnings reportcard)))


(defmacro def-vl-apply-reportcard (elem)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (elem-p      (mksym 'vl- elem '-p))
       (elem-fix    (mksym 'vl- elem '-fix))
       (elem-fn     (mksym 'vl- elem '-apply-reportcard))
       (change-elem (mksym 'change-vl- elem))
       (list-p      (mksym 'vl- elem 'list-p))
       (list-fn     (mksym 'vl- elem 'list-apply-reportcard)))
    `(progn
       (define ,elem-fn ((x          ,elem-p)
                         (reportcard vl-reportcard-p))
         :parents (vl-apply-reportcard)
         :returns (new-x ,elem-p)
         :short ,(cat "Add any warnings from a @(see vl-reportcard-p) to a @(see " (symbol-name elem-p) ").")
         (b* (((,(mksym 'vl- elem) x) x)
              (entry      (hons-get x.name (vl-reportcard-fix reportcard)))
              ((unless entry)
               (,elem-fix x)))
           (,change-elem x
                         :warnings
                         (revappend-without-guard (cdr entry) x.warnings))))

       (defprojection ,list-fn ((x          ,list-p)
                                (reportcard vl-reportcard-p))
         :parents (vl-apply-reportcard)
         :short ,(cat "Add any warnings from a @(see vl-reportcard-p) to a @(see " (symbol-name list-p) ").")
         :returns (new-x ,list-p)
         (,elem-fn x reportcard)))))

(def-vl-apply-reportcard module)
(def-vl-apply-reportcard udp)
(def-vl-apply-reportcard interface)
(def-vl-apply-reportcard program)
(def-vl-apply-reportcard class)
(def-vl-apply-reportcard package)
(def-vl-apply-reportcard config)
(def-vl-apply-reportcard typedef)

(define vl-clean-reportcard-aux
  :parents (vl-clean-reportcard)
  :short "Assumes X has already been shrunk, so we may safely recur down it."
  ((x   vl-reportcard-p)
   (acc vl-reportcard-p))
  :returns (acc vl-reportcard-p)
  :measure (vl-reportcard-count x)
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x))
        (vl-reportcard-fix acc))
       ((cons name warnings) (car x))
       (warnings (vl-clean-warnings warnings))
       (acc      (if (atom warnings)
                     acc
                   (hons-acons name warnings acc))))
    (vl-clean-reportcard-aux (cdr x) acc)))

(define vl-clean-reportcard
  :short "Shrink a @(see vl-reportcard-p) and cleans all of its warning lists
with @(see vl-clean-warnings)."
  ((x vl-reportcard-p))
  :returns (new-x vl-reportcard-p)
  :long "<p>Cleaning can be useful before printing report cards, to minimize
any useless or redundant information.  We shrink the report card to eliminate
any shadowed pairs, clean any redundant warnings, and eliminate entries for
modules that don't have any warnings.  The resulting report card doesn't have
redundant/unnecessary information and is suitable for, e.g., printing.</p>"

  (b* ((x        (vl-reportcard-fix x))
       (x-shrink (hons-shrink-alist x nil))
       (ret      (vl-clean-reportcard-aux x-shrink nil)))
    (fast-alist-free x-shrink)
    ret))


(define vl-design-reportcard-keys
  :parents (vl-apply-reportcard)
  :short "Gather a list of all valid @(see vl-reportcard) keys for a design."
  ((design vl-design-p))
  :prepwork ((local (in-theory (enable acl2::rcons))))
  :returns (keys vl-reportcardkeylist-p)
  (b* (((vl-design design) design))
    (mbe :logic (append (vl-modulelist->names design.mods)
                        (vl-udplist->names design.udps)
                        (vl-interfacelist->names design.interfaces)
                        (vl-programlist->names design.programs)
                        (vl-classlist->names design.classes)
                        (vl-packagelist->names design.packages)
                        (vl-configlist->names design.configs)
                        (vl-typedeflist->names design.typedefs)
                        '(:design))
         :exec (with-local-nrev
                 (b* ((nrev (vl-modulelist->names-nrev design.mods nrev))
                      (nrev (vl-udplist->names-nrev design.udps nrev))
                      (nrev (vl-interfacelist->names-nrev design.interfaces nrev))
                      (nrev (vl-programlist->names-nrev design.programs nrev))
                      (nrev (vl-classlist->names-nrev design.classes nrev))
                      (nrev (vl-packagelist->names-nrev design.packages nrev))
                      (nrev (vl-configlist->names-nrev design.configs nrev))
                      (nrev (vl-typedeflist->names-nrev design.typedefs nrev))
                      (nrev (nrev-push :design nrev)))
                   nrev))))
  ///
  (defthm design-in-vl-design-reportcard-keys
    (member :design (vl-design-reportcard-keys x))))



(define vl-revive-invalid-warning ((name    stringp)
                                   (warning vl-warning-p))
  :returns (new-warning vl-warning-p)
  :parents (vl-reportcard-revive-invalid-warnings)
  (b* (((vl-warning warning)))
    (change-vl-warning warning :msg (cat "In " name " -- " warning.msg))))

(defprojection vl-revive-invalid-warnings ((name stringp)
                                           (x    vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  :parents (vl-reportcard-revive-invalid-warnings)
  (vl-revive-invalid-warning name x))

(local (defthm consp-of-car-when-vl-reportcard-p
         (implies (vl-reportcard-p x)
                  (equal (consp (car x))
                         (consp x)))))

(local (defthm stringp-when-vl-reportcardkey-p
         (implies (vl-reportcardkey-p x)
                  (equal (stringp x)
                         (not (equal x :design))))
         :hints(("Goal" :in-theory (enable vl-reportcardkey-p)))))

(define vl-reportcard-revive-invalid-warnings-exec ((x vl-reportcard-p)
                                                    valid-fal
                                                    nrev)
  :guard (hons-assoc-equal :design valid-fal)
  :measure (vl-reportcard-count x)
  :parents (vl-reportcard-revive-invalid-warnings)
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x))
        (nrev-fix nrev))
       ((cons name1 warnings1) (car x))
       ((when (hons-get name1 valid-fal))
        ;; Valid name, so no need to revive its warnings.
        (vl-reportcard-revive-invalid-warnings-exec (cdr x) valid-fal nrev))
       ;; Else, it's invalid, so revive it.
       (nrev (vl-revive-invalid-warnings-nrev name1 warnings1 nrev)))
    (vl-reportcard-revive-invalid-warnings-exec (cdr x) valid-fal nrev)))

(define vl-reportcard-revive-invalid-warnings
  :short "Convert any warnings about invalid keys into warnings about the top-level design."
  ((x vl-reportcard-p) valid-fal)
  :guard (hons-assoc-equal :design valid-fal)
  :returns (warnings vl-warninglist-p)
  :measure (vl-reportcard-count x)
  :verify-guards nil
  (mbe :logic
       (b* ((x (vl-reportcard-fix x))
            ((when (atom x))
             nil)
            ((cons name1 warnings1) (car x))
            ((when (hons-get name1 valid-fal))
             ;; Valid name, so no need to revive its warnings.
             (vl-reportcard-revive-invalid-warnings (cdr x) valid-fal)))
         (append (vl-revive-invalid-warnings name1 warnings1)
                 (vl-reportcard-revive-invalid-warnings (cdr x) valid-fal)))
       :exec
       (with-local-nrev
         (vl-reportcard-revive-invalid-warnings-exec x valid-fal nrev)))
  ///
  (defthm vl-reportcard-revive-invalid-warnings-exec-removal
    (equal (vl-reportcard-revive-invalid-warnings-exec x valid-fal nrev)
           (append nrev (vl-reportcard-revive-invalid-warnings x valid-fal)))
    :hints(("Goal" :in-theory (enable vl-reportcard-revive-invalid-warnings-exec))))

  (verify-guards vl-reportcard-revive-invalid-warnings))

(define vl-apply-reportcard ((x          vl-design-p)
                             (reportcard vl-reportcard-p))
  :returns (new-x vl-design-p)
  :short "Update a design to include any warnings from a @(see
vl-reportcard-p)."

  :long "<p>This is typically the last step in using a reportcard.  We change
the design @('x') by adding the warnings from throughout the report card to the
appropriate design elements.  For instance, if there is a module named @('foo')
in the design that currently has two warnings, and the report card lists three
warnings about @('foo'), then in the new design these warnings will have been
merged so that @('foo') will now have 5 warnings.</p>

<p>One subtlety is that the reportcard may mention modules that aren't in the
design.  This typically shouldn't happen.  If it does, these warnings will be
associated with the top-level design, instead.</p>"

  (b* (((vl-design x) (vl-design-fix x))
       (reportcard    (vl-reportcard-fix reportcard))
       ((when (atom reportcard))
        ;; Optimization: if there aren't any warnings there's nothing to do.
        x)
       (reportcard     (vl-clean-reportcard reportcard))
       (valid-keys     (vl-design-reportcard-keys x))
       (valid-fal      (make-lookup-alist valid-keys))
       (revived        (vl-reportcard-revive-invalid-warnings reportcard valid-fal))
       (- (fast-alist-free valid-fal))
       (new-toplevel   (append-without-guard (cdr (hons-get :design reportcard))
                                             revived x.warnings))
       (new-x (change-vl-design
               x
               :mods       (vl-modulelist-apply-reportcard    x.mods       reportcard)
               :udps       (vl-udplist-apply-reportcard       x.udps       reportcard)
               :interfaces (vl-interfacelist-apply-reportcard x.interfaces reportcard)
               :programs   (vl-programlist-apply-reportcard   x.programs   reportcard)
               :classes    (vl-classlist-apply-reportcard     x.classes    reportcard)
               :packages   (vl-packagelist-apply-reportcard   x.packages   reportcard)
               :configs    (vl-configlist-apply-reportcard    x.configs    reportcard)
               :typedefs   (vl-typedeflist-apply-reportcard   x.typedefs   reportcard)
               :warnings   new-toplevel))
       (- (fast-alist-free reportcard)))
    new-x))

(defmacro def-vl-gather-reportcard (name elem &key fn parents elem->name)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (list-p         (mksym 'vl- name '-p))
       (fn             (or fn      (mksym 'vl- name '-gather-reportcard)))
       (parents        (or parents '(vl-design-reportcard)))
       (elem->name     (or elem->name (mksym 'vl- elem '->name)))
       (elem->warnings (mksym 'vl- elem '->warnings)))
    `(define ,fn ((x ,list-p) (acc vl-reportcard-p))
       :parents ,parents
       :returns (new-acc vl-reportcard-p)
       (b* (((when (atom x))
             (vl-reportcard-fix acc))
            (acc (vl-extend-reportcard-list (,elem->name (car x))
                                            (,elem->warnings (car x))
                                            acc)))
         (,fn (cdr x) acc)))))

(def-vl-gather-reportcard modulelist module)
(def-vl-gather-reportcard udplist udp)
(def-vl-gather-reportcard interfacelist interface)
(def-vl-gather-reportcard programlist program)
(def-vl-gather-reportcard classlist class)
(def-vl-gather-reportcard packagelist package)
(def-vl-gather-reportcard configlist config)
(def-vl-gather-reportcard typedeflist typedef)

(define vl-design-reportcard-aux
  :parents (vl-design-reportcard)
  :short "Extend a @(see vl-reportcard-p) with all of the warnings for a design."
  ((x   vl-design-p)
   (acc vl-reportcard-p "Should be a fast alist."))
  :returns (new-acc vl-reportcard-p "Fast alist, stolen from @('acc').  Not cleaned.")
  (b* (((vl-design x))
       (acc (vl-modulelist-gather-reportcard    x.mods       acc))
       (acc (vl-udplist-gather-reportcard       x.udps       acc))
       (acc (vl-interfacelist-gather-reportcard x.interfaces acc))
       (acc (vl-programlist-gather-reportcard   x.programs   acc))
       (acc (vl-classlist-gather-reportcard     x.classes    acc))
       (acc (vl-packagelist-gather-reportcard   x.packages   acc))
       (acc (vl-configlist-gather-reportcard    x.configs    acc))
       (acc (vl-typedeflist-gather-reportcard   x.typedefs   acc))
       (acc (vl-extend-reportcard-list :design x.warnings acc)))
    acc))

(define vl-design-reportcard
  :short "Constructs a @(see vl-reportcard-p) for a design."
  ((x vl-design-p))
  :returns (reportcard vl-reportcard-p "Already cleaned.")
  :long "<p>This reportcard is in terms of elaborated (unparameterized) names;
see also @(see vl-design-origname-reportcard) for an alternative that uses
original names.</p>"
  (b* ((acc nil)
       (acc (vl-design-reportcard-aux x acc))
       (ret (vl-clean-reportcard acc)))
    (fast-alist-free acc)
    ret))

(def-vl-gather-reportcard modulelist module
  :fn vl-modulelist-gather-origname-reportcard
  :elem->name vl-module->origname)


(define vl-design-origname-reportcard-aux
  :parents (vl-design-origname-reportcard)
  :short "Extend a @(see vl-reportcard-p) with all of the warnings for a
design, in terms of the original design element names."
  ((x   vl-design-p)
   (acc vl-reportcard-p "Should be a fast alist."))
  :returns (new-acc vl-reportcard-p "Fast alist, stolen from @('acc').  Not cleaned.")
  (b* (((vl-design x))
       (acc (vl-modulelist-gather-origname-reportcard    x.mods acc))
       ;; BOZO are these going to have orignames?
       (acc (vl-udplist-gather-reportcard       x.udps acc))
       (acc (vl-interfacelist-gather-reportcard x.interfaces acc))
       (acc (vl-programlist-gather-reportcard   x.programs acc))
       (acc (vl-classlist-gather-reportcard     x.classes acc))
       (acc (vl-packagelist-gather-reportcard   x.packages acc))
       (acc (vl-configlist-gather-reportcard    x.configs acc))
       (acc (vl-typedeflist-gather-reportcard   x.typedefs acc))
       (acc (vl-extend-reportcard-list :design x.warnings acc)))
    acc))

(define vl-design-origname-reportcard
  :short "Constructs a @(see vl-reportcard-p) for a design in terms of original
design element names."
  ((x vl-design-p))
  :returns (reportcard vl-reportcard-p "Already cleaned.")

  :long "<p>This is like @(see vl-design-reportcard) but uses original,
pre-unparameterized names where possible.</p>

<p>Unparameterization causes problems for printing warnings about each module,
because, e.g., instead of having warnings about @('adder'), we actually have
warnings about @('adder$width=5') and @('adder$width=13'), etc.  Yet the
end-user typically shouldn't be bothered with looking at the warnings for each
specialized version of @('adder'); he just wants to see all of the
warnings.</p>

<p>This function gathers up all warnings associated with each module, and
builds a @(see vl-reportcard-p) that maps @('orignames') to warnings.  We take
care to ensure that all of the warnings associated with each name are properly
cleaned up and merged.</p>"

  (b* ((acc nil)
       (acc (vl-design-origname-reportcard-aux x acc))
       (ret (vl-clean-reportcard acc)))
    (fast-alist-free acc)
    ret))


(define vl-reportcard-types
  :short "Collect all types of warnings found in a reportcard."
  ((x vl-reportcard-p))
  :returns (types symbol-listp "Typically includes many duplicates.")
  :measure (vl-reportcard-count x)
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x))
        nil))
    (append (vl-warninglist->types (cdar x))
            (vl-reportcard-types (cdr x)))))

(define vl-keep-from-reportcard
  :short "Filter a reportcard to only keep the warnings of certain types."
  ((types symbol-listp)
   (x vl-reportcard-p))
  :returns (sub-reportcard vl-reportcard-p "Fast alist.")
  :measure (vl-reportcard-count x)
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x))
        nil)
       ((cons name1 warnings1) (car x))
       (keep1 (vl-keep-warnings types warnings1))
       (rest  (vl-keep-from-reportcard types (cdr x)))
       ((when keep1)
        (hons-acons name1 keep1 rest)))
    rest))

(define vl-remove-from-reportcard
  :short "Filter a reportcard to only remove the warnings of certain types."
  ((types symbol-listp)
   (x vl-reportcard-p))
  :returns (sub-reportcard vl-reportcard-p "Fast alist.")
  :measure (vl-reportcard-count x)
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x))
        nil)
       ((cons name1 warnings1) (car x))
       (remove1 (vl-remove-warnings types warnings1))
       (rest  (vl-remove-from-reportcard types (cdr x)))
       ((when remove1)
        (hons-acons name1 remove1 rest)))
    rest))


