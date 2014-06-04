; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(fty::defalist vl-reportcard
  :key-type stringp
  :val-type vl-warninglist-p
  :count vl-reportcard-count)

(defthm vl-reportcard-count-of-cdr-strong
  (implies (and (vl-reportcard-p x)
                (consp x))
           (< (vl-reportcard-count (cdr x))
              (vl-reportcard-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-reportcard-count))))


(defalist vl-reportcard-p (x)
  :parents (warnings)
  :short "A (typically fast) alist associating names to warnings."
  :key (stringp x)
  :val (vl-warninglist-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :long "<p>A <i>report card</i> associates names (strings) to lists of
warnings.  Typically the names are the names of top-level design
elements (modules, packages, interfaces, ...).</p>

<p>There are two common uses for report cards.</p>

<ol>

<li>When transforming modules, we sometimes want to add a warning to some other
module that is \"far away,\" i.e., not the module we're currently rewriting.
It would be somewhat awkward to iteratively update the @(see vl-modulelist-p),
so instead we might create a report card that associates target module names
with the new warnings we want to add to them.  The function @(see
vl-apply-reportcard) can then be used to add these warnings to a design.</li>

<p>Second, report cards can be useful when we want to print the warnings for a
bunch of modules.  Depending on the context, we might want to associate either
the elaborated (unparameterized) names of modules, or their original names, to
their related warnings.</p>"
  :already-definedp t)

(local (xdoc::set-default-parents vl-reportcard-p))

(defsection vl-reportcard-basics

  (defthm vl-reportcard-p-of-insert
    (implies (and (consp a)
                  (stringp (car a))
                  (vl-warninglist-p (cdr a))
                  (vl-reportcard-p x))
             (vl-reportcard-p (insert a x)))
    :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)))))

  (defthm vl-reportcard-p-of-mergesort
    (implies (force (vl-reportcard-p x))
             (vl-reportcard-p (mergesort x))))

  (defthm string-listp-of-alist-keys-when-vl-reportcard-p
    (implies (vl-reportcard-p x)
             (string-listp (alist-keys x)))
    :hints(("Goal" :induct (len x)))))

(define vl-extend-reportcard
  :short "Add a single warning to a @(see vl-reportcard-p)."
  ((name       stringp         "Name of design element to associate the warning with.")
   (warning    vl-warning-p    "Warning to add.")
   (reportcard vl-reportcard-p "Report card to extend."))
  :returns (new-reportcard vl-reportcard-p)
  (b* ((name         (string-fix name))
       (warning      (vl-warning-fix warning))
       (reportcard   (vl-reportcard-fix reportcard))
       (old-warnings (cdr (hons-get name reportcard)))
       (new-warnings (cons warning old-warnings)))
    (hons-acons name new-warnings reportcard)))

(define vl-extend-reportcard-list
  :short "Add a list of warnings to a @(see vl-reportcard-p)."
  ((name       stringp           "Name of design element to associate all of these warnings with.")
   (warnings   vl-warninglist-p  "List of warnings to add.")
   (reportcard vl-reportcard-p   "Report card to extend."))
  :returns (new-reportcard vl-reportcard-p)
  :long "<p>We add all the warnings at once, i.e., with a single fast-alist
  update.</p>"
  (b* ((name         (string-fix name))
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
(def-vl-apply-reportcard package)
(def-vl-apply-reportcard config)

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
merged so that @('foo') will now have 5 warnings.</p>"

  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods       (vl-modulelist-apply-reportcard    x.mods       reportcard)
                      :udps       (vl-udplist-apply-reportcard       x.udps       reportcard)
                      :interfaces (vl-interfacelist-apply-reportcard x.interfaces reportcard)
                      :programs   (vl-programlist-apply-reportcard   x.programs   reportcard)
                      :packages   (vl-packagelist-apply-reportcard   x.packages   reportcard)
                      :configs    (vl-configlist-apply-reportcard    x.configs    reportcard))))



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
(def-vl-gather-reportcard packagelist package)
(def-vl-gather-reportcard configlist config)

(define vl-design-reportcard
  :short "Constructs a @(see vl-reportcard-p) for a design."
  ((x vl-design-p))
  :returns (reportcard vl-reportcard-p "Already cleaned.")
  :long "<p>This reportcard is in terms of elaborated (unparameterized) names;
see also @(see vl-design-origname-reportcard) for an alternative that uses
original names.</p>"
  (b* (((vl-design x) x)
       (acc nil)
       (acc (vl-modulelist-gather-reportcard    x.mods acc))
       (acc (vl-udplist-gather-reportcard       x.udps acc))
       (acc (vl-interfacelist-gather-reportcard x.interfaces acc))
       (acc (vl-programlist-gather-reportcard   x.programs acc))
       (acc (vl-packagelist-gather-reportcard   x.packages acc))
       (acc (vl-configlist-gather-reportcard    x.configs acc))
       (ret (vl-clean-reportcard acc)))
    (fast-alist-free acc)
    ret))

(def-vl-gather-reportcard modulelist module
  :fn vl-modulelist-gather-origname-reportcard
  :elem->name vl-module->origname)


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

  (b* (((vl-design x) x)
       (acc nil)
       (acc (vl-modulelist-gather-origname-reportcard    x.mods acc))
       ;; BOZO are these going to have orignames?
       (acc (vl-udplist-gather-reportcard       x.udps acc))
       (acc (vl-interfacelist-gather-reportcard x.interfaces acc))
       (acc (vl-programlist-gather-reportcard   x.programs acc))
       (acc (vl-packagelist-gather-reportcard   x.packages acc))
       (acc (vl-configlist-gather-reportcard    x.configs acc))
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
