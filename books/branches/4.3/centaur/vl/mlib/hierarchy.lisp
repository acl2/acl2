; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "modnamespace")
(include-book "filter")
(include-book "../util/string-alists")
(include-book "../util/defwellformed")
(local (include-book "modname-sets"))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (include-book "finite-set-theory/osets/set-order" :dir :system))


(defxdoc hierarchy
  :parents (mlib)
  :short "Functions for working with the module hierarchy.")

(defxdoc completeness
  :parents (hierarchy well-formedness)
  :short "We say that a module is <b>complete</b> when every module it
instances is defined.")

(defxdoc missing
  :parents (hierarchy)
  :short "We say a module is <b>missing</b> when it is instantiated
but not defined.")



(defsection vl-has-module
  :parents (hierarchy)
  :short "@(call vl-has-module) determines if a module named <tt>name</tt> is
defined in <tt>mods</tt>."

  :long "<p>We leave this function enabled.  In the logic, it is defined as
nothing more than membership in <tt>(@(see vl-modulelist->names)
mods)</tt>.</p>

<p>This function is not efficient.  It carries out an <tt>O(n)</tt> search of
the modules.  See @(see vl-fast-has-module) for a faster alternative.</p>"

  (defun vl-has-module (name mods)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods))))
    (mbe :logic
         (if (member-equal name (vl-modulelist->names mods))
             t
           nil)
         :exec
         (if (atom mods)
             nil
           (or (equal name (vl-module->name (car mods)))
               (vl-has-module name (cdr mods)))))))



(defsection vl-find-module
  :parents (hierarchy)
  :short "@(call vl-find-module) retrieves the first module named <tt>x</tt>
from <tt>mods</tt>."

  :long "<p>This is the logically simplest expression of looking up a module,
and is our preferred normal form for rewriting.</p>

<p>This function is not efficient.  It carries out an <tt>O(n)</tt> search of
the modules.  See @(see vl-fast-find-module) for a faster alternative.</p>"

  (defund vl-find-module (name mods)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods))))
    (cond ((atom mods)
           nil)
          ((equal name (vl-module->name (car mods)))
           (car mods))
          (t
           (vl-find-module name (cdr mods)))))

  (local (in-theory (enable vl-find-module)))

  (defthm vl-find-module-when-not-consp
    (implies (not (consp mods))
             (equal (vl-find-module name mods)
                    nil)))

  (defthm vl-find-module-of-cons
    (equal (vl-find-module name (cons a x))
           (if (equal name (vl-module->name a))
               a
             (vl-find-module name x))))

  (defthm vl-module-p-of-vl-find-module
    (implies (force (vl-modulelist-p mods))
             (equal (vl-module-p (vl-find-module name mods))
                    (vl-has-module name mods))))

  (defthm vl-find-module-under-iff
    (implies (force (vl-modulelist-p mods))
             (iff (vl-find-module name mods)
                  (vl-has-module name mods))))

  (defthm vl-module->name-of-vl-find-module
    (equal (vl-module->name (vl-find-module name mods))
           (if (vl-has-module name mods)
               name
             nil))
    :hints(("Goal" :in-theory (enable vl-module->name))))

  (defthm member-equal-of-vl-find-module-of-self
    (implies (force (vl-modulelist-p mods))
             (iff (member-equal (vl-find-module name mods) mods)
                  (vl-has-module name mods)))))



(defsection vl-modalist
  :parents (hierarchy)
  :short "Build a fast alist mapping module names to modules."

  :long "<p>@(call vl-modalist) constructs a fast alist that binds each
module's name to its definition.  This alist can be given to functions like
@(see vl-fast-has-module), @(see vl-fast-find-module), etc., to implement fast
module lookups.</p>"

  (defund vl-modalist (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (if (atom mods)
        nil
      (hons-acons (vl-module->name (car mods))
                  (car mods)
                  (vl-modalist (cdr mods)))))

  (local (in-theory (enable vl-modalist)))

  (defthm vl-modalist-when-not-consp
    (implies (not (consp x))
             (equal (vl-modalist x)
                    nil)))

  (defthm vl-modalist-of-cons
    (equal (vl-modalist (cons a x))
           (cons (cons (vl-module->name a) a)
                 (vl-modalist x))))

  (defthm alistp-of-vl-modalist
    (alistp (vl-modalist x)))

  (defthm strip-cars-of-vl-modalist
    (equal (strip-cars (vl-modalist x))
           (vl-modulelist->names x)))

  (defthm strip-cdrs-of-vl-modalist
    (equal (strip-cdrs (vl-modalist x))
           (list-fix x)))

  (defthm hons-assoc-equal-of-vl-modalist
    (implies (force (vl-modulelist-p x))
             (equal (hons-assoc-equal name (vl-modalist x))
                    (if (vl-has-module name x)
                        (cons name (vl-find-module name x))
                      nil)))))


(defsection vl-fast-has-module
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-has-module)."

  (definline vl-fast-has-module (name mods modalist)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-has-module name mods)
         :exec
         (if (hons-get name modalist)
             t
           nil))))


(defsection vl-fast-find-module
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-find-module)."

  (definline vl-fast-find-module (name mods modalist)
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-find-module name mods)
         :exec
         (cdr (hons-get name modalist)))))


(defsection vl-has-modules
  :parents (hierarchy)
  :short "@(call vl-has-modules) determines if every module in named in
<tt>x</tt> is defined in <tt>mods</tt>."

  :long "<p>We leave this function enabled.  In the logic, it is defined
as nothing more a subsetp-equal check in <tt>(@(see vl-modulelist->names)
mods)</tt>.</p>

<p>This function is not efficient.  It carries out a linear search through the
list of modules for each name in <tt>x</tt>, making it quadratic.  See also
@(see vl-fast-has-modules) for a faster alternative.</p>"

  (defun vl-has-modules (x mods)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods))))
    (mbe :logic
         (subsetp-equal x (vl-modulelist->names mods))
         :exec
         (or (atom x)
             (and (vl-has-module (car x) mods)
                  (vl-has-modules (cdr x) mods))))))


(defsection vl-fast-has-modules
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-has-modules)."

  (defun vl-fast-has-modules (x mods modalist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (subsetp-equal x (vl-modulelist->names mods))
         :exec
         (or (atom x)
             (and (vl-fast-has-module (car x) mods modalist)
                  (vl-fast-has-modules (cdr x) mods modalist))))))


(defsection vl-find-modules
  :parents (hierarchy)
  :short "@(call vl-find-modules) gathers every module in named in <tt>x</tt>
from <tt>mods</tt> and returns them as a list."

  :long "<p>This is a simple projection over @(see vl-find-module), and is our
logically simplest way of gathering modules by name.</p>

<p>This function is not efficient.  It carries out a linear search over the
module list for each module in <tt>x</tt>, making it quadratic.  For better
performance, see @(see vl-fast-find-modules).</p>"

  (defprojection vl-find-modules (x mods)
    (vl-find-module x mods)
    :guard (and (string-listp x)
                (vl-modulelist-p mods)))

  (local (in-theory (enable vl-find-modules)))

  (defthm vl-modulelist-p-of-vl-find-modules
    (implies (force (vl-modulelist-p mods))
             (equal (vl-modulelist-p (vl-find-modules names mods))
                    (vl-has-modules names mods))))

  (defthm subsetp-equal-of-vl-find-modules-of-self
    (implies (force (vl-modulelist-p mods))
             (equal (subsetp-equal (vl-find-modules names mods) mods)
                    (vl-has-modules names mods))))

  (defthm vl-modulelist-p-of-vl-find-modules-of-self
    (implies (force (vl-modulelist-p mods))
             (equal (vl-modulelist-p (vl-find-modules names mods))
                    (vl-has-modules names mods))))

  (defthm vl-modulelist->names-of-vl-find-modules
    (implies (vl-has-modules names mods)
             (equal (vl-modulelist->names (vl-find-modules names mods))
                    (list-fix names)))))



(defsection vl-fast-find-modules
  :parents (hierarchy)
  :short "@(see vl-modalist)-optimized version of @(see vl-find-modules)."

  (defun vl-fast-find-modules (x mods modalist)
    (declare (xargs :guard (and (string-listp x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (vl-find-modules x mods)
         :exec
         (if (atom x)
             nil
           (cons (vl-fast-find-module (car x) mods modalist)
                 (vl-fast-find-modules (cdr x) mods modalist))))))


(defsection vl-modulelist-everinstanced
  :parents (hierarchy)
  :short "@(call vl-modulelist-everinstanced) gathers the names of every module
instanced anywhere in a module list <tt>x</tt>."

  :long "<p>We leave this function enabled.  It is logically equal to:</p>

<code>
  (vl-modinstlist-&gt;modnames (vl-modulelist-&gt;modinsts x))
</code>

<p>But it is implemented more efficiently.  The list returned will typically
contain duplicates.  Even so, constructing the list of all instance names may
require a lot of consing.</p>

<p>Note: nreverse optimized in raw lisp.</p>"

  (defund vl-modulelist-everinstanced-exec (x acc)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (true-listp acc))
                    :verify-guards nil))
    (if (atom x)
        acc
      (let* ((modinsts1 (vl-module->modinsts (car x)))
             (acc       (vl-modinstlist->modnames-exec modinsts1 acc)))
        (vl-modulelist-everinstanced-exec (cdr x) acc))))

  (definline vl-modulelist-everinstanced (x)
    (declare (xargs :guard (vl-modulelist-p x)
                    :verify-guards nil))
    (mbe :logic (vl-modinstlist->modnames (vl-modulelist->modinsts x))
         :exec (reverse (vl-modulelist-everinstanced-exec x nil))))

  (local (defthm lemma
           (implies (true-listp acc)
                    (true-listp (vl-modulelist-everinstanced-exec x acc)))
           :hints(("Goal" :in-theory (enable vl-modulelist-everinstanced-exec)))))

  (defthm vl-modulelist-everinstanced-exec-removal
    (implies (force (true-listp acc))
             (equal (vl-modulelist-everinstanced-exec x acc)
                    (append (rev (vl-modinstlist->modnames (vl-modulelist->modinsts x)))
                            acc)))
    :hints(("Goal" :in-theory (enable vl-modulelist-everinstanced-exec))))

  (verify-guards vl-modulelist-everinstanced-exec)
  (verify-guards vl-modulelist-everinstanced)

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-modinstlist->modnames-exec ACL2::*never-profile-ht*) t)
   (setf (gethash 'vl-modulelist-everinstanced-exec ACL2::*never-profile-ht*) t)
   (defun vl-modulelist-everinstanced (x)
     (nreverse (vl-modulelist-everinstanced-exec x nil))))
  (defttag nil))


(defsection vl-modulelist-meganames
  :parents (hierarchy)
  :short "@(call vl-modulelist-meganames) gather the names of every module that
is ever defined or instantiated in <tt>x</tt>, and returns them as an ordered
set."

  :long "<p>We give this function a funny name because it is rather weird.
After all, our basic notion of @(see completeness) is that every instanced
module should be defined.</p>

<p>@(call vl-modulelist-meganames) is really a mechanism that lets us ignore
the ill-formedness of module lists in certain cases.  In particular, it allows
us to admit functions like @(see vl-dependent-modules), which build up sets of
module names until a fixed point is reached, even when the module list might
not be complete.</p>"

  (defund vl-modulelist-meganames (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (mbe :logic
         (mergesort (append (vl-modulelist->names x)
                            (vl-modulelist-everinstanced x)))
         :exec
         (let* ((acc (vl-modulelist-everinstanced-exec x nil))
                (acc (vl-modulelist->names-exec x acc)))
           (mergesort acc))))

  (local (in-theory (enable vl-modulelist-meganames)))

  (defthm true-listp-of-vl-modulelist-meganames
    (true-listp (vl-modulelist-meganames x))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-modulelist-meganames
    (setp (vl-modulelist-meganames x)))

  (defthm string-listp-of-vl-modulelist-meganames
    (implies (force (vl-modulelist-p x))
             (string-listp (vl-modulelist-meganames x))))

  (defthm subsetp-equal-of-vl-modulelist->names
    (subsetp-equal (vl-modulelist->names x)
                   (vl-modulelist-meganames x))))



(defsection vl-module-complete-p
  :parents (hierarchy completeness)
  :short "@(call vl-module-complete-p) determines if every module that is
instantiated by <tt>x</tt> is defined in <tt>mods</tt>."

  :long "<p>We leave this function enabled, preferring to reason about it as a
subset check.</p>

<p>This function is not efficient, and carries out a linear search of
<tt>mods</tt> for every module instance of <tt>x</tt>.  See @(see
vl-fast-module-complete-p) for a faster alternative.</p>"

  (defun vl-module-complete-p (x mods)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods))))
    (let* ((instances (vl-module->modinsts x))
           (names     (vl-modinstlist->modnames instances)))
      (vl-has-modules names mods))))


(defsection vl-fast-has-modules-of-vl-modinstlist->modnames
  :parents (hierarchy completeness)
  :short "Fused (@(see vl-fast-has-modules) of @(see vl-modinstlist->modnames)"

  (defun vl-fast-has-modules-of-vl-modinstlist->modnames (x mods modalist)
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-has-modules (vl-modinstlist->modnames x) mods)
         :exec
         (or (atom x)
             (and (vl-fast-has-module (vl-modinst->modname (car x)) mods modalist)
                  (vl-fast-has-modules-of-vl-modinstlist->modnames (cdr x) mods modalist))))))


(defsection vl-fast-module-complete-p
  :parents (hierarchy completeness)
  :short "@(see vl-modalist)-optimized version of @(see vl-module-complete-p)."

  (definline vl-fast-module-complete-p (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))))
             (ignorable mods))
    (mbe :logic
         (vl-module-complete-p x mods)
         :exec
         (vl-fast-has-modules-of-vl-modinstlist->modnames
          (vl-module->modinsts x) mods modalist))))


(defsection vl-fast-has-modules-of-vl-modulelist-everinstanced
  :parents (hierarchy completeness)
  :short "Fused @(see vl-fast-has-modules) of @(see vl-modulelist-everinstanced)"

  (defun vl-fast-has-modules-of-vl-modulelist-everinstanced (x mods modalist)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (vl-has-modules (vl-modulelist-everinstanced x) mods)
         :exec
         (or (atom x)
             (and (vl-fast-has-modules-of-vl-modinstlist->modnames
                   (vl-module->modinsts (car x)) mods modalist)
                  (vl-fast-has-modules-of-vl-modulelist-everinstanced
                   (cdr x) mods modalist))))))


(defsection vl-modulelist-complete-p
  :parents (hierarchy completeness)
  :short "@(call vl-modulelist-complete-p) determines if every module that is
instantiated in <tt>x</tt> is defined in <tt>mods</tt>."

  :long "<p>We leave this function enabled, preferring to reason about it
as a subset check.</p>

<p>This function is slightly inefficient in that it will construct its own
@(see vl-modalist).  If you already have a modalist available to you, for
better performance see @(see vl-fast-modulelist-complete-p).</p>"

  (defun vl-modulelist-complete-p (x mods)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modulelist-p mods))))
    (mbe :logic
         (subsetp-equal (vl-modulelist-everinstanced x)
                        (vl-modulelist->names mods))
         :exec
         (b* ((modalist (vl-modalist mods))
              (result   (vl-fast-has-modules-of-vl-modulelist-everinstanced x mods modalist))
              (-        (fast-alist-free modalist)))
             result)))

  (defthm vl-modulelist-meganames-when-complete
    (implies (vl-modulelist-complete-p x x)
             (equal (vl-modulelist-meganames x)
                    (mergesort (vl-modulelist->names x))))
    :hints(("Goal" :in-theory (enable vl-modulelist-meganames)))))


(defsection vl-fast-modulelist-complete-p
  :parents (hierarchy completeness)
  :short "Faster alternative to @(see vl-modulelist-complete-p)."

  :long "<p>This improves upon @(see vl-modulelist-complete-p) by requiring you
to provide it with the modalist to use.</p>"

  (definline vl-fast-modulelist-complete-p (x mods modalist)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (mbe :logic
         (vl-modulelist-complete-p x mods)
         :exec
         (vl-fast-has-modules-of-vl-modulelist-everinstanced x mods modalist))))


(defsection vl-module-check-complete
  :parents (hierarchy completeness)
  :short "@(call vl-module-check-complete) annotates <tt>x</tt> with any
warnings about @(see completeness)."

  :long "<p>If <tt>x</tt> is incomplete, a fatal warning is added that says
which missing modules it instantiates.</p>"

  (defund vl-module-check-complete (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((when (vl-fast-module-complete-p x mods modalist))
          ;; No problems to report.
          x)
         ((vl-module x) x)
         (referenced (mergesort (vl-modinstlist->modnames x.modinsts)))
         (defined    (mergesort (vl-modulelist->names mods)))
         (bad        (difference referenced defined))
         (warnings   (cons (make-vl-warning
                            :type :vl-incomplete
                            :msg "~m0 attempts to instantiate undefined ~
                                  module~s1 ~&2."
                            :args (list x.name
                                        (if (vl-plural-p bad) "s" "")
                                        bad)
                            :fatalp t
                            :fn 'vl-module-check-complete)
                           x.warnings))
         (x-prime (change-vl-module x :warnings warnings)))
      x-prime))

  (local (in-theory (enable vl-module-check-complete)))

  (defthm vl-module-p-of-vl-module-check-complete
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (vl-module-check-complete x mods modalist))))

  (defthm vl-module->name-of-vl-module-check-complete
    (equal (vl-module->name (vl-module-check-complete x mods modalist))
           (vl-module->name x))))



(defsection vl-modulelist-check-complete
  :parents (hierarchy completeness)
  :short "Extends @(see vl-module-check-complete) to a list of modules."

;; BOZO why not use an aux function and make the completeness check build
;; its own modalist?

  (defprojection vl-modulelist-check-complete (x mods modalist)
    (vl-module-check-complete x mods modalist)
    :guard (and (vl-modulelist-p x)
                (vl-modulelist-p mods)
                (equal modalist (vl-modalist mods)))
    :result-type vl-modulelist-p)

  (defthm vl-modulelist->names-of-vl-modulelist-check-complete
    (equal (vl-modulelist->names (vl-modulelist-check-complete x mods modalist))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))


(defsection vl-modulelist-missing
  :parents (hierarchy missing)
  :short "@(call vl-modulelist-missing) gathers the names of any modules which
are instantiated in the module list <tt>x</tt> but are not defined in
<tt>x</tt>, and returns them as an ordered set."

  (defund vl-modulelist-missing (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (mbe :logic
         (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
               (defined   (mergesort (vl-modulelist->names x))))
           (difference mentioned defined))
         :exec

; Some minor optimizations.  Since we're sorting the instnames anyway, we don't
; need to pay the price of reversing them and can just use the exec function
; directly.

         (let* ((mentioned (mergesort (vl-modulelist-everinstanced-exec x nil)))

; Also, since we often work with sets of modules, we can try to avoid
; mergesorting the names when they are known to be a set.  At best, this
; allows us to avoid sorting the module names, and hence saves a bunch of
; consing.
;
; Of course, when this fails we incur the additional price of a setp check,
; which in principle is as bad as O(n) comparisons.  On the other hand, setp
; can fail early.  It seems likely that an unordered list will have elements
; near its head that are out of order.  So, even when the setp check fails, it
; may often be that it fails pretty quickly.

                (names     (vl-modulelist->names x))
                (defined   (redundant-mergesort names)))
           (difference mentioned defined))))

  (local (in-theory (enable vl-modulelist-missing)))

  (defthm true-listp-of-vl-modulelist-missing
    (true-listp (vl-modulelist-missing x))
    :rule-classes :type-prescription)

  (defthm string-listp-of-vl-modulelist-missing
    (implies (force (vl-modulelist-p x))
             (string-listp (vl-modulelist-missing x))))

  (defthm setp-of-vl-modulelist-missing
    (setp (vl-modulelist-missing x))))



(defsection vl-modulelist-toplevel
  :parents (hierarchy)
  :short "@(call vl-modulelist-toplevel) gathers the names of any modules which
are defined in the module list <tt>x</tt> but are never instantiated in
<tt>x</tt>, and returns them as an ordered set."

  (defund vl-modulelist-toplevel (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (mbe :logic
         (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
               (defined   (mergesort (vl-modulelist->names x))))
           (difference defined mentioned))
         :exec
         ;; Optimizations as in vl-modulelist-missing
         (let* ((mentioned (mergesort (vl-modulelist-everinstanced-exec x nil)))
                (names     (vl-modulelist->names x))
                (defined   (if (setp names) names (mergesort names))))
           (difference defined mentioned))))

  (local (in-theory (enable vl-modulelist-toplevel)))

  (defthm true-listp-of-vl-modulelist-toplevel
    (true-listp (vl-modulelist-toplevel x))
    :rule-classes :type-prescription)

  (defthm string-listp-of-vl-modulelist-toplevel
    (implies (force (vl-modulelist-p x))
             (string-listp (vl-modulelist-toplevel x))))

  (defthm setp-of-vl-modulelist-toplevel
    (setp (vl-modulelist-toplevel x)))

  (defthm vl-has-modules-of-vl-modulelist-toplevel
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (vl-modulelist-p mods)))
             (subsetp-equal (vl-modulelist-toplevel mods)
                            (vl-modulelist->names mods)))))



(defsection vl-modulelist-highlevel
  :parents (hierarchy)
  :short "@(call vl-modulelist-highlevel) gathers the names of any \"high
level\" modules and return them as an ordered set."

  :long "<p>We say a module is <b>top level</b> (@(see vl-modulelist-toplevel))
when it is never instantiated by another module.  Similarly, we say that
modules are <b>high level</b> when they are \"near the top level\".</p>

<p>@(call vl-modulelist-highlevel) gathers the names of all modules which are
within <tt>n</tt> levels of the top.  When <tt>n</tt> is relatively small,
these modules are possibly the \"big units\" in the chip.</p>

<p>Historic note.  This function was once used in the \"unreasonable modules
report.\" It may not be in use any more.</p>"

  (defund vl-modulelist-highlevel (x n)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (natp n))
                    :verify-guards nil))
    (if (zp n)
        nil
      (let ((top (vl-modulelist-toplevel x)))
        (union top
               (vl-modulelist-highlevel (vl-delete-modules top x)
                                        (- n 1))))))

  (local (in-theory (enable vl-modulelist-highlevel)))

  (defthm true-listp-of-vl-modulelist-highlevel
    (true-listp (vl-modulelist-highlevel x n))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-modulelist-highlevel
    (setp (vl-modulelist-highlevel x n)))

  (defthm string-listp-of-vl-modulelist-highlevel
    (implies (force (vl-modulelist-p x))
             (string-listp (vl-modulelist-highlevel x n)))))



(defsection vl-depalist-core-aux

; Parent is the name of some module that contains these modinsts.  Alist is a
; vl-depalist-p we are constructing.  Add "parent" to the list of parents for
; every module named in modinsts.

  (defund vl-depalist-core-aux (parent modinsts alist)
    (declare (xargs :guard (and (stringp parent)
                                (vl-modinstlist-p modinsts)
                                (alistp alist)
                                (vl-string-keys-p alist)
                                (vl-string-list-values-p alist))))
    (if (consp modinsts)
        (let* ((mod   (vl-modinst->modname (car modinsts)))
               (entry (cdr (hons-get mod alist))))
          (hons-acons mod
                      (cons parent entry)
                      (vl-depalist-core-aux parent (cdr modinsts) alist)))
      alist))

  (local (in-theory (enable vl-depalist-core-aux)))

  (defthm alistp-of-vl-depalist-core-aux
    (implies (force (alistp alist))
             (alistp (vl-depalist-core-aux parent modinsts alist))))

  (defthm vl-string-keys-p-of-vl-depalist-core-aux
    (implies (and (force (stringp parent))
                  (force (vl-modinstlist-p modinsts))
                  (force (vl-string-keys-p alist)))
             (vl-string-keys-p (vl-depalist-core-aux parent modinsts alist))))

  (defthm vl-string-list-values-p-of-vl-depalist-core-aux
    (implies (and (force (stringp parent))
                  (force (vl-modinstlist-p modinsts))
                  (force (vl-string-list-values-p alist)))
             (vl-string-list-values-p (vl-depalist-core-aux parent modinsts alist))))

  (defthm member-equal-of-hons-assoc-equal-of-vl-depalist-core-aux
    (iff (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core-aux parent modinsts alist))))
         (or (member-equal par (cdr (hons-assoc-equal child alist)))
             (and (equal par parent)
                  (member-equal child (vl-modinstlist->modnames modinsts)))))))



(defsection vl-depalist-core

; X is a list of modules.  Add all the bindings for each module into the alist.
; The resulting alist has values which are just ordinary lists, so we'll need
; to sort them eventually.

  (defund vl-depalist-core (x alist)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (alistp alist)
                                (vl-string-keys-p alist)
                                (vl-string-list-values-p alist))))
    (if (consp x)
        (vl-depalist-core (cdr x)
                          (vl-depalist-core-aux (vl-module->name (car x))
                                                (vl-module->modinsts (car x))
                                                alist))
      alist))

  (local (in-theory (enable vl-depalist-core)))

  (defthm vl-depalist-core-when-not-consp
    (implies (not (consp x))
             (equal (vl-depalist-core x acc)
                    acc)))

  (defthm alistp-of-vl-depalist-core
    (implies (force (alistp alist))
             (alistp (vl-depalist-core x alist))))

  (defthm vl-string-keys-p-of-vl-depalist-core
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-string-keys-p alist)))
             (vl-string-keys-p (vl-depalist-core x alist))))

  (defthm vl-string-list-values-p-of-vl-depalist-core
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-string-list-values-p alist)))
             (vl-string-list-values-p (vl-depalist-core x alist))))

  (local (defthm lemma1
           (implies (member-equal par (cdr (hons-assoc-equal child alist)))
                    (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist)))))))

  (local (defthm lemma2
           (implies (member-equal child
                                  (vl-modinstlist->modnames
                                   (vl-module->modinsts
                                    (vl-find-module par x))))
                    (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist)))))))

  (local (defthm lemma3
           (implies (not (member-equal name (vl-modulelist->names x)))
                    (not (vl-find-module name x)))
           :hints(("Goal" :in-theory (e/d (vl-find-module) ((force)))))))

  (defthm member-equal-of-assoc-of-vl-depalist-core
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (iff (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist))))
                  (or (member-equal par (cdr (hons-assoc-equal child alist)))
                      (member-equal child
                                    (vl-modinstlist->modnames
                                     (vl-module->modinsts
                                      (vl-find-module par x)))))))))



(defsection vl-depalist
  :parents (hierarchy)
  :short "Build a dependency graph for use in @(see vl-dependent-modules)."

  :long "<p>Given a list of modules <tt>x</tt>, whose names are unique, @(call
vl-depalist) constructs a fast association list which maps each module name in
<tt>x</tt> to an ordered set of the names of its parents.  A more precise
description is given by the following theorem:</p>

  @(thm correctness-of-vl-depalist)

<p>This alist is useful in dependency computations such as @(see
vl-dependent-module).  It satisfies @(see alistp), @(see vl-depalist-p), and
@(see vl-set-values-p).</p>"

  (defund vl-depalist (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((unsorted (vl-depalist-core x nil))
         (shrunk   (hons-shrink-alist unsorted nil))
         (-        (flush-hons-get-hash-table-link unsorted))
         (-        (flush-hons-get-hash-table-link shrunk))
         (sorted   (vl-mergesort-values shrunk)))
      sorted))

  (local (in-theory (enable vl-depalist)))

  (defthm vl-depalist-when-not-consp
    (implies (not (consp x))
             (equal (vl-depalist x)
                    nil)))

  (defthm alistp-of-vl-depalist
    (alistp (vl-depalist x)))

  (defthm vl-string-keys-p-of-vl-depalist
    (implies (force (vl-modulelist-p x))
             (vl-string-keys-p (vl-depalist x))))

  (defthm vl-string-list-values-p-of-vl-depalist
    (implies (force (vl-modulelist-p x))
             (vl-string-list-values-p (vl-depalist x))))

  (defthm vl-set-values-p-of-vl-depalist
    (vl-set-values-p (vl-depalist x)))

  (defthm correctness-of-vl-depalist
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (equal (in parent (cdr (hons-assoc-equal child (vl-depalist x))))
                    (if (member-equal child
                                      (vl-modinstlist->modnames
                                       (vl-module->modinsts
                                        (vl-find-module parent x))))
                        t
                      nil)))))



(defsection vl-dependent-modules-direct
  :parents (hierarchy)
  :short "@(call vl-dependent-modules-direct) gathers the names of all modules
in <tt>mods</tt> that directly instantiate any module in <tt>names</tt>, and
returns them as an ordered set."

  :long "<p>See @(see vl-dependent-modules) for some additional discussion.  In
short, this function produces the set of all modules which \"directly depend
on\" any module in <tt>names</tt>.</p>"

  (defund vl-dependent-modules-direct (names mods depalist)
    (declare (xargs :guard (and (setp names)
                                (string-listp names)
                                (vl-modulelist-p mods)
                                (setp mods)
                                (uniquep (vl-modulelist->names mods))
                                (equal depalist (vl-depalist mods)))
                    :verify-guards nil))
    (if (empty names)
        nil
      (union (cdr (hons-get (head names) depalist))
             (vl-dependent-modules-direct (tail names) mods depalist))))

  (local (in-theory (enable vl-dependent-modules-direct)))

  (defthm true-listp-of-vl-dependent-modules-direct
    (true-listp (vl-dependent-modules-direct names mods depalist))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm setp-of-vl-dependent-modules-direct
    (setp (vl-dependent-modules-direct names mods depalist))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-dependent-modules-direct-when-not-consp
    (implies (and (not (consp mods))
                  (force (equal depalist (vl-depalist mods))))
             (equal (vl-dependent-modules-direct names mods depalist)
                    nil)))

  (defthm string-listp-of-vl-dependent-modules-direct
    (implies (force (vl-string-list-values-p depalist))
             (string-listp (vl-dependent-modules-direct names mods depalist))))

  (local (defthm lemma1
           (implies (not (vl-has-module name mods))
                    (equal (vl-find-module name mods)
                           nil))
           :hints(("Goal" :in-theory (e/d (vl-find-module)
                                          ((force)))))))

  (local (defthm lemma2
           (implies (and (vl-has-module name mods)
                         (setp mods)
                         (vl-modulelist-p mods)
                         (no-duplicatesp-equal (vl-modulelist->names mods)))
                    (in name (vl-modulelist->names mods)))))

  (local (defthm lemma3
           (implies (and (setp mods)
                         (vl-modulelist-p mods)
                         (no-duplicatesp-equal (vl-modulelist->names mods))
                         (vl-modulelist-complete-p mods mods)
                         (member-equal a (vl-modinstlist->modnames (vl-module->modinsts (vl-find-module name mods)))))
                    (in name (vl-modulelist->names mods)))
           :hints(("goal"
                   :cases ((vl-find-module name mods))
                   :in-theory (disable promote-member-equal-to-membership)))))

  (defthm subset-of-vl-dependent-modules-direct-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (setp mods))
                  (force (setp names))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (subset names (vl-modulelist-meganames mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules-direct names mods depalist)
                     (vl-modulelist->names mods))))

  (local (defthm lemma4
           (implies (member-equal a (vl-modinstlist->modnames (vl-module->modinsts (vl-find-module b mods))))
                    (member-equal b (vl-modulelist->names mods)))))

  (local (defthm lemma5
           (implies (member-equal a (vl-modinstlist->modnames (vl-module->modinsts (vl-find-module b mods))))
                    (in b (vl-modulelist-meganames mods)))
           :hints(("Goal" :in-theory (enable vl-modulelist-meganames)))))

  (defthm subset-of-vl-dependent-modules-direct-and-meganames
    (implies (and (force (setp mods))
                  (force (setp names))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (subset names (vl-modulelist-meganames mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules-direct names mods depalist)
                     (vl-modulelist-meganames mods)))
    :hints(("Goal" :induct (vl-dependent-modules-direct names mods depalist))))

  (verify-guards vl-dependent-modules-direct))



(defsection vl-dependent-modules-aux
  :parents (vl-dependent-modules)
  :short "Recursive closure of @(see vl-dependent-modules-direct)."
  :long "<p>@(call vl-dependent-modules-aux) produces a set of names.</p>

<h3>Overview</h3>

<p>Inputs:</p>
<ul>
  <li><tt>prev</tt> and <tt>curr</tt> are sets of module names</li>
  <li><tt>mods</tt> is a set of modules with unique names</li>
  <li><tt>depalist</tt> is the precomputed @(see vl-depalist) for <tt>mods</tt></li>
</ul>

<p>Note additionally that we assume every module named in <tt>prev</tt> and
<tt>curr</tt> is defined in <tt>mods</tt>, and that the list of modules are
@(see vl-modulelist-complete-p) so that every module which is ever instanced is
also in <tt>mods</tt>.</p>

<p>At a high level, the goal of this function is to compute the set of all
dependents of <tt>prev U curr</tt>.  The computation proceeds iteratively
by searching for new dependents and expanding <tt>prev U curr</tt> until a
fixed point is reached.</p>

<p>The separation between <tt>prev</tt> and <tt>curr</tt> is a useful device
for limiting where we are going to look next.  In particular, we assume as an
invariant that every direct dependent of any member of <tt>prev</tt> is already
in <tt>prev U curr</tt>.  Because of this, we do not need to look for any new,
direct dependents of <tt>prev</tt>, and can just focus on <tt>curr</tt>.</p>

<p>The algorithm proceeds as follows.  First, we look up the direct dependents
of <tt>curr</tt>.  Call these dependents <tt>newinsts</tt>.  If all of these
<tt>newinsts</tt> are already in <tt>curr U prev</tt>, we have reached a fixed point
and we can stop.</p>

<p>Otherwise, we wish to recur.  Taking the high-level view once again, our new
set is <tt>newinsts U curr U prev</tt>.  However, in the recursive call we set
<tt>prev</tt> to <tt>curr U prev</tt>, since all of their direct dependents
have now been accounted for.  The new value of <tt>curr</tt> is then simply
<tt>newinsts - (curr U prev)</tt>.</p>

<h3>Termination</h3>

<p>The proof of admission is somewhat involved, so we sketch it at a high
level, here.</p>

<h5>Goal</h5>

<code>
   (not (Newinsts \\subseteq (Curr U Prev)))
     --&gt;
   |Modnames - (Curr U Prev)| &gt;= |Modnames - (Newinsts U Curr U Prev)|
</code>

<h5>Proof</h5>

<p>First, note that:</p>
<code>
   |Modnames - (Curr U Prev)|
      = |Modnames| - |(Curr U Prev) \\cap Modnames|

   |Modnames - (Newinsts U Curr U Prev)|
      = |Modnames| - |(Newinsts U Curr U Prev) \\cap Modnames|
</code>

<p>So our goal simplifies to:</p>
<code>
    - |(Curr U Prev) \\cap Modnames| &gt;= - |(Newinsts U Curr U Prev) \\cap Modnames|
</code>

<p>Which is just:</p>
<code>
    |(Curr U Prev) \\cap Modnames| &lt;= |(Newinsts U Curr U Prev) \\cap Modnames|
</code>

<p>We claim this follows from two facts.  First, the left-hand side is
trivially a subset of the right-hand side.  Second, as we demonstrate below,
that there is an element in the right-hand side which is not in the left-hand
side.  In other words, the rhs is a proper superset of the lhs, hence it has
greater cardinality.</p>

<p>To see the existence of such an element, let <tt>e</tt> be a member of
<tt>Newinsts - (Curr U Prev)</tt>.  We know such an <tt>e</tt> exists because
our hypothesis is that <tt>Newinsts</tt> is not a subset of <tt>(Curr U
Prev)</tt>.  Furthermore, <tt>e</tt> is in <tt>modnames</tt> because
<tt>Newinsts</tt> is a subset of <tt>modnames</tt>.  Hence <tt>e</tt> is in the
right-hand side, but not in the left-hand side.</p>

<p><i>Q.E.D.</i></p>"

  (defsection admission-lemma-1

    (local (defthm lemma1
             (implies (and (subset newinsts modnames)
                           (not (subset newinsts (union curr prev))))
                      (subset (intersect (union curr prev) modnames)
                              (intersect (union newinsts (union curr prev))
                                         modnames)))))


    (local (defthm crock
             (implies (and (not (empty newinsts))
                           (not (in (head newinsts) other))
                           (in (head newinsts) modnames)
                           (subset (tail newinsts) modnames))
                      (not (subset (intersect modnames newinsts)
                                   (intersect modnames other))))))

    (local (defthm crock2
             (implies (not (subset (intersect modnames (tail newinsts))
                                   (intersect modnames other)))
                      (not (subset (intersect modnames newinsts)
                                   (intersect modnames other))))))

    (local (defthmd crock3
             (implies (and (subset newinsts modnames)
                           (not (subset newinsts other)))
                      (not (subset (intersect (union newinsts other) modnames)
                                   (intersect other modnames))))))

    (local (defthm lemma2
             (implies (and (subset newinsts modnames)
                           (not (subset newinsts (union curr prev))))
                      (not (subset (intersect (union newinsts (union curr prev))
                                              modnames)
                                   (intersect (union curr prev)
                                              modnames))))
             :hints(("goal" :by crock3))))

    (defthmd vl-dependent-mods-admission-lemma1
      (implies (and (subset newinsts modnames)
                    (not (subset newinsts (union curr prev))))
               (< (cardinality (intersect (union curr prev) modnames))
                  (cardinality (intersect (union newinsts (union curr prev)) modnames))))
      :hints(("Goal"
              :use ((:instance sets::proper-subset-cardinality
                               (sets::x (intersect (union curr prev) modnames))
                               (sets::y (intersect (union newinsts (union curr prev)) modnames)))
                    (:instance lemma2)
                    (:instance lemma1))))))


  (defsection admission-lemma-2

    (local (defthm intersect-intersect-rw
             (equal (intersect (difference x y)
                               (difference x z))
                    (difference x (union y z)))))

    (local (in-theory (disable sets::difference-over-union)))

    (local (defthm note1
             (equal (cardinality (difference x (union y z)))
                    (- (cardinality x)
                       (cardinality (intersect (union y z) x))))))

    ;; We re-prove <-minus-minus from arithmetic-3.  This is really easy and lets
    ;; us avoid the arith-3 dependency.

    (local (defthmd lemma-for-<-minus-minus
             (equal (equal (< a b) (< c d))
                    (iff (< a b) (< c d)))))

    (local (defthm <-minus-minus
             (equal (< (- x) (- y))
                    (< y x))
             :hints(("Goal" :in-theory (enable lemma-for-<-minus-minus)))))

    (local (defthm union-of-difference-of-self
             (equal (union a (difference b a))
                    (union a b))))

    (local  (defthm union-of-union-of-difference-of-self
              (equal (union a (union b (difference c a)))
                     (union a (union b c)))))

    (local  (defthm union-of-intersect-and-union
              (equal (union (intersect a b)
                            (intersect a c))
                     (intersect a (union b c)))))

    (local  (in-theory (disable sets::intersect-over-union)))

    (defthmd vl-dependent-mods-admission-lemma2
      (implies (and (subset newinsts modnames)
                    (not (subset newinsts (union curr prev))))
               (< (cardinality (union (intersect (difference modnames curr)
                                                 (intersect (difference modnames prev)
                                                            (difference modnames (difference newinsts curr))))
                                      (intersect (difference modnames curr)
                                                 (intersect (difference modnames prev)
                                                            (difference modnames (difference newinsts prev))))))
                  (cardinality (intersect (difference modnames curr)
                                          (difference modnames prev)))))
      :hints(("Goal"
              :in-theory (disable vl-dependent-mods-admission-lemma1)
              :use ((:instance vl-dependent-mods-admission-lemma1
                               (modnames modnames)
                               (curr curr)
                               (prev prev)
                               (newinsts newinsts)))))))


  (defund vl-dependent-modules-aux (curr prev mods depalist)
    (declare (xargs :guard (and (setp curr)
                                (setp prev)
                                (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (setp mods)
                                (subset curr (vl-modulelist-meganames mods))
                                (subset prev (vl-modulelist-meganames mods))
                                (equal depalist (vl-depalist mods)))
                    :verify-guards nil
                    :measure (cardinality
                              (difference (vl-modulelist-meganames (sfix mods))
                                          (union curr prev)))

                    :hints (("Goal"
                             :in-theory (disable (:linear sets::expand-cardinality-of-difference)
                                                 (:rewrite sets::expand-cardinality-of-union))
                             :do-not '(generalize fertilize)
                             :do-not-induct t
                             :use ((:instance vl-dependent-mods-admission-lemma2
                                              (modnames (vl-modulelist-meganames (sfix mods)))
                                              (curr curr)
                                              (newinsts (mergesort (vl-dependent-modules-direct curr (sfix mods) depalist)))
                                              (prev prev)))))))

    (let* ((mods      (mbe :logic (sfix mods) :exec mods))
           (newinsts  (vl-dependent-modules-direct curr mods depalist))
           (curr+prev (union curr prev)))
      (cond

       ;; Termination helper.  Never gets executed.
       ((mbe :logic (not (subset (union curr prev) (vl-modulelist-meganames mods)))
             :exec nil)
        curr+prev)

       ;; Termination helper.  Never gets executed.
       ((mbe :logic (not (subset newinsts (vl-modulelist-meganames mods)))
             :exec nil)
        curr+prev)

       ;; Fixed point reached.  Return the set we've built so far.
       ((subset newinsts curr+prev)
        curr+prev)

       ;; No fixed point.  Continue looking for more modules.
       (t
        (vl-dependent-modules-aux (difference newinsts curr+prev)
                                  curr+prev mods depalist)))))

  (local (in-theory (enable vl-dependent-modules-aux)))

  (defthm setp-of-vl-dependent-modules-aux
    (setp (vl-dependent-modules-aux curr prev mods depalist))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm string-listp-of-vl-dependent-modules-aux
    (implies (and (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (subset curr (vl-modulelist-meganames mods)))
                  (force (subset prev (vl-modulelist-meganames mods)))
                  (force (equal depalist (vl-depalist mods))))
             (string-listp (vl-dependent-modules-aux curr prev mods depalist))))

  (defthm subset-of-vl-dependent-modules-aux-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (subset curr (vl-modulelist-meganames mods)))
                  (force (subset prev (vl-modulelist-meganames mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules-aux curr prev mods depalist)
                     (vl-modulelist->names mods))))

  (defthm subset-of-vl-dependent-modules-aux-and-meganames
    (implies (and (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (subset curr (vl-modulelist-meganames mods)))
                  (force (subset prev (vl-modulelist-meganames mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules-aux curr prev mods depalist)
                     (vl-modulelist-meganames mods))))

  (verify-guards vl-dependent-modules-aux))




(defsection vl-dependent-modules
  :parents (hierarchy)
  :short "@(call vl-dependent-modules) gathers the names of all modules in
<tt>mods</tt> which, transitively, instantiate any module in <tt>names</tt>,
and returns them as an ordered set."

  :long "<p>We define the <i>depends on</i> relationship for modules as
follows.</p>

<ul>
 <li>Each module depends on itself, and</li>
 <li>If M instantiates A, and A depends on B, then M depends on B.</li>
</ul>

<p>This is an important relationship.  For instance, if we want to remove M
from our list of modules, we typically need to throw away the modules that
depend on M, as well.</p>

<p><tt>vl-dependent-modules</tt> is the main function for gathering dependent
modules.  It takes as arguments:</p>

<ul>
 <li><tt>names</tt>, a list of module names,</li>
 <li><tt>x</tt>, an ordered set of modules with unique names, and</li>
 <li><tt>depalist</tt>, the pre-computed @(see vl-depalist) for <tt>x</tt>.</li>
</ul>

<p>It produces a set of strings which are the names of all modules that depend
on any module in <tt>names</tt>.  Note that this set will include every member
of <tt>names</tt>, since, per the above definition, every module depends upon
itself.</p>"

  (defund vl-dependent-modules (names mods depalist)
    (declare (xargs :guard (and (string-listp names)
                                (setp mods)
                                (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (equal depalist (vl-depalist mods)))
                    :verify-guards nil))
    (mbe :logic
         (vl-dependent-modules-aux
          (intersect (mergesort names) (vl-modulelist-meganames mods))
          nil mods depalist)
         :exec

; We implement a variety of optimizations.  First, if the given names already
; happen to be sorted, don't bother to sort them again.  This is usually not
; too expensive when it fails, and may save some consing when it succeeds.

         (let* ((sorted-names (redundant-mergesort names))
                (modnames     (vl-modulelist->names mods)))

; Next, since it requires so much consing, we would really like to avoid
; computing vl-modulelist-meganames if possible.  Unfortunately, we need to
; ensure that curr and prev are subsets of meganames for the guard of
; vl-dependent-modules-aux.
;
; If the module list is complete, as it often is, then the meganames are just
; the module names.  So, we think it is likely that the names are a subset of
; (vl-modulelist->names mods).  Since (by our guard) the modules are a set and
; have unique names, the names are already unique.

           (if (subset sorted-names modnames)
               (vl-dependent-modules-aux sorted-names nil mods depalist)

; If we get to here, then we are asking for dependents of undefined modules,
; perhaps becuase the module list is incomplete or just because we are asking
; for the dependents of modules that just are not defined anywhere.  There's
; no good way that I can think of to avoid computing the meganames in this
; case, but I'll at least print a message.

             (prog2$
              (cw "; Performance warning in vl-dependent-modules: computing ~
                   vl-modulelist-meganames to try to find undefined modules ~
                   ~&0."
                  (difference sorted-names modnames))
              (vl-dependent-modules-aux
               (intersect sorted-names (vl-modulelist-meganames mods))
               nil mods depalist))))))

  (local (in-theory (enable vl-dependent-modules)))

  (local (defthm crock
           (implies (subsetp-equal names (vl-modulelist->names mods))
                    (equal (intersect (mergesort names) (vl-modulelist-meganames mods))
                           (mergesort names)))
           :hints(("goal" :in-theory (enable vl-modulelist-meganames)))))

  (verify-guards vl-dependent-modules)

  (defthm setp-of-vl-dependent-modules
    (setp (vl-dependent-modules names mods depalist)))

  (defthm string-listp-of-vl-dependent-modules
    (implies (and (force (string-listp names))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (equal depalist (vl-depalist mods))))
             (string-listp (vl-dependent-modules names mods depalist))))

  (defthm subset-of-vl-dependent-modules-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (string-listp names))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules names mods depalist)
                     (vl-modulelist->names mods))))

  (defthm subset-of-vl-dependent-modules-and-meganames
    (implies (and (force (string-listp names))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (equal depalist (vl-depalist mods))))
             (subset (vl-dependent-modules names mods depalist)
                     (vl-modulelist-meganames mods))))

  ;; We might want to try to prove some additional theorems that suggest
  ;; vl-dependent-modules is correct.  For example, its "soundness" might be
  ;; stated as follows:
  ;;
  ;;   If mods are complete, then deleting (vl-dependent-modules names mods)
  ;;   from mods is also complete.
  ;;
  ;; And its "completeness" might be stated like this:
  ;;
  ;;   If mods are complete and mods - (names U ext) is also complete, then
  ;;   (names U ext) is a superset of (vl-dependent-modules names mods).
  ;;
  ;; Which can be understood to mean, "no deletion from mods which includes
  ;; names is complete unless it deletes all of the dependent modules of
  ;; names."

  )



(defsection vl-necessary-direct-for-module
  :parents (vl-necessary-modules)
  :short "@(call vl-necessary-direct-for-module) gathers the names of all
modules which are directly instantiated by the module <tt>x</tt>, and returns
them as an ordered set."

  :long "<p>Logically, this function is nothing more than</p>

<code>
  (mergesort (vl-modinstlist-&gt;modnames (vl-module-&gt;modinsts x)))
</code>

<p>However, memoizing this function provides an efficiency boost to @(see
vl-necessary-modules).</p>"

  (defund vl-necessary-direct-for-module (x)
    (declare (xargs :guard (vl-module-p x)))
    (mbe :logic
         (mergesort (vl-modinstlist->modnames (vl-module->modinsts x)))
         :exec
         ;; Very minor efficiency tweak: avoid the reverse
         (mergesort (vl-modinstlist->modnames-exec (vl-module->modinsts x) nil))))

  (memoize 'vl-necessary-direct-for-module)

  (local (in-theory (enable vl-necessary-direct-for-module)))

  (defthm setp-of-vl-necessary-direct-for-module
    (setp (vl-necessary-direct-for-module x)))

  (defthm string-listp-of-vl-necessary-direct-for-module
    (implies (force (vl-module-p x))
             (string-listp (vl-necessary-direct-for-module x)))))



(defsection vl-necessary-modules-direct-slow
  :parents (vl-necessary-modules)
  :short "@(call vl-necessary-modules-direct-slow) gathers the names of all
modules in <tt>mods</tt> which are directly instanced by any module in
<tt>names</tt>, and returns them as an ordered set."

  :long "<p>This is a logically simple function which we do not typically
run.  See @(see vl-fast-necessary-modules) for a faster alternative which use a
@(see vl-modalist) for faster lookups.</p>

<p>See also @(see vl-necessary-modules) for some additional discussion.</p>"

  (defund vl-necessary-modules-direct-slow (names mods)
    (declare (xargs :guard (and (setp names)
                                (string-listp names)
                                (vl-modulelist-p mods))
                    :verify-guards nil))
    (if (empty names)
        nil
      (let* ((mod (vl-find-module (head names) mods)))
        (union (if mod
                   (vl-necessary-direct-for-module mod)
                 nil)
               (vl-necessary-modules-direct-slow (tail names) mods)))))

  (local (in-theory (enable vl-necessary-modules-direct-slow)))

  (defthm true-listp-of-vl-necessary-modules-direct-slow
    (true-listp (vl-necessary-modules-direct-slow names mods))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-necessary-modules-direct-slow
    (setp (vl-necessary-modules-direct-slow names mods)))

  (defthm string-listp-of-vl-necessary-modules-direct-slow
    (implies (and (force (string-listp names))
                  (force (vl-modulelist-p mods)))
             (string-listp (vl-necessary-modules-direct-slow names mods))))

  (local (defthm stringp-when-in-vl-modulelist->names
           (implies (and (in a (vl-modulelist->names x))
                         (force (vl-modulelist-p x)))
                    (stringp a))
           :hints(("Goal" :in-theory (enable sets::primitive-reasoning
                                             vl-modulelist->names)))))

  (verify-guards vl-necessary-modules-direct-slow)


  (local (defthm vl-module-complete-p-when-member-of-complete-list-1
           ;; This is really: if X is complete in Y, and mod is in X, then
           ;; mod is complete in Y.  But we write out the definitions in their
           ;; expanded forms, since we leave the definitions of completeness
           ;; enabled and the free variables make things delicate.
           (implies (and (subsetp-equal (vl-modinstlist->modnames
                                         (vl-modulelist->modinsts x))
                                        (vl-modulelist->names y))
                         (member-equal mod X))
                    (subsetp-equal (vl-modinstlist->modnames (vl-module->modinsts mod))
                                   (vl-modulelist->names y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm vl-module-complete-p-when-member-of-complete-list-2
           ;; This is the same as the above, but with the hyps flipped for better
           ;; free variable matching.
           (implies (and (member-equal mod X)
                         (subsetp-equal (vl-modinstlist->modnames (vl-modulelist->modinsts x))
                                        (vl-modulelist->names y)))
                    (subsetp-equal (vl-modinstlist->modnames (vl-module->modinsts mod))
                                   (vl-modulelist->names y)))))

  (local (defthm lemma-3
           (implies (member-equal name (vl-modulelist->names mods))
                    (member-equal (vl-find-module name mods) mods))
           :hints(("Goal"
                   :induct (len mods)
                   :in-theory (disable (force))))))

  (local (in-theory (enable vl-necessary-direct-for-module)))

  (defthm subset-of-vl-necessary-modules-direct-slow-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (subset (vl-necessary-modules-direct-slow names mods)
                     (vl-modulelist->names mods))))


  (local (defthm lemma-4
           (implies (and (vl-modulelist-p x)
                         (member-equal mod x)
                         (member-equal b (vl-modinstlist->modnames (vl-module->modinsts mod))))
                    (member-equal b (vl-modinstlist->modnames (vl-modulelist->modinsts x))))
           :hints(("Goal" :induct (len x)))))

  (local (defthm lemma-5
           (implies (and (vl-modulelist-p x)
                         (member-equal a (vl-modulelist->names x))
                         (member-equal b (vl-modinstlist->modnames
                                          (vl-module->modinsts (vl-find-module a x)))))
                    (in b (vl-modulelist-meganames x)))
           :hints(("goal"
                   :in-theory (e/d (vl-modulelist-meganames)
                                   (lemma-4))
                   :use ((:instance lemma-4
                                    (x x)
                                    (mod (vl-find-module a x))
                                    (b b)))))))

  (defthm subset-of-vl-necessary-modules-direct-slow-and-meganames
    (implies (force (vl-modulelist-p mods))
             (subset (vl-necessary-modules-direct-slow names mods)
                     (vl-modulelist-meganames mods)))))



(defsection vl-necessary-modules-direct-fast
  :parents (vl-necessary-modules)
  :short "@(see vl-modalist)-optimized version of @(see vl-necessary-modules-direct-slow)."

  (defun vl-necessary-modules-direct-fast (names mods modalist)
    (declare (xargs :guard (and (setp names)
                                (string-listp names)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))
                    :guard-hints (("Goal" :in-theory (enable vl-necessary-modules-direct-fast
                                                             vl-necessary-modules-direct-slow)))))
    (mbe :logic
         (vl-necessary-modules-direct-slow names mods)
         :exec
         (if (empty names)
             nil
           (let* ((mod (vl-fast-find-module (head names) mods modalist)))
             (union (if mod
                        (vl-necessary-direct-for-module mod)
                      nil)
                    (vl-necessary-modules-direct-fast (tail names) mods modalist)))))))



(defsection vl-necessary-modules-aux

; This is like vl-dependent-modules-aux, but for vl-necessary-modules
; instead.  Prev and curr are lists of module names, and mods is the entire
; list of modules.
;
; We are trying to compute the set of all modules which are necessary for
; curr and prev.  We assume that all of prev's directly-instantiated modules
; are already found within (curr U prev).
;
; So, we are looking for modules which are instantiated by modules in curr.
; If all of these are already in curr U prev, we have reached a fixed point
; and we can stop.
;
; Otherwise, newinsts - (curr U prev) contains all directly instantiated
; modules for (curr U prev), so we can recursively begin looking for these
; modules.

  (defund vl-necessary-modules-aux (curr prev mods modalist)
    (declare (xargs :guard (and (setp curr)
                                (setp prev)
                                (setp mods)
                                (string-listp prev)
                                (string-listp curr)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (uniquep (vl-modulelist->names mods))
                                (subset curr (vl-modulelist-meganames mods))
                                (subset prev (vl-modulelist-meganames mods)))
                    :verify-guards nil
                    :measure (cardinality
                              (difference (vl-modulelist-meganames (sfix mods))
                                          (union curr prev)))
                    :hints
                    (("Goal"
                      :in-theory (disable (:linear sets::expand-cardinality-of-difference)
                                          (:rewrite sets::expand-cardinality-of-union))
                      :do-not '(generalize fertilize)
                      :do-not-induct t
                      :use ((:instance vl-dependent-mods-admission-lemma2
                                       (modnames (vl-modulelist-meganames (sfix mods)))
                                       (curr curr)
                                       (newinsts (vl-necessary-modules-direct-fast curr (sfix mods) modalist))
                                       (prev prev)))))))

    (let* ((mods      (mbe :logic (sfix mods) :exec mods))
           (newinsts  (vl-necessary-modules-direct-fast curr mods modalist))
           (curr+prev (union curr prev)))
      (cond
       ;; Termination helper.  Never gets executed.
       ((mbe :logic (not (subset (union curr prev) (vl-modulelist-meganames mods)))
             :exec nil)
        curr+prev)

       ;; Termination helper.  Never gets executed.
       ((mbe :logic (not (subset newinsts (vl-modulelist-meganames mods)))
             :exec nil)
        curr+prev)

       ;; Fixed point reached.  Return the set we've built so far.
       ((subset newinsts curr+prev)
        curr+prev)

       ;; New modules added.  Continue adding their instances.
       (t
        (vl-necessary-modules-aux (difference newinsts curr+prev)
                                  curr+prev mods modalist)))))

  (local (in-theory (enable vl-necessary-modules-aux)))

  (defthm setp-of-vl-necessary-modules-aux
    (setp (vl-necessary-modules-aux curr prev mods modalist))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm string-listp-of-vl-necessary-modules-aux
    (implies (and (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (string-listp prev))
                  (force (string-listp curr))
                  (force (vl-modulelist-p mods))
                  (force (equal (vl-modalist mods) modalist)))
             (string-listp (vl-necessary-modules-aux curr prev mods modalist))))

  (defthm subset-of-vl-necessary-modules-aux-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (string-listp prev))
                  (force (string-listp curr))
                  (force (equal (vl-modalist mods) modalist))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (subset curr (vl-modulelist-meganames mods)))
                  (force (subset prev (vl-modulelist-meganames mods))))
             (subset (vl-necessary-modules-aux curr prev mods modalist)
                     (vl-modulelist->names mods)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :induct (vl-necessary-modules-aux curr prev mods modalist))))

  (defthm subset-of-vl-necessary-modules-aux-and-meganames
    (implies (and (force (setp curr))
                  (force (setp prev))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (string-listp prev))
                  (force (string-listp curr))
                  (force (equal (vl-modalist mods) modalist))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (subset curr (vl-modulelist-meganames mods)))
                  (force (subset prev (vl-modulelist-meganames mods))))
             (subset (vl-necessary-modules-aux curr prev mods modalist)
                     (vl-modulelist-meganames mods)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :induct (vl-necessary-modules-aux curr prev mods modalist))))

  (verify-guards vl-necessary-modules-aux))



(defsection vl-necessary-modules
  :parents (hierarchy)
  :short "@(call vl-necessary-modules) gathers the names of all modules in
<tt>mods</tt> which, transitively, are instantiated by any module in
<tt>names</tt>, and returns them as an ordered set."

    :long "<p>We define the <i>necessary for</i> relationship for modules as
follows.</p>

<ul>
 <li>M is necessary for itself</li>
 <li>If M instantiates A, then A is necessary for M</li>
 <li>If M instantiates A, and B is necessary for A, then B is also
      necessary for M.</li>
</ul>

<p>In other words, the necessary modules are all of the modules that are needed
in order for M to be fully defined.</p>"

  (defund vl-necessary-modules (names mods modalist)
    (declare (xargs :guard (and (string-listp names)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (setp mods)
                                (uniquep (vl-modulelist->names mods)))
                    :verify-guards nil))
    (mbe :logic
         (vl-necessary-modules-aux
          (intersect (mergesort names) (vl-modulelist-meganames mods))
          nil mods modalist)
         :exec

; We implement a variety of optimizations.  First, if the given names already
; happen to be sorted, don't bother to sort them again.  This is usually not
; too expensive when it fails, and may save some consing when it succeeds.

         (let* ((sorted-names (redundant-mergesort names))
                (modnames     (vl-modulelist->names mods)))

; Next, since it requires so much consing, we would really like to avoid
; computing vl-modulelist-meganames if possible.  Unfortunately, we need to
; ensure that curr and prev are subsets of meganames for the guards of
; vl-necessary-modules-aux.
;
; If the module list is complete, as it often is, then the meganames are just
; the module names.  So, we think it is likely that the names are a subset of
; (vl-modulelist->names mods).  We do not need to mergesort the names since, by
; our guard, the modules are a set and have unique names.

           (if (subset sorted-names modnames)
               (vl-necessary-modules-aux sorted-names nil mods modalist)

; If we get to here, then we are asking for dependents of undefined modules,
; perhaps becuase the module list is incomplete or just because we are asking
; for the dependents of modules that just are not defined anywhere.  There's
; no good way that I can think of to avoid computing the meganames in this
; case, but I'll at least print a message.

             (prog2$
              (cw "; Performance warning in vl-necessary-modules: computing ~
                   vl-modulelist-meganames to try to find undefined modules ~
                   ~&0."
                  (difference sorted-names modnames))
              (vl-necessary-modules-aux
               (intersect sorted-names (vl-modulelist-meganames mods))
               nil mods modalist))))))

  (local (in-theory (enable vl-necessary-modules)))

  (local (defthm crock
           (implies (subsetp-equal names (vl-modulelist->names mods))
                    (equal (intersect (mergesort names) (vl-modulelist-meganames mods))
                           (mergesort names)))
           :hints(("goal" :in-theory (enable vl-modulelist-meganames)))))

  (verify-guards vl-necessary-modules)

  (defthm setp-of-vl-necessary-modules
    (setp (vl-necessary-modules names mods modalist)))

  (defthm string-listp-of-vl-necessary-modules
    (implies (and (force (string-listp names))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (setp mods)))
             (string-listp (vl-necessary-modules names mods modalist))))

  (defthm subset-of-vl-necessary-modules-when-complete
    (implies (and (vl-modulelist-complete-p mods mods)
                  (force (string-listp names))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (setp mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-has-modules names mods)))
             (subset (vl-necessary-modules names mods modalist)
                     (vl-modulelist->names mods))))

  (defthm subset-of-vl-necessary-modules-and-meganames
    (implies (and (force (string-listp names))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (setp mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (subset (vl-necessary-modules names mods modalist)
                     (vl-modulelist-meganames mods)))))



(defsection vl-remove-unnecessary-modules
  :parents (hierarchy)
  :short "@(call vl-remove-unnecessary-modules) throws away any modules in
<tt>mods</tt> which are not necessary for the modules named in <tt>keep</tt>."

  :long "<p>Historically this function was used to implement the \"modules of
interest\" feature, which allowed us to throw away modules that we were not
interested in to speed up translation.  But it no longer seems to be used.</p>"

  (defund vl-remove-unnecessary-modules (keep mods)
    (declare (xargs :guard (and (string-listp keep)
                                (vl-modulelist-p mods)
                                (setp mods)
                                (uniquep (vl-modulelist->names mods)))))
    (b* ((modalist    (vl-modalist mods))
         (necessary   (vl-necessary-modules keep mods modalist))
         (-           (fast-alist-free modalist))
         (unnecessary (difference (vl-modulelist->names mods) necessary)))
      (vl-delete-modules unnecessary mods)))

  (local (in-theory (enable vl-remove-unnecessary-modules)))

  (defthm vl-modulelist-p-of-vl-remove-unnecessary-modules
    (implies (and (force (string-listp keep))
                  (force (vl-modulelist-p mods))
                  (force (setp mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (vl-modulelist-p (vl-remove-unnecessary-modules keep mods))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-remove-unnecessary-modules
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (vl-remove-unnecessary-modules keep x))))))




;                         DEPENDENCY ORDERING
;
; We now introduce a routine to sort modules into dependency order.
;

(defsection vl-deporder-alistp
  :parents (vl-deporder)
  :short "Alist that associates module names to their levels in the
instantiation hierarchy."

  :long "<p>If a module never instances any submodules, its level is 0.
Otherwise, its level is 1 more than the maximum level of any of its
submodules.</p>"

  (defund vl-deporder-alistp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (stringp (caar x))
           (natp (cdar x))
           (vl-deporder-alistp (cdr x)))))

  (local (in-theory (enable vl-deporder-alistp)))

  (defthm vl-deporder-alistp-when-atom
    (implies (atom x)
             (equal (vl-deporder-alistp x)
                    (not x))))

  (defthm vl-deporder-alistp-of-cons
    (equal (vl-deporder-alistp (cons a x))
           (and (consp a)
                (stringp (car a))
                (natp (cdr a))
                (vl-deporder-alistp x))))

  (defthm alistp-when-vl-deporder-alistp
    (implies (vl-deporder-alistp x)
             (alistp x)))

  (defthm natp-of-cdr-of-hons-assoc-equal-when-vl-deporder-alistp-one
    (implies (and (member-equal name (strip-cars x))
                  (vl-deporder-alistp x))
             (and (integerp (cdr (hons-assoc-equal name x)))
                  (<= 0 (cdr (hons-assoc-equal name x))))))

  (defthm vl-deporder-alistp-of-append
    (implies (and (vl-deporder-alistp x)
                  (vl-deporder-alistp y))
             (vl-deporder-alistp (append x y))))

  (defthm vl-deporder-alistp-of-make-fal
    (implies (and (vl-deporder-alistp x)
                  (vl-deporder-alistp y))
             (vl-deporder-alistp (make-fal x y)))
    :hints(("Goal" :in-theory (enable make-fal))))

  (defthm string-listp-of-strip-cars-when-vl-deporder-alistp
    (implies (vl-deporder-alistp x)
             (string-listp (strip-cars x)))))




(defsection vl-maximal-deporder
  :parents (vl-deporder)
  :short "@(call vl-maximal-deporder) returns the maximum level for any module
in <tt>names</tt>, according to the @(see vl-deporder-alist)."

  (defund vl-maximal-deporder (names alist)
    (declare (xargs :guard (and (true-listp names)
                                (vl-deporder-alistp alist)
                                (subsetp-equal names (strip-cars alist)))
                    :verify-guards nil))
    (if (atom names)
        0
      (max (cdr (hons-get (car names) alist))
           (vl-maximal-deporder (cdr names) alist))))

  (defthm natp-of-vl-maximal-deporder
    (implies (and (force (true-listp names))
                  (force (vl-deporder-alistp alist))
                  (force (subsetp-equal names (strip-cars alist))))
             (and (integerp (vl-maximal-deporder names alist))
                  (<= 0 (vl-maximal-deporder names alist))))
    :hints(("Goal" :in-theory (enable vl-maximal-deporder))))

  (verify-guards vl-maximal-deporder))



(defsection vl-deporder-pass
  :parents (vl-deporder)
  :short "@(call vl-deporder-pass) extends a partial @(see vl-deporder-alist)
with entries for the modules whose level is now apparent."

  :long "<p><tt>mods</tt> are a list of modules, <tt>alist</tt> is a partial
@(see vl-deporder-alist), and <tt>sorted-cars</tt> are the sorted cars of
alist (which we have precomputed so we don't have to be recomputing it all the
time.).</p>

<p>We walk down the list of modules, processing each in turn.  Suppose we are
processing module <tt>M</tt>.  Then, we consider the modules that <tt>M</tt>
instantates.  If all of these instantiated modules have their deporder
computed, then the deporder of <tt>M</tt> 1 more than their @(see
vl-maximal-deporder).  Otherwise, we will wait for a subsequent pass.</p>"

  (defund vl-deporder-pass (mods alist sorted-cars)
    "Returns (MV REMAINING UPDATES)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-deporder-alistp alist)
                                (equal sorted-cars (mergesort (strip-cars alist))))
                    :verify-guards nil))
    (b* (((when (atom mods))
          (mv nil nil))
         ((mv remaining-mods alist-updates)
          (vl-deporder-pass (cdr mods) alist sorted-cars))
         (insts-modnames*
          (vl-necessary-direct-for-module (car mods)))
         ((when (subset insts-modnames* sorted-cars))
          (mv remaining-mods
              (acons (vl-module->name (car mods))
                     (+ 1 (vl-maximal-deporder insts-modnames* alist))
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
    (implies (member-equal e (strip-cars (mv-nth 1 (vl-deporder-pass mods alist sorted-cars))))
             (member-equal e (vl-modulelist->names mods))))

  (defthm subsetp-equal-of-vl-deporder-pass
    (subsetp-equal (strip-cars (mv-nth 1 (vl-deporder-pass mods alist sorted-cars)))
                   (vl-modulelist->names mods)))

  (defthm vl-deporder-alistp-of-vl-deporder-pass
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-deporder-alistp alist))
                  (force (equal sorted-cars (mergesort (strip-cars alist)))))
             (vl-deporder-alistp (mv-nth 1 (vl-deporder-pass mods alist sorted-cars))))
    :hints(("Goal" :in-theory (enable vl-necessary-direct-for-module))))

  (verify-guards vl-deporder-pass
    :hints(("Goal" :in-theory (enable vl-necessary-direct-for-module))))

  ;; BOZO i broke it.  is this important?
  ;;
  ;; (defcong subsetp-equiv equal (vl-deporder-pass mods alist sorted-cars) 3
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
          (vl-deporder-pass mods alist (mergesort (strip-cars alist))))
         ((unless remaining)
          (make-fal updates alist))
         ((when (same-lengthp mods remaining))
          (prog2$ (er hard? 'vl-deporder-pass* "Failed to reach a fixed point.")
                  alist))
         (alist (make-fal updates alist)))
      (vl-deporder-pass* remaining alist)))

  (local (in-theory (enable vl-deporder-pass*)))

  (defthm vl-deporder-alistp-of-vl-deporder-pass*
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-deporder-alistp alist)))
             (vl-deporder-alistp (vl-deporder-pass* mods alist)))))



(defsection vl-deporder
  :parents (hierarchy)
  :short "@(call vl-deporder) returns a list of module names in dependency
order."

  (defund vl-deporder (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (b* ((alist (vl-deporder-pass* mods nil))
         (-     (clear-memoize-table 'vl-necessary-direct-for-module))
         (-     (fast-alist-free alist))
         ((unless (uniquep (strip-cars alist)))
          (er hard? 'vl-deporder-sort "Expected cars to be unique, but found duplicates for ~x0."
              (duplicated-members (strip-cars alist))))
         ;; Now, our alist is a mapping of strings to numbers.  We want to sort
         ;; it so that the lowest numbers come first.  A really stupid way to do
         ;; this is as follows:
         (swap-alist (pairlis$ (strip-cdrs alist)
                               (strip-cars alist)))
         (sorted     (mergesort swap-alist)))
      (strip-cdrs sorted)))

  (local (in-theory (enable vl-deporder)))

  (defthm string-listp-of-vl-deporder
    (implies (force (vl-modulelist-p mods))
             (string-listp (vl-deporder mods)))
    :hints(("Goal" :in-theory (disable strip-cdrs-of-pairlis$)))))


(defsection vl-deporder-sort
  :parents (hierarchy)
  :short "@(call vl-deporder-sort) reorders <tt>mods</tt> so that they are
listed in dependency order."

  (defund vl-deporder-sort (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (b* ((order    (vl-deporder mods))
         (allnames (vl-modulelist->names mods))
         ((unless (equal (mergesort order) (mergesort allnames)))
          (prog2$ (er hard? 'vl-deporder-sort "Expected all modules to be accounted for.")
                  mods))
         (modalist (vl-modalist mods))
         (result   (vl-fast-find-modules order mods modalist))
         (-        (fast-alist-free modalist)))
      result))

  (local (in-theory (enable vl-deporder-sort)))

  (defthm vl-modulelist-p-of-vl-deporder-sort
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-deporder-sort mods)))))

