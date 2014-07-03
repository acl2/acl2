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
(include-book "find-module")
(include-book "modnamespace")
(include-book "filter")
(include-book "../util/defwellformed")
(include-book "../util/string-alists")
(local (include-book "modname-sets"))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (include-book "centaur/misc/osets-witnessing" :dir :system))
(local (std::add-default-post-define-hook :fix))

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


(define vl-modulelist-everinstanced-nrev ((x vl-modulelist-p)
                                          (nrev))
  :parents (vl-modulelist-everinstanced)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (modinsts1 (vl-module->modinsts (car x)))
       (nrev      (vl-modinstlist->modnames-nrev modinsts1 nrev)))
    (vl-modulelist-everinstanced-nrev (cdr x) nrev)))

(define vl-modulelist-everinstanced ((x vl-modulelist-p))
  :parents (hierarchy)
  :short "Gather the names of every module ever instanced in a module list."
  :long "<p>We leave this function enabled.  It is logically equal to:</p>

@({
  (vl-modinstlist->modnames (vl-modulelist->modinsts x))
})

<p>The returned list typically will contain a lot of duplicates.  This is
fairly expensive, requiring a cons for every single module instance.  We
optimize it to avoid the construction of intermediate lists and to use @(see
nrev).</p>"

  :enabled t
  (mbe :logic (vl-modinstlist->modnames (vl-modulelist->modinsts x))
       :exec (with-local-nrev (vl-modulelist-everinstanced-nrev x nrev)))
  :verify-guards nil
  ///
  (defthm vl-modulelist-everinstanced-nrev-removal
    (equal (vl-modulelist-everinstanced-nrev x nrev)
           (append nrev
                   (vl-modinstlist->modnames (vl-modulelist->modinsts x))))
    :hints(("Goal" :in-theory (enable vl-modulelist-everinstanced-nrev))))

  (verify-guards vl-modulelist-everinstanced))

(define vl-modulelist-meganames ((x vl-modulelist-p))
  :returns (names (and (setp names)
                       (string-listp names)))
  :parents (hierarchy)
  :short "@(call vl-modulelist-meganames) gather the names of every module that
is ever defined or instantiated in @('x'), and returns them as an ordered set."

  :long "<p>We give this function a funny name because it is rather weird.
After all, our basic notion of @(see completeness) is that every instanced
module should be defined.</p>

<p>@(call vl-modulelist-meganames) is really a mechanism that lets us ignore
the ill-formedness of module lists in certain cases.  In particular, it allows
us to admit functions like @(see vl-dependent-modules), which build up sets of
module names until a fixed point is reached, even when the module list might
not be complete.</p>"

  (mbe :logic
       (mergesort (append (vl-modulelist->names x)
                          (vl-modulelist-everinstanced x)))
       :exec
       (mergesort (with-local-nrev
                    (let* ((nrev (vl-modulelist-everinstanced-nrev x nrev))
                           (nrev (vl-modulelist->names-nrev x nrev)))
                      nrev))))
  ///
  (defthm true-listp-of-vl-modulelist-meganames
    (true-listp (vl-modulelist-meganames x))
    :rule-classes :type-prescription)

  (defthm subsetp-equal-of-vl-modulelist->names
    (subsetp-equal (vl-modulelist->names x)
                   (vl-modulelist-meganames x))))



(define vl-module-complete-p ((x vl-module-p)
                              (mods vl-modulelist-p))
  :parents (hierarchy completeness)
  :short "@(call vl-module-complete-p) determines if every module that is
instantiated by @('x') is defined in @('mods')."

  :long "<p>We leave this function enabled, preferring to reason about it as a
subset check.</p>

<p>This function is not efficient, and carries out a linear search of
@('mods') for every module instance of @('x').  See @(see
vl-fast-module-complete-p) for a faster alternative.</p>"
  :enabled t

  (let* ((instances (vl-module->modinsts x))
         (names     (vl-modinstlist->modnames instances)))
    (vl-has-modules names mods)))


(define vl-fast-has-modules-of-vl-modinstlist->modnames
  :parents (hierarchy completeness)
  :short "Fused (@(see vl-fast-has-modules) of @(see vl-modinstlist->modnames)"
  ((x        vl-modinstlist-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :enabled t
  :hooks nil
  (mbe :logic
       (vl-has-modules (vl-modinstlist->modnames x) mods)
       :exec
       (or (atom x)
           (and (vl-fast-has-module (vl-modinst->modname (car x)) mods modalist)
                (vl-fast-has-modules-of-vl-modinstlist->modnames (cdr x) mods modalist)))))

(define vl-fast-module-complete-p
  :parents (hierarchy completeness)
  :short "@(see vl-modalist)-optimized version of @(see vl-module-complete-p)."
  ((x        vl-module-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic
       (vl-module-complete-p x mods)
       :exec
       (vl-fast-has-modules-of-vl-modinstlist->modnames
        (vl-module->modinsts x) mods modalist)))

(define vl-fast-has-modules-of-vl-modulelist-everinstanced
  :parents (hierarchy completeness)
  :short "Fused @(see vl-fast-has-modules) of @(see vl-modulelist-everinstanced)"
  ((x        vl-modulelist-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :enabled t
  :hooks nil
  (mbe :logic
       (vl-has-modules (vl-modulelist-everinstanced x) mods)
       :exec
       (or (atom x)
           (and (vl-fast-has-modules-of-vl-modinstlist->modnames
                 (vl-module->modinsts (car x)) mods modalist)
                (vl-fast-has-modules-of-vl-modulelist-everinstanced
                 (cdr x) mods modalist)))))


(define vl-modulelist-complete-p
  :parents (hierarchy completeness)
  :short "@(call vl-modulelist-complete-p) determines if every module that is
instantiated in @('x') is defined in @('mods')."

  ((x    vl-modulelist-p)
   (mods vl-modulelist-p))

  :long "<p>We leave this function enabled, preferring to reason about it
as a subset check.</p>

<p>This function is slightly inefficient in that it will construct its own
@(see vl-modalist).  If you already have a modalist available to you, for
better performance see @(see vl-fast-modulelist-complete-p).</p>"

  :enabled t
  (mbe :logic
       (subsetp-equal (vl-modulelist-everinstanced x)
                      (vl-modulelist->names mods))
       :exec
       (b* ((modalist (vl-modalist mods))
            (result   (vl-fast-has-modules-of-vl-modulelist-everinstanced
                       x mods modalist)))
         (fast-alist-free modalist)
         result))
  ///
  (defthm vl-modulelist-meganames-when-complete
    (implies (vl-modulelist-complete-p x x)
             (equal (vl-modulelist-meganames x)
                    (mergesort (vl-modulelist->names x))))
    :hints(("Goal" :in-theory (enable vl-modulelist-meganames)))))


(define vl-fast-modulelist-complete-p
  :parents (hierarchy completeness)
  :short "Faster alternative to @(see vl-modulelist-complete-p)."

  ((x        vl-modulelist-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))

  :long "<p>This improves upon @(see vl-modulelist-complete-p) by requiring you
to provide it with the modalist to use.</p>"
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic
       (vl-modulelist-complete-p x mods)
       :exec
       (vl-fast-has-modules-of-vl-modulelist-everinstanced x mods modalist)))





(define vl-module-check-complete
  :parents (hierarchy completeness)
  :short "@(call vl-module-check-complete) annotates @('x') with any
warnings about @(see completeness)."

  ((x        vl-module-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))

  :returns (new-x vl-module-p)
  :long "<p>If @('x') is incomplete, a fatal warning is added that says
which missing modules it instantiates.</p>"

  (b* (((when (vl-fast-module-complete-p x mods modalist))
        ;; No problems to report.
        (vl-module-fix x))
       ((vl-module x) x)
       (referenced (mergesort (vl-modinstlist->modnames x.modinsts)))
       (defined    (mergesort (vl-modulelist->names mods)))
       (bad        (difference referenced defined))
       (warnings   (fatal :type :vl-incomplete
                          :msg "~m0 attempts to instantiate undefined ~
                               module~s1 ~&2."
                          :args (list x.name
                                      (if (vl-plural-p bad) "s" "")
                                      bad)
                          :acc x.warnings))
       (x-prime (change-vl-module x :warnings warnings)))
    x-prime)
  ///
  (defthm vl-module->name-of-vl-module-check-complete
    (equal (vl-module->name (vl-module-check-complete x mods modalist))
           (vl-module->name x))))

(defprojection vl-modulelist-check-complete-aux ((x        vl-modulelist-p)
                                                 (mods     vl-modulelist-p)
                                                 (modalist (equal modalist (vl-modalist mods))))
  :returns (new-x vl-modulelist-p)
  :parents (hierarchy completeness)
  :short "Extends @(see vl-module-check-complete) to a list of modules."
  (vl-module-check-complete x mods modalist))

(define vl-modulelist-check-complete ((x vl-modulelist-p))
  :short "Annotate all modules with any incompleteness warnings."
  :parents (hierarchy)
  :returns (new-x vl-modulelist-p)
  (b* ((modalist (vl-modalist x))
       (ans      (vl-modulelist-check-complete-aux x x modalist)))
    (fast-alist-free modalist)
    (clear-memoize-table 'vl-necessary-direct-for-module)
    ans)
  :verbosep t)

(define vl-design-check-complete ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods (vl-modulelist-check-complete x.mods))))


(define vl-modulelist-missing
  :parents (hierarchy missing)
  :short "@(call vl-modulelist-missing) gathers the names of any modules which
are instantiated in the module list @('x') but are not defined in
@('x'), and returns them as an ordered set."

  ((x vl-modulelist-p))
  :returns (names string-listp)

  (mbe :logic
       (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
             (defined   (mergesort (vl-modulelist->names x))))
         (difference mentioned defined))
       :exec

; Some minor optimizations.

; Historically, since we're sorting the instnames anyway, we don't need to pay
; the price of reversing them and can just use the exec function directly.  Now
; that we're using nrev I don't bother to do this.

       (let* ((mentioned (mergesort (vl-modulelist-everinstanced x)))

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
         (difference mentioned defined)))
  ///
  (defthm true-listp-of-vl-modulelist-missing
    (true-listp (vl-modulelist-missing x))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-modulelist-missing
    (setp (vl-modulelist-missing x))))


(define vl-modulelist-toplevel
  :parents (hierarchy)
  :short "@(call vl-modulelist-toplevel) gathers the names of any modules which
are defined in the module list @('x') but are never instantiated in
@('x'), and returns them as an ordered set."

  ((x vl-modulelist-p))
  :returns (names string-listp)

  (mbe :logic
       (let ((mentioned (mergesort (vl-modulelist-everinstanced x)))
             (defined   (mergesort (vl-modulelist->names x))))
         (difference defined mentioned))
       :exec
       ;; Optimizations as in vl-modulelist-missing
       (let* ((mentioned (mergesort (vl-modulelist-everinstanced x)))
              (names     (vl-modulelist->names x))
              (defined   (if (setp names) names (mergesort names))))
         (difference defined mentioned)))
  ///
  (defthm true-listp-of-vl-modulelist-toplevel
    (true-listp (vl-modulelist-toplevel x))
    :rule-classes :type-prescription)

  (defthm setp-of-vl-modulelist-toplevel
    (setp (vl-modulelist-toplevel x)))

  (defthm vl-has-modules-of-vl-modulelist-toplevel
    (implies (vl-modulelist-complete-p mods mods)
             (subsetp-equal (vl-modulelist-toplevel mods)
                            (vl-modulelist->names mods)))
    :hints((set-reasoning))))


(define vl-modulelist-highlevel
  :parents (hierarchy)
  :short "@(call vl-modulelist-highlevel) gathers the names of any \"high
level\" modules and return them as an ordered set."

  ((x vl-modulelist-p)
   (n natp "How many levels from the top to consider."))

  :returns (names string-listp)

  :long "<p>We say a module is <b>top level</b> (@(see vl-modulelist-toplevel))
when it is never instantiated by another module.  Similarly, we say that
modules are <b>high level</b> when they are \"near the top level\".</p>

<p>@(call vl-modulelist-highlevel) gathers the names of all modules which are
within @('n') levels of the top.  When @('n') is relatively small,
these modules are possibly the \"big units\" in the chip.</p>

<p>Historic note.  This function was once used in the \"unreasonable modules
report.\" It may not be in use any more.</p>"

  :verify-guards nil
  (b* (((when (zp n))
        nil)
       (top (vl-modulelist-toplevel x)))
    (union top
           (vl-modulelist-highlevel (vl-delete-modules top x)
                                    (- n 1))))
  ///
  (defthm true-listp-of-vl-modulelist-highlevel
    (true-listp (vl-modulelist-highlevel x n))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm setp-of-vl-modulelist-highlevel
    (setp (vl-modulelist-highlevel x n)))

  (verify-guards vl-modulelist-highlevel))



(fty::defalist vl-depalist
  :key-type stringp
  :val-type string-listp)

(defalist vl-depalist-p (x)
  :key (stringp x)
  :val (string-listp x)
  :keyp-of-nil nil
  :valp-of-nil t
  :already-definedp t
  :short "Associates modules names to the lists of modules that instantiate them."
  :long "<p>Typically these are produced by @(see vl-depalist).</p>")

(defthm vl-depalist-p-of-vl-mergesort-values
  (implies (vl-depalist-p x)
           (vl-depalist-p (vl-mergesort-values x)))
  :hints(("Goal" :in-theory (enable vl-mergesort-values))))



(define vl-depalist-core-aux
  :parents (vl-depalist)
  :short "Inner loop for dependency alist construction."
  ((parent   stringp          "The name of some module that contains these instances.")
   (modinsts vl-modinstlist-p "Instances contained by these modules.")
   (alist    vl-depalist-p    "The dependency alist we're constructing."))
  :returns (extended-alist vl-depalist-p)
  :long "Add @('parent') to the list of parents for every module named in modinsts."
  (b* ((parent (string-fix parent))
       (alist (vl-depalist-fix alist))
       ((when (atom modinsts))
        alist)
       (mod   (vl-modinst->modname (car modinsts)))
       (entry (cdr (hons-get mod alist))))
    (hons-acons mod
                (cons parent entry)
                (vl-depalist-core-aux parent (cdr modinsts) alist)))
  ///
  (defthm member-equal-of-hons-assoc-equal-of-vl-depalist-core-aux
    (implies (vl-depalist-p alist)
             (iff (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core-aux parent modinsts alist))))
                  (or (member-equal par (cdr (hons-assoc-equal child alist)))
                      (and (equal par (string-fix parent))
                           (member-equal child (vl-modinstlist->modnames modinsts))))))))


(define vl-depalist-core
  :parents (vl-depalist)
  ((x     vl-modulelist-p)
   (alist vl-depalist-p   "The dependency alist we're constructing."))
  :returns (extended-alist vl-depalist-p)
  :long "<p>The resulting alist has values which are just ordinary lists, so
 we'll need to sort them eventually.</p>"
  (b* (((when (atom x))
        (vl-depalist-fix alist))
       (alist (vl-depalist-core-aux (vl-module->name (car x))
                                    (vl-module->modinsts (car x))
                                    alist)))
    (vl-depalist-core (cdr x) alist))
  ///
  (defthm vl-depalist-core-when-atom
    (implies (atom x)
             (equal (vl-depalist-core x alist)
                    (vl-depalist-fix alist))))

  (local (defthm lemma1
           (implies (vl-depalist-p alist)
                    (implies (member-equal par (cdr (hons-assoc-equal child alist)))
                             (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist))))))))

  (local (defthm lemma2
           (implies (and (vl-depalist-p alist)
                         (member-equal child
                                       (vl-modinstlist->modnames
                                        (vl-module->modinsts
                                         (vl-find-module par x)))))
                    (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist)))))))

  (local (defthm lemma3
           (implies (not (member-equal name (vl-modulelist->names x)))
                    (not (vl-find-module name x)))
           :hints(("Goal" :in-theory (e/d (vl-find-module) ((force)))))))

  (defthm member-equal-of-assoc-of-vl-depalist-core
    (implies (and (vl-depalist-p alist)
                  (force (no-duplicatesp-equal (vl-modulelist->names x))))
             (iff (member-equal par (cdr (hons-assoc-equal child (vl-depalist-core x alist))))
                  (or (member-equal par (cdr (hons-assoc-equal child alist)))
                      (member-equal child
                                    (vl-modinstlist->modnames
                                     (vl-module->modinsts
                                      (vl-find-module par x)))))))))

(define vl-depalist
  :parents (hierarchy)
  :short "Build a dependency graph for use in @(see vl-dependent-modules)."
  ((x vl-modulelist-p))
  :returns (alist vl-depalist-p)

  :long "<p>Given a list of modules @('x'), whose names are unique, @(call
vl-depalist) constructs a fast association list which maps each module name in
@('x') to an ordered set of the names of its parents.  A more precise
description is given by the following theorem:</p>

  @(thm correctness-of-vl-depalist)

<p>This alist is useful in dependency computations such as @(see
vl-dependent-modules).</p>"

  (b* ((unsorted (vl-depalist-core x nil))
       (shrunk   (hons-shrink-alist unsorted nil))
       (-        (fast-alist-free unsorted))
       (-        (fast-alist-free shrunk))
       (sorted   (vl-mergesort-values shrunk)))
    sorted)
  ///
  (defthm vl-depalist-when-atom
    (implies (atom x)
             (equal (vl-depalist x)
                    nil)))

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



(define vl-dependent-modules-direct
  :parents (hierarchy)
  :short "@(call vl-dependent-modules-direct) gathers the names of all modules
in @('mods') that directly instantiate any module in @('names'), and
returns them as an ordered set."
  ((names    string-listp)
   (mods     vl-modulelist-p)
   (depalist (equal depalist (vl-depalist mods))))
  :guard (setp names)
  :long "<p>See @(see vl-dependent-modules) for some additional discussion.</p>"
  :verify-guards nil
  :hooks nil
  (if (empty names)
      nil
    (union (cdr (hons-get (head names) depalist))
           (vl-dependent-modules-direct (tail names) mods depalist)))

  ///
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
    (implies (force (vl-depalist-p depalist))
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
  <li>@('prev') and @('curr') are sets of module names</li>
  <li>@('mods') is a set of modules with unique names</li>
  <li>@('depalist') is the precomputed @(see vl-depalist) for @('mods')</li>
</ul>

<p>Note additionally that we assume every module named in @('prev') and
@('curr') is defined in @('mods'), and that the list of modules are
@(see vl-modulelist-complete-p) so that every module which is ever instanced is
also in @('mods').</p>

<p>At a high level, the goal of this function is to compute the set of all
dependents of @('prev U curr').  The computation proceeds iteratively
by searching for new dependents and expanding @('prev U curr') until a
fixed point is reached.</p>

<p>The separation between @('prev') and @('curr') is a useful device
for limiting where we are going to look next.  In particular, we assume as an
invariant that every direct dependent of any member of @('prev') is already
in @('prev U curr').  Because of this, we do not need to look for any new,
direct dependents of @('prev'), and can just focus on @('curr').</p>

<p>The algorithm proceeds as follows.  First, we look up the direct dependents
of @('curr').  Call these dependents @('newinsts').  If all of these
@('newinsts') are already in @('curr U prev'), we have reached a fixed point
and we can stop.</p>

<p>Otherwise, we wish to recur.  Taking the high-level view once again, our new
set is @('newinsts U curr U prev').  However, in the recursive call we set
@('prev') to @('curr U prev'), since all of their direct dependents
have now been accounted for.  The new value of @('curr') is then simply
@('newinsts - (curr U prev)').</p>

<h3>Termination</h3>

<p>The proof of admission is somewhat involved, so we sketch it at a high
level, here.</p>

<h5>Goal</h5>

@({
   (not (Newinsts \\subseteq (Curr U Prev)))
     -->
   |Modnames - (Curr U Prev)| >= |Modnames - (Newinsts U Curr U Prev)|
})

<h5>Proof</h5>

<p>First, note that:</p>
@({
   |Modnames - (Curr U Prev)|
      = |Modnames| - |(Curr U Prev) \\cap Modnames|

   |Modnames - (Newinsts U Curr U Prev)|
      = |Modnames| - |(Newinsts U Curr U Prev) \\cap Modnames|
})

<p>So our goal simplifies to:</p>
@({
    - |(Curr U Prev) \\cap Modnames| >= - |(Newinsts U Curr U Prev) \\cap Modnames|
})

<p>Which is just:</p>
@({
    |(Curr U Prev) \\cap Modnames| <= |(Newinsts U Curr U Prev) \\cap Modnames|
})

<p>We claim this follows from two facts.  First, the left-hand side is
trivially a subset of the right-hand side.  Second, as we demonstrate below,
that there is an element in the right-hand side which is not in the left-hand
side.  In other words, the rhs is a proper superset of the lhs, hence it has
greater cardinality.</p>

<p>To see the existence of such an element, let @('e') be a member of
@('Newinsts - (Curr U Prev)').  We know such an @('e') exists because
our hypothesis is that @('Newinsts') is not a subset of @('(Curr U
Prev)').  Furthermore, @('e') is in @('modnames') because
@('Newinsts') is a subset of @('modnames').  Hence @('e') is in the
right-hand side, but not in the left-hand side.</p>

<p><i>Q.E.D.</i></p>"

  (local (set::use-osets-reasoning))

  (local (in-theory (disable cardinality
                             subset-of-union
                             set::expand-cardinality-of-union
                             set::expand-cardinality-of-difference
                             vl-modulelist-complete-p)))

  (local (defthm cardinalty-<-by-proper-subset
              (iff (< (cardinality x) (cardinality y))
                   (if (subset x y)
                       (not (subset y x))
                     (hide (< (cardinality x) (cardinality y)))))
              :hints (("goal" :expand ((:free (x) (hide x)))))))

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

                    :hints (("Goal" :in-theory (disable (force))))))

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


  (local (in-theory (disable set::difference-in
                             set::subset-in
                             set::intersect-over-union
                             set::intersect-in
                             set::subset-difference
                             set::in-tail
                             set::insert-identity)))

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
@('mods') which, transitively, instantiate any module in @('names'),
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

<p>@('vl-dependent-modules') is the main function for gathering dependent
modules.  It takes as arguments:</p>

<ul>
 <li>@('names'), a list of module names,</li>
 <li>@('x'), an ordered set of modules with unique names, and</li>
 <li>@('depalist'), the pre-computed @(see vl-depalist) for @('x').</li>
</ul>

<p>It produces a set of strings which are the names of all modules that depend
on any module in @('names').  Note that this set will include every member
of @('names'), since, per the above definition, every module depends upon
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



(define vl-necessary-direct-for-module
  :parents (vl-necessary-modules)
  :short "@(call vl-necessary-direct-for-module) gathers the names of all
modules which are directly instantiated by the module @('x'), and returns
them as an ordered set."
  ((x vl-module-p))
  :returns (necessary (and (string-listp necessary)
                           (setp necessary)))

  :long "<p>Logically, this function is nothing more than</p>

@({
  (mergesort (vl-modinstlist->modnames (vl-module->modinsts x)))
})

<p>However, memoizing this function provides an efficiency boost to @(see
vl-necessary-modules).</p>"

  (mergesort (vl-modinstlist->modnames (vl-module->modinsts x)))
  ///
  (memoize 'vl-necessary-direct-for-module))


(defsection vl-necessary-modules-direct-slow
  :parents (vl-necessary-modules)
  :short "@(call vl-necessary-modules-direct-slow) gathers the names of all
modules in @('mods') which are directly instanced by any module in
@('names'), and returns them as an ordered set."

  :long "<p>This is a logically simple function which we do not typically run.
See @(see vl-necessary-modules-direct-fast) for a faster alternative which use
a @(see vl-modalist) for faster lookups.</p>

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

  (local
   (encapsulate nil
     (local (set::use-osets-reasoning))
     (defthm stringp-when-in-vl-modulelist->names
           (implies (and (in a (vl-modulelist->names x))
                         (force (vl-modulelist-p x)))
                    (stringp a))
           :hints(("Goal" :in-theory (enable vl-modulelist->names))))))

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
           (implies (and (vl-modulelist-p mods)
                         (member-equal name (vl-modulelist->names mods)))
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
                     (vl-modulelist-meganames mods)))
    :hints((set-reasoning))))



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
  :parents (vl-necessary-modules)

  :long "<p>This is like vl-dependent-modules-aux, but for vl-necessary-modules
instead.  Prev and curr are lists of module names, and mods is the entire list
of modules.</p>

<p>We are trying to compute the set of all modules which are necessary for curr
and prev.  We assume that all of prev's directly-instantiated modules are
already found within (curr U prev).</p>

<p>So, we are looking for modules which are instantiated by modules in curr.
If all of these are already in curr U prev, we have reached a fixed point
and we can stop.</p>

<p>Otherwise, newinsts - (curr U prev) contains all directly instantiated
modules for (curr U prev), so we can recursively begin looking for these
modules.</p>"

  (local (set::use-osets-reasoning))

  (local (in-theory (disable cardinality
                             subset-of-union
                             set::expand-cardinality-of-union
                             set::expand-cardinality-of-difference
                             vl-modulelist-complete-p)))

  (local (defthm cardinalty-<-by-proper-subset
              (iff (< (cardinality x) (cardinality y))
                   (if (subset x y)
                       (not (subset y x))
                     (hide (< (cardinality x) (cardinality y)))))
              :hints (("goal" :expand ((:free (x) (hide x)))))))


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
                      :in-theory (disable (force))))))

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
@('mods') which, transitively, are instantiated by any module in
@('names'), and returns them as an ordered set."

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
@('mods') which are not necessary for the modules named in @('keep')."

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
    (vl-modulelist-p (vl-remove-unnecessary-modules keep mods)))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-remove-unnecessary-modules
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (vl-remove-unnecessary-modules keep x))))))




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
                 (a name) (x x))))))



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

