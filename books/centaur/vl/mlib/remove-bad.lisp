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
(include-book "hierarchy")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (include-book "modname-sets"))



(define vl-blame-alist-aux1
  ((bad   "name of a module we are currently processing" stringp)
   (deps  "modules that depend on @('bad')" string-listp)
   (alist "partially constructed blame list"))
  :parents (vl-blame-alist)
  :short "For each module M in DEPS, we additionally blame BAD."
  (b* (((when (atom deps))
        alist)
       (m          (car deps))
       (old-blamed (cdr (hons-get m alist)))
       (new-blamed (cons bad old-blamed))
       (new-alist  (hons-acons m new-blamed alist)))
    (vl-blame-alist-aux1 bad (cdr deps) new-alist))

  ///

  (defthm alistp-of-vl-blame-alist-aux1
    (implies (force (alistp alist))
             (alistp (vl-blame-alist-aux1 bad deps alist))))

  (defthm vl-string-keys-p-of-vl-blame-alist-aux1
    (implies (and (force (vl-string-keys-p alist))
                  (force (string-listp deps)))
             (vl-string-keys-p (vl-blame-alist-aux1 bad deps alist))))

  (defthm vl-string-list-values-p-of-vl-blame-alist-aux1
    (implies (and (force (vl-string-list-values-p alist))
                  (force (stringp bad)))
             (vl-string-list-values-p (vl-blame-alist-aux1 bad deps alist)))))


(define vl-blame-alist-aux2
  ((bads "names of all the bad modules" string-listp)
   (mods "list of all modules." (and (setp mods)
                                     (vl-modulelist-p mods)
                                     (uniquep (vl-modulelist->names mods))))
   (depalist "precomputed depalist for @('mods'), for fast lookups"
             (equal depalist (vl-depalist mods)))
   (alist "partially constructed blame alist"))
  :parents (vl-blame-alist)
  :short "For each Bi in BADS we compute deps(Bi) = {M1, ..., Mk}, and blame Bi
for ruining each Mj."

  (b* (((when (atom bads))
        alist)
       (deps  (vl-dependent-modules (list (car bads)) mods depalist))
       (alist (vl-blame-alist-aux1 (car bads) deps alist)))
    (vl-blame-alist-aux2 (cdr bads) mods depalist alist))

  ///

  (defthm vl-blame-alist-aux2-when-not-consp
    (implies (not (consp bads))
             (equal (vl-blame-alist-aux2 bads mods depalist alist)
                    alist)))

  (defthm alistp-of-vl-blame-alist-aux2
    (implies (force (alistp alist))
             (alistp (vl-blame-alist-aux2 bads mods depalist alist))))

  (defthm vl-string-keys-p-of-vl-blame-alist-aux2
    (implies (and (force (string-listp bads))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (equal depalist (vl-depalist mods)))
                  (force (vl-string-keys-p alist)))
             (vl-string-keys-p
              (vl-blame-alist-aux2 bads mods depalist alist))))

  (defthm vl-string-list-values-p-of-vl-blame-alist-aux2
    (implies (and (force (string-listp bads))
                  (force (setp mods))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods)))
                  (force (equal depalist (vl-depalist mods)))
                  (force (vl-string-list-values-p alist)))
             (vl-string-list-values-p
              (vl-blame-alist-aux2 bads mods depalist alist)))))


(define vl-blame-alist
  ((bads "names of bad modules" string-listp)
   (mods "list of all modules" (and (vl-modulelist-p mods)
                                    (uniquep (vl-modulelist->names mods)))))
  :returns (ans alistp)
  :parents (vl-remove-bad-modules)
  :short "Build an alist describing which modules are to blame for their
dependents being thrown away."

  :long "<p><b>Fast alist warning:</b> the returned alist is a fast alist, and
should be freed by the caller with @('fast-alist-free') to avoid memory
leaks.</p>

<h3>Explanation of Blame Alists</h3>

<p>Suppose we are transforming a list of modules, and we run into problems in
some module, @('M').  Our basic error handling strategy is to:</p>

<ul>

<li>Add a warning onto @('M') that says why we had the problem, and</li>

<li>Remove @('M') from the list of modules, so that we can continue with the
other modules.</li>

</ul>

<p>But this is not quite sufficient.  In addition to removing @('M'), we need
to remove any dependents (@(see vl-dependent-modules)) of @('M'), since
removing @('M') would cause these modules to be incomplete.  As we remove these
dependent modules, we would also like to annotate them with warnings explaining
why they are being removed, and that @('M') is at fault.</p>

<p>In general, instead of a single \"bad\" module, imagine that we have a list
of bad modules, @('B1'), ..., @('Bn').  Additionally,</p>

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

<p>Our approach is to blame both of them.  To do this, we first construct a
<b>blame alist</b>.  This alist includes an entry for every module @('M') in
@('D').  In particular, we associate each such @('M') with @('{ Bi
: M in deps(Bi) }').  Once the blame alist is constructed, we can easily use
it to annotate each module in its domain with a warning that says which modules
are to blame for its removal.</p>

<p>Efficiency note.  Since @(see vl-depalist) requires that the given mods are
a set, we originally tried to require @('(setp mods)') as part of our guard.
We later found that we wanted to be able to apply blame lists even to module
lists that were not sorted in name order: in particular, after we run the
dependency-order sort, we want to keep the modules in dependency order.  In
short, we now pay the modest price of sorting the modules ourselves, so that
the caller can use any module order he likes.</p>"

  (mbe :logic
       (let ((mods (if (setp mods)
                       mods
                     (mergesort mods))))
         (hons-shrink-alist
          (vl-blame-alist-aux2 bads mods (vl-depalist mods) nil)
          nil))
       :exec
       (if (not bads)
           nil
         (let ((mods (if (setp mods)
                         mods
                       (mergesort mods))))
           (b* ((depalist (vl-depalist mods))
                (result   (vl-blame-alist-aux2 bads mods depalist nil))
                (-        (fast-alist-free depalist))
                (shrunk   (hons-shrink-alist result nil))
                (-        (fast-alist-free result)))
             shrunk))))

  ///

  (defthm vl-string-keys-p-of-vl-blame-alist
    (implies (and (force (string-listp bads))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (vl-string-keys-p (vl-blame-alist bads mods))))

  (defthm vl-string-list-values-p-of-vl-blame-alist
    (implies (and (force (string-listp bads))
                  (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (vl-string-list-values-p (vl-blame-alist bads mods)))))




(defsection vl-apply-blame-alist
  :parents (vl-remove-bad-modules)
  :short "Annotates transitively-bad modules with warnings, and throws them
away."

  :long "<p>@(call vl-apply-blame-alist) returns @('(mv survivors
  victims)').</p>

<p>Inputs:</p>

<ul>

<li>@('mods') are the list of all \"good\" modules,</li>

<li>@('alist') is a blame alist formed by @(see vl-blame-alist),</li>

</ul>

<p>Outputs:</p>

<ul>

<li>@('survivors') contains the modules from @('mods') which are not
transitively bad, and are not being thrown away.</li>

<li>@('victims') contains the modules from @('mods') that are being thrown
away, each of which has been updated with a warning explaining which modules
are to blame.</li>

</ul>

<p>Note that the survivors are returned in the same order as they occur in
@('mods').</p>"

  ;; just a speed hint
  (local (in-theory (disable hons-assoc-equal
                             no-duplicatesp-equal-when-same-length-mergesort
                             remove-equal
                             promote-member-equal-to-membership
                             true-listp
                             acl2::subsetp-equal-member
                             acl2::true-listp-member-equal)))

  (defconst *vl-bad-submodule-message*
    "Module ~m0 (perhaps transitively) depends upon modules which have been ~
     eliminated.  In particular, the following submodule(s) are to blame: ~
     ~&1.")

  (defund vl-apply-blame-alist-exec (mods alist survivors victims)
    "Returns (mv survivors victims)"
    (declare (xargs :guard (vl-modulelist-p mods)))
    (if (atom mods)
        (mv survivors victims)
      (b* ((mod1   (car mods))
           (name1  (vl-module->name mod1))
           (entry1 (hons-get name1 alist)))
        (if (not entry1)
            (vl-apply-blame-alist-exec (cdr mods) alist (cons mod1 survivors) victims)
          ;; The blame falls upon everyone mentioned in the blame alist.  But
          ;; it's weird to add a warning saying that a module is to blame for
          ;; itself.  So, we remove the module itself from the blame list.
          (let ((blame (remove-equal-without-guard name1 (cdr entry1))))
            (if (not blame)
                ;; This is still a victim that we're throwing out.  It just
                ;; doesn't get a warning.
                (vl-apply-blame-alist-exec (cdr mods) alist survivors (cons mod1 victims))

              ;; Else there is someone to blame, so blame them.
              (b* ((new-warnings (cons (make-vl-warning :type :vl-bad-submodule
                                                        :msg *vl-bad-submodule-message*
                                                        :args (list name1 (cdr entry1))
                                                        :fatalp t
                                                        :fn 'vl-apply-blame-alist)
                                       (vl-module->warnings mod1)))
                   (new-mod1     (change-vl-module mod1 :warnings new-warnings)))
                (vl-apply-blame-alist-exec (cdr mods) alist survivors
                                           (cons new-mod1 victims)))))))))

  (defund vl-apply-blame-alist (mods alist)
    "Returns (mv survivors victims)"
    (declare (xargs :guard (vl-modulelist-p mods)
                    :verify-guards nil))
    (mbe :logic
         (if (atom mods)
             (mv nil nil)
           (b* ((mod1                   (car mods))
                (name1                  (vl-module->name mod1))
                (entry1                 (hons-get name1 alist))
                (blame                  (remove-equal name1 (cdr entry1)))
                ((mv survivors victims) (vl-apply-blame-alist (cdr mods) alist)))
             (cond ((not entry1)
                    (mv (cons mod1 survivors) victims))
                   ((not blame)
                    (mv survivors (cons mod1 victims)))
                   (t
                    (b* ((new-warnings (cons (make-vl-warning :type :vl-bad-submodule
                                                              :msg *vl-bad-submodule-message*
                                                              :args (list name1 (cdr entry1))
                                                              :fatalp t
                                                              :fn 'vl-apply-blame-alist)
                                             (vl-module->warnings mod1)))
                         (new-mod1     (change-vl-module mod1 :warnings new-warnings)))
                      (mv survivors (cons new-mod1 victims)))))))
         :exec (mv-let (survivors victims)
                 (vl-apply-blame-alist-exec mods alist nil nil)
                 (mv (reverse survivors) (reverse victims)))))

  (defmvtypes vl-apply-blame-alist (true-listp true-listp))

  (local (in-theory (enable vl-apply-blame-alist-exec
                            vl-apply-blame-alist)))

  (defthm vl-apply-blame-alist-exec-removal
    (implies (and (true-listp survivors)
                  (true-listp victims))
             (equal (vl-apply-blame-alist-exec mod alist survivors victims)
                    (mv (revappend (mv-nth 0 (vl-apply-blame-alist mod alist)) survivors)
                        (revappend (mv-nth 1 (vl-apply-blame-alist mod alist)) victims)))))

  (verify-guards vl-apply-blame-alist)

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-apply-blame-alist-exec acl2::*never-profile-ht*) t)
   (defun vl-apply-blame-list (mods alist)
     (mv-let (survivors victims)
       (vl-apply-blame-alist-exec mods alist nil nil)
       (mv (nreverse survivors) (nreverse victims)))))
  (defttag nil)

  (defthm vl-modulelist-p-of-vl-apply-blame-alist-0
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 0 (vl-apply-blame-alist mods alist)))))

  (defthm vl-modulelist-p-of-vl-apply-blame-alist-1
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 1 (vl-apply-blame-alist mods alist)))))

  (defthm subsetp-equal-names-of-vl-apply-blame-alist-0
    (subsetp-equal
     (vl-modulelist->names (mv-nth 0 (vl-apply-blame-alist mods alist)))
     (vl-modulelist->names mods)))

  (defthm subsetp-equal-names-of-vl-apply-blame-alist-1
    (subsetp-equal
     (vl-modulelist->names (mv-nth 1 (vl-apply-blame-alist mods alist)))
     (vl-modulelist->names mods)))

  (local
   (defthm lemma-0
     (implies (not (member-equal a (vl-modulelist->names x)))
              (not (member-equal a (vl-modulelist->names
                                    (mv-nth 0 (vl-apply-blame-alist x alist))))))))

  (local
   (defthm lemma-1
     (implies (not (member-equal a (vl-modulelist->names x)))
              (not (member-equal a (vl-modulelist->names
                                    (mv-nth 1 (vl-apply-blame-alist x alist))))))))

  (defthm no-duplicatesp-equal-of-vl-apply-blame-alist-0
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-apply-blame-alist x alist))))))

  (defthm no-duplicatesp-equal-of-vl-apply-blame-alist-1
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 1 (vl-apply-blame-alist x alist))))))

  (local
   (defthm lemma-2
     (let ((ret (vl-apply-blame-alist mods alist)))
       (implies (no-duplicatesp-equal (vl-modulelist->names mods))
                (iff (member-equal a (vl-modulelist->names (mv-nth 1 ret)))
                     (and (member-equal a (vl-modulelist->names mods))
                          (not (member-equal a (vl-modulelist->names (mv-nth 0 ret))))))))
     :hints(("Goal"
             :induct (len mods)
             ;; speed hints
             :in-theory (disable hons-assoc-equal
                                 no-duplicatesp-equal-when-same-length-mergesort
                                 remove-equal
                                 promote-member-equal-to-membership
                                 true-listp
                                 acl2::subsetp-equal-member
                                 acl2::true-listp-member-equal)
             :do-not '(generalize fertilize)))))

  (defthm names-of-vl-apply-blame-alist-1
    ;; This is somewhat iffy and was intended to canonicalize the victims'
    ;; names to be in terms of the survivors' names.  It's not clear whether
    ;; this is a good rule.
    (implies
     (force (no-duplicatesp-equal (vl-modulelist->names mods)))
     (set-equivp
      (vl-modulelist->names (mv-nth 1 (vl-apply-blame-alist mods alist)))
      (set-difference-equal
       (vl-modulelist->names mods)
       (vl-modulelist->names (mv-nth 0 (vl-apply-blame-alist mods alist))))))
    :hints((set-reasoning))))




(define vl-remove-bad-modules
  ((names "modules to be eliminated" string-listp)
   (mods  "list of all modules" (and (vl-modulelist-p mods)
                                     (uniquep (vl-modulelist->names mods)))))
  :returns (mv (survivors "modules that didn't depend on @('names')")
               (victims "modules that were eliminated"))
  :parents (mlib)
  :short "Safely remove some faulty modules and their dependents."

  :long "<p>This is a high-level, convenient operation for safely eliminating
modules.  We determine which modules depend upon @('names'), annotate them with
warnings explaining that they are being removed because they instantiate bad
modules, and separate them from the modules that are okay.</p>

<p>The returned @('survivors') are in the same order as they occur in
@('mods').</p>"

  (b* ((blame-alist            (vl-blame-alist names mods))
       ((mv survivors victims) (vl-apply-blame-alist mods blame-alist))
       (-                      (fast-alist-free blame-alist)))
    (mv survivors victims))

  ///

  (defmvtypes vl-remove-bad-modules (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-remove-bad-modules-0
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 0 (vl-remove-bad-modules names mods)))))

  (defthm vl-modulelist-p-of-vl-remove-bad-modules-1
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 1 (vl-remove-bad-modules names mods)))))

  (defthm subsetp-equal-names-of-vl-remove-bad-modules-0
    (subsetp-equal
     (vl-modulelist->names (mv-nth 0 (vl-remove-bad-modules names mods)))
     (vl-modulelist->names mods)))

  (defthm subsetp-equal-names-of-vl-remove-bad-modules-1
    (subsetp-equal
     (vl-modulelist->names (mv-nth 1 (vl-remove-bad-modules names mods)))
     (vl-modulelist->names mods))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm no-duplicatesp-equal-of-vl-remove-bad-modules-0
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-remove-bad-modules names x))))))

  (defthm no-duplicatesp-equal-of-vl-remove-bad-modules-1
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 1 (vl-remove-bad-modules names mods))))))

  (defthm names-of-vl-remove-bad-modules-1
    ;; This is somewhat iffy and was intended to canonicalize the victims'
    ;; names to be in terms of the survivors' names.  It's not clear whether
    ;; this is a good rule.
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (set-equivp
              (vl-modulelist->names (mv-nth 1 (vl-remove-bad-modules names mods)))
              (set-difference-equal
               (vl-modulelist->names mods)
               (vl-modulelist->names (mv-nth 0 (vl-remove-bad-modules names mods)))))))

  ;; BOZO it would be nice to eventually prove this:
  ;;
  ;;(defthm vl-modulelist-complete-p-of-vl-remove-bad-modules
  ;;  (implies (and (vl-modulelist-p mods)
  ;;                (vl-modulelist-complete-p mods mods))
  ;;           (vl-modulelist-complete-p
  ;;            (first (vl-remove-bad-modules names mods))
  ;;            (first (vl-remove-bad-modules names mods)))))

  )


(define vl-modulelist-zombies ((x vl-modulelist-p))
  :returns (ans string-listp :hyp :fguard)
  :parents (warnings)
  :short "Identify modules with fatal warnings."

  :long "<p>@(call vl-modulelist-zombies) gathers and returns the names of all
modules in @('x') which have some fatal warning (as determined by @(see
vl-some-warning-fatalp).  This function is mainly used in @(see
vl-propagate-errors).</p>"

  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-module->warnings (car x)))
         (cons (vl-module->name (car x))
               (vl-modulelist-zombies (cdr x))))
        (t
         (vl-modulelist-zombies (cdr x)))))


(define vl-propagate-errors ((x (and (vl-modulelist-p x)
                                     (uniquep (vl-modulelist->names x)))))
  :returns (mv survivors victims)
  :parents (warnings)
  :short "Eliminate modules with fatal warnings (and their dependents)."
  :long "<p>Given a list of modules, @('x'), we find all modules that have
fatal @(see warnings) using @(see vl-modulelist-zombies).  We then use @(see
vl-remove-bad-modules) to safely remove these modules and all of their
dependents from the module list.  The resulting @('survivors') are kept in the
same order as they occur in @('x').</p>"

  (let ((zombies (vl-modulelist-zombies x)))
    (if zombies
        (vl-remove-bad-modules zombies x)
      (mv (redundant-list-fix x) nil)))

  ///

  (defmvtypes vl-propagate-errors (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-propagate-errors-0
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-propagate-errors x)))))

  (defthm vl-modulelist-p-of-vl-propagate-errors-1
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 1 (vl-propagate-errors x)))))

  (defthm subsetp-equal-names-of-vl-propagate-errors-0
    (subsetp-equal
     (vl-modulelist->names (mv-nth 0 (vl-propagate-errors mods)))
     (vl-modulelist->names mods)))

  (defthm subsetp-equal-names-of-vl-propagate-errors-1
    (subsetp-equal
     (vl-modulelist->names (mv-nth 1 (vl-propagate-errors mods)))
     (vl-modulelist->names mods)))

  (defthm no-duplicatesp-equal-of-vl-propagate-errors-0
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-propagate-errors x))))))

  (defthm no-duplicatesp-equal-of-vl-propagate-errors-1
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 1 (vl-propagate-errors mods))))))

  (defthm names-of-vl-propagate-errors-1
    ;; This is somewhat iffy and was intended to canonicalize the victims'
    ;; names to be in terms of the survivors' names.  It's not clear whether
    ;; this is a good rule.
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (set-equivp
              (vl-modulelist->names (mv-nth 1 (vl-propagate-errors mods)))
              (set-difference-equal
               (vl-modulelist->names mods)
               (vl-modulelist->names (mv-nth 0 (vl-propagate-errors mods))))))))



(define vl-propagate-new-errors
  ((x (and (vl-modulelist-p x)
           (uniquep (vl-modulelist->names x))))
   old-victims)
  :parents (warnings)
  :short "Trivial wrapper for @(see vl-propagate-errors) that accumulates
victims."

  :long "<p>This function is like @(see vl-propagate-errors), except that it
adds the new victims to @('old-victims').</p>"

  (b* (((mv survivors victims) (vl-propagate-errors x))
       (new-victims            (append victims (redundant-list-fix old-victims))))
    (mv survivors new-victims))

  ///

  (defmvtypes vl-propagate-new-errors (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-propagate-new-errors-0
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-propagate-new-errors x old-victims)))))

  (defthm vl-modulelist-p-of-vl-propagate-new-errors-1
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-modulelist-p old-victims)))
             (vl-modulelist-p (mv-nth 1 (vl-propagate-new-errors x old-victims)))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-propagate-new-errors
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-propagate-new-errors x old-victims)))))))

