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
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (include-book "modname-sets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc propagating-errors
  :parents (warnings vl-simplify)
  :short "The error handling strategy used by @(see vl-simplify)."

  :long "<p>As described in @(see warnings), our @(see transforms) can
sometimes run into severe problems, e.g., we might run into an instance of an
undefined module.  In this case, the transform should typically extend the
module with a fatal warning.</p>

<p>In the context of @(see vl-simplify), we generally want to throw away any
design elements (e.g., modules, packages, etc.) that have fatal errors, so that
we only produce a formal model of whatever part of the design is well-formed
and supported.</p>

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

<p>Our basic strategy for dealing with this, in @(see vl-simplify) at least, is
to imagine two designs, <b>good</b> and <b>bad</b>.  Initially, we put all of
the design elements into the good design, and the bad design is empty.  We
always only try to transform the good design, and afterward we can move any
design elements that had errors into the bad design.</p>

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
  :key-type stringp
  :val-type string-listp)

(defalist vl-blamealist-p (x)
  :key (stringp x)
  :val (string-listp x)
  :keyp-of-nil nil
  :valp-of-nil t
  :already-definedp t
  :short "A record of which submodules are to blame for transitive failures to
  translate modules."

  :long "<h3>Explanation of Blame Alists</h3>

<p>Suppose we are transforming a list of modules, and we run into problems in
some module, @('M').  Our basic strategy for @(see propagating-errors) is:</p>

<ul>
<li>Add a warning onto @('M') that says why we had the problem, and</li>
<li>Remove @('M') from the list of modules, so that we can continue with the
other modules.</li>
</ul>

<p>This isn't really good enough.  Besides removing @('M'), we should also
remove any dependents (@(see vl-dependent-modules)) of @('M'), since removing
@('M') would cause these modules to be incomplete.  As we remove these
dependent modules, we would also like to annotate them with warnings explaining
that they are being removed because of problems with @('M').</p>

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

<p>Our approach is to blame them both..  To do this, we first construct a
<b>blame alist</b>.  This alist includes an entry for every module @('M') in
@('D').  In particular, we associate each such @('M') with @('{ Bi
: M in deps(Bi) }').  Once the blame alist is constructed, we can easily use
it to annotate each module in its domain with a warning that says which modules
are to blame for its removal.</p>")

(define vl-blame-alist-aux1
  :parents (vl-blame-alist)
  :short "For each module M in DEPS, we additionally blame BAD."
  ((bad   "Name of a module we are currently processing." stringp)
   (deps  "Modules that depend on @('bad')." string-listp)
   (alist "Partially constructed blame list." vl-blamealist-p))
  :returns (new-alist vl-blamealist-p)
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

(define vl-blame-alist-aux2
  :parents (vl-blame-alist)
  :short "For each Bi in BADS we compute deps(Bi) = {M1, ..., Mk}, and blame Bi
          for ruining each Mj."
  ((bads "Names of all the bad modules." string-listp)
   (mods "List of all modules." (and (setp mods)
                                     (vl-modulelist-p mods)
                                     (uniquep (vl-modulelist->names mods))))
   (depalist "Precomputed depalist for @('mods'), for fast lookups"
             (equal depalist (vl-depalist mods)))
   (alist "Partially constructed blame alist"
          vl-blamealist-p))
  :returns (new-alist vl-blamealist-p)
  :hooks nil
  (b* (((when (atom bads))
        (vl-blamealist-fix alist))
       (deps  (vl-dependent-modules (list (car bads)) mods depalist))
       (alist (vl-blame-alist-aux1 (car bads) deps alist)))
    (vl-blame-alist-aux2 (cdr bads) mods depalist alist))
  ///
  (defthm vl-blame-alist-aux2-when-not-consp
    (implies (not (consp bads))
             (equal (vl-blame-alist-aux2 bads mods depalist alist)
                    (vl-blamealist-fix alist)))))

(define vl-blame-alist
  :short "Build an alist describing which modules are really to blame for their
          dependents being thrown away."
  ((bads "Names of bad modules." string-listp)
   (mods "List of all modules."  vl-modulelist-p))
  :guard (uniquep (vl-modulelist->names mods))
  :returns (blame-alist vl-blamealist-p "Fast alist.")
  :long "<p>Efficiency note.  Since @(see vl-depalist) requires that the given
mods are a set, we originally tried to require @('(setp mods)') as part of our
guard.  We later found that we wanted to be able to apply blame lists even to
module lists that were not sorted in name order: in particular, after we run
the dependency-order sort, we want to keep the modules in dependency order.  In
short, we now pay the modest price of sorting the modules ourselves, so that
the caller can use any module order he likes.</p>"
  (mbe :logic
       (b* ((bads (string-list-fix bads))
            (mods (vl-modulelist-fix mods))
            (mods (mergesort mods)))
         (hons-shrink-alist
          (vl-blame-alist-aux2 bads mods (vl-depalist mods) nil)
          nil))
       :exec
       (b* (((unless bads)
             nil)
            (mods     (redundant-mergesort mods))
            (depalist (vl-depalist mods))
            (result   (vl-blame-alist-aux2 bads mods depalist nil))
            (-        (fast-alist-free depalist))
            (shrunk   (hons-shrink-alist result nil))
            (-        (fast-alist-free result)))
         shrunk)))


(defval *vl-bad-submodule-message*
  :parents (vl-apply-blame-alist)
  "Module ~m0 (perhaps transitively) depends upon modules which have been ~
   eliminated.  In particular, the following submodule(s) are to blame: ~&1.")

(define vl-apply-blame-alist-exec
  :parents (vl-apply-blame-alist)
  ((mods vl-modulelist-p)
   (alist vl-blamealist-p)
   (nrev "Survivors")
   (nrev2 "Victims"))
  :verbosep t
  :returns (mv nrev nrev2)
  (b* ((alist (vl-blamealist-fix alist))
       ((when (atom mods))
        (b* ((nrev (nrev-fix nrev))
             (nrev2 (nrev-fix nrev2)))
          (mv nrev nrev2)))
       (mod1   (vl-module-fix (car mods)))
       (name1  (vl-module->name mod1))
       (entry1 (hons-get name1 alist))
       ((unless entry1)
        (b* ((nrev (nrev-push mod1 nrev)))
          (vl-apply-blame-alist-exec (cdr mods) alist nrev nrev2)))
       ;; The blame falls upon everyone mentioned in the blame alist.  But it's
       ;; weird to add a warning saying that a module is to blame for itself.
       ;; So, we remove the module itself from the blame list.
       (blame (remove-equal-without-guard name1 (cdr entry1)))
       ((unless blame)
        ;; This is still a victim that we're throwing out.  It just doesn't get
        ;; a warning.
        (b* ((nrev2 (nrev-push mod1 nrev2)))
          (vl-apply-blame-alist-exec (cdr mods) alist nrev nrev2)))
       ;; Else there is someone to blame, so blame them.
       (new-warnings (fatal :type :vl-bad-submodule
                            :msg *vl-bad-submodule-message*
                            :args (list name1 (cdr entry1))
                            ;; Horrible -- have to lie to get the MBE equivalence
                            :fn 'vl-apply-blame-alist
                            :acc (vl-module->warnings mod1)))
       (new-mod1     (change-vl-module mod1 :warnings new-warnings))
       (nrev2        (nrev-push new-mod1 nrev2)))
    (vl-apply-blame-alist-exec (cdr mods) alist nrev nrev2)))


(define vl-apply-blame-alist
  :parents (vl-remove-bad-modules)
  :short "Annotates transitively-bad modules with warnings, and throws them
away."

  ((mods  vl-modulelist-p "The list of all \"good\" modules.")
   (alist vl-blamealist-p "The blame alist, see @(see vl-blame-alist)."))
  :returns
  (mv (survivors vl-modulelist-p "The modules that are still okay.")
      (victims   vl-modulelist-p "The modules that were thrown away, annotated
                                  with warnings about why they are being
                                  eliminated."))
  :verify-guards nil
  (mbe :logic
       (b* ((alist (vl-blamealist-fix alist))
            ((when (atom mods))
             (mv nil nil))
            (mod1                   (vl-module-fix (car mods)))
            (name1                  (vl-module->name mod1))
            (entry1                 (hons-get name1 alist))
            (blame                  (remove-equal name1 (cdr entry1)))
            ((mv survivors victims) (vl-apply-blame-alist (cdr mods) alist))
            ((unless entry1)
             (mv (cons mod1 survivors) victims))
            ((unless blame)
             (mv survivors (cons mod1 victims)))
            (new-warnings (fatal :type :vl-bad-submodule
                                 :msg *vl-bad-submodule-message*
                                 :args (list name1 (cdr entry1))
                                 :acc (vl-module->warnings mod1)))
            (new-mod1     (change-vl-module mod1 :warnings new-warnings)))
         (mv survivors (cons new-mod1 victims)))
       :exec (b* (((local-stobjs nrev nrev2)
                   (mv survivors victims nrev nrev2))
                  ((mv nrev nrev2)
                   (vl-apply-blame-alist-exec mods alist nrev nrev2))
                  ((mv survivors nrev) (nrev-finish nrev))
                  ((mv victims nrev2) (nrev-finish nrev2)))
               (mv survivors victims nrev nrev2)))
  ///
  (local (in-theory (e/d (vl-apply-blame-alist-exec)
                         ((force)
                          hons-assoc-equal
                          no-duplicatesp-equal-when-same-length-mergesort
                          remove-equal
                          promote-member-equal-to-membership
                          true-listp
                          acl2::subsetp-member
                          acl2::true-listp-member-equal))))

  (defmvtypes vl-apply-blame-alist (true-listp true-listp))

  (defthm vl-apply-blame-alist-exec-removal
    (equal (vl-apply-blame-alist-exec mod alist survivors victims)
           (mv (append survivors
                       (mv-nth 0 (vl-apply-blame-alist mod alist)))
               (append victims
                       (mv-nth 1 (vl-apply-blame-alist mod alist)))))
    :hints(("Goal" :in-theory (enable vl-apply-blame-alist-exec))))

  (verify-guards vl-apply-blame-alist)
  (deffixequiv vl-apply-blame-alist)

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
                                 acl2::subsetp-member
                                 acl2::true-listp-member-equal)
             :do-not '(generalize fertilize)))))

  (defthm names-of-vl-apply-blame-alist-1
    ;; This is somewhat iffy and was intended to canonicalize the victims'
    ;; names to be in terms of the survivors' names.  It's not clear whether
    ;; this is a good rule.
    (implies
     (force (no-duplicatesp-equal (vl-modulelist->names mods)))
     (set-equiv
      (vl-modulelist->names (mv-nth 1 (vl-apply-blame-alist mods alist)))
      (set-difference-equal
       (vl-modulelist->names mods)
       (vl-modulelist->names (mv-nth 0 (vl-apply-blame-alist mods alist))))))
    :hints((set-reasoning))))



(define vl-remove-bad-modules
  :short "Safely remove some faulty modules and their dependents."

  ((names "Modules to be eliminated" string-listp)
   (mods  "List of all modules"      vl-modulelist-p))
  :guard (uniquep (vl-modulelist->names mods))
  :returns
  (mv (survivors vl-modulelist-p "Modules that didn't depend on @('names').")
      (victims   vl-modulelist-p "Modules that were eliminated, annotated with warnings."))

  :long "<p>This is a high-level, convenient operation for safely eliminating
modules.  We determine which modules depend upon @('names'), annotate them with
warnings explaining that they are being removed because they instantiate bad
modules, and separate them from the modules that are okay.</p>"

  (b* ((blame-alist            (vl-blame-alist names mods))
       ((mv survivors victims) (vl-apply-blame-alist mods blame-alist)))
    (fast-alist-free blame-alist)
    (mv survivors victims))

  ///
  (defmvtypes vl-remove-bad-modules (true-listp true-listp))

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
             (set-equiv
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


(define vl-modulelist-zombies
  :short "Identify modules with fatal warnings."
  ((x vl-modulelist-p))
  :returns (ans string-listp "Names of modules that have any fatal warnings.")
  (cond ((atom x)
         nil)
        ((vl-some-warning-fatalp (vl-module->warnings (car x)))
         (cons (vl-module->name (car x))
               (vl-modulelist-zombies (cdr x))))
        (t
         (vl-modulelist-zombies (cdr x)))))


(define vl-modulelist-propagate-errors
  :short "Eliminate modules with fatal warnings (and their dependents)."
  ((x vl-modulelist-p "A list of modules, some of which may have fatal errors."))
  :guard (uniquep (vl-modulelist->names x))
  :returns
  (mv (survivors vl-modulelist-p
                 "The good portion of @('x'), i.e., the subset of the modules
                  that do not depend on any faulty submodules.")
      (victims   vl-modulelist-p
                 "The bad portion of @('x'), i.e., any modules that have fatal
                  warnings and (transitively) any modules that depend on
                  them."))
  (b* ((x       (vl-modulelist-fix x))
       (zombies (vl-modulelist-zombies x))
       ((when zombies)
        (vl-remove-bad-modules zombies x)))
    (mv (redundant-list-fix x) nil))
  ///
  (defmvtypes vl-modulelist-propagate-errors (true-listp true-listp))

  (defthm subsetp-equal-names-of-vl-modulelist-propagate-errors-0
    (subsetp-equal
     (vl-modulelist->names (mv-nth 0 (vl-modulelist-propagate-errors mods)))
     (vl-modulelist->names mods)))

  (defthm subsetp-equal-names-of-vl-modulelist-propagate-errors-1
    (subsetp-equal
     (vl-modulelist->names (mv-nth 1 (vl-modulelist-propagate-errors mods)))
     (vl-modulelist->names mods)))

  (defthm no-duplicatesp-equal-of-vl-modulelist-propagate-errors-0
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-modulelist-propagate-errors x))))))

  (defthm no-duplicatesp-equal-of-vl-modulelist-propagate-errors-1
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 1 (vl-modulelist-propagate-errors mods))))))

  (defthm names-of-vl-modulelist-propagate-errors-1
    ;; This is somewhat iffy and was intended to canonicalize the victims'
    ;; names to be in terms of the survivors' names.  It's not clear whether
    ;; this is a good rule.
    (implies (force (no-duplicatesp-equal (vl-modulelist->names mods)))
             (set-equiv
              (vl-modulelist->names (mv-nth 1 (vl-modulelist-propagate-errors mods)))
              (set-difference-equal
               (vl-modulelist->names mods)
               (vl-modulelist->names (mv-nth 0 (vl-modulelist-propagate-errors mods))))))))


(define vl-design-propagate-errors
  :short "Top-level function for @(see propagating-errors).  Move any faulty
design elements out of a @('good') design and into a @('bad') design."
  ((good vl-design-p
         "The good design, which has presumably just been transformed in some way,
          and may now have some design elements with fatal warnings.")
   (bad  vl-design-p
         "The bad design which holds any faulty design elements."))
  :returns
  (mv (good-- vl-design-p
              "Cut down version of the good design, with any faulty elements and
               their dependents eliminated.")
      (bad++  vl-design-p
              "Extended version of the bad design, with any faulty elements from
               @('good') moved over into it."))
  (b* (((vl-design good) good)
       ((vl-design bad)  bad)

       ;; To make this as convenient as possible, we try hard to resolve any
       ;; name conflicts.
       ((mv uniquep mods)
        (b* (((when (uniquep (vl-modulelist->names good.mods)))
              (mv t good.mods))
             (mods (mergesort good.mods))
             ((when (uniquep (vl-modulelist->names mods)))
              (mv t mods)))
          (mv nil mods)))
       ((unless uniquep)
        (raise "Name clash.  We expected the module names to be unique, but ~
                found multiple occurrences of ~&0."
               (duplicated-members (vl-modulelist->names mods)))
        (mv (make-vl-design) (make-vl-design)))

       ((mv survivors victims)
        (vl-modulelist-propagate-errors mods))

       (good-- (change-vl-design good
                                 :mods survivors))
       (bad++  (change-vl-design bad
                                 :mods (append victims bad.mods))))
    (mv good-- bad++))
  ///
  (defthm no-duplicatesp-equal-of-vl-design-propagate-errors
    (no-duplicatesp-equal
     (vl-modulelist->names
      (vl-design->mods
       (mv-nth 0 (vl-design-propagate-errors good bad)))))))

