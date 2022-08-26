; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "structure")
(include-book "centaur/misc/hons-remove-dups" :dir :system)

(defxdoc defsvtv-phasewise
  :parents (svex-stvs)
  :short "(Deprecated in favor of @(see defsvtv$).)"
  :long "<p>@('Defsvtv-phasewise') is a way of creating an SVTV -- see @(see
svex-stvs). It uses an older workflow to create the SVTV object and thus is
deprecated in favor of @(see defsvtv$-phasewise), which works similarly but
uses the @(see svtv-data) stobj-based framework.  Its syntax is the same as
@(see defsvtv$) using the @(':phases') argument rather than
@(':inputs')/@(':outputs')/@(':overrides').</p>")

(defxdoc defsvtv-phasewise
  :parents (svex-stvs)
  :short "(Deprecated) Alternative format for creating an SVTV."
  :long "
<p>This is deprecated in favor of @(see defsvtv$).</p>

<p>A longstanding frustration with the SVTV user interface is that you
need to insert the right number of underscores on each line before a cycle in
which something happens.  When the sequencing changes, you need to then insert
or delete the right number of underscores on multiple lines.</p>

<p>This alternative interface for defsvtv works around this problem by
generating an old-style SVTV from a new input format that is easier to get
right and easier to maintain.</p>

<p>The input format looks like this:</p>

@({
 (defsvtv$-phasewise my-svtv
   :design *my-design*
   :parents ... :short ... :long ...
   :simplify t   ;; default
   :phases
   (;; Phase 0:
    (:label p
     :inputs ((\"clk\" 0 :toggle 1)  ;; will toggle each phase until end or until reassigned
              (\"start\" 1)))

    ;; Phase 4:
    (:delay 4 ;; number of phases since last one listed
     :label q
     :inputs ((\"cntl\" cntl4 :hold t)) ;; will hold this value until end or until reassigned
     :overrides ((\"inst.subinst.internalsig\" internal4)
                 ;; syntax for combined conditional override/output
                 (\"inst.subinst.decompsig\" decompsig :cond decompsig-ovr :output decompsig)
                 ;; old syntax for conditional override
                 (\"inst.subinst.decompsig\" (testsig testsig-ovr))))
 
    ;; Phase 6:
    (:delay 2
     :label r
     :inputs ((\"late\" late6))
     :outputs ((\"early\" early6)))
 
    ;; Phase 8:
    (:delay 2
     :label s
     :inputs ((\"cntl\" _)) ;; release previous held value
     :outputs ((\"inst.subinst.interesting\" interesting8)))))
 })

<p>The keyword options are the same as for @(see defsvtv$), except that
@(':phases') replaces @(':inputs'), @(':overrides'), @(':outputs'),
@(':internals'), and @(':labels').</p>

<p>For now, defsvtv$-phasewise is implemented by simply preprocessing it into a @(see
defsvtv$) form.  Perhaps later both forms will instead be different interfaces
to a shared backend.</p>

<p>The format of the @(':phases') input is a list of individual phases, which are
keyword-value lists with the following keywords recognized:</p>

<ul>

<li>@(':delay'): Number of phases since the previous one in the list,
defaulting to 1.  Must be positive.  (Note: If the first phase in the list has
a delay of 1, its assignments occur on the first phase that is to be simulated.
Phase 0 is skipped, in some sense.)</li>

<li>@(':label'): Optional name of the phase, for documentation purposes.</li>

<li>@(':inputs'): Input signals to be assigned a value at that phase.  Entries are described below.</li>

<li>@(':overrides'): Internal signals to be overridden to some value at that phase.  Entries are described below.</li>

<li>@(':outputs'): Signals to be read and their values stored in variables at that phase.</li>

</ul>

<p>The format for @(':outputs') is simply a list of entries of the form</p>
@({
  (signal-name variable-name)
 })
<p>where signal-name is a string giving the real hierarchical name in the
design and variable-name is a symbol.</p>

<p>The format for @(':inputs') is a list of entries of the form:</p>
@({
 (signal-name setting [ :hold t-or-nphases | :toggle nphases ])
 })
<p>Setting can be one of:</p>
<ul>
<li>a 4vec constant, that is, an integer or a pair @('(upper . lower)'), both integers</li>
<li>a don\'t-care indicator, which is a symbol whose name is \"_\", \"-\", or \"\&amp;\" in any package</li>
<li>a variable, i.e. any other non-Boolean, non-keyword symbol.</li>
</ul>

<p>The @(':hold') keyword, if set to t, indicates that this assignment is valid
for all subsequent phases until the same signal is set again. If it is set to a
number, it is held for that number of additional phases or until it is set
again. I.e., @(':hold 0') would be the same as @(':hold nil') (but isn't
allowed), @(':hold 1') means hold for a total of two phases -- the current
one (which this entry would affect without the hold) and one additional.</p>

<p>The @(':toggle') keyword, if set to t or a positive integer @('nphases'),
indicates that the signal will be held and toggled every @('nphases') phases,
where @('t') is the same as 1.  It is only valid (for now) if the setting is a
constant.</p>

<p>Note: Don\'t use the special symbol @('~'), which is what you'd use for
@(':toggle') in the original @('defsvtv').</p>

<p>The format for @(':overrides') is similar to that of inputs, but adds two
additional keyword variables:</p>

<ul>
<li>@(':cond'), if specified, gives an override condition value (a variable or
4vec constant), making this a conditional override.  This means bits of the
signal corresponding to 1-bits of the override condition are overridden and
take the value of the corresponding bits of the override value (@('setting')
field).</li>

<li>@(':output'), if specified, gives an output variable for the same signal at
the given time.  This output will be assigned the non-overridden value of the
signal.  This syntactic convenience supports the recommended method for
decomposition proofs; see @(see def-svtv-generalized-thm).  The @(':hold') and
@(':toggle') options don't apply to the output, in that it is only sampled at
the phase in which it is declared.</li>
</ul>

<p>The @('setting') field can also take one additional form @('(value test)'),
which is another way of specifying a conditional override (this may not be used
along with the @(':cond') keyword).  Here @('test') is the override condition
and @('value') is the override value.</p>

<p>The @(':toggle') and @(':hold') keywords still apply to overrides and
conditional overrides: @(':hold') means that test and value both apply to
subsequent phases, and @(':toggle') means that test applies to subsequent
phases and value is toggled.</p>")

(fty::defprod svtv*-input
  ((setting svtv-entry-p)
   (toggle maybe-posp :rule-classes :type-prescription)
   ;; Hold NIL means don't hold
   ;; Hold 0 means hold forever.
   ;; Hold N (posp) means hold N additional cycles.
   (hold maybe-natp :rule-classes :type-prescription))
  :layout :list)

(fty::defalist svtv*-input-alist :key-type stringp :val-type svtv*-input :true-listp t)

(define svtv-variable-p (x)
  (and (symbolp x)
       (not (booleanp x))
       (not (keywordp x))
       (not (svtv-dontcare-p x)))
  ///
  (define svtv-variable-fix ((x svtv-variable-p))
    :returns (new-x svtv-variable-p)
    (mbe :logic (if (svtv-variable-p x) x 'x)
         :exec x)
    ///
    (defthm svtv-variable-fix-when-svtv-variable-p
      (implies (svtv-variable-p x)
               (equal (svtv-variable-fix x) x)))

    (fty::deffixtype svtv-variable :pred svtv-variable-p :fix svtv-variable-fix
      :equiv svtv-variable-equiv :define t)))


(fty::defalist svtv*-output-alist :key-type stringp :val-type svtv-variable :true-listp t)

(local (defthm alistp-of-extract-keywords
         (implies (alistp acc)
                  (alistp (mv-nth 0 (std::extract-keywords ctx keys args acc))))))

(local (defthm svtv-entry-p-when-condoverride
         (implies (svtv-condoverride-p x)
                  (svtv-entry-p x))
         :hints(("Goal" :in-theory (enable svtv-entry-p)))))

(local (in-theory (disable std::extract-keywords
                           assoc-equal
                           set::sets-are-true-lists-cheap
                           true-listp)))

(define svtv*-parse-input (x overridep)
  :returns (mv (input-entry svtv*-input-alist-p)
               (output-entry svtv*-output-alist-p))
  ;; :mode :program
  (b* ((intype (if overridep "Override" "Input"))
       ((unless (true-listp x))
        (raise "~s0 entries should be true-lists" intype)
        (mv nil nil))
       (signame (car x))
       ((unless (stringp signame))
        (raise "~s0 entries should begin with signal names (strings) -- bad: ~x1" intype x)
        (mv nil nil))
       (entry (second x))
       ((unless (svtv-entry-p entry))
        (raise "~s0 entries should have second elements that satisfy svtv-entry-p -- bad: ~x1" intype x)
        (mv nil nil))
       ((unless (or overridep (not (svtv-condoverride-p entry))))
        (raise "~s0 entries should not be conditional overrides -- bad: ~x1" intype x)
        (mv nil nil))
       (rest (cddr x))
       ((unless rest)
        (mv (list (cons signame (make-svtv*-input :setting entry))) nil))
       ((mv kwd-alist extra) (std::extract-keywords 'svtv*-parse-input
                                                    (if overridep
                                                        '(:toggle :hold :cond :output)
                                                      '(:toggle :hold))
                                                    (cddr x) nil))
       ((when extra)
        (raise "~s0 entry contains extra junk: ~x1" intype x)
        (mv nil nil))
       ((when (and (assoc :toggle kwd-alist)
                   (assoc :hold kwd-alist)))
        (raise "~s0 entry should not contain both :hold and :toggle: ~x1" intype x)
        (mv nil nil))
       ((unless (or (booleanp (cdr (assoc :hold kwd-alist)))
                    (posp (cdr (assoc :hold kwd-alist)))))
        (raise "~s0 entry ~x1: :hold value should be positive integer or Boolean" intype x)
        (mv nil nil))
       ((unless (or (booleanp (cdr (assoc :toggle kwd-alist)))
                    (posp (cdr (assoc :toggle kwd-alist)))))
        (raise "~s0 entry ~x1: :toggle value should be positive integer or Boolean" intype x)
        (mv nil nil))
       (toggle (if (eq t (cdr (assoc :toggle kwd-alist)))
                   1
                 (cdr (assoc :toggle kwd-alist))))
       (hold   (if (eq t (cdr (assoc :hold kwd-alist)))
                   0
                 (cdr (assoc :hold kwd-alist))))
       ((unless overridep)
        (mv (list (cons signame (make-svtv*-input :setting entry :toggle toggle :hold hold))) nil))
       ;; Couple of extra things to check for overrides.
       (cond (cdr (assoc :cond kwd-alist)))
       ((unless (or (not cond)
                    (svtv-baseentry-p entry)))
        (raise "~s0: when using :cond keyword, value must be a valid svtv-baseentry -- bad: ~x1~%" intype x)
        (mv nil nil))
       ((unless (or (not cond)
                    (svtv-baseentry-p cond)))
        (raise "~s0: :cond keyword must be a valid svtv-baseentry -- bad: ~x1~%" intype x)
        (mv nil nil))
       (entry (if cond
                  (make-svtv-condoverride :value entry :test cond)
                entry))
       (output (cdr (assoc :output kwd-alist)))
       (input-result (list (cons signame (make-svtv*-input :setting entry :toggle toggle :hold hold))))
       ((unless output)
        (mv input-result nil))
       ((unless (svtv-variable-p output))
        (raise "Output entries should have second elements that are variable names -- bad: ~x0" x)
        (mv nil nil)))
    (mv input-result (list (cons signame output)))))
       
       
       

(define svtv*-parse-inputs (x overridep)
  :returns (mv (inputs svtv*-input-alist-p)
               (outputs svtv*-output-alist-p))
  (if (atom x)
      (mv nil nil)
    (b* (((mv inputs1 outputs1) (svtv*-parse-input (car x) overridep))
         ((mv inputs2 outputs2) (svtv*-parse-inputs (cdr x) overridep)))
      (mv (append inputs1 inputs2)
          (append outputs1 outputs2)))))

(define svtv*-parse-output (x)
  :returns (singleton svtv*-output-alist-p)
                      ;; :mode :program
  (b* (((unless (true-listp x))
        (raise "Output entries should be true-lists"))
       ((unless (stringp (car x)))
        (raise "Output entries should begin with signal names (strings) -- bad: ~x0" x))
       ((unless (svtv-variable-p (second x)))
        (raise "Output entries should have second elements that are variable names -- bad: ~x0" x)))
    (list (cons (car x) (second x)))))

(define svtv*-parse-outputs (x)
  :returns (outputs svtv*-output-alist-p)
  (if (atom x)
      nil
    (append (svtv*-parse-output (car x))
            (svtv*-parse-outputs (cdr x)))))



(fty::defprod svtv*-phase
  ((label symbolp :default 'acl2::? :rule-classes :type-prescription)
   (inputs svtv*-input-alist-p)
   (overrides svtv*-input-alist-p)
   (outputs svtv*-output-alist-p))
  :layout :list)

(fty::deflist svtv*-phaselist :elt-type svtv*-phase :true-listp t)



(define svtv*-parse-phase (x)
  :returns (phases  svtv*-phaselist-p)
  (b* (((mv kwd-alist extra) (std::extract-keywords 'svtv*-parse-phase
                                                    '(:delay :label :inputs :overrides :outputs)
                                                    x nil))
       ((when extra)
        (raise "Extra non-keywords found in phase: ~x0" x))
       (delay (std::getarg :delay 1 kwd-alist))
       ((unless (posp delay))
        (raise "Delay must be a natural number: ~x0" x))
       (label (std::getarg :label :? kwd-alist))
       ((unless (symbolp label))
        (raise "Label must be a symbol: ~x0" x))
       ((mv inputs &) (svtv*-parse-inputs (cdr (assoc :inputs kwd-alist)) nil))
       ((mv overrides override-outputs) (svtv*-parse-inputs (cdr (assoc :overrides kwd-alist)) t))
       (outputs (svtv*-parse-outputs (cdr (assoc :outputs kwd-alist)))))
    (append (repeat (1- delay) (make-svtv*-phase))
            (list (make-svtv*-phase ;; :delay delay
                   :label label
                   :inputs inputs
                   :overrides overrides
                   :outputs (append override-outputs outputs))))))

(define svtv*-parse-phases (x)
  :Returns (phases svtv*-phaselist-p)
  (if (atom x)
      nil
    (b* ((phases (svtv*-parse-phase (car x))))
      (append phases
              (svtv*-parse-phases (cdr x))))))

(define svtv*-phaselist-nphases ((x svtv*-phaselist-p))
  (len x))

(define svtv*-input-signal-find-next-phase ((name stringp)
                                            (phases svtv*-phaselist-p)
                                            (overridep))
  :returns (mv (inactive-phases natp :rule-classes :type-prescription)
               (entry (implies entry (svtv*-input-p entry)))
               (suffix svtv*-phaselist-p))
  :prepwork ((local (defthm svtv*-input-p-of-input-alist-entry
                      (implies (and (svtv*-input-alist-p x)
                                    (assoc k x))
                               (svtv*-input-p (cdr (assoc k x))))
                      :hints(("Goal" :in-theory (enable svtv*-input-alist-p assoc-equal)))))
             (local (defthm consp-assoc-equal-of-svtv*-input-alist-p-rw
                      (implies (and (svtv*-input-alist-p x)
                                    (assoc k x))
                               (consp (assoc k x)))
                      :hints(("Goal" :in-theory (enable assoc-equal)))))
             (local (defthm cdr-assoc-equal-of-svtv*-input-alist-p-rw
                      (implies (and (svtv*-input-alist-p x)
                                    (assoc k x))
                               (cdr (assoc k x)))
                      :hints(("Goal" :in-theory (enable assoc-equal))))))
  :verify-guards nil
  (b* (((when (atom phases))
        (mv 1 nil nil))
       ((svtv*-phase phase1) (car phases))
       (alist (if overridep phase1.overrides phase1.inputs))
       (look (assoc-equal (acl2::str-fix name) alist))
       ((when look)
        (mv 1 (cdr look) (svtv*-phaselist-fix (cdr phases))))
       ((mv rest-phases entry suffix) (svtv*-input-signal-find-next-phase name (cdr phases) overridep)))
    (mv (+ 1 rest-phases) entry suffix))
  ///
  (verify-guards svtv*-input-signal-find-next-phase)

  (defret len-phases-of-svtv*-input-signal-find-next-phase
    (implies entry (< (len suffix) (len phases)))
    :rule-classes :linear)

  (defret nphases-of-<fn>
    (equal (svtv*-phaselist-nphases suffix)
           (+ (svtv*-phaselist-nphases phases)
              (if entry 0 1)
              (- inactive-phases)))
    :hints(("Goal" :in-theory (enable svtv*-phaselist-nphases))))

  (defret next-phase-when-not-found-of-<fn>
    (implies (not entry)
             (equal inactive-phases
                    (1+ (svtv*-phaselist-nphases phases))))
    :hints(("Goal" :in-theory (enable svtv*-phaselist-nphases)))))

(define svtv*-input-toggle ((nphases natp)
                            (curr-toggle posp)
                            (toggle posp)
                            (val 4vec-p))
  :returns (entries 4veclist-p)
  (b* (((when (zp nphases)) nil)
       (rest (if (eql 1 (lposfix curr-toggle))
                 (svtv*-input-toggle (1- nphases)
                                     (lposfix toggle)
                                     toggle
                                     (4vec-bitnot val))
               (svtv*-input-toggle (1- nphases)
                                   (1- curr-toggle)
                                   toggle
                                   val))))
    (cons (4vec-fix val) rest))
  ///
  (defret len-of-<fn>
    (equal (len entries) (nfix nphases))))

(define svtv*-condoverride-toggle ((nphases natp)
                                   (curr-toggle posp)
                                   (toggle posp)
                                   (val 4vec-p)
                                   (test svtv-baseentry-p))
  :returns (entries svtv-entrylist-p
                    :hints(("Goal" :in-theory (enable svtv-entry-p))))
  :prepwork ((local (defthm svtv-baseentry-p-when-4vec-p
                      (implies (4vec-p x)
                               (svtv-baseentry-p x))
                      :hints(("Goal" :in-theory (enable svtv-baseentry-p))))))
  (b* (((when (zp nphases)) nil)
       (rest (if (eql 1 (lposfix curr-toggle))
                 (svtv*-condoverride-toggle (1- nphases)
                                     (lposfix toggle)
                                     toggle
                                     (4vec-bitnot val)
                                     test)
               (svtv*-condoverride-toggle (1- nphases)
                                   (1- curr-toggle)
                                   toggle
                                   val
                                   test))))
    (cons (svtv-condoverride (4vec-fix val) test) rest))
  ///
  (defret len-of-<fn>
    (equal (len entries) (nfix nphases))))

(define svtv*-input-entry-to-svtv-line-entries ((entry svtv*-input-p)
                                                 (nphases natp))
  :returns (entries svtv-entrylist-p)
  :prepwork ((local (defthm svtv-entrylist-p-when-4veclist-p
                      (implies (4veclist-p x)
                               (svtv-entrylist-p x))
                      :hints(("Goal" :in-theory (enable svtv-entrylist-p 4veclist-p
                                                        svtv-entry-p
                                                        svtv-baseentry-p))))))
  (b* (((svtv*-input entry))
       ((when (zp nphases)) nil)
       ((when (svtv-dontcare-p entry.setting))
        (repeat nphases entry.setting))
       ((when entry.hold)
        (if (eql entry.hold 0)
            (repeat nphases entry.setting)
          (b* ((reps (min nphases (+ 1 entry.hold))))
            (append (repeat reps entry.setting)
                    (repeat (- nphases reps) '&)))))
       ((unless entry.toggle)
        (cons entry.setting (repeat (1- nphases) '&)))
       ;; toggle is positive
       ((unless (svtv-condoverride-p entry.setting))
        (b* (((unless (4vec-p entry.setting))
              (raise "Entry with a :toggle must have a constant value")
              (repeat nphases '&)))
          (svtv*-input-toggle nphases
                              entry.toggle ;; phases at current setting
                              entry.toggle ;; toggle period
                              entry.setting)))
       ((svtv-condoverride entry.setting))
       ((unless (4vec-p entry.setting.value))
        (raise "Entry with a :toggle must have a constant value")
        (repeat nphases '&)))
    (svtv*-condoverride-toggle nphases
                               entry.toggle ;; phases at current setting
                               entry.toggle ;; toggle period
                               entry.setting.value
                               entry.setting.test))
  ///
  (defret len-of-<fn>
    (equal (len entries) (nfix nphases))))
        
       


       
(define svtv*-input-to-svtv-line-entries ((name stringp)
                                          (entry svtv*-input-p)
                                          (phases svtv*-phaselist-p)
                                          (overridep))
  :measure (len phases)
  ;; First element returned corresponds to the first phase in the list --
  ;; i.e. the delay on that phase is ignored.
  :returns (entries svtv-entrylist-p)
  (b* (((mv next-delay next-entry next-phases) (svtv*-input-signal-find-next-phase name phases overridep))
       (prefix (svtv*-input-entry-to-svtv-line-entries entry next-delay))
       ((unless next-entry) prefix))
    (append prefix
            (svtv*-input-to-svtv-line-entries name next-entry next-phases overridep)))
  ///
  (defret len-of-<fn>
    (equal (len entries) (+ 1 (svtv*-phaselist-nphases phases)))))

(define svtv*-inputs-to-svtv-lines ((names string-listp)
                                    (phases svtv*-phaselist-p)
                                    (overridep))
  (if (atom names)
      nil
    (cons (cons (acl2::str-fix (car names))
                (cdr (svtv*-input-to-svtv-line-entries (car names)
                                                       (make-svtv*-input :setting '&)
                                                       phases overridep)))
          (svtv*-inputs-to-svtv-lines (cdr names) phases overridep))))

    


(define svtv*-output-to-svtv-line-entries ((name stringp)
                                           (phases svtv*-phaselist-p))
  :returns (entries svtv-entrylist-p)
  :prepwork ((local (defthm consp-assoc-equal-of-svtv*-output-alist-p-rw
                      (implies (and (svtv*-output-alist-p x)
                                    (assoc k x))
                               (consp (assoc k x)))
                      :hints(("Goal" :in-theory (enable assoc-equal)))))
             (local (defthm svtv-entry-p-when-svtv-variable-p
                      (implies (svtv-variable-p x)
                               (svtv-entry-p x))
                      :hints(("Goal" :in-theory (enable svtv-variable-p
                                                        svtv-entry-p
                                                        svtv-baseentry-p)))))
             (local (defthm svtv-entry-p-lookup-in-svtv*-output-alist-p
                      (implies (and (svtv*-output-alist-p x)
                                    (assoc k x))
                               (svtv-entry-p (cdr (assoc k x))))
                      :hints(("Goal" :in-theory (enable svtv*-output-alist-p
                                                        assoc-equal))))))
  (b* (((when (atom phases)) nil)
       ((svtv*-phase phase1) (car phases))
       ; (prefix (repeat (1- phase1.delay) '&))
       (entry (or (cdr (assoc-equal (acl2::str-fix name) phase1.outputs)) '&)))
    (cons entry (svtv*-output-to-svtv-line-entries name (cdr phases))))
  ///
  (defret len-of-<fn>
    (equal (len entries)
           (svtv*-phaselist-nphases phases))
    :hints(("Goal" :in-theory (enable svtv*-phaselist-nphases)))))

(define svtv*-outputs-to-svtv-lines ((names string-listp)
                                     (phases svtv*-phaselist-p))
  (if (atom names)
      nil
    (cons (cons (acl2::str-fix (car names))
                (svtv*-output-to-svtv-line-entries (car names) phases))
          (svtv*-outputs-to-svtv-lines (cdr names) phases))))




(define svtv*-phaselist-collect-inputnames ((x svtv*-phaselist-p))
  :returns (names string-listp)
  :prepwork ((local (defthm string-listp-of-strip-input-alist
                      (implies (svtv*-input-alist-p x)
                               (string-listp (strip-cars x)))
                      :hints(("Goal" :in-theory (enable svtv*-input-alist-p))) ))
             (local (defthm string-listp-append
                      (implies (and (string-listp x)
                                    (string-listp y))
                               (string-listp (append x y))))))
  (if (atom x)
      nil
    (append (strip-cars (svtv*-phase->inputs (car x)))
            (svtv*-phaselist-collect-inputnames (cdr x)))))

(define svtv*-phaselist-collect-overridenames ((x svtv*-phaselist-p))
  :returns (names string-listp)
  :prepwork ((local (defthm string-listp-of-strip-input-alist
                      (implies (svtv*-input-alist-p x)
                               (string-listp (strip-cars x)))
                      :hints(("Goal" :in-theory (enable svtv*-input-alist-p))) ))
             (local (defthm string-listp-append
                      (implies (and (string-listp x)
                                    (string-listp y))
                               (string-listp (append x y))))))
  (if (atom x)
      nil
    (append (strip-cars (svtv*-phase->overrides (car x)))
            (svtv*-phaselist-collect-overridenames (cdr x)))))

(define svtv*-phaselist-collect-outputnames ((x svtv*-phaselist-p))
  :returns (names string-listp)
  :prepwork ((local (defthm string-listp-of-strip-output-alist
                      (implies (svtv*-output-alist-p x)
                               (string-listp (strip-cars x)))
                      :hints(("Goal" :in-theory (enable svtv*-output-alist-p))) ))
             (local (defthm string-listp-append
                      (implies (and (string-listp x)
                                    (string-listp y))
                               (string-listp (append x y))))))
  (if (atom x)
      nil
    (append (strip-cars (svtv*-phase->outputs (car x)))
            (svtv*-phaselist-collect-outputnames (cdr x)))))


(define svtv*-phaselist-collect-labels ((x svtv*-phaselist-p))
  :returns (label symbol-listp)
  :prepwork ((local (defthm symbol-listp-of-repeat
                      (implies (Symbolp x)
                               (symbol-listp (repeat n x)))
                      :hints(("Goal" :in-theory (enable repeat)))))
             (local (defthm symbol-listp-of-append
                      (implies (and (Symbol-listp x)
                                    (symbol-listp y))
                               (symbol-listp (append x y))))))
  (if (Atom x)
      nil
    (b* (((svtv*-phase x1) (car x)))
      ;;    (delay-1 (1- x1.delay)))
      ;; (append (make-list delay-1 :initial-element 'acl2::?)
      (cons (svtv*-phase->label (car x))
            (svtv*-phaselist-collect-labels (cdr x))))))

      
(define defsvtv*-phases-to-defsvtv-args ((x svtv*-phaselist-p))
  :prepwork ((local (Defthm string-listp-of-remove-duplicates
                      (implies (string-listp x)
                               (string-listp (remove-duplicates-equal x)))
                      :hints(("Goal" :in-theory (enable remove-duplicates-equal))))))
  (b* ((innames (acl2::hons-remove-dups (svtv*-phaselist-collect-inputnames x)))
       (overridenames (acl2::hons-remove-dups (svtv*-phaselist-collect-overridenames x)))
       (outputnames (acl2::hons-remove-dups (svtv*-phaselist-collect-outputnames x)))
       (inputs (svtv*-inputs-to-svtv-lines innames x nil))
       (overrides (svtv*-inputs-to-svtv-lines overridenames x t))
       (outputs (svtv*-outputs-to-svtv-lines outputnames x))
       (labels (svtv*-phaselist-collect-labels x)))
    (list :inputs (list 'quote inputs) :overrides (list 'quote overrides) :outputs (list 'quote outputs) :labels (list 'quote labels))))

(define maybe-keyword-arg ((name symbolp) (alist alistp))
  (b* ((look (assoc-eq name alist)))
    (and look (list name (cdr look)))))

(define maybe-keyword-args ((names symbol-listp) (alist alistp))
  (if (atom names)
      nil
    (append (maybe-keyword-arg (car names) alist)
            (maybe-keyword-args (cdr names) alist))))

(define defsvtv-phasewise-fn (name args)
  :mode :program
  (b* ((transferred-keys
        '(:design :mod :parents :short :long :state-machine :simplify :pre-simplify
                                 :define-macros :initial-state-vars :keep-final-state :keep-all-states))
       (all-keys (cons :phases transferred-keys))
       ((mv kwd-alist rest) 
        (std::extract-keywords `(defsvtv-phasewise ,name) all-keys args nil))
       ((when rest)
        (raise "Extra args in defsvtv-phasewise form"))
       (phases (svtv*-parse-phases (cdr (assoc :phases kwd-alist))))
       (main-args (defsvtv*-phases-to-defsvtv-args phases)))
    `(defsvtv ,name
       ,@(maybe-keyword-args transferred-keys kwd-alist)
       ,@main-args)))


(defmacro defsvtv-phasewise (name &rest args)
  (defsvtv-phasewise-fn name args))


;; Functions for programmatic manipulation of a phaselist.

(define nth-phase ((n natp) (x svtv*-phaselist-p))
  :returns (phase svtv*-phase-p)
  (mbe :logic (svtv*-phase-fix (nth n x))
       :exec (if (< n (len x))
                 (nth n x)
               (make-svtv*-phase :label nil))))

(define update-nth-phase ((n natp) (phase svtv*-phase-p) (x svtv*-phaselist-p))
  :returns (new-x svtv*-phaselist-p)
  :prepwork ((local (defthm update-nth-when-out-of-bound
                      (implies (< (len x) (nfix n))
                               (equal (update-nth n v x)
                                      (append x (repeat (- (nfix n) (len x)) nil) (list v))))
                      :hints(("Goal" :in-theory (e/d (repeat)
                                                     (acl2::equal-of-append-repeat)))))))
  (mbe :logic (svtv*-phaselist-fix (update-nth n phase x))
       :exec (if (<= n (len x))
                 (update-nth n phase x)
               (append x (repeat (- n (len x)) (make-svtv*-phase :label nil)) (list phase))))

  ///
  (local (include-book "std/lists/nth" :dir :System))
  
  (defthm nth-phase-of-update-nth-phase
    (equal (nth-phase m (update-nth-phase n phase x))
           (if (equal (nfix n) (nfix m))
               (svtv*-phase-fix phase)
             (nth-phase m x)))
    :hints(("Goal" :in-theory (enable nth-phase)))))




#||

:trans1  (defsvtv-phasewise my-svtv
   :design *my-design*
   ;; :parents ... :short ... :long ...
   :simplify t   ;; default
   :phases
   (;; Phase 0:
    (:label p
     :inputs (("clk" 0 :toggle 1)  ;; will toggle each phase until end or until reassigned
              ("start" 1)))

    ;; Phase 4:
    (:delay 4 ;; number of phases since last one listed
     :label q
     :inputs (("cntl" cntl4 :hold t)) ;; will hold this value until end or until reassigned
     :overrides (("inst.subinst.internalsig" internal4)
                 ;; syntax for combined conditional override/output
                 ("inst.subinst.decompsig" decompsig :cond decompsig-ovr :output decompsig)
                 ;; old syntax for conditional override
                 ("inst.subinst.decompsig" (testsig testsig-ovr))))
 
    ;; Phase 6:
    (:delay 2
     :label r
     :inputs (("late" late6))
     :outputs (("early" early6)))
 
    ;; Phase 8:
    (:delay 2
     :label s
     :inputs (("cntl" _)) ;; release previous held value
     :outputs (("inst.subinst.interesting" interesting8)))))

||#
