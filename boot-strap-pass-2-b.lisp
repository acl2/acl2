; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; This is the second of a pair of files; see boot-strap-pass-2-a.lisp for the
; first of the pair.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Support for system-verify-guards
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section supports a mechanism for users to extend the set of
; guard-verified functions.  They do so in community books under books/system/,
; which are checked when building with feature :acl2-devel, for example
; building with `make' with ACL2_DEVEL=d.  But normal builds will not set that
; feature, and will simply trust that functions marked in
; *system-verify-guards-alist* can be guard-verified.  For more about this, see
; the comments in *system-verify-guards-alist*.

; A flaw in our approach is that user-supplied guard verifications may depend
; on package axioms.  Thus, we view such verifications as strong hints, rather
; than as ironclad guarantees that the functions can be guard-verified in
; definitional (or even conservative) extensions of the ground-zero theory.  We
; consider this sufficient, as the event that some package axiom will cause
; such bogus marking as guard-verified seems much less likely than the event
; that our system has other serious bugs!

(verify-termination-boot-strap safe-access-command-tuple-form) ; and guards

(verify-termination-boot-strap acl2-system-namep) ; and guards

(mutual-recursion

(defun system-pseudo-termp (x w)
  (declare (xargs :guard (and (pseudo-termp x)
                              (plist-worldp w))
                  :mode :logic))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cdr (cdr x)))))
        ((not (true-listp x)) nil)
        ((not (system-pseudo-term-listp (cdr x) w)) nil)
        (t (if (symbolp (car x))
               (acl2-system-namep (car x) w)
             (system-pseudo-termp (caddr (car x)) w)))))

(defun system-pseudo-term-listp (lst w)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp w))
                  :mode :logic))
  (cond ((atom lst) (equal lst nil))
        (t (and (system-pseudo-termp (car lst) w)
                (system-pseudo-term-listp (cdr lst) w)))))

)

(defun pair-fns-with-measured-subsets (fns wrld acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld)
                              (true-listp acc))))
  (cond ((endp fns) (reverse acc))
        (t (pair-fns-with-measured-subsets
            (cdr fns)
            wrld
            (cons (let* ((fn (car fns))
                         (justification (getpropc fn 'justification nil wrld))
                         (ms0 (and (weak-justification-p justification) ; for guard
                                   (access justification justification
                                           :measure)))
                         (ms (and ms0
                                  (if (and (pseudo-termp ms0) ; for guard
                                           (system-pseudo-termp ms0 wrld))
                                      ms0
                                    (cons :? (access justification
                                                     justification :subset))))))
                    (cons fn ms))
                  acc)))))

(defun new-verify-guards-fns1 (wrld installed-wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (plist-worldp installed-wrld)
                              (symbol-listp acc))))
  (cond ((or (endp wrld)
             (and (eq (caar wrld) 'command-landmark)
                  (eq (cadar wrld) 'global-value)
                  (equal (safe-access-command-tuple-form (cddar wrld))
                         '(exit-boot-strap-mode))))
         (pair-fns-with-measured-subsets
          (strict-merge-sort-symbol< acc)
          installed-wrld
          nil))
        ((and (eq (cadar wrld) 'symbol-class)
              (eq (cddar wrld) :COMMON-LISP-COMPLIANT)
              (getpropc (caar wrld) 'predefined nil installed-wrld))
         (new-verify-guards-fns1 (cdr wrld)
                                 installed-wrld
                                 (cons (caar wrld) acc)))
        (t (new-verify-guards-fns1 (cdr wrld) installed-wrld acc))))

(defun new-verify-guards-fns (state)

; It is important for performance that this function be guard-verified, because
; it is called inside an assert-event form in chk-new-verified-guards, which
; causes evaluation to be in safe-mode and would cause evaluation of
; plist-worldp on behalf of guard-checking for new-verify-guards-fns1.

  (declare (xargs :stobjs state))
  (let ((wrld (w state)))
    (new-verify-guards-fns1 wrld wrld nil)))

; An error occurred when moving this below, because arities-okp is to be put
; into :logic mode and calls logicp.
(verify-termination-boot-strap logicp) ; and guards

(defconst *devel-check-book* "system/devel-check")

(defmacro chk-new-verified-guards ()
  `(progn (include-book ,*devel-check-book*
                        :DIR :SYSTEM
                        :UNCERTIFIED-OKP nil
                        :DEFAXIOMS-OKP nil
                        :SKIP-PROOFS-OKP nil
                        :TTAGS nil)
          (assert-event
           (equal *system-verify-guards-alist*
                  (new-verify-guards-fns state))
           :msg (msg "ERROR: The set of newly guard-verified functions from ~
                      the ACL2 community book ~x0 does not match the expected ~
                      set from the constant ~
                      *system-verify-guards-alist*.~|~%From the ~
                      book:~|~X13~|~%Expected from ~
                      *system-verify-guards-alist*:~|~X23~|"
                     ,*devel-check-book*
                     (new-verify-guards-fns state)
                     *system-verify-guards-alist*
                     nil))
          (value-triple :CHK-NEW-VERIFIED-GUARDS-SUCCESS)))

(defun system-verify-guards-aux (fns-alist acc acc1 old-num)
  (declare (xargs :guard
                  (and (alistp fns-alist)
                       (nat-listp (strip-cars fns-alist)) ; and ordered by >
                       (symbol-alistp (strip-cdrs fns-alist))
                       (true-list-listp acc1))
                  :ruler-extenders :lambdas))
  (let* ((num/pair (car fns-alist))
         (num (car num/pair))
         (entry (cdr num/pair))
         (next (and fns-alist ; optimization
                    `(,(car entry)
                      ,@(let ((measure (cdr entry)))
                          (and measure
                               `((declare (xargs :measure
                                                 ,measure))))))))
         (same-num-p (and fns-alist
                          (eql num old-num)))
         (acc (if (or (null acc1) ; true at the top-level
                      same-num-p)
                  acc
                (list* `(skip-proofs (verify-termination-boot-strap ,@acc1))

; Normally the following verify-guards will be redundant.  However, if the
; original defun specified xargs :verify-guards nil, then this will be
; necessary.  (An example as of this writing is remove-lambdas.)

                       `(skip-proofs (verify-guards ,(caar acc1)))
                       acc))))
    (cond ((endp fns-alist) acc)
          (t (system-verify-guards-aux
              (cdr fns-alist)
              acc
              (if same-num-p ; accumulate into mutual-recursion
                  (cons next acc1)
                (list next))
              num)))))

(defun cons-absolute-event-numbers (fns-alist wrld acc)
  (declare (xargs :guard (and (symbol-alistp fns-alist)
                              (plist-worldp wrld)
                              (alistp acc))))
  (cond ((endp fns-alist) acc)
        (t (cons-absolute-event-numbers
            (cdr fns-alist)
            wrld
            (acons (or (getpropc (caar fns-alist) 'absolute-event-number nil
                                 wrld)
                       (er hard? 'cons-absolute-event-numbers
                           "The 'absolute-event-number property is missing ~
                            for ~x0."
                           (caar fns-alist)))
                   (car fns-alist)
                   acc)))))

(defun sort->-absolute-event-number (fns-alist wrld)
  (declare (xargs :mode :program)) ; because of merge-sort-car->
  (merge-sort-car->
   (cons-absolute-event-numbers fns-alist wrld nil)))

(defmacro system-verify-guards (alist)
  `(make-event
    (let ((events (system-verify-guards-aux
                   (sort->-absolute-event-number
                    ,alist
                    (w state))
                   nil nil nil)))
      (list* 'encapsulate
             ()
             '(set-inhibit-warnings "Skip-proofs")
             '(set-verify-guards-eagerness 2)
             events))))

; Normally we trust *system-verify-guards-alist*, installing guard-verified
; functions with the two calls below of system-verify-guards.  But when feature
; :acl2-devel is set, then we do not do so, as we instead intend to run
; (chk-new-verified-guards) in order to check that the effect of
; system-verify-guards is sound.  This check is performed by using `make' with
; target devel-check; see the comments in *system-verify-guards-alist*.

; Note that we have two calls of system-verify-guards below.  First, we verify
; termination and guards for other than apply$ scions.  That is necessary
; before we verify termination and guards for apply$-prim and badge, which is
; done next.  Finally, we verify termination and guards for apply$ scions.

#+(and acl2-loop-only ; Note that make-event can't be called here in raw Lisp.
       (not acl2-devel))
(system-verify-guards *system-verify-guards-alist-1*)

#-acl2-devel
(verify-termination-boot-strap apply$-prim) ; and guards
#-acl2-devel
(verify-termination-boot-strap badge) ; and guards

#-acl2-devel
(in-theory (disable badge
                    (:executable-counterpart badge)))

#+(and acl2-loop-only ; Note that make-event can't be called here in raw Lisp.
       (not acl2-devel))
(system-verify-guards *system-verify-guards-alist-2*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Support for system-events
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro system-event (event)

; (System-event E) expands to (skip-proofs E) during normal builds.  However,
; for acl2-devel builds (see discussion under the section "Support for
; system-verify-guards" earlier in this file), we merely add the event to a
; table, to be checked by Make target devel-check, which invokes function
; system-verify-skip-proofs for that purpose.

  #+acl2-devel `(table system-event-table ',event t)

; It is tempting to generate a progn, where the skip-proofs is preceded by:

; (value-triple ,(concatenate 'string "Verified in community book " book-name))

; However, that value-triple event doesn't show up with any of :pe, :pcb, or
; :pcb!, so we won't bother.

  #-acl2-devel `(skip-proofs ,event))

(defun system-events-fn (events)
  (declare (xargs :guard (true-listp events)))
  (cond ((endp events) nil)
        (t (cons `(system-event ,(car events))
                 (system-events-fn (cdr events))))))

(defmacro system-events (&rest events)
  (declare (xargs :guard t))
  (cons 'progn (system-events-fn events)))

(defmacro check-system-events ()

; Executed by "make devel-check".

  '(make-event
    (let ((event-book-alist (table-alist 'system-event-table (w state))))
      `(progn (include-book ,*devel-check-book* :dir :system)
              (set-enforce-redundancy t)
              ,@(strip-cars event-book-alist)
              (value-triple :CHECK-SYSTEM-EVENTS-SUCCESS)))))

(system-events ; "system/termp"

(defthm legal-variable-or-constant-namep-implies-symbolp
  (implies (not (symbolp x))
           (not (legal-variable-or-constant-namep x))))

(in-theory (disable legal-variable-or-constant-namep))

(defthm termp-implies-pseudo-termp
  (implies (termp x w)
           (pseudo-termp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm term-listp-implies-pseudo-term-listp
  (implies (term-listp x w)
           (pseudo-term-listp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm arities-okp-implies-arity
  (implies (and (arities-okp user-table w)
                (assoc fn user-table))
           (equal (arity fn w) (cdr (assoc fn user-table)))))

(defthm arities-okp-implies-logicp
  (implies (and (arities-okp user-table w)
                (assoc fn user-table))
           (logicp fn w)))

(in-theory (disable arity arities-okp logicp))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Finishing up with apply$
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Events in this section must occur after the calls above of
; system-verify-guards.  They would naturally belong in apply.lisp were it not
; for the fact that the relevant functions are in :program mode at that point.

; We disable the executable counterparts of tamep because badge-userfn is
; undefined, so running tamep on constants, such as (tamep '(CONS A B)) fails
; and introduces a HIDE.  However, expansion of the definitional axioms allow
; us to use the badge properties of warrants.

; Of course, when acl2-devel is true then these functions are in :program mode,
; so it makes no sense to try to disable them.

#-acl2-devel
(in-theory (disable (:executable-counterpart tamep)
                    (:executable-counterpart tamep-functionp)
                    (:executable-counterpart suitably-tamep-listp)
                    ev$
                    ev$-list
                    apply$
                    (:executable-counterpart apply$)))

;;; Finish up on "7. Functional Equivalence"

#-acl2-loop-only
(progn (declaim (ftype (function (t t)
                                 (values t))
                       apply$))
       (declaim (ftype (function (t)
                                 (values t))
                       tamep-functionp)))

#-acl2-devel ; because apply$ is in :program mode when #+acl2-devel
(defun-sk apply$-equivalence (fn1 fn2)
  (declare (xargs :verify-guards t ; avoid make-event in boot-strap
                  :guard t))
  (forall (args)

; We use ec-call to support guard verification in "make proofs".

    (equal (ec-call (apply$ fn1 args))
           (ec-call (apply$ fn2 args)))))

#-acl2-devel ; because apply$-equivalence is #-acl2-devel
(defun fn-equal (fn1 fn2)
  (declare (xargs :mode :logic :guard t))
  (if (equal fn1 fn2)
      t
      (and (tamep-functionp fn1)
           (tamep-functionp fn2)
           (apply$-equivalence fn1 fn2))))

(system-events ; "system/apply/apply"
(defequiv fn-equal :package :legacy)
)

(system-events ; "system/apply/loop-scions"
(defthm natp-from-to-by-measure
  (natp (from-to-by-measure i j))
  :rule-classes :type-prescription)
)

(defun mempos (e lst)

; Even though it is not necessary to define mempos in order to build ACL2, but
; because the book books/projects/apply/loop.lisp introduces it to establish
; the loop$-as-correspondence rule, it is best not to let the user define it.
; It is identically defined in community book books/projects/apply/loop.lisp,
; which should be included anytime the user is serious about using scions.

  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) 0)
        ((equal e (car lst)) 0)
        (t (+ 1 (mempos e (cdr lst))))))

#-acl2-devel
(when-pass-2

; The following function symbols must be in :logic mode, and they are, from the
; system-verify-guards calls above.  Moreover, we must restrict to pass 2 since
; defwarrant is defined within when-pass-2.  Of course, this source file
; (boot-strap-pass-2-b.lisp) is only given to LD in pass 2 anyhow; but by using
; when-pass-2, we don't rely on that and more importantly, we do not evaluate
; these forms in raw Lisp (important because defwarrant is not defined during
; compilation).

; WARNING.  Note that proofs are skipped for forms in the scope of when-pass-2.
; So there is a critical invariant: that all of the defwarrant forms below are
; justified in the books.  As of this writing in late January 2019, that is the
; case; see the defun$ forms in community book
; books/system/apply/loop-scions.lisp, whose proof obligations are checked when
; running #+acl2-devel builds.  Perhaps we should consider using system-events
; for ensuring this invariant.

 (defwarrant empty-loop$-as-tuplep)
 (defwarrant car-loop$-as-tuple)
 (defwarrant cdr-loop$-as-tuple)
 (defwarrant loop$-as-ac)
 (defwarrant loop$-as)
 (defwarrant from-to-by-measure)
 (defwarrant tails-ac)
 (defwarrant tails)
 (defwarrant from-to-by-ac)
 (defwarrant from-to-by)
 (defwarrant until$-ac)
 (defwarrant until$)
 (defwarrant until$+-ac)
 (defwarrant until$+)
 (defwarrant when$-ac)
 (defwarrant when$)
 (defwarrant when$+-ac)
 (defwarrant when$+)
 (defwarrant sum$-ac)
 (defwarrant sum$)
 (defwarrant sum$+-ac)
 (defwarrant sum$+)
 (defwarrant always$)
 (defwarrant always$+)
 (defwarrant thereis$)
 (defwarrant thereis$+)
 (defwarrant collect$-ac)
 (defwarrant collect$)
 (defwarrant collect$+-ac)
 (defwarrant collect$+)
 (defwarrant revappend-true-list-fix)
 (defwarrant append$-ac)
 (defwarrant append$)
 (defwarrant append$+-ac)
 (defwarrant append$+)
 (defwarrant mempos)
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Memoization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+(and hons acl2-loop-only)
(progn

; We skip raw Lisp functions here; see *thread-unsafe-builtin-memoizations*.

  (memoize 'fchecksum-obj :stats nil :forget t)

; We no longer define pkg-names-memoize (other than to cause an error); see the
; comment there.
; (memoize 'pkg-names-memoize :stats nil :forget t)

; Comment on memoizing a worse-than function:

; In Version_7.0 and several preceding versions, we memoized a "worse-than"
; function as follows.

; (memoize 'worse-than-builtin-memoized :stats nil)

; We now use a clocked version of worse-than and avoid such memoization.  See
; worse-than-builtin-clocked for comments about potential memoization.
; To restore such memoization, search for every occurrence of
; "Comment on memoizing a worse-than function".

; Below, we discuss some earlier experiments on memoizing worse-than-builtin or
; the like, on two particular community books:

; - books/coi/dtrees/base.lisp does not benefit from memoization of worse-than
;   functions, and can be slowed down by it.

; - books/centaur/esim/stv/stv2c/stv2c.lisp requires memoization of
;   worse-than-builtin (or the like) to avoid stalling out in a proof.

; Below we look at some results for the first of these books, using Version_7.0
; except (where indicated below) a development version that was close to
; Version_7.0.

; Except where indicated otherwise, we memoized worse-than-builtin for
; experiments below as follows.

; (memoize 'worse-than-builtin
;          :stats nil
;          :condition ; Sol Swords suggestion
;          '(and (nvariablep term1)
;                (not (fquotep term1))
;                (nvariablep term2)
;                (not (fquotep term2))))

; Specifically, we ran the following commands in the above book's directory.

;   (ld "cert.acl2")
;   (rebuild "base.lisp" t)
;   (in-package "DTREE")
;   (ubt! 'aux-domain-of-dtreemapfix)
;   (skip-proofs (defthm lemma
;                  (implies (set::in a (aux-domain (dtreemapfix map)))
;                           (set::in a (aux-domain map)))))

; In some cases we also ran the following command or the following two commands
; after the commands above but before evaluating the defthm shown below:

;   (acl2::unmemoize 'acl2::worse-than-builtin)
;   #!acl2(memoize 'worse-than-builtin
;            :stats nil
;            :forget t
;            :condition ; Sol Swords suggestion
;            '(and (nvariablep term1)
;                 (not (fquotep term1))
;                  (nvariablep term2)
;                  (not (fquotep term2))))

; Then we submitted the following event.

;   (defthm lemma2-for-aux-domain-of-dtreemapfix
;     (implies (set::in a (aux-domain map))
;              (set::in a (aux-domain (dtreemapfix map)))))

; Times and memory use (last two reports from top) from some experiments are
; shown below.  The key is that all runs with worse-than unmemoized were
; significantly faster than all runs with worse-than memoized, regardless of
; various attempts to speed up that memoization.

; With GCL, out of the box:
; Time:  122.34 seconds (prove: 122.33, print: 0.01, other: 0.00)
; 11959 kaufmann  20   0 15.3g 2.8g  53m R  100  9.0   2:05.29 gcl-saved_acl2h
; 11959 kaufmann  20   0 15.3g 2.8g  53m S   21  9.0   2:05.92 gcl-saved_acl2h

; With GCL, after the above unmemoize form:
; Time:  78.72 seconds (prove: 78.72, print: 0.00, other: 0.00)
; 11934 kaufmann  20   0 13.2g 854m  53m R  100  2.7   1:18.68 gcl-saved_acl2h
; 11934 kaufmann  20   0 13.2g 854m  53m S   98  2.7   1:21.64 gcl-saved_acl2h

; With GCL, after the above sequence of unmemoize and memoize:
; Time:  94.45 seconds (prove: 94.44, print: 0.01, other: 0.00)
; 11995 kaufmann  20   0 13.8g 727m  53m R  100  2.3   1:35.62 gcl-saved_acl2h
; 11995 kaufmann  20   0 13.8g 727m  53m S   62  2.3   1:37.47 gcl-saved_acl2h

; With CCL, out of the box:
; Time:  131.46 seconds (prove: 131.42, print: 0.04, other: 0.00)
; 12044 kaufmann  20   0  512g 1.8g  17m S  100  5.6   2:10.31 lx86cl64
; 12044 kaufmann  20   0  512g 1.8g  17m S   81  5.6   2:12.73 lx86cl64

; With CCL, after the above unmemoize form:
; Time:  89.83 seconds (prove: 89.82, print: 0.00, other: 0.00)
; 12068 kaufmann  20   0  512g 1.3g  17m S   99  4.2   1:29.91 lx86cl64
; 12068 kaufmann  20   0  512g 1.4g  17m S   40  4.4   1:31.12 lx86cl64

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  147.46 seconds (prove: 147.44, print: 0.02, other: 0.00)
; 12093 kaufmann  20   0  512g 804m  18m S  100  2.5   2:27.86 lx86cl64
; 12093 kaufmann  20   0  512g 1.0g  18m S   30  3.2   2:28.77 lx86cl64

; All of the above were run with EGC off (the default at the time).  Now we
; repeat some of the above tests, but after turning EGC on as follows.

; (acl2::value :q) (ccl::egc t) (acl2::lp)

; With CCL, out of the box:
; Time:  1439.72 seconds (prove: 1439.71, print: 0.01, other: 0.00)
; 12127 kaufmann  20   0  512g 3.0g  35m S  100  9.4  23:58.68 lx86cl64
; 12127 kaufmann  20   0  512g 3.0g  35m S   78  9.4  24:01.03 lx86cl64

; With CCL, after the above unmemoize form:
; Time:  87.27 seconds (prove: 87.26, print: 0.01, other: 0.00)
; 12362 kaufmann  20   0  512g 407m  35m S  100  1.3   1:25.72 lx86cl64
; 12362 kaufmann  20   0  512g 417m  35m S   93  1.3   1:28.51 lx86cl64

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  135.92 seconds (prove: 135.90, print: 0.02, other: 0.00)
; 12384 kaufmann  20   0  512g 705m  36m S    0  2.2   2:17.39 lx86cl64
; 12384 kaufmann  20   0  512g 705m  36m S    0  2.2   2:17.40 lx86cl64

; As just above, but after redefining waterfall1 in raw Lisp so that its
; body is (prog2$ (clear-memoize-table 'worse-than-builtin) <old-body>)
; Time:  134.38 seconds (prove: 134.37, print: 0.02, other: 0.00)
; 12631 kaufmann  20   0  512g 691m  36m S   99  2.1   2:14.64 lx86cl64
; 12631 kaufmann  20   0  512g 698m  36m S   38  2.2   2:15.79 lx86cl64

; All of the above used ACL2 Version_7.0.  The tests below were run with a
; development copy as of 1/21/2015 (a mere 9 days after the release of 7.0).
; We continue to turn EGC on at the start, as above.

; With CCL, after the above sequence of unmemoize and memoize:
; Time:  135.80 seconds (prove: 135.79, print: 0.01, other: 0.00)
; 13018 kaufmann  20   0  512g 664m  36m S   99  2.1   2:15.91 lx86cl64
; 13018 kaufmann  20   0  512g 671m  36m S   42  2.1   2:17.16 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, after the above sequence of
; unmemoize and memoize:
; Time:  136.47 seconds (prove: 136.45, print: 0.02, other: 0.00)
; 13049 kaufmann  20   0  512g  59m  36m S   99  0.2   2:14.93 lx86cl64
; 13049 kaufmann  20   0  512g  59m  36m S   96  0.2   2:17.81 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, after the above unmemoize
; form:
; Time:  86.33 seconds (prove: 86.33, print: 0.01, other: 0.00)
; 13178 kaufmann  20   0  512g  58m  35m S  100  0.2   1:27.18 lx86cl64
; 13178 kaufmann  20   0  512g  58m  35m S   17  0.2   1:27.70 lx86cl64

; With CCL executable built without start-sol-gc (now called
; set-gc-strategy-builtin-delay) and with EGC on, out of the box except for
; redefining waterfall1 in raw Lisp so that its body is (prog2$
; (clear-memoize-table 'worse-than-builtin) <old-body>); notice that :forget
; remains nil.
; Time:  182.61 seconds (prove: 182.58, print: 0.02, other: 0.00)
; 13135 kaufmann  20   0  512g 137m  17m S  100  0.4   3:02.78 lx86cl64
; 13135 kaufmann  20   0  512g 137m  17m S   37  0.4   3:03.90 lx86cl64

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deprecation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defdeprecate (old new version)

; Old is the first parameter so that meta-. can find its definition (based on
; defdeprecate).

  (declare (type string version)) ; e.g., "8.4"
  `(progn
     (defmacro ,old (&rest args)
       (prog2$
        (cw "~%**DEPRECATED** in ACL2 Version ~s0: ~x1.  Use ~x2 instead.~|"
            ,version ',old ',new)
        (cons ',new args)))
     (add-macro-alias ,old ,new)
     (value-triple ',old)))

(defdeprecate symbol-< symbol< "8.4")
(defdeprecate strict-symbol-<-sortedp strict-symbol<-sortedp "8.4")
(defdeprecate strict-merge-symbol-< strict-merge-symbol< "8.4")
(defdeprecate strict-merge-sort-symbol-< strict-merge-sort-symbol< "8.4")
(defdeprecate strict-merge-sort-symbol-<-cdrs strict-merge-sort-symbol<-cdrs "8.4")
(defdeprecate merge-symbol-< merge-symbol< "8.4")
(defdeprecate merge-sort-symbol-< merge-sort-symbol< "8.4")
(defdeprecate logical-defun get-defun-event "8.4")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; End
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory ground-zero

; We want to keep this near the end of *acl2-pass-2-files* in order for the
; ground-zero theory to be as expected; hence the assert$ below.

  #-acl2-loop-only ; *acl2-pass-2-files* is only defined in raw Lisp.
  (assert (equal (car (last *acl2-pass-2-files*))
                  "boot-strap-pass-2-b.lisp"))
  (current-theory :here))

(deflabel

; WARNING: Put this at the end of the last file in
; *acl2-pass-2-files*.

  end-of-pass-2)
