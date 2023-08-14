; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "remove-runes-val")
(include-book "permute-randomly")
(include-book "augmented-useless-runes")

(program)
(set-state-ok t)

(defun delete-fake-runes (runes)

; This is similar to drop-fake-runes in kestrel/utilities/runes, but avoid name
; conflictt of *fake-rule-classes* with the version in
; books/workshops/2017/coglio-kaufmann-smith/support/runes.lisp.

; This could be put into guard-verified :logic mode, but we keep it in :program
; mode to avoid polluting our testing environment.

  (declare (xargs :guard t))
  (if (atom runes)
      nil
    (let ((rune (first runes)))
      (if (and (consp rune)
               (assoc-eq (first rune) *fake-rune-alist*))
          (delete-fake-runes (rest runes))
        (cons rune (delete-fake-runes (rest runes)))))))

(defun remove-rune-checkpoints-2 (term pspv arunes augmented-useless-runes val
                                       hints time-limit ens wrld ctx state acc)

; See remove-rune-checkpoints-1.  Here we accumulate onto acc suitable
; association to values of each rune from the given augmented runes, arunes,

  (cond
   ((null arunes) (value acc))
   (t (er-let* ((tmp (remove-runes-val
                      (remove1-equal (car arunes) augmented-useless-runes)
                      term pspv hints time-limit ens wrld ctx state)))
        (remove-rune-checkpoints-2 term pspv (cdr arunes)
                                   augmented-useless-runes
                                   val hints time-limit ens wrld ctx state
                                   (cons (cons (cdar arunes)

;;; !! Probably need to update comment:
; Note that we are removing ALL BUT the first rune in arunes, rather than
; removing that rune.  If the proof still goes through, then we know that
; removing that rune (in addition to removing those others) causes the proof to
; fail, and we already know what the checkpoints are, as stored in val from
; when we removed all those runes (i.e., those in arunes and those in
; arunes-done).

                                               (if (equal tmp
                                                          *remove-rune-val*)
                                                   val
                                                 *remove-rune-val*))
                                         acc))))))

(defun my-union-augmented-theories (lst1 lst2 ans)

; This is closely based on ACL2 source function union-augmented-theories-fn1,
; but unlike that function, this one returns an augmented runic theory rather
; than a runic theory.

  (cond ((null lst1) (revappend ans lst2))
        ((null lst2) (revappend ans lst1))
        ((int= (car (car lst1)) (car (car lst2)))
         (my-union-augmented-theories (cdr lst1) (cdr lst2)
                                      (cons (car lst1) ans)))
        ((> (car (car lst1)) (car (car lst2)))
         (my-union-augmented-theories (cdr lst1) lst2
                                      (cons (car lst1) ans)))
        (t (my-union-augmented-theories lst1 (cdr lst2)
                                        (cons (car lst2) ans)))))

(defun mark-removable-runes (augmented-runes)

; Accumulate onto acc the pairs mapping the rune of of each given augumented
; rune to the :REMOVE value.

  (cond ((endp augmented-runes) nil)
        (t (cons (cons (cdar augmented-runes)
                       *remove-rune-val*)
                 (mark-removable-runes (cdr augmented-runes))))))

(defun remove-rune-checkpoints-1 (term pspv runes
                                       augmented-useless-runes
                                       hints time-limit ens wrld
                                       ctx state seen acc)

; Augmented-useless-runes is an augmented theory, thus sorted by car in reverse
; numeric order.  It contains all runes in wrld, initially excepting those
; reported as used in the successful proof as well as all equivalence and
; congruence runes (since those aren't fully tracked).

; We cycle through runes, looking for one that makes the proof fail with at
; least one checkpoint when removed, accumulating into seen those runes already
; thus handled.

; But suppose runes is initially (A B ... Q R S ... Z) and we remove each rune
; in (A B ... R), where the proof succeeds until we finally remove R.  Assume
; also that we get checkpoints c0 (possibly: :FAIL) from removing (A ... R).
; We call remove-rune-checkpoints-2 for each augmented rune r0 in (A ... Q),
; such that we remove all runes (A ... R) *except* r0.  If that succeeds, then
; we associate r0 with c0 for each such augmented rune r0 and also for R, since
; we know that relative to removing all augmented runes in (A ... R) except r0,
; then additionally removing r0 causes the proof to fail with those
; checkpoints.  Otherwise we associate r0 with keyword :REMOVE (but that won't
; be the case for R).  We accumulate all such r0, except for R, into seen.

; If we never get a proof failure after processing every rune in runes, then we
; return entries showing that each rune in seen as well as the final rune may
; be removed.

; Otherwise now we have to start another "round", to deal with (S ... Z), if
; there are any such runes remaining.  We continue as before, but first we add
; augmented runes for (A ... Q) to augmented-useless-runes.

; The order of the alist returned is such that its runes (cars) are reversed
; from the order of the runes input, accumulated to the front of acc.

; I've considered saving information saying which runes from the original set
; were removed in addition to the one associated with the checkpoint.  But I
; don't think the ML folks will have a use for that info.

  (cond
   ((endp runes)

; If seen is non-nil, then we have run out of runes before finding a failure
; (in the current round).  The runes in seen are thus all removable, and need
; to be marked as such.  Note that the order in seen is the reverse of the
; order given by the random$ call in remove-rune-checkpoints, so arrange for
; mark-removable-runes to keep the order of seen so that we can simply
; accumulate into acc, to support the property that remove-rune-checkpoints-1
; revrses the order of the given runes.

    (value (append (mark-removable-runes seen) acc)))
   (t (let* ((rune (car runes))
             (augmented-rune (cons (runep rune wrld) rune))
             (new-augmented-useless-runes
              (my-union-augmented-theories (list augmented-rune)
                                           augmented-useless-runes
                                           nil)))
        (er-let* ((val

; Remove all runes up to and including the current rune, seeking a failure.

                   (remove-runes-val new-augmented-useless-runes term pspv
                                     hints time-limit ens wrld ctx state)))
          (cond
           ((equal val *remove-rune-val*)

; Removing the current rune didn't cause a failure.  Recur with it added to
; seen.

            (remove-rune-checkpoints-1 term pspv (cdr runes)
                                       new-augmented-useless-runes hints
                                       time-limit ens wrld ctx state
                                       (cons augmented-rune seen)
                                       acc))
           (t (er-let* ((acc (remove-rune-checkpoints-2
                              term pspv

; We do not include rune into seen, as it is accumulated into acc further
; below.  We want to continue accumulating into acc in reverse of the original
; order of runes (after the random$ call in remove-rune-checkpoints), so we
; reverse seen to get back to the original order.

; A possible future enhancement would be to add an argument that appends all
; these values of seen including previous recursive calls of
; remove-rune-checkpoints-1, so that when we report that removing a rune causes
; a proof to fail, we can see which other runes have been removed with it.  In
; the meantime, one can use raw Lisp -- say, with (format t "~%Rune: ~s~%Seen:
; ~s~%" rune seen) -- to print all these "seen values" and append them all
; together from under a given event's proof attempt that are printed above the
; desired "Rune:" thus shown as removed.

                              (reverse seen)
                              new-augmented-useless-runes val hints time-limit
                              ens wrld ctx state acc)))
                (remove-rune-checkpoints-1
                 term pspv (cdr runes) augmented-useless-runes hints time-limit
                 ens wrld ctx state nil
                 (cons (cons rune val) acc))))))))))

(defun adjust-hints-for-revert (ttree hints)

; Hints is a translated hints list.  We find the "Goal" hint-settings and add
; :induct t if the ttree indicates that we aborted to prove the original goal
; by induction and :induct is not already present in those hint-settings.  A
; comment in README describes a test that failed without this addition.

  (cond ((not (tag-tree-occur 'abort-cause 'revert ttree))
         hints)
        (t (let ((translated-hint (assoc-equal *initial-clause-id* hints)))

; Translated-hint might be nil, but that's OK.

             (cond ((assoc-eq :induct (cdr translated-hint))
                    hints)
                   (t
                    (put-assoc-equal *initial-clause-id*
                                     (acons :induct *t* (cdr translated-hint))
                                     hints)))))))

(defun remove-rune-checkpoints (term pspv ttree hints time-limit ens wrld ctx
                                     state)

; We return an error-triple whose value component (in the non-error case)
; associates each rune in runes, in the order obtained after permuting with
; permute-randomly, with a suitable value indicating whether it can be removed
; and, if not, checkpoints (if any, else :fail) produced by failure.

; The order doesn't matter except for debugging.  But it's useful for
; debugging, where we can remove runes manually to check results.

; Note that hints are translated.

  (let ((runes (all-runes-in-ttree ttree nil))
        (hints (adjust-hints-for-revert ttree hints)))
    (cond
     ((or (null time-limit)
          (null runes)
          (ld-skip-proofsp state))
      (value nil))
     (t
      (mv-let (runes state)
        (permute-randomly (delete-fake-runes runes)
                          state)
        (mv-let (erp val state)
          (with-output!
            :off :all
            :gag-mode nil
            (state-global-let*
             ((abort-soft nil)) ; interrupts abort immediately to the top level
             (remove-rune-checkpoints-1 term pspv runes
                                        (augmented-useless-runes runes wrld)
                                        hints time-limit ens wrld ctx state nil
                                        nil)))
          (value (and (null erp)

; We reverse the order returned by remove-rune-checkpoints-1 in order to get
; back to the original order.  At one point we checked the following during
; testing: (equal (strip-cars (reverse val)) runes).

                      (reverse val)))))))))
