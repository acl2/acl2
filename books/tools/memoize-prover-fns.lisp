; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann, May, 2016
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to David Rager for suggesting memoization of a number of prover
; functions, including var-fn-count-1, ffnnamep-lst, ffnnamesp-lst,
; all-fnnames1, all-vars1-lst, term-listp, sublis-var1-lst, sublis-var1.  He
; mentioned turning a 4200 second proof into a 49 second proof in this way,
; though he acknowledged that his proof referenced a lot of terms that might be
; honsed.

; I don't claim that memoizing any particular set of prover functions is
; necessarily a good idea.  But it appears that this is the case in some
; circumstances, such as the one for David mentioned above.  Users can
; experiment by modifying state global 'memoized-prover-fns.  David also noted
; the following.

; (memoize 'ffnnamep-lst) ; helpful but would finish reasonably without memoizing
; memoizing ffnnamesp-lst isn't helpful
; (memoize 'all-fnnames1) ; needed
; (memoize 'all-vars1-lst) ; needed
; (memoize 'term-listp) ; needed
; memoizing sublis-var1-lst isn't helpful
; (memoize 'sublis-var1) ; needed

; Thanks too to David for suggesting removing accumulated memoization
; information after each proof.  Here, we do that by using the
; finalize-event-user mechanism to clear memoize-tables.

; An existing example of memoizing a prover function is in
; books/projects/stateman/stateman22.lisp, where we find this form:

; (memoize 'sublis-var1 :condition '(and (null alist) (consp form) (eq (car form) 'HIDE)))

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun memoize-lst-fn (lst options acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc))))
  (cond ((endp lst) (reverse acc))
        (t (memoize-lst-fn (cdr lst)
                           options
                           (cons `(memoize ',(car lst) ,@options)
                                 acc)))))

(defmacro memoize-lst (lst &rest options &key (verbose 'nil))

; Lst is evaluated but options is not.  Note that verbose may be part of
; options, but we want its value to be nil by default so we need to pass a
; suitably updated options to memoize-lst-fn.

  (declare (ignorable verbose))
  `(make-event
    (cons 'progn (memoize-lst-fn ,lst
                                 ',(list* :verbose verbose
                                          (remove-keyword :verbose
                                                          options))
                                 nil))))

(defun unmemoize-lst-fn (lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc))))
  (cond ((endp lst) (reverse acc))
        (t (unmemoize-lst-fn (cdr lst)
                             (cons `(unmemoize ',(car lst))
                                   acc)))))

(defmacro unmemoize-lst (lst)

; Lst is evaluated but options is not.  Note that verbose may be part of
; options, but we want its value to be nil by default so we need to pass a
; suitably updated options to memoize-lst-fn.

  `(make-event
    (list 'with-output
          :off :all
          (cons 'progn (unmemoize-lst-fn ,lst nil)))))

(defun clear-memoize-table-lst (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (prog2$ (clear-memoize-table (car lst))
                   (clear-memoize-table-lst (cdr lst))))))

(make-event
 (pprogn (f-put-global 'memoized-prover-fns

; NOTE!  The list below is just a suggestion, with very little evidence that
; it's a good suggestion!  Please feel free to experiment by modifying the
; value of state global 'memoized-prover-fns.

; The following four may be worth considering, but in little experiments based
; on CCL using
; books/workshops/2004/legato/support/proof-by-generalization-mult.lisp they
; didn't seem useful, for the reasons indicated.

; VAR-FN-COUNT-1 ; very expensive
; REWRITE-RECOGNIZER ; few hits
; SUBLIS-VAR! ; few hits
; SEARCH-TYPE-ALIST-WITH-REST ; few hits

; These also might seem to be good candidates, but they're not, for the reasons
; given below.

; FGETPROP ; macro
; EV-SYNP ; takes state

                        '(macroexpand1-cmp
                          translate11-lst
                          translate11-call
                          translate11
                          all-fnnames1
                          all-vars1
                          all-vars1-lst
                          ffnnamep-mod-mbe-lst
                          remove-guard-holders
                          remove-guard-holders-weak
                          remove-guard-holders1
                          remove-guard-holders1-lst
                          normalize
                          normalize-lst)
                        state)
          (value '(value-triple :MEMOIZED-PROVER-FNS-ASSIGNED)))
 :check-expansion t)

; I tried this by itself with CCL in the Legato book above; 10M calls produced
; 100% hits, but it slowed things down:
; (memoize 'fn-count-evg-rec :condition '(and (zerop acc) (zerop calls)))

; Same as above -- no better:
; (defn fn-count-evg-rec-condition (evg acc calls)
;   (declare (ignore evg)
;            (type (unsigned-byte 29) acc calls))
;   (and (eql acc 0) (eql calls 0)))
; (memoize 'fn-count-evg-rec :condition-fn 'fn-count-evg-rec-condition)

(memoize-lst (f-get-global 'memoized-prover-fns state))

(defun finalize-event-user-memoize (ctx body state)
  (declare (xargs :stobjs state)
           (ignore ctx body))
  (cond ((or

; We got an error from an LD of the Legato book mentioned above when we didn't
; include the following condition.  It's not surprising that clearing
; memoization tables in the middle of including arbitrary books could be
; problematic, though ideally I'll return to this issue some day and eliminate
; that problem.  We could actually make this check more generous by checking
; that (f-get-global 'ld-skip-proofsp state) is non-nil, but perhaps we'd want
; some of the memoizations to take place even when skipping proofs at the top
; level.

          (global-val 'include-book-path (w state))

; The following naturally belongs in the guard, but the guard needs to be T in
; order for the defattach below to succeed.

          (not (and (f-boundp-global 'memoized-prover-fns state)
                    (true-listp (f-get-global 'memoized-prover-fns
                                              state)))))
         state)
        (t (progn$
            ;; (cw "@@@ Clearing @@@~%") ; debug
            (clear-memoize-table-lst (f-get-global 'memoized-prover-fns
                                                   state))
            state))))

(defattach (finalize-event-user finalize-event-user-memoize)
  :system-ok t)

(defxdoc memoized-prover-fns
  :parents (memoize)
  :short "Memoize some theorem prover functions"
  :long "<p>In the @(see community-books), the book
 @('tools/memoize-prover-fns.lisp') arranges to @(see memoize) some functions
 in the theorem prover.  Including this book MAY, in some cases, improve
 performance; perhaps more likely, including this book may degrade performance!
 So if you decide to include this book, it would serve you well to experiment
 by changing the list of prover functions to memoize.  To do this you can
 proceed as follows.</p>

 @({
 (progn
   (unmemoize-lst (f-get-global 'memoized-prover-fns state))
   (make-event
    (pprogn (f-put-global 'memoized-prover-fns '(... <your_list> ...) state)
            (value '(value-triple nil))))
   (memoize-lst (f-get-global 'memoized-prover-fns state)))
 })

 <p>Of course, you can run experiments that compare times for your proofs with
 different prover functions memoized (or, no prover functions memoized).  In
 addition, as usual with memoization, you can evaluate @('(memsum)') after
 trying some proofs to see if the functions you have memoized result in good
 ratios of hits to calls.</p>

 <p>Note that this book automatically provides an attachment to @(tsee
 finalize-event-user).  So it might not work well with other books that provide
 such an attachment.  For this book, the attachment clears the memoization
 tables after each book not under @(tsee include-book).  (That restriction
 could easily be lifted, but perhaps it's useful for performance.  And perhaps
 not &mdash; feel free to experiment!)</p>

 <p>If you find a good set of prover functions to memoize, please consider
 modifying the @(tsee f-put-global) call in the aforementioned book,
 @('tools/memoize-prover-fns.lisp'), for your own set of prover
 functions.</p>")

(defpointer memoize-prover-fns memoized-prover-fns)
