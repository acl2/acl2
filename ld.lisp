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

; This file, ld.lisp, provides the definition of the ACL2 macro ld,
; which implements both the ACL2 read-eval-print loop and the ACL2
; file loader.

(defrec ld-prompt-memo

; There is no need to memoize the binding of #\r for the purpose of checking if
; the prompt is current, since it never changes during a given session.  Of
; course, #\r is bound in the alist.

  ((current-package ld-level . ld-skip-proofsp)
   mode
   not-gc-off
   #+:non-standard-analysis
   script-mode
   .
   alist)
  t)

(defun default-print-prompt (channel state)

; This is the default function for printing the ACL2 ld loop prompt.  A typical
; prompt looks like: ACL2 !>, where the number of >'s indicates the ld-level.
; The prompt is printed by (fmt "~@0~sr ~@1~*2" a channel state nil), where a
; is an alist computed from current-package, ld-level, default-defun-mode,
; guard-checking-on, and ld-skip-proofsp, and #\r is bound to "" except for the
; #+:non-standard-analysis version, where it is bound to "(r)".  To keep from
; consing up this alist every time, we memoize it, storing in 'prompt-memo the
; tuple (pkg level skipp defun-mode+ gc-on a), where defun-mode+ is the
; default-defun-mode except in raw-mode, where defun-mode+ is nil.  Thus, if
; the current settings are as in the memo, we use the a in the memo.
; Otherwise, we compute and store a new memo.

; Warning:  If you change the default prompt format, be sure to change it
; in eval-event-lst, where we print it by hand.

  (let ((prompt-memo (and (f-boundp-global 'prompt-memo state)
                          (f-get-global 'prompt-memo state))))
    (cond
     ((and prompt-memo
           (equal (access ld-prompt-memo prompt-memo :current-package)
                  (f-get-global 'current-package state))
           (equal (access ld-prompt-memo prompt-memo :ld-level)
                  (f-get-global 'ld-level state))
           (eq (access ld-prompt-memo prompt-memo :ld-skip-proofsp)
               (f-get-global 'ld-skip-proofsp state))
           (eq (access ld-prompt-memo prompt-memo :mode)
               (and (not (raw-mode-p state))
                    (default-defun-mode (w state))))

; In the following, we could use iff instead of eq, because the dependence of
; defun-mode-prompt on (f-get-global 'guard-checking-on state) is restricted to
; whether or not the latter is nil/:none.  But it's cheap to update the
; prompt-memo so we keep the more restrictive eq test for robustness, in case
; the code for defun-mode-prompt changes.

           (eq (access ld-prompt-memo prompt-memo :not-gc-off)
               (f-get-global 'guard-checking-on state))
           #+:non-standard-analysis
           (eq (access ld-prompt-memo prompt-memo :script-mode)
               (f-get-global 'script-mode state)))
      (fmt1 "~@0~sr ~@1~*2"
            (access ld-prompt-memo prompt-memo :alist)
            0 channel state nil))
     (t
      (let ((alist
             (list (cons #\0 (f-get-global 'current-package state))
                   (cons #\1 (defun-mode-prompt-string state))
                   (cons #\2 (list "" ">" ">" ">"
                                   (make-list-ac (f-get-global 'ld-level state)
                                                 nil nil)))
                   (cons #\r
                         #+:non-standard-analysis
                         (if (f-get-global 'script-mode state)
                             ""
                           "(r)")
                         #-:non-standard-analysis ""))))
        (pprogn
         (f-put-global
          'prompt-memo
          (make ld-prompt-memo
                :current-package (f-get-global 'current-package state)
                :ld-level (f-get-global 'ld-level state)
                :ld-skip-proofsp (f-get-global 'ld-skip-proofsp state)
                :mode (and (not (raw-mode-p state))
                           (default-defun-mode (w state)))
                :not-gc-off (not (gc-off state))
                #+:non-standard-analysis
                :script-mode
                #+:non-standard-analysis
                (f-get-global 'script-mode state)
                :alist alist)
          state)
         (fmt1 "~@0~sr ~@1~*2" alist 0 channel state nil)))))))

(defun print-prompt (prompt output-channel state)
  (with-output-forced
   output-channel
   (col state)
   (let ((prompt-fn (cond ((null prompt) nil)
                          ((eq prompt t)
                           (f-get-global 'prompt-function state))
                          (t prompt))))
     (cond
      ((null prompt-fn) (mv 0 state))
      ((eq prompt-fn 'default-print-prompt)
       (default-print-prompt output-channel state))
      (t (mv-let (erp trans-ans state)

; We could call trans-eval-no-warning here instead, to avoid horrible warnings
; appearing as the prompt is printed.  But if that printing modifies a user
; stobj, then probably it would be most appropriate for the superior call of ld
; to specify :ld-user-stobjs-modified-warning nil.

           (trans-eval-default-warning (list prompt-fn
                                             (list 'quote output-channel)
                                             'state)
                                       'print-prompt state t)

; If erp is non-nil, trans-ans is of the form (stobjs-out . valx).  We
; strongly expect that stobjs-out is (nil state).  (That is true if
; prompt is in fact ld-prompt.)  That being the case, we expect
; valx to be (col replaced-state).

           (cond
            ((or erp
                 (not (and (equal (car trans-ans) '(nil state))
                           (integerp (car (cdr trans-ans))))))
             (fmt1 "~%~%Bad Prompt~%See :DOC ld-prompt>"
                   nil 0 output-channel state nil))
            (t (mv (car (cdr trans-ans)) state)))))))))

(defun initialize-timers (state)
  (pprogn
   (set-timer 'prove-time '(0) state)
   (set-timer 'print-time '(0) state)
   (set-timer 'proof-tree-time '(0) state)
   (set-timer 'other-time '(0) state)))

(defun maybe-add-command-landmark (old-wrld old-default-defun-mode form
                                            trans-ans state)

; Old-wrld is the world before the trans-evaluation of form.  That
; trans-evaluation returned trans-ans, which is thus of the form (stobjs-out
; . valx).  If valx contains a state (then it must in fact contain the state
; state), and the current world of that state is different from old-wrld and
; does not end with a command landmark, we add a command landmark for form.

; We pass in old-default-defun-mode as the default-defun-mode of old-wrld.
; This way, we can compute that value at a time that old-wrld is still
; installed, so that the corresponding getprop will be fast.

  (let ((wrld (w state)))
    (cond ((and (member-eq 'state (car trans-ans))
                (not (and (eq (caar wrld) 'command-landmark)
                          (eq (cadar wrld) 'global-value)))
                (not (equal old-wrld wrld)))
           (er-progn
            (get-and-chk-last-make-event-expansion

; For purposes of tracking make-event, we allow time$ only at the top level.
; If there is user demand, we could consider allowing it in arbitrary positions
; of embedded event forms, though in that case we should be careful to check
; that nested calls work well.  Note that we look for time$, not for
; return-last, because we are looking at a user-supplied form, not its
; macroexpansion.

             (cond ((consp form)
                    (case (car form)
                      (time$ (cadr form))
                      (otherwise form)))
                   (t form))
             wrld 'top-level state
             (primitive-event-macros))
            (pprogn
             (cond ((raw-mode-p state)

; If we are in raw mode, then it is scary to imagine that we have changed the
; logical world.

                    (warning$ 'top-level "Raw"
                              "The ACL2 world is being modified while in raw ~
                               mode.  See :DOC set-raw-mode.  Further ~
                               computation in this ACL2 session may have some ~
                               surprising results."))
                   (t state))
             (set-w 'extension
                    (add-command-landmark
                     old-default-defun-mode
                     form
                     (f-get-global 'connected-book-directory state)
                     (f-get-global 'last-make-event-expansion state)
                     wrld)
                    state)
             (value nil))))
          (t (value nil)))))

(defun replace-last-cdr (x val)
  (cond ((atom x) val)
        ((atom (cdr x)) (cons (car x) val))
        (t (cons (car x) (replace-last-cdr (cdr x) val)))))

(defun ld-standard-oi-missing (val file-name ld-missing-input-ok ctx state)
  (cond ((eq ld-missing-input-ok t)
         (value nil))
        (t (let ((msg (msg "~@0  It is likely that the file you requested, ~
                            ~x1, does not exist."
                           (msg *ld-special-error*
                                'standard-oi val)
                           file-name)))
             (cond (ld-missing-input-ok ; not t, so :warn
                    (pprogn (warning$ ctx "ld-missing-input" "~@0" msg)
                            (value nil)))
                   (t (er soft ctx "~@0" msg)))))))

(defun chk-acceptable-ld-fn1-pair (pair ld-missing-input-ok ctx state
                                        co-string co-channel)

; We check that pair, which is of the form (var . val) where var is a symbolp,
; specifies a legitimate "binding" for the LD special var.  This means that we
; check that var is one of the state globals that LD appears to bind (i.e.,
; push and pop in an unwind-protected way) and that val is a reasonable value
; of that global.  For example, 'standard-oi is an LD special but must be bound
; to a true-list of objects or an open object input channel.

; Co-string and co-channel are here to provide a very subtle feature of LD.  If
; the same string is specified for both standard-co and proofs-co then we open
; one channel and use it in both places.  Our caller, chk-acceptable-ld-fn1, is
; responsible for maintaining these two accumulators as we map down the list of
; pairs.  It puts into co-string and co-channel the string and returned channel
; for the first of standard-co or proofs-co encountered.

  (let* ((var (car pair))
         (val (cdr pair))
         (file-name (and (member-eq var
                                    '(standard-oi standard-co proofs-co))
                         (stringp val) ; else not file-name is not used
                         (extend-pathname
                          (f-get-global 'connected-book-directory state)
                          val
                          state))))

; The first three LD specials, namely the three channels, are special because
; we may have to open a channel and create a new pair.  Once we get past those
; three, we can just use the standard checkers and return the existing pair.

    (case var
          (standard-oi
           (cond
            ((and (symbolp val)
                  (open-input-channel-p val :object state))
             (value pair))
            ((true-listp val)
             (value pair))
            ((stringp val)
             (mv-let (ch state)
               (open-input-channel file-name :object state)
               (cond (ch (value (cons 'standard-oi ch)))
                     (t (ld-standard-oi-missing
                         val file-name ld-missing-input-ok ctx
                         state)))))
            ((consp val)
             (let ((last-cons (last val)))
               (cond
                ((and (symbolp (cdr last-cons))
                      (open-input-channel-p (cdr last-cons) :object state))
                 (value pair))
                ((stringp (cdr last-cons))
                 (let ((file-name (extend-pathname
                                   (f-get-global 'connected-book-directory
                                                 state)
                                   (cdr last-cons)
                                   state)))
                   (mv-let (ch state)
                           (open-input-channel file-name :object state)
                           (cond
                            (ch (value (cons 'standard-oi
                                             (replace-last-cdr val ch))))
                            (t (ld-standard-oi-missing
                                val file-name ld-missing-input-ok ctx
                                state))))))
                (t (er soft ctx *ld-special-error* 'standard-oi val)))))
            (t (er soft ctx *ld-special-error* 'standard-oi val))))
          (standard-co
           (cond
            ((and (symbolp val)
                  (open-output-channel-p val :character state))
             (value pair))
            ((equal val co-string)
             (value (cons 'standard-co co-channel)))
            ((stringp val)
             (mv-let (ch state)
                     (open-output-channel file-name :character state)
                     (cond (ch (value (cons 'standard-co ch)))
                           (t (er soft ctx *ld-special-error* 'standard-co
                                  val)))))
            (t (er soft ctx *ld-special-error* 'standard-co val))))
          (proofs-co
           (cond
            ((and (symbolp val)
                  (open-output-channel-p val :character state))
             (value pair))
            ((stringp val)
             (cond
              ((equal file-name co-string)
               (value (cons 'proofs-co co-channel)))
              (t
               (mv-let (ch state)
                 (open-output-channel file-name :character state)
                 (cond
                  (ch (value (cons 'proofs-co ch)))
                  (t (er soft ctx *ld-special-error* 'proofs-co val)))))))
            (t (er soft ctx *ld-special-error* 'proofs-co val))))
          (current-package
           (er-progn (chk-current-package val ctx state)
                     (value pair)))
          (ld-skip-proofsp
           (er-progn (chk-ld-skip-proofsp val ctx state)
                     (value pair)))
          (ld-redefinition-action
           (er-progn (chk-ld-redefinition-action val ctx state)
                     (value pair)))
          (ld-prompt
           (er-progn (chk-ld-prompt val ctx state)
                     (value pair)))
          (ld-missing-input-ok
           (er-progn (chk-ld-missing-input-ok val ctx state)
                     (value pair)))
          (ld-pre-eval-filter
           (er-progn (chk-ld-pre-eval-filter val ctx state)
                     (value pair)))
          (ld-pre-eval-print
           (er-progn (chk-ld-pre-eval-print val ctx state)
                     (value pair)))
          (ld-post-eval-print
           (er-progn (chk-ld-post-eval-print val ctx state)
                     (value pair)))
          (ld-evisc-tuple
           (er-progn (chk-evisc-tuple val ctx state)
                     (value pair)))
          (ld-error-triples
           (er-progn (chk-ld-error-triples val ctx state)
                     (value pair)))
          (ld-error-action
           (er-progn (chk-ld-error-action val ctx state)
                     (value pair)))
          (ld-query-control-alist
           (er-progn (chk-ld-query-control-alist val ctx state)
                     (value pair)))
          (ld-verbose
           (er-progn (chk-ld-verbose val ctx state)
                     (value pair)))
          (ld-user-stobjs-modified-warning
           (er-progn (chk-ld-user-stobjs-modified-warning val ctx state)
                     (value pair)))
          (otherwise
           (er soft ctx
               "The variable ~x0 is not an authorized LD special and ~
                hence cannot be bound by LD."
               var)))))

(defun close-channels (channel-closing-alist state)

; It is necessary to close the channels that we open.  We must in fact
; record them somewhere in state so that if we abort LD with a hard error or
; user interrupt that throws us into the unwind-protect code of LP, they are
; still closed.  To enable such "remote closings" we invent the notion of a
; "channel closing alist" which is an alist that pairs opened channels to
; their "types", where a type is either 'oi (object input) or 'co (character
; output).  Given such an alist we close each channel in it, if the channel
; is in fact open.

  (cond
   ((null channel-closing-alist) state)
   (t (pprogn
       (cond
        ((eq (cdar channel-closing-alist) 'oi)
         (cond
          ((open-input-channel-p (caar channel-closing-alist) :object state)
           (close-input-channel (caar channel-closing-alist) state))
          (t state)))
        ((eq (cdar channel-closing-alist) 'co)
         (cond
          ((open-output-channel-p (caar channel-closing-alist)
                                  :character state)
           (close-output-channel (caar channel-closing-alist) state))
          (t state)))
        (t (let ((temp (er hard 'close-channels
                           "The channel ~x0 was tagged with an unimplemented ~
                            channel type, ~x1."
                           (caar channel-closing-alist)
                           (cdar channel-closing-alist))))
             (declare (ignore temp))
             state)))
       (close-channels (cdr channel-closing-alist) state)))))

(defun chk-acceptable-ld-fn1 (alist ld-missing-input-ok ctx state co-string
                                    co-channel new-alist channel-closing-alist)

; We copy alist (reversing it) onto new-alist, checking that each pair in it
; binds an LD special to a legitimate value.  We open the requested files as we
; go and replace the file names with the open channels.  We also accumulate
; into channel-closing-alist the pairs necessary to close (with close-channels)
; the channels we have opened.  We return a pair consisting of the new-alist
; and the final channel-closing-alist.  See chk-acceptable-ld-fn1-pair for an
; explanation of co-string and co-channel.

; Implementation Note: This odd structure has the single redeeming feature that
; if any given pair of alist causes an error, we have in our hands enough
; information to close any channels we might have opened thus far.  If we get
; all the way down alist without causing an error, the channel-closing-alist
; will be used in the acl2-unwind-protect cleanup form and enable us to "close
; on pop" -- which was its original purpose.  But an earlier coding of this
; function suffered from the problem that we could open several channels and
; then, right here, cause an error (e.g., the proposed 'current-package setting
; is bad).  If that happened, those open channels would never be closed.  It is
; still possible to "lose" an opened channel: abort this function after some
; files have been opened.

; This flaw cannot be fixed, at least with the current set of primitives.  To
; close a channel we must have the channel.  We don't have the channel until
; after we have opened it, i.e., the way we get our hands on a channel in ACL2
; is to open a file, but the way we close a channel is to call
; close-output-channel on the channel object (rather than the file).  Thus,
; there is no way we can unwind protect code that opens a channel so as to
; guarantee to close the channel because we can't get the object we are to
; "cleanup" (the channel) until after we have "modified" (opened) it.  So there
; is a window of vulnerability between the time we open the channel and the
; time we stash it away in some location known to our cleanup form.  During
; that window an abort can cause us to lose a channel in the sense that we do
; not close it.  Now we can make that window much smaller than it is now.  As
; things stand now we are vulnerable to aborts from the time we start
; processing alist here until we finish and enter the acl2-unwind-protect in
; ld-fn that "binds" the ld specials.  But all this vulnerability means is that
; lisp fails to close some opened channels during an abort.  If such a thing
; happens, the user could detect it with some poking around.  For example, he
; could just type

; (open-output-channel-p 'ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-i
;                        :character state)

; for a bunch of i starting at 0 and see if there are some he doesn't know
; about.  This is not a catastrophic error.  It is as though the abort placed
; in the open-output-channels field of the state an additional channel or two.
; The only way, as far as we can see, that this can be a problem is in the
; sense of resource exhaustion: operating systems (and thus lisps) generally
; allow a finite number of open channels.

; If we someday endeavor to plug this hole some additional care must be taken
; because the act of opening an ACL2 channel (in raw lisp) is non-atomic -- we
; have to open the stream, generate a channel symbol, and store some stuff on
; the property list of the symbol.  So an abort there can cause an
; irretrievable loss of an open channel unless the problem is addressed down
; there as well.

; Finally we would just like to note that soft errors are handled perfectly
; here in the sense that if some channels are opened and then we get a soft
; error, we close the channels.  And aborts are handled perfectly once we get
; outside of the window of vulnerability discussed.

  (cond
   ((null alist)
    (let ((new-alist
           (cond ((eq ld-missing-input-ok :missing)
                  (put-assoc-eq 'ld-verbose nil
                                (put-assoc-eq 'ld-prompt nil new-alist)))
                 (t new-alist))))
      (value (cons new-alist channel-closing-alist))))
   (t (mv-let
       (erp pair state)
       (chk-acceptable-ld-fn1-pair (car alist) ld-missing-input-ok ctx state
                                   co-string co-channel)
       (cond
        (erp (pprogn
              (close-channels channel-closing-alist state)
              (mv t nil state)))
        (t
         (mv-let
          (pair ld-missing-input-ok)
          (cond ((null pair)
                 (assert$ (eq  (caar alist) 'standard-oi)
                          (mv (cons 'standard-oi nil) :missing)))
                (t (mv pair ld-missing-input-ok)))
          (chk-acceptable-ld-fn1
           (cdr alist) ld-missing-input-ok ctx state
           (cond ((and (null co-string)
                       (or (eq (car pair) 'standard-co)
                           (eq (car pair) 'proofs-co))
                       (stringp (cdr (car alist))))
                  (extend-pathname
                   (f-get-global 'connected-book-directory state)
                   (cdr (car alist))
                   state))
                 (t co-string))
           (cond ((and (null co-channel)
                       (or (eq (car pair) 'standard-co)
                           (eq (car pair) 'proofs-co))
                       (stringp (cdr (car alist))))
                  (cdr pair))
                 (t co-channel))
           (cons pair new-alist)
           (cond
            ((eq (car pair) 'standard-oi)
             (cond ((stringp (cdr (car alist)))
                    (cons (cons (cdr pair) 'oi) channel-closing-alist))
                   ((and (consp (cdr (car alist)))
                         (stringp (cdr (last (cdr (car alist))))))
                    (cons (cons (cdr (last (cdr pair))) 'oi)
                          channel-closing-alist))
                   (t channel-closing-alist)))
            ((and (or (eq (car pair) 'standard-co)
                      (eq (car pair) 'proofs-co))
                  (stringp (cdr (car alist))))
             (cons (cons (cdr pair) 'co) channel-closing-alist))
            (t channel-closing-alist))))))))))

(defun chk-acceptable-ld-fn (alist state)

; Alist is an alist that pairs LD specials with proposed values.  We check
; that those values are legitimate and that only authorized LD specials are
; bound.  If strings are supplied for the specials standard-oi, standard-co,
; and proofs-co, we open corresponding channels and put those channels in
; for the values in the alist.  We return a pair consisting of the modified
; alist and a channel closing alist that pairs opened channels with the
; type information it takes to close them.

  (let ((ctx 'ld))
    (er-progn
     (cond
      ((or (null (f-boundp-global 'current-acl2-world state))
           (null (w state)))
       (er soft ctx
           "The theorem prover's database has not yet been initialized.  To ~
            initialize ACL2 to its full theory, which currently takes about 3 ~
            minutes on a Sparc 2 (Dec. 1992), invoke (initialize-acl2) from ~
            Common Lisp."))
      (t (value nil)))
     (cond ((symbol-alistp alist) (value nil))
           (t (er soft ctx
                  "The argument to ld-fn must be a symbol-alistp and ~x0 is ~
                   not."
                  alist)))
     (cond ((assoc-eq 'standard-oi alist) (value nil))
           (t (er soft ctx
                  "The alist argument to ld-fn must specify a value ~
                   for 'standard-oi and ~x0 does not."
                  alist)))
     (cond ((not (duplicate-keysp-eq alist)) (value nil))
           (t (er soft ctx
                  "The alist argument to ld-fn must contain no duplications ~
                   among the LD specials to be bound.  Your alist contains ~
                   duplicate values for ~&0."
                  (duplicates (strip-cars alist)))))
     (chk-acceptable-ld-fn1 alist
                            (cdr (assoc-eq 'ld-missing-input-ok alist))
                            ctx state nil nil nil nil))))

(defun f-put-ld-specials (alist state)

; Alist is an alist that pairs LD specials with their new values.  We
; f-put-global each special.  Because f-put-global requires an explicitly
; quoted variable, we case split on the authorized LD-specials.  This is
; easier and safer than making translate give us special treatment.  To add
; a new LD-special you must change this function, as well as
; f-get-ld-specials and the checker chk-acceptable-ld-fn1-pair.

; Warning: Somebody else better have checked that the values assigned are
; legitimate.  For example, we here set 'current-package to whatever we are
; told to set it.  This is not a function the user should call!

  (cond
   ((null alist) state)
   (t (pprogn
       (case
        (caar alist)
        (standard-oi
         (f-put-global 'standard-oi (cdar alist) state))
        (standard-co
         (f-put-global 'standard-co (cdar alist) state))
        (proofs-co
         (f-put-global 'proofs-co (cdar alist) state))
        (current-package
         (f-put-global 'current-package (cdar alist) state))
        (ld-skip-proofsp
         (f-put-global 'ld-skip-proofsp (cdar alist) state))
        (ld-redefinition-action
         (f-put-global 'ld-redefinition-action (cdar alist) state))
        (ld-prompt
         (f-put-global 'ld-prompt (cdar alist) state))
        (ld-missing-input-ok
         (f-put-global 'ld-missing-input-ok (cdar alist) state))
        (ld-pre-eval-filter
         (if (and (f-boundp-global 'ld-pre-eval-filter state); for boot-strap
                  (eq (f-get-global 'ld-pre-eval-filter state) :illegal-state))
             state ; See the Essay on Illegal-states.
           (f-put-global 'ld-pre-eval-filter (cdar alist) state)))
        (ld-pre-eval-print
         (f-put-global 'ld-pre-eval-print (cdar alist) state))
        (ld-post-eval-print
         (f-put-global 'ld-post-eval-print (cdar alist) state))
        (ld-evisc-tuple
         (f-put-global 'ld-evisc-tuple (cdar alist) state))
        (ld-error-triples
         (f-put-global 'ld-error-triples (cdar alist) state))
        (ld-error-action
         (f-put-global 'ld-error-action (cdar alist) state))
        (ld-query-control-alist
         (f-put-global 'ld-query-control-alist (cdar alist) state))
        (ld-verbose
         (f-put-global 'ld-verbose (cdar alist) state))
        (ld-user-stobjs-modified-warning
         (if (eq (cdar alist) :same)
             state
           (f-put-global 'ld-user-stobjs-modified-warning (cdar alist) state)))
        (otherwise
         (let ((x (er hard 'f-put-ld-specials
                      "Someone is using ~x0 as an unauthorized LD-special."
                      (caar alist))))
           (declare (ignore x))
           state)))
       (f-put-ld-specials (cdr alist) state)))))

(defun f-get-ld-specials (state)

; Make an alist, suitable for giving to f-put-ld-specials, that records the
; current values of all LD-specials.  To add a new LD-special you must
; change this function, f-put-ld-specials, and the checker
; chk-acceptable-ld-fn1-pair.

  (list (cons 'standard-oi
              (f-get-global 'standard-oi state))
        (cons 'standard-co
              (f-get-global 'standard-co state))
        (cons 'proofs-co
              (f-get-global 'proofs-co state))
        (cons 'current-package
              (f-get-global 'current-package state))
        (cons 'ld-skip-proofsp
              (f-get-global 'ld-skip-proofsp state))
        (cons 'ld-redefinition-action
              (f-get-global 'ld-redefinition-action state))
        (cons 'ld-prompt
              (f-get-global 'ld-prompt state))
        (cons 'ld-missing-input-ok
              (f-get-global 'ld-missing-input-ok state))
        (cons 'ld-pre-eval-filter
              (f-get-global 'ld-pre-eval-filter state))
        (cons 'ld-pre-eval-print
              (f-get-global 'ld-pre-eval-print state))
        (cons 'ld-post-eval-print
              (f-get-global 'ld-post-eval-print state))
        (cons 'ld-evisc-tuple
              (f-get-global 'ld-evisc-tuple state))
        (cons 'ld-error-triples
              (f-get-global 'ld-error-triples state))
        (cons 'ld-error-action
              (f-get-global 'ld-error-action state))
        (cons 'ld-query-control-alist
              (f-get-global 'ld-query-control-alist state))
        (cons 'ld-verbose
              (f-get-global 'ld-verbose state))
        (cons 'ld-user-stobjs-modified-warning
              (f-get-global 'ld-user-stobjs-modified-warning state))))

(defun ld-read-keyword-command1 (n state)
  (cond
   ((= n 0) (value nil))
   (t (mv-let (eofp obj state)
              (read-standard-oi state)
              (cond
               (eofp (er soft 'ld-read-keyword-command
                         "Unfinished keyword command at eof on (standard-oi ~
                          state)."))
               (t
                (er-let*
                 ((rst (ld-read-keyword-command1 (1- n) state)))

; Note: We take advantage of the fact that this function ALWAYS returns a list
; of quoted objects.  See the call of strip-cadrs in ld-read-keyword-command
; below.  So if you optimize away some of the quotes, beware!

                 (value (cons (list 'quote obj) rst)))))))))

(defun exit-ld (state)

; This is the function most commonly aliased to the keyword command :q.  Its
; evaluation causes LD to terminate immediately.  Any function that returns
; three results, the first of which is nil, the second of which is :q and the
; third of which is STATE will do the same.

  (value :q))

(defun ld-read-keyword-command (key state)

; ld supports the convention that when a keyword :key is typed
; as a command and the corresponding symbol in the "ACL2" package,
; ACL2::key is a function or macro of arity n, we read n more
; objects, quote them, and apply the ACL2 function or macro.
; Thus,

; MY-PKG !>:ubt foo

; is the same thing as

; MY-PKG !>(ACL2::UBT 'foo)

; We require that the macro not have any lambda keyword arguments, since
; that makes it hard or impossible to determine how many things we should
; read.

; We also support the convention that if :key is bound on 'ld-keyword-aliases
; in state, say in the entry (:key n fn), we manufacture (fn 'x1 ...  'xn)
; instead of requiring that key be a function and returning (key 'x1 ...  'xn).

; This function returns four results, (mv erp keyp form state).  If erp is t an
; error was caused and the message has been printed.  Otherwise, keyp is
; non-nil or nil according to whether the keyword hack was involved.  Form is
; the parsed form of the command read, e.g., (acl2::ubt 'foo).  If non-nil,
; keyp is the actual list of objects read, e.g., (:ubt foo).

  (let ((temp (assoc-eq key (ld-keyword-aliases state))))
    (cond
     (temp
      (mv-let (erp args state)
              (ld-read-keyword-command1 (cadr temp) state)
              (cond
               (erp (mv t nil nil state))
               (t (mv nil
                      (cons key (strip-cadrs args))
                      (cons (caddr temp) args)
                      state)))))
     ((eq key :q)

; Here is the only place we recognize :q as a special command.  Essentially :q
; is an alias for (exit-ld state) except it is overridden by any other aliases
; for :q.

      (mv nil '(:q) '(exit-ld state) state))
     (t
      (let* ((sym (intern (symbol-name key) "ACL2"))
             (wrld (w state))
             (len (cond ((function-symbolp sym wrld)
                         (length (formals sym wrld)))
                        ((getpropc sym 'macro-body nil wrld)
                         (macro-minimal-arity
                          sym
                          `(:error "See LD-READ-KEYWORD-COMMAND.")
                          wrld))
                        (t nil))))
        (cond (len (mv-let (erp args state)
                           (ld-read-keyword-command1 len state)
                           (cond (erp (mv t nil nil state))
                                 (t (mv nil
                                        (cons key (strip-cadrs args))
                                        (cons sym args)
                                        state)))))
              (t (mv-let (erp val state)
                         (er soft 'LD
                             "Unrecognized keyword command ~x0."
                             key)
                         (declare (ignore erp val))
                         (mv t nil nil state)))))))))

(defun ld-fix-command (form)
  #-acl2-loop-only
  (when (and (consp form)
             (eq (car form) 'defconst) ; optimization
             (f-get-global 'boot-strap-flg *the-live-state*))
    (case-match form
      (('defconst name ('quote val) . &)
       (assert (boundp name))
       (let ((old-val (symbol-value name)))

; Note that we are in the boot-strap, where we presumably don't use
; redefinition.  If we later do so, we should see this assertion fire and then
; we can figure out what to do.

         (assert (equal val old-val))
         (when (not (eq val old-val))
           (let ((caddr-form (caddr form))) ; (quote val)
             (setf (cadr caddr-form)
                   old-val)))))))
  form)

(defun ld-read-command (state)

; This function reads an ld command from the standard-oi channel of state and
; returns it.  It implements the keyword command hack.  We return five results:
; (mv eofp erp keyp form state).  Eofp means we exhausted standard-oi.  Erp,
; when t, indicates that an error occurred, e.g., an ill-formed keyword command
; was read.  The error message has been printed.  Keyp, when non-nil, indicates
; that form is the parsed form of a keyword command.  The list of objects
; actually read is the non-nil value of keyp and that list, without the
; enclosing parentheses, should be printed instead of form.  Thus, if :kons is
; an alias for cons, then :kons x y will parse into (cons 'x 'y) and keyp will
; be (:kons x y).

  (pprogn
   (iprint-oracle-updates state) ; even before the read
   (mv-let (eofp val state)
           (read-standard-oi state)
           (pprogn
            (cond ((int= (f-get-global 'ld-level state) 1)
                   (let ((last-index (iprint-last-index state)))
                     (cond ((> last-index (iprint-soft-bound state))
                            (rollover-iprint-ar nil last-index state))
                           (t state))))
                  (t state))
            (cond (eofp (mv t nil nil nil state))
                  ((keywordp val)
                   (mv-let (erp keyp form state)
                           (ld-read-keyword-command val state)
                           (mv nil erp keyp form state)))
                  ((stringp val)
                   (let ((upval (string-upcase val)))
                     (cond ((find-non-hidden-package-entry
                             upval
                             (global-val 'known-package-alist (w state)))
                            (mv nil nil nil `(in-package ,upval) state))
                           (t (mv nil nil nil val state)))))
                  (t (mv nil nil nil (ld-fix-command val) state)))))))

(defun ld-print-command (keyp form col state)
  (with-base-10
   (mv-let (col state)
     (cond
      ((not (eq (ld-pre-eval-print state) t)) (mv col state))
      (keyp
       (fmt1 "~*0~|"
             (list (cons #\0 (list "" "~x*" "~x* " "~x* " keyp)))
             col
             (standard-co state)
             state
             (ld-evisc-tuple state)))
      (t
       (fmt1 "~q0~|"
             (list (cons #\0 form))
             col
             (standard-co state)
             state
             (ld-evisc-tuple state))))
     (declare (ignore col))
     state)))

(defmacro continue-from-illegal-state ()

; See the Essay on Illegal-states.

  '(er-progn (set-ld-pre-eval-filter :all state)
             (value :continuing)))

(defun ld-filter-command (form state)
  (let ((filter (ld-pre-eval-filter state)))
    (cond ((eq filter :all) (value t))
          ((eq filter :query)
           (acl2-query :filter
                       '("~#0~[~Y12?~/Eval?~]"
                         :y t :n nil :r :return :q :error
                         :? ("We are in the LD read-eval-print loop, ~
                              processing the forms in standard-oi.  The ~
                              form printed above is one of those forms.  Do ~
                              you want to evaluate it (Y) or not (N)?   You ~
                              may also answer R, meaning ``return ~
                              immediately from LD (without reading or ~
                              evaluating any more forms)'' or Q meaning ~
                              ``return immediately from LD, signaling an ~
                              error.''"
                             :y t :n nil :r :return :q :error))
                       (list (cons #\0 (if (eq (ld-pre-eval-print state) t) 1 0))
                             (cons #\1 form)
                             (cons #\2 (ld-evisc-tuple state)))
                       state))
          ((eq filter :illegal-state) ; See the Essay on Illegal-states.
           (cond ((equal form '(exit-ld state)) ; from :q
                  (value t))
                 ((equal form '(continue-from-illegal-state))
                  (er-progn (continue-from-illegal-state)
                            (value t)))
                 (t (er soft 'ld-filter-command
                        "You are still in an illegal state!  See :DOC ~
                         illegal-state.  You can submit the ~
                         form~|:CONTINUE-FROM-ILLEGAL-STATE~|to continue -- ~
                         AT YOUR OWN RISK."))))
          (t (value t)))))

#-acl2-loop-only
(defun-one-output ppr? (x raw-x col channel state)
  (cond
   ((and (raw-mode-p state)
         (bad-lisp-objectp x))
    (if (not (eq channel *standard-co*))
        (error "Attempted to print LD results to other than *standard-co*!"))
    (format t "[Note:  Printing non-ACL2 result.]")
    (terpri)
    (prin1 raw-x)
    state)
   (t
    (ppr x col channel state t))))

(defun ld-print-results (trans-ans state)

; This is the function used by ld to print the results of the
; trans-evaluation of the form read.  Trans-ans is of the form
; (stobjs-out . valx).

; If ld-post-eval-print is nil we print nothing.  If it is t, we
; print with the standard evisceration (ld-evisc-tuple).  If it is
; :command-conventions, we hide error/value/state pairs by just printing
; value and we don't print anything when the value is :invisible.

  (let ((flg (ld-post-eval-print state))
        (output-channel (standard-co state)))

; In raw mode in Allegro Common Lisp (and not GCL, but perhaps other lisps),
; evaluation of (time ...) causes the result value to be printed at the end of
; a comment line printed by time, which is unfortunate.  This sort of printing
; problem does not seem to have come up in other than raw mode, and besides, we
; do not want to try to model this sort of maybe-newline printing in the
; logic.  So we restrict this solution to raw mode.  Furthermore, the lisps
; listed below do not need this fix, and they all print a newline even with
; "~&" when apparently not necessary, so we exclude them from this fix.

    #-(or acl2-loop-only gcl cmu sbcl lispworks ccl)
    (when (raw-mode-p state)
      (format (get-output-stream-from-channel output-channel) "~&"))
    (cond
     ((null flg) state)
     (t
      (let* ((stobjs-out (car trans-ans))
             (valx (cdr trans-ans))
             (evisc-tuple (ld-evisc-tuple state))
             (evisc-alist (world-evisceration-alist state (car evisc-tuple)))
             (print-level (cadr evisc-tuple))
             (print-length (caddr evisc-tuple))
             (hiding-cars (cadddr evisc-tuple)))
        (mv-let
         (eviscerated-valx state)
         (eviscerate-stobjs-top (evisceration-stobj-marks stobjs-out nil)
                                valx
                                print-level print-length evisc-alist
                                (table-alist 'evisc-table (w state))
                                hiding-cars
                                state)
         (cond
          ((and (eq flg :command-conventions)
                (ld-error-triples state)
                (equal stobjs-out *error-triple-sig*))

; We get here if we are following command-conventions and the form
; returned triple (mv erp val state).  Note that erp must be a
; non-stobj (typically a Boolean) but that val may be a stobj or not.

           (cond
            ((eq (cadr valx) :invisible)
             state)
            (t
             (pprogn
              (princ$ (if (stringp (f-get-global 'triple-print-prefix state))
                          (f-get-global 'triple-print-prefix state)
                        "")
                      output-channel state)

; The following raw code is identical to the logic code below except that the
; raw code handles infix and raw-mode printing (which are, at the moment,
; entirely extra-logical).

              #-acl2-loop-only
              (let ((col
                     (if (stringp (f-get-global 'triple-print-prefix state))
                         (length (f-get-global 'triple-print-prefix state))
                       0))
                    (evg (cadr eviscerated-valx)))
                (cond
                 #+acl2-infix
                 ((and (live-state-p state)
                       (output-in-infixp state))
                  (print-infix
                   evg
                   nil
                   (- (fmt-hard-right-margin state) col)
                   0 col
                   (get-output-stream-from-channel output-channel)
                   t)
                  *the-live-state*)
                 (t (ppr? evg (cadr valx) col output-channel state))))
              #+acl2-loop-only
              (ppr (cadr eviscerated-valx)
                   (if (stringp (f-get-global 'triple-print-prefix state))
                       (length (f-get-global 'triple-print-prefix state))
                     0)
                   output-channel state t)
              (newline output-channel state)))))
          (t (pprogn
              #-acl2-loop-only
              (cond
               #+acl2-infix
               ((and (live-state-p state)
                     (output-in-infixp state))
                (print-infix
                 eviscerated-valx
                 nil
                 (fmt-hard-right-margin state)
                 0 0
                 (get-output-stream-from-channel output-channel)
                 t)
                *the-live-state*)
               (t (ppr? eviscerated-valx valx 0 output-channel state)))
              #+acl2-loop-only
              (ppr eviscerated-valx 0 output-channel state t)
              (newline output-channel state))))))))))

(defun ld-print-prompt (state)

; Like print-prompt except may print the prompt both to *standard-co*
; and (standard-co state).

  (mv-let (col state)
          (print-prompt (ld-prompt state) (standard-co state) state)
          (cond
           ((and (eq (standard-oi state) *standard-oi*)
                 (not (eq (standard-co state) *standard-co*)))
            (mv-let (irrel-col state)
                    (print-prompt (ld-prompt state) *standard-co* state)
                    (declare (ignore irrel-col))
                    (mv col state)))
           (t (mv col state)))))

(defun ld-return-error (state)
  (let ((action (ld-error-action state)))
    (cond ((eq action :return!)
           (mv :return
               (list :stop-ld (f-get-global 'ld-level state))
               state))
          ((and (consp action)
                (eq (car action) :exit))
           (mv action (good-bye-fn (cadr action)) state))
          (t (mv action :error state)))))

(defun initialize-accumulated-warnings ()
  #-acl2-loop-only
  (setq *accumulated-warnings* nil)
  nil)

(defun ld-read-eval-print (state)

; This is LD's read-eval-print step.  We read a form from standard-oi, eval it,
; and print the result to standard-co, will lots of bells and whistles
; controlled by the various LD specials.  The result of this function is a
; triple (mv signal val state), where signal is one of :CONTINUE, :RETURN,
; :ERROR, or (:EXIT n).  When the signal is :continue, :error, or (:exit n),
; val is irrelevant.  When the signal is :return, val is the "reason" we are
; terminating and is one of :exit, :eof, :error, :filter, or (:stop-ld n) where
; n is the ld-level at the time of termination.

  (pprogn
   (cond ((<= (f-get-global 'ld-level state) 1)
          (print-deferred-ttag-notes-summary state))
         (t state))
   (f-put-global 'raw-guard-warningp t state)
   (chk-absstobj-invariants state)
   (mv-let
    (col state)
    (if (and (eql (f-get-global 'in-verify-flg state) 1)
             (eql (f-get-global 'ld-level state) 1)
             (not (illegal-state-p state)))
        (mv 0 state)
      (ld-print-prompt state))
    (mv-let
     (eofp erp keyp form state)
     (let ((in-verify-flg (f-get-global 'in-verify-flg state)))
       (cond (in-verify-flg
              (pprogn (f-put-global 'in-verify-flg nil state)
                      (cond ((and (eql (f-get-global 'ld-level state) 1)
                                  (eql in-verify-flg 1)
                                  (not (illegal-state-p state)))
                             (pprogn
                              (print-re-entering-proof-builder nil state)
                              (mv nil nil nil '(verify) state)))
                            (t (ld-read-command state)))))
             (t (ld-read-command state))))
     (cond
      (eofp (cond ((ld-prompt state)
                   (pprogn (princ$ "Bye." (standard-co state) state)
                           (newline (standard-co state) state)

; In versions before v2-8, typing ctrl-d (ctrl-c ctrl-d in Emacs) did not
; immediately kill the Lisp if the resulting eof condition was detected by BRR
; processing.  The code below fixes that; let's hope it doesn't "fix" anything
; else!

                           (prog2$ (and (equal (standard-oi state) *standard-oi*)
                                        (good-bye))
                                   state)
                           (mv :return :eof state)))
                  (t (mv :return :eof state))))
      (erp (ld-return-error state))
      (t (pprogn
          (ld-print-command keyp form col state)
          (mv-let
           (erp ans state)
           (ld-filter-command form state)
           (cond
            (erp (ld-return-error state))
            ((null ans) (mv :continue nil state))
            ((eq ans :error) (mv :error nil state))
            ((eq ans :return) (mv :return :filter state))
            (t (assert$
                (eq ans t)
                (pprogn
                 (cond ((<= (f-get-global 'ld-level state) 1)
                        (prog2$ (initialize-accumulated-warnings)
                                (initialize-timers state)))
                       (t state))
                 (f-put-global 'last-make-event-expansion nil state)
                 (let* ((old-wrld (w state))
                        (old-default-defun-mode
                         (default-defun-mode old-wrld)))
                   (mv-let
                    (error-flg trans-ans state)
                    (revert-world-on-error
                     (mv-let (error-flg trans-ans state)
                             (if (raw-mode-p state)
                                 (acl2-raw-eval form state)
                               (trans-eval-default-warning form 'top-level
                                                           state t))

; If error-flg is non-nil, trans-ans is (stobjs-out . valx).

                             (er-progn
                              (assign last-ld-result (cons error-flg
                                                           trans-ans))
                              (cond
                               (error-flg (mv t nil state))
                               ((and (ld-error-triples state)
                                     (equal (car trans-ans) *error-triple-sig*)
                                     (car (cdr trans-ans)))
                                (mv t nil state))
                               (t (er-progn
                                   (maybe-add-command-landmark
                                    old-wrld
                                    old-default-defun-mode
                                    form
                                    trans-ans state)
                                   (mv nil trans-ans state)))))))

; If error-flg is non-nil, trans-ans is (stobjs-out . valx) and we know
; that valx is not an erroneous error triple if we're paying attention to
; error triples.

; The code inside the revert-world-on-error arranges to revert if either
; trans-eval returns an error, or the value is to be thought of as an
; error triple and it signals an error.  Error-flg, now, is set to t
; iff we reverted.

                    (cond
                     (error-flg (ld-return-error state))
                     ((and (equal (car trans-ans) *error-triple-sig*)
                           (eq (cadr (cdr trans-ans)) :q))
                      (mv :return :exit state))
                     (t (pprogn
                         (ld-print-results trans-ans state)
                         (cond
                          ((and (ld-error-triples state)
                                (not (eq (ld-error-action state) :continue))
                                (equal (car trans-ans) *error-triple-sig*)
                                (let ((val (cadr (cdr trans-ans))))
                                  (and (consp val)
                                       (eq (car val) :stop-ld))))
                           (mv :return
                               (list* :stop-ld
                                      (f-get-global 'ld-level state)
                                      (cdr (cadr (cdr trans-ans))))
                               state))
                          (t

; We make the convention of checking the new-namep filter immediately after
; we have successfully eval'd a form (rather than waiting for the next form)
; so that if the user has set the filter up he gets a satisfyingly
; immediate response when he introduces the name.

                           (let ((filter (ld-pre-eval-filter state)))
                             (cond
                              ((and (not (eq filter :all))
                                    (not (eq filter :query))
                                    (not (eq filter :illegal-state))
                                    (not (new-namep filter
                                                    (w state))))
                               (er-progn

; We reset the filter to :all even though we are about to exit this LD
; with :return.  This just makes things work if "this LD" is the top-level
; one and LP immediately reenters.

                                (set-ld-pre-eval-filter :all state)
                                (mv :return :filter state)))
                              (t (mv :continue nil state)))))))))))))))))))))))

(defun ld-loop (state)

; Note: We use a bit of raw lisp to ensure that the ACL2 unwind protect stack
; is properly configured before we execute the prompt for the next command.
; This acl2-unwind can be exercised, we think, by evaluating LD recursively
; and aborting the inferior LD so that it fails to cleanup after itself.

  (mv-let
   (signal val state)
   #+acl2-loop-only
   (ld-read-eval-print state)
   #-acl2-loop-only
   (progn (acl2-unwind *ld-level* t)
          (setq *trace-level* 0)
          (setq *hcomp-loop$-alist* nil) ; could be modified in raw-mode
          (ld-read-eval-print state))
   (cond ((eq signal :continue)
          (ld-loop state))
         ((eq signal :return)
          (value val))
         (t (mv t nil state)))))

; The following raw lisp special variable controls whether the raw lisp version
; of ld-fn-body, below, prints the header as per ld-verbose or does not.  The
; handling of aborts in ld-fn forces us to call ld-fn-body again after each
; abort and we wish to suppress the header message after all entrances other
; than the first.  This only happens after an abort (all bets are off) and the
; idea is to fool the user into thinking a normal error was signaled.

#-acl2-loop-only
(defvar *first-entry-to-ld-fn-body-flg*)

(defun get-directory-of-file (p)

; P is an absolute pathname for a file, not a directory.  We return an absolute
; pathname for the directory of that file.  See also get-parent-directory,
; which is a related function for directories.

  (let* ((p-rev (reverse p))
         (posn (position *directory-separator* p-rev)))
    (if posn
        (subseq p 0 (1- (- (length p) posn)))
      (er hard 'get-directory-of-file
          "Implementation error!  Unable to get directory for file ~x0."
          p))))

(defun update-cbd (standard-oi0 state)

; For the case that standard-oi0 is a string (representing a file), we formerly
; used extend-pathname to compute the new cbd from the old cbd and
; standard-oi0.  However, this caused us to follow soft links when that was
; undesirable.  Here is a suitable experiment, after building the nonstd books
; by connecting to books/nonstd/ and running "make clean-nonstd" followed by
; "make all-nonstd".  In this experiment, we had already certified the regular
; books using ACL2(h), and an error occurred because of an attempt to read
; books/arithmetic/equalities.cert, which used a special hons-only format.

; cd /projects/acl2/devel/books/nonstd/arithmetic/
; /projects/acl2/devel/allegro-saved_acl2r
; (ld "top.lisp")

  (let ((old-cbd (f-get-global 'connected-book-directory state)))
    (cond ((and old-cbd
                (stringp standard-oi0)
                (position *directory-separator* standard-oi0))
           (let* ((os (os (w state)))
                  (filename-dir
                   (expand-tilde-to-user-home-dir
                    (concatenate 'string
                                 (get-directory-of-file
                                  standard-oi0)
                                 *directory-separator-string*)
                    os 'update-cbd state)))
             (f-put-global
              'connected-book-directory
              (if (absolute-pathname-string-p filename-dir nil os)
                  filename-dir
                (our-merge-pathnames old-cbd filename-dir))
              state)))
          (t state))))

(defun ld-fn-body (standard-oi0 new-ld-specials-alist state)

; This function is defined only to make it convenient for ld-fn to execute its
; "body" either inside or outside an acl2-unwind-protect.

; WARNING: Because of the hidden acl2-unwind in the raw code for ld-loop above
; do not try to use acl2-unwind-protect in this function.  The cleanup form for
; it will be executed before the first form is read because ld-loop rolls back
; to the initialized version of the frame.  Furthermore, do not execute
; non-idempotent state changing forms here, i.e., incrementing or decrementing
; some counter in state, because the abort handling may cause this body to be
; reentered after an abort while the logical semantics suggests that it is
; entered only once.  (Of course, aborts mean all bets are off, but the idea is
; to make it seem like they are errors.)  We once incremented and decremented
; ld-level here and found the load level going down every time an abort
; occurred (because its increment was undone by the hidden acl2-unwind in
; ld-loop, mentioned above, and it was decremented at every abort).

  #+(and acl2-par (not acl2-loop-only))
  (when (and (not *wormholep*)

; We do not reset parallelism variables while in a wormhole (say from :brr),
; because that could interfere with a surrounding (outside the wormhole) prover
; call.

; Fortunately, it isn't necessary to do that reset, because there is nothing to
; clean up: we (plan as of Feb. 2011 to) disable entry to the prover from a
; wormhole when parallelism is enabled for the prover.

             (or (eql *ld-level* 1)
                 *reset-parallelism-variables*))

; We claim that the parallelism variables are reset when either (1) we are
; entering the top-level ACL2 loop from raw Lisp, or else (2) a raw Lisp break
; has occurred.  Let's see how the conditions above guarantee that claim.  If
; (1) holds then the initial call of ld-fn-body in ld-fn0 will get us here with
; *ld-level* 1.  When (2) holds then our-abort threw to 'local-top-level after
; setting *reset-parallelism-variables* to t, and the ld-fn-body call in ld-fn0
; is re-entered after that throw is caught, and here we are!

; In rare cases we might get here without (1) or (2) holding -- say, after :a!.
; But it's OK to call reset-all-parallelism-variables in such cases; we simply
; prefer to minimize the frequency of calls, for efficiency.

    (reset-all-parallelism-variables))

  (pprogn
    (f-put-ld-specials new-ld-specials-alist state)
    (update-cbd standard-oi0 state)
    (cond (#+acl2-loop-only (ld-verbose state)
           #-acl2-loop-only (and *first-entry-to-ld-fn-body-flg*
                                  (ld-verbose state))

; We print the file name rather than the channel.

           (cond
            ((eq (ld-verbose state) t)
             (fms (if (eq standard-oi0 *standard-oi*)
                      "ACL2 loading *standard-oi*.~%"
                      "ACL2 loading ~x0.~%")
                  (list (cons #\0 (cond ((consp standard-oi0) (kwote standard-oi0))
                                        (t standard-oi0))))
                  (standard-co state)
                  state
                  (ld-evisc-tuple state)))
            (t (with-base-10
                (fms
                 "~@0"
                 (list (cons #\0 (ld-verbose state))
                       (cons #\v (f-get-global 'acl2-version state))
                       (cons #\l (f-get-global 'ld-level state))
                       (cons #\c (f-get-global 'connected-book-directory
                                               state))
                       (cons #\b (f-get-global 'system-books-dir
                                               state)))
                 (standard-co state)
                 state
                 (ld-evisc-tuple state))))))
          (t state))
    (mv-let
     (erp val state)
     (ld-loop state)
     (pprogn
      (cond ((eq (ld-verbose state) t)
             (fms (if (eq standard-oi0 *standard-oi*)
                      "Finished loading *standard-oi*.~%"
                      "Finished loading ~x0.~%")
                  (list (cons #\0 (cond ((consp standard-oi0) (kwote standard-oi0))
                                        (t standard-oi0))))
                  (standard-co state)
                  state
                  (ld-evisc-tuple state)))
            (t state))
      (mv erp val state)))))

(defun ld-fn1 (standard-oi0 alist state bind-flg)

; If this function weren't defined we would have to duplicate its body twice in
; ld-fn, once in the #+acl2-loop-only section and again in the
; #-acl2-loop-only section in the case where the state is not the live state.
; The reason we grab the old ld-level and use it in the cleanup form rather
; than just decrementing the then current value is that we do not know how many
; times the cleanup form will be tried before it is not interrupted.

  (let* ((old-ld-level (f-get-global 'ld-level state))
         (new-ld-level (1+ old-ld-level))
         (old-cbd (f-get-global 'connected-book-directory state)))
    (er-let*
     ((pair (chk-acceptable-ld-fn alist state)))
     (let ((old-ld-specials-alist (f-get-ld-specials state))
           (new-ld-specials-alist (car pair))
           (channel-closing-alist (cdr pair)))
       (if bind-flg
           (acl2-unwind-protect
            "ld-fn"
            (pprogn
             (f-put-global 'ld-level new-ld-level state)
             (ld-fn-body standard-oi0 new-ld-specials-alist state))
            (pprogn
             (f-put-global 'ld-level old-ld-level state)
             (f-put-global 'connected-book-directory old-cbd state)
             (f-put-ld-specials old-ld-specials-alist state)
             (close-channels channel-closing-alist state))
            (pprogn
             (f-put-global 'ld-level old-ld-level state)
             (f-put-global 'connected-book-directory old-cbd state)
             (f-put-ld-specials old-ld-specials-alist state)
             (close-channels channel-closing-alist state)))
         (acl2-unwind-protect
          "ld-fn"
          (pprogn (f-put-global 'ld-level new-ld-level state)
                  (ld-fn-body standard-oi0 new-ld-specials-alist state))
          (f-put-global 'ld-level old-ld-level state)
          (f-put-global 'ld-level old-ld-level state)))))))

(defun ld-fn-alist (alist state)
  (let ((standard-oi (cdr (assoc 'standard-oi alist)))
        (dir         (cdr (assoc 'dir alist)))
        (ctx         'ld)
        (os (os (w state))))
    (cond ((and (stringp standard-oi)
                dir)
           (let ((standard-oi-expanded
                  (expand-tilde-to-user-home-dir standard-oi os ctx state)))
             (cond ((absolute-pathname-string-p standard-oi-expanded nil os)
                    (er hard ctx
                        "It is illegal to supply a :DIR argument to LD here ~
                         because the supplied filename,~|~%  ~s0,~|~%is an ~
                         absolute pathname (see :DOC pathname), and hence ~
                         there is no reasonable way to merge it with a :DIR ~
                         value."
                        standard-oi))
                   (t
                    (let ((resolve-dir
                           (include-book-dir-with-chk hard 'ld dir)))
                      (cond (resolve-dir
                             (put-assoc-eq 'standard-oi
                                           (our-merge-pathnames
                                            resolve-dir
                                            standard-oi-expanded)
                                           (remove1-assoc-eq 'dir alist)))
                            (t alist)))))))
          ((and (not (stringp standard-oi))
                dir)
           (er hard ctx
               "It is illegal to supply a :DIR argument to LD here because ~
                the first argument of the LD call, ~x0, is not a string.  ~
                Such an argument would be ignored anyhow, so you probably ~
                should consider simply removing that :DIR argument.  See :DOC ~
                ld."
               standard-oi))
          ((assoc-eq 'dir alist)
           (remove1-assoc-eq 'dir alist))
          (t alist))))

(defun ld-fn0 (alist state bind-flg)

; We set the ld specials to the values specified in alist and then enter the
; standard ACL2 read-eval-print loop.  If bind-flg is t then the ld specials
; are restored to their pre-call values upon exit or abort.  Otherwise they are
; not.  Another interpretation of the flag is: if bind-flg is t then the load
; specials are merely "bound" locally to the values in alist, otherwise, they
; are globally smashed to values in alist.  If this call is considered the
; "top-level" call of ld-fn, bind-flg ought to be nil: the final values of the
; load specials established during the interaction survive exiting to raw lisp
; and are present when ld-fn is reentered later.  If this call is not
; "top-level" then the values established during interaction are lost on exit.

; Advice: It is best to read this function as though ld-fn1's body were
; substituted below.  Ld-fn1 is just a way to avoid duplication of code and has
; nothing to do with the unwind protection we are really implementing.

  (let ((alist (ld-fn-alist alist state)))

    #+acl2-loop-only
    (ld-fn1 (cdr (assoc-eq 'standard-oi alist)) alist state bind-flg)

; The part in UPPERCASE below is raw lisp that manages the unwind stack and
; *ld-level*.  The part in lowercase is identical to the pure ACL2 in ld-fn1
; above.  It is helpful to split the buffer, put the pure ACL2 in the top
; window and read what follows in the bottom one.  Observe that if the state is
; not live, we just use the pure ACL2.  So start with the PROGN below.

    #-acl2-loop-only
    (COND
     ((LIVE-STATE-P STATE)
      (PROGN
       (ACL2-UNWIND *LD-LEVEL* NIL)
       (PUSH NIL *ACL2-UNWIND-PROTECT-STACK*)
       (LET* ((*LD-LEVEL* (1+ *LD-LEVEL*))
              (*READTABLE* *ACL2-READTABLE*)
              (*FIRST-ENTRY-TO-LD-FN-BODY-FLG* T)
              (ABORT-OBJ (CONS 'ABORT NIL))
              (THROWN-VAL NIL)
              (LD-ERP ABORT-OBJ)
              (LD-VAL NIL)) ; below implies an abort happened
             (let* ((old-ld-level (f-get-global 'ld-level state))
                    (new-ld-level (1+ old-ld-level))
                    (old-cbd (f-get-global 'connected-book-directory state)))
               (MV-LET
                (ERP pair STATE)
                (chk-acceptable-ld-fn alist state)
                (COND
                 (ERP (ACL2-UNWIND (1- *LD-LEVEL*) NIL) (MV ERP PAIR STATE))
                 (T
                  (let ((old-ld-specials-alist (f-get-ld-specials state))
                        (new-ld-specials-alist (car pair))
                        (channel-closing-alist (cdr pair)))
                    (PUSH-CAR
                     (CONS "ld-fn"
                           (IF bind-flg
                               (FUNCTION
                                (LAMBDA
                                 NIL
                                 (pprogn
                                  (f-put-global 'ld-level old-ld-level state)
                                  (f-put-global 'connected-book-directory
                                                old-cbd state)
                                  (f-put-ld-specials old-ld-specials-alist
                                                     state)
                                  (close-channels channel-closing-alist
                                                  state))))
                               (FUNCTION
                                (LAMBDA
                                 NIL
                                 (pprogn
                                  (f-put-global 'ld-level old-ld-level state))))))
                     *ACL2-UNWIND-PROTECT-STACK*
                     'LD-FN)
                    (TAGBODY
                     LOOP
                     (UNWIND-PROTECT
                      (pprogn (f-put-global 'ld-level new-ld-level state)
                              (PROGN
                               (SETQ THROWN-VAL
                                     (CATCH
                                      'LOCAL-TOP-LEVEL
                                      (MV-LET
                                       (ERP VAL STATE)
                                       (ld-fn-body (cdr (assoc-eq 'standard-oi
                                                                  alist))
                                                   new-ld-specials-alist state)
                                       (PROGN
                                        (WHEN bind-flg
                                              (f-put-global
                                               'connected-book-directory
                                               old-cbd
                                               state))
                                        (SETQ LD-ERP ERP)
                                        (SETQ LD-VAL VAL)
                                        NIL))))
                               STATE))
                      (WITH-INTERRUPTS

; We allow interrupts for the cleanup form.  This seems acceptable because of
; how we handle ACL2 unwind-protects, calling ACL2-UNWIND; see The Essay on
; Unwind-Protect.  It also seems acceptable because some Lisps don't disable
; interrupts during evaluation of unwind-protect cleanup forms, so we expect to
; allow interrupts anyhow.  And it seems important to do so, in case printing
; the gag-state needs to be interrupted; see the call of print-summary-on-error
; in prove-loop0.

                       (COND
                        (*ACL2-PANIC-EXIT-STATUS*
                         (exit-lisp *ACL2-PANIC-EXIT-STATUS*))
                        ((EQ LD-ERP ABORT-OBJ)

; We get here if the ld-fn-body failed to terminate normally.  This can happen
; either because lisp caused some error or because we threw to the tag above.
; If we threw to the tag then LD-ERP is ABORT-OBJ (because we didn't get to
; the SETQ above) and THROW-VAL is whatever we threw.  If we did not throw,
; then THROWN-VAL is NIL (because the lisp error prevented us from doing the
; SETQ THROWN-VAL).  We make the convention that we always throw non-nil
; values to the tag so as to distinguish these two cases.

                         #+akcl (si::RESET-STACK-LIMITS)
                         (COND ((EQ THROWN-VAL :ABORT)

; THROWN-VAL is always either NIL (meaning no throw occurred) or else the
; "reason" we threw.  Currently the possibilities are :ABORT (thrown when the
; user types (a!)), :POP (thrown when the user types (p!)) or :WORMHOLE-ER
; (thrown when we tried to make a non-undoable change to state while in a
; wormhole).  We only care about :ABORT.  :WORMHOLE-ER is treated as a "normal"
; lisp error, i.e., we just unwind back to here and continue at this level.
; :ABORT means we are to exit all the way back to *LD-LEVEL* 1.  :POP means
; that we are to pop up one level unless we are already at the top level.

                                (COND ((= *LD-LEVEL* 1)

; At *LD-LEVEL* = 1 we know *standard-co* is *STANDARD-OUTPUT*.

                                       (PRINC "Abort to ACL2 top-level"
                                              *STANDARD-OUTPUT*)
                                       (TERPRI *STANDARD-OUTPUT*))
                                      (T
                                       (THROW 'LOCAL-TOP-LEVEL :ABORT))))
                               ((EQ THROWN-VAL :POP)
                                (COND ((= *LD-LEVEL* 1)
                                       (PRINC "Currently at ACL2 top-level"
                                              *STANDARD-OUTPUT*))
                                      (t
                                       (COND ((= *LD-LEVEL* 2)
                                              (PRINC "Pop up to ACL2 top-level"
                                                     *STANDARD-OUTPUT*))
                                             (t
                                              (PRINC "Pop up one LD level"
                                                     *STANDARD-OUTPUT*)))
                                       (WHEN (NOT (EQ (LD-ERROR-ACTION STATE)
                                                      :ERROR))
                                             (SET-LD-ERROR-ACTION :RETURN!
                                                                  STATE))))
                                (TERPRI *STANDARD-OUTPUT*)))
                         (ACL2-UNWIND *LD-LEVEL* T)
; We first unwind back to the current level so STANDARD-OI and LD-ERROR-ACTION
; are correctly set.
                         (COND ((EQ (LD-ERROR-ACTION STATE) :CONTINUE)
                                (SETQ *FIRST-ENTRY-TO-LD-FN-BODY-FLG*
                                      (COND ((EQ THROWN-VAL :ABORT) T)
                                            (T NIL)))
                                (SETQ NEW-LD-SPECIALS-ALIST NIL)
                                (SETQ THROWN-VAL NIL)
                                (GO LOOP))
                               ((EQ (LD-ERROR-ACTION STATE) :RETURN)
                                (ACL2-UNWIND (1- *LD-LEVEL*) NIL)
                                (RETURN-FROM LD-FN0 (VALUE :ERROR)))
                               ((EQ (LD-ERROR-ACTION STATE) :RETURN!)
                                (ACL2-UNWIND (1- *LD-LEVEL*) NIL)
                                (RETURN-FROM
                                 LD-FN0
                                 (VALUE (LIST :STOP-LD
                                              (F-GET-GLOBAL 'LD-LEVEL
                                                            STATE)))))
                               (T (ACL2-UNWIND (1- *LD-LEVEL*) NIL)
                                  (RETURN-FROM LD-FN0 (MV T NIL STATE)))))
                        (T
                         (ACL2-UNWIND (1- *LD-LEVEL*) NIL)
                         (RETURN-FROM LD-FN0
                                      (MV LD-ERP LD-VAL STATE)))))))))))))))
     (T (ld-fn1 (cdr (assoc-eq 'standard-oi alist)) alist state bind-flg)))))

(defun ld-fn (alist state bind-flg)

; See ld-fn0.  Here, we just provide a little wrapper for top-level calls of
; ld-fn0 in case that there is an interrupt that isn't handled inside ld-fn0.
; To see this issue in action, evaluate the following four forms and interrupt
; the last one twice: once late in the proof attempt and once immediately upon
; printing the checkpoint summary (which is done by a call of acl2-unwind in
; the cleanup form of an unwind-protect, on behalf of a call of
; acl2-unwind-protect inside prove-loop0 that invokes
; print-summary-on-error upon an error).

; (defun foo (n acc)
;   (if (zp n)
;       acc
;     (foo (1- n)
;          (cons `(equal (nth ,n x) x)
;                acc))))
;
; (defmacro mac (n)
;   (cons 'and (foo n nil)))
;
; (set-rewrite-stack-limit 10000)
;
; (thm
;  (mac 1000)
;  :otf-flg t
;  :hints (("Goal" :do-not '(preprocess))))

  (let ((alist (if (assoc-eq 'ld-error-action alist)
                  alist
                (acons 'ld-error-action
                       (let ((action (ld-error-action state)))
                         (if (and (consp action)
                                  (eq (car action) :exit))
                             action
                           :return!))
                       alist))))
    (cond
     ((not (f-get-global 'ld-okp state))
      (er soft 'ld
          "It is illegal to call LD in this context.  See :DOC ~
           calling-ld-in-bad-contexts."))
     (t
      #-acl2-loop-only
      (cond (*load-compiled-stack*
             (error "It is illegal to call LD while loading a compiled book, ~
                     in this case:~%~a .~%See :DOC calling-ld-in-bad-contexts."
                    (caar *load-compiled-stack*)))
            ((= *ld-level* 0)
             (return-from
              ld-fn
              (let ((complete-flg nil))
                (unwind-protect
                    (mv-let (erp val state)
                      (ld-fn0 alist state bind-flg)
                      (progn (setq complete-flg t)
                             (mv erp val state)))
                  (when (and (not complete-flg)
                             (not *acl2-panic-exit-status*))
                    (fms "***NOTE***: An interrupt or error has occurred in ~
                          the process of cleaning up from an earlier ~
                          interrupt or error.  This is likely to leave you at ~
                          the raw Lisp prompt after you abort to the top ~
                          level.  If so, then execute ~x0 to re-enter the ~
                          ACL2 read-eval-print loop.~|~%"
                         (list (cons #\0 '(lp)))
                         *standard-co*
                         state
                         nil)))))))
      (ld-fn0 alist state bind-flg)))))

(defmacro ld (standard-oi
              &key
              dir
              (standard-co 'same standard-cop)
              (proofs-co 'same proofs-cop)
              (current-package 'same current-packagep)
              (ld-skip-proofsp 'same ld-skip-proofspp)
              (ld-redefinition-action 'same ld-redefinition-actionp)
              (ld-prompt 'same ld-promptp)
              (ld-missing-input-ok 'same ld-missing-input-okp)
              (ld-pre-eval-filter 'same ld-pre-eval-filterp)
              (ld-pre-eval-print 'same ld-pre-eval-printp)
              (ld-post-eval-print 'same ld-post-eval-printp)
              (ld-evisc-tuple 'same ld-evisc-tuplep)
              (ld-error-triples 'same ld-error-triplesp)
              (ld-error-action 'same ld-error-actionp)
              (ld-query-control-alist 'same ld-query-control-alistp)
              (ld-verbose 'same ld-verbosep)
              (ld-user-stobjs-modified-warning ':same))
  `(ld-fn
    (list ,@(append
             (list `(cons 'standard-oi ,standard-oi))
             (if dir
                 (list `(cons 'dir ,dir))
                 nil)
             (if standard-cop
                 (list `(cons 'standard-co ,standard-co))
                 nil)
             (if proofs-cop
                 (list `(cons 'proofs-co ,proofs-co))
                 nil)
             (if current-packagep
                 (list `(cons 'current-package ,current-package))
                 nil)
             (if ld-skip-proofspp
                 (list `(cons 'ld-skip-proofsp ,ld-skip-proofsp))
                 nil)
             (if ld-redefinition-actionp
                 (list `(cons 'ld-redefinition-action
                              ,ld-redefinition-action))
                 nil)
             (if ld-promptp
                 (list `(cons 'ld-prompt ,ld-prompt))
                 nil)
             (if ld-missing-input-okp
                 (list `(cons 'ld-missing-input-ok ,ld-missing-input-ok))
               nil)
             (if ld-pre-eval-filterp
                 (list `(cons 'ld-pre-eval-filter ,ld-pre-eval-filter))
                 nil)
             (if ld-pre-eval-printp
                 (list `(cons 'ld-pre-eval-print ,ld-pre-eval-print))
                 nil)
             (if ld-post-eval-printp
                 (list `(cons 'ld-post-eval-print ,ld-post-eval-print))
                 nil)
             (if ld-evisc-tuplep
                 (list `(cons 'ld-evisc-tuple ,ld-evisc-tuple))
                 nil)
             (if ld-error-triplesp
                 (list `(cons 'ld-error-triples ,ld-error-triples))
                 nil)
             (if ld-error-actionp
                 (list `(cons 'ld-error-action ,ld-error-action))
                 nil)
             (if ld-query-control-alistp
                 (list `(cons 'ld-query-control-alist ,ld-query-control-alist))
                 nil)
             (if ld-verbosep
                 (list `(cons 'ld-verbose ,ld-verbose))
                 nil)
             (if (eq ld-user-stobjs-modified-warning :same)
                 nil
               (list `(cons 'ld-user-stobjs-modified-warning
                            ,ld-user-stobjs-modified-warning)))))
    state
    t))

(defmacro quick-test nil

; We might want to add other events to the list below to test a wide variety of
; features.

  '(ld '((defun app (x y)
           (declare (xargs :guard (true-listp x)))
           (if (eq x nil) y (cons (car x) (app (cdr x) y))))
         (defthm true-listp-app
           (implies (true-listp x) (equal (true-listp (app x y)) (true-listp y))))
         :program
         (defun rev (x)
           (declare (xargs :guard (true-listp x)))
           (if (eq x nil) nil (app (rev (cdr x)) (list (car x)))))
         :logic
         (verify-termination rev)
         (verify-guards rev)
         (defthm true-listp-rev
           (implies (true-listp x) (true-listp (rev x)))
           :rule-classes :type-prescription)
         (defthm rev-rev (implies (true-listp x) (equal (rev (rev x)) x))))
       :ld-pre-eval-print t
       :ld-error-action :return

; Do we want to allow this macro to be called inside code?  There's no obvious
; reason why not.  So we need to specify the following keyword.

       :ld-user-stobjs-modified-warning :same))

(defun wormhole-prompt (channel state)
  (fmt1 "Wormhole ~s0~sr ~@1~*2"
        (list (cons #\0 (f-get-global 'current-package state))
              (cons #\1 (defun-mode-prompt-string state))
              (cons #\r
                    #+:non-standard-analysis "(r)"
                    #-:non-standard-analysis "")
              (cons #\2
                    (list "" ">" ">" ">"
                          (make-list-ac (- (f-get-global 'ld-level state) 1) nil nil))))
        0 channel state nil))

(defun reset-ld-specials-fn (reset-channels-flg state)

; We restore all of the ld specials to their initial, top-level
; values, except for the three channels, standard-oi, standard-co, and
; proofs-co, which are not reset unless the reset-channels-flg is t.
; Of course, if this function is called while under a recursive ld,
; then when we pop out of that ld, the reset values will be lost.

  (f-put-ld-specials
   (cond (reset-channels-flg *initial-ld-special-bindings*)
         (t (cdddr *initial-ld-special-bindings*)))
   state))

(defmacro reset-ld-specials (reset-channels-flg)
  `(reset-ld-specials-fn ,reset-channels-flg state))

(defun maybe-reset-defaults-table1
  (key pre-defaults-tbl post-defaults-tbl state)
  (let* ((pre-val (cdr (assoc-eq key pre-defaults-tbl)))
         (post-val (cdr (assoc-eq key post-defaults-tbl)))
         (cmd `(table acl2-defaults-table ,key ',pre-val)))
    (if (equal pre-val post-val)
        (value nil)
      (er-let*
       ((ans
         (acl2-query
          :ubt-defaults
          '("The default ~s0 was ~x1 before undoing, but will be ~x2 after ~
             undoing unless the command ~x3 is executed.  Do you wish to ~
             re-execute this command after the :ubt?"
            :y t :n nil
            :? ("If you answer in the affirmative, then the command ~X34 will ~
                 be executed on your behalf.  This will make the default ~s0 ~
                 equal to ~x1, which is what it was just before your :ubt ~
                 command was executed.  Otherwise, the default ~s0 will be ~
                 what it is in the world after the undoing, namely ~x2.  See ~
                 also :DOC acl2-defaults-table."
                :y t :n nil))
          (list (cons #\0 (string-downcase (symbol-name key)))
                (cons #\1 pre-val)
                (cons #\2 post-val)
                (cons #\3 cmd)
                (cons #\4 nil))
          state)))
       (if ans
           (ld (list cmd)
               :ld-pre-eval-filter :all
               :ld-pre-eval-print t
               :ld-post-eval-print :command-conventions
               :ld-evisc-tuple (abbrev-evisc-tuple state)
               :ld-error-triples t
               :ld-error-action :return)
         (value nil))))))

(defun maybe-reset-defaults-table2
  (keys pre-defaults-tbl post-defaults-tbl state)
  (if keys
      (er-progn (maybe-reset-defaults-table1
                 (car keys) pre-defaults-tbl post-defaults-tbl state)
                (maybe-reset-defaults-table2
                 (cdr keys) pre-defaults-tbl post-defaults-tbl state))
    (value nil)))

(defun maybe-reset-defaults-table (pre-defaults-tbl post-defaults-tbl state)
  (maybe-reset-defaults-table2 (union-equal (strip-cars pre-defaults-tbl)
                                            (strip-cars post-defaults-tbl))
                               pre-defaults-tbl post-defaults-tbl state))

(defun delete-something (lst)

; Lst must be non-nil.  We return a list that is one shorter than lst by either
; dropping the first nil we find in lst or, if there are no nils, the last
; element.

  (cond ((null (cdr lst)) nil)
        ((null (car lst)) (cdr lst))
        (t (cons (car lst) (delete-something (cdr lst))))))

(defun store-in-kill-ring (x0 ring)

; A "kill ring" is a fancy queue that stores a fixed number, say n, of non-nil
; items in the order in which they were stored.  Only the most recent n non-nil
; items stored are saved.  When a non-nil item is stored and the ring is full,
; the oldest item is dropped out and lost.  So we have described a queue so
; far.  The only other operation on kill rings is "rotate" which selects an
; item from the kill ring but does not remove it.  Given a ring containing n
; items, n+1 rotations will return the each of the items in turn and in the
; reverse order in which they were stored.  More on rotation later.

; Kill rings are just lists of the n items, in order.  The length of the list
; is n but there may be nils in the list.  The initial kill ring of length n
; is just n nils.

  (cond ((or (null x0)          ; item is nil or the size of the
             (null ring))       ; ring is 0.  We store nothing.
         ring)
        (t (cons x0 (delete-something ring)))))

(defun rotate-kill-ring1 (ring xn)
  (cond ((null ring) xn)
        ((car ring) (append ring xn))
        (t (rotate-kill-ring1 (cdr ring) (append xn (list nil))))))

(defun rotate-kill-ring (ring xn)

; See store-in-kill-ring for background on rings.  Xn is an element to add to
; the ring.  We step the ring once, returning (mv item ring'), where item is
; the most recently added item in ring and ring' is the result of removing that
; item and adding xn as the oldest item in the ring.  Thus, a series of
; rotate-kill-ring n+1 long will return us to the original configuration.

  (cond ((null (car ring)) (mv nil ring))
        (t (mv (car ring)
               (rotate-kill-ring1 (cdr ring) (list xn))))))

(defun ubt-ubu-fn1 (kwd wrld pred-wrld state)
  (let ((pre-defaults-table (table-alist 'acl2-defaults-table wrld)))
    (er-let*
     ((redo-cmds (ubt-ubu-query kwd wrld pred-wrld nil
                                nil wrld state nil)))
     (pprogn
      (f-put-global
       'undone-worlds-kill-ring
       (store-in-kill-ring wrld
                           (f-get-global
                            'undone-worlds-kill-ring
                            state))
       state)
      (set-w 'retraction pred-wrld state)
      (let ((redo-cmds (if (eq (car redo-cmds)
                               (default-defun-mode pred-wrld))
                           (cdr redo-cmds)
                         redo-cmds)))
        (er-progn
         (if redo-cmds
             (mv-let (col state)
                     (fmt "Undoing complete.  Redoing started...~%"
                          nil (standard-co state) state nil)
                     (declare (ignore col))
                     (value nil))
           (value nil))
         (if redo-cmds
             (ld redo-cmds
                 :ld-redefinition-action '(:doit! . :overwrite)
                 :ld-pre-eval-filter :all
                 :ld-pre-eval-print t
                 :ld-post-eval-print :command-conventions
                 :ld-evisc-tuple (abbrev-evisc-tuple state)
                 :ld-error-triples t
                 :ld-error-action :return
                 :ld-query-control-alist
                 (cons '(:redef :y)
                       (ld-query-control-alist state)))
           (value nil))
         (if redo-cmds
             (mv-let (col state)
                     (fmt1 "Redoing complete.~%~%"
                           nil 0 (standard-co state) state nil)
                     (declare (ignore col))
                     (value nil))
           (value nil))
         (maybe-reset-defaults-table
          pre-defaults-table
          (table-alist 'acl2-defaults-table (w state))
          state)
         (pcs-fn :x :x nil state)
         (value :invisible)))))))

(defun ubt?-ubu?-fn (kwd cd state)

; Kwd is :ubt or :ubu.

  (let* ((wrld (w state))
         (command-number-baseline
          (access command-number-baseline-info
                  (global-val 'command-number-baseline-info wrld)
                  :current)))
    (er-let* ((cmd-wrld (er-decode-cd cd wrld kwd state)))
             (cond ((if (eq kwd :ubt)
                        (<= (access-command-tuple-number (cddar cmd-wrld))
                            command-number-baseline)
                      (< (access-command-tuple-number (cddar cmd-wrld))
                         command-number-baseline))
                    (cond
                     ((let ((command-number-baseline-original
                             (access command-number-baseline-info
                                     (global-val 'command-number-baseline-info wrld)
                                     :original)))
                        (if (eq kwd :ubt)
                            (<= (access-command-tuple-number (cddar cmd-wrld))
                                command-number-baseline-original)
                          (< (access-command-tuple-number (cddar cmd-wrld))
                             command-number-baseline-original)))
                      (er soft kwd "Can't undo into system initialization."))
                     (t (er soft kwd
                            "Can't undo into prehistory.  See :DOC ~
                             reset-prehistory."))))
                   ((and (eq kwd :ubu) (equal wrld cmd-wrld))
                    (er soft kwd
                        "Can't undo back to where we already are!"))
                   (t
                    (let ((pred-wrld (if (eq kwd :ubt)
                                         (scan-to-command (cdr cmd-wrld))
                                       cmd-wrld)))
                      (ubt-ubu-fn1 kwd wrld pred-wrld state)))))))

(defun ubt-ubu-fn (kwd cd state)

; Kwd is :ubt or :ubu.

  (state-global-let*
   ((ld-query-control-alist
     (list* `(,kwd :n!)
            '(:ubt-defaults :n)
            (@ ld-query-control-alist))))
   (mv-let (erp val state)
           (ubt?-ubu?-fn kwd cd state)
           (declare (ignore erp val))
           (value :invisible))))

(defun ubt!-ubu!-fn (kwd cd state)

; Kwd is :ubt or :ubu.

  (state-global-let*
   ((ld-query-control-alist
     (list* `(,kwd :n!)
            '(:ubt-defaults :n)
            (@ ld-query-control-alist)))
    (inhibit-output-lst
     (union-equal '(observation warning error)
                  (@ inhibit-output-lst))))
   (mv-let (erp val state)
           (ubt?-ubu?-fn kwd cd state)
           (declare (ignore erp val))
           (value :invisible))))

(defmacro ubt-prehistory ()
  (list 'ubt-prehistory-fn 'state))

(defun ubt-prehistory-fn (state)
  (let* ((ctx 'ubt-prehistory)
         (wrld (w state))
         (command-number-baseline-info
          (global-val 'command-number-baseline-info wrld))
         (command-number-baseline
          (access command-number-baseline-info
                  command-number-baseline-info
                  :current)))
    (cond ((eql command-number-baseline
                (access command-number-baseline-info
                        command-number-baseline-info
                        :original))
           (er soft ctx
               "There is no reset-prehistory event to undo."))
          ((access command-number-baseline-info
                   command-number-baseline-info
                   :permanent-p)
           (er soft ctx
               "It is illegal to undo a reset-prehistory event that had its ~
                permanent-p flag set to t.  See :DOC reset-prehistory."))
          (t (er-let* ((val (ubt-ubu-fn1
                             :ubt-prehistory
                             wrld
                             (scan-to-command
                              (cdr (lookup-world-index
                                    'command command-number-baseline wrld)))
                             state)))
                      (er-progn
                       (reset-kill-ring t state)
                       (value val)))))))

(defun oops-warning (state)

; If the set of Lisps that compile all functions changes from {sbcl, ccl}, then
; change the #+/#- below accordingly.

  #+(or sbcl ccl)
  (fms "Installing the requested world.~|~%"
       nil (f-get-global 'standard-co state) state nil)
  #-(or sbcl ccl)
  (fms "Installing the requested world.  Note that functions being re-defined ~
        during this procedure will not have compiled definitions, even if ~
        they had compiled definitions before the last :ubt or :u.~|~%"
       nil (f-get-global 'standard-co state) state nil))

(defun oops-fn (state)
  (mv-let (new-wrld new-kill-ring)
          (rotate-kill-ring (f-get-global 'undone-worlds-kill-ring state)
                            (w state))
          (cond ((null new-wrld)
                 (cond ((null (f-get-global 'undone-worlds-kill-ring state))
                        (er soft :oops
                            "Oops has been disabled in this ACL2 session.  ~
                             See :DOC reset-kill-ring"))
                       (t
                        (er soft :oops
                            "ACL2 cannot execute :oops at this time, ~
                             presumably because you have never executed :ubt ~
                             or :u during this ACL2 session (at least not ~
                             since the last invocation of reset-kill-ring)."))))
                (t (er-progn
                    (revert-world-on-error
                     (pprogn
                      (oops-warning state)
                      (set-w! new-wrld state)
                      (er-progn (pcs-fn :x :x nil state)
                                (value nil))))
                    (pprogn
                     (f-put-global 'undone-worlds-kill-ring
                                   new-kill-ring state)
                     (value :invisible)))))))

(defmacro oops nil
  '(oops-fn state))

(defmacro i-am-here ()
  '(mv-let (col state)
           (fmt1 "~ I-AM-HERE~|" nil 0 (standard-co state) state nil)
           (declare (ignore col))
           (mv t nil state)))

(defun rebuild-fn-read-filter (file state)
  (state-global-let*
   ((standard-oi *standard-oi*)
    (standard-co *standard-co*))
   (er-let*
     ((ans
       (acl2-query
        :rebuild
        '("How much of ~x0 do you want to process?"
          :t :all :all :all :query :query :until :until
          :? ("If you answer T or ALL, then the entire file will be ~
               loaded.  If you answer QUERY, then you will be asked ~
               about each command in the file.  If you answer UNTIL, ~
               then you should also type some name after the UNTIL ~
               and we will then proceed to process all of the events ~
               in file until that name has been introduced.  Rebuild ~
               automatically stops if any command causes an error.  ~
               When it stops, it leaves the logical world in the ~
               state it was in immediately before the erroneous ~
               command.  Thus, another way to use rebuild is to get ~
               into the habit of planting (i-am-here) -- or any other ~
               form that causes an error when executed -- and then ~
               using the filter T or ALL when you rebuild."
              :t :all :all :all :query :query :until :until))
        (list (cons #\0 file))
        state)))
     (cond ((eq ans :until)
            (with-infixp-nil
             (read-object *standard-oi* state)))
           (t (value ans))))))

(defun rebuild-fn (file filter filterp dir state)
  (er-let*
      ((filter
        (if filterp
            (value (if (eq filter t) :all filter))
          (rebuild-fn-read-filter file state))))
    (mv-let (erp val state)
      (ld file
          :dir dir
          :standard-co *standard-co*
          :proofs-co *standard-co*
          :ld-skip-proofsp t
          :ld-prompt nil
          :ld-missing-input-ok nil
          :ld-pre-eval-filter filter
          :ld-pre-eval-print nil
          :ld-post-eval-print :command-conventions
          :ld-evisc-tuple (abbrev-evisc-tuple state)
          :ld-error-triples t
          :ld-error-action :return!
          :ld-query-control-alist '((:filter . nil) . t)
          :ld-verbose t)
      (declare (ignore erp val))
      (value t))))

(defmacro rebuild (file &optional (filter 'nil filterp)
                        &key dir)
  `(rebuild-fn ,file ,filter ,filterp ,dir state))

;           The Tall Texas Tale about  BIG-CLOCK

; Like any Lisp system, it may be said, loosely speaking, that ACL2
; typically reads a form, evaluates it in the current state, and
; prints the result.  This read-eval-print activity in ACL2 is done by
; the function ld-fn.  When the user enters ACL2 by invoking (LP),
; ld-fn is called to do the work.

; The read phase of the read-eval-print activity is done with the
; read-object function, which calls the Common Lisp read function.
; This read is influenced by *package*, *readtable*, and *features*,
; as described in acl2.lisp.

; The semantics of an ACL2 read-eval-print cycles is best described
; from the logical point of view via the logic programming paradigm, to
; which we digress momentarily.  In the Lisp paradigm, one thinks
; of an interaction as always being something like

; >  (fact 3) = ?

; wherein a variable free term is evaluated to obtain a suitable
; value, say 6.  In logic programming, as in Baroque or Prolog, one
; can ask a question like:

; ? (fact x) = 6

; i.e. does there exist an x whose factorial is 6?  The system then
; attempts to answer the question and may find one or several values for
; x that does the job, e.g. 3.  In fact, one can even imagine asking

; ? (fact x) = y

; to obtain a variety of values of x and y that satisfy the relation.
; Or might might merely be informed that that, yes, there do exist
; values of x and y satisfying the relation, without being given x and
; y explicitly.

; The point of this digression is merely to mention the well-known
; (but non-Lispish) idea that the input to a computation need not
; always be given entirely in advance of the commencement of a
; computation.  In truth, even in regular Common Lisp, the input is not
; really always given entirely in advance because the characters that
; may appear in *standard-input* or the file system need not be known
; before evaluation commences.  ACL2 employs this ``incompletely
; specified at evaluation commencement'' idea.

; From the logical point of view, an ACL2 ``state'' is any object in
; the logic satisfying the state-p predicate, q.v. in axioms.lisp.
; There is a long comment in axioms.lisp under the heading STATE which
; describes the many fields that a state has.

; At the beginning of any interaction with the top-level ACL2 ld-fn,
; there is a ``partial current state'', which may be partially
; perceived, without side-effect, in Common Lisp, but outside of ACL2,
; by invoking (what-is-the-global-state).  This partial current-state
; includes (a) the names, types, and times of the open input and
; output channels (but not the characters read or written to those
; channels), (b) the symbols in the global table, (c) the t-stack, (d)
; the 32-bit stack, and (e) the file clock.  We say that an object o
; satisfying state-p is ``consistent with the current partial state''
; provided that every fact revealed by (what-is-the-global-state) and
; by examination of the bound globals is true about o.

; In Lisp (as opposed to Prolog) the input form has no explicit free
; variable.  In ACL2, however, one free variable is permitted, and
; this variable, always named STATE, refers, loosely speaking to the
; ``value of the state at the time of input''.  In ACL2, the variable
; STATE includes the input via files and channels.


;                   Common LISP IO

; If we have a Common Lisp system that is connected to an IO system,
; then at each tick of time, the system may (a) print a character,
; byte, or object to any of the open streams, (b) read a character,
; byte, or object from any of the open streams, (c) open a file for
; reading or writing and (c) close an open stream.

; Suppose that old and new are two objects satisfying state-p and that
; we have an implementation of ACL2 in a Common Lisp which is
; connected to an IO system.  We say that old and new are ``IO
; consistent with the Common Lisp IO system's behavior in the time
; period between old and new'' provided that the relationships between
; the various io fields of old and new are just what happened.  For
; example, suppose that old and new are different only in that in new
; on one input character channel one character has been consumed.
; Then that is consistent with a Common Lisp IO system in which the
; stream corresponding to the channel was read to get just one
; character.  As another example, suppose that old and new are
; different only because a file is now on read-files that was not
; there before and file-clock has been ticked twice and the two most
; recent values of the file clock are the open and close time of the
; read file.  Then that is consistent with a Common Lisp IO system in
; which a stream for a file of the read file's name was opened and
; consumed and the characters read were exactly the characters
; associated with the file name in readable-files at the file-clock
; upon open.  This concept needs to be completely and fully spelled
; out, but we believe it is all boring and obvious:  the file clock is
; to keep track of the opening and closing times.  The read-files and
; written-files entries record closing times and contents.  The
; readable-files and input channels entries record characters actually
; consumed.

; In the extremely important degenerate case, old and new are
; consistent with the Common Lisp IO system's behavior over a time
; interval if all the fields of old and new are identical, excepting
; only the global-table, stacks, and big-clock entries, and no IO
; occurred in the time interval.


;                        The ACL2 ld theorem

; Let us suppose, without loss of generality, that run is a function
; of one argument, state, that has been defined by the user, and
; accepted by ACL2.  Let us further suppose that run returns a single
; state value.  (There is no loss of generality here because any
; particular arguments or output value that the user wishes to provide
; or see can be placed in state globals.  For example, one could add
; two to three by defining run as (defun run (state) (f-set-global
; 'foo (+ 2 3)))).  Let us suppose that an ACL2 interaction of the
; form

; ACL2 !> (run state)

; completes.  What is the theorem that describes the relationship
; between the old current partial state and the new current partial
; state?  The theorem is that (a) there exists an object, old, which
; satisfies the predicate statep and an object, new, which also
; satisfies the predicate statep such that old is consistent with the
; partial current state at the time of the input and new is consistent
; with the partial current state at the time of the output (b) new and
; old are IO consistent with the Common Lisp IO system's behavior in
; the time period between the beginning and ending of the evaluation
; (c) new = (trans-eval '(run state) nil old t), and (d) (run old) =
; (trans-eval '(run state) nil old t) except in the big-clock field.

; In the important degenerate case in which no io occurs, this means
; essentially that there exists (in the constructive sense) a
; big-clock entry in old which is ``large enough'' to perform the
; trans-eval of the input form without ``running out of time''.  ACL2
; does not reveal to the user how much ``time'' was required, but
; merely guarantees that there exists a sufficiently large amount of
; time.  In fact, because we ``jump into compiled code'' in
; raw-ev-fncall, we have no way of efficiently keeping track of how
; much time has been used.

; Note that there is no commitment to a uniform value for big-clock
; across all ACL2 interactions.  In particular, there obviously exists
; an infinite sequence of forms, say (fact 1), (fact 2), (fact 3),
; ....  which would require an infinitely increasing series of
; big-clocks.  An ACL2 evaluation effort may fail for a variety of
; reasons, including resource errors and certain design decisions,
; e.g. the detection that a function should not be clobbered because
; there is already a function by that name with a symbol-function
; property.  If evaluation fails, some characters may nevertheless
; have been printed or read and state may have been changed.

(defconst *basic-sweep-error-str*
  "The state back to which we have been asked to roll would contain an ~
   object that is inconsistent with the requested resetting of the ~
   ACL2 known-package-alist.  Logical consistency would be imperiled ~
   if the rollback were undertaken.  Please get rid of pointers to ~
   such objects before attempting such a rollback.~|~%")

(defun sweep-symbol-binding-for-bad-symbol (sym obj deceased-packages state)
  (cond ((symbolp obj)
         (cond ((member-equal (symbol-package-name obj) deceased-packages)
                (er soft "undo consistency check"
                    "~@0In particular, the value of the global ~
                     variable ~x1 contains the symbol ~x2 in package ~
                     ~x3, which we have been asked to remove.   ~
                     Please reset ~x1, as with (assign ~x1 nil)."
                    *basic-sweep-error-str*
                    sym
                    obj
                    (symbol-package-name obj)))
               (t (value nil))))
        ((atom obj) (value nil))
        ((equal obj (w state))
         (value nil))
        (t (er-progn (sweep-symbol-binding-for-bad-symbol
                      sym (car obj)
                      deceased-packages state)
                     (sweep-symbol-binding-for-bad-symbol
                      sym (cdr obj) deceased-packages state)))))

(defun sweep-global-lst (l deceased-packages state)
  (cond ((null l) (value nil))
        (t (er-progn
            (sweep-symbol-binding-for-bad-symbol
             (car l)
             (get-global (car l) state)
             deceased-packages state)
            (sweep-global-lst (cdr l) deceased-packages state)))))

(defun sweep-stack-entry-for-bad-symbol (name i obj deceased-packages state)
  (cond ((symbolp obj)
         (cond ((member-equal (symbol-package-name obj) deceased-packages)
                (er soft "undo consistency check"
                    "~@0In particular, the entry in the ~@1 at ~
                     location ~x2 contains the symbol ~x3 in package ~
                     ~x4, which we have been asked to undo.  Please ~
                     change the ~@1 entry at location ~x2 or ~
                     shrink the ~@1."
                    *basic-sweep-error-str*
                    name
                    i
                    obj
                    (symbol-package-name obj)))
               (t (value nil))))
        ((atom obj) (value nil))
        ((equal obj (w state))
         (value nil))
        (t (er-progn (sweep-stack-entry-for-bad-symbol
                      name i (car obj) deceased-packages state)
                     (sweep-stack-entry-for-bad-symbol
                      name i (cdr obj) deceased-packages state)))))

(defun sweep-t-stack (i deceased-packages state)
  (cond ((> i (t-stack-length state))
         (value nil))
        (t (er-progn
            (sweep-stack-entry-for-bad-symbol
             "t-stack" i (aref-t-stack i state) deceased-packages state)
            (sweep-t-stack (+ 1 i) deceased-packages state)))))

(defun sweep-acl2-oracle (i deceased-packages state)

; A valid measure is (- (len (acl2-oracle state)) if we want to admit this
; function in logic mode, since read-acl2-oracle replaces the acl2-oracle of
; the state with its cdr.

  (mv-let
   (nullp car-oracle state)
   (read-acl2-oracle state)
   (cond (nullp (value nil))
         (t (er-progn
             (sweep-stack-entry-for-bad-symbol
              "acl2-oracle" i car-oracle deceased-packages state)
             (sweep-acl2-oracle (+ 1 i) deceased-packages state))))))

(defun sweep-global-state-for-lisp-objects (deceased-packages state)

; This function sweeps every component of the state represented by
; *the-live-state* to verify that no symbol is contained in a package that we
; are about to delete.  This is sensible before we undo a defpkg, for example,
; which may ``orphan'' some objects held in, say, global variables in the
; state.  We look in the global variables, the t-stack, and acl2-oracle.  If a
; global variable, t-stack entry, or acl2-oracle entry contains such an object,
; we cause an error.  This function is structurally similar to
; what-is-the-global-state in axioms.lisp.

; The components of the state and their disposition are:

; open-input-channels  -  there are no objects in the dynamic channels.
;                         Objects obtained from those channels will be
;                         read into an otherwise ok state.

; open-output-channels -  there are no objects in the dynamic channels

; global-table - the global table is the most likely place we will find
;                bad objects.  However, we know that the value of
;                'current-acl2-world is not bad, because after an undo
;                it is set to a previously approved value.

  (er-progn
   (sweep-global-lst (global-table-cars state) deceased-packages state)


; t-stack - this stack may contain bad objects.

   (sweep-t-stack 0 deceased-packages state)
   (sweep-acl2-oracle 0 deceased-packages state))

; The remaining fields contain no ``static'' objects.  The fields are:
; 32-bit-integer-stack
; big-clock
; idates
; file-clock
; readable-files
; written-files
; read-files
; writeable-files
; list-all-package-names-lst

  )

(defmacro wet (form &rest kwd-args)
  (let* ((book-tail (member-eq :book kwd-args))
         (kwd-args (if book-tail (remove-keyword :book kwd-args) kwd-args))
         (book-form (if book-tail
                        (cond ((null book-tail)
                               nil)
                              ((stringp (cadr book-tail))
                               (list 'include-book (cadr book-tail)))
                              (t (cons 'include-book (cadr book-tail))))
                      '(include-book "misc/wet" :dir :system))))
    `(with-output
      :off (summary event)
      (make-event (mv-let (erp val state)
                          (progn
                           ,@(and book-form (list book-form))
                           (wet! ,form ,@kwd-args))
                          (cond (erp (mv "WET failed!" nil state))
                                (t (value `(value-triple ',val)))))))))

(defmacro disassemble$ (fn &rest args
                           &key (recompile ':default)

; And, in case community book books/misc/disassemble.lisp changes between
; releases:

                           &allow-other-keys)
  `(with-ubt!
    (with-output
     :off (event history summary proof-tree)
     (progn
       (include-book "misc/disassemble" :dir :system :ttags '(:disassemble$))
       (value-triple (disassemble$-fn ,fn ,recompile (list ,@args)))))))

(defmacro near-misses (name)

; This macro is similar in nature to wet and disassemble$, in that it relies on
; including books.  At some point we might share code by adding an autoload
; utility.

  `(with-output
     :off :all
     :on error
     (make-event
      (er-progn
       (include-book "system/event-names" :dir :system)
       (include-book "xdoc/spellcheck" :dir :system)
       (make-event (pprogn
                    (f-put-global 'near-misses-val-crazy-name-used-only-here
                                  (plausible-misspellings ',name)
                                  state)
                    (value '(value-triple nil))))
       (value `(value-triple
                ',(@ near-misses-val-crazy-name-used-only-here)))))))

; Changes made March 9-16, 2009 (after v3-4), for more efficient handling of
; certificates, etc.:

; The Essay on Skip-proofs was redone, and a new Essay on Soundness Threats was
; added, that explain current handling of skip-proofs, redef, etc.  The basic
; idea is that we have eliminated state globals 'skipped-proofsp and
; include-book-alist-state, instead tracking more in the world
; (e.g. include-book-alist-all).  See in particular install-event, which
; handles such matters, and note that maybe-add-command-landmark no longer does
; so.  (We also changed include-book-fn and encapsulate-fn for this purpose.)
; We added state global 'skip-proofs-by-system to help (again, see
; install-event).

; Of course, there were miscellaneous supporting changes, some in comments.  In
; particular, we (about a month later) eliminated chk-certification-worldxxx.
; Also, eval-event-lst now returns an extra element, which can be a natural
; number we can supply to nthcdr to eliminate some expense from our call of
; pkg-names in certify-book-fn.  This value is passed to
; process-embedded-events, and back from it in the case that the caller is
; 'certify-book.

; We also changed checksum usage so that we don't include the expansion-alist
; with the events from the actual book.  For calls of check-sum-obj on event
; lists that support the handling of certificates, we now use only the events
; from the book ev-lst and no longer include events in the expansion-alist.
; Instead, we rely on the checksum of the cert-obj, which is still
; incorporated in the certificate, for ensuring that we have the right
; expansion-alist.  Notice however that this extra security disappears when
; state global 'book-hash-alistp is true.

#-acl2-loop-only
(defun-one-output compiled-function-p! (fn)

; In CMU Lisp, it seems that the symbol-function of every defun'd function
; satisfies compiled-function-p.  Some are #<Interpreted Function ...> and
; others are #<Function ...>.  The following test seems to work.  Fn is assumed
; to be a symbol.

  #+cmu
  (not (eq (type-of (symbol-function fn)) 'eval:interpreted-function))
  #-cmu
  (compiled-function-p (symbol-function fn)))

(defun compile-function (ctx fn0 state)

; Fn0 can either be a symbol, (:raw sym), or (:exec sym).

  (declare (xargs :guard
                  (and (or (symbolp fn0)
                           (and (consp fn0)
                                (member-eq (car fn0) '(:raw :exec))
                                (consp (cdr fn0))
                                (null (cddr fn0))))
                       (state-p state))))
  (let ((wrld (w state))
        (fn (if (consp fn0)
                (cadr fn0)
              fn0)))
    (cond
     ((not (eq (f-get-global 'compiler-enabled state) t))
      (value (er hard ctx
                 "Implementation error: Compile-function called when ~x0."
                 '(not (eq (f-get-global 'compiler-enabled state) t)))))
     ((eq (getpropc fn 'formals t wrld)
          t)
      (er soft ctx
          "~x0 is not a defined function in the current ACL2 world."
          fn))
     (t
      (state-global-let*
       ((trace-specs (f-get-global 'trace-specs state))
        (retrace-p t))
       (prog2$
        #+acl2-loop-only
        nil
        #-acl2-loop-only
        (let ((trace-spec
               (assoc-eq fn (f-get-global 'trace-specs state))))
          (when trace-spec
            (untrace$-fn (list fn) state))
          (let* ((form (cltl-def-from-name fn wrld))
                 (*1*fn (*1*-symbol fn))
                 (raw-only-p  (and (consp fn0) (eq (car fn0) :raw)))
                 (exec-only-p (and (consp fn0) (eq (car fn0) :exec))))
            (cond
             ((not (or exec-only-p
                       (compiled-function-p! fn)))
              (cond (form
                     (eval (make-defun-declare-form fn form))))
              (compile fn)))
            (cond
             ((and (not raw-only-p)
                   (fboundp *1*fn)
                   (not (compiled-function-p! *1*fn)))
              #-acl2-mv-as-values ; may delete this restriction in the future
              (eval
               (make-defun-declare-form
                fn
                (cons 'defun (oneified-def fn wrld))))
              (compile *1*fn)))
            (when trace-spec
              (trace$-fn trace-spec ctx state))))
        (value fn)))))))

#-acl2-loop-only
(defun-one-output tmp-filename (dir suffix)

; Warning: If this function is changed, look at its call in save-gprof.lsp.

; Dir should be a filename in Unix-style syntax, possibly "".  We return a
; filename in Unix-style syntax.

  (let ((pid (and (not (eq (f-get-global 'keep-tmp-files *the-live-state*)
                           :no-pid))
                  (getpid$)))
        (dir (if (and (not (equal dir ""))
                      (not (eql (char dir (1- (length dir)))
                                *directory-separator*)))
                 (concatenate 'string dir *directory-separator-string*)
               dir)))
    (coerce (packn1 (list* dir
                           "TMP"
                           (if pid
                               (if suffix
                                   (list "@" pid "@" suffix)
                                 (list "@" pid "@"))
                             (if suffix
                                 (list suffix)
                               nil))))
            'string)))

(defun keep-tmp-files (state)
  (f-get-global 'keep-tmp-files state))

(defun comp-fn (fns gcl-flg tmp-suffix state)

; Gcl-flg should only be used with GCL, and causes .c and .h files to be left
; around after compilation.

  (declare (xargs :guard (and (state-p state)
                              (or (and (true-listp fns) fns)
                                  (symbolp fns))
                              (stringp tmp-suffix)
                              (not (equal tmp-suffix ""))))
           #+acl2-loop-only
           (ignore tmp-suffix))
  (cond
   ((eql 0 (f-get-global 'ld-level state))
    (pprogn (warning$ 'comp "Comp"
                      "Comp is ignored outside the ACL2 loop.")
            (value nil)))
   #-gcl
   (gcl-flg
    (er soft 'comp
        "Comp-gcl may only be used in GCL implementations."))
   ((not (eq (f-get-global 'compiler-enabled state) t))
    (value nil))
   (t
    (let ((fns (cond
                ((or (and (symbolp fns)
                          (not (eq fns t))
                          (not (eq fns :raw))
                          (not (eq fns :exec))
                          (not (eq fns nil)))
                     (and (consp fns)
                          (member-eq (car fns) '(:raw :exec))
                          (consp (cdr fns))
                          (null (cddr fns))))
                 (list fns))
                (t fns))))
      (cond
       ((and (consp fns)
             (null (cdr fns))
             (not gcl-flg))
        (compile-function 'comp (car fns) state))
       ((null fns)
        (er soft 'comp
            "We do not allow the notion of compiling the empty list of ~
             functions.  Perhaps you meant to do something else."))
       (t
        #+acl2-loop-only
        (value t)
        #-acl2-loop-only
        (state-global-let*
         ((retrace-p t))
         (let ((*package* *package*)
               (dir (or (f-get-global 'tmp-dir state)
                        (f-get-global 'connected-book-directory state)
                        ""))
               (raw-fns nil)
               (exec-fns nil)
               (trace-specs nil))
           (cond
            ((consp fns)
             (dolist (fn fns)
               (cond
                ((and (consp fn)
                      (member-eq (car fn) '(:raw :exec)))
                 (cond ((and (consp (cdr fn))
                             (null (cddr fn))
                             (symbolp (cadr fn)))
                        (cond ((eq (car fn) :raw)
                               (setq raw-fns (cons (cadr fn) raw-fns)))
                              (t ; :exec
                               (setq exec-fns (cons (cadr fn) exec-fns)))))
                       (t
                        (er hard 'comp
                            "Unexpected function specifier, ~x0."
                            fn))))
                ((symbolp fn)
                 (setq raw-fns (cons fn raw-fns))
                 (setq exec-fns (cons fn exec-fns)))
                (t (er hard 'comp
                       "Unexpected function specifier, ~x0."
                       fn)))
               (setq raw-fns (nreverse raw-fns))
               (setq exec-fns (nreverse exec-fns))))
            (t (setq raw-fns fns)
               (setq exec-fns fns)))
           (when (not (eq fns :exec))
             (setq trace-specs
                   (f-get-global 'trace-specs state))
             (untrace$)
             (let ((tmpfile (tmp-filename dir nil)))
               (compile-uncompiled-defuns
                tmpfile
                (if (or (eq fns t)
                        (eq fns :raw))
                    :some
                  raw-fns)
                gcl-flg)))
           (when (not (eq fns :raw))
             (when (and (null trace-specs)
                        (f-get-global 'trace-specs state))
               (setq trace-specs
                     (f-get-global 'trace-specs state))
               (untrace$))
             (let ((tmpfile (tmp-filename dir tmp-suffix)))
               (compile-uncompiled-*1*-defuns
                tmpfile
                (if (member-eq fns '(t :exec))
                    :some
                  exec-fns)
                gcl-flg)))
           (when trace-specs
             (trace$-lst trace-specs 'comp state))
           (value t)))))))))

#-acl2-loop-only
(defmacro comp (fns)
  (declare (ignore fns))
  nil)

#+acl2-loop-only
(defmacro comp (fns)
  `(comp-fn ,fns nil "1" state))

(defmacro comp-gcl (fns)
  `(comp-fn ,fns t "1" state))

(defun scan-past-deeper-event-landmarks (depth wrld)

; We scan down wrld until either it is exhausted or we find a command-landmark
; or we find an event-landmark whose access-event-tuple-depth is depth or less.
; Thus, the world we return is either nil or begins with a command-landmark or
; event-landmark.

  (cond
   ((or (null wrld)
        (and (eq (car (car wrld)) 'command-landmark)
             (eq (cadr (car wrld)) 'global-value)))
    wrld)
   ((and (eq (car (car wrld)) 'event-landmark)
         (eq (cadr (car wrld)) 'global-value))
    (cond
     ((> (access-event-tuple-depth (cddr (car wrld))) depth)
      (scan-past-deeper-event-landmarks depth (cdr wrld)))
     (t wrld)))
   (t (scan-past-deeper-event-landmarks depth (cdr wrld)))))

(defun puffable-encapsulate-p (cddr-car-wrld installed-wrld ntep)

; An encapsulate is puffable if it has an empty signature.  If on the other
; hand it has a non-empty signature and ntep (Non-Trivial-Encapsulate Property)
; is false, then it is not puffable.  The remaining case is that ntep is true
; and the signature is non-empty.  Then the encapsulate is puffable if and only
; if any of its signature's function symbols are have unknown-constraints
; (equivalently, all of them).

  (and (eq (access-event-tuple-type cddr-car-wrld) 'encapsulate)
       (let* ((encap (access-event-tuple-form cddr-car-wrld))
              (signatures (cadr encap))
              (fns (signature-fns signatures)))
         (not (and (consp fns)
                   (or (not ntep) ; don't puff non-trivial encapsulates
                       (mv-let
                         (name x)
                         (constraint-info (car fns) installed-wrld)
                         (declare (ignore name))
                         (unknown-constraints-p x))))))))

(defun puffable-command-blockp (wrld cmd-form ntep installed-wrld)

; Initially, wrld should be the cdr of a world starting at some
; command-landmark.  Cmd-form should be the command-tuple form of that landmark
; (note that it will be nil for the very first command-landmark ever laid down,
; the one with access-command-tuple-number -1).

; This function returns nil except in the following cases.

; (a) Cmd-form is an include-book: return 'include-book.
; (b) Cmd-form is an encapsulate and the first event form in wrld is a puffable
;     encapsulate: return 'encapsulate.
; (c) Cmd-form is neither an include-book nor an encapsulate, and it differs
;     from the first event form in world: return t.

  (cond
   ((or (null wrld)
        (and (eq (car (car wrld)) 'command-landmark)
             (eq (cadr (car wrld)) 'global-value)))
    nil)
   ((and (eq (car (car wrld)) 'event-landmark)
         (eq (cadr (car wrld)) 'global-value))
    (cond ((atom cmd-form) ; perhaps impossible except for first command
           nil)
          ((eq (car cmd-form) 'certify-book)
           'certify-book)
          ((eq (car cmd-form) 'include-book)
           (assert$
            (eq (car (access-event-tuple-form (cddr (car wrld))))
                'include-book)
            'include-book))
          ((eq (car cmd-form) 'encapsulate)
           (and (puffable-encapsulate-p
                 (cddr (car wrld))
                 installed-wrld
                 ntep)
                'encapsulate))
          (t (not (equal cmd-form
                         (access-event-tuple-form (cddr (car wrld))))))))
   (t (puffable-command-blockp (cdr wrld) cmd-form ntep installed-wrld))))

(defun puffable-command-numberp (i state)

; Let i be a legal relative command number for (w state).  We determine whether
; the command at i is puffable.

  (mv-let (flg n)
          (normalize-absolute-command-number
           (relative-to-absolute-command-number i (w state))
           (w state))
          (and (null flg)
               (let ((wrld (lookup-world-index 'command n (w state))))
                 (puffable-command-blockp
                  (cdr wrld)
                  (access-command-tuple-form (cddr (car wrld)))

; We don't puff non-trivial encapsulates with puff*.  See relevant comment in
; puffed-command-sequence.

                  nil
                  (w state))))))

(defun puff-include-book (wrld include-book-alist-entry final-cmds ctx state)

; This function should only be called under puff-fn1; see comments about
; puff-fn1 below.

; We puff an include-book simply by going to the file named by the include-book
; and return the events in it.  Recursive include-books are not flattened here.

  (let ((full-book-name (access-event-tuple-namex (cddr (car wrld)))))
    (cond
     ((assoc-equal full-book-name (table-alist 'puff-included-books (w state)))
      (value final-cmds))
     (t
      (er-progn
       (chk-input-object-file full-book-name ctx state)
       (chk-book-name full-book-name full-book-name ctx state)
       (er-let*
           ((ev-lst (read-object-file full-book-name ctx state))
            (cert-obj (chk-certificate-file
                       full-book-name
                       nil
                       'puff
                       ctx
                       state
                       '((:uncertified-okp . t)
                         (:defaxioms-okp t)
                         (:skip-proofs-okp t))
                       nil)))
         (let* ((old-book-hash

; The assoc-equal just below is of the form (full-book-name user-book-name
; familiar-name cert-annotations . book-hash).

                 (cddddr (assoc-equal full-book-name
                                      (global-val 'include-book-alist
                                                  (w state)))))

; We include the expansion-alist and cert-data only if the book appears to be
; certified.

                (expansion-alist
                 (and old-book-hash
                      cert-obj
                      (access cert-obj cert-obj :expansion-alist)))
                (cert-data
                 (and old-book-hash
                      cert-obj
                      (access cert-obj cert-obj :cert-data)))
                (cmds (and cert-obj
                           (access cert-obj cert-obj :cmds))))
           (er-let* ((ev-lst-book-hash
                      (if old-book-hash ; otherwise, don't care
                          (book-hash old-book-hash full-book-name cmds
                                     expansion-alist cert-data ev-lst state)
                        (value nil))))
             (cond
              ((and old-book-hash
                    (not (equal ev-lst-book-hash old-book-hash)))

; It is possible that the book is no longer certified.  It seems possible that
; the reason the book-hash has changed is only that somehow expansion-alist or
; cert-data was non-nil after certification but is now viewed as nil.  In that
; case, perhaps the message below is a bit misleading, since perhaps the .cert
; file has been modified rather than the book.  But that's unlikely, and this
; function is supporting the lightly-supported puff operation, so we can live
; with that, especially given the "weasel word" below, "presumably".

               (er soft ctx
                   "When the certified book ~x0 was included, its book-hash ~
                    was ~x1.  The book-hash for ~x0 is now ~x2.  The book has ~
                    thus presumably been modified since it was last included ~
                    and we cannot now recover the events that created the ~
                    current logical world."
                   full-book-name
                   old-book-hash
                   ev-lst-book-hash))
              (t (let ((fixed-cmds
                        (append
                         cmds
                         (cons (assert$

; We want to execute the in-package here.  But we don't need to restore the
; package, as that is done with a state-global-let* binding in puff-fn1.

                                (and (consp (car ev-lst))
                                     (eq (caar ev-lst) 'in-package))
                                (car ev-lst))
                               (subst-by-position expansion-alist
                                                  (cdr ev-lst)
                                                  1)))))
                   (value
                    `((ld

; We are comfortable setting the cbd here because when ld returns, it will set
; the cbd to its starting value (because ld calls ld-fn with bind-flg t).

                       '((set-cbd
                          ,(directory-of-absolute-pathname
                            full-book-name))
                         ,@fixed-cmds
                         ,@(and include-book-alist-entry ; always true?
                                `((table puff-included-books
                                         ,full-book-name
                                         ',include-book-alist-entry))))
                       :ld-error-action :error)
                      (maybe-install-acl2-defaults-table
                       ',(table-alist 'acl2-defaults-table wrld)
                       state)
                      ,@final-cmds)))))))))))))

(defun puff-command-block1 (wrld immediate ans ctx state)

; Wrld is a world that starts just after a command landmark.  We scan down to
; the next command landmark and return the list of events in this command
; block.  We replace every encapsulate and include-book by the events in its
; body or file, which exposes the LOCAL events that are not actually part of
; wrld now.  However, we do not recursively flatten the encapsulates and
; include-books that are exposed by this flattening.

; Immediate is non-nil when we are puffing a certify-book command (immediate =
; 'certify-book) or encapsulate command (immediate = 'encapsulate).  In the
; certify-book case, if the first event encountered is an include-book of the
; same book, we puff that include-book command.  In the encapsulate case, we
; expect the first event encountered to be an encapsulate event, and we use its
; event-tuple instead of the command-tuple so that make-event expansions are
; used, as is the case for other resulting from :puff.

  (cond
   ((or (null wrld)
        (and (eq (car (car wrld)) 'command-landmark)
             (eq (cadr (car wrld)) 'global-value)))
    (value ans))
   ((and (eq (car (car wrld)) 'event-landmark)
         (eq (cadr (car wrld)) 'global-value))
    (let* ((event-tuple (cddr (car wrld)))
           (event-type (access-event-tuple-type event-tuple))
           (include-book-alist-entry
            (car (global-val 'include-book-alist wrld))))
      (cond
       ((and (eq immediate 'certify-book)
             (eq event-type 'include-book)
             (equal (car include-book-alist-entry)
                    (access-event-tuple-namex event-tuple)))

; The include-book here represents the evaluation of all events after the final
; local event in the book common to the certify-book command and the current
; include-book event landmark.  We ignore all events in the current world that
; precede that final local event, instead doing a direct collection of all
; events in the book.

        (puff-include-book wrld include-book-alist-entry ans ctx state))
       ((eq immediate 'encapsulate)

; In the case of an encapsulate event, flattening means to do the body of the
; encapsulate -- including the LOCAL events.  Note that this destroys the sense
; of those encapsulates that introduce constrained functions!  After flattening
; the constrained functions are defined as their witnesses!  We cannot recover
; the LOCAL events by a scan through wrld since they are not in wrld.  We must
; instead re-execute the body of the encapsulate.  Therefore, we just return
; the body of the encapsulate.

        (assert$
         (eq event-type 'encapsulate)
         (value (append (cddr (access-event-tuple-form (cddr (car wrld))))
                        (cons `(maybe-install-acl2-defaults-table
                                ',(table-alist 'acl2-defaults-table wrld)
                                state)
                              ans)))))
       (t
        (puff-command-block1
         (cond ((member-eq event-type
                           '(encapsulate include-book))
                (scan-past-deeper-event-landmarks
                 (access-event-tuple-depth event-tuple)
                 (cdr wrld)))
               (t (cdr wrld)))
         nil ; already found the immediate match
         (cons (access-event-tuple-form event-tuple)
               ans)
         ctx state)))))
   (t (puff-command-block1 (cdr wrld) immediate ans ctx state))))

(defun puff-command-block (cmd-type wrld final-cmds ctx state)

; Wrld is a world that starts just after a command landmark.  We scan down to
; the next command landmark and return the list of events in this command
; block.  We replace every encapsulate and include-book by the events in its
; body or file, which exposes the LOCAL events that are not actually part of
; wrld now.  However, we do not recursively flatten the encapsulates and
; include-books that are exposed by this flattening.

  (case cmd-type
    (encapsulate (puff-command-block1 wrld 'encapsulate final-cmds ctx state))
    (include-book (puff-include-book wrld
                                     (car (global-val 'include-book-alist
                                                      wrld))
                                     final-cmds ctx state))
    (certify-book (puff-command-block1 wrld 'certify-book final-cmds ctx state))
    (otherwise    (puff-command-block1 wrld nil final-cmds ctx state))))

(defun commands-back-to-1 (wrld1 wrld2 cbd cbd0 ans)

; Wrld2 is a tail of wrld1.  Each starts with a command-landmark initially.  We
; collect all the non-eviscerated commands back to (but not including) the one
; at wrld2, in reverse order.  The idea is to evaluate the resulting list of
; commands on top of wrld2 to get a world that is roughly equivalent to wrld1.

; To understand the algorithm here, consider the following example of wrld1: it
; starts with wrld2 and is following by the two include-book commands below,
; each stored with the indicated cbd.

;   wrld2
;   (include-book "book1") ; cbd "cbd1"
;   (include-book "book2") ; cbd "cbd2"

; When we puff, we generate the commands shown below.  Thus "cbd" is the
; current cbd if wrld1 is the currently installed world, and otherwise it is
; the cbd of the next command.  The blank lines show accumulating into ans on
; successive calls of commands-back-to-1.

;   <wrld2>

;   (set-cbd "cbd1")

;   (include-book "book1") ; cbd "cbd1" in the command tuple
;   (set-cbd "cbd2")

;   (include-book "book2") ; cbd "cbd2" in the command tuple
;   (set-cbd "cbd") ; where "cbd" is the cbd we started with

;   <post-wrld1>

; However, if cbd1 is the same as the cbd in place in wrld2 when the first
; include-book was executed, then we can omit (set-cbd "cbd1").  Similarly, we
; can omit (set-cbd "cbd2") if "cbd1" and "cbd2" are equal.  And finally, we
; can omit the final (set-cbd "cbd") if "cbd2" and "cbd" are equal.

; We carry out this optimization by passing cbd as the cbd to be in place after
; wrld1.  At the top level, this is the current cbd.

  (cond
   ((equal wrld1 wrld2)
    (assert$ (and (eq (car (car wrld1)) 'command-landmark)
                  (eq (cadr (car wrld1)) 'global-value))
             (if (equal cbd cbd0)
                 ans
               (cons `(set-cbd ,cbd) ans))))
   ((and (eq (car (car wrld1)) 'command-landmark)
         (eq (cadr (car wrld1)) 'global-value))
    (let* ((next-cbd (access-command-tuple-cbd (cddr (car wrld1))))
           (ans

; Possibly set the cbd for the top of the current value of ans.  Except: if ans
; is nil, then set the cbd to the value of formal parameter cbd, which is the
; cbd for the next command after wrld1.

            (if (equal cbd next-cbd)
                ans
              (cons `(set-cbd ,cbd) ans))))
      (commands-back-to-1
       (cdr wrld1) wrld2 next-cbd cbd0
       (cons (access-command-tuple-form (cddr (car wrld1)))
             ans))))
   (t (commands-back-to-1 (cdr wrld1) wrld2 cbd cbd0 ans))))

(defun commands-back-to (wrld1 wrld2 state)

; Wrld2 is a tail of wrld1.  See commands-back-to-1 for more explanation.

  (let ((cbd (f-get-global 'connected-book-directory state)))
    (commands-back-to-1
     wrld1 wrld2 cbd cbd
     (cond ((equal cbd (access-command-tuple-cbd (cddr (car wrld1))))
            nil)
           (t (list `(set-cbd ,cbd)))))))

(defun puffed-command-sequence (cd ctx wrld state)

; Cd is a command descriptor.  We puff up the command at cd, into the list of
; immediate subevents, and then append to that list the commands in wrld that
; chronologically followed cd.

  (er-let* ((cmd-wrld (er-decode-cd cd wrld ctx state)))
    (let ((cmd-type (puffable-command-blockp
                     (cdr cmd-wrld)
                     (access-command-tuple-form (cddr (car cmd-wrld)))

; A non-trivial encapsulate is puffabble by :puff but not by :puff*.  There are
; two reasons why we are nervous about puffing non-trivial encapsulates.  One
; reason is that this will mess up the recording of constraints, in particular
; for later functional-instantiation.  The other is that in a non-trivial
; encapsulate from a book, local definitions of the signature functions may be
; elided due to the use of make-event, in which case puffing will fail.  In
; this latter case the user has a much better chance of understanding the error
; when using :puff than when using :puff*.  (Arguably, it's not really more
; difficult when using puff* with a non-nil optional argument; but let's keep
; things simple.)

; For both of these reasons, it seems best that if one wishes to puff a
; non-trivial encapsulate, one should use :puff directly on that form, rather
; than having the puffing happen rather invisibly under :puff*.

                     (eq ctx :puff)
                     (w state)))
          (final-cmds (commands-back-to wrld cmd-wrld state)))
      (cond
       (cmd-type
        (puff-command-block cmd-type

; Usually (cdr cmd-wrld) will start with an event-landmark, but not always; for
; example, a command-index is possible.  So we scan to the next event.

                            (scan-to-event (cdr cmd-wrld))
                            final-cmds ctx state))
       (t (er soft ctx
              "The command at ~x0, namely ~X12, cannot be puffed.  See :DOC ~
               puff."
              cd
              (access-command-tuple-form (cddr (car cmd-wrld)))
;;; (evisc-tuple 2 3 nil nil)
              '(nil 2 3 nil)))))))

(defun ld-read-eval-print-simple (state)

; This is a simplified version of ld-read-eval-print to be executed under
; ld-simple, which doesn't mess with ld-level or much else, in support of :puff
; and :puff*.  It just reads, evals, and prints.  It doesn't even print the
; prompt, it's oblivious to being inside verify, and it ignores
; ld-pre-eval-filter.  For other simplifications, compare this code with the
; code for ld-read-eval-print.

  (mv-let
   (eofp erp keyp form state)
   (ld-read-command state)
   (declare (ignore keyp))
   (cond
    (eofp (mv :return :eof state))
    (erp (ld-return-error state))
    (t (pprogn
        (f-put-global 'last-make-event-expansion nil state)
        (let* ((old-wrld (w state))
               (old-default-defun-mode
                (default-defun-mode old-wrld)))
          (mv-let
           (error-flg trans-ans state)
           (mv-let (error-flg trans-ans state)
                   (if (raw-mode-p state)
                       (acl2-raw-eval form state)
                     (trans-eval-default-warning form 'top-level state t))

; If error-flg is non-nil, trans-ans is (stobjs-out . valx).

                   (cond
                    (error-flg (mv t nil state))
                    ((and (ld-error-triples state)
                          (equal (car trans-ans) *error-triple-sig*)
                          (car (cdr trans-ans)))
                     (mv t nil state))
                    (t (er-progn
                        (maybe-add-command-landmark
                         old-wrld
                         old-default-defun-mode
                         form
                         trans-ans state)
                        (mv nil trans-ans state)))))

; If error-flg is non-nil, trans-ans is (stobjs-out . valx) and we know
; that valx is not an erroneous error triple if we're paying attention to
; error triples.

; The code inside the revert-world-on-error arranges to revert if either
; trans-eval returns an error, or the value is to be thought of as an
; error triple and it signals an error.  Error-flg, now, is set to t
; iff we reverted.

           (cond
            (error-flg (ld-return-error state))
            ((and (equal (car trans-ans) *error-triple-sig*)
                  (eq (cadr (cdr trans-ans)) :q))
             (mv :return :exit state))
            ((and (ld-error-triples state)
                  (equal (car trans-ans) *error-triple-sig*)
                  (let ((val (cadr (cdr trans-ans))))
                    (and (consp val)
                         (eq (car val) :stop-ld))))
             (mv :return
                 (list* :stop-ld
                        (f-get-global 'ld-level state)
                        (cdr (cadr (cdr trans-ans))))
                 state))
            (t (mv :continue nil state))))))))))

(defun ld-loop-simple (state)
  (mv-let
   (signal val state)
   (ld-read-eval-print-simple state)
   (cond ((eq signal :continue)
          (ld-loop-simple state))
         ((eq signal :return)
          (value val))
         (t (mv t nil state)))))

(defun ld-simple (forms state)

; This is a considerable simplification of ld-fn (and ld-fn0, ld-fn1,
; ld-fn-body, ld-loop, and especially ld-read-eval-print), which doesn't
; traffic in many of the bells and whistles of ld, for example, the ld-level.
; Any ld specials of interest to the user can be bound by state-global-let*
; before calling this function.  We introduced this function after Version_7.1
; while improving :puff (which this function now supports), in order to avoid
; thinking about the complex #-acl2-loop-only code in ld-fn0.

  (state-global-let* ((standard-oi forms)
                      (ld-skip-proofsp 'include-book-with-locals)
                      (ld-verbose nil)
                      (ld-prompt nil)
                      (ld-missing-input-ok nil)
                      (ld-pre-eval-filter :all)
                      (ld-pre-eval-print :never)
                      (ld-post-eval-print nil)
                      (ld-error-triples t)
                      (ld-error-action :error)
                      (ld-query-control-alist
                       (cons '(:redef :y)
                             (ld-query-control-alist state))))
                     (ld-loop-simple state)))

(defun puff-fn1 (cd ctx state)

; This function is essentially :puff except that it does no printing.
; It returns a pair, (i . j), where i and j are the relative command numbers
; delineating the region inserted by the puff.  In particular, cd points to
; the command with relative command number i, that command got puffed up,
; and the new commands have the numbers i through j, inclusive.

  (revert-world-on-error
   (state-global-let*
    ((current-package ; See comment about this binding in puff-include-book.
      (current-package state))
     (modifying-include-book-dir-alist

; The Essay on Include-book-dir-alist explains that the above state global must
; be t in order to set the include-book-dir!-table or the
; :include-book-dir-alist field of the acl2-defaults-table.  The idea is to
; enforce the rule that these are used for the include-book-dir-alist when in
; the ACL2 loop, but state globals 'raw-include-book-dir-alist and
; 'raw-include-book-dir!-alist are used instead when in raw Lisp (see for
; example change-include-book-dir).  Without binding
; modifying-include-book-dir-alist here, we will get an error when replaying an
; event of the form (table acl2-defaults-table :include-book-dir-alist ...).

; But such an error is not necessary, since there is no danger that we are in
; raw Lisp here.  That is because we are (presumably) evaluating puff or puff*
; in the loop rather than when loading a book's compiled file, since puff and
; puff* are not embedded event forms.  (Note that make-event is not legal
; inside a book except with a check-expansion argument that is used as the
; expansion.)  Now, with raw mode one can in principle call all sorts of ACL2
; system functions in raw Lisp that we never intended to be called there -- but
; that requires a trust tag, so it's not our problem!

      t))
    (let ((wrld (w state)))
      (er-let* ((cmd-wrld (er-decode-cd cd wrld ctx state)))
        (cond ((<= (access-command-tuple-number (cddar cmd-wrld))
                   (access command-number-baseline-info
                           (global-val 'command-number-baseline-info wrld)
                           :current))

; See the similar comment in ubt?-ubu?-fn.

               (cond
                ((<= (access-command-tuple-number (cddar cmd-wrld))
                     (access command-number-baseline-info
                             (global-val 'command-number-baseline-info wrld)
                             :original))
                 (er soft ctx
                     "Can't puff a command within the system initialization."))
                (t
                 (er soft ctx
                     "Can't puff a command within prehistory.  See :DOC ~
                     reset-prehistory."))))
              (t
               (er-let*
                   ((cmds (puffed-command-sequence cd ctx wrld state)))
                 (let* ((pred-wrld (scan-to-command (cdr cmd-wrld)))
                        (i (absolute-to-relative-command-number
                            (max-absolute-command-number cmd-wrld)
                            (w state)))
                        (k (- (absolute-to-relative-command-number
                               (max-absolute-command-number (w state))
                               (w state))
                              i)))
                   (pprogn
                    (set-w 'retraction pred-wrld state)
                    (er-progn
                     (state-global-let*
                      ((guard-checking-on t)) ; agree with include-book
                      (ld-simple cmds state))
                     (value (cons i
                                  (- (absolute-to-relative-command-number
                                      (max-absolute-command-number (w state))
                                      (w state))
                                     k))))))))))))))

(defun puff-report (caller new-cd1 new-cd2 cd state)
  (cond ((eql new-cd1 (1+ new-cd2))
         (pprogn (io? history nil state
                      (caller cd)
                      (fms "Note: ~x0 is complete, but no events were ~
                            executed under the given command descriptor, ~
                            ~x1.~|"
                           (list (cons #\0 caller)
                                 (cons #\1 cd))
                           (standard-co state) state nil))
                 (value :invisible)))
        (t (pcs-fn new-cd1 new-cd2 t state))))

(defun puff-fn (cd state)
  (er-let* ((pair (puff-fn1 cd :puff state)))
           (puff-report :puff (car pair) (cdr pair) cd state)))

(defun puff*-fn11 (ptr k i j state)

; If there is a command whose relative command number, n, is i<=n<=j, then we
; puff the command with the smallest such n.  Then, we iterate, over the
; interval [ptr, max-k], where max is the maximum relative command number in
; the puffed world.  This function must be protected with
; revert-world-on-error.

  (cond
   ((> i j) (value (cons ptr j)))
   ((puffable-command-numberp i state)
    (mv-let
     (erp val state)
     (puff-fn1 i :puff* state)
     (declare (ignore val))
     (cond
      (erp ; See puff* for how this value is used.
       (mv erp (cons i (cons ptr j)) state))
      (t (puff*-fn11 ptr k
                     ptr (- (absolute-to-relative-command-number
                             (max-absolute-command-number (w state))
                             (w state))
                            k)
                     state)))))
   (t (puff*-fn11 ptr k (1+ i) j state))))

(defun puff*-fn1 (ptr k state)

; Ptr is a relative command number.  K is an integer.  Let max be the maximum
; relative command number in (w state).  We are to recursively puff all the
; commands whose relative command numbers lie between ptr and max-k,
; inclusively.  Thus, for example, if ptr is 12, max is 21 and k is 2, we are
; to puff all the commands that lie in the interval [12, 19].  Observe that
; this means we leave the last k commands of (w state) unpuffed.  Observe that
; every time we puff a command in the interval, max grows (or stays fixed) and
; the width of the region to be puffed grows (weakly).  See the comment in
; puff*-fn for an example.

; We therefore find the first command (the command with the smallest number) in
; the region that is puffable, we puff it, and we iterate.  We stop when no
; command in the region is puffable.  This function uses
; revert-world-on-error because it is possible that the attempt to puff some
; command will cause an error (e.g., because some book's book-hash no longer
; agrees with include-book-alist).

; At one time we called revert-world-on-error here.  But we expect this
; function to be called at the top level on behalf of :puff*, where normally
; the world is reverted upon error anyhow.  Even if not, the
; revert-world-on-error called in puff-fn1 will avoid corruption of the logical
; world.

  (puff*-fn11 ptr k
              ptr
              (- (absolute-to-relative-command-number
                  (max-absolute-command-number (w state))
                  (w state))
                 k)
              state))

(defun puff*-fn (cd state)
  (let ((wrld (w state)))
    (er-let* ((cmd-wrld (er-decode-cd cd wrld :puff* state)))
             (cond ((<= (access-command-tuple-number (cddar cmd-wrld))
                        (access command-number-baseline-info
                                (global-val 'command-number-baseline-info wrld)
                                :current))

; See the similar comment in ubt?-ubu?-fn.

                    (cond
                     ((<= (access-command-tuple-number (cddar cmd-wrld))
                          (access command-number-baseline-info
                                  (global-val 'command-number-baseline-info wrld)
                                  :original))
                      (er soft :puff*
                          "Can't puff* a command within the system ~
                           initialization."))
                     (t
                      (er soft :puff*
                          "Can't puff* a command within prehistory.  See :DOC ~
                           reset-prehistory."))))
                   (t
                    (let* ((mx (absolute-to-relative-command-number
                                (max-absolute-command-number wrld)
                                wrld))
                           (ptr (absolute-to-relative-command-number
                                 (max-absolute-command-number cmd-wrld)
                                 wrld))
                           (k (- mx ptr)))
                      (er-let*
                       ((pair (puff*-fn1 ptr k state)))

; The difference between puff and puff* is that puff* iterates puff across the
; region generated by the first puff until there are no more commands that are
; puffable.  Before continuing, we illustrate how we determine the bounds of
; the region in question.  We bound the region with relative command numbers.
; Suppose we are asked to puff* cd, where cd points to relative command number
; 12 below.

; 12   cmd1   ; ptr = 12 = the relative command number indicated by cd
; 13   cmd2
; 14   cmd3   ; mx = latest command

; Then mx, above, will be 14 and ptr will be 12.  Observe that there are two
; commands then that are not part of the region to be puffed, namely commands
; 13 and 14.  Now after puffing once, we will have something like:

; 12   cmd1a
; 13   cmd1b
; ...
; 19   cmd1h
; 20   cmd2
; 21   cmd3

; Observe that the new max command number is 21.  The region to be recursively
; puffed now lies between 12 and 19, inclusive.  The last two commands, now
; numbered 20 and 21, are outside the region.

; Let k be (- mx ptr), i.e., 2 in this example and, in general, the number of
; commands not in the region.  Then in general we should recursively puff
; commands whose numbers are between ptr and (- max k), where max is the
; current maximum relative command number, inclusive.  Initially this region
; contains just one command, the one we are to puff first.  ;

                      (puff-report :puff* (car pair) (cdr pair) cd
                                   state))))))))

(defmacro puff (cd)
  `(puff-fn ,cd state))

(defmacro puff* (cd &optional no-error)
  (declare (xargs :guard (booleanp no-error))) ; avoid variable capture
  `(let ((cd ,cd) (no-error ,no-error))
     (mv-let (erp val state)
             (puff*-fn cd state)
             (cond ((and no-error
                         erp
                         (consp val)
                         (consp (cdr val))
                         (natp (car val))
                         (natp (cadr val))
                         (natp (cddr val)))
                    (pprogn
                     (warning$ 'puff* "Puff*"
                               "Puff* did not complete: Failed at ~x0."
                               (car val))
                     (er-progn
                      (puff-report :puff* (cadr val) (cddr val) cd
                                   state)
                      (value (list :incomplete :at-command (car val))))))
                   (t (mv erp val state))))))

(defmacro mini-proveall nil

; ACL2 (a)>:mini-proveall

; will change the default-defun-mode to :logic and do a short proveall.  The
; final defun-mode will be :logic.

  '(ld
    '(:logic

; We start with a nice example of forcing, involving primitive fns.

      (thm (implies (and (true-listp x)
                         (true-listp y))
                    (equal (revappend (append x y) z)
                           (revappend y (revappend x z)))))
      (defun app (x y)
        (if (consp x)
            (cons (car x) (app (cdr x) y))
            y))
      (defthm assoc-of-app
        (equal (app (app a b) c) (app a (app b c))))
      (defun rev (x)
        (if (consp x)
            (app (rev (cdr x)) (cons (car x) nil))
            nil))
      (defthm true-listp-rev
        (true-listp (rev x))
        :rule-classes (:REWRITE :GENERALIZE))

; Here we test the proof-builder using the same theorem as the one that
; follows (but not storing it as a :rewrite rule).

      (defthm rev-app-proof-builder
        (equal (rev (app a b)) (app (rev b) (rev a)))
        :rule-classes nil
        :instructions
        (:induct :bash :induct :bash :split (:dv 1)
                 :x :nx (:dv 1)
                 :x :top :s :bash (:dive 1 1)
                 := (:drop 2)
                 :top :bash))
      (defthm rev-app
        (equal (rev (app a b)) (app (rev b) (rev a))))
      (defthm rev-rev
        (implies (true-listp x) (equal (rev (rev x)) x)))

;    The following events are the big example in deflabel equivalence.

      (encapsulate (((lt * *) => *))
                   (local (defun lt (x y) (declare (ignore x y)) nil))
                   (defthm lt-non-symmetric (implies (lt x y) (not (lt y x)))))

      (defun insert (x lst)
        (cond ((atom lst) (list x))
              ((lt x (car lst)) (cons x lst))
              (t (cons (car lst) (insert x (cdr lst))))))

      (defun insert-sort (lst)
        (cond ((atom lst) nil)
              (t (insert (car lst) (insert-sort (cdr lst))))))

      (defun del (x lst)
        (cond ((atom lst) nil)
              ((equal x (car lst)) (cdr lst))
              (t (cons (car lst) (del x (cdr lst))))))

      (defun mem (x lst)
        (cond ((atom lst) nil)
              ((equal x (car lst)) t)
              (t (mem x (cdr lst)))))

      (defun perm (lst1 lst2)
        (cond ((atom lst1) (atom lst2))
              ((mem (car lst1) lst2)
               (perm (cdr lst1) (del (car lst1) lst2)))
              (t nil)))

      (defthm perm-reflexive
        (perm x x))

      (defthm perm-cons
        (implies (mem a x)
                 (equal (perm x (cons a y))
                        (perm (del a x) y)))
        :hints (("Goal" :induct (perm x y))))

      (defthm perm-symmetric
        (implies (perm x y) (perm y x)))

      (defthm mem-del
        (implies (mem a (del b x)) (mem a x))
        :rule-classes ((:rewrite :match-free :once)))

      (defthm perm-mem
        (implies (and (perm x y)
                      (mem a x))
                 (mem a y))
        :rule-classes ((:rewrite :match-free :once)))

      (defthm mem-del2
        (implies (and (mem a x)
                      (not (equal a b)))
                 (mem a (del b x))))

      (defthm comm-del
        (equal (del a (del b x)) (del b (del a x))))

      (defthm perm-del
        (implies (perm x y)
                 (perm (del a x) (del a y))))

      (defthm perm-transitive
        (implies (and (perm x y) (perm y z)) (perm x z))
        :rule-classes ((:rewrite :match-free :once)))

      (defequiv perm)

      (in-theory (disable perm perm-reflexive perm-symmetric perm-transitive))

      (defcong perm perm (cons x y) 2)

      (defcong perm iff (mem x y) 2)

      (defthm atom-perm
        (implies (not (consp x)) (perm x nil))
        :rule-classes :forward-chaining
        :hints (("Goal" :in-theory (enable perm))))

      (defthm insert-is-cons
        (perm (insert a x) (cons a x)))

      (defthm insert-sort-is-id
        (perm (insert-sort x) x))

      (defcong perm perm (app x y) 2)

      (defthm app-cons
        (perm (app a (cons b c)) (cons b (app a c))))

      (defthm app-commutes
        (perm (app a b) (app b a)))

      (defcong perm perm (app x y) 1 :hints (("Goal" :induct (app y x))))

      (defthm rev-is-id (perm (rev x) x))

      (defun == (x y)
        (if (consp x)
            (if (consp y)
                (and (equal (car x) (car y))
                     (== (cdr x) (cdr y)))
                nil)
            (not (consp y))))

      (defthm ==-symmetric (== x x))

      (defthm ==-reflexive (implies (== x y) (== y x)))

      (defequiv ==)

      (in-theory (disable ==-symmetric ==-reflexive))

      (defcong == == (cons x y) 2)

      (defcong == iff (consp x) 1)

      (defcong == == (app x y) 2)

      (defcong == == (app x y) 1)

      (defthm rev-rev-again (== (rev (rev x)) x))

; This next block tests forcing.

      (defun ends-in-a-0 (x)
        (declare (xargs :guard t))
        (if (consp x) (ends-in-a-0 (cdr x)) (equal x 0)))

      (defun app0 (x y)
        (declare (xargs :guard (ends-in-a-0 x)))
        (if (ends-in-a-0 x)
            (if (equal x 0) y (cons (car x) (app0 (cdr x) y)))
            'default))

      (defun rev0 (x)
        (declare (xargs :guard (ends-in-a-0 x)))
        (if (ends-in-a-0 x)
            (if (equal x 0) 0 (app0 (rev0 (cdr x)) (cons (car x) 0)))
            'default))

      (defthm app0-right-id
        (implies (force (ends-in-a-0 x)) (equal (app0 x 0) x)))

      (defun ends-in-a-zero (x) (ends-in-a-0 x))

      (defthm ends-in-a-zero-app0
        (implies (force (ends-in-a-zero x)) (ends-in-a-0 (app0 x (cons y 0)))))

      (in-theory (disable ends-in-a-zero))

; The following theorem causes two forcing rounds.  In the first, there
; are three goals, all variants of one another.  An inductive proof of one
; of them is done and generates the second forcing round.

      (defthm force-test
        (and (implies (ends-in-a-0 x) (equal (app0 (rev0 x) 0) (rev0 x)))
             (implies (ends-in-a-0 y) (equal (app0 (rev0 y) 0) (rev0 y)))
             (implies (ends-in-a-0 z) (equal (app0 (rev0 z) 0) (rev0 z))))
        :hints (("[2]Goal" :in-theory (enable ends-in-a-zero))))

; This defun does a lot of proving for both termination and guard verification.

      (defun proper-cons-nest-p (x)
        (declare (xargs :guard (pseudo-termp x)))
        (cond ((symbolp x) nil)
              ((fquotep x) (true-listp (cadr x)))
              ((eq (ffn-symb x) 'cons)
               (proper-cons-nest-p (fargn x 2)))
              (t nil)))

; This defthm has two forcing rounds and is very realistic.

      (defthm ordered-symbol-alistp-remove1-assoc-eq-test
        (implies (and (ordered-symbol-alistp l)
                      (symbolp key)
                      (assoc-eq key l))
                 (ordered-symbol-alistp (remove1-assoc-eq key l)))
        :hints (("Goal"
                 :in-theory (disable ordered-symbol-alistp-remove1-assoc-eq))))

      (value-triple "Mini-proveall completed successfully.")

      )
    :ld-skip-proofsp nil
    :ld-redefinition-action nil
    :ld-pre-eval-print t
    :ld-error-action :return!))

(defmacro set-guard-checking (flg)
  (declare (xargs :guard
                  (let ((flg (if (and (consp flg)
                                      (eq (car flg) 'quote)
                                      (consp (cdr flg)))
                                 (cadr flg)
                               flg)))
                    (member-eq flg *guard-checking-values*))))
  `(let ((current-flg (f-get-global 'guard-checking-on state))
         (flg ,(if (and (consp flg) (eq (car flg) 'quote) (consp (cdr flg)))
                   (cadr flg)
                 flg)))
     (cond
      ((and (raw-mode-p state) flg)
       (er soft 'set-guard-checking
           "It is illegal (and anyhow, would be useless) to attempt to modify ~
            guard checking while in raw mode, since guards are not checked in ~
            raw mode."))
      ((eq flg current-flg)
       (pprogn
        (fms "Guard-checking-on already has value ~x0.~%~%"
             (list (cons #\0 flg))
             (standard-co state) state nil)
        (value :invisible)))
      ((null flg)
       (pprogn (f-put-global 'guard-checking-on nil state)
               (fms "Masking guard violations but still checking guards ~
                     except for self-recursive calls.  To avoid guard ~
                     checking entirely, :SET-GUARD-CHECKING :NONE.  See :DOC ~
                     set-guard-checking.~%~%"
                    nil (standard-co state) state nil)
               (value :invisible)))
      ((eq flg :none)
       (pprogn (f-put-global 'guard-checking-on :none state)
               (fms "Turning off guard checking entirely.  To allow execution ~
                     in raw Lisp for functions with guards other than T, ~
                     while continuing to mask guard violations, ~
                     :SET-GUARD-CHECKING NIL.  See :DOC ~
                     set-guard-checking.~%~%"
                    nil (standard-co state) state nil)
               (value :invisible)))
      (t (pprogn
          (f-put-global 'guard-checking-on flg state)
          (assert$ (and flg (not (eq flg current-flg)))
                   (cond ((member-eq current-flg '(nil :none))
                          (fms "Turning guard checking on, value ~x0.~%~%"
                               (list (cons #\0 flg))
                               (standard-co state) state nil))
                         (t
                          (fms "Leaving guard checking on, but changing value ~
                                to ~x0.~%~%"
                               (list (cons #\0 flg))
                               (standard-co state) state nil))))
          (value :invisible))))))

(defmacro get-guard-checking ()
  `(f-get-global 'guard-checking-on state))

; Next: dmr

(defun dmr-stop-fn (state)
  (declare (xargs :guard (state-p state)))
  (let ((dmrp (f-get-global 'dmrp state)))
    (cond (dmrp #-acl2-loop-only
                (dmr-stop-fn-raw)
                (pprogn (f-put-global 'dmrp nil state)
                        (if (consp dmrp)
                            (set-debugger-enable-fn (car dmrp) state)
                          state)))
          (t (observation 'dmr-stop
                          "Skipping dmr-stop (dmr is already stopped).")))))

(defmacro dmr-stop ()
  '(dmr-stop-fn #+acl2-loop-only state
                #-acl2-loop-only *the-live-state*))

(defun dmr-start-fn (state)
  (declare (xargs :guard (state-p state)))
  (cond ((f-get-global 'dmrp state)
         (observation 'dmr-start
                      "Skipping dmr-start (dmr is already started)."))
        (t (let* ((old-debugger-enable (f-get-global 'debugger-enable state))
                  (new-debugger-enable ; for interactive use of dmr-flush
                   (case old-debugger-enable
                     ((nil) t)
                     (:bt :break-bt))))
             (pprogn
              (if new-debugger-enable
                  (set-debugger-enable-fn new-debugger-enable state)
                state)
              #-acl2-loop-only
              (dmr-start-fn-raw state)
              (f-put-global 'dmrp
                            (if new-debugger-enable
                                (list old-debugger-enable)
                              t)
                            state))))))

(defmacro dmr-start ()
  '(dmr-start-fn #+acl2-loop-only state
                 #-acl2-loop-only *the-live-state*))

; Essay on Metafunction Support, Part 2

; For the first part of this essay, see ``Metafunction Support, Part
; 1'' in axioms.lisp.  This code is here at the end of ld so that it
; can use all our utilities and functions.

; We here turn to the problem of defining the uninterpreted functions
; that can actually be executed within a meta-level function.  Review Part 1 of
; the essay for the background and basic strategy.  We take up from there.

; Note: You can add other uninterpreted functions linked to theorem
; prover :program functions.  However, you should obey the following
; rules.

; (1) Of course, the metafunction context must be rich enough (or made
; rich enough) to provide the necessary arguments.  If you change the
; structure of metafunction-context, you must modify the accessors
; defined above mfc-clause, in axioms.lisp, or else the build will fail
; with a redefinition error.

; (2) Include STATE as an argument to the uninterpreted symbol,
; whether it is otherwise needed or not.

(defconst *meta-level-function-problem-1*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to ~
   the expression ~x1, which is not a term for which every function symbol is ~
   in :logic mode.  The meta-level function computation was ignored.~%~%")

(defconst *meta-level-function-problem-1a*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to an ~
   alist argument with ~@1.  The meta-level function computation was ignored.~%~%")

(defconst *meta-level-function-problem-1b*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to ~
   the non-rune ~x1 for the rune argument.  The meta-level function ~
   computation was ignored.~%~%")

(defconst *meta-level-function-problem-1c*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to ~
   the expression ~x1 for the target argument.  This expression must be a ~
   term that is the application of a function symbol and consists entirely of ~
   logic-mode functions; but it is not.  The meta-level function computation ~
   was ignored.~%~%")

(defconst *meta-level-function-problem-1d*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to ~
   the rune ~x1 and the target ~x2.  This is illegal, because there is no ~
   rewrite, definition, meta, or linear lemma named ~x1 whose top-level ~
   function symbol is ~x3.  The meta-level function computation was ~
   ignored.~%~%")

(defconst *meta-level-function-problem-1e*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to ~
   the ~x1 for the bkptr argument, which is not a valid one-based index into ~
   the hypothesis list of the lemma named by rune ~x2.  The meta-level ~
   function computation was ignored.~%~%")

(defconst *meta-level-function-problem-2*
  "~%~%Meta-level function Problem:  Some meta-level function applied ~x0 to a ~
   context different from the one passed to the meta-level function ~
   itself.  We cannot authenticate manufactured contexts.  The ~
   manufactured context was ~X12.  The meta-level function computation ~
   was ignored.~%~%")

(defconst *meta-level-function-problem-3*
  "~%~%Meta-level function Problem:  You or some meta-level function applied ~x0 but not ~
   from within the theorem prover's meta-level function handler.  This ~
   suggests you are trying to test a meta-level function and have evidently ~
   manufactured an allegedly suitable context.  Perhaps so. But that ~
   is so difficult to check that we don't bother.  Instead we cause ~
   this error and urge you to test your meta-level function by having the ~
   meta-level function handler invoke it as part of a test proof-attempt. To ~
   do this, assume the metatheorem that you intend eventually to ~
   prove.  You may do this by executing the appropriate DEFTHM event ~
   embedded in a SKIP-PROOFS form.  Then use THM to submit ~
   conjectures for proof and observe the behavior of your ~
   metafunction.  Remember to undo the assumed metatheorem before you ~
   attempt genuine proofs! If this suggestion isn't applicable to ~
   your situation, contact the authors.~%~%")

; We next introduce uninterpreted :logic mode functions with
; execute-only-in-meta-level-functions semantics, as per defun-overrides calls
; for mfc-ts-fn and such.  We use defproxy for now because state-p is still in
; :program mode; a partial-encapsulate comes later in the boot-strap (see
; boot-strap-pass-2-a.lisp).

#+acl2-loop-only
(defproxy mfc-ap-fn (* * state *) => *)
(defproxy mfc-relieve-hyp-fn (* * * * * * state *) => *)
(defproxy mfc-relieve-hyp-ttree (* * * * * * state *) => (mv * *))
(defproxy mfc-rw+-fn (* * * * * state *) => *)
(defproxy mfc-rw+-ttree (* * * * * state *) => (mv * *))
(defproxy mfc-rw-fn (* * * * state *) => *)
(defproxy mfc-rw-ttree (* * * * state *) => (mv * *))
(defproxy mfc-ts-fn (* * state *) => *)
(defproxy mfc-ts-ttree (* * state *) => (mv * *))

#-acl2-loop-only
(progn

(defun mfc-ts-raw (term mfc state forcep)
  (declare (xargs :guard (state-p state)))

; Type-set doesn't really use state.  We originally used the presence of the
; live state as authorization to execute, believing that the live state object
; cannot arise in an execution on behalf of an evaluation of a subexpression in
; a theorem or proof.  We now know that this is not the case; see the
; "soundness bug involving system function canonical-pathname" in :doc
; note-6-1.  However, we keep state around for legacy reasons.  If a reason is
; brought to our attention why it would be useful to remove state as a
; parameter, we can consider doing so.

  (let ((ev-fncall-val `(ev-fncall-null-body-er nil mfc-ts ,term mfc state)))
    (cond
     ((not (live-state-p state))

; This function acts like an undefined function unless it is applied to the
; live state.  See comment above.

      (throw-raw-ev-fncall ev-fncall-val))

     (*metafunction-context*

; We are within the application of a meta-level function by the theorem prover.

      (cond
       ((eq mfc *metafunction-context*)
        (cond
         ((logic-termp term (access metafunction-context mfc :wrld))

; At this point we can code freely.  In general, any data used below
; (i.e., any actuals passed in above) must be vetted as shown above.
; There is absolutely no reason to believe that the user has called
; mfc-ts correctly, even in a verified meta-level function and we must defend
; against hard errors.

; Note by the way that even though we have access to the mfc-ancestors, we do
; not use this data.  The reason is that type-set does not use the ancestors
; provided by the rewriter either.  Put another way: Type-set does not take
; ancestors as an argument, and calls of type-set-rec occur (at least as of
; this writing) only in the mutual-recursion nest where type-set is defined.

          (type-set term
                    (mfc-force-flg forcep mfc)
                    nil ;;; dwp
                    (access metafunction-context mfc :type-alist)
                    (access rewrite-constant
                            (access metafunction-context mfc :rcnst)
                            :current-enabled-structure)
                    (access metafunction-context mfc :wrld)
                    nil ;;; ttree
                    nil nil))
         (t (cw *meta-level-function-problem-1* 'mfc-ts term)
            (throw-raw-ev-fncall ev-fncall-val))))
       (t (cw *meta-level-function-problem-2* 'mfc-ts mfc
              (abbrev-evisc-tuple *the-live-state*))
          (throw-raw-ev-fncall ev-fncall-val))))

; We are not within the application of a meta-level function by the theorem
; prover.  We don't actually know if we are in the theorem prover.  This could
; be a proof-time evaluation of a subterm of a conjecture about MFC-TS (e.g.,
; the proof of the metatheorem justifying a metafunction using MFC-TS, or the
; proof of a lemma involved in that metatheorem proof).  Or, this could be a
; top-level call of MFC-TS or some function using it, as part of the user's
; testing of a meta-level function's development.

     (*hard-error-returns-nilp*

; This evaluation is part of a conjecture being proved.  Quietly act as though
; mfc-ts is an undefined function.  It is believed that this can never happen,
; because STATE is live.

      (throw-raw-ev-fncall ev-fncall-val))

     (t

; This is a top-level call of mfc-ts or some function using it.  Cause an error
; no matter what context the user has supplied.  See the error message.

      (cw *meta-level-function-problem-3* 'mfc-ts)
      (throw-raw-ev-fncall ev-fncall-val)))))

(defun mfc-rw-raw (term alist obj equiv-info mfc fn state forcep)
  (declare (xargs :guard (state-p state)))
  (let ((ev-fncall-val `(ev-fncall-null-body-er nil mfc-rw-raw ,term ,alist
                                                ',obj ,equiv-info mfc ,fn
                                                state)))
    (cond
     ((not (live-state-p state))
      (throw-raw-ev-fncall ev-fncall-val))
     (*metafunction-context*
      (cond
       ((eq mfc *metafunction-context*)
        (let ((wrld  (access metafunction-context mfc :wrld))
              (rcnst (access metafunction-context mfc :rcnst)))
          (cond
           ((not (logic-termp term wrld))
            (cw *meta-level-function-problem-1* fn term)
            (throw-raw-ev-fncall ev-fncall-val))
           ((let ((msg (term-alistp-failure-msg alist wrld)))
              (when msg
                (cw *meta-level-function-problem-1a* fn msg)
                (throw-raw-ev-fncall ev-fncall-val))))
           ((member-eq obj '(t nil ?))
            (sl-let
             (rw ttree)
             (let ((gstack (access metafunction-context mfc :gstack))
                   (rcnst (update-rncst-for-forcep forcep rcnst)))
               (rewrite-entry
                (rewrite term alist 'meta)
                :rdepth (access metafunction-context mfc :rdepth)
                :step-limit (initial-step-limit wrld state)
                :type-alist (access metafunction-context mfc :type-alist)
                :geneqv (cond ((eq equiv-info t)
                               *geneqv-iff*)
                              ((eq equiv-info nil)
                               nil) ; nil means EQUAL
                              ((and (symbolp equiv-info)
                                    (equivalence-relationp equiv-info wrld)
                                    (car (geneqv-lst
                                          equiv-info nil
                                          (access rewrite-constant rcnst
                                                  :current-enabled-structure)
                                          wrld))))
                              (t (prog2$ (or (congruence-rule-listp
                                              equiv-info
                                              wrld)
                                             (er hard! fn
                                                 "~x0 has been passed an ~
                                                  equiv-info argument that is ~
                                                  neither t, nil, a known ~
                                                  equivalence relation, nor a ~
                                                  list of congruence rules:~| ~
                                                   ~x1"
                                                 fn
                                                 equiv-info))
                                         equiv-info)))
                :pequiv-info nil
                :wrld wrld
                :fnstack (access metafunction-context mfc :fnstack)
                :ancestors (access metafunction-context mfc :ancestors)
                :backchain-limit (access metafunction-context mfc
                                         :backchain-limit)
                :simplify-clause-pot-lst (access metafunction-context mfc
                                                 :simplify-clause-pot-lst)
                :rcnst rcnst
                :gstack gstack
                :ttree nil))
             (declare (ignore step-limit))
             (mv rw ttree)))
           (t (cw "~%~%Meta-level function Problem:  Some meta-level function ~
                   called ~x0 with the OBJ argument set to ~x1.  That ~
                   argument must be one of the three symbols ?, T, or NIL."
                  fn
                  obj)
              (throw-raw-ev-fncall ev-fncall-val)))))
       (t (cw *meta-level-function-problem-2* fn mfc
              (abbrev-evisc-tuple *the-live-state*))
          (throw-raw-ev-fncall ev-fncall-val))))
     (*hard-error-returns-nilp*
      (throw-raw-ev-fncall ev-fncall-val))
     (t
      (cw *meta-level-function-problem-3* fn)
      (throw-raw-ev-fncall ev-fncall-val)))))

(defun mfc-relieve-hyp-raw (hyp alist rune target bkptr mfc state
                                forcep)

; We ignore issues concerning memoization and free variables below.
; As we gain experience with the use of this function, we may want
; to reconsider this.

  (declare (xargs :guard (state-p state)))
  (let ((ev-fncall-val `(ev-fncall-null-body-er nil mfc-relieve-hyp ,hyp ,alist
                                                ,rune ,target ,bkptr mfc
                                                state)))
    (cond
     ((not (live-state-p state))
      (throw-raw-ev-fncall ev-fncall-val))
     (*metafunction-context*
      (cond
       ((eq mfc *metafunction-context*)
        (let ((wrld  (access metafunction-context mfc :wrld))
              (rcnst (access metafunction-context mfc :rcnst))
              (ancestors (access metafunction-context mfc :ancestors)))
          (cond
           ((not (logic-termp hyp wrld))
            (cw *meta-level-function-problem-1* 'mfc-relieve-hyp hyp)
            (throw-raw-ev-fncall ev-fncall-val))
           ((let ((msg (term-alistp-failure-msg alist wrld)))
              (when msg
                (cw *meta-level-function-problem-1a* 'mfc-relieve-hyp msg)
                (throw-raw-ev-fncall ev-fncall-val))))
           ((not (runep rune wrld))
            (cw *meta-level-function-problem-1b* 'mfc-relieve-hyp rune)
            (throw-raw-ev-fncall ev-fncall-val))
           ((not (and (logic-termp target wrld)
                      (nvariablep target)
                      (not (fquotep target))
                      (symbolp (ffn-symb target))))
            (cw *meta-level-function-problem-1c* 'mfc-relieve-hyp target)
            (throw-raw-ev-fncall ev-fncall-val))
           (t
            (let* ((linearp (eq (car rune) :linear))
                   (lemmas (getpropc (ffn-symb target)
                                     (if linearp 'linear-lemmas 'lemmas)
                                     nil wrld))
                   (lemma (if linearp
                              (find-runed-linear-lemma rune lemmas)
                            (find-runed-lemma rune lemmas))))
              (cond ((null lemma)
                     (cw *meta-level-function-problem-1d*
                         'mfc-relieve-hyp rune target (ffn-symb target))
                     (throw-raw-ev-fncall ev-fncall-val))
                    ((not (and (posp bkptr)
                               (<= bkptr
                                   (length (if linearp
                                               (access linear-lemma lemma
                                                       :hyps)
                                             (access rewrite-rule lemma
                                                     :hyps))))))
                     (cw *meta-level-function-problem-1e*
                         'mfc-relieve-hyp
                         bkptr
                         rune)
                     (throw-raw-ev-fncall ev-fncall-val)))
              (sl-let
               (wonp failure-reason new-unify-subst ttree memo)
               (rewrite-entry
                (relieve-hyp rune target hyp alist bkptr nil)
                :rdepth (access metafunction-context mfc :rdepth)
                :step-limit (initial-step-limit wrld state)
                :type-alist (access metafunction-context mfc :type-alist)
                :obj nil    ; ignored
                :geneqv nil ; ignored
                :pequiv-info nil ; ignored
                :wrld wrld
                :fnstack (access metafunction-context mfc :fnstack)
                :ancestors ancestors
                :backchain-limit
                (new-backchain-limit (if (and (not linearp)
                                              (eq (access rewrite-rule lemma
                                                          :subclass)
                                                  'meta))
                                         (access rewrite-rule lemma
                                                 :backchain-limit-lst)
                                       (nth (1- bkptr)
                                            (if linearp
                                                (access linear-lemma lemma
                                                        :backchain-limit-lst)
                                              (access rewrite-rule lemma
                                                      :backchain-limit-lst))))
                                     (access metafunction-context mfc
                                             :backchain-limit)
                                     ancestors)
                :simplify-clause-pot-lst (access metafunction-context mfc
                                                 :simplify-clause-pot-lst)
                :rcnst (update-rncst-for-forcep forcep rcnst)
                :gstack (access metafunction-context mfc :gstack)
                :ttree nil)
               (declare (ignore step-limit failure-reason new-unify-subst
                                memo))
               (if (member-eq wonp '(t :unify-subst-list))
                   (mv t ttree)
                 (mv nil nil))))))))
       (t (cw *meta-level-function-problem-2* 'mfc-relieve-hyp mfc
              (abbrev-evisc-tuple *the-live-state*))
          (throw-raw-ev-fncall ev-fncall-val))))
     (*hard-error-returns-nilp*
      (throw-raw-ev-fncall ev-fncall-val))
     (t
      (cw *meta-level-function-problem-3* 'mfc-relieve-hyp)
      (throw-raw-ev-fncall ev-fncall-val)))))

(defun-one-output mfc-ap-raw (term mfc state forcep)
  (declare (xargs :guard (state-p state)))
  (let ((ev-fncall-val `(ev-fncall-null-body-er nil mfc-ap ,term mfc state)))
    (cond
     ((not (live-state-p state))
      (throw-raw-ev-fncall ev-fncall-val))
     (*metafunction-context*
      (cond
       ((eq mfc *metafunction-context*)
        (cond
         ((logic-termp term (access metafunction-context mfc :wrld))
          (let* ((force-flg (mfc-force-flg forcep mfc))
                 (linearized-list
                  (linearize term
                             t ;;; positivep
                             (access metafunction-context mfc :type-alist)
                             (access rewrite-constant
                                     (access metafunction-context mfc :rcnst)
                                     :current-enabled-structure)
                             force-flg
                             (access metafunction-context mfc :wrld)
                             nil ;;; ttree
                             state)))
            (cond ((null linearized-list)
                   nil)
                  ((null (cdr linearized-list))
                   (mv-let (contradictionp new-arith-db)
                           (add-polys (car linearized-list)
                                      (access metafunction-context
                                              mfc :simplify-clause-pot-lst)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :pt)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :nonlinearp)
                                      (access metafunction-context
                                              mfc :type-alist)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :current-enabled-structure)
                                      force-flg
                                      (access metafunction-context mfc :wrld))
                           (declare (ignore new-arith-db))
                           contradictionp))
                  (t
                   (mv-let (contradictionp1 new-arith-db)
                           (add-polys (car linearized-list)
                                      (access metafunction-context
                                              mfc :simplify-clause-pot-lst)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :pt)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :nonlinearp)
                                      (access metafunction-context
                                              mfc :type-alist)
                                      (access rewrite-constant
                                              (access metafunction-context
                                                      mfc :rcnst)
                                              :current-enabled-structure)
                                      force-flg
                                      (access metafunction-context mfc :wrld))
                           (declare (ignore new-arith-db))
                           (if contradictionp1
                               (mv-let (contradictionp2 new-arith-db)
                                       (add-polys (cadr linearized-list)
                                                  (access metafunction-context
                                                          mfc :simplify-clause-pot-lst)
                                                  (access rewrite-constant
                                                          (access metafunction-context
                                                                  mfc :rcnst)
                                                          :pt)
                                                  (access rewrite-constant
                                                          (access metafunction-context
                                                                  mfc :rcnst)
                                                          :nonlinearp)
                                                  (access metafunction-context
                                                          mfc :type-alist)
                                                  (access rewrite-constant
                                                          (access metafunction-context
                                                                  mfc :rcnst)
                                                          :current-enabled-structure)
                                                  force-flg
                                                  (access metafunction-context mfc :wrld))
                                       (declare (ignore new-arith-db))
                                       contradictionp2)
                             nil))))))
         (t (cw *meta-level-function-problem-1* 'mfc-ap term)
            (throw-raw-ev-fncall ev-fncall-val))))
       (t (cw *meta-level-function-problem-2* 'mfc-ap mfc
              (abbrev-evisc-tuple *the-live-state*))
          (throw-raw-ev-fncall ev-fncall-val))))
     (*hard-error-returns-nilp*
      (throw-raw-ev-fncall ev-fncall-val))
     (t
      (cw *meta-level-function-problem-3* 'mfc-ap)
      (throw-raw-ev-fncall ev-fncall-val)))))
)

(defmacro mfc-ts (term mfc st &key
                       (forcep ':same)
                       ttreep)
  (declare (xargs :guard (and (member-eq forcep '(t nil :same))
                              (booleanp ttreep))))
  (if ttreep
      `(mfc-ts-ttree ,term ,mfc ,st ,forcep)
    `(mfc-ts-fn ,term ,mfc ,st ,forcep)))

(defmacro mfc-rw (term obj equiv-info mfc st &key
                       (forcep ':same)
                       ttreep)

; We introduced mfc-rw+ after Version_3.0.1.  It was tempting to eliminate
; mfc-rw altogether (and then use the name mfc-rw for what we now call
; mfc-rw+), but we decided to leave mfc-rw unchanged for backward
; compatibility.  Worth mentioning: An attempt to replace mfc-rw by
; corresponding calls of mfc-rw+ in community book books/arithmetic-3/ resulted
; in a failed proof (of floor-floor-integer in community book
; books/arithmetic-3/floor-mod/floor-mod.lisp).

  (declare (xargs :guard (and (member-eq forcep '(t nil :same))
                              (booleanp ttreep))))
  (if ttreep
      `(mfc-rw-ttree ,term ,obj ,equiv-info ,mfc ,st ,forcep)
    `(mfc-rw-fn ,term ,obj ,equiv-info ,mfc ,st ,forcep)))

(defmacro mfc-rw+ (term alist obj equiv-info mfc st &key
                        (forcep ':same)
                        ttreep)
  (declare (xargs :guard (and (member-eq forcep '(t nil :same))
                              (booleanp ttreep))))
  (if ttreep
      `(mfc-rw+-ttree ,term ,alist ,obj ,equiv-info ,mfc ,st ,forcep)
    `(mfc-rw+-fn ,term ,alist ,obj ,equiv-info ,mfc ,st ,forcep)))

(defmacro mfc-relieve-hyp (hyp alist rune target bkptr mfc st &key
                               (forcep ':same)
                               ttreep)
  (declare (xargs :guard (and (member-eq forcep '(t nil :same))
                              (booleanp ttreep))))
  (if ttreep
      `(mfc-relieve-hyp-ttree ,hyp ,alist ,rune ,target ,bkptr ,mfc ,st
                              ,forcep)
    `(mfc-relieve-hyp-fn ,hyp ,alist ,rune ,target ,bkptr ,mfc ,st
                         ,forcep)))

(defmacro mfc-ap (term mfc st &key
                       (forcep ':same))
  (declare (xargs :guard (member-eq forcep '(t nil :same))))
  `(mfc-ap-fn ,term ,mfc ,st ,forcep))

(defun congruence-rule-listp (x wrld)
  (if (atom x)
      (null x)
    (and (let ((rule (car x)))
           (case-match rule
             ((nume equiv . rune)
              (and (equivalence-relationp equiv wrld)
                   (or (runep rune wrld)
                       (equal rune
                              *fake-rune-for-anonymous-enabled-rule*))
                   (eql (fnume rune wrld) nume)))))
         (congruence-rule-listp (cdr x) wrld))))

(defun term-alistp-failure-msg (alist wrld)

; Returns nil if alist is an alist binding variables to terms.  Otherwise,
; returns a message suitable for use in *meta-level-function-problem-1a*.

  (cond ((atom alist)
         (and alist
              (msg "a non-nil final cdr")))
        ((atom (car alist))
         (msg "a non-consp element, ~x0" (car alist)))
        ((not (and (termp (caar alist) wrld)
                   (variablep (caar alist))))
         (msg "an element, ~p0, whose car is not a variable" (caar alist)))
        ((not (termp (cdar alist) wrld))
         (msg "an element, ~p0, whose cdr is not a term" (cdar alist)))
        (t (term-alistp-failure-msg (cdr alist) wrld))))

(defun find-runed-linear-lemma (rune lst)

; Lst must be a list of lemmas.  We find the first one with :rune rune (but we
; make no assumptions on the form of rune).

  (cond ((null lst) nil)
        ((equal rune
                (access linear-lemma (car lst) :rune))
         (car lst))
        (t (find-runed-linear-lemma rune (cdr lst)))))

(defun mfc-force-flg (forcep mfc)
  (cond ((eq forcep :same)
         (ok-to-force (access metafunction-context mfc :rcnst)))
        (t forcep)))

(defun update-rncst-for-forcep (forcep rcnst)
  (cond ((or (eq forcep :same)
             (iff forcep
                  (ok-to-force rcnst)))
         rcnst)
        (t (change rewrite-constant rcnst
                   :force-info
                   (if forcep
                       t
                     'weak)))))

; Essay on Saved-output

; Starting with Version_2.9.2, ACL2 has the capability of running not only with
; output inhibited but also with output saved, to be printed upon demand by pso
; and pso! (see their documentation).  This capability is controlled by state
; global variables whose names start with SAVED-OUTPUT-, namely:
; 'saved-output-reversed, 'saved-output-token-lst, and 'saved-output-p.  State
; global 'print-clause-ids was also introduced at the same time, in order to
; allow printing of clause ids with output inhibited in order that the user can
; observe progress of the proof.

; Why do we need both 'saved-output-p and 'saved-output-token-lst?  The latter
; records the output that the user wants saved (typically, :all or nil).  The
; former activates the saving of output, which is why it is bound to t in
; with-ctx-summarized.  The idea is that we do not want to save output that
; comes from top-level calls by the user that are not event forms, so
; 'saved-output-p remains nil at the top level.

; Perhaps we should add a mechanical check that there are no nested calls of
; io?, since such calls could confuse our mechanism for saving output.

; Implementation note: Calls of io? on a given body take as an argument a
; listing of all the free variables of that body.  After the definitions below,
; a macro call (av body) will print out such a list.

; (defun all-vars-untrans (form state)
;   (declare (xargs :mode :program :stobjs state))
;   (mv-let (erp val bindings state)
;     (translate1 form
;                 :stobjs-out
;                 '((:stobjs-out . :stobjs-out))
;                 t 'top-level
;                 (w state) state)
;     (declare (ignore erp bindings))
;     (value (remove1-eq 'state (all-vars val)))))
;
; (defmacro av (form)
;   `(all-vars-untrans ',form state))

(defun print-saved-output-lst (io-record-lst io-markers stop-markers ctx state)
  (cond
   ((endp io-record-lst)
    (value :invisible))
   (t
    (let ((io-marker (access io-record (car io-record-lst)
                             :io-marker)))
      (cond
       ((member-equal io-marker stop-markers)
        (value :invisible))
       ((or (eq io-markers :all)
            (member-equal io-marker io-markers))
        (er-progn (trans-eval

; We could call trans-eval-default-warning here instead of trans-eval.  But if
; a user stobj is modified simply by printing output, we should probably know
; about it (and someone will likely complain loudly).

                   (access io-record (car io-record-lst)
                           :form)
                   ctx state t)
                  (print-saved-output-lst (cdr io-record-lst)
                                          (if stop-markers
                                              :all ; print till we're stopped
                                            io-markers)
                                          stop-markers
                                          ctx
                                          state)))
       (t (print-saved-output-lst (cdr io-record-lst) io-markers stop-markers
                                  ctx state)))))))

(defun print-saved-output (inhibit-output-lst gag-mode io-markers stop-markers
                                              state)

; Normally io-markers is :all, indicating the set of all io-markers; but
; instead it can be a list of io-markers.

  (let ((saved-output (reverse (f-get-global 'saved-output-reversed
                                             state)))
        (channel (standard-co state))
        (ctx 'print-saved-output))
    (cond
     ((or (null saved-output)
          (and (null (cdr saved-output))
               (eq (access io-record (car saved-output)
                           :io-marker)
                   :ctx)))
      (er-progn (if saved-output
                    (trans-eval

; We could call trans-eval-default-warning here instead of trans-eval.  But if
; a user stobj is modified simply by printing output, we should probably know
; about it (and someone will likely complain loudly).

                     (access io-record (car saved-output)
                             :form)
                     ctx state t)
                  (value nil))
                (pprogn (fms "There is no saved output to print.  ~
                              See :DOC set-saved-output.~|"
                             nil
                             channel state nil)
                        (value :invisible))))
     (t (let ((old-gag-state (f-get-global 'gag-state state)))
          (state-global-let*
           ((saved-output-reversed nil) ; preserve this (value doesn't matter)
            (inhibit-output-lst inhibit-output-lst)
            (gag-mode gag-mode)
            (gag-state-saved (f-get-global 'gag-state-saved state)))
           (pprogn (initialize-summary-accumulators state)
                   (save-event-state-globals
                    (pprogn
                     (if old-gag-state
                         state

; Otherwise we set gag-state to nil after saving the gag-state in
; gag-state-saved.

                       (f-put-global 'gag-state
                                     (f-get-global 'gag-state-saved state)
                                     state))
                     (revert-world
                      (state-global-let*
                       ((saved-output-p nil)
                        (acl2-world-alist (f-get-global 'acl2-world-alist
                                                        state)))
                       (pprogn
                        (pop-current-acl2-world 'saved-output-reversed state)
                        (print-saved-output-lst saved-output io-markers
                                                stop-markers ctx
                                                state)))))))))))))

(defun convert-io-markers-lst (io-markers acc)
  (cond ((endp io-markers) acc)
        (t (convert-io-markers-lst (cdr io-markers)
                                   (cons (if (stringp (car io-markers))
                                             (parse-clause-id (car io-markers))
                                           (car io-markers))
                                         acc)))))

(defun convert-io-markers (io-markers)
  (cond ((member-eq io-markers '(nil :all))
         io-markers)
        ((and io-markers
              (atom io-markers))
         (convert-io-markers-lst (list io-markers) nil))
        (t (convert-io-markers-lst io-markers nil))))

(defmacro pso (&optional (io-markers ':all)
                         stop-markers)
  `(print-saved-output '(proof-tree) nil
                       (convert-io-markers ,io-markers)
                       (convert-io-markers ,stop-markers)
                       state))

(defmacro psog (&optional (io-markers ':all)
                          stop-markers)
  `(print-saved-output '(proof-tree) t
                       (convert-io-markers ,io-markers)
                       (convert-io-markers ,stop-markers)
                       state))

(defmacro pso! (&optional (io-markers ':all)
                          stop-markers)
  `(print-saved-output nil nil
                       (convert-io-markers ,io-markers)
                       (convert-io-markers ,stop-markers)
                       state))

(defmacro set-raw-proof-format (flg)
  (declare (xargs :guard (member-equal flg '(t 't nil 'nil))))
  (let ((flg (if (atom flg)
                 (list 'quote flg)
               flg)))
    `(f-put-global 'raw-proof-format ,flg state)))

(defmacro set-raw-warning-format (flg)
  (declare (xargs :guard (member-equal flg '(t 't nil 'nil))))
  (let ((flg (if (atom flg)
                 (list 'quote flg)
               flg)))
    `(f-put-global 'raw-warning-format ,flg state)))

(defun-for-state set-standard-co (val state))

(defun-for-state set-proofs-co (val state))

(defmacro with-standard-co-and-proofs-co-to-file (filename form)
  `(mv-let
    (wof-chan state)
    (open-output-channel ,filename :character state)
    (cond
     ((null wof-chan)
      (er soft 'with-standard-co-and-proofs-co-to-file
          "Unable to open file ~x0 for output."
          ,filename))
     (t
      (pprogn
       (princ$ "-*- Mode: auto-revert -*-" wof-chan state)
       (newline wof-chan state)
       (mv-let (erp val state)
               (state-global-let*
                ((standard-co wof-chan set-standard-co-state)
                 (proofs-co wof-chan set-proofs-co-state))
                (check-vars-not-free
                 (wof-chan)
                 ,form))
               (pprogn (close-output-channel wof-chan state)
                       (cond (erp (silent-error state))
                             (t (value val))))))))))

(defmacro wof (filename form) ; Acronym: With Output File
  `(with-standard-co-and-proofs-co-to-file ,filename ,form))

(defmacro psof (filename
                &optional
                (io-markers ':all)
                (stop-markers 'nil))
  (declare (xargs :guard (or (stringp filename)
                             (and (consp filename)
                                  (consp (cdr filename))
                                  (null (cddr filename))
                                  (eq (car filename) 'quote)
                                  (stringp (cadr filename))))))
  `(cond #+acl2-par
         ((f-get-global 'waterfall-parallelism state)
          (er soft 'psof
              "The PSOF command is disabled with waterfall-parallelism ~
               enabled, because in that case most prover output is printed to ~
               *standard-co* (using wormholes), so cannot be redirected."))
         (t (wof ,(if (consp filename) (cadr filename) filename)
                 (pso ,io-markers ,stop-markers)))))

; We now develop code for without-evisc.

(defun set-ld-evisc-tuple (val state)
  (set-evisc-tuple val
                   :sites :ld
                   :iprint :same))

(defun-for-state set-ld-evisc-tuple (val state))

(defun set-abbrev-evisc-tuple (val state)
  (set-evisc-tuple val
                   :sites :abbrev
                   :iprint :same))

(defun-for-state set-abbrev-evisc-tuple (val state))

(defun set-gag-mode-evisc-tuple (val state)
  (set-evisc-tuple val
                   :sites :gag-mode
                   :iprint :same))

(defun-for-state set-gag-mode-evisc-tuple (val state))

(defun set-term-evisc-tuple (val state)
  (set-evisc-tuple val
                   :sites :term
                   :iprint :same))

(defun-for-state set-term-evisc-tuple (val state))

(defun without-evisc-fn (form state)
  (state-global-let*
   ((abbrev-evisc-tuple nil set-abbrev-evisc-tuple-state)
    (gag-mode-evisc-tuple nil set-gag-mode-evisc-tuple-state)
    (term-evisc-tuple   nil set-term-evisc-tuple-state))
   (er-progn (ld (list form)
                 :ld-verbose nil
                 :ld-prompt nil
                 :ld-evisc-tuple nil
                 :ld-user-stobjs-modified-warning nil)
             (value :invisible))))

(defmacro without-evisc (form)
  `(without-evisc-fn ',form state))
