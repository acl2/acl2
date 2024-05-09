; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/utilities/checkpoints" :dir :system)

(defun rmh-removal-pairs-simple (kwd-1 kwd pre-rev post acc)

; We use this function when kwd is :expand or :use.  See rmh-removal-pairs.
; For example, if kwd is :use, pre-rev is nil, post is (e1 e2 e3), and acc is
; nil, then kwd-1 is :use-1 and we return

; (((:use-1 e1) . (:use e2 e3))
;  ((:use-1 e2) . (:use e1 e3))
;  ((:use-1 e3) . (:use e2 e3))).

; The value of (revappend pre-rev post) is maintained as we recur by pushing
; the car of post onto pre-rev.

  (declare (xargs :guard (and (true-listp pre-rev)
                              (true-listp post)
                              (true-list-listp acc))))
  (cond ((endp post) (reverse acc))
        (t (rmh-removal-pairs-simple
            kwd-1 kwd
            (cons (car post) pre-rev)
            (cdr post)
            (cons (let* ((next (car post))
                         (key (list kwd-1 next)))
                    (cons key (cons kwd (revappend pre-rev (cdr post)))))
                  acc)))))

(defun rmh-removal-pairs-do-not (pre-rev post acc)

; This is similar to rmh-removal-pairs-simple, except that we produce a valid
; do-not hint in each returned cdr.  See rmh-removal-pairs.  Note that pre-rev
; and post do not contain the quote.

  (declare (xargs :guard (and (true-listp pre-rev)
                              (true-listp post)
                              (true-list-listp acc))))
  (cond ((endp post) (reverse acc))
        (t (rmh-removal-pairs-do-not
            (cons (car post) pre-rev)
            (cdr post)
            (cons (let* ((next (car post))
                         (key (list :do-not-1 next)))
                    (cons key (cons :do-not
                                    (list 'quote
                                          (revappend pre-rev (cdr post))))))
                  acc)))))

(defun single-rune-for-symbol-p (x defp wrld)

; We assume that x is not a macro name; deref-macro-name has been applied
; before this call.  Defp is true when we allow more than one rune if one is a
; :DEFINITION rune and it is followed in the runic-mapping-pairs by an
; :executable-counterpart rune.

  (declare (xargs :guard (and (symbolp x)
                              (plist-worldp wrld))))
  (let ((temp (getpropc x 'runic-mapping-pairs nil wrld)))
    (and (consp temp)
         (or (null (cdr temp))
; a test from convert-theory-to-unordered-mapping-pairs1:
             (and defp
                  (= (len (car temp)) 2) ; for guard verification
                  (eq (car (cdr (car temp))) :DEFINITION)
                  (not (= (len temp) 4)) ; no :induction rune
                  (consp (cdr temp)) ; for guard verification
                  (= (len (cadr temp)) 2) ; for guard verification
                  (eq (car (cdr (cadr temp))) :EXECUTABLE-COUNTERPART))))))

(local (defthm r-symbol-alistp-forward-to-alistp
         (implies (r-symbol-alistp x)
                  (alistp x))
         :rule-classes :forward-chaining))

(local (defthm values-are-symbols-in-r-symbol-alistp
         (implies (r-symbol-alistp x)
                  (symbolp (cdr (assoc-equal key x))))))

(defun rmh-remove-* (kwd)

; Kwd is :enable* or :disable* when this function is called in
; rmh-enable-disable-key-1, but can be :enable or :disable when called in
; rmh-enable-disable-key.

  (declare (xargs :guard t))
  (cond ((eq kwd :enable*) :enable)
        ((eq kwd :disable*) :disable)
        (t kwd)))

(defun rmh-enable-disable-key-1 (kwd x wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((kwd2 (cond ((member-eq kwd '(:enable :disable))
                     kwd)
                    ((and (symbolp x)
                          (or (getpropc x 'runic-mapping-pairs nil wrld)
                              (not (eq (getpropc x 'theory t wrld) t))))
                     (rmh-remove-* kwd))
                    ((and (consp x)
                          (not (member-eq (car x)
; See :DOC expand-ruleset.
                                          '(:executable-counterpart-theory
                                            :current-theory
                                            :theory
                                            :rules-of-class))))
                     (rmh-remove-* kwd))
                    (t kwd))))
    (list kwd2 x)))

(defund rmh-enable-disable-key (kwd x macro-aliases wrld)

; This definition was inspired by ACL2 source function rule-name-designatorp.
; Here we assume that x is a valid runic designator.

  (declare (xargs :guard (and (r-symbol-alistp macro-aliases)
                              (plist-worldp wrld))))
  (cond
   ((symbolp x)
    (rmh-enable-disable-key-1 kwd
                              (deref-macro-name x macro-aliases)
                              wrld))
   ((and (consp x)
         (null (cdr x))
         (symbolp (car x)))
    (let ((fn (deref-macro-name (car x) macro-aliases)))
      (list (rmh-remove-* kwd) fn)))
   (t (let ((y (translate-abbrev-rune x macro-aliases)))
        (cond
         ((not (= (len y) 2)) ; impossible?
          x)
         (t (let* ((sym (base-symbol y))
                   (defp (and (consp y)
                              (eq (car y) :definition))))
              (rmh-enable-disable-key-1
               kwd
               (if (and (symbolp sym) ; for guard verification
                        (single-rune-for-symbol-p sym defp wrld))
                   sym
                 y)
               wrld))))))))

(defun rmh-removal-pairs-enable-or-disable (kwd sym pre-rev post acc
                                                macro-aliases wrld)

; This is similar to rmh-removal-pairs-simple, modified to be as described in
; rmh-removal-pairs for handling :in-theory (enable ...) or :in-theory (disable
; ...) or similarly for enable* or disable*.

  (declare (xargs :guard (and (true-listp pre-rev)
                              (true-listp post)
                              (true-list-listp acc)
                              (r-symbol-alistp macro-aliases)
                              (plist-worldp wrld))))
  (cond ((endp post) (reverse acc))
        (t (rmh-removal-pairs-enable-or-disable
            kwd sym
            (cons (car post) pre-rev)
            (cdr post)
            (cons (let* ((next (car post))
                         (key (rmh-enable-disable-key kwd next macro-aliases
                                                      wrld)))
                    (cons key (cons :in-theory
                                    (cons sym
                                          (revappend pre-rev (cdr post))))))
                  acc)
            macro-aliases wrld))))

(defun rmh-removal-pairs-e/d (e-p kwd sym other-lst pre-rev post rest acc
                                  macro-aliases wrld)

; This is similar to rmh-removal-pairs-simple, modified to be as described in
; rmh-removal-pairs for handling :in-theory (e/d lst1 lst2).  If e-p is true
; then we are removing from the enables, lst1, which is (revappend pre-rev
; post); then other-lst is lst2, the disables.  It's the other way around if
; e-p is false.

  (declare (xargs :guard (and (true-listp pre-rev)
                              (true-listp post)
                              (true-listp rest)
                              (true-list-listp acc)
                              (r-symbol-alistp macro-aliases)
                              (plist-worldp wrld))))
  (cond ((endp post) (reverse acc))
        (t (rmh-removal-pairs-e/d
            e-p kwd sym other-lst
            (cons (car post) pre-rev)
            (cdr post)
            rest
            (cons (let* ((next (car post))
                         (key (rmh-enable-disable-key kwd next macro-aliases
                                                      wrld))
                         (removal-lst (revappend pre-rev (cdr post))))
                    (cons key
                          (cons :in-theory
                                (cons sym
                                      (if e-p
                                          (list* removal-lst other-lst rest)
                                        (list* other-lst removal-lst rest))))))
                  acc)
            macro-aliases wrld))))

(defthm true-listp-rmh-removal-pairs-e/d
  (implies (true-listp acc)
           (true-listp
            (rmh-removal-pairs-e/d e-p kwd sym other-lst pre-rev post rest acc
                                   macro-aliases wrld)))
  :rule-classes :type-prescription)

(defun rmh-removal-pairs (kwd val macro-aliases wrld)

; For some untranslated hint-settings, removal is not atomic.  For example, if
; the user specifies ("Goal" :use (lemma1 lemma2)), then we would like to
; remove lemma1 and lemma2 individually rather than removing the entire
; untranslated hint-setting of :use (lemma1 lemma2).  This function returns a
; non-nil value in such non-atomic cases, which is used by
; rmh-checkpoints-multiple to record proof attempts for such removals.

; Kwd is a hint-setting keyword such as :use or :in-theory (but also allowed
; are :enable and :disable; see comments in remove-hint-setting-checkpoints).
; Val is the value of kwd in untranslated hint settings such as a user would
; supply on "Goal".

; We return either nil, indicating that the indicated hint setting should be
; removed atomically, or else a list of pairs (uhs . val') obtained by removing
; one "part" of val at a time.  Here are examples of what is returned in the
; non-nil case.

; If kwd is :use and val is (e1 e2 e3), then we return
; (((:use-1 e1) . (:use . (e2 e3)))
;  ((:use-1 e2) . (:use . (e1 e3)))
;  ((:use-1 e3) . (:use . (e1 e2)))).

; If kwd is :expand and val is (e1 e2 e3), where e1 is not a symbol other than
; :lambdas, then we return (in complete analogy with the :use case above):
; (((:expand-1 e1) . (:expand . (e2 e3)))
;  ((:expand-1 e2) . (:expand . (e1 e3)))
;  ((:expand-1 e3) . (:expand . (e1 e2)))).

; If kwd is :do-not and val is '(e1 e2 e3), then we return
; (((:do-not-1 e1) . (:do-not . '(e2 e3)))
;  ((:do-not-1 e2) . (:do-not . '(e1 e3)))
;  ((:do-not-1 e3) . (:do-not . '(e1 e2)))).

; If kwd is :in-theory and val is (enable e1 e2 e3), then we return the
; following; similarly for (disable e1 e2 e3), and for enable* and disable* in
; place of enable and disable, resp.
; (((:enable e1) . (:in-theory . (enable e2 e3)))
;  ((:enable e2) . (:in-theory . (enable e1 e3)))
;  ((:enable e3) . (:in-theory . (enable e1 e2)))).

; If kwd is :in-theory and val is (e/d (e1 e2 e3) (d1 d2 d3)), then we return
; the following; similarly for e/d*.
; (((:enable e1)  . (:in-theory . (e/d (e2 e3)    (d1 d2 d3))))
;  ((:enable e2)  . (:in-theory . (e/d (e1 e3)    (d1 d2 d3))))
;  ((:enable e3)  . (:in-theory . (e/d (e1 e2)    (d1 d2 d3))))
;  ((:disable d1) . (:in-theory . (e/d (e1 e2 e3) (d2 d3))))
;  ((:disable d2) . (:in-theory . (e/d (e1 e2 e3) (d1 d3))))
;  ((:disable d3) . (:in-theory . (e/d (e1 e2 e3) (d1 d2))))).

  (declare (xargs :guard (and (keywordp kwd)
                              (r-symbol-alistp macro-aliases)
                              (plist-worldp wrld))))
  (case kwd
    (:do-not (and (consp val)
                  (eq (car val) 'quote)
                  (consp (cdr val))
                  (let ((lst (cadr val)))
                    (and (symbol-listp lst) ; always true?
                         (null (cddr val))
                         (consp (cdr lst))
                         (rmh-removal-pairs-do-not nil lst nil)))))
    (:expand (and
; First check that it's not a single term to expand (else we handle the hint in
; the normal way).  Keep this in sync with translate-expand-hint.
              (not (eq val :lambdas))
              (not (and (consp val)
                        (symbolp (car val))
                        (not (eq (car val) :lambdas))))
; Now check directly that we don't have a singleton.
              (true-listp val) ; always true?
              (consp (cdr val))
              (rmh-removal-pairs-simple :expand-1 :expand nil val nil)))
    (:use (and (consp val)
; First check that it's not a single term to expand (else we handle the hint in
; the normal way).  Keep this in sync with translate-use-hint.
               (not (member-eq (car val)
                               '(:instance
                                 :functional-instance
                                 :theorem
                                 :termination-theorem
                                 :termination-theorem!
                                 :guard-theorem)))
; The following should rule out runep.
               (not (keywordp (car val)))
; Now check directly that we don't have a singleton.
               (true-listp val) ; always true?
               (consp (cdr val))
               (rmh-removal-pairs-simple :use-1 :use nil val nil)))
    (:in-theory (and
                 (consp val)
                 (true-listp val) ; always true?
                 (case (car val)
                   ((enable disable enable* disable*)
                    (and (consp (cdr val))
                         (rmh-removal-pairs-enable-or-disable
                          (intern (symbol-name (car val)) "KEYWORD")
                          (car val)
                          nil (cdr val) nil macro-aliases wrld)))
                   ((e/d e/d*) ; (e/d* enables disables ...)

; It is probably uncommon to give more than two arguments to e/d or e/d*.  But
; it's fine if there are extra arguments; we simply don't bother removing from
; them, but instead, we let them ride along for free.  If removing an enable or
; a disable from the first or second argument (respectively) makes the proof
; fail, then it's legitimate to note that in the :HINT-SETTING-ALIST.  If it
; indicates :REMOVE then that's perhaps a bit weird (see
; e.g. tests/test2b.lisp), but probably harmless.

                    (let ((enables (cadr val))
                          (disables (caddr val))
                          (rest (cdddr val)))
                      (and (true-listp enables)       ; always true?
                           (true-listp disables)      ; always true?
                           (append (rmh-removal-pairs-e/d
                                    t
                                    (if (eq (car val) 'e/d)
                                        :enable
                                      :enable*)
                                    (car val)
                                    disables nil enables rest nil
                                    macro-aliases wrld)
                                   (rmh-removal-pairs-e/d
                                    nil
                                    (if (eq (car val) 'e/d)
                                        :disable
                                      :disable*)
                                    (car val)
                                    enables nil disables rest nil
                                    macro-aliases wrld)))))
                   (otherwise nil))))
    (otherwise nil)))

; Code involving calls of prove need to be in program mode.
(program)
(set-state-ok t)

(defun replace-defthm-hints (defthm-event untrans-goal-hint-settings)

; This trivial function replaces the body of a defthm with the given body,
; which is typically an untranslated term.

; Note that this function does nothing with other fields of the defthm,
; such as corollaries (whose proofs might depend on body).

  (let ((rest (cdddr defthm-event))
        (ctx 'replace-defthm-hints))
    (cond
     ((keyword-value-listp rest)
      (let ((hints (cadr (assoc-keyword :hints rest))))
        (cond
         ((null hints)
          (er hard! ctx
              "Implementation error: Expected :hints to be non-empty!"))
         ((not (alistp hints))
          (er hard! ctx
              "Implementation error: Expected :hints to be an alist, but it ~
               is ~x0."
              hints))
         (t
          (let ((pair (assoc-string-equal "goal" hints)))
            (cond
             ((null pair)
              (er hard! ctx
                  "Implementation error: Expected :hints to include ~
                   hint-settings for \"Goal\", but ~x0 does not."
                  hints))
             (t (let ((new-hints
                       (if untrans-goal-hint-settings
                           (put-assoc-equal (car pair)
                                            untrans-goal-hint-settings
                                            hints)
                         (remove-assoc-equal (car pair) hints))))
                  (mv-let (pre post)
                    (split-keyword-alist :hints rest)
                    (append (take 3 defthm-event)
                            pre
                            (and new-hints (list :hints new-hints))
                            (cddr post)))))))))))
     (t (er hard! ctx
            "Implementation error: Expected keyword-value-listp for cdddr but ~
             got ~x0."
            rest)))))

(defun rmh-checkpoints-2 (term pspv
                               untrans-hint-settings hint-settings
                               key thints time-limit
                               event-form ens wrld ctx state)
  (save-event-state-globals
   (mv-let (erp val state)
     (with-prover-time-limit
      time-limit
      (prove term pspv
             (acons *initial-clause-id* hint-settings thints)
             ens wrld ctx state))
     (declare (ignore val))
     (pprogn
      (f-put-global 'gag-state-saved (@ gag-state) state)

; If prove caused an error, then we expect checkpoints.  An error without
; checkpoints may be unusual, since it means that the proof failed but there
; were no checkpoints, perhaps because the time-limit was reached before any
; checkpoints were created; we return (list untrans-hint-setting :fail) in that
; case.  If prove did not cause an error, then we return (list
; untrans-hint-setting :remove) to indicate that the untranslated hint-setting
; can be removed.

      (value (let ((new-event (replace-defthm-hints
                               event-form
                               untrans-hint-settings)))
               (cond (erp (let ((c1 (checkpoint-list t state))
                                (c2 (checkpoint-list nil state)))
                            (cond ((or c1 c2)
                                   (list key
                                         c1
                                         (prettyify-clause-lst c1 nil wrld)
                                         c2
                                         (prettyify-clause-lst c2 nil wrld)
                                         new-event))
                                  (t (list key :fail new-event)))))
                     (t (list key :remove new-event)))))))))

(defun rmh-checkpoints-multiple (lst term pspv
                                     untrans-goal-hint-settings-1
                                     goal-hint-settings-1
                                     cddr-untrans-goal-hint-settings-2
                                     cdr-goal-hint-settings-2
                                     thints time-limit event-form
                                     ens wrld ctx state acc)

; Lst is a list of rhs-removal-pairs (see also the function of that name), each
; of the form (key . h) where key is a "uhs" describing what is removed, as
; discussed in remove-hint-setting-checkpoints -- for example, (:use e1) or
; (:expand e1) -- and h is an untranslated hint-setting (kwd arg).

  (cond
   ((endp lst) (value acc))
   (t (let* ((trip (car lst))
             (key (car trip))
             (kwd (cadr trip))
             (arg (cddr trip)))
        (mv-let (erp hint-value state)
          (translate-x-hint-value nil ; irrelevant name-tree for (car lst)
                                  "Goal" kwd arg ctx wrld state)
          (er-let* ((val
                     (cond
                      (erp

; Error output is inhibited, so we use a hard error instead of a soft error.

                       (prog2$ (er hard ctx
                                   "Possible implementation error: Unable to ~
                                    translate hint from rhs-removal-pair ~
                                    ~x0.~|~%"
                                   (car lst))
                               (value (list key
                                            :fail
                                            :unreachable-replaced-defthm))))
                      ((and (eq kwd :in-theory)
                            (member-equal arg
                                          '((enable) (enable*)
                                            (disable) (disable*)
                                            (e/d () ()) (e/d* () ()))))
                       (rmh-checkpoints-2
                        term pspv
                        (revappend untrans-goal-hint-settings-1
                                   cddr-untrans-goal-hint-settings-2)
                        (revappend goal-hint-settings-1
                                   cdr-goal-hint-settings-2)
                        key thints time-limit event-form ens wrld ctx state))
                      (t
                       (rmh-checkpoints-2
                        term pspv
                        (revappend untrans-goal-hint-settings-1
                                   (list* kwd arg
                                          cddr-untrans-goal-hint-settings-2))
                        (revappend goal-hint-settings-1
                                   (cons (cons kwd hint-value)
                                         cdr-goal-hint-settings-2))
                        key thints time-limit event-form ens wrld ctx state)))))
            (rmh-checkpoints-multiple (cdr lst) term pspv
                                      untrans-goal-hint-settings-1
                                      goal-hint-settings-1
                                      cddr-untrans-goal-hint-settings-2
                                      cdr-goal-hint-settings-2
                                      thints time-limit event-form
                                      ens wrld ctx state
                                      (cons val acc))))))))

(defun rmh-checkpoints-1 (term pspv
                               untrans-goal-hint-settings-1
                               goal-hint-settings-1
                               untrans-goal-hint-settings-2
                               goal-hint-settings-2
                               thints time-limit event-form
                               ens wrld ctx state acc)
  (cond
   ((endp goal-hint-settings-2) (value acc))
   (t
    (let* ((untrans-kwd (car untrans-goal-hint-settings-2))
           (untrans-val (cadr untrans-goal-hint-settings-2))
           (lst (rmh-removal-pairs untrans-kwd untrans-val
                                   (macro-aliases wrld)
                                   wrld)))
      (er-let* ((acc
                 (cond
                  (lst (rmh-checkpoints-multiple
                        lst term pspv
                        untrans-goal-hint-settings-1
                        goal-hint-settings-1
                        (cddr untrans-goal-hint-settings-2)
                        (cdr goal-hint-settings-2)
                        thints time-limit event-form ens wrld ctx state acc))
                  (t (er-let* ((entry
                                (rmh-checkpoints-2
                                 term pspv
                                 (revappend untrans-goal-hint-settings-1
                                            (cddr untrans-goal-hint-settings-2))
                                 (revappend goal-hint-settings-1
                                            (cdr goal-hint-settings-2))
                                 (list untrans-kwd untrans-val)
                                 thints time-limit event-form
                                 ens wrld ctx state)))
                       (value (cons entry acc)))))))
        (rmh-checkpoints-1
         term pspv
         (list* untrans-val untrans-kwd untrans-goal-hint-settings-1)
         (cons (car goal-hint-settings-2)
               goal-hint-settings-1)
         (cddr untrans-goal-hint-settings-2)
         (cdr goal-hint-settings-2)
         thints time-limit event-form ens wrld ctx state acc))))))

(defun rmh-keys-equal (lst a2)
  (declare (xargs :guard (and (keyword-value-listp lst) (alistp a2))))
  (cond ((endp lst) (null a2))
        ((endp a2) nil)
        (t (and (eq (car lst) (caar a2))
                (rmh-keys-equal (cddr lst) (cdr a2))))))

(defun remove-hint-setting-checkpoints (term pspv hints thints time-limit
                                             event-form ens wrld ctx state)

; We return an error triple whose value is a list of entries of one of the
; forms below, where uhs is an untranslated hint setting (list kwd val) that
; the user might give in :hints, such as (:use foo), though we also allow
; (:enable foo) and other such; more on uhs below.

; (list uhs c1 c2)   ; each ci a list of checkpoints (top-level for c1, under
;                    ; induction for c2)
; (list uhs :fail)   ; as above, but where failure produced no checkpoints
; (list uhs :remove) ; the indicated hint setting can be removed

; The main purpose here is to identify hint settings that might be useful in
; other proofs, due their being critical for the current proof.  So for
; example, if removing (:use foo) causes the current proof to fail, then maybe
; (:use foo) is helpful in other proofs too.  To that end, we don't restrict
; ourselves to removing entire hint settings; in some cases we allow removal of
; part of a hint setting.  Here are examples.

; :use (e1 e2 e3) generates uhs keys of:
;   (:use e1) when replacing by (:use e1 e2);
;   (:use e2) when replacing by (:use e1 e3); and
;   (:use e3) when replacing by (:use e1 e2).

; :do-not '(p1 p2 p3) generates uhs keys of:
;   (:do-not '(p1) when replacing by (:do-not '(p2 p3));
;   (:do-not '(p2) when replacing by (:do-not '(p1 p3)); and
;   (:do-not '(p2) when replacing by (:do-not '(p1 p2)).

; :expand e1 e2 e3 generates uhs keys of:
;   (:expand e1) when replacing by (:expand e1 e2);
;   (:expand e2) when replacing by (:expand e1 e3); and
;   (:expand e3) when replacing by (:expand e1 e2).

; And for special cases of :in-theory we have the following (similarly for the
; ruleset versions disable*, enable*, and e/d*).

; :in-theory (disable d1 d2 d3) generates uhs keys of:
;   (:disable d1) when replacing by (disable d2 d3);
;   (:disable d2) when replacing by (disable d1 d3); and
;   (:disable d3) when replacing by (disable d1 d2).

; :in-theory (enable e1 e2 e3) generates uhs keys of:
;   (:enable e1) when replacing by (enable e2 e3);
;   (:enable e2) when replacing by (enable e1 e3); and
;   (:enable e3) when replacing by (enable e1 e2).

; :in-theory (e/d (e1 e2 e3) (d1 d2 d3) generates uhs keys of:
;   (:enable e1) when replacing by (e/d (e2 e3) (d1 d2 d3))
;   (:enable e2) when replacing by (e/d (e1 e3) (d1 d2 d3)); and
;   (:enable e3) when replacing by (e/d (e1 e2) (d1 d2 d3)).
;   (:disable d1) when replacing by (e/d (e1 e2 e3) (d2 d3))
;   (:disable d2) when replacing by (e/d (e1 e2 e3) (d1 d3)); and
;   (:disable d3) when replacing by (e/d (e1 e2 e3) (d1 d2)).

; Note that we could probably do something similar for :hands-off and :restrict
; to what we do for :use, and :expand, but those are rare so it's probably not
; worth the bother.

  (cond
   ((or (null time-limit)
        (null thints)
        (ld-skip-proofsp state))
    (value nil))
   (t
    (let* ((goal-hint-settings
            (cdr (assoc-equal *initial-clause-id* thints)))
           (untranslated-goal-hint-settings
            (and goal-hint-settings
                 (alistp hints)
                 (cdr (assoc-string-equal "goal" hints)))))
      (cond
       ((not (and untranslated-goal-hint-settings
                  (keyword-value-listp untranslated-goal-hint-settings)
                  (rmh-keys-equal untranslated-goal-hint-settings
                                  goal-hint-settings)))
        (value nil))
       (t
        (mv-let
          (erp val state)
          (with-output!
            :off :all
            :gag-mode nil
            (state-global-let*
             ((abort-soft nil)) ; interrupts abort immediately to the top level
             (rmh-checkpoints-1
              term pspv
              nil nil
              untranslated-goal-hint-settings goal-hint-settings
              (remove-assoc-equal *initial-clause-id* thints)
              time-limit event-form ens wrld ctx state nil)) )
          (value (and (null erp) (reverse val))))))))))
