; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann (with inspiration from Alessandro Coglio and Eric Smith)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; TODO items to consider doing:

; - Deal with FIXMEs below.

; NOTE: An interesting difference between the implementations of simplify-defun
; and simplify-defun-sk is that the former goes out of its way to incorporate
; the acl2::congruence-theory into the set of runes created, while
; simplify-defun-sk does not.  Why is that?  One reason, and perhaps the only
; one, is that the before-vs-after lemmas supporting a call of simplify-defun
; use the generated equivalence relation at a subterm specified by
; :simplify-body.  This is unnecessary for simplify-defun-sk or simplify-term,
; because a single equality (or equivalence) lemma is generated for the entire
; body or term, respectively.  Thus, simplify-defun is optimized in the sense
; that rewriting is restricted to the relevant subterms; calls outside the
; subterms are not rewritten.  This difference could be rationalized (perhaps
; eliminated) in the future if the need arises, either by simplifying the
; implementation of simplify-defun to make it agree with the implementations of
; simplify-defun-sk and simplify-term, or instead, applying the finer-grained
; simplification performed by simplify-defun to the implementations of
; simplify-defun-sk and simplify-term.

(in-package "APT")

(include-book "simplify-defun-impl")
(include-book "kestrel/std/system/defun-sk-queries" :dir :system) ; for defun-sk
(include-book "kestrel/utilities/apply-fn-if-known" :dir :system) ; for defun-sk2
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)

(program)
(set-state-ok t)

(defun fn-simp-defs-sk (fn fn-simp hyps theory expand simplify-body
                           skolem-name guard guard-hints
                           verify-guards rewrite untranslate must-simplify
                           fn-simp-is-fn-name verbose ctx state)

; See fn-simp-defs for the analogous function to use when fn is defined by
; defun; here, fn is defined by defun-sk.

; Note that new-enable isn't handled here, but rather, in the caller.

  (b* ((wrld (w state))
       (fn-runes (fn-runes-name fn wrld))
       ((unless (defun-sk-p fn wrld))
        (er soft ctx
            "The symbol ~x0 was not introduced by ~x1."
            fn 'defun-sk))
       (formals (formals fn wrld))
       (quantifier (defun-sk-quantifier fn wrld))
       (bound-vars (defun-sk-bound-vars fn wrld))
       (matrix (defun-sk-matrix fn wrld))
       (untrans-matrix (defun-sk-imatrix fn wrld))
       (rewrite-kind (and (eq rewrite :auto) ; optimization
                          (defun-sk-rewrite-kind fn wrld)))
       (strengthen (defun-sk-strengthen fn wrld))
       (non-executable (non-executablep fn wrld))
       (verify-guards-eagerness (default-verify-guards-eagerness wrld))
       (verify-guards
         (cond
          ((not (eq verify-guards :auto))
           verify-guards)
          (t (case verify-guards-eagerness
               (0 nil)
               (1 (cond ((eq guard :auto)
                         (eq (symbol-class fn wrld)
                             :common-lisp-compliant))
                        (t ; :guard explicitly supplied
                         t)))
               (2 t)
               (otherwise
                (er hard 'fn-simp-defs-sk
                    "Unexpected value ~x0 for ~x1!"
                    verify-guards-eagerness
                    '(default-verify-guards-eagerness (w state))))))))
       (stobjs-out-exec (and (not non-executable)
                             (stobjs-out fn wrld)))
       (on-failure-msg
        (msg "Guard verification has failed for ~x0.  See :DOC ~
              apt::simplify-failure for some ways to address this failure."
             fn-simp))
       ((er sofunp)
        (apply-fn-if-known "SOFT" "SOFUNP" (list fn wrld) state))
       (defun-sk?
         (if sofunp
             'defun-sk2
           'defun-sk))
       ((er thyps) (translate-hyp-list hyps fn ctx wrld state))
       ((er address-subterm-governors-lst)
        (if (not (booleanp simplify-body)) ; then non-nil value (or, error)
            (ext-address-subterm-governors-lst-state
             simplify-body matrix ctx state)
          (value (list (list* nil matrix nil nil)))))
       (fn-simp-alist `((,fn . ,fn-simp)))
       (hints-from-theory+expand (theory+expand-to-hints theory expand))
       ((er thints)
        (translate-hints ctx hints-from-theory+expand ctx wrld state))
       ((er body-result)
        (fn-simp-body fn fn-simp nil simplify-body matrix thyps
                      address-subterm-governors-lst *geneqv-iff* thints
                      must-simplify fn-simp-alist ctx wrld state))
       (simp-body (sublis-fn-simple fn-simp-alist
                                    (access fn-simp-body-result
                                            body-result
                                            :body)))
       (untrans-simp-body
        (cond
         ((eq untranslate t)
          (untranslate simp-body t wrld))
         ((eq untranslate nil)
          simp-body)
         ((eq untranslate :nice-expanded)
          (directed-untranslate-no-lets
           untrans-matrix matrix simp-body t stobjs-out-exec wrld))
         (t ; :nice
          (directed-untranslate untrans-matrix matrix simp-body t
                                stobjs-out-exec wrld))))
       ((er -)
        (cond ((and simplify-body
                    must-simplify)
               (check-simplified untrans-matrix matrix
                                 untrans-simp-body simp-body
                                 "" ctx state))
              (t (value nil))))
       (runes (merge-sort-lexorder (access fn-simp-body-result body-result
                                           :runes)))
       (guard-decl
        (cond ((eq guard :auto)
               (let ((guard (guard-raw fn wrld)))
                 (cond ((equal guard t)
                        (cond ((eql verify-guards-eagerness 2)
                               '(declare (xargs :verify-guards nil)))
                              (t nil)))
                       (t `(declare (xargs :guard ,guard
                                           :verify-guards nil))))))
              (t `(declare (xargs :guard ,guard
                                  :verify-guards nil)))))
       (rewrite-lst
        (cond ((not (eq rewrite :auto))
               (and rewrite `(:rewrite ,rewrite)))
              ((eq rewrite-kind :default)
               nil)
              ((eq rewrite-kind :direct)
               '(:rewrite :direct))
              (t
               (assert$
                (eq rewrite-kind :custom)

; FIXME: We should deal properly with this case.  Here is a comment from
; Alessandro.

;   I think that simplify-defthm would be useful in general. You re right that
;   the effect of a custom rewrite rule is similar to proving a theorem after
;   the defun-sk, but the difference is that the theorem is not "linked" to the
;   function as the :thm-name is - in particular, the quantfun utilities will
;   retrieve TEMP in that case. We could work around this issue via a
;   user-defined table that associates to defun-sk's generated by
;   transformations, their rewrite rule, and have our transformations handle
;   these appropriately. But it would be probably cleaner, if possible, to
;   generate the right rewrite rule as part of the generated defun-sk.

; Probably this should be an error so that the user can be directed to specify
; a value for :rewrite in the call of simplify-defun-sk.  But for now I won't
; rock the boat.

                nil))))
       (verify-guards-form
        (and verify-guards
             `(verify-guards ,fn-simp
                :hints
                ,(fn-simp-defs-verify-guards-hints
                  guard-hints fn wrld
                  `((quote (:in-theory ,theory)))
                  `(cons ',fn-simp-is-fn-name
                         ,fn-runes)
                  `(cons ',fn-simp-is-fn-name
                         ,theory)
                  verbose)))))
    (value
     `((,defun-sk? ,fn-simp ,formals
         ,@(and (not non-executable)
                '((declare (xargs :non-executable nil))))
         ,@(and guard-decl
                (list guard-decl))
         (,quantifier ,bound-vars ,untrans-simp-body)
         :quant-ok t
         ,@(and strengthen
                '(:strengthen t))
         ,@(and skolem-name
                `(:skolem-name ,skolem-name))
         ,@rewrite-lst)
       (defconst ,fn-runes
; WARNING: Do not change the caddr of this form without considering the effect
; on the printing of runes done in simplify-defun-sk-form.
         ',(acl2::drop-fake-runes runes))
       ,(and verify-guards-form
             `(on-failure
               ,verify-guards-form
               :ctx ,ctx
               :erp :condition-failed
               :val nil
               :msg ,on-failure-msg))
       ,untrans-matrix
       ,untrans-simp-body))))

(defun fn-simp-is-fn-sk-subst-mv (len bound-vars witness2-formals acc)
  (cond ((zp len) acc)
        (t (let ((index (1- len)))
             (fn-simp-is-fn-sk-subst-mv
              index
              (cdr bound-vars)
              witness2-formals
              (cons (list (car bound-vars)
                          (list 'mv-nth index witness2-formals))
                    acc))))))

(defun fn-simp-is-fn-sk-subst (fn wrld)

; See fn-simp-is-fn-sk-computed-hint.

  (let* ((bound-vars (defun-sk-bound-vars fn wrld))
         (len (length bound-vars))
         (witness-formals-call (cons (defun-sk-witness fn wrld)
                                     (formals fn wrld))))
    (if (eql len 1)
        (list (list (car bound-vars)
                    witness-formals-call))
      (fn-simp-is-fn-sk-subst-mv len
                                 (reverse bound-vars)
                                 witness-formals-call
                                 nil))))

(defun fn-simp-is-fn-sk-computed-hint (fn fn-simp lemma-name wrld)

; Note that fn-runes is expected to (have evaluated to) a symbol, e.g.,
; *foo-runes*.  Note also that at the time this function is called, both
; fn-runes and fn-simp will have been defined.

; Here is an example of what this function should return for fn = f$1, defined
; as follows: (defun-sk f$1 (lst) (forall (x y) ...)).

;   (:in-theory
;    '(f$1 f$2)
;    :use ((:instance <becomes-lemma>
;                     (x (mv-nth 0 (f$2-witness lst)))
;                     (y (mv-nth 1 (f$2-witness lst))))
;          (:instance <becomes-lemma>
;                     (x (mv-nth 0 (f$1-witness lst)))
;                     (y (mv-nth 1 (f$1-witness lst))))
;          (:instance f$1-necc
;                     (x (mv-nth 0 (f$2-witness lst)))
;                     (y (mv-nth 1 (f$2-witness lst))))
;          (:instance f$2-necc
;                     (x (mv-nth 0 (f$1-witness lst)))
;                     (y (mv-nth 1 (f$1-witness lst))))))

  (list
   :in-theory
   `(quote (,fn ,fn-simp))
   :use
   (let ((subst1 (fn-simp-is-fn-sk-subst fn wrld))
         (subst2 (fn-simp-is-fn-sk-subst fn-simp wrld)))
     (list (list* :instance
                  lemma-name
                  :extra-bindings-ok
                  subst2)
           (list* :instance
                  lemma-name
                  :extra-bindings-ok
                  subst1)
           (list* :instance
                  (defun-sk-rewrite-name fn wrld)
                  :extra-bindings-ok
                  subst2)
           (list* :instance
                  (defun-sk-rewrite-name fn-simp wrld)
                  :extra-bindings-ok
                  subst1)))))

(defun fn-simp-is-fn-sk-lemma (fn fn-simp hyps matrix matrix-simp theorem-name
                                  expand state)
  (let* ((wrld (w state))
         (fn-runes (fn-runes-name fn wrld))
         (lemma-name (fn-simp-is-fn-lemma-name fn fn-simp theorem-name wrld)))
    `(defthm ,lemma-name
       ,(implicate-untranslated-terms hyps
                                      `(iff ,matrix ,matrix-simp))
       :hints ,(theory+expand-to-hints fn-runes expand)
       :rule-classes nil)))

(defun fn-simp-is-fn-sk/computed-hint-call (fn fn-simp hyps theorem-name
                                               thm-enable state)
  (let* ((wrld (w state))
         (fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-simp-call (cons fn-simp fn-formals))
         (equality `(iff ,fn-call ,fn-simp-call))
         (main-name (fn-simp-is-fn-name fn fn-simp theorem-name wrld))
         (lemma-name (fn-simp-is-fn-lemma-name fn fn-simp theorem-name wrld))
         (defthm? (if thm-enable 'defthm 'defthmd)))
    (mv `(,defthm? ,main-name
           ,(implicate-untranslated-terms hyps equality))
        `(fn-simp-is-fn-sk-computed-hint ',fn ',fn-simp ',lemma-name world))))

(defun simplify-defun-sk-form (fn hyps theory expand
                                  theorem-name new-name
                                  thm-enable new-enable
                                  simplify-body skolem-name
                                  guard guard-hints
                                  verify-guards rewrite untranslate
                                  must-simplify verbose ctx state)

; Actually returns (when not an error) the value (cons full-form defun-sk-form).

  (b* (((er fn-simp)
        (fn-simp-name fn new-name ctx state))
       (fn-simp-is-fn-name (fn-simp-is-fn-name fn fn-simp theorem-name
                                               (w state)))
       ((er fn-simp-defs)
        (fn-simp-defs-sk fn fn-simp hyps theory expand simplify-body
                         skolem-name guard guard-hints
                         verify-guards rewrite untranslate must-simplify
                         fn-simp-is-fn-name
                         verbose ctx state))
       (new-defun
        (nth 0 fn-simp-defs)) ; (defun-sk foo$1 ...)
       (state (cond (verbose
                     (fms "Proposed simplified definition:~|~x0~%"
                          (list (cons #\0 new-defun))
                          (standard-co state) state nil))
                    (t state)))
       (runes-def
        (nth 1 fn-simp-defs)) ; (defconst *foo-runes* ...)
       (state (cond (verbose
                     (fms "List of runes used in simplification for ~x0:~|~x1~%"
                          (list (cons #\0 fn)
                                (cons #\1 (unquote (caddr runes-def))))
                          (standard-co state) state nil))
                    (t state)))
       (verify-guards-form
        (nth 2 fn-simp-defs))
       (matrix
        (nth 3 fn-simp-defs))
       (matrix-simp
        (nth 4 fn-simp-defs))
       (fn-simp-is-fn-lemma
        (fn-simp-is-fn-sk-lemma fn fn-simp hyps matrix matrix-simp theorem-name
                                expand state))
       ((mv fn-simp-is-fn computed-hint-call)
        (fn-simp-is-fn-sk/computed-hint-call fn fn-simp hyps theorem-name
                                             thm-enable state))
       ((mv not-norm-event - -)
        (install-not-normalized-event fn t nil (w state))))
    (value
     `(encapsulate-report-errors
       ,ctx
        nil
        (logic)
        (set-inhibit-warnings "theory")
        (set-ignore-ok t)
        (set-irrelevant-formals-ok t)
        ,not-norm-event
        ,new-defun
        ,@(and verify-guards-form (list verify-guards-form))
        (local ,runes-def)
        (local (encapsulate
                 ()
                 ,(simplify-defun-heuristics nil)
                 (local (set-default-hints nil))
                 (local (set-override-hints nil))
                 ,fn-simp-is-fn-lemma))

; By keeping the computed hint separate from the fn-simp-is-fn theorem, we
; produce a prettier theorem event form.

        (set-default-hints '(,computed-hint-call))
        ,fn-simp-is-fn
        ,@(and (not new-enable)
               `((in-theory (disable ,fn-simp))))))))

(defun simplify-defun-sk-event (fn assumptions
                                   theory enable disable
                                   expand
                                   theorem-name new-name
                                   thm-enable new-enable
                                   simplify-body skolem-name
                                   guard guard-hints verify-guards
                                   rewrite untranslate must-simplify
                                   verbose ctx state)
  (acl2::with-simplify-setup
   (b* ((wrld (w state))
        ((unless (and (function-namep fn wrld)
                      (definedp fn wrld)))
         (er soft ctx
             "The first argument to the SIMPLIFY transformation must be a ~
              defined function symbol, but ~x0 is not."
             fn))
        ((unless (member-eq untranslate
                            *untranslate-specifier-keywords*))
         (er soft ctx
             "The value of keyword :UNTRANSLATE for ~x0 must be ~v1.  The ~
              value ~x2 is thus illegal."
             'simplify-defun-sk
             *untranslate-specifier-keywords*
             untranslate))
        ((er theory)
         (simplify-defun-theory
          (clique-runic-designators (list fn))
          theory enable disable ctx state))
        (rune (fn-rune-nume fn nil nil wrld))
        (new-enable (if (eq new-enable :auto)
                        (and rune ; true if we've done enough error checking?
                             (enabled-runep rune (ens state) wrld))
                      new-enable))
       ((er hyps) (assumptions-to-hyps assumptions nil fn
                                       (and (not (eq guard :auto))

; In the case of defun-sk, simplify allows a :guard, which we use when an
; assumption is specified as :guard.

                                            guard)
                                       ctx wrld state))
        (expand (fix-expand-hint expand))
        (must-simplify (if (eq must-simplify ':default)
                           t
                         must-simplify))
        ((er form)
         (simplify-defun-sk-form
          fn hyps
          theory expand
          theorem-name new-name
          thm-enable new-enable
          simplify-body skolem-name guard guard-hints
          verify-guards rewrite untranslate must-simplify
          verbose ctx state)))
     (value form))))
