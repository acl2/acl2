; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann (with inspiration from Alessandro Coglio and Eric Smith)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See "NOTE: An interesting difference ...." near the top of
; simplify-defun-sk-impl.lisp.

(in-package "APT")

(include-book "simplify-defun-impl")

(program)
(set-state-ok t)

(defun fn-simp-defs-term (uterm tterm hyps theory equiv expand simplify-body
                                untranslate must-simplify ctx state)
  (b* ((wrld (w state))
       (fn-runes 'acl2::*simplify-term-runes*)
       ((er thyps) (translate-hyp-list hyps nil ctx wrld state))
       ((er address-subterm-governors-lst)
        (if (not (booleanp simplify-body)) ; then non-nil value (or, error)
            (ext-address-subterm-governors-lst-state
             simplify-body tterm ctx state)
          (value (list (list* nil tterm nil nil)))))
       (hints-from-theory+expand (theory+expand-to-hints theory expand))
       ((er thints)
        (translate-hints ctx hints-from-theory+expand ctx wrld state))
       ((er body-result)
        (fn-simp-body nil nil nil simplify-body tterm thyps
                      address-subterm-governors-lst
                      (geneqv-from-g?equiv equiv wrld)
                      thints must-simplify nil ctx wrld state))
       (sterm (access fn-simp-body-result body-result :body))
       (new-uterm
        (let ((iff-flg

; We use iff-flg below to produce an untranslated term from sterm.  For
; example, with iff-flg = t, (untranslate '(if x 't y) iff-flg wrld) = (OR X
; Y); but with iff-flg = nil, the result is (IF X T Y).  Thus, it suffices that
; iff-flg refines equiv.  But to check that would require proof, so we insist
; -- at least until a complaint comes along -- that equiv is exactly iff in
; order to use iff-flg = t.  There is no soundness issue here, because the
; untranslation for iff-flg = nil is always correct.

               (eq equiv 'iff)))
          (cond
           ((eq untranslate t)
            (untranslate sterm iff-flg wrld))
           ((eq untranslate nil)
            sterm)
           (t (let ((stobjs-out-exec
                     (acl2::term-stobjs-out tterm
                                            (table-alist 'nth-aliases-table wrld)
                                            wrld)))
                (cond
                 ((eq untranslate :nice-expanded)
                  (directed-untranslate-no-lets
                   uterm tterm sterm iff-flg stobjs-out-exec wrld))
                 (t ; :nice
                  (directed-untranslate uterm tterm sterm iff-flg
                                        stobjs-out-exec wrld))))))))
       ((er -)
        (cond ((and simplify-body
                    must-simplify)
               (check-simplified uterm tterm new-uterm sterm "" ctx state))
              (t (value nil))))
       (runes (merge-sort-lexorder (access fn-simp-body-result body-result
                                           :runes))))
    (value
     (list new-uterm
           `(defconst ,fn-runes
; WARNING: Do not change the caddr of this form without considering the effect
; on the printing of runes done in simplify-term-form.
              ',(acl2::drop-fake-runes runes))))))

(defconst *simplify-term-fn*
  'acl2::simplify-term-thm)

(defun simplify-term-new-name (thm-name ctx wrld state)
  (cond ((member-eq thm-name '(nil :auto))
         (value (cond ((acl2::logical-namep *simplify-term-fn* wrld)
                       (next-numbered-name *simplify-term-fn* wrld))
                      (t *simplify-term-fn*))))
        (t (er-progn (ensure-symbol-new-event-name
                      thm-name
                      (msg "The name ~x0, which is the name proposed for the ~
                            theorem equating the given term with its ~
                            simplification,"
                           thm-name)
                      :bad-input nil ctx state)
                     (value thm-name)))))

(defun simplify-term-defthm (uterm new-uterm hyps new-name thm-enable
                                   runes-name equiv expand rule-classes)
  (list* (if thm-enable 'defthm 'defthmd)
         new-name
         (implicate-untranslated-terms
          hyps
          (list equiv uterm new-uterm))
         :hints
         (theory+expand-to-hints runes-name expand) ; known non-nil
         (and (not (eq rule-classes :rewrite))
              (list :rule-classes rule-classes))))

(defun simplify-term-form (uterm assumptions theory equiv
                                 expand thm-name thm-enable
                                 simplify-body untranslate must-simplify
                                 rule-classes verbose ctx state)

; Actually returns (when not an error) the value (cons full-form defun-sk-form).

  (b* ((wrld (w state))
       ((er tterm)
        (acl2::translate uterm t t t ctx wrld state))
       ((er fn-simp-defs)
        (fn-simp-defs-term uterm tterm assumptions theory equiv expand
                           simplify-body untranslate must-simplify ctx state))
       (new-uterm
        (nth 0 fn-simp-defs))
       (state (cond (verbose
                     (fms "Proposed simplified term:~|~x0~%"
                          (list (cons #\0 new-uterm))
                          (standard-co state) state nil))
                    (t state)))
       (runes-def
        (nth 1 fn-simp-defs)) ; (defconst *foo-runes* ...)
       (state (cond (verbose
                     (fms "List of runes used in simplification:~|~x0~%"
                          (list (cons #\0 (unquote (caddr runes-def))))
                          (standard-co state) state nil))
                    (t state)))
       ((er new-name)
        (simplify-term-new-name thm-name ctx wrld state))
       (thm
        (simplify-term-defthm uterm new-uterm assumptions new-name thm-enable
                              (cadr runes-def) equiv expand rule-classes))
       ((er -)
        (acl2::translate-rule-classes
         new-name rule-classes
         (caddr thm) ; formula of the thm
         ctx (ens state) wrld state)))
    (value
     `(encapsulate-report-errors
       ,ctx
        nil
        (logic)
        (set-inhibit-warnings "theory")
        (local ,runes-def)
        (encapsulate
          ()
          ,(simplify-defun-heuristics nil)
          (local (set-default-hints nil))
          (local (set-override-hints nil))
          ,thm)))))

#!acl2
(defun simplify-term-event (uterm assumptions theory enable disable equiv
                                  expand thm-name thm-enable
                                  simplify-body untranslate must-simplify
                                  rule-classes verbose ctx state)
  (acl2::with-simplify-setup
   (b* (((unless (member-eq untranslate
                            apt::*untranslate-specifier-keywords*))
         (er soft ctx
             "The value of keyword :UNTRANSLATE for SIMPLIFY-TERM must be ~
              ~v0.  The value ~x1 is thus illegal."
             apt::*untranslate-specifier-keywords*
             untranslate))
        ((er theory)
         (apt::simplify-defun-theory nil theory enable disable ctx state))
        ((er must-simplify)
         (apt::check-must-simplify must-simplify ctx state))
        ((er equiv)
         (apt::check-equivalence-relation equiv ctx wrld state))
        (expand (apt::fix-expand-hint expand))
        (must-simplify (if (eq must-simplify ':default)
                           t
                         must-simplify))
        ((er form)
         (apt::simplify-term-form uterm assumptions theory equiv
                                  expand thm-name thm-enable
                                  simplify-body untranslate must-simplify
                                  rule-classes verbose ctx state)))
     (value form))))
