; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "APT")

(program)
(set-state-ok t)

(include-book "simplify-defun-impl")
(include-book "simplify-defun-sk-impl")
(include-book "simplify-term-impl")
(include-book "utilities/deftransformation")

(defun check-simplify-defaults (triples fn type ctx state bad)

; This little utility checks that arguments intended for simplify-defun are not
; passed to simplify-defun-sk, and vice-versa.

; Our intention is to check that for every triple (:kwd val default) in
; triples, val equals default -- and when that fails, report that :kwd has been
; given the value value which is not its default.  The purpose is to use msg to
; tell the user when a supplied value for :kwd is nonsensical because :kwd is
; not used in the appropriate transformation, xform.  Bad is initially nil, and
; accumulates the bad keywords.

; A better check would be whether :kwd is supplied, rather than whether its val
; is the default.  But we currently don't have that information available by
; the caller (it seems awkward to provide).

  (cond ((endp triples)
         (cond (bad (er-soft+ ctx :bad-input nil
                      "The transformation ~x0 has been called on ~x1 with ~
                       keyword argument~#2~[~/s~] ~&2, which ~#2~[is~/are~] ~
                       illegal because ~x1 ~#3~[was defined using ~
                       defun-sk~/was defined using defun~/is a term to be ~
                       simplified~]."
                      'simplify
                      fn
                      bad
                      (case type
                        (:defun-sk 0)
                        (:defun 1)
                        (t 2))))
               (t (value nil))))
        (t (check-simplify-defaults
            (cdr triples) fn type ctx state
            (cond ((not (equal (cadr (car triples))
                               (caddr (car triples))))
                   (cons (caar triples) bad))
                  (t bad))))))

(defun simplify-event (fn assumptions hyp-fn
                          theory enable disable
                          equiv expand
                          hints
                          thm-name new-name
                          thm-enable new-enable
                          simplify-body
                          simplify-guard guard-hints
                          verify-guards
                          simplify-measure
                          measure-hints measure
                          untranslate must-simplify non-executable
                          rewrite guard skolem-name ; only for simplify-defun-sk
                          rule-classes
                          print-expand ctx state)
  (cond ((and (consp fn)
              (not (eq (car fn) 'quote)))
         (er-progn
          (check-simplify-defaults
           `((:hyp-fn ,hyp-fn nil)
             (:hints ,hints nil)
             (:guard ,guard :auto)
             (:guard-hints ,guard-hints :auto)
             (:measure ,measure :auto)
             (:measure-hints ,measure-hints :auto)
             (:new-name ,new-name nil)
             (:new-enable ,new-enable :auto)
             (:non-executable ,non-executable :auto)
             (:skolem-name ,skolem-name nil)
             (:simplify-guard ,simplify-guard nil)
             (:simplify-measure ,simplify-measure nil)
             (:verify-guards ,verify-guards :auto))
           fn :term ctx state nil)
          (acl2::simplify-term-event fn ; uterm (untranslated term)
                                     assumptions
                                     theory enable disable
                                     equiv
                                     expand
                                     thm-name
                                     thm-enable
                                     simplify-body untranslate must-simplify
                                     rule-classes
                                     print-expand ctx state)))
        ((not (and (symbolp fn)
                   (function-symbolp fn (w state))))
         (er soft ctx
             "The first argument of the SIMPLIFY transformation must either ~
              be a known function symbol or a term that is neither a variable ~
              nor a constant.  The argument ~x0 is thus illegal."
             fn))
        ((defun-sk-p fn (w state))
         (er-progn
          (check-simplify-defaults
           `((:equiv ,equiv nil)
             (:hyp-fn ,hyp-fn nil)
             (:hints ,hints nil)
             (:measure ,measure :auto)
             (:measure-hints ,measure-hints :auto)
             (:non-executable ,non-executable :auto)
             (:rule-classes ,rule-classes :rewrite)
             (:simplify-guard ,simplify-guard nil)
             (:simplify-measure ,simplify-measure nil))
           fn :defun-sk ctx state nil)
          (simplify-defun-sk-event fn assumptions
                                   theory enable disable
                                   expand
                                   thm-name new-name
                                   thm-enable new-enable
                                   simplify-body skolem-name
                                   guard guard-hints verify-guards
                                   rewrite untranslate must-simplify
                                   print-expand ctx state)))
        ((getpropc fn 'unnormalized-body nil (w state))
         (er-progn
          (check-simplify-defaults
           `((:rewrite ,rewrite :auto)
             (:guard ,guard :auto)
             (:rule-classes ,rule-classes :rewrite)
             (:skolem-name ,skolem-name nil))
           fn :defun ctx state nil)
          (simplify-defun-event fn assumptions hyp-fn
                                theory enable disable
                                equiv expand
                                hints
                                thm-name new-name
                                thm-enable new-enable
                                simplify-body
                                simplify-guard guard-hints
                                verify-guards
                                simplify-measure
                                measure-hints measure
                                untranslate must-simplify non-executable
                                print-expand ctx state)))
        (t (er soft ctx
               "The function symbol ~x0 was not introduced with defun or ~
                defun-sk."
               fn))))

(acl2::deftransformation
 simplify

; Some implementation notes on simplify-defun:

; Note that simplification of the guard is done without assuming the
; :assumptions, since the :assumptions might simplify the guard away.  The
; measure's simplification also does not use the :assumptions; consider for
; example the case that :assumptions is (natp x), which might be the guard, and
; the measure is (nfix x), which must not simplify to x.

; As things currently stand, if :simplify-body is non-nil then the body must
; simplify; but we do not make the analogous requirement for :simplify-guard or
; :simplify-measure.

; Note that :simplify-body may be a pattern.  See :doc simplify-defun.

 (fn)
 ((assumptions 'nil) ; Consider ':guard instead?
  (hyp-fn 'nil)
  (theory ':none)
  (enable ':none)
  (disable ':none)
  (equiv 'nil)
  (expand 'nil)
  (hints 'nil)
  (thm-name ':auto)
  (new-name 'nil)
  (thm-enable 't)
  (new-enable ':auto)
  (simplify-body 't)     ; can be t, nil, or pattern
  (simplify-guard 'nil)  ; will likely change to 't
  (guard-hints ':auto)
  (verify-guards ':auto)
  (simplify-measure 'nil) ; will likely change to 't
  (measure-hints ':auto)
  (measure ':auto)
  (untranslate ':nice)
  (must-simplify ':default)
  (non-executable ':auto)
  (rewrite ':auto)
  (guard ':auto)
  (skolem-name 'nil)
  (rule-classes ':rewrite))
 :revert-world t
 :pass-print t
 :pass-context t)

(defmacro acl2::simplify (&rest args)
  `(simplify ,@args))
(defmacro acl2::show-simplify (&rest args)
  `(show-simplify ,@args))
(defmacro acl2::simplify-programmatic (&rest args)
  `(simplify-programmatic ,@args))

(defmacro simplify-defun (&rest args)
  `(simplify ,@args))
(defmacro acl2::simplify-defun (&rest args)
  `(simplify-defun ,@args))

(defmacro show-simplify-defun (&rest args)
  `(show-simplify ,@args))
(defmacro acl2::show-simplify-defun (&rest args)
  `(show-simplify-defun ,@args))

(defmacro simplify-defun-programmatic (&rest args)
  `(simplify-programmatic ,@args))
(defmacro acl2::simplify-defun-programmatic (&rest args)
  `(simplify-defun-programmatic ,@args))

(defmacro simplify-defun-sk (&rest args)
  `(simplify ,@args))
(defmacro acl2::simplify-defun-sk (&rest args)
  `(simplify-defun-sk ,@args))

(defmacro show-simplify-defun-sk (&rest args)
  `(show-simplify ,@args))
(defmacro acl2::show-simplify-defun-sk (&rest args)
  `(show-simplify-defun-sk ,@args))

(defmacro simplify-defun-sk-programmatic (&rest args)
  `(simplify-programmatic ,@args))
(defmacro acl2::simplify-defun-sk-programmatic (&rest args)
  `(simplify-defun-sk-programmatic ,@args))

(defmacro simplify-term (&rest args)
  `(simplify ,@args))
(defmacro acl2::simplify-term (&rest args)
  `(simplify-term ,@args))

(defmacro show-simplify-term (&rest args)
  `(show-simplify ,@args))
(defmacro acl2::show-simplify-term (&rest args)
  `(show-simplify-term ,@args))

(defmacro simplify-term-programmatic (&rest args)
  `(simplify-programmatic ,@args))
(defmacro acl2::simplify-term-programmatic (&rest args)
  `(simplify-term-programmatic ,@args))

; for compatibility with other transformations:
(set-numbered-name-index-start "$")
(set-numbered-name-index-end "")
(set-paired-name-separator "-BECOMES-")
