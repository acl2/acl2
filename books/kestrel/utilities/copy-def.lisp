; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; NOTE: Documentation may come later.  Also, several definitions below are
; quite general in nature and, as noted below, may be moved to a more general
; utilities book.  An example at the end shows how to use copy-def to avoid
; induction proofs by using functional instantiation.

; The new definition is not guard-verified.

(in-package "ACL2")

(include-book "kestrel/std/basic/symbol-package-name-non-cl" :dir :system)

(defun fn-copy-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern$ (concatenate 'string (symbol-name fn) "-COPY")
           (symbol-package-name-non-cl fn)))

(defun fn-copy-def-name (fn)
  (intern$ (concatenate 'string (symbol-name fn) "-COPY-DEF")
           (symbol-package-name-non-cl fn)))

; The following function might be moved to a more general utilities book.
(defun implicate-untranslated-terms (hyps concl)
  (declare (xargs :guard (true-listp hyps)))
  (cond ((null hyps) concl)
        ((null (cdr hyps))
         `(implies ,(car hyps) ,concl))
        (t
         `(implies (and ,@hyps) ,concl))))

(defun copy-def-signatures (alist wrld acc)
  (declare (xargs :mode :program))
  (cond
   ((endp alist) (reverse acc))
   (t (copy-def-signatures
       (cdr alist)
       wrld
       (let* ((fn (caar alist))
              (fn-copy (cdar alist))
              (fn-stobjs-in (stobjs-in fn wrld))
              (stobjs-in-pretty
               (and fn-stobjs-in ; leave nil as nil
                    (let ((tmp (prettyify-stobjs-out fn-stobjs-in)))
                      (if (atom tmp)
                          (list tmp)
                        (assert$ (eq (car tmp) 'mv)
                                 (cdr tmp))))))
              (stobjs-out-pretty (prettyify-stobjs-out (stobjs-out fn wrld))))
         (cons `((,fn-copy ,@stobjs-in-pretty) => ,stobjs-out-pretty)
               acc))))))

(defun copy-def-defuns (alist wrld acc)
  (declare (xargs :mode :program))
  (cond
   ((endp alist) (reverse acc))
   (t (copy-def-defuns
       (cdr alist)
       wrld
       (let* ((fn (caar alist))
              (fn-copy (cdar alist))
              (fn-formals (formals fn wrld))
              (fn-call (cons fn fn-formals)))
         (cons `(local (defun ,fn-copy ,fn-formals
                         (declare (xargs :normalize nil))
                         ,fn-call))
               acc))))))

(defun copy-def-defthms (alist-tail alist wrld theory clique controller-alist
                                    hyps-fn[-alist] equiv[-alist] acc)
  (declare (xargs :mode :program))
  (cond
   ((endp alist-tail) (reverse acc))
   (t (copy-def-defthms
       (cdr alist-tail) alist wrld theory clique controller-alist
       hyps-fn[-alist]
       equiv[-alist]
       (cons (let* ((fn (caar alist-tail))
                    (fn-copy (cdar alist-tail))
                    (fn-formals (formals fn wrld))
                    (fn-call (cons fn fn-formals))
                    (fn-copy-call (cons fn-copy fn-formals))
                    (hyps-fn (if (symbolp hyps-fn[-alist])
                                 hyps-fn[-alist]
                               (cdr (assoc-eq fn hyps-fn[-alist]))))
                    (hyps (and hyps-fn
                               (list (cons hyps-fn fn-formals))))
                    (equiv (if (symbolp equiv[-alist])
                               equiv[-alist]
                             (or (cdr (assoc-eq fn equiv[-alist]))
                                 'equal))))
               `(defthm ,(fn-copy-def-name fn)
                  ,(implicate-untranslated-terms
                    hyps
                    `(,equiv ,fn-copy-call
                             ,(sublis-fn-simple alist
                                                (body fn nil wrld))))
                  :hints (("Goal"
                           :in-theory ,theory
                           :expand (,fn-call)))
                  :rule-classes
                  ((:definition ; avoid normalizing
                    :install-body t
                    :clique ,clique
                    ,@(and controller-alist
                           `(:controller-alist ,controller-alist))))))
             acc)))))

(defun copy-def-encapsulate (alist hyps-fn[-alist] equiv[-alist] wrld)
  (declare (xargs :mode :program))
  (let ((theory (kwote (pairlis-x1 ':d (pairlis$ (strip-cdrs alist) nil))))
        (clique (strip-cdrs alist))
        (controller-alist (sublis alist
                                  (access def-body (def-body (caar alist) wrld)
                                          :controller-alist))))
    `(encapsulate
       ,(copy-def-signatures alist wrld nil)
       (set-verify-guards-eagerness 0)
       ,@(copy-def-defuns alist wrld nil)
       ,@(copy-def-defthms alist alist wrld theory clique controller-alist
                           hyps-fn[-alist] equiv[-alist] nil))))

(defun fn-is-fn-copy-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (concatenate 'string
                (symbol-name fn)
                "-IS-"
                (symbol-name (fn-copy-name fn)))
   fn))

(defun fn-is-fn-copy-runes (alist wrld acc)
  (declare (xargs :mode :program))
  (cond
   ((endp alist) (reverse acc))
   (t (fn-is-fn-copy-runes
       (cdr alist)
       wrld
       (let* ((fn (caar alist))
              (def-body (def-body fn wrld))
              (def-body-rune (if def-body
                                 (access def-body def-body :rune)
                               (er hard 'fn-is-fn-copy
                                   "Unexpected error!  (Sorry about the ~
                                    obscure error message; please send it to ~
                                    Matt, who will investigate.)"))))
         (list* def-body-rune
                (fn-copy-def-name fn)
                acc))))))

(defun fn-is-fn-copy (fn hyps-fn hyps-preserved-thm-names equiv flagp wrld)

; Flagp is either t, nil, or :none, with the following effects.

; t     - create a defthm event under a defthm-flag-xxx wrapper
; nil   - create a standalone defthm event
; :none - create a standalone defthm event that is to be redundant

  (declare (xargs :guard
                  (symbol-listp hyps-preserved-thm-names) ; partial guard
                  :mode :program))
  (let* ((fn-copy (fn-copy-name fn))
         (fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-copy-call (cons fn-copy fn-formals))
         (equality `(,equiv ,fn-call ,fn-copy-call))
         (hyps (and hyps-fn
                    (list (cons hyps-fn fn-formals))))
         (singly-recursivep (and (not flagp)
                                 (recursivep fn t wrld))))
    `(defthm ,(fn-is-fn-copy-name fn)
       ,(implicate-untranslated-terms hyps equality)
       ,@(and (eq flagp nil)
              `(:hints
                (("Goal"
                  ,@(and singly-recursivep `(:induct ,fn-call))
                  :expand (,fn-call ,fn-copy-call))
                 ,@(and hyps-preserved-thm-names
                        `('(:use (,@hyps-preserved-thm-names)))))))
       ,@(and (eq flagp t)
              `(:flag ,fn))
       :rule-classes nil)))

(defun fn-copy-alist (names acc)

; Given a list of function symbols FN, return a corresponding alist with
; entries (FN . FN-copy).

  (cond ((endp names) (reverse acc))
        (t (fn-copy-alist (cdr names)
                          (acons (car names)
                                 (fn-copy-name (car names))
                                 acc)))))

(defun fn-is-fn-copy-lst (alist hyps-fn[-alist] hyps-preserved-thm-names
                                equiv[-alist] flagp wrld acc)
  (declare (xargs :mode :program))
  (cond
   ((endp alist) (reverse acc))
   (t
    (fn-is-fn-copy-lst
     (cdr alist)
     hyps-fn[-alist] hyps-preserved-thm-names equiv[-alist] flagp wrld
     (cons (let ((fn (caar alist)))
             (fn-is-fn-copy fn
                            (if (symbolp hyps-fn[-alist])
                                hyps-fn[-alist]
                              (cdr (assoc-eq fn hyps-fn[-alist])))
                            hyps-preserved-thm-names
                            (if (symbolp equiv[-alist])
                                equiv[-alist]
                              (or (cdr (assoc-eq fn equiv[-alist]))
                                  'equal))
                            flagp wrld))
           acc)))))

(defun filter-defthm-names (candidates wrld acc)
  (cond ((endp candidates) (reverse acc))
        (t (filter-defthm-names
            (cdr candidates)
            wrld
            (if (getpropc (car candidates) 'theorem nil wrld)
                (cons (car candidates) acc)
              acc)))))

(defun congruence-runes (lst acc)
  (cond ((endp lst) acc)
        (t (congruence-runes (cdr lst)
                             (if (member-eq (caar lst)
                                            '(:congruence :equivalence))
                                 (cons (car lst) acc)
                               acc)))))

(defun congruence-theory-fn (logical-name wrld)
  (declare (xargs :mode :program))
  (congruence-runes (current-theory-fn logical-name wrld)
                    nil))

(defmacro congruence-theory (logical-name)

; Unlike current-theory, the result might not be a runic theory.

  (list 'congruence-theory-fn logical-name 'world))

(defun congruence-theory-extension (equiv world theory)
  (declare (xargs :mode :program))
  (cond ((eq equiv 'equal)
         theory)
        (t (append (congruence-theory :here)
                   theory))))

(defun copy-def-event (fn hyps-fn hyps-preserved-thm-names equiv flag-name wrld)
  (declare (xargs :mode :program))
  (let* ((hyps-fn[-alist] hyps-fn)
         (equiv[-alist] equiv)
         (recp (recursivep fn t wrld))
         (mut-rec-p (cdr recp))
         (alist (cond (mut-rec-p (fn-copy-alist recp nil))
                      (t (list (cons fn (fn-copy-name fn))))))
         (runes (fn-is-fn-copy-runes alist wrld nil))
         (encap (copy-def-encapsulate alist hyps-fn[-alist] equiv[-alist] wrld))
         (hyps-preserved-thm-names
          (filter-defthm-names (if (and hyps-preserved-thm-names
                                        (symbolp hyps-preserved-thm-names))
                                   (list hyps-preserved-thm-names)
                                 hyps-preserved-thm-names)
                               wrld
                               nil)))
    (cond
     ((not mut-rec-p)
      `(encapsulate
         ()
         ,encap
         (local (in-theory (congruence-theory-extension
                            ',equiv
                            world
                            '(,@(and recp `((:induction ,fn)))
                              ,@runes

; We have seen an example in which copy-def fails unless return-last is
; explicity enabled.  This presumably has something to do with :normalize nil,
; as it showed up when we messed with prog2$ in directed-untranslate.  It seems
; harmless and potentially useful simply to enable all guard-holders.  This
; list of guard-holders comes from inspecting the definition of
; remove-guard-holders1.

                              return-last mv-list cons-with-hint the-check))))
         ,(fn-is-fn-copy fn hyps-fn hyps-preserved-thm-names equiv nil
                         wrld)))
     (t
      (let* ((pkg (symbol-package-name-non-cl fn))
             (flag-name (or flag-name
                            (intern$ (concatenate 'string
                                                  "FLAG-"
                                                  (symbol-name fn))
                                     pkg)))
             (defthm-flag-name (intern$ (concatenate 'string
                                                     "DEFTHM-"
                                                     (symbol-name flag-name))
                                        pkg)))
        `(encapsulate
           ()
           (local (make-flag ,flag-name ,fn :last-body t))
           ,encap
           (local (in-theory (congruence-theory-extension
                              ',equiv
                              world
                              '((:induction ,flag-name)
                                ,(flag::equivalences-name flag-name)
                                ,@runes))))
           ,@(and hyps-preserved-thm-names
                  `((local (set-default-hints
                            '('(:use (,@hyps-preserved-thm-names)))))))
           (local
            (,defthm-flag-name
              ,@(fn-is-fn-copy-lst alist hyps-fn[-alist] nil equiv[-alist] t
                                   wrld nil)))
           ,@(fn-is-fn-copy-lst alist hyps-fn[-alist] nil equiv[-alist] :none
                                wrld nil)))))))

(defmacro copy-def (fn &key
                       hyps-fn ; can be an alist
                       hyps-preserved-thm-names
                       equiv
                       flag-name)
  (let ((equiv (or equiv 'equal)))
    `(make-event
      (copy-def-event ',fn ',hyps-fn
                      ',hyps-preserved-thm-names ',equiv ',flag-name (w state)))))

; The following example shows an example of what is generated by copy-def, and
; how to use copy-def to avoid induction proofs by using functional
; instantiation.

(local
 (progn

   (defun foo-1 (x)
     (if (consp x)
         (+ 1 1 (foo-1 (cdr x)))
       0))

   (defun foo-2 (x)
     (if (consp x)
         (+ 2 (foo-2 (cdr x)))
       0))

   (copy-def foo-1)

   (encapsulate
     ()
     (set-enforce-redundancy t) ; local to enclosing encapsulate

     (ENCAPSULATE
       (((FOO-1-COPY *) => *))
       (SET-VERIFY-GUARDS-EAGERNESS 0)
       (LOCAL (DEFUN FOO-1-COPY (X)
                (DECLARE (XARGS :NORMALIZE NIL))
                (FOO-1 X)))
       (DEFTHM
         FOO-1-COPY-DEF
         (EQUAL (FOO-1-COPY X)
                (IF (CONSP X)
                    (BINARY-+ '1
                              (BINARY-+ '1 (FOO-1-COPY (CDR X))))
                    '0))
         :HINTS (("Goal" :IN-THEORY '((:D FOO-1-COPY))
                  :EXPAND ((FOO-1 X))))
         :RULE-CLASSES
         ((:DEFINITION :INSTALL-BODY T
                       :CLIQUE (FOO-1-COPY)
                       :CONTROLLER-ALIST ((FOO-1-COPY T))))))

     (DEFTHM FOO-1-IS-FOO-1-COPY
       (EQUAL (FOO-1 X) (FOO-1-COPY X))
       :HINTS (("Goal" :INDUCT (FOO-1 X)
                :IN-THEORY '((:DEFINITION FOO-1)
                             (:INDUCTION FOO-1)
                             FOO-1-COPY-DEF)))
       :RULE-CLASSES NIL))

   (defthm foo-1-is-foo-2
     (equal (foo-1 x)
            (foo-2 x))
     :hints (("Goal"
              :by (:functional-instance foo-1-is-foo-1-copy
                                        (foo-1-copy foo-2))
              :in-theory (theory 'minimal-theory)
              :expand ((foo-2 x)))))
   ))
