; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; NOTE: Documentation may come later.  Also, several definitions below are
; quite general in nature and, as noted below, may be moved to a more general
; utilities book.  An example at the end shows how to use copy-def to avoid
; induction proofs by using functional instantiation.

(in-package "ACL2")

; The following function might be moved to a more general utilities book.
(defun symbol-package-name-safe (sym)

; Let's avoid accidentally creating a function symbol in the "COMMON-LISP"
; package, which is illegal.

  (declare (xargs :guard (symbolp sym)))
  (let ((pkg (symbol-package-name sym)))
    (if (equal pkg *main-lisp-package-name*)
        "ACL2"
      pkg)))

(defun fn-copy-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern$ (concatenate 'string (symbol-name fn) "-COPY")
           (symbol-package-name-safe fn)))

(defun fn-copy-def-name (fn)
  (intern$ (concatenate 'string (symbol-name fn) "-COPY-DEF")
           (symbol-package-name-safe fn)))

; The following function might be moved to a more general utilities book.
(defun implicate-untranslated-terms (hyps concl)
  (declare (xargs :guard (true-listp hyps)))
  (cond ((null hyps) concl)
        ((null (cdr hyps))
         `(implies ,(car hyps) ,concl))
        (t
         `(implies (and ,@hyps) ,concl))))

(defun copy-def-encapsulate (fn fn-copy hyps-fn equiv wrld)
  (declare (xargs :mode :program))
  (let* ((fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-copy-call (cons fn-copy fn-formals))
         (fn-stobjs-in (stobjs-in fn wrld))
         (stobjs-in-pretty
          (and fn-stobjs-in ; leave nil as nil
               (let ((tmp (prettyify-stobjs-out fn-stobjs-in)))
                 (if (atom tmp)
                     (list tmp)
                   (assert$ (eq (car tmp) 'mv)
                            (cdr tmp))))))
         (stobjs-out-pretty (prettyify-stobjs-out (stobjs-out fn wrld)))
         (hyps (and hyps-fn
                    (list (cons hyps-fn fn-formals))))
         (fn-body (body fn nil wrld))
         (controller-alist-0 (access def-body (def-body fn wrld)
                                     :controller-alist))
         (controller-alist-0-entry (cdr (assoc-eq fn controller-alist-0)))
         (controller-alist (and controller-alist-0-entry
                                (list (cons fn-copy controller-alist-0-entry)))))
    `(encapsulate
       (((,fn-copy ,@stobjs-in-pretty) => ,stobjs-out-pretty))
       (local (defun ,fn-copy ,fn-formals
                (declare (xargs :normalize nil))
                ,fn-call))
       (defthm ,(fn-copy-def-name fn)
         ,(implicate-untranslated-terms
           hyps
           `(,equiv ,fn-copy-call
                    ,(sublis-fn-simple (list (cons fn fn-copy))
                                       fn-body)))
         :hints (("Goal"
                  :in-theory '((:d ,fn-copy))
                  :expand (,fn-call)))
         :rule-classes ((:definition ; avoid normalizing
                         :install-body t
                         ,@(and controller-alist
                                `(:controller-alist ,controller-alist))))))))

(defun fn-is-fn-copy-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (concatenate 'string
                (symbol-name fn)
                "-IS-"
                (symbol-name (fn-copy-name fn)))
   fn))

; The following function might be moved to a more general utilities book.
(defun hyps-preserved-thm-name (fn hyps-fn)
  (declare (xargs :guard (and (symbolp fn)
                              (symbolp hyps-fn)
                              fn
                              hyps-fn)
                  :mode :logic))
  (intern$ (concatenate 'string
                        (symbol-name hyps-fn)
                        "-PRESERVED-FOR-"
                        (symbol-name fn))
           (symbol-package-name-safe hyps-fn)))

(defun fn-is-fn-copy (fn fn-copy hyps-fn hyps-preserved-thm-name equiv wrld)
  (declare (xargs :guard (symbolp hyps-preserved-thm-name) ; partial guard
                  :mode :program))
  (let* ((fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-copy-call (cons fn-copy fn-formals))
         (equality `(,equiv ,fn-call ,fn-copy-call))
         (hyps (and hyps-fn
                    (list (cons hyps-fn fn-formals))))
         (hyps-preserved-thm-name hyps-preserved-thm-name)
         (recursivep (getprop fn 'recursivep nil 'current-acl2-world wrld))
         (def-body (def-body fn wrld))
         (def-body-rune (if def-body
                            (access def-body def-body :rune)
                          (er hard 'fn-is-fn-copy
                              "Unexpected error!  (Sorry about the obscure ~
                               error message; please send it to Matt, who ~
                               will investigate.)"))))
    `(defthm ,(fn-is-fn-copy-name fn)
       ,(implicate-untranslated-terms hyps equality)
       :hints
       (("Goal"
         ,@(and recursivep `(:induct ,fn-call))
         :in-theory '(,def-body-rune
                       ,@(and recursivep `((:induction ,fn)))
                       ,(fn-copy-def-name fn)))
        ,@(and hyps-preserved-thm-name
               (getpropc hyps-preserved-thm-name 'theorem nil wrld)
               `('(:use ,hyps-preserved-thm-name))))
       :rule-classes nil)))

(defun copy-def-event (fn fn-copy hyps-fn hyps-preserved-thm-name equiv wrld)
  (declare (xargs :mode :program))
  `(progn ,(copy-def-encapsulate fn fn-copy hyps-fn equiv wrld)
          ,(fn-is-fn-copy fn fn-copy hyps-fn hyps-preserved-thm-name equiv wrld)))

(defmacro copy-def (fn &key
                       hyps-fn
                       hyps-preserved-thm-name
                       (equiv 'equal))
  `(make-event
    (copy-def-event ',fn (fn-copy-name ',fn) ',hyps-fn
                    ',hyps-preserved-thm-name ',equiv (w state))))

; The following example shows how to use copy-def to avoid induction proofs by
; using functional instantiation.

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
