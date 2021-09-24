; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, 2/27/09
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; defmac.lisp
; Automated support for faster macroexpansion

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc defmac
  :parents (defmacro)
  :short "Define a macro that expands efficiently."
  :long "<p>Example forms</p>

@({
  (include-book \"misc/defmac\" :dir :system)

  (defmac my-xor (x y)
    (list 'if x (list 'not y) y))

  (defmac my-mac (x &optional (y '3 y-p))
    `(list ,x ,y ,y-p))

  (defmac one-of (x &rest rst)
    :macro-fn one-of-function
    \"stubbed-out :doc.\"
    (declare (xargs :guard (symbol-listp rst)))
    (cond ((null rst) nil)
          (t (list 'or
                   (list 'eq x (list 'quote (car rst)))
                   (list* 'one-of x (cdr rst))))))~/
})

<p>General Form:</p>

@({
  (defmac name macro-args
          :macro-fn name-macro-fn ; optional
          doc-string              ; optional
          dcl ... dcl             ; optional
          body)
})

<p>where @('name') is a new symbolic name (see @(see name)), @(see macro-args)
specifies the formals of the macro (see @(see macro-args) for a description),
and @('body') is a term.  @('Doc-string') is an optional @(see documentation)
string, which (as for @(tsee defmacro)) is essentially ignored by ACL2.  Each
@('dcl') is an optional declaration as for @(see defun) (see @(see
declare)).</p>

<p>See @(see defmacro) for a discussion of @('defmacro'), which is the
traditional way of introducing macros.  @('Defmac') is similar to @('defmacro')
except that the resulting macro may execute significantly more efficiently, as
explained below.  You can use @('defmac') just as you would normally use
@('defmacro'), though your @('defmac') form should include the declaration
@('(declare (xargs :mode :program))') to be truly compatible with @('defmacro'),
which allows calls of @(':')@(see program) mode functions in its body.</p>

<p>A @('defmac') form generates the following form, which introduces a @(see
defun) and a @(see defmacro).  Here we refer to the ``General Form'' above;
hence the @(':macro-fn'), @('doc-string'), and each @('dcl') are optional.  The
@('doc-string') is as specified for @(see defmacro), and each @('dcl') is as
specified for @(see defun).  @(':Macro-fn') specifies @('name-macro-fn') (used
below) as illustrated above, but if @(':macro-fn') is not specified then
@('name-macro-fn') is obtained by adding the suffix @('\"-MACRO-FN\"') to the
@(see symbol-name) of @('name') to get a symbol in the same package as
@('name').  The list @('(v1 ... vk)') enumerates all the names introduced in
@('macro-args').</p>

@({
  (progn
    (defun name-macro-fn (v1 ... vk)
      dcl ... dcl
      body)
    (defmacro name macro-args
      doc-string
      (name-macro-fn v1 ... vk))
    )
})

<p>The reason for introducing a @('defun') is efficiency.  ACL2 expands a macro
call by running its own evaluator on the body of the macro, and this can be
relatively slow if that body is large.  But with @('defmac'), the evaluator
call reduces quickly to a single raw Lisp call of the (executable counterpart
of) the auxiliary function on the actuals of the macro.</p>")

; See :doc defmac for information.

(defun defmac-fn (mdef)

; Some of the code for this function is adapted from code for defmacro-fn.

  (declare (xargs :mode :program))
  (let ((ctx (cons 'defmac (car mdef))))
    (mv-let
     (macro-fn mdef)
     (cond ((and (true-listp mdef)
                 (<= 4 (length mdef))
                 (eq (nth 2 mdef) :MACRO-FN))
            (mv (nth 3 mdef) (list* (nth 0 mdef)
                                    (nth 1 mdef)
                                    (nthcdr 4 mdef))))
           (t (mv nil mdef)))
     (mv-let
      (er-string four)
      (chk-defmacro-width mdef)
      (cond
       (er-string (list 'er 'soft (kwote ctx) (kwote er-string) (kwote four)))
       (t
        (let ((name (car four))
              (args (cadr four))
              (dcls (caddr four))
              (body (cadddr four)))
          (cond
           ((or (not (symbolp name))
                (keywordp name))
            `(er soft ',ctx
                 "Names of macros must be non-keyword symbols.  The name ~x0 ~
                  is thus illegal."
                 ',name))
           (t (let ((msg

; We need to check the shape of args before we can apply macro-vars (below).

                     (chk-macro-arglist-msg args nil nil)))
                (cond (msg `(er soft ',ctx "~@0" ',msg))
                      (t
                       (let ((doc (if (stringp (car dcls)) (car dcls) nil))
                             (dcls (if (stringp (car dcls)) (cdr dcls) dcls))
                             (macro-fn (or macro-fn
                                           (intern-in-package-of-symbol
                                            (concatenate 'string
                                                         (symbol-name name)
                                                         "-MACRO-FN")
                                            name)))
                             (formals (macro-vars args)))
                         `(progn (defun ,macro-fn ,formals
                                   ,@dcls
                                   ,body)
                                 (defmacro ,name ,args
                                   ,@(and doc (list doc))
                                   (,macro-fn ,@formals))))))))))))))))

(defmacro defmac (&rest mdef)

; The documentation below borrows heavily from :doc defmacro.

; Warning: See the Important Boot-Strapping Invariants before modifying!

  (defmac-fn mdef))

; Example:

(local
 (encapsulate
  ()
  (defmac one-of (x &rest rst)
    :macro-fn one-of-function
    ;; Jared removed the doc section here toward axing legacy doc stuff
    "
     stubbed-out :doc~/

     ~/~/"
    (declare (xargs :guard (symbol-listp rst)))
    (cond ((null rst) nil)
          (t (list 'or
                   (list 'eq x (list 'quote (car rst)))
                   (list* 'one-of x (cdr rst))))))
  (defun one-of-test-fn (a)
    (one-of a u v w))
  (defthm one-of-test-thm
    (iff (one-of-test-fn a)
         (member a '(u v w))))))
