; ACL2 Standard Library
; Copyright (c) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "support")
(set-state-ok t)
(program)

(defxdoc defval
  :parents (std/util defconst)
  :short "A replacement for @(see defconst) with @(see xdoc) integration."

  :long "<h5>Basic Example</h5>

@({
    (defval *defval-example-number*
      :parents (defval)
      :short \"Example of a constant for @(see defval).\"
      :long \"<p>This number is not very important.</p>\"
      (fib 5))
})

<p>This is equivalent to just doing a @(see defxdoc) followed by a @(see
defconst), except that the @(':long') string will be automatically extended
with the defining event for @('*defval-example-number*').</p>

<h5>General Form</h5>

@({
    (defval *name*
      [keyword options]
      body                 ;; defining expression
      [/// other events])

    Option          Default
      :parents        nil
      :short          nil
      :long           nil
      :showdef        t
      :showval        nil
      :prepwork       nil
})

<p>The @(':parents'), @(':short'), and @(':long') options are as in @(see
defxdoc).  Typically you should specify at least @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), to get bare-bones
documentation put into your manual in the right place.</p>

<p>The @(':showdef') and @(':showval') options control what kind of
documentation will be added to your @(':long') section, if any.  These options
are independent, i.e., you can say that you want either, both, or neither kinds
of automatic documentation.</p>

<p>When @(':showdef') is enabled, which is the default, @('defval') will
automatically extend your @(':long') string with a the <i>definition</i> of the
constant.  For instance, here's what this looks like for
@('*defval-example-number*'):</p>

<box>
@(def *defval-example-number*)
</box>

<p>In contrast, when @(':showval') is enabled, @('defval') will extend
@(':long') with the <i>value</i> of your constant, e.g.,</p>

<box>
<p><b>Value:</b></p>
@(`(:code *defval-example-number*)`)
</box>

<p>The optional @(':prepwork') argument can be used to put arbitrary events
before the constant.  This could be used, for instance, to define functions
that are going to be used in the definition of the constant.  These events will
be documented as in the usual @(see defsection) style.</p>

<p>The optional @('///') syntax is like that of @(see define).  After the
@('///') you can put related events that should come after the definition.
These events will be included in the documentation, as in @(see
defsection).</p>

<h5>Warning about Large Constants</h5>

<p>Either @(':showdef') or @(':showval') <b>can cause problems</b> when the
printed representation of your constant's definition or value is very large.
Trying to put huge values into the documentation could cause performance
problems when generating or viewing the manual.</p>

<p>This is much more likely to be a problem with @(':showval'), since even very
small definitions like @('(make-list 100000)') can produce large values.
Because of this, @('defval') disables @(':showval') disabled by default.</p>

<p>This is unlikely to be a problem for @(':showdef') when you are writing your
own @('defval') forms.  However, if you are using @(see make-event) or other
macros to generate @('defval') forms, you will need to be careful.</p>")

(defconst *defval-valid-keywords*
  '(:parents
    :short
    :long
    :showdef
    :showval
    :prepwork))

(defun defval-extract-keywords
  ;; This is very much like extract-keywords, but don't error out if we see a
  ;; lone keyword at the end (because that could be the constant we're
  ;; defining!)
  (ctx        ; context for error messages
   legal-kwds ; what keywords the args are allowed to contain
   args       ; args that the user supplied
   kwd-alist  ; accumulator alist of extracted keywords to values
   )
  "Returns (mv kwd-alist other-args)"
  (declare (xargs :guard (and (symbol-listp legal-kwds)
                              (no-duplicatesp legal-kwds)
                              (alistp kwd-alist))))
  (b* ((__function__ 'defval-extract-keywords)
       ((when (atom args))
        (mv kwd-alist args))
       (arg1 (first args))

       ((unless (and (keywordp arg1)
                     (member arg1 legal-kwds)
                     (consp (cdr args))))
        ;; Skip over ANYTHING unless it's a keyword that we know is ours
        ;; followed by a value.
        (b* (((mv kwd-alist other-args)
              (defval-extract-keywords ctx legal-kwds (cdr args) kwd-alist)))
          (mv kwd-alist (cons arg1 other-args))))

       ((when (assoc arg1 kwd-alist))
        (raise "~x0: multiple occurrences of keyword ~x1." ctx arg1)
        (mv nil nil))
       (value     (second args))
       (kwd-alist (acons arg1 value kwd-alist)))
    (defval-extract-keywords ctx legal-kwds (cddr args) kwd-alist)))

(defun defval-fn (name body kwd-alist other-events state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((__function__ 'defval)
       (showdef   (getarg :showdef  t   kwd-alist))
       (showval   (getarg :showval  nil kwd-alist))
       (prepwork  (getarg :prepwork nil kwd-alist))
       (short     (getarg :short    nil kwd-alist))
       (long      (getarg :long     nil kwd-alist))
       (parents-p (assoc :parents kwd-alist))
       (parents   (cdr parents-p))
       (parents   (if parents-p
                      parents
                    (or (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))))

       ((unless (booleanp showdef))
        (raise ":showdef must be a boolean, but is ~x0." showdef))
       ((unless (booleanp showval))
        (raise ":showval must be a boolean, but is ~x0." showval))
       ((unless (true-listp prepwork))
        (raise ":prepwork must be a true-listp, but is ~x0." prepwork))
       ((unless (symbol-listp parents))
        (raise ":parents must be a symbol list, but is ~x0." parents))
       ((unless (or (stringp long) (true-listp long)))
        (raise ":long must be a string or a true-listp, but is ~x0." long))
       ((unless (or (stringp short) (true-listp short)))
        (raise ":short must be a string or a true-listp, but is ~x0." short))

       ;; Note that we always generate documentation: even if the user gives no
       ;; arguments and has no default-parents set, we'll put it into the
       ;; Undocumented topic.  Hence, we always want to extend long, etc.
       ;; Note also that we treat long as a form, so that it can be evaluated.

       (long     (or long ""))
       (name-str (concatenate 'string (symbol-package-name name) "::" (symbol-name name)))
       (long     (if showdef
                     `(concatenate 'string ,long "@(def " ,name-str ")")
                   long))
       (long     (if showval
                     `(concatenate 'string
                                   ,long "<p><b>Value:</b></p>"
                                   "@(`(:code " ,name-str ")`)")
                   long)))

    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       ,@prepwork
       (defconst ,name ,body)
       . ,(and other-events
               `((with-output :stack :pop (progn . ,other-events)))))))

(defmacro defval (name &rest args)
  (b* ((__function__ 'defval)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'defval name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist other-args)
        (defval-extract-keywords ctx *defval-valid-keywords* main-stuff nil))
       ((unless (tuplep 1 other-args))
        (raise "Wrong number of arguments to defval."))
       (body (first other-args)))
    `(with-output
       :stack :push
       :off (acl2::summary
             acl2::observation
             acl2::prove
             acl2::proof-tree
             acl2::event)
       (make-event
        `(progn ,(defval-fn ',name ',body ',kwd-alist ',other-events state)
                (value-triple '(defval ,',name)))))))
