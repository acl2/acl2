; FTY type support library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
;                  Jared Davis <jared@centtech.com>

(in-package "FTY")
(include-book "database")
(include-book "fixtype")
(include-book "xdoc/names" :dir :system)
(include-book "xdoc/fmt-to-str-orig" :dir :system)
(set-state-ok t)
(program)


(defun html-encode-str (x acc)
  (xdoc::simple-html-encode-str x 0 (length x) acc))


(defun flexlist->defxdoc (x parents kwd-alist state)
  ;; Returns (mv events state)
  (declare (ignorable state))
  (b* (((flexlist x) x)
       (parents (getarg :parents parents kwd-alist))
       (short   (or (getarg :short nil kwd-alist)
                    (cat "A list of @(see? " (xdoc::full-escape-symbol x.elt-type)
                         ") objects.")))
       (long    (or (getarg :long nil kwd-alist)
                    (cat "<p>This is an ordinary @(see fty::deflist).</p>"))))
    (mv `((defxdoc ,x.name
            :parents ,parents
            :short ,short
            :long ,long
            :no-override t))
        state)))

(defun flexalist->defxdoc (x parents kwd-alist state)
  ;; Returns (mv events state)
  (declare (ignorable state))
  (b* (((flexalist x) x)
       (parents (getarg :parents parents kwd-alist))
       (key-link (if x.key-type
                     (cat "@(see? " (xdoc::full-escape-symbol x.key-type) ")")
                   "anything"))
       (val-link (if x.val-type
                     (cat "@(see? " (xdoc::full-escape-symbol x.val-type) ")")
                   "anything"))
       (short   (or (getarg :short nil kwd-alist)
                    (cat "An alist mapping " key-link " to " val-link ".")))
       (long    (or (getarg :long nil kwd-alist)
                    (cat "<p>This is an ordinary @(see fty::defalist).</p>"))))
    (mv `((defxdoc ,x.name
            :parents ,parents
            :short ,short
            :long ,long
            :no-override t))
        state)))

(defun defprod-field-doc (x acc base-pkg state)
  (b* (((flexprod-field x) x)
       (acc (revappend-chars "<dt>" acc))
       ((mv name-str state) (xdoc::fmt-to-str-orig x.name base-pkg state))
       (acc (html-encode-str name-str acc))
       (acc (b* (((when (eq x.type nil))
                  acc)
                 (fixtype (find-fixtype x.type (get-fixtypes-alist (w state))))
                 (target  (if fixtype
                              (fixtype->topic fixtype)
                            x.type))
                 (acc (revappend-chars " &mdash; @(see? " acc))
                 (acc (revappend-chars (xdoc::full-escape-symbol target) acc))
                 (acc (revappend-chars ")" acc)))
              acc))
       (acc (revappend-chars "</dt>" acc))
       (acc (cons #\Newline acc))
       (acc (b* (((when (equal x.doc ""))
                  acc)
                 (acc (revappend-chars "<dd>" acc))
                 (acc (revappend-chars x.doc acc))
                 (acc (revappend-chars "</dd>" acc))
                 (acc (cons #\Newline acc)))
              acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(defun defprod-fields-doc-aux (x acc base-pkg state)
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (defprod-field-doc (car x) acc base-pkg state)))
    (defprod-fields-doc-aux (cdr x) acc base-pkg state)))

(defun defprod-fields-doc (x acc base-pkg state)
  (b* ((acc (revappend-chars "<dl>" acc))
       ((mv acc state) (defprod-fields-doc-aux x acc base-pkg state))
       (acc (revappend-chars "</dl>" acc)))
    (mv acc state)))

(defun defprod-main-description (prod base-pkg acc state)
  ;; Returns (mv acc state)
  (b* (((flexprod prod) prod)
       ((unless (consp prod.fields))
        (mv (revappend-chars "<p>This is an atomic/empty structure; it has no fields.</p>" acc)
            state))
       (acc  (revappend-chars "<h5>Fields</h5>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state)
        ;; BOZO this is all wrong
        (defprod-fields-doc prod.fields acc base-pkg state))
       ((when (eq prod.require t))
        ;; Don't show stupidly trivial requirement
        (mv acc state))
       (acc (revappend-chars "<h5>Additional Requirements</h5>" acc))
       (acc (revappend-chars "<p>The following invariant is enforced on the fields:</p>" acc))
       ((mv req-str state) (xdoc::fmt-to-str-orig prod.require base-pkg state))
       (acc (revappend-chars "<code>" acc))
       (acc (html-encode-str req-str acc))
       (acc (revappend-chars "</code>" acc)))
    (mv acc state)))

(defun defprod-main-autodoc (x parents kwd-alist base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum x) x)
       (prod    (car x.prods))
       (parents (getarg :parents parents kwd-alist))
       (short   (cdr (assoc :short kwd-alist)))
       (long    (cdr (assoc :long kwd-alist)))
       (acc  nil)
       (acc  (revappend-chars "<p>This is a product type introduced by @(see fty::defprod).</p>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state) (defprod-main-description prod base-pkg acc state))
       ;; long may be a form that evaluates to a string:
       (acc  `(revappend-chars ,(or long "") ',acc))
       (long `(rchars-to-string ,acc)))
    (mv `((defxdoc ,x.name
            :parents ,parents
            :short ,short
            :long ,long
            :no-override t))
        state)))


(defun defprod-ctor-optional-fields (field-names pad acc)
  (declare (xargs :guard (and (symbol-listp field-names)
                              (stringp pad))))
  (b* (((when (atom field-names))
        acc)
       (name1 (xdoc::name-low (symbol-name (car field-names))))
       (len1  (length name1))
       (acc   (str::revappend-chars "[:" acc))
       (acc   (xdoc::simple-html-encode-str name1 0 len1 acc))
       (acc   (str::revappend-chars " &lt;" acc))
       (acc   (xdoc::simple-html-encode-str name1 0 len1 acc))
       (acc   (str::revappend-chars "&gt;]" acc))
       (acc   (if (consp (cdr field-names))
                  (str::revappend-chars pad acc)
                acc)))
    (defprod-ctor-optional-fields (cdr field-names) pad acc)))

(defun defprod-ctor-optional-call (name line1 field-names)
  (declare (xargs :guard (and (symbolp name)
                              (stringp line1)
                              (symbol-listp field-names))))
  (b* ((ctor-name (xdoc::name-low (symbol-name name)))
       (pad (str::implode ;; +2 for leading paren & trailing space after ctor-name
             (cons #\Newline
                   (make-list (+ 2 (length ctor-name))
                              :initial-element #\Space))))
       (acc nil)
       (acc (str::revappend-chars "<code>" acc))
       (acc (cons #\Newline acc))
       (acc (cons #\( acc))
       (acc (xdoc::simple-html-encode-str ctor-name 0 (length ctor-name) acc))
       (acc (cons #\Space acc))
       (acc (if (equal line1 "")
                acc
              (str::revappend-chars pad
                                    (str::revappend-chars line1 acc))))
       (acc (defprod-ctor-optional-fields field-names pad acc))
       (acc (cons #\) acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "</code>" acc)))
    (str::rchars-to-string acc)))

#||
(defprod-ctor-optional-call 'make-honsed-foo "" '(lettuce cheese meat))
(defprod-ctor-optional-call 'change-foo "x" '(lettuce cheese meat))
||#

(defun defprod-ctor-autodoc (prod)
  (b* (((flexprod prod)      prod)
       ((when prod.no-ctor-macros)
        ;; Well, there's nothing to document, then.
        nil)
       (foo                  prod.type-name)
       (make-foo-fn          prod.ctor-name)
       (make-foo             prod.ctor-macro)
       ;; It doesn't seem like these are stored in the product itself, but this should agree
       ;; with how flexprod-constructor does it, above.
       (change-foo           (std::da-changer-name prod.ctor-name))

       (plain-foo            (let* ((foo-low (xdoc::name-low (symbol-name foo)))
                                    (acc nil)
                                    (acc (str::revappend-chars "<tt>" acc))
                                    (acc (xdoc::simple-html-encode-str foo-low 0 (length foo-low) acc))
                                    (acc (str::revappend-chars "</tt>" acc)))
                               (str::rchars-to-string acc)))

       (see-foo              (xdoc::see foo))
       (see-make-foo         (xdoc::see make-foo))
       (see-change-foo       (xdoc::see change-foo))

       ;; For make-foo, change-foo, etc., it's nicer to present a list of [:fld <fld>] options
       ;; rather than just saying &rest args, which is what @(call ...) would do.
       (fieldnames           (flexprod-fields->names prod.fields))
       (call-make-foo        (defprod-ctor-optional-call make-foo   "" fieldnames))
       (call-change-foo      (defprod-ctor-optional-call change-foo "x" fieldnames))

       (def-make-foo-fn      (str::cat "@(def " (xdoc::full-escape-symbol make-foo-fn)   ")"))
       (def-make-foo         (str::cat "@(def " (xdoc::full-escape-symbol make-foo)      ")"))
       (def-change-foo       (str::cat "@(def " (xdoc::full-escape-symbol change-foo)    ")")))

    `(;; Unlike defaggregate, I think we don't want to document the raw
      ;; constructor, because it is going to share its name with the type.  I
      ;; also won't try to include honsing information here, for now at least.
      (defxdoc ,make-foo
        :parents (,foo)
        :short ,(str::cat "Basic constructor macro for " see-foo " structures.")
        :long ,(str::cat
                "<h5>Syntax</h5>"
                call-make-foo

                "<p>This is the usual way to construct " see-foo
                " structures.  It simply conses together a structure with the
                specified fields.</p>

                <p>This macro generates a new " plain-foo " structure from
                scratch.  See also " see-change-foo ", which can \"change\" an
                existing structure, instead.</p>"

                "<h3>Definition</h3>

                <p>This is an ordinary @('make-') macro introduced by @(see
                fty::defprod).</p>"

                def-make-foo
                def-make-foo-fn)
        :no-override t)

      (defxdoc ,change-foo
        :parents (,foo)
        :short ,(str::cat "Modifying constructor for " see-foo " structures.")
        :long ,(str::cat
                "<h5>Syntax</h5>"
                call-change-foo

                "<p>This is an often useful alternative to " see-make-foo ".</p>

                <p>We construct a new " see-foo " structure that is a copy of
                @('x'), except that you can explicitly change some particular
                fields.  Any fields you don't mention just keep their values
                from @('x').</p>

                <h3>Definition</h3>

                <p>This is an ordinary @('change-') macro introduced by @(see
                fty::defprod).</p>"

                def-change-foo)
        :no-override t))))

(defun defprod->defxdoc (x parents kwd-alist base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum x)      x)
       (prod             (car x.prods))
       ((flexprod prod)  prod)
       (foo              x.name)
       (foo-p            x.pred)
       (foo-fix          x.fix)
       (make-foo         prod.ctor-macro)
       (change-foo       (std::da-changer-name foo))

       ((mv main-doc state) (defprod-main-autodoc x parents kwd-alist base-pkg state))
       (make/change         (defprod-ctor-autodoc prod))
       (doc-events (append main-doc
                           make/change
                           ;; Special hack to make the subtopic order for a
                           ;; structure look really nice.  We omit the
                           ;; accessors.  XDOC will put them at the end in
                           ;; alphabetical order.
                           `((xdoc::order-subtopics ,foo
                             (,foo-p ,foo-fix ,make-foo ,change-foo))))))
    (mv doc-events state)))

(defun deftagsum-prod-doc (sum  ; the containing sum type
                           prod ; one of the products within it
                           parents ; usually (sum.name)
                           base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       (acc  nil)
       (acc  (revappend-chars "<p>This is a product type, introduced by @(see " acc))
       (acc  (revappend-chars (xdoc::full-escape-symbol sum.typemacro) acc))
       (acc  (revappend-chars ") in support of @(see " acc))
       (acc  (revappend-chars (xdoc::full-escape-symbol sum.name) acc))
       (acc  (revappend-chars ").</p>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state) (defprod-main-description prod base-pkg acc state))
       ;; prod.long may be a form that evaluates to a string:
       (acc  `(revappend-chars ,(or prod.long "") ',acc))
       (long `(rchars-to-string ,acc))
       (top-doc `((defxdoc ,prod.type-name
                    :parents ,parents
                    :short ,prod.short
                    :long ,long
                    :no-override t)))
       (make/change (defprod-ctor-autodoc prod))

       (make-foo         prod.ctor-macro)
       (change-foo       (std::da-changer-name prod.type-name))
       ;; Unlike a standalone defprod, these don't have a fix function
       ;; They also don't have a recognizer
       )
    (mv (append top-doc
                make/change
                `((xdoc::order-subtopics ,prod.type-name (,make-foo ,change-foo)))
                )
        state)))

(defun deftagsum-prods-doc (sum prods parents base-pkg state)
  ;; Returns (mv events state)
  (b* (((when (atom prods))
        (mv nil state))
       ((mv events1 state) (deftagsum-prod-doc sum (car prods) parents base-pkg state))
       ((mv events2 state) (deftagsum-prods-doc sum (cdr prods) parents base-pkg state)))
    (mv (append events1 events2)
        state)))

(defun deftagsum-summarize-prod (sum prod base-pkg acc state)
  ;; Returns (mv acc state)
  (declare (ignorable sum base-pkg))
  (b* (((flexprod prod) prod)
       (acc (revappend-chars "<dt><tt>" acc))
       ((mv kind-str state) (xdoc::fmt-to-str-orig prod.kind base-pkg state))
       (acc (html-encode-str kind-str acc))
       (acc (revappend-chars "</tt> &rarr; @(see " acc))
       (acc (revappend-chars (xdoc::full-escape-symbol prod.type-name) acc))
       (acc (revappend-chars ")</dt>" acc))
       (acc (cons #\Newline acc))

       ((unless prod.short)
        (mv acc state))
       (acc (revappend-chars "<dd>" acc))
       (acc (revappend-chars prod.short acc))
       (acc (revappend-chars "</dd>" acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(defun deftagsum-summarize-prods (sum prods base-pkg acc state)
  ;; Returns (mv acc state)
  (b* (((when (atom prods))
        (mv acc state))
       ((mv acc state) (deftagsum-summarize-prod sum (car prods) base-pkg acc state))
       ((mv acc state) (deftagsum-summarize-prods sum (cdr prods) base-pkg acc state)))
    (mv acc state)))

(defun flexprodlist->type-names (x)
  (if (atom x)
      nil
    (cons (flexprod->type-name (car x))
          (flexprodlist->type-names (cdr x)))))

(defun flexsum-case-macro-defxdoc.examples (kinds acc)
  (b* (((when (atom kinds))
        acc)
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "      :" acc))
       (acc (str::revappend-chars (str::downcase-string (symbol-name (car kinds))) acc))
       (acc (str::revappend-chars " ..." acc)))
    (flexsum-case-macro-defxdoc.examples (cdr kinds) acc)))

(defun flexsum-case-macro-defxdoc (sum)
  (b* (((flexsum sum) sum)
       (kinds       (flexprods->kinds sum.prods))
       (name-link   (xdoc::see sum.name))
       (name-plain  (str::downcase-string (symbol-name sum.name)))
       (case-str    (str::downcase-string (symbol-name sum.case)))
       (kind-fn-str (str::downcase-string (symbol-name sum.kind)))
       (kind1-str   (str::downcase-string (symbol-name (car kinds))))
       (examples    (str::rchars-to-string (flexsum-case-macro-defxdoc.examples kinds nil)))
       )
    `((defxdoc ,sum.case
        :parents (,sum.name)
        :short ,(cat "Case macro for the different kinds of " name-link " structures.")
        :long ,(cat "<p>This is an @(see fty::fty) sum-type case macro,
typically introduced by @(see fty::defflexsum) or @(see fty::deftagsum).  It
allows you to safely check the type of a " name-link " structure, or to split
into cases based on its type.</p>

<h3>Short Form</h3>

<p>In its short form, @('" case-str "') allows you to safely check the type of
a @('" name-plain "') structure.  For example:</p>

@({
    (" case-str " x :" kind1-str ")
})
"
    (if sum.kind
        (cat "<p>is essentially just a safer alternative to writing:</p>
              @({
                  (equal (" kind-fn-str " x) :" kind1-str ")
              })

              <p>Why is using " case-str " safer?  When we directly inspect the
              kind with @('equal'), there is no static checking being done to
              ensure that, e.g., @(':" kind1-str "') is a valid kind of "
              name-link " structure.  That means there is nothing to save you
              if, later, you change the kind keyword for this type from @(':"
              kind1-str "') to something else.  It also means you get no help
              if you just make a typo when writing the @(':" kind1-str "')
              symbol.  Over the course of developing VL, we found that such
              issues were very frequent sources of errors!</p>")
      ;; Otherwise: there is no kind function.  BOZO some day we might try to
      ;; explain what happens here, but it's probably tricky, we'd have to
      ;; pretty-print something like (flexprod->cond (car sum.prods)), and
      ;; that's just messy.  So we'll just say something generic here.
      (cat "<p>can be used to determine whether @('x') is a @('"
           kind1-str "') instead of some other kind of " name-plain
           " structure.</p>"))

    "<h3>Long Form</h3>

<p>In its longer form, @('" case-str "') allows you to split into cases based
on the kind of structure you are looking at.  A typical example would be:</p>

@({
    (" case-str " x" examples ")
})

<p>It is also possible to consolidate ``uninteresting'' cases using
@(':otherwise').</p>

<p>For convenience, the case macro automatically binds the fields of @('x') for
you, as appropriate for each case.  That is, in the @(':" kind1-str "') case,
you can use @(see fty::defprod)-style @('foo.bar') style accessors for @('x')
without having to explicitly add a @('" kind1-str "') @(see b*)
binder.</p>")
        :no-override t))))

(defun deftagsum->defxdoc (x parents kwd-alist base-pkg state)
  ;; Returns (mv events state)
  (declare (ignorable x parents base-pkg))
  (b* (((flexsum x) x)
       (short (cdr (assoc :short kwd-alist)))
       (long  (cdr (assoc :long kwd-alist)))
       (acc   nil)
       (acc   (revappend-chars "<p>This is a tagged union type, introduced by @(see fty::deftagsum).</p>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars "<h5>Member Tags &rarr; Types</h5>" acc))
       (acc   (revappend-chars "<dl>" acc))
       ((mv acc state) (deftagsum-summarize-prods x x.prods base-pkg acc state))
       (acc   (revappend-chars "</dl>" acc))
       (acc   (cons #\Newline acc))
       ;; long may be a form that evaluates to a string:
       (acc `(revappend-chars ,(or long "") ',acc))
       (long `(rchars-to-string ,acc))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long
                     :no-override t)))
       (type-names (flexprodlist->type-names x.prods))
       (case-doc (flexsum-case-macro-defxdoc x))
       ((mv prods-doc state)
        (deftagsum-prods-doc x x.prods (list x.name) base-pkg state)))
    (mv (append main-doc
                prods-doc
                case-doc
                `((xdoc::order-subtopics ,x.name
                                         ,(remove nil
                                                  (list* x.pred x.kind x.case x.fix x.equiv x.count
                                                         type-names)))))
        state)))

(defun defflexsum->defxdoc (x parents kwd-alist base-pkg state)
  ;; Returns (mv events state)
  (declare (ignorable x parents base-pkg))
  (b* (((flexsum x) x)
       (short (cdr (assoc :short kwd-alist)))
       (long  (cdr (assoc :long kwd-alist)))
       (acc   nil)
       (acc   (revappend-chars "<p>This is a sum-of-products (i.e., union) type, introduced by @(see fty::defflexsum).</p>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars "<h5>Members</h5>" acc))
       (acc   (revappend-chars "<dl>" acc))
       ((mv acc state) (deftagsum-summarize-prods x x.prods base-pkg acc state))
       (acc   (revappend-chars "</dl>" acc))
       (acc   (cons #\Newline acc))
       ;; long may be a form that evaluates to a string:
       (acc `(revappend-chars ,(or long "") ',acc))
       (long `(rchars-to-string ,acc))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long
                     :no-override t)))
       (type-names (flexprodlist->type-names x.prods))
       (sum-name-shared-with-prod-name (member x.name type-names))
       (parents (if sum-name-shared-with-prod-name parents (list x.name)))
       ((mv prods-doc state)
        (deftagsum-prods-doc x x.prods parents base-pkg state)))
    (mv (append (and (not sum-name-shared-with-prod-name) main-doc)
                prods-doc
                `((xdoc::order-subtopics ,x.name
                                         ,(remove nil (list* x.pred x.fix x.kind x.equiv x.count
                                                             type-names)))))
        state)))

(defun defoption->defxdoc (x parents kwd-alist base-pkg state)
  ;; Returns (mv events state)
  (declare (ignorable x parents base-pkg))
  (b* (((flexsum x) x)
       ((fixtype base) (cdr (assoc :basetype x.kwd-alist)))
       (short (or (cdr (assoc :short kwd-alist))
                  (str::cat "Option type; @(see? "
                            (xdoc::full-escape-symbol base.name)
                            ") or @('nil').")))
       (long  (cdr (assoc :long kwd-alist)))

       (acc nil)
       (acc (revappend-chars
             "<p>This is an option type introduced by @(see fty::defoption).
              Note that @('defoption') is just a wrapper for @(see
              fty::defflexsum), so there are @(':none') and @(':some') member
              types, a case macro, and so forth.</p>" acc))
       (acc (revappend-chars "<h5>Member Types</h5>" acc))
       (acc (revappend-chars "<dl>" acc))
       ((mv acc state) (deftagsum-summarize-prods x x.prods base-pkg acc state))
       (acc (revappend-chars "</dl>" acc))

       (acc   (cons #\Newline acc))
       ;; long may be a form that evaluates to a string:
       (acc `(revappend-chars ,(or long "") ',acc))
       (long `(rchars-to-string ,acc))
       ((mv prods-doc state)
        (deftagsum-prods-doc x x.prods (list x.name) base-pkg state))
       (case-doc (flexsum-case-macro-defxdoc x))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long
                     :no-override t))))
    (mv (append main-doc
                prods-doc
                case-doc
                `((xdoc::order-subtopics ,x.name
                                         ,(remove nil (list x.pred x.fix x.equiv x.count)))))
        state)))

(defun flextranssum-members->xdoc (members acc state)
  (b* (((when (atom members))
        acc)
       ((flextranssum-member x1) (car members))
       (target (fixtype->topic (find-fixtype x1.name (get-fixtypes-alist (w state)))))
       (acc (str::revappend-chars "<li>" acc))
       (acc (str::revappend-chars "@(see? " acc))
       (acc (str::revappend-chars (xdoc::full-escape-symbol target) acc))
       (acc (str::revappend-chars ")</li>" acc))
       (acc (cons #\Newline acc)))
    (flextranssum-members->xdoc (cdr members) acc state)))

(defun flextranssum->defxdoc (x parents kwd-alist state)
  ;; Returns (mv events state)
  (b* (((flextranssum x) x)
       (short (cdr (assoc :short kwd-alist)))
       (long  (cdr (assoc :long kwd-alist)))
       (acc   nil)
       (acc (revappend-chars
             "<p>This is a ``transparent'' sum type introduced using @(see fty::deftranssum).  It
              is simply any one of the following types:</p>" acc))
       (acc   (revappend-chars "<ul>" acc))
       (acc   (cons #\Newline acc))
       (acc   (flextranssum-members->xdoc x.members acc state))
       (acc   (revappend-chars "</ul>" acc))
       (acc   (cons #\Newline acc))
       ;; long may be a form that evaluates to a string:
       (acc `(revappend-chars ,(or long "") ',acc))
       (long `(rchars-to-string ,acc))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long
                     :no-override t))))
    (mv (append main-doc
                `((xdoc::order-subtopics ,x.name
                                         (,x.pred ,x.fix ,x.equiv))))
        state)))

(defun flexsum->defxdoc (x parents kwd-alist state)
  ;; Returns (mv events state)
  (b* ((__function__ 'flexsum->defxdoc)
       ((flexsum x) x)
       (parents (or (cdr (assoc :parents kwd-alist)) parents))
       (base-pkg (pkg-witness (acl2::f-get-global 'acl2::current-package state)))
       ((unless (symbol-listp parents))
        (mv (raise "~x0: :parents must be a list of symbols." x.name) state)))
    (case x.typemacro
      (defprod    (defprod->defxdoc x parents kwd-alist base-pkg state))
      (deftagsum  (deftagsum->defxdoc x parents kwd-alist base-pkg state))
      (defflexsum (defflexsum->defxdoc x parents kwd-alist base-pkg state))
      (defoption  (defoption->defxdoc x parents kwd-alist base-pkg state))
      (t (mv (raise "~x0: unknown typemacro" x.name) state)))))

(defun flextype->defxdoc (x parents kwd-alist state)
  ;; Returns (mv event state)
  (b* ((__function__ 'flextype->defxdoc)
       ((mv events state)
        (with-flextype-bindings x
          (flex*->defxdoc x parents
                          (append kwd-alist (flex*->kwd-alist x))
                          state)
          :default (mv (raise "Unexpected flex type: ~x0." (tag x))
                       state))))
    (mv `(progn . ,events) state)))

(defun flextypes-collect-defxdoc (types parents)
  (if (atom types)
      nil
    (cons `(make-event (b* (((mv val state)
                             (flextype->defxdoc ',(car types) ',parents nil state)))
                         (value val)))
          (flextypes-collect-defxdoc (cdr types) parents))))

(defun remove-topic (name x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (cdr x)
      (cons (car x) (remove-topic name (cdr x))))))

(defun find-subtype-kwd-alist (types name)
  (if (atom types)
      (mv nil nil)
    (with-flextype-bindings (x (car types))
      (if (eq name (flex*->name x))
          (mv (flex*->kwd-alist x) x)
        (find-subtype-kwd-alist (cdr types) name))
      :default (find-subtype-kwd-alist (cdr types) name))))

(defun flextypes-final-xdoc-fn (x world)
  (b* (((flextypes x) x)
       (parents-look (assoc :parents x.kwd-alist))
       (short        (getarg :short nil x.kwd-alist))
       (long         (getarg :long nil x.kwd-alist))

       ;; x.name may or may not agree with the names of any of the things
       ;; inside it.  For instance:
       ;;   (deftypes pseudo-termp
       ;;     (defprod pseudo-termp ...)
       ;;     (deflist pseudo-term-listp ...))
       ;; or
       ;;   (deftypes statements
       ;;     (defsum vl-stmt-p ...)
       ;;     (deflist vl-stmtlist-p ...))

       ((mv sub-kwd-alist subtype) (find-subtype-kwd-alist x.types x.name))
       (sub-parents-look (assoc :parents sub-kwd-alist))
       ((when (and parents-look sub-parents-look))
        (er hard? 'deftypes "Parents listed for both top-level ~x0 and type ~x0.~%" x.name))
       (parents      (or (cdr parents-look)
                         (cdr sub-parents-look)
                         (xdoc::get-default-parents world)
                         '(acl2::undocumented)))
       (sub-short (getarg :short nil sub-kwd-alist))
       (sub-long (getarg :long nil sub-kwd-alist))
       ((unless subtype)
        `(defxdoc ,x.name
           :parents ,parents
           :short ,short
           :long ,long
           :no-override t))

       ((when (and short sub-short))
        (er hard? 'deftypes "Can't give a top-level :short when you are also ~
                   putting :short documentation on the interior ~x0." x.name))
       ((when (and long sub-long))
        (er hard? 'deftypes "Can't give a top-level :long when you are also ~
                   putting :long documentation on the interior ~x0." x.name))
       (short (or short sub-short))
       (long  (or long sub-long))
       (new-event  `(make-event
                     (b* (((mv val state)
                           (flextype->defxdoc
                            ',subtype ',parents
                            '((:short . ,short)
                              (:long . ,long))
                            state)))
                         (value val)))))
    ;; There's existing sub-documentation, so remove it because we're going to
    ;; overwrite it and we don't want redundant xdoc warnings.
    `(progn
       (table xdoc::xdoc 'xdoc::doc
              (remove-topic ',x.name (xdoc::get-xdoc-table world)))
       ,new-event)))

(defmacro flextypes-final-xdoc (x)
  `(make-event (flextypes-final-xdoc-fn ',x (w state))))

(defun flextypes-defxdoc (x world)
  (b* (((flextypes x) x)
       (parents-look (assoc :parents x.kwd-alist))
       (mutually-recursive-p (consp (cdr x.types)))
       (parents      (or (cdr parents-look)
                         (xdoc::get-default-parents world)
                         '(acl2::undocumented)))
       (parents-for-each-type
        (if mutually-recursive-p
            (list x.name)
          parents)))
    (append (flextypes-collect-defxdoc x.types parents-for-each-type)
            `((flextypes-final-xdoc ,x)))))
