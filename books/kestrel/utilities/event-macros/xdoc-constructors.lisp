; Event Macros -- XDOC Constructors
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/system/world-queries" :dir :system)
(include-book "kestrel/utilities/xdoc/constructors" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ xdoc::evmac-constructors
  :parents (event-macros xdoc::constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document <see topic='@(url event-macros)'>event macros</see>."
  :long
  (xdoc::topapp
   (xdoc::p
    "The @('xdoc::evmac-section-...') utilities construct level-3 sections.
     Some are relatively thin wrappers,
     which precede their arguments
     (which must be zero or more pieces of XDOC text)
     with specific level-3 headings.
     Other utilities provide more automation.")
   (xdoc::p
    "The @('xdoc::evmac-input-...') utilities construct
     <see topic='@(url xdoc::desc)'>descriptions</see>
     of inputs that are expected to be common to multiple event macros.
     Each such utility includes zero or more parameters
     to customize the description,
     as well as zero or more additional pieces of XDOC text (e.g. paragraphs)
     that are appended after the automatically generated XDOC text."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-intro
  :short "Construct the introduction section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-intro"))
  (defmacro xdoc::evmac-section-intro (&rest content)
    `(xdoc::app
      (xdoc::h3 "Introduction")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-form
  :short "Construct the general form section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-form"))
  (defmacro xdoc::evmac-section-form (&rest content)
    `(xdoc::app
      (xdoc::h3 "General Form")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-form-auto
  :short "Construct and fill the general form section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "The section is filled with a form that starts with the macro name,
     followed by the required arguments, one per line, vertically aligned;
     then there is @('&key') on one line, vertically aligned with the arguments,
     followed by the keyword arguments, one per line, vertically aligned,
     each preceded by colon
     and followed by an end-of-line comment indicating the default value.
     This form is also used in other ACL2+Books manual pages.")
   (xdoc::p
    "If the macro includes @('&...') lambda keywords
     other than @('&key') and @('&whole'),
     we fail because this utility
     only handles required and keyword arguments for now.")
   (xdoc::p
    "The name of the symbol of the macro is made lowercase,
     without the package because the manual page where this section goes
     should be in the same package.")
   (xdoc::p
    "We calculate the indentation of the arguments as
     1 for the opening pathenthesis
     plus the length of the macro name
     plus 1 for the space after the macro name.
     We calculate the indentation of
     the semicolons of the end-of-line comments as
     the maximum length of a keyword argument plus two spaces
     (which provide a little more visual separation that just one space).")
   (xdoc::p
    "We construct the lines (strings) via two loops (recursions).
     The first loop is for the macro's required arguments.
     A boolean flag,
     initially @('t') but @('nil') at the first recursive call,
     determines whether we are constructing the first line
     (which must start with the name of the macro)
     or a successive line
     (which must start with just spaces).")
   (xdoc::p
    "Before the second loop, we construct a line with just @('&key').
     This is preceded by the macro name if the macro has no required arguments,
     otherwise it is preceded by spaces.")
   (xdoc::p
    "The second loop is for the macro's keyword arguments.
     Each line starts with the spaces to align to the other arguments,
     then there's the keyword argument name,
     made lowercase and preceded by colon,
     then some padding to the end-of-line comment,
     then the end-of-line comment.
     For now we only support keyword arguments
     whose default values are symbols:
     the symbols are printed, lowercase, in the end-of-line comments;
     if the symbols are keywords, they are preceded by colon.")
   (xdoc::p
    "We conclude the form with a line with a closing parenthesis.")
   (xdoc::def "xdoc::evmac-section-form-auto"))

  (define xdoc::evmac-section-form-auto-max-key ((key-args symbol-alistp))
    :returns (max natp)
    :parents nil ; override default
    (cond ((endp key-args) 0)
          (t (max (length (symbol-name (caar key-args)))
                  (xdoc::evmac-section-form-auto-max-key (cdr key-args))))))

  (define xdoc::evmac-section-form-auto-req-lines ((macro-name stringp)
                                                   (req-args symbol-listp)
                                                   (spaces stringp)
                                                   (first-line-p booleanp))
    :returns (lines string-listp)
    :verify-guards nil
    :parents nil ; override default
    (b* (((when (endp req-args)) nil)
         (arg-name (string-downcase (symbol-name (car req-args))))
         (start (if first-line-p
                    (concatenate 'string "(" macro-name " ")
                  spaces))
         (line (concatenate 'string start arg-name))
         (lines (xdoc::evmac-section-form-auto-req-lines
                 macro-name (cdr req-args) spaces nil)))
      (cons line lines)))

  (define xdoc::evmac-section-form-auto-key-lines ((key-args symbol-alistp)
                                                   (spaces stringp)
                                                   (indent-comment natp))
    :returns (lines string-listp)
    :verify-guards nil
    :parents nil ; override default
    (b* (((when (endp key-args)) nil)
         (arg-name (string-downcase (symbol-name (caar key-args))))
         (padding (coerce (make-list (- indent-comment (length arg-name))
                                     :initial-element #\Space)
                          'string))
         (comment-start "; default ")
         (value (cdar key-args))
         ((unless (symbolp value))
          (raise "Unsupported macro default value ~x0." value))
         (value-string (concatenate 'string
                                    (if (keywordp value) ":" "")
                                    (string-downcase (symbol-name value))))
         (line (concatenate 'string
                            spaces
                            arg-name
                            padding
                            comment-start
                            value-string))
         (lines (xdoc::evmac-section-form-auto-key-lines
                 (cdr key-args) spaces indent-comment)))
      (cons line lines)))

  (define xdoc::evmac-section-form-auto-lines ((macro symbolp)
                                               (wrld plist-worldp))
    :returns (lines string-listp)
    :verify-guards nil
    :parents nil ; override default
    (b* ((all-args (macro-args macro wrld))
         ((when (intersectp-eq all-args
                               '(&optional &rest &body &allow-other-keys)))
          (raise "Unsupported macro keywords: ~&0."
                 (intersection-eq all-args
                                  '(&optional &rest &body &allow-other-keys))))
         (req-args (macro-required-args macro wrld))
         (key-args (macro-keyword-args macro wrld))
         (macro-name (string-downcase (symbol-name macro)))
         (indent-arg (+ 2 (length macro-name)))
         (indent-comment (+ 2 (xdoc::evmac-section-form-auto-max-key key-args)))
         (spaces (coerce (make-list indent-arg :initial-element #\Space)
                         'string))
         (req-lines (xdoc::evmac-section-form-auto-req-lines
                     macro-name req-args spaces t))
         (key-line (concatenate 'string
                                (if (= (len req-args) 0)
                                    (concatenate 'string "(" macro-name " ")
                                  spaces)
                                "&key"))
         (key-lines (xdoc::evmac-section-form-auto-key-lines
                     key-args spaces indent-comment))
         (last-line "  )"))
      (append req-lines
              (list key-line)
              key-lines
              (list last-line)))
    :prepwork
    ((local (include-book "std/typed-lists/string-listp" :dir :system))))

  (defmacro xdoc::evmac-section-form-auto (macro)
    (declare (xargs :guard (symbolp macro)))
    `(xdoc::evmac-section-form
      (xdoc::code-fn (xdoc::evmac-section-form-auto-lines ',macro (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-inputs
  :short "Construct the inputs section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-inputs"))
  (defmacro xdoc::evmac-section-inputs (&rest content)
    `(xdoc::app
      (xdoc::h3 "Inputs")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-appconds
  :short "Construct the applicability conditions section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "Note that the generated text mentions `above'
     in reference to the inputs of the event macro.
     In the reference documentation of the event macro,
     the <see topic='@(url xdoc::evmac-section-inputs)'>inputs
     section</see> should come before
     the <see topic='@(url xdoc::evmac-section-appconds)'>applicability
     conditions section</see>.")
   (xdoc::def "xdoc::evmac-section-appconds"))
  (defmacro xdoc::evmac-section-appconds (macro &rest content)
    (declare (xargs :guard (symbolp macro)))
    (let ((macro-name (string-downcase (symbol-name macro))))
      `(xdoc::app
        (xdoc::h3 "Applicability Conditions")
        (xdoc::p
         (concatenate 'string
                      "In order for @('"
                      ,macro-name
                      "') to apply,
                       in addition to the requirements on the inputs
                       stated above,
                       the following conditions must be proved.
                       The proofs are attempted when @('"
                      ,macro-name
                      "') is called,
                       using the hints optionally supplied
                       as the @(':hints') input above."))
        ,@content))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-generated
  :short "Construct the generated function(s) and theorem(s) section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "The two parameters indicate how many functions and theorems are listed
     (none, one, more than one).
     These are used to customize the section title.")
   (xdoc::def "xdoc::evmac-section-generated"))
  (defmacro xdoc::evmac-section-generated (fns thms &rest content)
    (declare (xargs :guard (and (member-eq fns '(:none :one :many))
                                (member-eq thms '(:none :one :many))
                                (not (and (eq fns :none)
                                          (eq thms :none))))))
    (b* ((fn-word (if (eq fns :many) "Functions" "Function"))
         (thm-word (if (eq thms :many) "Theorems" "Theorem"))
         (title (cond ((eq fns :none) (concatenate 'string
                                                   "Generated "
                                                   thm-word))
                      ((eq thms :none) (concatenate 'string
                                                    "Generated "
                                                    fn-word))
                      (t (concatenate 'string
                                      "Generated "
                                      fn-word
                                      " and "
                                      thm-word)))))
      `(xdoc::app (xdoc::h3 ,title)
                  ,@content))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-redundancy
  :returns (text xdoc::textp)
  :short "Construct the redundancy section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "This assumes an event macro with a @(':print') and @(':show-only') inputs
     with specific meanings.
     This XDOC constructor may be generalized in the future
     to cover event macros that do not have exactly
     those two specific inputs with those specific meanings.")
   (xdoc::def "xdoc::evmac-section-redundancy"))
  (defmacro xdoc::evmac-section-redundancy (macro)
    (declare (xargs :guard (symbolp macro)))
    (let ((macro-name (string-downcase (symbol-name macro))))
      `(xdoc::app
        (xdoc::h3 "Redundancy")
        (xdoc::p
         (concatenate
          'string
          "A call of @('"
          ,macro-name
          "') is redundant if and only if
           it is identical to a previous successful call of @('"
          ,macro-name
          "') whose @(':show-only') input is not @('t'),
           except that the two calls may differ in
           their @(':print') and @(':show-only') inputs.
           These inputs do not affect the generated events,
           and thus they are ignored for the purpose of redundancy."))
        (xdoc::p
         (xdoc::app
          "A call of @('"
          ,macro-name
          "') whose @(':show-only') input is @('t')
           does not generate any event.
           Thus, no successive call may be redundant with such a call."))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-hints
  :short "Construct a description of the @(':hints') input
          for the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "Note that the generated text mentions `below'
     in reference to the applicability conditions.
     In the reference documentation of the event macro,
     the <see topic='@(url xdoc::evmac-section-inputs)'>inputs
     section</see> should come before
     the <see topic='@(url xdoc::evmac-section-appconds)'>applicability
     conditions section</see>.")
   (xdoc::def "xdoc::evmac-input-hints"))
  (defmacro xdoc::evmac-input-hints (&rest additional)
    `(xdoc::desc
      "@(':hints') &mdash; default @('nil')"
      (xdoc::p
       "Hints to prove the applicability conditions below.")
      (xdoc::p
       "It must be a
        <see topic='@(url acl2::keyword-value-listp)'>keyword-value list</see>
        @('(appcond1 hints1 ... appcondp hintsp)'),
        where each @('appcondk') is a keyword
        that identifies one of the applicability conditions below,
        and each @('hintsk') consists of hints that may appear
        just after @(':hints') in a @(tsee defthm).
        The hints @('hintsk') are used
        to prove applicability condition @('appcondk').")
      (xdoc::p
       "The @('appcond1'), ..., @('appcondp') keywords must be all distinct.")
      (xdoc::p
       "An @('appcondk') keyword is allowed in the @(':hints') input iff
        the corresponding applicability condition is present,
        as specified below.")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-print
  :short "Construct a description of the @(':print') input
          for the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "Note that the generated text mentions `below'
     in reference to the generated events and to redundancy.
     In the reference documentation of the event macro,
     the <see topic='@(url xdoc::evmac-section-inputs)'>inputs
     section</see> should come before
     the <see topic='@(url xdoc::evmac-section-generated)'>generated
     events section</see> and
     the <see topic='@(url xdoc::evmac-section-redundancy)'>redundancy
     section</see>.")
   (xdoc::def "xdoc::evmac-input-print"))
  (defmacro xdoc::evmac-input-print (macro &rest additional)
    (declare (xargs :guard (symbolp macro)))
    (let* ((macro-name (string-downcase (symbol-name macro)))
           (macro-ref (concatenate 'string "@('" macro-name "')")))
      `(xdoc::desc
        "@(':print') &mdash; default @(':result')"
        (xdoc::p
         "Specifies what is printed on the screen:")
        (xdoc::ul
         (xdoc::li
          "@('nil'), to print nothing (not even error output).")
         (xdoc::li
          "@(':error'), to print only error output (if any).")
         (xdoc::li
          (concatenate
           'string
           "@(':result'), to print,
            besides any error output,
            also the generated events described below,
            i.e. the resulting events of "
           ,macro-ref
           ". This is the default value of the @(':print') input."))
         (xdoc::li
          (concatenate
           'string
           "@(':info'), to print,
            besides any error output and the resulting events,
            also some additional information about the operations performed by "
           ,macro-ref
           "."))
         (xdoc::li
          "@(':all'), to print,
          besides any error output,
          the resulting events,
          and the additional information,
          also ACL2's output in response to all the submitted events
          (the ones that form the result as well as some ancillary ones)."))
        (xdoc::p
         "These are ordered printing levels")
        (xdoc::code
         "nil < :error < :result < :info < :all")
        (xdoc::p
         "where the amount of printed material increases monotonically.")
        (xdoc::p
         (concatenate
          'string
          "If the call of "
          ,macro-ref
          " is redundant
           (as defined in the `Redundancy' section below),
           a message to that effect is printed on the screen,
           unless @(':print') is @('nil')."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-show-only
  :short "Construct a description of the @(':show-only') input
          for the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "Note that the generated text mentions `below'
     in reference to redundancy.
     In the reference documentation of the event macro,
     the <see topic='@(url xdoc::evmac-section-inputs)'>inputs
     section</see> should come before
     the <see topic='@(url xdoc::evmac-section-redundancy)'>redundancy
     section</see>.")
   (xdoc::def "xdoc::evmac-input-show-only"))
  (defmacro xdoc::evmac-input-show-only (macro &rest additional)
    (declare (xargs :guard (symbolp macro)))
    (let* ((macro-name (string-downcase (symbol-name macro)))
           (macro-ref (concatenate 'string "@('" macro-name "')")))
      `(xdoc::desc
        "@(':show-only') &mdash; default @('nil')"
        (xdoc::p
         (concatenate
          'string
          "Determines whether the event expansion of "
          ,macro-ref
          " is submitted to ACL2 or just printed on the screen:"))
        (xdoc::ul
         (xdoc::li
          "@('nil'), to submit it.")
         (xdoc::li
          (concatenate
           'string
           "@('t'), to just print it.
            In this case:
            the event expansion is printed even if @(':print') is @('nil')
            (because the user has explicitly asked to show the event expansion);
            the resulting events are not re-printed separately
            (other than their appearance in the printed event expansion)
            even if @(':print') is @(':result') or @(':info') or @(':all');
            no ACL2 output is printed for the event expansion
            even if @(':print') is @(':all')
            (because the event expansion is not submitted).
            If the call of "
           ,macro-ref
           " is redundant
            (as defined in the `Redundancy' section below),
            the event expansion generated by the existing call is printed.")))
        ,@additional))))
