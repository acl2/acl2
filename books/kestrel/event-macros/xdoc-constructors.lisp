; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/macro-keyword-args" :dir :system)
(include-book "kestrel/std/system/macro-required-args" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-xdoc-constructors
  :parents (event-macros xdoc::composite-constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document <see topic='@(url event-macros)'>event macros</see>
          and their implementations.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-xdoc-constructors-user-level
  :parents (event-macro-xdoc-constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document <see topic='@(url event-macros)'>event macros</see>
          at the user level."
  :long
  (xdoc::topstring
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
  (xdoc::topstring
   (xdoc::@def "xdoc::*evmac-section-intro-title*")
   (xdoc::@def "xdoc::evmac-section-intro"))

  (defconst xdoc::*evmac-section-intro-title*
    "Introduction")

  (defmacro xdoc::evmac-section-intro (&rest content)
    `(xdoc::&&
      (xdoc::h3 xdoc::*evmac-section-intro-title*)
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-form
  :short "Construct the general form section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::@def "xdoc::*evmac-section-form-title*")
   (xdoc::@def "xdoc::evmac-section-form"))

  (defconst xdoc::*evmac-section-form-title*
    "General Form")

  (defmacro xdoc::evmac-section-form (&rest content)
    `(xdoc::&&
      (xdoc::h3 xdoc::*evmac-section-form-title*)
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-form-auto
  :short "Construct and fill the general form section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
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
   (xdoc::@def "xdoc::evmac-section-form-auto"))

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
      (xdoc::codeblock-fn
       (xdoc::evmac-section-form-auto-lines ',macro (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-inputs
  :short "Construct the inputs section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::@def "xdoc::*evmac-section-inputs-title*")
   (xdoc::@def "xdoc::evmac-section-inputs"))

  (defconst xdoc::*evmac-section-inputs-title*
    "Inputs")

  (defmacro xdoc::evmac-section-inputs (&rest content)
    `(xdoc::&&
      (xdoc::h3 xdoc::*evmac-section-inputs-title*)
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-appconds
  :short "Construct the applicability conditions section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this documentation is part of the XDOC topic
     whose name is the name of the macro,
     the @('macro-ref') variable is not a link.")
   (xdoc::@def "xdoc::*evmac-section-appconds-title*")
   (xdoc::@def "xdoc::evmac-section-appconds"))

  (defconst xdoc::*evmac-section-appconds-title*
    "Applicability Conditions")

  (defmacro xdoc::evmac-section-appconds (macro &rest content)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@('" macro-name "')"))
         (inputs-ref (concatenate 'string
                                  "`"
                                  xdoc::*evmac-section-inputs-title*
                                  "' section")))
      `(xdoc::&&
        (xdoc::h3 xdoc::*evmac-section-appconds-title*)
        (xdoc::p
         "In order for "
         ,macro-ref
         " to apply,
          in addition to the requirements on the inputs
          stated in the "
         ,inputs-ref
         ", the following "
         (xdoc::seetopic "acl2::event-macro-applicability-conditions"
                         "applicability conditions")
         " must be proved.
          The proofs are attempted when "
         ,macro-ref
         " is called,
          using the hints optionally supplied as the @(':hints') input
          described in the "
         ,inputs-ref
         ".")
        ,@content))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-generated
  :short "Construct the generated events section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::@def "xdoc::*evmac-section-generated-title*")
   (xdoc::@def "xdoc::evmac-section-generated"))

  (defconst xdoc::*evmac-section-generated-title*
    "Generated Events")

  (defmacro xdoc::evmac-section-generated (&rest content)
    `(xdoc::&&
      (xdoc::h3 xdoc::*evmac-section-generated-title*)
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-redundancy
  :returns (text xdoc::treep)
  :short "Construct the redundancy section
          of the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This assumes an event macro with a @(':print') and @(':show-only') inputs
     with specific meanings.
     This XDOC constructor may be generalized in the future
     to cover event macros that do not have exactly
     those two specific inputs with those specific meanings.")
   (xdoc::p
    "Since this documentation is part of the XDOC topic
     whose name is the name of the macro,
     the @('macro-ref') variable is not a link.")
   (xdoc::@def "xdoc::*evmac-section-redundancy-title*")
   (xdoc::@def "xdoc::evmac-section-redundancy"))

  (defconst xdoc::*evmac-section-redundancy-title*
    "Redundancy")

  (defmacro xdoc::evmac-section-redundancy (macro)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@('" macro-name "')")))
      `(xdoc::&&
        (xdoc::h3 xdoc::*evmac-section-redundancy-title*)
        (xdoc::p
         (concatenate
          'string
          "A call of "
          ,macro-ref
          " is redundant if and only if
           it is identical to a previous successful call of "
          ,macro-ref
          " whose @(':show-only') input is not @('t'),
           except that the two calls may differ in
           their @(':print') and @(':show-only') inputs.
           These inputs do not affect the generated events,
           and thus they are ignored for the purpose of redundancy."))
        (xdoc::p
         (concatenate
          'string
          "A call of "
          ,macro-ref
          " whose @(':show-only') input is @('t')
           does not generate any event.
           Thus, no successive call may be redundant with such a call."))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-hints
  :short "Construct a description of the @(':hints') input
          for the reference documentation of an event macro."
  :long (xdoc::topstring-@def "xdoc::evmac-input-hints")

  (defmacro xdoc::evmac-input-hints (&rest additional)
    (let ((appconds-ref (concatenate 'string
                                     "`"
                                     xdoc::*evmac-section-appconds-title*
                                     "' section")))
      `(xdoc::desc
        "@(':hints') &mdash; default @('nil')"
        (xdoc::p
         "Hints to prove the applicability conditions.")
        (xdoc::p
         "It must be one of the following:")
        (xdoc::ul
         (xdoc::li
          "A "
          (xdoc::seetopic "acl2::keyword-value-listp" "keyword-value list")
          " @('(appcond1 hints1 appcond2 hints2 ...)'),
           where each @('appcondk') is a keyword
           that identifies one of the applicability conditions
           listed in the "
          ,appconds-ref
          " and each @('hintsk') is a list of hints of the kind
           that may appear just after @(':hints') in a @(tsee defthm).
           The hints @('hintsk') are used
           to prove applicability condition @('appcondk').
           The @('appcond1'), @('appcond2'), ... keywords must be all distinct.
           An @('appcondk') keyword is allowed only if
           the corresponding applicability condition is present,
           as specified in the "
          ,appconds-ref
          ".")
         (xdoc::li
          "A list of hints of the kind
           that may appear just after @(':hints') in a @(tsee defthm).
           In this case, these same hints are used
           to prove every applicability condition,."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-print
  :short "Construct a description of the @(':print') input
          for the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this documentation is part of the XDOC topic
     whose name is the name of the macro,
     the @('macro-ref') variable is not a link.")
   (xdoc::@def "xdoc::evmac-input-print"))

  (defmacro xdoc::evmac-input-print (macro &rest additional)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@('" macro-name "')"))
         (generated-ref (concatenate 'string
                                     "`"
                                     xdoc::*evmac-section-generated-title*
                                     "' section"))
         (redundancy-ref (concatenate 'string
                                      "`"
                                      xdoc::*evmac-section-redundancy-title*
                                      "' section")))
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
            also the generated events described
            in the "
           ,generated-ref
           ", i.e. the resulting events of "
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
        (xdoc::codeblock
         "nil < :error < :result < :info < :all")
        (xdoc::p
         "where the amount of printed material increases monotonically.")
        (xdoc::p
         (concatenate
          'string
          "If the call of "
          ,macro-ref
          " is redundant
           (as defined in the "
          ,redundancy-ref
          "), a message to that effect is printed on the screen,
           unless @(':print') is @('nil')."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-input-show-only
  :short "Construct a description of the @(':show-only') input
          for the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this documentation is part of the XDOC topic
     whose name is the name of the macro,
     the @('macro-ref') variable is not a link.")
   (xdoc::@def "xdoc::evmac-input-show-only"))

  (defmacro xdoc::evmac-input-show-only (macro &rest additional)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@('" macro-name "')"))
         (redundancy-ref (concatenate 'string
                                      "`"
                                      xdoc::*evmac-section-redundancy-title*
                                      "' section")))
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
            (as defined in the "
           ,redundancy-ref
           "), the event expansion generated by the existing call
            is printed.")))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-desc-function/lambda/macro
  :short "Construct a common description text for an input that must be
          a function name or a lambda expression or a macro name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This text expresses some common requirements
     on this kind of inputs to event macros.")
   (xdoc::p
    "This utility provides some customization facilities:")
   (xdoc::ul
    (xdoc::li
     "The @('subject') parameter must be XDOC text
      that describes the subject of the assertion of the requirements.
      The default is the string @('\"It\"'),
      which should be appropriate if this text follows
      some preceding text that describes what the input is for.")
    (xdoc::li
     "The @('1arg') parameter must be a boolean
      that specifies whether the function or lambda expression
      must be unary (i.e. take one argument) or not.")
    (xdoc::li
     "The @('1res') parameter must be a boolean
      that specifies whether the function or lambda expression
      must return a single (i.e. non-@(tsee mv)) result or not.")
    (xdoc::li
     "The @('guard') parameter must be one of the following:
      (i) XDOC text that describes the condition under which
      the guards must be verified;
      (ii) @('t'), to indicate that the guards must always be verified;
      (iii) @('nil'), to indicate that there are no requirements
      on the guards being verified.
      The default is @('nil').")
    (xdoc::li
     "The @('dont-be-or-call') parameter must be one of the following:
      (i) XDOC text that describes functions that
      the input (if a function) must differ from
      or that the input (if a lambda expression) must not reference;
      (ii) @('nil') (the default), to indicate no such requirements.")
    (xdoc::li
     "The @('additional-function') parameter must be one of the following:
      (i) XDOC text that describes additional requirements
      for the function (typically a sentence);
      (ii) @('nil') (the default) for no additional text.")
    (xdoc::li
     "The @('additional-lambda') parameter must be one of the following:
      (i) XDOC text that describes additional requirements
      for the lambda expression (typically a sentence);
      (ii) @('nil') (the default) for no additional text.")
    (xdoc::li
     "The @('additional-forms') parameter must consist of
      XDOC list items that describe additional possible forms of the input,
      besides the function and lambda expression forms.
      For instance, an additional form could be a keyword @(':auto')
      to infer the function or lambda expression automatically.
      The default is the empty string, i.e. no additional forms."))
   (xdoc::p
    "Looking at some uses of this utility should make it clearer.")
   (xdoc::p
    "This utility may need to be extended and generalized in the future,
     in particular with more customization facilities.")
   (xdoc::@def "xdoc::evmac-desc-function/lambda/macro"))

  (defmacro xdoc::evmac-desc-function/lambda/macro (&key
                                                    (subject '"It")
                                                    (1arg 'nil)
                                                    (1res 'nil)
                                                    (guard 'nil)
                                                    (dont-be-or-call 'nil)
                                                    (additional-function 'nil)
                                                    (additional-lambda 'nil)
                                                    (additional-forms '""))
    `(xdoc::&&
      (xdoc::p
       ,subject " must be one of the following:")
      (xdoc::ul
       (xdoc::li
        "The name of a "
        ,(if 1arg "unary " "")
        "logic-mode function.
         This function must have no input or output @(see acl2::stobj)s."
        ,(if 1res
             " This function must return
              a single (i.e. non-@(tsee acl2::mv)) result."
           "")
        ,(cond ((eq guard t) " This function must be guard-verified.")
               ((eq guard nil) "")
               (t `(xdoc::&&
                    " If "
                    ,guard
                    ", then this function must be guard-verified.")))
        ,(if dont-be-or-call
             `(xdoc::&& " This function must be distinct from "
                        ,dont-be-or-call
                        ".")
           "")
        ,(if additional-function
             `(xdoc::&& " " ,additional-function)
           ""))
       (xdoc::li
        "A "
        ,(if 1arg "unary " "")
        "closed lambda expression
         that only references logic-mode functions.
         This lambda expression must have
         no input or output @(see acl2::stobj)s."
        ,(if 1res
             " This lambda expression must return
              a single (i.e. non-@(tsee acl2::mv)) result."
           "")
        ,(cond ((eq guard t) " The body of this lambda expression
                              must only call guard-verified functions,
                              except possibly
                              in the @(':logic') subterms of @(tsee acl2::mbe)s
                              or via @(tsee acl2::ec-call).")
               ((eq guard nil) "")
               (t `(xdoc::&&
                    " If " ,guard ", then the body of this lambda expression
                     must only call guard-verified functions,
                     except possibly
                     in the @(':logic') subterms of @(tsee acl2::mbe)s
                     or via @(tsee acl2::ec-call).")))
        " As an abbreviation, the name @('mac') of a macro stands for
         the lambda expression @('(lambda (z1 z2 ...) (mac z1 z2 ...))'),
         where @('z1'), @('z2'), ... are the required parameters of @('mac');
         that is, a macro name abbreviates its eta-expansion
         (considering only the macro's required parameters)."
        ,(if dont-be-or-call
             `(xdoc::&& " This lambda expression must not reference "
                        ,dont-be-or-call
                        ".")
           "")
        ,(if additional-lambda
             `(xdoc::&& " " ,additional-lambda)
           ""))
       ,additional-forms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-desc-term
  :short "Construct a common description text for an input that must be a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This text expresses some common requirements
     on this kind of inputs to event macros.")
   (xdoc::p
    "This utility provides some customization facilities:")
   (xdoc::ul
    (xdoc::li
     "The @('subject') parameter must be XDOC text
      that describes the subject of the assertion of the requirements.
      The default is the string @('\"It\"'),
      which should be appropriate if this text follows
      some preceding text that describes what the input is for.")
    (xdoc::li
     "The @('free-vars') parameter must be one of the following:
      (i) XDOC text that describes the allowed free variables in the term;
      (ii) @('nil') (the default) for no requirements on free variables.")
    (xdoc::li
     "The @('1res') parameter must be a boolean
      that specifies whether the term
      must return a single (i.e. non-@(tsee mv)) value or not.")
    (xdoc::li
     "The @('guard') parameter must be one of the following:
      (i) XDOC text that describes the condition under which
      the guards must be verified;
      (ii) @('t'), to indicate that the guards must always be verified;
      (iii) @('nil'), to indicate that there are no requirements
      on the guards being verified.
      The default is @('nil').")
    (xdoc::li
     "The @('dont-call') parameters must one of the following:
      (i) XDOC text that describes functions that this term must not call;
      (ii) @('nil') (the default),
      to indicate that the term may call any function.")
    (xdoc::li
     "The @('additional') parameter must be one of the following:
      (i) XDOC text that describes additional requirements
      for the term (typically a sentence);
      (ii) @('nil') (the default) for no additional text."))
   (xdoc::p
    "Looking at some uses of this utility should make it clearer.")
   (xdoc::p
    "This utility may need to be extended and generalized in the future,
     in particular with more customization facilities.")
   (xdoc::@def "xdoc::evmac-desc-term"))

  (defmacro xdoc::evmac-desc-term (&key
                                   (subject '"It")
                                   (free-vars 'nil)
                                   (1res 'nil)
                                   (guard 'nil)
                                   (dont-call 'nil)
                                   (additional 'nil))
    `(xdoc::&&
      (xdoc::p
       ,subject
       " must be a term that only references logic-mode functions"
       ,(if free-vars
            `(xdoc::&&
              " and that includes no free variables other than "
              ,free-vars)
          "")
       ". This term must have no output @(see acl2::stobj)s."
       ,(if 1res
            " This term must return
              a single (i.e. non-@(tsee acl2::mv)) value."
          "")
       ,(cond ((eq guard t) " This term
                             must only call guard-verified functions,
                             except possibly
                             in the @(':logic') subterms of @(tsee acl2::mbe)s
                             or via @(tsee acl2::ec-call).")
              ((eq guard nil) "")
              (t `(xdoc::&&
                   " If " ,guard ", then this term
                    must only call guard-verified functions,
                    except possibly
                    in the @(':logic') subterms of @(tsee acl2::mbe)s
                    or via @(tsee acl2::ec-call).")))
       ,(if dont-call
            `(xdoc::&& " This term must not reference " ,dont-call ".")
          "")
       ,(if additional
            `(xdoc::&& " " ,additional)
          "")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-appcond
  :short "Construct an applicability condition description
          in the reference documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This generates an @(tsee xdoc::desc).")
   (xdoc::p
    "The @('name') input must be a string
     that names the applicability condition.")
   (xdoc::p
    "The @('main') input must be an XDOC tree
     that contains the main description of the applicability condition,
     consisting of explanatory natural language
     and formal code for the formula(s).")
   (xdoc::p
    "The @('design-notes') and @('design-notes-appcond') inputs
     must be either both present or both absent.
     If present, they must be both XDOC trees:
     the first one references the design notes of the event macro
     (which usually includes a link to the design notes);
     the second one provides the name of the applicability condition
     (usually some mathematical notation) used in the design notes.
     If these two inputs are present,
     the generated XDOC includes text
     relating the applicability condition to the design notes.")
   (xdoc::p
    "If the @('presence') input is present,
     it must be an XDOC tree.
     In this case,
     the generated XDOC includes text
     explaining that the applicability condition is present
     under the condition described by the @('presence') input."))

  (defmacro xdoc::evmac-appcond (name
                                 main
                                 &key
                                 design-notes
                                 design-notes-appcond
                                 presence)
    (declare (xargs :guard (stringp name)))
    `(xdoc::desc
      ,(concatenate 'string "@('" name "')")
      ,main
      ,@(and design-notes
             design-notes-appcond
             `((xdoc::p
                "This corresponds to " ,design-notes-appcond
                " in the " ,design-notes ".")))
      ,@(and presence
             `((xdoc::p
                "This applicability condition if present if and only if "
                ,presence "."))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-topic-design-notes
  :short "Generate an XDOC topic for the design notes of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This utility takes the following arguments:")
   (xdoc::ul
    (xdoc::li
     "The event macro's symbol.")
    (xdoc::li
     "A string for the @('href') link with the actual notes,
      normally of the form @('res/.../<notes>.pdf'), based on the "
     (xdoc::seetopic "xdoc::add-resource-directory" "XDOC resource directory")
     ".")
    (xdoc::li
     "A list of additional parent topics, besides the macro itself.")
    (xdoc::li
     "Zero or more XDOC trees (often just strings)
      to put into the bullets that explain the correspondence between
      the symbols in the design notes and the reference documentation.
      If this list is empty,
      then no bulletted list is generated,
      and no introductory text for it.")
    (xdoc::li
     "Zero or more XDOC trees (often paragraphs)
      that provide some additional explanation
      about how the design notes relate to the event macro
      (e.g. parts of the design notes that are not implemented yet."))
   (xdoc::@def "xdoc::evmac-topic-design-notes"))

  (define xdoc::evmac-topic-design-notes-make-bullets
    ((correspondences xdoc::tree-listp))
    :returns (bullets xdoc::tree-listp :hyp :guard)
    :parents nil
    (cond ((endp correspondences) nil)
          (t (cons (xdoc::li (car correspondences))
                   (xdoc::evmac-topic-design-notes-make-bullets
                    (cdr correspondences))))))

  (defmacro xdoc::evmac-topic-design-notes (macro
                                            notes-ref
                                            &key
                                            additional-parents
                                            correspondences
                                            additional-doc)
    (declare (xargs :guard (and (symbolp macro)
                                (stringp notes-ref)
                                (symbol-listp additional-parents))))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-DESIGN"))
         (parents (cons macro additional-parents))
         (short (concatenate 'string
                             "Design notes for "
                             macro-ref
                             "."))
         (long `(xdoc::topstring
                 (xdoc::p
                  "The design of "
                  ,macro-ref
                  " is described in "
                  (xdoc::a :href ,notes-ref "these notes")
                  ", which use "
                  (xdoc::a :href "res/kestrel-design-notes/notation.pdf"
                    "this notation")
                  ".")
                 ,@(and correspondences
                        `((xdoc::p
                           "The correspondence between
                            the design notes and the reference documentation
                            is the following:")
                          (xdoc::ul-fn
                           nil
                           (xdoc::evmac-topic-design-notes-make-bullets
                            (list ,@correspondences)))))
                 ,@additional-doc)))
      `(defxdoc ,this-topic
         :parents ,parents
         :short ,short
         :long ,long))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-xdoc-constructors-implementation-level
  :parents (event-macro-xdoc-constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document the implementation of
          <see topic='@(url event-macros)'>event macros</see>."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-topic-implementation
  :short "Generate an XDOC topic for the implementation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "The topic lists the names used for arguments and results of functions,
     along with brief descriptions of the names.
     This listing consists of bullet in an unordered list.
     The @(':items') argument must be a list of XDOC trees,
     each of which is wrapped into an @(tsee xdoc::li),
     and the so-wrapped items are put into an @(tsee xdoc::ul).")
   (xdoc::p
    "Certain common items, like the @('state') variable,
     can be included among the items just by setting
     the corresponding keyword options to @('t').")
   (xdoc::p
    "If there are items, the list is omitted altogether.")
   (xdoc::@def "xdoc::evmac-topic-implementation"))

  (define xdoc::evmac-topic-implementation-li-wrap ((items true-listp))
    :returns (li-wrapped-items true-listp)
    (cond ((endp items) nil)
          (t (cons `(xdoc::li ,(car items))
                   (xdoc::evmac-topic-implementation-li-wrap (cdr items))))))

  (defmacro xdoc::evmac-topic-implementation (macro
                                              &key
                                              items
                                              item-state
                                              item-wrld
                                              item-ctx)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-IMPLEMENTATION"))
         (parent-topic macro)
         (short (concatenate 'string "Implementation of " macro-ref "."))
         (all-items
          (append (and item-state
                       '((xdoc::&&
                          "@('state') is the ACL2 "
                          (xdoc::seetopic "acl2::state" "state")
                          ".")))
                  (and item-wrld
                       '((xdoc::&&
                          "@('wrld') is the ACL2 "
                          (xdoc::seetopic "acl2::world" "world")
                          ".")))
                  (and item-ctx
                       '("@('ctx') is the context used for errors."))
                  items))
         (long (and all-items
                    `(xdoc::topstring
                      (xdoc::p
                       "The implementation functions have arguments,
                        as well as results (in the "
                       (xdoc::seetopic "std::returns-specifiers"
                                       "@(':returns') specifiers")
                       "), consistently named as follows:")
                      (xdoc::ul
                       ,@(xdoc::evmac-topic-implementation-li-wrap all-items))
                      (xdoc::p
                       "Implementation functions' arguments and results
                        that are not listed above
                        are described in, or clear from,
                        those functions' documentation.")))))
      `(defxdoc+ ,this-topic
         :parents (,parent-topic)
         :short ,short
         ,@(and long (list :long long))
         :order-subtopics t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-topic-library-extensions
  :short "Generate an XDOC topic for the library extensions
          that are part of the implementation of an event macro."
  :long (xdoc::topstring-@def "xdoc::evmac-topic-library-extensions")

  (defmacro xdoc::evmac-topic-library-extensions (macro)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-LIBRARY-EXTENSIONS"))
         (parent-topic (add-suffix macro "-IMPLEMENTATION"))
         (short (concatenate 'string "Library extensions for " macro-ref "."))
         (long (xdoc::topstring-p
                "These are used by, but more general than, "
                macro-ref
                ". Thus, they should be moved
                 to more general libraries eventually.")))
      `(defxdoc+ ,this-topic
         :parents (,parent-topic)
         :short ,short
         :long ,long
         :order-subtopics t
         :default-parent t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-topic-input-processing
  :short "Generate an XDOC topic for the input processing
          that is part of the implementation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro accepts additional pieces of XDOC text,
     which are added at the end of the generated @(':long').")
   (xdoc::@def "xdoc::evmac-topic-input-processing"))

  (defmacro xdoc::evmac-topic-input-processing (macro &rest additional)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-INPUT-PROCESSING"))
         (parent-topic (add-suffix macro "-IMPLEMENTATION"))
         (short (concatenate 'string
                             "Input processing performed by "
                             macro-ref
                             "."))
         (long `(xdoc::topstring
                 (xdoc::p
                  "This involves validating the inputs.
                   When validation fails, "
                  (xdoc::seetopic "acl2::er" "soft errors")
                  " occur.
                   Thus, generally the input processing functions return "
                  (xdoc::seetopic "acl2::error-triple" "error triples")
                  ".")
                 ,@additional)))
      `(defxdoc+ ,this-topic
         :parents (,parent-topic)
         :short ,short
         :long ,long
         :order-subtopics t
         :default-parent t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-topic-event-generation
  :short "Generate an XDOC topic for the event generation
          that is part of the implementation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "An event macro may generate some events only locally;
     in this case, the @(':some-local-p') argument must be @('t').
     An event macro may generate some events both locally and non-locally,
     where the local variant has proof hints and the non-local variant does not;
     in this case, the @(':some-local-nonlocal-p') argument must be @('t').
     These arguments are used to customize the generated @(':long').")
   (xdoc::@def "xdoc::evmac-topic-event-generation"))

  (defmacro xdoc::evmac-topic-event-generation (macro
                                                &key
                                                some-local-p
                                                some-local-nonlocal-p)
    (declare (xargs :guard (and (symbolp macro)
                                (booleanp some-local-p)
                                (booleanp some-local-nonlocal-p))))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-EVENT-GENERATION"))
         (parent-topic (add-suffix macro "-IMPLEMENTATION"))
         (short (concatenate 'string
                             "Event generation performed by "
                             macro-ref
                             "."))
         (para-local-nonlocal?
          (and some-local-nonlocal-p
               '((xdoc::p
                  "Some events are generated in two slightly different variants:
                   one that is local to the generated "
                  (xdoc::seetopic "acl2::encapsulate" "@(tsee encapsulate)")
                  ", and one that is exported from the "
                  (xdoc::seetopic "acl2::encapsulate" "@(tsee encapsulate)")
                  ". Proof hints are in the former but not in the latter,
                   thus keeping the ACL2 history ``clean'';
                   some proof hints may refer to events
                   that are generated only locally to the "
                  (xdoc::seetopic "acl2::encapsulate" "@(tsee encapsulate)")
                  "."))))
         (para-local?
          (and some-local-p
               '((xdoc::p
                  "Some events are generated only locally to the generated "
                  (xdoc::seetopic "acl2::encapsulate" "@(tsee encapsulate)")
                  ". These are auxiliary events
                   needed to introduce the non-local (i.e. exported) events,
                   but whose presence in the ACL2 history is no longer needed
                   once the exported events have been introduced.
                   These only-local events have generated fresh names.
                   In contrast, exported events have names
                   that are user-controlled, directly or indirectly."))))
         (long? (and (or some-local-nonlocal-p
                         some-local-p)
                     `(xdoc::topstring
                       ,@para-local-nonlocal?
                       ,@para-local?))))
      `(defxdoc+ ,this-topic
         :parents (,parent-topic)
         :short ,short
         ,@(and long? (list :long long?))
         :order-subtopics t
         :default-parent t))))
