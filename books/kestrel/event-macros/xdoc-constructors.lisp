; Event Macros Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "std/util/define" :dir :system)
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

(defmacro+ xdoc::evmac-section (title &rest content)
  :short "Construct a section
          of the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "This provides more abstraction than using a specific heading.")
  `(xdoc::&&
    (xdoc::h3 ,title)
    ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-subsection (title &rest content)
  :short "Construct a subsection
          of the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "This provides more abstraction than using a specific heading.")
  `(xdoc::&&
    (xdoc::h4 ,title)
    ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-subsubsection (title &rest content)
  :short "Construct a subsubsection
          of the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "This provides more abstraction than using a specific heading.")
  `(xdoc::&&
    (xdoc::h5 ,title)
    ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-subsubsubsection (title &rest content)
  :short "Construct a subsubsubsection
          of the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "This provides more abstraction than using a specific heading.")
  `(xdoc::&&
    (xdoc::h6 ,title)
    ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-intro-title*
  "Introduction")

(defmacro+ xdoc::evmac-section-intro (&rest content)
  :short "Construct the introduction section
          of the user documentation of an event macro."
  `(xdoc::evmac-section xdoc::*evmac-section-intro-title*
                        ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-form-title*
  "General Form")

(defmacro+ xdoc::evmac-section-form (&rest content)
  :short "Construct the general form section
          of the user documentation of an event macro."
  `(xdoc::evmac-section xdoc::*evmac-section-form-title*
                        ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-inputs-title*
  "Inputs")

(defmacro+ xdoc::evmac-section-inputs (&rest content)
  :short "Construct the inputs section
          of the user documentation of an event macro."
  `(xdoc::evmac-section xdoc::*evmac-section-inputs-title*
                        ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-appconds-title*
  "Applicability Conditions")

(defmacro+ xdoc::evmac-section-appconds (macro &rest content)
  (declare (xargs :guard (symbolp macro)))
  :short "Construct the applicability conditions section
          of the user documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this documentation is part of the XDOC topic
     whose name is the name of the macro,
     the @('macro-ref') variable is not a link."))
  (b* ((macro-name (string-downcase (symbol-name macro)))
       (macro-ref (concatenate 'string "@('" macro-name "')"))
       (inputs-ref (concatenate 'string
                                "`"
                                xdoc::*evmac-section-inputs-title*
                                "' section")))
    `(xdoc::evmac-section
      xdoc::*evmac-section-appconds-title*
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
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-generated-title*
  "Generated Events")

(defmacro+ xdoc::evmac-section-generated (&rest content)
  :short "Construct the generated events section
          of the user documentation of an event macro."
  `(xdoc::evmac-section xdoc::*evmac-section-generated-title*
                        ,@content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst xdoc::*evmac-section-redundancy-title*
  "Redundancy")

(defmacro+ xdoc::evmac-section-redundancy (macro)
  (declare (xargs :guard (symbolp macro)))
  :short "Construct the redundancy section
          of the user documentation of an event macro."
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
     the @('macro-ref') variable is not a link."))
  (b* ((macro-name (string-downcase (symbol-name macro)))
       (macro-ref (concatenate 'string "@('" macro-name "')")))
    `(xdoc::evmac-section
      xdoc::*evmac-section-redundancy-title*
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
         Thus, no successive call may be redundant with such a call.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-input-hints (&key additional)
  :short "Construct a description of the @(':hints') input
          for the user documentation of an event macro."
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
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-input-print (macro &key additional)
  :short "Construct a description of the @(':print') input
          for the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "Since this documentation is part of the XDOC topic
    whose name is the name of the macro,
    the @('macro-ref') variable is not a link.")
  (declare (xargs :guard (symbolp macro)))
  (b* ((macro-name (string-downcase (symbol-name macro)))
       (macro-ref (concatenate 'string "@('" macro-name "')")))
    `(xdoc::desc
      "@(':print') &mdash; default @(':result')"
      (xdoc::p
       "Specifies what is printed on the screen
        (see @(see acl2::event-macro-screen-printing)).")
      (xdoc::p
       "It must be one of the following:")
      (xdoc::ul
       (xdoc::li
        "@('nil'), to print nothing (not even error output).")
       (xdoc::li
        "@(':error'), to print only error output (if any).")
       (xdoc::li
        "@(':result'), to print, besides any error output,
         also the "
        (xdoc::seetopic "acl2::event-macro-results" "results")
        " of " ,macro-ref ".
         This is the default value of the @(':print') input.")
       (xdoc::li
        "@(':info'), to print,
         besides any error output and the results,
         also some additional information about
         the internal operations of " ,macro-ref ".")
       (xdoc::li
        "@(':all'), to print,
          besides any error output,
          the results,
          and the additional information,
          also ACL2's output in response to all the submitted events."))
      (xdoc::p
       "If the call of " ,macro-ref " is redundant,
        an indication to that effect is printed on the screen,
        unless @(':print') is @('nil').")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-input-show-only (macro &key additional)
  :short "Construct a description of the @(':show-only') input
          for the user documentation of an event macro."
  :long
  (xdoc::topstring-p
   "Since this documentation is part of the XDOC topic
    whose name is the name of the macro,
    the @('macro-ref') variable is not a link.")
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
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-desc-input-name (prefix
                                        &key
                                        desc
                                        auto-desc
                                        additional
                                        name-rest)
  :short "Construct a description of a @(':...-name') input
          for the user documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for an input to determine the name of
     an entity (e.g. a function) generated by the event macro.")
   (xdoc::p
    "The @('...') in @(':...-name') is passed as
     the @('prefix') argument of this macro.")
   (xdoc::p
    "A description of the entitty whose name is being determined
     is passed as the @('desc') argument of this macro.")
   (xdoc::p
    "The @('auto-desc') argument of this macro describes the name used
     when the @(':...-name') input is @(':auto').")
   (xdoc::p
    "An XDOC tree of additional text can be passed
     as the @('additional') argument of this macro.")
   (xdoc::p
    "The @('name-rest') argument of this macro is
     the name that the generated documentation says that will be used
     as the name of the entity in the rest of the documentation page."))
  (declare (xargs :guard (and (stringp prefix)
                              (stringp desc)
                              (stringp auto-desc)
                              (stringp name-rest))))
  `(xdoc::desc
    ,(concatenate 'string
                  "@(':" prefix "-name') &mdash; default @(':auto')")
    (xdoc::p
     "Determines the name of " ,desc ".")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@(':auto'), to use " ,auto-desc ".")
     (xdoc::li
      "Any other symbol, to use as the name."))
    ,@(and additional (list additional))
    (xdoc::p
     "In the rest of this documentation page,
      let @('" ,name-rest "') be this name.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-desc-input-enable-t/nil (prefix
                                                &key
                                                default
                                                desc)
  :short "Construct a description of a @(':...-enable') input
          for the user documentation of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for an input to determine the enablement of
     an entity (e.g. a function) generated by the event macro.")
   (xdoc::p
    "The @('...') in @(':...-enable') is passed as
     the @('prefix') argument of this macro.")
   (xdoc::p
    "The default is passed as the @('default') argument of this macro.")
   (xdoc::p
    "The description of the entity is passed as
     the @('desc') argument of this macro."))
  (declare (xargs :guard (and (stringp prefix)
                              (booleanp default)
                              (stringp desc))))
  `(xdoc::desc
    ,(concatenate 'string
                  "@(':" prefix "-enable') &mdash; default "
                  (if default "@('t')" "@('nil')"))
    (xdoc::p
     "Determines whether " ,desc " is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable.")
     (xdoc::li
      "@('nil'), to disable."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-desc-function/lambda/macro (&key
                                                   (subject '"It")
                                                   (1arg 'nil)
                                                   (1res 'nil)
                                                   (guard 'nil)
                                                   (dont-be-or-call 'nil)
                                                   (additional-function 'nil)
                                                   (additional-lambda 'nil)
                                                   (additional-forms '""))
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
     in particular with more customization facilities."))
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
     ,additional-forms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-desc-term (&key
                                  (subject '"It")
                                  (free-vars 'nil)
                                  (1res 'nil)
                                  (guard 'nil)
                                  (dont-call 'nil)
                                  (additional 'nil))
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
     in particular with more customization facilities."))
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
        ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-appcond (name
                                main
                                &key
                                design-notes
                                design-notes-appcond
                                presence)
  :short "Construct an applicability condition description
          in the user documentation of an event macro."
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
              "This applicability condition is present if and only if "
              ,presence ".")))))

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
      the symbols in the design notes and the user documentation.
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
                            the design notes and the user documentation
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
     This listing consists of bullets  in an unordered list.
     The @(':items') argument must be a list of XDOC trees,
     each of which is wrapped into an @(tsee xdoc::li),
     and the so-wrapped items are put into an @(tsee xdoc::ul).")
   (xdoc::p
    "We also provide some named constants for certain common items,
     like the @('state') variable.
     We also provide some functions for certain common kinds of items,
     like the user inputs to the event macro.")
   (xdoc::p
    "If there are no items, the list is omitted altogether.")
   (xdoc::p
    "This macro also provide a @(':default-parent') option,
     which is @('nil') by default and is passed to @(tsee defxdoc+).")
   (xdoc::@def "xdoc::evmac-topic-implementation"))

  (define xdoc::evmac-topic-implementation-li-wrap ((items true-listp))
    :parents nil
    :returns (li-wrapped-items true-listp)
    (cond ((endp items) nil)
          (t (cons `(xdoc::li ,(car items))
                   (xdoc::evmac-topic-implementation-li-wrap (cdr items))))))

  (defmacro xdoc::evmac-topic-implementation (macro &key items default-parent)
    (declare (xargs :guard (symbolp macro)))
    (b* ((macro-name (string-downcase (symbol-name macro)))
         (macro-ref (concatenate 'string "@(tsee " macro-name ")"))
         (this-topic (add-suffix macro "-IMPLEMENTATION"))
         (parent-topic macro)
         (short (concatenate 'string "Implementation of " macro-ref "."))
         (long (and items
                    `(xdoc::topstring
                      (xdoc::p
                       "The implementation functions have arguments,
                        as well as results (in the "
                       (xdoc::seetopic "std::returns-specifiers"
                                       "@(':returns') specifiers")
                       "), consistently named as follows:")
                      (xdoc::ul
                       ,@(xdoc::evmac-topic-implementation-li-wrap items))
                      (xdoc::p
                       "Implementation functions' arguments and results
                        that are not listed above
                        are described in, or clear from,
                        those functions' documentation.")))))
      `(defxdoc+ ,this-topic
         :parents (,parent-topic)
         :short ,short
         ,@(and long (list :long long))
         :order-subtopics t
         :default-parent ,default-parent)))

  (defconst xdoc::*evmac-topic-implementation-item-state*
    (xdoc::&& "@('state') is the ACL2 "
              (xdoc::seetopic "acl2::state" "state")
              "."))

  (defconst xdoc::*evmac-topic-implementation-item-wrld*
    (xdoc::&& "@('wrld') is the ACL2 "
              (xdoc::seetopic "acl2::world" "world")
              "."))

  (defconst xdoc::*evmac-topic-implementation-item-ctx*
    (xdoc::&& "@('ctx') is the "
              (xdoc::seetopic "ctx" "context")
              " used for errors."))

  (defconst xdoc::*evmac-topic-implementation-item-call*
    "@('call') is the call of the event macro.")

  (defconst xdoc::*evmac-topic-implementation-item-names-to-avoid*
    "@('names-to-avoid') is a cumulative list of names of generated events,
     used to ensure the absence of name clashes in the generated events.")

  (defconst xdoc::*evmac-topic-implementation-item-appcond-thm-names*
    "@('appcond-thm-names') is an alist
     from the keywords that identify the applicability conditions
     to the corresponding generated theorem names.")

  (define xdoc::evmac-topic-implementation-item-input ((name stringp))
    :parents nil
    (xdoc::&&
     "@('" name "') is the homonymous input to the event macro."))

  (define xdoc::evmac-topic-implementation-item-input-untyped/typed
    ((name stringp))
    :parents nil
    (xdoc::&& "@('" name "') is the homonymous input to the event macro
               if it has no type;
               otherwise, it is the (possibly different) typed value
               resulting from processing that input."))

  (define xdoc::evmac-topic-implementation-item-fn-doc ((name stringp))
    :parents nil
    (xdoc::&& "@('" name "') is the homonymous function symbol "
              "described in the user documentation."))

  (define xdoc::evmac-topic-implementation-item-thm-doc ((name stringp))
    :parents nil
    (xdoc::&& "@('" name "') is the homonymous theorem symbol "
              "described in the user documentation."))

  (define xdoc::evmac-topic-implementation-item-var-doc ((name stringp))
    :parents nil
    (xdoc::&& "@('" name "') is the homonymous variable symbol "
              "described in the user documentation.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-topic-library-extensions (macro)
  :short "Generate an XDOC topic for the library extensions
          that are part of the implementation of an event macro."
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
       :default-parent t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-topic-input-processing (macro &rest additional)
  :short "Generate an XDOC topic for the input processing
          that is part of the implementation of an event macro."
  :long
  (xdoc::topstring-p
   "This macro accepts additional pieces of XDOC text,
    which are added at the end of the generated @(':long').")
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
                "See "
                (xdoc::seetopic "acl2::event-macro-input-processing"
                                "input processing")
                " for general background.")
               ,@additional)))
    `(defxdoc+ ,this-topic
       :parents (,parent-topic)
       :short ,short
       :long ,long
       :order-subtopics t
       :default-parent t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::evmac-topic-event-generation (macro
                                               &key
                                               some-local-p
                                               some-local-nonlocal-p
                                               some-nonlocal-p)
  :short "Generate an XDOC topic for the event generation
          that is part of the implementation of an event macro."
  :long
  (xdoc::topstring-p
   "An event macro may generate some events only locally;
    in this case, the @(':some-local-p') argument must be @('t').
    An event macro may generate some events both locally and non-locally,
    where the local variant has proof hints and the non-local variant does not;
    in this case, the @(':some-local-nonlocal-p') argument must be @('t').
    An event macro may generate some events only non-locally;
    in this case the @(':some-nonlocal-p') argument must be @('t').
    These arguments are used to customize the generated @(':long').")
  (declare (xargs :guard (and (symbolp macro)
                              (booleanp some-local-p)
                              (booleanp some-local-nonlocal-p)
                              (booleanp some-nonlocal-p))))
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
       (para-nonlocal?
        (and some-nonlocal-p
             '((xdoc::p
                "Some events are generated only non-locally to the generated "
                (xdoc::seetopic "acl2::encapsulate" "@(tsee encapsulate)")
                ", i.e. they are exported,
                 without local counterparts."))))
       (long? (and (or some-local-nonlocal-p
                       some-local-p
                       some-nonlocal-p)
                   `(xdoc::topstring
                     ,@para-local-nonlocal?
                     ,@para-local?
                     ,@para-nonlocal?))))
    `(defxdoc+ ,this-topic
       :parents (,parent-topic)
       :short ,short
       ,@(and long? (list :long long?))
       :order-subtopics t
       :default-parent t)))
