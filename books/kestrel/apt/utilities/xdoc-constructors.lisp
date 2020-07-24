; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ xdoc::apt-constructors
  :parents (utilities xdoc::composite-constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document <see topic='@(url apt)'>APT</see> transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('xdoc::desc-apt-input-...') utilities construct
     <see topic='@(url xdoc::desc)'>descriptions</see>
     of inputs common to multiple APT transformations.
     Each such utility includes zero or more parameters
     to customize the description,
     as well as zero or more additional items (e.g. paragraphs)
     that are appended to the end of the generated description."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-old (&rest additional)
  :short "Build a description of the @('old') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@('old')"
    (xdoc::p
     "Denotes the target function to transform.")
    (xdoc::p
     "It must be the name of a function,
      or a <see topic='@(url acl2::numbered-names)'>numbered name</see>
      with a wildcard index that
      <see topic='@(url acl2::resolve-numbered-name-wildcard)'>resolves</see>
      to the name of a function.
      In the rest of this documentation page, for expository convenience,
      it is assumed that @('old') is the name of the denoted function.")
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-new-name (&rest additional)
  :short "Build a description of the @(':new-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':new-name') &mdash; default @(':auto')"
    (xdoc::p
     "Determines the name of the generated new function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@(':auto'), to generate the name automatically
       as described in @(see function-name-generation).")
     (xdoc::li
      "Any other symbol, to use as the name of the function."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('new') be this function.")
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-new-enable (&rest additional)
  :short "Build a description of the @(':new-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':new-enable') &mdash; default @(':auto')"
    (xdoc::p
     "Determines whether @('new') is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable it.")
     (xdoc::li
      "@('nil'), to disable it.")
     (xdoc::li
      "@(':auto'), to enable it iff @('old') is enabled."))
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-wrapper (&rest additional)
  :short "Build a description of the @(':wrapper') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':wrapper') &mdash; default @('nil')"
    (xdoc::p
     "Determines whether the wrapper function is generated.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to generate it.")
     (xdoc::li
      "@('nil'), to not generate it."))
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-wrapper-name (&rest additional)
  :short "Build a description of the @(':wrapper-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':wrapper-name') &mdash; default @(':auto')"
    (xdoc::p
     "Determines the name of the generated wrapper function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@(':auto'), to generate the name automatically
       as described in @(see function-name-generation).")
     (xdoc::li
      "Any other symbol, to use as the name of the function."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    (xdoc::p
     "In the rest of this documentation page,
      let @('wrapper') be this function.")
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-wrapper-enable (&rest additional)
  :short "Build a description of the @(':wrapper-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':wrapper-enable') &mdash; default @('t')"
    (xdoc::p
     "Determines whether @('wrapper') is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable it.")
     (xdoc::li
      "@('nil'), to disable it."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    ,@additional))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-old-to-new-name ()
  :short "Build a description of the @(':old-to-new-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':old-to-new-name') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines the name of the theorem that
      rewrites the old function in terms of the new function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "A keyword, to use as separator between
       the names of @('old') and @('new').
       A keyword @(':kwd') specifies the theorem name @('oldkwdnew'),
       in the same package as @('new').")
     (xdoc::li
      "Any other symbol, to use as the name of the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-old-to-new-name)."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('old-to-new') be the name of this theorem.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-new-to-old-name ()
  :short "Build a description of the @(':new-to-old-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':new-to-old-name') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines the name of the theorem that
      rewrites the new function in terms of the old function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "A keyword, to use as separator between
       the names of @('new') and @('old').
       A keyword @(':kwd') specifies the theorem name @('newkwdold'),
       in the same package as @('new').")
     (xdoc::li
      "Any other symbol, to use as the name of the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-new-to-old-name)."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('new-to-old') be the name of this theorem.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-old-to-new-enable ()
  :short "Build a description of the @(':old-to-new-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':old-to-new-enable') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines whether the @('old-to-new') theorem is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable the theorem.")
     (xdoc::li
      "@('nil'), to disable the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-old-to-new-enable)."))
    (xdoc::p
     "If this input is @('t'),
      the @(':new-to-old-enable') input must be @('nil').
      At most one of these two inputs may be @('t') at any time.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-new-to-old-enable ()
  :short "Build a description of the @(':new-to-old-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':new-to-old-enable') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines whether the @('new-to-old') theorem is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable the theorem.")
     (xdoc::li
      "@('nil'), to disable the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-new-to-old-enable)."))
    (xdoc::p
     "If this input is @('t'),
      the @(':old-to-new-enable') input must be @('nil').
      At most one of these two inputs may be @('t') at any time.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-old-to-wrapper-name ()
  :short "Build a description of the @(':old-to-wrapper-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':old-to-wrapper-name') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines the name of the theorem that
      rewrites the old function in terms of the wrapper function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "A keyword, to use as separator between
       the names of @('old') and @('wrapper').
       A keyword @(':kwd') specifies the theorem name @('oldkwdwrapper'),
       in the same package as @('wrapper').")
     (xdoc::li
      "Any other symbol, to use as the name of the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-old-to-wrapper-name)."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    (xdoc::p
     "In the rest of this documentation page,
      let @('old-to-wrapper') be the name of this theorem
      (if it is generated).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-wrapper-to-old-name ()
  :short "Build a description of the @(':wrapper-to-old-name') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':wrapper-to-old-name') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines the name of the theorem that
      rewrites the wrapper function in terms of the old function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "A keyword, to use as separator between
       the names of @('wrapper') and @('old').
       A keyword @(':kwd') specifies the theorem name @('wrapperkwdold'),
       in the same package as @('wrapper').")
     (xdoc::li
      "Any other symbol, to use as the name of the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-wrapper-to-old-name)."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    (xdoc::p
     "In the rest of this documentation page,
      let @('wrapper-to-old') be the name of this theorem
      (if it is generated).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-old-to-wrapper-enable ()
  :short "Build a description of the @(':old-to-wrapper-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':old-to-wrapper-enable') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines whether the @('old-to-wrapper') theorem is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable the theorem.")
     (xdoc::li
      "@('nil'), to disable the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-old-to-wrapper-enable)."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    (xdoc::p
     "If this input is @('t'),
      the @(':wrapper-to-old-enable') input must be @('nil').
      At most one of these two inputs may be @('t') at any time.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-wrapper-to-old-enable ()
  :short "Build a description of the @(':wrapper-to-old-enable') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':wrapper-to-old-enable') &mdash;
     default from <see topic='@(url defaults-table)'>table</see>"
    (xdoc::p
     "Determines whether the @('wrapper-to-old') theorem is enabled.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable the theorem.")
     (xdoc::li
      "@('nil'), to disable the theorem.")
     (xdoc::li
      "Absent, to use the value from the APT defaults table,
       which is set via @(tsee set-default-input-wrapper-to-old-enable)."))
    (xdoc::p
     "This input may be present only if the @(':wrapper') input is @('t').")
    (xdoc::p
     "If this input is @('t'),
      the @(':old-to-wrapper-enable') input must be @('nil').
      At most one of these two inputs may be @('t') at any time.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-thm-name (wrapper? &rest additional)
  (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
  :short "Build a description of the @(':thm-name') input
          for the user documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('wrapper?') parameter of this macro
     has the value @(':never') when the transformation
     never generates a wrapper;
     it has the value @(':optional') when the transformation includes
     a @(':wrapper') input that determines whether
     the wrapper is generated or not (i.e. the wrapper is optional);
     it has the value @(':always') when the transformation
     always generates the wrapper.")
   (xdoc::p
    "The theorem relates the old function to the new function
     when there is no wrapper function,
     while it relates the old function to the wrapper function
     where there is a wrapper function.
     Thus, the description is tailored based on the @('wrapper?') parameter."))
  (b* ((new/wrapper-ref
        (case wrapper?
          (:never "@('new')")
          (:optional "@('new') (if the @(':wrapper') input is @('nil')) or
                      @('wrapper') (if the @(':wrapper') input is @('t'))")
          (:always "@('wrapper')")))
       (thm-name
        (case wrapper?
          (:never "@('old-to-new')")
          (:optional "@('old-to-new')
                      (if the @(':wrapper') input is @('nil')) or
                      @('old-to-wrapper')
                      (if the @(':wrapper') input is @('t'))")
          (:always "@('old-to-wrapper')"))))
    `(xdoc::desc
      "@('thm-name') &mdash; default @(':auto')"
      (xdoc::p
       "Determines the name of the theorem that relates @('old') to "
       ,new/wrapper-ref
       ":")
      (xdoc::ul
       (xdoc::li
        "@(':auto'), to use the "
        (xdoc::seetopic "acl2::paired-names" "paired name")
        " obtained by "
        (xdoc::seetopic "acl2::make-paired-name" "pairing")
        " the name of @('old') and the name of "
        ,new/wrapper-ref
        ", putting the result into the same package as "
        ,new/wrapper-ref
        ".")
       (xdoc::li
        "Any other symbol
         (that is not in the main Lisp package and that is not a keyword),
         to use as the name of the theorem."))
      (xdoc::p
       "In the rest of this documentation page, let "
       ,thm-name
       " be this theorem.")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-thm-enable (wrapper? &rest additional)
  (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
  :short "Build a description of the @(':thm-enable') input
          for the user documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('wrapper?') parameter of this macro
     has the value @(':never') when the transformation
     never generates a wrapper;
     it has the value @(':optional') when the transformation includes
     a @(':wrapper') input that determines whether
     the wrapper is generated or not (i.e. the wrapper is optional);
     it has the value @(':always') when the transformation
     always generates the wrapper.")
   (xdoc::p
    "This transformation input refers to the theorem that relates
     the old function to either the new function or the wrapper function,
     depending on the @('wrapper?') parameter."))
  (b* ((thm-name-ref
        (case wrapper?
          (:never "@('old-to-new')")
          (:optional "@('old-to-new')
                        (if the @(':wrapper') input is @('nil')) or
                        @('old-to-wrapper')
                        (if the @(':wrapper') input is @('t'))")
          (:always "@('old-to-wrapper')"))))
    `(xdoc::desc
      "@(':thm-enable') &mdash; default @('t')"
      (xdoc::p
       "Determines whether "
       ,thm-name-ref
       " is enabled:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to enable it.")
       (xdoc::li
        "@('nil'), to disable it."))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-verify-guards (wrapper? &rest additional)
  (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
  :short "Build a description of the @(':verify-guards') input
          for the user documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('wrapper?') parameter of this macro
     has the value @(':never') when the transformation
     never generates a wrapper;
     it has the value @(':optional') when the transformation includes
     a @(':wrapper') input that determines whether
     the wrapper is generated or not (i.e. the wrapper is optional);
     it has the value @(':always') when the transformation
     always generates the wrapper.")
   (xdoc::p
    "This involves the new function,
     and also the wrapper function when present.
     This is determined by the @('wrapper?') parameter of this macro."))
  (b* ((new/wrapper-ref
        (case wrapper?
          (:never "@('new')")
          (:optional "@('new') and (if generated) @('wrapper')")
          (:always "@('new') and @('wrapper')")))
       (is/are
        (case wrapper?
          (:never "is")
          (:optional "is/are")
          (:always "are")))
       (it/them
        (case wrapper?
          (:never "it")
          (:optional "it/them")
          (:always "them"))))
    `(xdoc::desc
      "@(':verify-guards') &mdash; default @(':auto')"
      (xdoc::p
       "Determines whether "
       ,new/wrapper-ref
       " "
       ,is/are
       " guard-verified:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to guard-verify "
        ,it/them
        ".")
       (xdoc::li
        "@('nil'), to not guard-verify "
        ,it/them
        ".")
       (xdoc::li
        "@(':auto'), to guard-verify "
        ,it/them
        " iff @('old') is guard-verified."))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xdoc::desc-apt-input-untranslate (&rest additional)
  :short "Build a description of the @(':untranslate') input
          for the user documentation of an APT transformation."
  `(xdoc::desc
    "@(':untranslate') &mdash; default @(':nice')"
    (xdoc::p
     "Specifies if and how the body of @('new') should be turned
      from internal translated form to external untranslated form.")
    (xdoc::p
     "It must be an "
     (xdoc::seetopic "untranslate-specifier" "untranslate specifier")
     "; see that documentation topic for details.")
    ,@additional))
