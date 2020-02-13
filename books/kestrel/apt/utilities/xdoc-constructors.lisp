; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

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

(defsection xdoc::desc-apt-input-old
  :short "Build a description of the @('old') input
          for the user documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-old")
  (defmacro xdoc::desc-apt-input-old (&rest additional)
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
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-new-name
  :short "Build a description of the @(':new-name') input
          for the user documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-new-name")
  (defmacro xdoc::desc-apt-input-new-name (&rest additional)
    `(xdoc::desc
      "@(':new-name') &mdash; default @(':auto')"
      (xdoc::p
       "Determines the name of the generated new function:")
      (xdoc::ul
       (xdoc::li
        "@(':auto'),
         to use the <see topic='@(url acl2::numbered-names)'>numbered name</see>
         obtained by
         <see topic='@(url acl2::next-numbered-name)'>incrementing</see>
         the index of @('old').")
       (xdoc::li
        "Any other symbol
         (that is not in the main Lisp package and that is not a keyword),
         to use as the name of the function."))
      (xdoc::p
       "In the rest of this documentation page,
        let @('new') be this function.")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-new-enable
  :short "Build a description of the @(':new-enable') input
          for the user documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-new-enable")
  (defmacro xdoc::desc-apt-input-new-enable (&rest additional)
    `(xdoc::desc
      "@(':new-enable') &mdash; default @(':auto')"
      (xdoc::p
       "Determines whether @('new') is enabled:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to enable it.")
       (xdoc::li
        "@('nil'), to disable it.")
       (xdoc::li
        "@(':auto'), to enable it iff @('old') is enabled."))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-wrapper
  :short "Build a description of the @(':wrapper') input
          for the user documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-wrapper")
  (defmacro xdoc::desc-apt-input-wrapper (&rest additional)
    `(xdoc::desc
      "@(':wrapper') &mdash; default @('nil')"
      (xdoc::p
       "Determines whether the wrapper function is generated:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to generate it.")
       (xdoc::li
        "@('nil'), to not generate it."))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-wrapper-name
  :short "Build a description of the @(':wrapper-name') input
          for the user documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('wrapper?') parameter of this macro
     has the value @(':optional') when the transformation includes
     a @(':wrapper') input that determines whether
     the wrapper is generated or not (i.e. the wrapper is optional);
     it has the value @(':always') when the transformation
     always generates the wrapper.
     If the transformation never generates a wrapper,
     this macro should not be called.")
   (xdoc::p
    "If the wrapper is optional, we generate some documentation text
     asserting that the @(':wrapper-name') input may be provided
     only if the wrapper is generated.
     If the wrapper is always generated, no such text is generated.")
   (xdoc::@def "xdoc::desc-apt-input-wrapper-name"))
  (defmacro xdoc::desc-apt-input-wrapper-name (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:optional :always))))
    `(xdoc::desc
      "@(':wrapper-name') &mdash; default @(':auto')"
      (xdoc::p
       "Determines the name of the generated wrapper function:")
      (xdoc::ul
       (xdoc::li
        "@(':auto'),
         to use the concatenation of the name of @('new') with @('-wrapper').")
       (xdoc::li
        "Any other symbol
         (that is not in the main Lisp package and that is not a keyword),
         to use as the name of the function."))
      ,@(and (eq wrapper? :optional)
             (list
              '(xdoc::p
                "This input may be present
                 only if the @(':wrapper') input is @('t').")))
      (xdoc::p
       "In the rest of this documentation page,
        let @('wrapper') be this function.")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-wrapper-enable
  :short "Build a description of the @(':wrapper-enable') input
          for the user documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('wrapper?') parameter of this macro
     has the value @(':optional') when the transformation includes
     a @(':wrapper') input that determines whether
     the wrapper is generated or not (i.e. the wrapper is optional);
     it has the value @(':always') when the transformation
     always generates the wrapper.
     If the transformation never generates a wrapper,
     this macro should not be called.")
   (xdoc::p
    "If the wrapper is optional, we generate some documentation text
     asserting that the @(':wrapper-enable') input may be provided
     only if the wrapper is generated.
     If the wrapper is always generated, no such text is generated.")
   (xdoc::@def "xdoc::desc-apt-input-wrapper-enable"))
  (defmacro xdoc::desc-apt-input-wrapper-enable (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:optional :always))))
    `(xdoc::desc
      "@(':wrapper-enable') &mdash; default @('t')"
      (xdoc::p
       "Determines whether @('wrapper') is enabled:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to enable it.")
       (xdoc::li
        "@('nil'), to disable it."))
      ,@(and (eq wrapper? :optional)
             (list
              '(xdoc::p
                "This input may be present
                 only if the @(':wrapper') input is @('t').")))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-thm-name
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
     Thus, the description is tailored based on the @('wrapper?') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-thm-name"))
  (defmacro xdoc::desc-apt-input-thm-name (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
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
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-thm-enable
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
     depending on the @('wrapper?') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-thm-enable"))
  (defmacro xdoc::desc-apt-input-thm-enable (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
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
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-non-executable
  :short "Build a description of the @(':non-executable') input
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
     This is determined by the @('wrapper?') parameter of this macro.")
   (xdoc::@def "xdoc::desc-apt-input-non-executable"))
  (defmacro xdoc::desc-apt-input-non-executable (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
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
        "@(':non-executable') &mdash; default @(':auto')"
        (xdoc::p
         "Determines whether "
         ,new/wrapper-ref
         " "
         ,is/are
         " "
         (xdoc::seetopic "acl2::non-executable" "non-executable")
         ":")
        (xdoc::ul
         (xdoc::li
          "@('t'), to make "
          ,it/them
          " non-executable.")
         (xdoc::li
          "@('nil'), to not make "
          ,it/them
          " non-executable.")
         (xdoc::li
          "@(':auto'), to make "
          ,it/them
          " non-executable iff @('old') is non-executable."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-verify-guards
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
     This is determined by the @('wrapper?') parameter of this macro.")
   (xdoc::@def "xdoc::desc-apt-input-verify-guards"))
  (defmacro xdoc::desc-apt-input-verify-guards (wrapper? &rest additional)
    (declare (xargs :guard (member-eq wrapper? '(:never :optional :always))))
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
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-untranslate
  :short "Build a description of the @(':untranslate') input
          for the user documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-untranslate")
  (defmacro xdoc::desc-apt-input-untranslate (&rest additional)
    `(xdoc::desc
      "@(':untranslate') &mdash; default @(':nice')"
      (xdoc::p
       "Specifies if and how the body of @('new') should be turned
        from internal translated form to external untranslated form.")
      (xdoc::p
       "It must be an "
       (xdoc::seetopic "untranslate-specifier" "untranslate specifier")
       "; see that documentation topic for details.")
      ,@additional)))
