
; APT Utilities -- XDOC Constructors
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

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
          for the reference documentation of an APT transformation."
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
          for the reference documentation of an APT transformation."
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
          for the reference documentation of an APT transformation."
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

(defsection xdoc::desc-apt-input-wrapper-name
  :short "Build a description of the @(':wrapper-name') input
          for the reference documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-wrapper-name")
  (defmacro xdoc::desc-apt-input-wrapper-name (&rest additional)
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
      (xdoc::p
       "In the rest of this documentation page,
        let @('wrapper') be this function.")
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-wrapper-enable
  :short "Build a description of the @(':wrapper-enable') input
          for the reference documentation of an APT transformation."
  :long (xdoc::topstring-@def "xdoc::desc-apt-input-wrapper-enable")
  (defmacro xdoc::desc-apt-input-wrapper-enable (&rest additional)
    `(xdoc::desc
      "@(':wrapper-enable') &mdash; default @('t')"
      (xdoc::p
       "Determines whether @('wrapper') is enabled:")
      (xdoc::ul
       (xdoc::li
        "@('t'), to enable it.")
       (xdoc::li
        "@('nil'), to disable it."))
      ,@additional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-thm-name
  :short "Build a description of the @(':thm-name') input
          for the reference documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem relates the old function to the new function
     when there is no wrapper function,
     while it related the old function to the wrapper function
     where there is a wrapper function.
     This choice is determined by the @('wrapperp') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-thm-name"))
  (defmacro xdoc::desc-apt-input-thm-name (wrapperp &rest additional)
    (declare (xargs :guard (booleanp wrapperp)))
    (b* ((fn (if wrapperp "wrapper" "new")))
      `(xdoc::desc
        "@(':thm-name') &mdash; default @(':auto')"
        (xdoc::p
         (concatenate 'string
                      "Determines the name of the theorem
                       that relates @('old') to @('"
                      ,fn
                      "'):"))
        (xdoc::ul
         (xdoc::li
          (concatenate 'string
                       "@(':auto'), to use the
                        <see topic='@(url acl2::paired-names)'>paired
                        name</see> obtained by
                        <see topic='@(url acl2::make-paired-name)'>pairing</see>
                        the name of @('old') and the name of @('"
                       ,fn
                       "'), putting the result into the same package as @('"
                       ,fn
                       "')."))
         (xdoc::li
          "Any other symbol
           (that is not in the main Lisp package and that is not a keyword),
           to use as the name of the theorem."))
        (xdoc::p
         (concatenate 'string
                      "In the rest of this documentation page, let @('old-to-"
                      ,fn
                      "') be this theorem."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-thm-enable
  :short "Build a description of the @(':thm-enable') input
          for the reference documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This refers to the theorem that relates the old function
     to either the new function or the wrapper function,
     depending on whether the latter is present or not.
     This is indicated by the @('wrapperp') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-thm-enable"))
  (defmacro xdoc::desc-apt-input-thm-enable (wrapperp &rest additional)
    (declare (xargs :guard (booleanp wrapperp)))
    (b* ((fn (if wrapperp "wrapper" "new")))
      `(xdoc::desc
        "@(':thm-enable') &mdash; default @('t')"
        (xdoc::p
         (concatenate 'string
                      "Determines whether @('old-to-"
                      ,fn
                      "') is enabled:"))
        (xdoc::ul
         (xdoc::li
          "@('t'), to enable it.")
         (xdoc::li
          "@('nil'), to disable it."))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-non-executable
  :short "Build a description of the @(':non-executable') input
          for the reference documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This involves the new function,
     and also the wrapper function when present.
     This is indicated by the @('wrapperp') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-non-executable"))
  (defmacro xdoc::desc-apt-input-non-executable (wrapperp &rest additional)
    (declare (xargs :guard (booleanp wrapperp)))
    (b* ((new/newwrapper (if wrapperp
                             "@('new') and @('wrapper') are"
                           "@('new') is"))
         (it/them (if wrapperp "them" "it")))
      `(xdoc::desc
        "@(':non-executable') &mdash; default @(':auto')"
        (xdoc::p
         (concatenate 'string
                      "Determines whether "
                      ,new/newwrapper
                      " <see topic='@(url acl2::non-executable)'
                       >non-executable</see>:"))
        (xdoc::ul
         (xdoc::li
          (concatenate 'string
                       "@('t'), to make "
                       ,it/them
                       " non-executable."))
         (xdoc::li
          (concatenate 'string
                       "@('nil'), to not make "
                       ,it/them
                       " non-executable."))
         (xdoc::li
          (concatenate 'string
                       "@(':auto'), to make "
                       ,it/them
                       " non-executable
                        iff @('old') is non-executable.")))
        ,@additional))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc-apt-input-verify-guards
  :short "Build a description of the @(':verify-guards') input
          for the reference documentation of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This involves the new function,
     and also the wrapper function when present.
     This is indicated by the @('wrapperp') parameter.")
   (xdoc::@def "xdoc::desc-apt-input-verify-guards"))
  (defmacro xdoc::desc-apt-input-verify-guards (wrapperp &rest additional)
    (declare (xargs :guard (booleanp wrapperp)))
    (b* ((new/newwrapper (if wrapperp
                             "@('new') and @('wrapper') are"
                           "@('new') is"))
         (it/them (if wrapperp "them" "it")))
      `(xdoc::desc
        "@(':verify-guards') &mdash; default @(':auto')"
        (xdoc::p
         (concatenate 'string
                      "Determines whether "
                      ,new/newwrapper
                      " guard-verified:"))
        (xdoc::ul
         (xdoc::li
          (concatenate 'string
                       "@('t'), to guard-verify "
                       ,it/them
                       "."))
         (xdoc::li
          (concatenate 'string
                       "@('nil'), to not guard-verify "
                       ,it/them
                       "."))
         (xdoc::li
          (concatenate 'string
                       "@(':auto'), to guard-verify "
                       ,it/them
                       " iff @('old') is guard-verified.")))
        ,@additional))))
