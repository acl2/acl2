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
     which precede their arguments with specific level-3 headings.
     Others provide more automation."))
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
    `(xdoc::evmac-section-intro
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
   (xdoc::def "xdoc::evmac-section-appconds"))
  (defmacro xdoc::evmac-section-appconds (&rest content)
    `(xdoc::app
      (xdoc::h3 "Applicability Conditions")
      ,@content)))

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
