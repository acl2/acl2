; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "defaults-table")

(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-processors
  :parents (utilities)
  :short "Utilities to process inputs
          that are common to multiple APT transformations."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new-name (new-name
                                (old symbolp)
                                (names-to-avoid symbol-listp)
                                ctx
                                state)
  :returns (mv erp
               (result "A tuple @('(new-name$ updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process the @(':new-name') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility have
     a @(':new-name') input but not a @(':wrapper') and @(':wrapper-name') input
     (the ones with these additional two inputs
     should use the utility @(tsee process-input-new/wrapper-names) instead).
     This utility processes (and validates) the @(':new-name') inputs,
     as described in @(see function-name-generation)."))
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ new-name "The :NEW-NAME input" t nil))
       ((mv numbered-name-p base index) (check-numbered-name old wrld))
       ((mv base index) (if numbered-name-p
                            (mv base index)
                          (mv old 0))))
    (if (eq new-name :auto)
        (b* (((mv new-name names-to-avoid)
              (next-fresh-numbered-name base
                                        (1+ index)
                                        names-to-avoid
                                        wrld)))
          (value (list new-name names-to-avoid)))
      (b* ((msg/nil (fresh-namep-msg-weak new-name
                                          'function
                                          wrld))
           ((when msg/nil)
            (er-soft+ ctx t nil
                      "The name ~x0 specified by :NEW-NAME ~
                       is already in use.  ~@1"
                      new-name msg/nil))
           ((when (member-eq new-name names-to-avoid))
            (er-soft+ ctx t nil
                      "The name ~x0 specified by :NEW-NAME ~
                       must be distinct form the names ~&1 ~
                       that are also being generated."
                      new-name names-to-avoid)))
        (value (list new-name
                     (cons new-name names-to-avoid)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new/wrapper-names (new-name
                                         wrapper-name
                                         (wrapper-name-present booleanp)
                                         (wrapper-gen booleanp)
                                         (old symbolp)
                                         (names-to-avoid symbol-listp)
                                         ctx
                                         state)
  :returns (mv erp
               (result "A tuple
                        @('(new-name$ wrapper-name$ updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         symbolp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process the @(':new-name') and @(':wrapper-name') inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility have
     a @(':new-name'), @(':wrapper-name'), and @(':wrapper') input:
     the first specifies the name of the new function,
     the second one specifies the name of the wrapper function,
     and the third one specifies whether the wrapper function is generated;
     the second input may be present only if the third input is @('t').
     This utility processes (and validates)
     the @(':new-name') and (':wrapper-name') inputs,
     given the value of the @(':wrapper') input
     that is passed as the @('wrapper-gen') parameter.
     The processing is as described in @(see function-name-generation).")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('wrapper-name-present') to @('t')
     iff the @(':wrapper-name') input is present.
     It must also pass
     the value of the @(':wrapper') input as the @('wrapper-gen') parameter,
     and the name of the target function as the @('old') parameter."))
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ new-name "The :NEW-NAME input" t nil))
       ((er &)
        (ensure-value-is-symbol$ wrapper-name "The :WRAPPER-NAME input" t nil))
       ((mv numbered-name-p base index) (check-numbered-name old wrld))
       ((mv base index) (if numbered-name-p
                            (mv base index)
                          (mv old 0))))
    (if wrapper-gen
        (cond ((and (eq new-name :auto)
                    (eq wrapper-name :auto))
               (b* ((new-base (add-suffix base "-AUX"))
                    (wrapper-base base)
                    ((mv (list new-name$ wrapper-name$) names-to-avoid)
                     (next-fresh-numbered-names (list new-base
                                                      wrapper-base)
                                                (1+ index)
                                                names-to-avoid
                                                wrld)))
                 (value (list new-name$ wrapper-name$ names-to-avoid))))
              ((eq new-name :auto)
               (b* ((msg/nil (fresh-namep-msg-weak wrapper-name
                                                   'function
                                                   wrld))
                    ((when msg/nil)
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :WRAPPER-NAME ~
                                is already in use.  ~@1"
                               wrapper-name msg/nil))
                    ((when (member-eq wrapper-name names-to-avoid))
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :WRAPPER-NAME ~
                                must be distinct form the names ~&1 ~
                                that are also being generated."
                               wrapper-name names-to-avoid))
                    ((mv new-name$ names-to-avoid)
                     (next-fresh-numbered-name base
                                               (1+ index)
                                               (cons wrapper-name
                                                     names-to-avoid)
                                               wrld)))
                 (value (list new-name$
                              wrapper-name
                              (cons wrapper-name names-to-avoid)))))
              ((eq wrapper-name :auto)
               (b* ((msg/nil (fresh-namep-msg-weak new-name
                                                   'function
                                                   wrld))
                    ((when msg/nil)
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :NEW-NAME ~
                                is already in use.  ~@1"
                               new-name msg/nil))
                    ((when (member-eq new-name names-to-avoid))
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :NEW-NAME ~
                                must be distinct form the names ~&1 ~
                                that are also being generated."
                               new-name names-to-avoid))
                    ((mv wrapper-name$ names-to-avoid)
                     (next-fresh-numbered-name base
                                               (1+ index)
                                               (cons new-name
                                                     names-to-avoid)
                                               wrld)))
                 (value (list new-name
                              wrapper-name$
                              (cons new-name names-to-avoid)))))
              (t
               (b* ((msg/nil (fresh-namep-msg-weak wrapper-name
                                                   'function
                                                   wrld))
                    ((when msg/nil)
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :NEW-NAME ~
                                is already in use.  ~@1"
                               new-name msg/nil))
                    (msg/nil (fresh-namep-msg-weak wrapper-name
                                                   'function
                                                   wrld))
                    ((when msg/nil)
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :WRAPPER-NAME ~
                                is already in use.  ~@1"
                               wrapper-name msg/nil))
                    ((when (member-eq new-name names-to-avoid))
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :NEW-NAME ~
                                must be distinct form the names ~&1 ~
                                that are also being generated."
                               new-name names-to-avoid))
                    ((when (member-eq wrapper-name names-to-avoid))
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :WRAPPER-NAME ~
                                must be distinct form the names ~&1 ~
                                that are also being generated."
                               wrapper-name names-to-avoid))
                    ((when (eq new-name wrapper-name))
                     (er-soft+ ctx t nil
                               "The name ~x0 specified by :NEW-NAME ~
                                and the name ~x1 specified by :WRAPPER-NAME ~
                                must be distinct."
                               new-name wrapper-name)))
                 (value (list new-name
                              wrapper-name
                              (list* new-name wrapper-name names-to-avoid))))))
      (if wrapper-name-present
          (er-soft+ ctx t nil
                    "Since the :WRAPPER input is (perhaps by default) NIL, ~
                     no :WRAPPER-NAME input may be supplied.")
        (if (eq new-name :auto)
            (b* (((mv new-name$ names-to-avoid)
                  (next-fresh-numbered-name base
                                            (1+ index)
                                            names-to-avoid
                                            wrld)))
              (value (list new-name$ nil names-to-avoid)))
          (b* ((msg/nil (fresh-namep-msg-weak new-name
                                              'function
                                              wrld))
               ((when msg/nil)
                (er-soft+ ctx t nil
                          "The name ~x0 specified by :NEW-NAME ~
                           is already in use.  ~@1"
                          new-name msg/nil))
               ((when (member-eq new-name names-to-avoid))
                (er-soft+ ctx t nil
                          "The name ~x0 specified by :NEW-NAME ~
                           must be distinct form the names ~&1 ~
                           that are also being generated.")))
            (value (list new-name nil (cons new-name names-to-avoid)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-to-new-name (old-to-new-name
                                       (old-to-new-name-present booleanp)
                                       (old symbolp)
                                       (new symbolp)
                                       (names-to-avoid symbol-listp)
                                       ctx
                                       state)
  :returns (mv erp
               (result "A list @('(old-to-new updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':old-to-new-name') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have an input @(':old-to-new-name')
     that specifies the name of the generated theorem
     that rewrites the old function in terms of the new function.
     This input must be either a symbol to use directly as the theorem name
     (in which case the symbol must not be a keyword),
     or a keyword used as a separator
     between the names of the old and new functions
     as expained in @(tsee set-default-input-old-to-new-name).
     If also explained there, if this input is absent,
     it is taken from the APT defaults table.")
   (xdoc::p
    "This utility processes the @(':old-to-new-name') input
     of an APT transformation,
     validating that the input specifies a valid name
     for the new theorem.
     The @('names-to-avoid') parameter contains names of other events
     that are generated by the transformation but do not yet exist:
     they are used to ensure that the name of this theorem
     is distinct from them;
     this theorem's name is added to the list, which is also returned.")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('old-to-new-name-present') to @('t')
     iff the @(':old-to-new-name') input is present.
     If this is @('nil'), the parameter @('old-to-new-name') is ignored."))
  (b* ((wrld (w state))
       ((er &) (if old-to-new-name-present
                   (ensure-value-is-symbol$ old-to-new-name
                                            "The :OLD-TO-NEW-NAME input"
                                            t
                                            nil)
                 (value nil)))
       (name (if (or (not old-to-new-name-present)
                     (keywordp old-to-new-name))
                 (b* ((kwd (if old-to-new-name-present
                               old-to-new-name
                             (get-default-input-old-to-new-name wrld))))
                   (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name old)
                                 (symbol-name kwd)
                                 (symbol-name new))
                    new))
               old-to-new-name))
       (description (msg "The name ~x0 of the theorem ~
                          that rewrites the old function ~x1 ~
                          in terms of the new function ~x2, ~
                          specified (perhaps by default) ~
                          by the :OLD-TO-NEW-NAME input ~x3,"
                         name old new old-to-new-name))
       (error-msg? (fresh-namep-msg-weak name nil wrld))
       ((when error-msg?)
        (er-soft+ ctx t nil
                  "~@0 must be a valid fresh theorem name.  ~@1"
                  description error-msg?))
       ((er &) (ensure-value-is-not-in-list$
                name
                names-to-avoid
                (msg "among the names ~x0 of other events ~
                      generated by this transformation"
                     names-to-avoid)
                description
                t
                nil)))
    (value (list name (cons name names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new-to-old-name (new-to-old-name
                                       (new-to-old-name-present booleanp)
                                       (old symbolp)
                                       (new symbolp)
                                       (names-to-avoid symbol-listp)
                                       ctx
                                       state)
  :returns (mv erp
               (result "A list @('(new-to-old updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':new-to-old-name') input of an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-new-name),
    but for the @(':new-to-old-name') input of an APT transformation.")
  (b* ((wrld (w state))
       ((er &) (if new-to-old-name-present
                   (ensure-value-is-symbol$ new-to-old-name
                                            "The :NEW-TO-OLD-NAME input"
                                            t
                                            nil)
                 (value nil)))
       (name (if (or (not new-to-old-name-present)
                     (keywordp new-to-old-name))
                 (b* ((kwd (if new-to-old-name-present
                               new-to-old-name
                             (get-default-input-new-to-old-name wrld))))
                   (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name new)
                                 (symbol-name kwd)
                                 (symbol-name old))
                    new))
               new-to-old-name))
       (description (msg "The name ~x0 of the theorem ~
                          that rewrites the new function ~x1 ~
                          in terms of the old function ~x2, ~
                          specified (perhaps by default) ~
                          by the :NEW-TO-OLD-NAME input ~x3,"
                         name new old new-to-old-name))
       (error-msg? (fresh-namep-msg-weak name nil wrld))
       ((when error-msg?)
        (er-soft+ ctx t nil
                  "~@0 must be a valid fresh theorem name.  ~@1"
                  description error-msg?))
       ((er &) (ensure-value-is-not-in-list$
                name
                names-to-avoid
                (msg "among the names ~x0 of other events ~
                      generated by this transformation"
                     names-to-avoid)
                description
                t
                nil)))
    (value (list name (cons name names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-if-new-name (old-if-new-name
                                       (old-if-new-name-present booleanp)
                                       (old symbolp)
                                       (new symbolp)
                                       (names-to-avoid symbol-listp)
                                       ctx
                                       state)
  :returns (mv erp
               (result "A list @('(old-if-new updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':old-if-new-name') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have an input @(':old-if-new-name')
     that specifies the name of the generated theorem
     asserting that the old function is implied by the new function.
     This input must be either a symbol to use directly as the theorem name
     (in which case the symbol must not be a keyword),
     or a keyword used as a separator
     between the names of the old and new functions
     as expained in @(tsee set-default-input-old-if-new-name).
     If also explained there, if this input is absent,
     it is taken from the APT defaults table.")
   (xdoc::p
    "This utility processes the @(':old-if-new-name') input
     of an APT transformation,
     validating that the input specifies a valid name
     for the new theorem.
     The @('names-to-avoid') parameter contains names of other events
     that are generated by the transformation but do not yet exist:
     they are used to ensure that the name of this theorem
     is distinct from them;
     this theorem's name is added to the list, which is also returned.")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('old-if-new-name-present') to @('t')
     iff the @(':old-if-new-name') input is present.
     If this is @('nil'), the parameter @('old-if-new-name') is ignored."))
  (b* ((wrld (w state))
       ((er &) (if old-if-new-name-present
                   (ensure-value-is-symbol$ old-if-new-name
                                            "The :OLD-IF-NEW-NAME input"
                                            t
                                            nil)
                 (value nil)))
       (name (if (or (not old-if-new-name-present)
                     (keywordp old-if-new-name))
                 (b* ((kwd (if old-if-new-name-present
                               old-if-new-name
                             (get-default-input-old-if-new-name wrld))))
                   (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name old)
                                 (symbol-name kwd)
                                 (symbol-name new))
                    new))
               old-if-new-name))
       (description (msg "The name ~x0 of the theorem ~
                          that rewrites the old function ~x1 ~
                          in terms of the new function ~x2, ~
                          specified (perhaps by default) ~
                          by the :OLD-IF-NEW-NAME input ~x3,"
                         name old new old-if-new-name))
       (error-msg? (fresh-namep-msg-weak name nil wrld))
       ((when error-msg?)
        (er-soft+ ctx t nil
                  "~@0 must be a valid fresh theorem name.  ~@1"
                  description error-msg?))
       ((er &) (ensure-value-is-not-in-list$
                name
                names-to-avoid
                (msg "among the names ~x0 of other events ~
                      generated by this transformation"
                     names-to-avoid)
                description
                t
                nil)))
    (value (list name (cons name names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-to-wrapper-name (old-to-wrapper-name
                                           (old-to-wrapper-name-present
                                            booleanp)
                                           (gen-wrapper booleanp)
                                           (old symbolp)
                                           (wrapper symbolp)
                                           (names-to-avoid symbol-listp)
                                           ctx
                                           state)
  :returns (mv erp
               (result "A list @('(old-to-wrapper updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':old-to-wrapper-name') input of an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-new-name),
    but for the @(':old-to-wrapper-name') input of an APT transformation.
    The @('gen-wrapper') parameter is @('t') iff the wrapper is generated,
    i.e. if the @(':wrapper') input of the transformation is @('t').
    If this is @('nil'), we ensure that @(':old-to-wrapper-name') is absent.")
  (if gen-wrapper
      (b* ((wrld (w state))
           ((er &) (if old-to-wrapper-name-present
                       (ensure-value-is-symbol$ old-to-wrapper-name
                                                "The :OLD-TO-WRAPPER-NAME input"
                                                t
                                                nil)
                     (value nil)))
           (name (if (or (not old-to-wrapper-name-present)
                         (keywordp old-to-wrapper-name))
                     (b* ((kwd (if old-to-wrapper-name-present
                                   old-to-wrapper-name
                                 (get-default-input-old-to-wrapper-name wrld))))
                       (intern-in-package-of-symbol
                        (concatenate 'string
                                     (symbol-name old)
                                     (symbol-name kwd)
                                     (symbol-name wrapper))
                        wrapper))
                   old-to-wrapper-name))
           (description (msg "The name ~x0 of the theorem ~
                              that rewrites the old function ~x1 ~
                              in terms of the wrapper function ~x2, ~
                              specified (perhaps by default) ~
                              by the :OLD-TO-WRAPPER-NAME input ~x3,"
                             name old wrapper old-to-wrapper-name))
           (error-msg? (fresh-namep-msg-weak name nil wrld))
           ((when error-msg?)
            (er-soft+ ctx t nil
                      "~@0 must be a valid fresh theorem name.  ~@1"
                      description error-msg?))
           ((er &) (ensure-value-is-not-in-list$
                    name
                    names-to-avoid
                    (msg "among the names ~x0 of other events ~
                          generated by this transformation"
                         names-to-avoid)
                    description
                    t
                    nil)))
        (value (list name (cons name names-to-avoid))))
    (if old-to-wrapper-name-present
        (er-soft+ ctx t nil
                  "Since the :WRAPPER input is (perhaps by default) NIL, ~
                   no :OLD-TO-WRAPPER-NAME input may be supplied,
                   but ~x0 was supplied instead."
                  old-to-wrapper-name)
      (value (list nil names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-wrapper-to-old-name (wrapper-to-old-name
                                           (wrapper-to-old-name-present
                                            booleanp)
                                           (gen-wrapper booleanp)
                                           (old symbolp)
                                           (wrapper symbolp)
                                           (names-to-avoid symbol-listp)
                                           ctx
                                           state)
  :returns (mv erp
               (result "A list @('(wrapper-to-old updated-names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp symbol-listp result)').")
               state)
  :mode :program
  :short "Process the @(':wrapper-to-old-name') input of an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-wrapper-name),
    but for the @(':wrapper-to-old-name') input of an APT transformation.")
  (if gen-wrapper
      (b* ((wrld (w state))
           ((er &) (if wrapper-to-old-name-present
                       (ensure-value-is-symbol$ wrapper-to-old-name
                                                "The :WRAPPER-TO-OLD-NAME input"
                                                t
                                                nil)
                     (value nil)))
           (name (if (or (not wrapper-to-old-name-present)
                         (keywordp wrapper-to-old-name))
                     (b* ((kwd (if wrapper-to-old-name-present
                                   wrapper-to-old-name
                                 (get-default-input-wrapper-to-old-name wrld))))
                       (intern-in-package-of-symbol
                        (concatenate 'string
                                     (symbol-name wrapper)
                                     (symbol-name kwd)
                                     (symbol-name old))
                        wrapper))
                   wrapper-to-old-name))
           (description (msg "The name ~x0 of the theorem ~
                          that rewrites the wrapper function ~x1 ~
                          in terms of the old function ~x2, ~
                          specified (perhaps by default) ~
                          by the :WRAPPER-TO-OLD-NAME input ~x3,"
                             name wrapper old wrapper-to-old-name))
           (error-msg? (fresh-namep-msg-weak name nil wrld))
           ((when error-msg?)
            (er-soft+ ctx t nil
                      "~@0 must be a valid fresh theorem name.  ~@1"
                      description error-msg?))
           ((er &) (ensure-value-is-not-in-list$
                    name
                    names-to-avoid
                    (msg "among the names ~x0 of other events ~
                      generated by this transformation"
                         names-to-avoid)
                    description
                    t
                    nil)))
        (value (list name (cons name names-to-avoid))))
    (if wrapper-to-old-name-present
        (er-soft+ ctx t nil
                  "Since the :WRAPPER input is (perhaps by default) NIL, ~
                   no :WRAPPER-TO-OLD-NAME input may be supplied,
                   but ~x0 was supplied instead."
                  wrapper-to-old-name)
      (value (list nil names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new-enable (new-enable (old symbolp) ctx state)
  :returns (mv erp (enable booleanp) state)
  :verify-guards nil
  :short "Process the @(':new-enable') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have a @(':new-enable') input
     that specifies whether to enable or not the new function.
     This input must be a boolean or @(':auto') (the default).
     If it is @(':auto'), the new function is enabled iff the old one is.
     In any case, this utility returns a boolean
     saying whether the new function is enabled or not."))
  (cond ((eq new-enable t) (value t))
        ((eq new-enable nil) (value nil))
        ((eq new-enable :auto) (value (fundef-enabledp old state)))
        (t (er-soft+ ctx t nil
                     "The :NEW-ENABLE input must be T, NIL, or :AUTO, ~
                      but it is ~x0 instead."
                     new-enable))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-wrapper-enable (wrapper-enable
                                      (wrapper-enable-present booleanp)
                                      (gen-wrapper booleanp)
                                      ctx
                                      state)
  :returns (mv erp (processed-wrapper-enable booleanp) state)
  :short "Process the @(':wrapper-enable') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have a @(':wrapper-enable') input
     that specifies whether to enable or not the wrapper function,
     assuming it is generated.
     This input must be a boolean.
     If absent, it is taken from the APT defaults table;
     see @(tsee set-default-input-wrapper-enable).")
   (xdoc::p
    "The @('gen-wrapper') parameter is @('t') iff the wrapper is generated,
     i.e. if the @(':wrapper') input of the transformation is @('t').
     If this is @('nil'), we ensure that @(':wrapper-enable') is absent.")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('wrapper-enable-present') to @('t')
     iff the @(':wrapper-enable') input is present.
     If this is @('nil'), the parameter @('wrapper-enable') is ignored."))
  (if gen-wrapper
      (if wrapper-enable-present
          (b* (((er &)
                (ensure-value-is-boolean$ wrapper-enable
                                          "The :WRAPPER-ENABLE input"
                                          t
                                          nil)))
            (value wrapper-enable))
        (value (get-default-input-wrapper-enable (w state))))
    (if wrapper-enable-present
        (er-soft+ ctx t nil
                  "Since the :WRAPPER input is (perhaps by default) NIL, ~
                   no :WRAPPER-ENABLE input may be supplied,
                   but ~x0 was supplied instead."
                  wrapper-enable)
      (value nil)))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-to-new-enable (old-to-new-enable
                                         (old-to-new-enable-present booleanp)
                                         ctx
                                         state)
  :returns (mv erp (processed-old-to-new-enable booleanp) state)
  :short "Process the @(':old-to-new-enable') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have an @(':old-to-new-enable') input
     that specifies whether to enable or not
     the theorem that rewrites the old function in terms of the new function.
     This must be a boolean.
     If absent, it is taken from the APT defaults table;
     see @(tsee set-default-input-old-to-new-enable).")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('old-to-new-enable-present') to @('t')
     iff the @(':old-to-new-enable') input is present.
     If this is @('nil'), the parameter @('old-to-new-enable') is ignored."))
  (if old-to-new-enable-present
      (b* (((er &) (ensure-value-is-boolean$ old-to-new-enable
                                             "The :OLD-TO-NEW-ENABLE input"
                                             t
                                             nil)))
        (value old-to-new-enable))
    (value (get-default-input-old-to-new-enable (w state))))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-new-to-old-enable (new-to-old-enable
                                         (new-to-old-enable-present booleanp)
                                         ctx
                                         state)
  :returns (mv erp (processed-new-to-old-enable booleanp) state)
  :short "Process the @(':new-to-old-enable') input of an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-new-enable),
    but for the @(':new-to-old-enable') input of an APT transformation.")
  (if new-to-old-enable-present
      (b* (((er &) (ensure-value-is-boolean$ new-to-old-enable
                                             "The :NEW-TO-OLD-ENABLE input"
                                             t
                                             nil)))
        (value new-to-old-enable))
    (value (get-default-input-new-to-old-enable (w state))))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-if-new-enable (old-if-new-enable
                                         (old-if-new-enable-present booleanp)
                                         ctx
                                         state)
  :returns (mv erp (processed-old-if-new-enable booleanp) state)
  :short "Process the @(':old-if-new-enable') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have an @(':old-if-new-enable') input
     that specifies whether to enable or not
     asserting that the old function is implied by the new function.
     This must be a boolean.
     If absent, it is taken from the APT defaults table;
     see @(tsee set-default-input-old-if-new-enable).")
   (xdoc::p
    "The caller of this utility must set
     the parameter @('old-if-new-enable-present') to @('t')
     iff the @(':old-if-new-enable') input is present.
     If this is @('nil'), the parameter @('old-if-new-enable') is ignored."))
  (if old-if-new-enable-present
      (b* (((er &) (ensure-value-is-boolean$ old-if-new-enable
                                             "The :OLD-IF-NEW-ENABLE input"
                                             t
                                             nil)))
        (value old-if-new-enable))
    (value (get-default-input-old-if-new-enable (w state))))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-to-wrapper-enable (old-to-wrapper-enable
                                             (old-to-wrapper-enable-present
                                              booleanp)
                                             (gen-wrapper booleanp)
                                             ctx
                                             state)
  :returns (mv erp (processed-old-to-wrapper-enable booleanp) state)
  :short "Process the @(':old-to-wrapper-enable') input of
          an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-new-enable),
    but for the @(':old-to-wrapper-enable') input of an APT transformation.
    The @('gen-wrapper') parameter is @('t') iff the wrapper is generated,
    i.e. if the @(':wrapper') input of the transformation is @('t').
    If this is @('nil'), we ensure that @(':old-to-wrapper-enable') is absent.")
  (if gen-wrapper
      (if old-to-wrapper-enable-present
          (b* (((er &)
                (ensure-value-is-boolean$ old-to-wrapper-enable
                                          "The :OLD-TO-WRAPPER-ENABLE input"
                                          t
                                          nil)))
            (value old-to-wrapper-enable))
        (value (get-default-input-old-to-wrapper-enable (w state))))
    (if old-to-wrapper-enable-present
        (er-soft+ ctx t nil
                  "Since the :WRAPPER input is (perhaps by default) NIL, ~
                   no :OLD-TO-WRAPPER-ENABLE input may be supplied,
                   but ~x0 was supplied instead."
                  old-to-wrapper-enable)
      (value nil)))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-wrapper-to-old-enable (wrapper-to-old-enable
                                             (wrapper-to-old-enable-present
                                              booleanp)
                                             (gen-wrapper booleanp)
                                             ctx
                                             state)
  :returns (mv erp (processed-wrapper-to-old-enable booleanp) state)
  :short "Process the @(':wrapper-to-old-enable') input of
          an APT transformation."
  :long
  (xdoc::topstring-p
   "This is quite analogous to @(tsee process-input-old-to-wrapper-name),
    but for the @(':wrapper-to-old-name') input of an APT transformation.")
  (if gen-wrapper
      (if wrapper-to-old-enable-present
          (b* (((er &)
                (ensure-value-is-boolean$ wrapper-to-old-enable
                                          "The :WRAPPER-TO-OLD-ENABLE input"
                                          t
                                          nil)))
            (value wrapper-to-old-enable))
        (value (get-default-input-wrapper-to-old-enable (w state))))
    (if wrapper-to-old-enable-present
        (er-soft+ ctx t nil
                  "Since the :WRAPPER input is (perhaps by default) NIL, ~
                   no :WRAPPER-TO-OLD-ENABLE input may be supplied,
                   but ~x0 was supplied instead."
                  wrapper-to-old-enable)
      (value nil)))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-verify-guards (verify-guards (old symbolp) ctx state)
  :returns (mv erp (doit booleanp) state)
  :verify-guards nil
  :short "Process the @(':verify-guards') input of an APT transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The APT transformations that use this utility
     have a @(':verify-guards') input
     that specifies whether to verify the guards of the generated function(s).
     This input must be a boolean or @(':auto') (the default).
     If it is @(':auto'), guard verification takes place
     iff the old function is guard-verified.
     In any case, this utility returns a boolean
     saying whether the guard verification must take place or not."))
  (cond ((eq verify-guards t) (value t))
        ((eq verify-guards nil) (value nil))
        ((eq verify-guards :auto) (value (guard-verified-p old (w state))))
        (t (er-soft+ ctx t nil
                     "The :VERIFY-GUARDS input must be T, NIL, or :AUTO, ~
                      but it is ~x0 instead."
                     verify-guards))))
