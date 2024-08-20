; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ error-value-tuples

  :parents (std/util std::std/util-extensions)

  :short "Utilities for error-value tuples."

  :long

  (xdoc::topstring

   (xdoc::p
    "These are experimental utilities for now.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::section
    "Motivation"

    (xdoc::p
     "Sometimes execution runs into exceptional conditions
      that warrant returning error indications,
      which are propagated through the callers up the stack,
      and may or may not be caught, and recovered from, at some point;
      if they are not caught, execution terminates,
      with some kind of error message.")

    (xdoc::p
     "Some languages like Java provide exception mechanisms for this.
      ACL2 does not have a full exception mechanism,
      but it has some built-in facilities,
      as well as the ability to build facilities,
      to approximate that."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::section
    "Error-Value Tuples"

    (xdoc::p
     "An <i>error-value tuple</i> is a list consisting of
      an <i>error component</i> @('erp')
      followed by
      zero or more <i>value components</i> @('val1'), ..., @('valN'),
      where @('N') &ge; 0.
      An ACL2 function can return an error-value tuple
      to indicate possible errors:
      if no error occurs,
      @('erp') is @('nil')
      and @('val1'), ..., @('valN') are the normal results of the function;
      if an error occurs,
      @('erp') contains non-@('nil') information about the error
      and @('val1'), ..., @('valN') contain irrelevant values.")

    (xdoc::p
     "There is no strict requirements on the type of @('erp'),
      but it should be, or include, an optional "
     (xdoc::seetopic "msg" "message")
     " that describes the error in human-readable terms;
      for instance, an error could be a @(tsee cons) pair
      whose @(tsee car) is a machine-oriented error code or structure,
      and whose @(tsee cdr) is a human-readable message.
      When writing code in a statically strongly typed style,
      particularly using @(tsee define) with argument and result types
      (the latter in @(':returns')),
      it may be better to leave @('erp') untyped for future extensibility,
      while @('val1'), ..., @('valN') should have types
      that make sense when no error occurs.
      If a type for @('erp') is used, e.g. @(tsee maybe-msgp),
      it should be the same for all the functions that call each other,
      so that the same type of errors can be propagated (see below).")

    (xdoc::p
     "We provide utilities, described below,
      to facilitate the use of error-value tuples.
      More utilities may be added in the future,
      particularly for richer forms of @('erp'),
      which for now is assumed to be an optional message.")

    (xdoc::p
     "This is not a new idea, but just a variation of existing ideas.
      A comparison with these related approaches is given below,
      after describing the utilities for error-value tuples."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::section
    "Utilities for Error-Value Tuples"

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Returning Errors"

     (xdoc::p
      "When there is an error,
       an ACL2 function can return
       @('(mv erp irr-val1 ... irr-valN)') if @('N') &gt; 0,
       or just @('erp') if @('N') is 0,
       where @('erp') is a non-@('nil') error indication,
       such as a message of the form @('(msg ...)'),
       and where @('irr-val1'), ..., @('irr-valN')
       are terms that evaluate to irrelevant values of appropriate types.
       In a statically strongly typed style,
       the values should have the same types
       that they have when no error occurs,
       so that the @(':returns') theorems apply uniformly
       to the error and non-error cases,
       without the need of conditions on the @('erp') results.")

     (xdoc::p
      "To return errors more clearly and concisely,
       we provide a @(tsee b*) binder @(tsee patbind-reterr)
       that defines the irrelevant values once,
       and that makes it possible for the rest of the code in the function
       to mention just @('erp') when returning an error.
       The binder is used, generally at the beginning of a function, as"
      (xdoc::codeblock
       "((reterr) irr-val1 ... irr-valN)")
      (xdoc::p
       "where the symbol @('reterr') is in the @('ACL2') package,
        but can be of course imported in the application package of interest,
        and where @('irr-val1'), ..., @('irr-valN') are
        irrelevant values of appropriate types,
        to be returned along with a non-@('nil') @('erp').
        If @('N') is 0, the binding is just @('((reterr))'),
        but must still be provided."))

     (xdoc::p
      "The binding expands to a local macro (in the @(tsee macrolet) sense),
       also named @('reterr') in the @('ACL2') package,
       that takes one argument @('erp')
       and extends it to an error-value tuple with the irrelevant values.
       This way, code in the function can return an error as"
      (xdoc::codeblock
       "(reterr erp)")
      (xdoc::p
       "where @('erp') is the desired error, e.g. @('(msg ...)').
        This not only makes the call more clear and compact,
        by hiding the irrelevant values,
        but also avoids repeating the irrelevant values
        as many times as there are points in the code that return errors.
        It makes it easier to change the code
        if the numbers or types of the values change."))

     (xdoc::p
      "The practice of causing "
      (xdoc::seetopic "hard-error" "hard errors")
      " when an unrecoverable internal condition arises
       (e.g. reaching a state that should never be reached)
       can be integrated with error-value tuples by doing something like")
     (xdoc::codeblock
      "(reterr (hard-error ...))")
     (xdoc::p
      "or perhaps using the more convenient @(tsee raise)
       when using @(tsee define).
       Technically @(tsee hard-error) returns @('nil'),
       which would mean no error in an error-value tuple,
       but such (non-)error is never returned,
       because @(tsee hard-error) stops execution.
       The advantage of using @(tsee hard-error) (or similar)
       inside @('reterr') is that logically the ACL2 function
       still returns results of the appropriate number and type,
       without the need to follow @(tsee hard-error)
       by an explicit dummy term to return irrelevant results.")

     (xdoc::p
      "The terms denoting the irrelevant values do not need to be ground,
       because this binder expands into a @(tsee macrolet),
       which can introduce variables in the expansion.
       This is useful to return stobj results, including state,
       as value components of error-value tuples."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Returning Non-Errors"

     (xdoc::p
      "When there is no error,
       an ACL2 function can return
       @('(mv nil val1 ... valN)') if @('N') &gt; 0,
       or just @('nil') if @('N') is 0,
       where @('val1'), ..., @('valN') are appropriate relevant values.")

     (xdoc::p
      "We provide a macro @('retok'),
       in the @('ACL2') package
       (from where it can be imported in an application package),
       to make this slightly more clear and compact.
       The use of this macro hides the @('nil') @('erp'),
       and just takes the values, as")
     (xdoc::codeblock
      "(retok val1 ... valN)")
     (xdoc::p
      "If @('N') is 0, it is writte as @('(retok)'),
       which in a way may be more clear than @('nil')
       in saying that things are okay, i.e. no error occurred.
       It is also symmetric with @('reterr').
       However, admittedly this does not provide huge advantages
       over just @('(mv nil val1 .. valN)') or @('nil').")

     (xdoc::p
      "Note that while @('reterr') is local to a function,
       and must be introduced via the homonymous binder,
       @('retok') is a global macro,
       which takes a variable number of arguments."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Propagating Errors"

     (xdoc::p
      "To propagate an error from a called ACL2 function,
       a caller ACL2 function can use a binder for the call,
       check the @('erp') result,
       and return an error with the same @('erp')
       and with its own irrelevant values, as")
     (xdoc::codeblock
      "((mv erp val1 ... valN) (f ...))"
      "((when erp) (reterr erp))")
     (xdoc::p
      "or, if @('N') is 0, as")
     (xdoc::codeblock
      "(erp (f ...))"
      "((when erp) (reterr erp))")

     (xdoc::p
      "We provide a @(tsee b*) binder @(tsee patbind-erp)
       that expands to the code shown just above.
       This is used as")
     (xdoc::codeblock
      "((erp val1 ... valN) (f ...))")
     (xdoc::p
      "where @('erp') is in the @('ACL2') package
       (but can imported into the package of interest).
       If @('N') is 0, the binding is @('((erp) (f ...))').
       The @('val1'), ..., @('valN') may be @(tsee b*) patterns
       that can be used as components of the @(tsee patbind-mv) binder.")

     (xdoc::p
      "This binder assumes that @('reterr') is a local macro
       introduced by a preceding @('reterr') binder (described above).")

     (xdoc::p
      "This binder has an option to change the error to be returned.
       Only the error component can be changed;
       the irrelevant values are always the same, from @('reterr').
       The option is used as")
     (xdoc::codeblock
      "((erp val1 ... valN) (f ...) :iferr erp1)")
     (xdoc::p
      "where @('erp1') is a term that evaluates to the error to be returned.
       This term may reference the variable @('erp')
       as containing the error returned by the called function,
       so that it can build
       a new error component that depends on the old one.
       When @(':iferr') is present, the binding expands to")
     (xdoc::codeblock
      "((mv erp val1 ... valN) (f ...))"
      "((when erp) (reterr erp1))")
     (xdoc::p
      "or, if @('N') is 0, to")
     (xdoc::codeblock
      "(erp (f ...))"
      "((when erp) (reterr erp1))")
     (xdoc::p
      "We expect that this option may be used less often than not.")

     (xdoc::p
      "Because on the restriction on stobj results with @('reterr'),
       this binder cannot be currently used when
       the values of error-value triples include stobjs.
       In this case, errors must be checked and propagated explicitly."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Catching Errors"

     (xdoc::p
      "To catch (i.e not propagate) an error from a called ACL2 function,
       a caller ACL2 function can use an @('mv') binder for the call,
       check the @('erp') result,
       and continue its computation if an error occurs,
       presumably to recover from the error somehow.
       If the called function does not return an error,
       presumably the caller function
       will continue computation in some other way.")

     (xdoc::p
      "At this point we do not provide any general utilities
       for the case in which the error is caught.
       The reason is that the actions to take when catching the error
       are application-specific.
       Furthermore, we expect that this kind of errors
       will be propagated more often than caught.
       Error-value tuples are intended for when execution
       runs into exceptional conditions,
       similarly to the situations in which languages with exceptions
       would throw exceptions.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::section
    "Related Ideas"

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Hard Errors"

     (xdoc::p
      "A "
      (xdoc::seetopic "er" "hard error")
      " is a bit like an exception.
       When a hard error occurs,
       it print a message to ACL2's error output,
       and it stops execution.
       A hard error is automatically propagated
       through the callers up the stack.
       However, a hard error cannot be caught: it always stops execution.")

     (xdoc::p
      "Since logically a hard error returns @('nil'),
       when a function returns a hard error,
       unless it has one result whose type includes @('nil'),
       one must add code to return an appropriate number and type of results,
       in order to maintain a statically strongly typed style.
       This is equivalent in effort to writing the @('reterr') binder,
       and the hard error call, which contains just a message,
       is equivalent in effort to writing a @('reterr') call with the message.
       Hard error propagation is fully automatic,
       but writing the @('erp') binder is equivalent in effort
       to writing an @('mv') or a single-variable binder
       for a call of a function that may return a hard error
       (such a function needs not return an error result).
       Thus, all in all, using error-value tuples,
       with the utilities provided here,
       takes about the same amount of code as using hard errors,
       with the advantage that errors can be potentially caught,
       which is useful for using tools programmatically besides interactively.
       The only extra effort required for error-value tuples is that,
       if the error is not caught,
       there must be some code, near the top level,
       to actually print the message on the screen,
       perhaps using a hard or soft error."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Soft Errors"

     (xdoc::p
      "A "
      (xdoc::seetopic "er" "soft error")
      " print a message to ACL2's error output,
       but does not stop execution.
       It causes the current function to return an "
      (xdoc::seetopic "error-triple" "error triple")
      ", which the function's caller can treat just like any other result.
       The caller can catch it and continue execution,
       or it can propagate it up to the caller.
       The propagation is not automatic,
       but it is facilitated by macros like the built-in @(tsee er-let*)
       or the @(tsee b*) binder "
      (xdoc::seetopic "patbind-er" "@('er')")
      ", which is similar to the @('erp') binder for error-value tuples.")

     (xdoc::p
      "Soft errors are used when "
      (xdoc::seetopic "programming-with-state" "programming with state")
      ". They need @(see state) to be available
       (i.e. to be passed to the function that throws the soft error).
       They also require the function that throws the soft error
       to return state, in the form of an error triple.
       Taking, and even more returning state, is sometimes inconvenient,
       namely when there is otherwise no reason to take or return it.")

     (xdoc::p
      "If a function that could naturally return multiple results
       needs to throw soft errors,
       the multiple results must be aggregated into
       the value component of the error triple,
       because @(tsee mv) cannot be nested.
       This aggregation is slightly inconvenient,
       especially when writing code in a statically strongly typed style,
       in which every argument and result has a clear type.
       A possible aggregation is a tuple (i.e. list),
       which means that the multiple results in the value
       must be accessed as elements of the list,
       which is not as direct
       (see @(tsee std::tuple) for a macro to facilitate
       the declaration of multiple value reuslts
       in @(tsee define) return specifiers).
       Another possible aggregation is a user-defined product type
       (e.g. @(tsee std::defaggregate) or @(tsee fty::defprod)),
       but that requires such a type to be explicitly defined.
       Neither approach is as convenient as just returning multiple results,
       but that is not possible if the function
       already returns an error triple due to soft errors.")

     (xdoc::p
      "For the above reason, it seems that,
       unless error triples are needed for some other reason,
       error-value tuples may be more flexible."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Context-Message Pairs"

     (xdoc::p
      "A "
      (xdoc::seetopic "context-message-pair" "context-message pair")
      " is a bit like an error triple without state.
       Another difference with soft errors is that,
       instead of printing an error message,
       it returns a "
      (xdoc::seetopic "msg" "message")
      ", which a (direct or indirect) caller can print.")

     (xdoc::p
      "A context-message pair can be caught or propagated.
       The propagation is not automatic,
       but it is facilitated by macros like the built-in @(tsee er-let*-cmp).
       Since there is no automatic printing,
       if the error is not caught,
       the message should be explicitly printed,
       which makes context-message pairs
       slightly less convenient than hard and soft errors in this respect.
       However, an advantage is that state
       does not need not be taken and returned.")

     (xdoc::p
      "Note that,
       if the first component of a context-message pair is non-@('nil'),
       the error message is the second component of the context-message pair.
       This nicely solves the issue of which value to return
       when there is an error;
       in a soft error, some value must be picked for the second component,
       even though it is often irrelevant.
       However, the fact that the second component of a context-message pair
       may be either a message or an application-specific value
       goes a bit against a statically strongly typed style of coding,
       in which ideally every result of a function has a clear type.
       If the value may be a message,
       its type is the union of the ``real'' type and the type of messages,
       which is a little more complicated than just using the ``real''type,
       and makes it necessary to create a type for the union.")

     (xdoc::p
      "Context-message pairs are thus quite similar to error-value tuples,
       and are sometimes used as context-message tuples
       (i.e. with more than one value).
       The difference is that, in error-message pairs,
       we put the message in the error,
       so that values have more uniform types.
       The error-value tuple utilities are also tailored to this."))

;;;;;;;;;;;;;;;;;;;;

    (xdoc::subsection
     "Result Types"

     (xdoc::p
      "A different approach to errors is that of "
      (xdoc::seetopic "fty::defresult" "result types")
      ", in which a function returns either a good result or an error result.
       See the discussion in the documentation of result types
       for a comparison with the approach of
       returning a possibly @('nil') error and some values,
       as done with error-value tuples, soft errors, and context-message pairs.
       In short, the advantage of result types is that
       they avoid the issue of irrelevant values when the error is non-@('nil'),
       and prevent any accidental use of such irrelevant values.
       The disadvantage is that functions that return multiple results
       must return one aggregate result
       (whose type can be defined
       via @(tsee std::defaggregate) or @(tsee fty::defprod),
       for example),
       and also that the code may be less efficient
       due to the construction and deconstruction
       of aggregations of multiple results.")

     (xdoc::p
      "Result types may be more appropriate for development
       in which ACL2 is used as a logical language,
       e.g. in a formalization,
       where clarity has paramount importance,
       and efficiency, or the need to define additional aggregate types,
       is a secondary concern.
       Error-value tuples, like soft errors and context-message pairs,
       may be more appropriate for programs,
       where ACL2 is used as a programming language,
       e.g. in a tool implementation,
       where expediency and efficiency may be more important
       than extreme conceptual clarity."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder reterr
  :parents (error-value-tuples)
  :short "Binder to introduce a local function that returns
          an error-value tuple with certain irrelevant values."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see error-value-tuples) for details."))
  :decls ((declare (xargs :guard (or (null args)
                                     (cw "~%~%**** ERROR ****~%~
                                          The RETERR binder ~
                                          takes no arguments, ~
                                          but the arguments ~x0 ~
                                          were supplied instead.~%~%"
                                         args))))
          (declare (ignore args)))
  :body `(macrolet ((reterr (erp)
                            ,(if (consp forms)
                                 `(list* 'mv erp ',forms)
                               'erp)))
                   ,rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ retok (&rest args)
  :parents (error-value-tuples)
  :short "Macro to return an error-value tuple with no error."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see error-value-tuples) for details."))
  (if (consp args)
      `(mv nil ,@args)
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder erp
  :parents (error-value-tuples)
  :short "Binder to propagate errors from error-value tuples."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see error-value-tuples) for details."))
  :decls ((declare (xargs :guard (or (and (consp forms)
                                          (null (cdr forms)))
                                     (and (consp forms)
                                          (consp (cdr forms))
                                          (eq (cadr forms) :iferr)
                                          (consp (cddr forms))
                                          (null (cdddr forms)))
                                     (cw "~%~%**** ERROR ****~%~
                                          The ERP binder ~
                                          must be followed by ~
                                          exactly one form,
                                          optionally followed by ~
                                          :IFERR and a form, ~
                                          but instead this ERP binder ~
                                          is followed by the forms ~x0.~%~%"
                                         forms)))))
  :body
  `(b* ((,(if (consp args)
              `(mv erp ,@args)
            'erp)
         ,(car forms)))
     (if erp
         ,(if (consp (cdr forms))
              `(reterr ,(caddr forms))
            '(reterr erp))
       ,rest-expr)))
