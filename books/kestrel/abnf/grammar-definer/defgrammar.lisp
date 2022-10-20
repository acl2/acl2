; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-parser/executable")
(include-book "../notation/syntax-abstraction")
(include-book "../operations/well-formedness")
(include-book "../operations/closure")

(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/untranslate-preprocessing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defgrammar

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input "name")

  (xdoc::evmac-topic-implementation-item-input "file")

  (xdoc::evmac-topic-implementation-item-input "untranslate")

  (xdoc::evmac-topic-implementation-item-input "well-formedness")

  (xdoc::evmac-topic-implementation-item-input "closure")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing defgrammar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-process-name (name (ctx ctxp) state)
  :returns (mv erp nothing state)
  :mode :program
  :short "Process the @('*name*') input."
  (b* (((unless (legal-constantp name))
        (acl2::er-soft+ ctx t nil
                        "The first input must be a legal constant name, ~
                         but ~x0 is not a legal constant name."
                        name))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 specified as first input" name)
                'const
                nil
                t
                nil)))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defgrammar-allowed-options*
  :short "Keyword options accepted by @(tsee defgrammar)."
  (list :file
        :untranslate
        :well-formedness
        :closure
        :parents
        :short
        :long)
  ///
  (assert-event (acl2::keyword-listp *defgrammar-allowed-options*))
  (assert-event (no-duplicatesp-eq *defgrammar-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-process-inputs ((args true-listp) (ctx ctxp) state)
  :returns (mv erp
               (val "A @('(tuple (name acl2::symbolp)
                                 (file acl2::stringp)
                                 (untranslate booleanp)
                                 (well-formedness booleanp)
                                 (closure booleanp)
                                 parents
                                 short
                                 long
                                 (other-events true-listp)
                                 val)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((mv args other-events) (std::split-/// ctx args))
       ((mv erp name options)
        (partition-rest-and-keyword-args args *defgrammar-allowed-options*))
       ((when (or erp
                  (not (consp name))
                  (not (endp (cdr name)))))
        (acl2::er-soft+ ctx t nil
                        "The inputs must be the constant name ~
                         followed by the options ~&0 ~
                         and possibly /// followed by other events."
                        *defgrammar-allowed-options*))
       (name (car name))
       ((er &) (defgrammar-process-name name ctx state))
       (file-option (assoc-eq :file options))
       ((unless (consp file-option))
        (acl2::er-soft+ ctx t nil
                        "The :FILE input must be supplied."))
       (file (cdr file-option))
       ((er &) (acl2::ensure-value-is-string$ file
                                              "The :FILE input"
                                              t nil))
       (untranslate-option (assoc-eq :untranslate options))
       (untranslate (if (consp untranslate-option)
                        (cdr untranslate-option)
                      t))
       ((er &) (acl2::ensure-value-is-boolean$ untranslate
                                               "The :UNTRANSLATE input"
                                               t nil))
       (well-formedness-option (assoc-eq :well-formedness options))
       (well-formedness (if (consp well-formedness-option)
                            (cdr well-formedness-option)
                          t))
       ((er &) (acl2::ensure-value-is-boolean$ well-formedness
                                               "The :WELL-FORMEDNESS input"
                                               t nil))
       (closure-option (assoc-eq :closure options))
       (closure (if (consp closure-option)
                    (cdr closure-option)
                  nil))
       ((er &) (acl2::ensure-value-is-boolean$ closure
                                               "The :CLOSURE input"
                                               t nil))
       (parents-option (assoc-eq :parents options))
       (parents (if (consp parents-option)
                    (cdr parents-option)
                  :absent))
       (short-option (assoc-eq :short options))
       (short (if (consp short-option)
                  (cdr short-option)
                :absent))
       (long-option (assoc-eq :long options))
       (long (if (consp long-option)
                 (cdr long-option)
               :absent)))
    (value (list name
                 file
                 untranslate
                 well-formedness
                 closure
                 parents
                 short
                 long
                 other-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defgrammar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-gen-everything ((name acl2::symbolp)
                                   (file acl2::stringp)
                                   (untranslate booleanp)
                                   (well-formedness booleanp)
                                   (closure booleanp)
                                   parents
                                   short
                                   long
                                   (other-events true-listp)
                                   state)
  :returns (mv erp
               (event pseudo-event-formp :hyp (true-listp other-events))
               state)
  :short "Generate all the events."
  (b* (((mv cstree state) (parse-grammar-from-file file state))
       ((unless (treep cstree))
        (value (prog2$ (raise "Internal error: no concrete syntax tree.")
                       '(_))))
       (astree (abstract-rulelist cstree))
       (defconst-event
         `(defconst ,name ',astree))
       (untranslate-event?
        (and untranslate
             (list `(add-const-to-untranslate-preprocess ,name))))
       (well-formedness-event?
        (and well-formedness
             (list `(defthm ,(acl2::packn-pos (list 'rulelist-wfp-of- name)
                                              name)
                      (rulelist-wfp ,name)
                      :hints (("Goal" :in-theory '((:e rulelist-wfp))))))))
       (closure-event?
        (and closure
             (list `(defthm ,(acl2::packn-pos (list 'rulelist-closedp-of- name)
                                              name)
                      (rulelist-closedp ,name)
                      :hints (("Goal" :in-theory '((:e rulelist-closedp))))))))
       (event
        `(defsection ,name
           ,@(and (not (eq parents :absent))
                  (list :parents parents))
           ,@(and (not (eq short :absent))
                  (list :short short))
           ,@(and (not (eq long :absent))
                  (list :long long))
           ,defconst-event
           ,@untranslate-event?
           ,@well-formedness-event?
           ,@closure-event?
           ,@other-events)))
    (value event))
  :guard-debug t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (defgrammar-implementation)
  :short "Process the inputs and generate the events."
  (b* (((er (list name
                  file
                  untranslate
                  well-formedness
                  closure
                  parents
                  short
                  long
                  other-events))
        (defgrammar-process-inputs args ctx state)))
    (defgrammar-gen-everything
      name
      file
      untranslate
      well-formedness
      closure
      parents
      short
      long
      other-events
      state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defgrammar-macro-definition
  :parents (defgrammar-implementation)
  :short "Definition of the @(tsee defgrammar) macro."
  (defmacro defgrammar (&rest args)
    `(make-event (defgrammar-fn ',args 'defgrammar state))))
