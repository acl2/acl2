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
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/untranslate-preprocessing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination std::split-///)

(defrulel true-listp-of-split-///
  (b* (((mv pre-/// post-///) (std::split-/// ctx x)))
    (implies (true-listp x)
             (and (true-listp pre-///)
                  (true-listp post-///)))))

(in-theory (disable std::split-///))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel partition-rest-and-keyword-args1-results
  (implies (true-listp x)
           (b* (((mv rest keypart) (acl2::partition-rest-and-keyword-args1 x)))
             (and (true-listp rest)
                  (true-listp keypart)))))

(defrulel partition-rest-and-keyword-arg2-results
  (implies (symbol-alistp alist)
           (b* ((alist1
                 (acl2::partition-rest-and-keyword-args2 keypart keys alist)))
             (implies (not (equal alist1 t))
                      (symbol-alistp alist1)))))

(defrulel partition-rest-and-keyword-args-results
  (implies (true-listp x)
           (b* (((mv erp rest keypart)
                 (partition-rest-and-keyword-args x keys)))
             (implies (not erp)
                      (and (true-listp rest)
                           (symbol-alistp keypart))))))

(local (in-theory (disable partition-rest-and-keyword-args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel alistp-when-symbol-alistp
  (implies (symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel consp-of-cdr-iff-cdr-when-true-listp
  (implies (true-listp x)
           (iff (consp (cdr x))
                (cdr x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-anyp (x)
  :returns (yes/no booleanp)
  (declare (ignore x))
  t
  ///
  (defrule defgrammar-anyp-holds
    (defgrammar-anyp x)))

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
  :short "Process the @('*name*') input."
  (b* (((unless (legal-constantp name))
        (er-soft+ ctx t nil
                  "The first input must be a legal constant name, ~
                   but ~x0 is not a legal constant name."
                  name))
       ((er &) (ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 specified as first input" name)
                'acl2::const
                nil
                t
                nil)))
    (value nil))
  ///

  (defret defgrammar-process-name-symbol-when-not-error
    (implies (not erp)
             (acl2::symbolp name)))

  (in-theory (disable defgrammar-process-name-symbol-when-not-error)))

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
  (assert-event (keyword-listp *defgrammar-allowed-options*))
  (assert-event (no-duplicatesp-eq *defgrammar-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defgrammar-process-inputs ((args true-listp) (ctx ctxp) state)
  :returns (mv erp
               (val (std::tuple (name acl2::symbolp)
                                (file acl2::stringp)
                                (untranslate booleanp)
                                (well-formedness booleanp)
                                (closure booleanp)
                                (parents defgrammar-anyp)
                                (short defgrammar-anyp)
                                (long defgrammar-anyp)
                                (other-events true-listp)
                                val)
                    :hyp (true-listp args))
               state)
  :short "Process all the inputs."
  (b* (((fun (irr)) (list nil "" nil nil nil nil nil nil nil))
       ((mv args other-events) (std::split-/// ctx args))
       ((mv erp name options)
        (partition-rest-and-keyword-args args *defgrammar-allowed-options*))
       ((when (or erp
                  (not (consp name))
                  (not (endp (cdr name)))))
        (er-soft+ ctx t (irr)
                  "The inputs must be the constant name ~
                   followed by the options ~&0 ~
                   and possibly /// followed by other events."
                  *defgrammar-allowed-options*))
       (name (car name))
       ((er & :iferr (irr)) (defgrammar-process-name name ctx state))
       (file-option (assoc-eq :file options))
       ((unless (consp file-option))
        (er-soft+ ctx t (irr) "The :FILE input must be supplied."))
       (file (cdr file-option))
       ((er &) (ensure-value-is-string$ file
                                        "The :FILE input"
                                        t
                                        (irr)))
       (untranslate-option (assoc-eq :untranslate options))
       (untranslate (if (consp untranslate-option)
                        (cdr untranslate-option)
                      nil))
       ((er &) (ensure-value-is-boolean$ untranslate
                                         "The :UNTRANSLATE input"
                                         t
                                         (irr)))
       (well-formedness-option (assoc-eq :well-formedness options))
       (well-formedness (if (consp well-formedness-option)
                            (cdr well-formedness-option)
                          nil))
       ((er &) (ensure-value-is-boolean$ well-formedness
                                         "The :WELL-FORMEDNESS input"
                                         t
                                         (irr)))
       (closure-option (assoc-eq :closure options))
       (closure (if (consp closure-option)
                    (cdr closure-option)
                  nil))
       ((er &) (ensure-value-is-boolean$ closure
                                         "The :CLOSURE input"
                                         t
                                         (irr)))
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
                 other-events)))
  :prepwork
  ((local (in-theory (enable defgrammar-process-name-symbol-when-not-error
                             acl2::ensure-value-is-string
                             acl2::ensure-value-is-boolean))))

  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

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
             (list `(defthm ,(packn-pos (list 'rulelist-wfp-of- name) name)
                      (rulelist-wfp ,name)
                      :hints (("Goal" :in-theory '((:e rulelist-wfp))))))))
       (closure-event?
        (and closure
             (list `(defthm ,(packn-pos (list 'rulelist-closedp-of- name) name)
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
  :returns (mv erp
               (event pseudo-event-formp :hyp (true-listp args))
               state)
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
                  other-events)
            :iferr '(_))
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
