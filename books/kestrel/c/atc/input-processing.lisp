; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "pretty-printing-options")
(include-book "defstruct")
(include-book "defobject")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/std/strings/letter-digit-uscore-dash-chars" :dir :system)
(include-book "kestrel/std/system/irecursivep-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)
(include-book "kestrel/std/util/error-value-tuples" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "oslib/dirname" :dir :system :ttags ((:quicklisp) :oslib))
(include-book "oslib/file-types" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) :oslib))
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/alists/top" :dir :system))

(local (in-theory (disable state-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel alistp-when-symbol-alistp
  (implies (symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing atc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-remove-called-fns ((fns symbol-listp) (term pseudo-termp))
  :returns (new-fns symbol-listp :hyp (symbol-listp fns))
  :short "Remove from a list of function symbols
          all the functions called by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atc-process-function);
     see that function's documentation for details."))
  (cond ((endp fns) nil)
        (t (if (ffnnamep (car fns) term)
               (atc-remove-called-fns (cdr fns) term)
             (cons (car fns)
                   (atc-remove-called-fns (cdr fns) term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function ((fn symbolp)
                              (previous-fns symbol-listp)
                              (uncalled-fns symbol-listp)
                              (wrld plist-worldp))
  :guard (function-symbolp fn wrld)
  :returns (mv erp
               (new-previous-fns symbol-listp
                                 :hyp (and (symbolp fn)
                                           (symbol-listp previous-fns)))
               (new-uncalled-fns symbol-listp
                                 :hyp (and (symbolp fn)
                                           (symbol-listp uncalled-fns))))
  :short "Process a target function @('fn') among @('t1'), ..., @('tp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we perform some of the checks prescribed in @(tsee atc),
     namely the ones that are easy to perform
     without analyzing the body of the function in detail.
     The remaining checks are performed during code generation,
     where it is more natural to perform them,
     as the functions' bodies are analyzed and translated to C.")
   (xdoc::p
    "The @('previous-fns') parameter lists the symbols of
     all the target functions
     that precede @('fn') in @('(t1 ... tp)').
     This list is used to ensure that
     there are no duplicate target functions.")
   (xdoc::p
    "The @('uncalled-fns') parameter lists the symbols of
     all the recursive target functions
     that precede @('fn') in @('(t1 ... tp)')
     and that are not called by any of the functions
     that precede @('fn') in @('(t1 ... tp)').
     This list is used to ensure that all the recursive target functions,
     which represent C loops,
     are called by some other target functions (that follow them).
     The reason for checking this is that C loops may only occur in C functions;
     if this check were not satisfied,
     there would be some C loop, represented by a recursive target function,
     that does not appear in the generated C code.
     As we process @('fn'),
     we remove from @('uncalled-fns') all the functions called by @('fn').
     If @('fn') is recursive, we add it to @('uncalled-fns').
     We return the updated list of uncalled functions.")
   (xdoc::p
    "When this input processing function is called,
     @('fn') is already known to be a function name.
     See @(tsee atc-process-target)."))
  (b* (((reterr) nil nil)
       (previous-fns (cons fn previous-fns))
       (desc (msg "The target function ~x0" fn))
       ((unless (logicp fn wrld))
        (reterr (msg "~@0 must be in logic mode." desc)))
       ((unless (acl2::guard-verified-p fn wrld))
        (reterr (msg "~@0 must be guard-verified." desc)))
       ((unless (acl2::definedp fn wrld))
        (reterr (msg "~@0 must be defined." desc)))
       ((when (ffnnamep fn (uguard+ fn wrld)))
        (reterr (msg "The target function ~x0 is used in its own guard. ~
                      This is currently not supported in ATC."
                     fn)))
       (rec (irecursivep+ fn wrld))
       ((when (and rec (> (len rec) 1)))
        (reterr (msg "The recursive target function ~x0 ~
                      must be singly recursive, ~
                      but it is mutually recursive with ~x1 instead."
                     fn (remove-eq fn rec))))
       ((when (and rec
                   (not (equal (well-founded-relation+ fn wrld)
                               'o<))))
        (reterr (msg "The well-founded relation ~
                      of the recursive target function ~x0 ~
                      must be O<, but it ~x1 instead. ~
                      Only recursive functions with well-founded relation O< ~
                      are currently supported by ATC."
                     fn (well-founded-relation+ fn wrld))))
       (uncalled-fns (atc-remove-called-fns uncalled-fns (ubody+ fn wrld)))
       (uncalled-fns (if rec
                         (cons fn uncalled-fns)
                       uncalled-fns)))
    (retok previous-fns
           uncalled-fns))
  ///
  (more-returns
   (new-previous-fns true-listp
                     :hyp (true-listp previous-fns)
                     :rule-classes :type-prescription)
   (new-uncalled-fns true-listp
                     :hyp (true-listp new-uncalled-fns)
                     :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-target (target
                            (previous-structs symbol-listp)
                            (previous-objs symbol-listp)
                            (previous-fns symbol-listp)
                            (uncalled-fns symbol-listp)
                            (ctx ctxp)
                            state)
  :returns (mv erp
               (val (tuple (new-previous-structs symbol-listp)
                           (new-previous-objs symbol-listp)
                           (new-previous-fns symbol-listp)
                           (new-uncalled-fns symbol-listp)
                           val)
                    :hyp (and (symbol-listp previous-structs)
                              (symbol-listp previous-objs)
                              (symbol-listp previous-fns)
                              (symbol-listp uncalled-fns)))
               state)
  :short "Process a target among @('t1'), ..., @('tp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters @('previous-fns') and @('uncalled-fns')
     are explained in @(tsee atc-process-function).
     The parameters @('previous-structs') and @('previous-objs')
     are analogous to @('previous-fns'),
     but for the @(tsee defstruct) and @(tsee defobject) targets
     instead of the function targets:
     it lists all the @(tsee defstruct) and @('defobject') targets
     that precede @('target')
     in the list of targets @('(t1 ... tp)').
     This is used to detect duplicate symbol names.")
   (xdoc::p
    "If the target is a function name,
     its processing is delegated to @(tsee atc-process-function),
     except for ensuring that its symbol name is distinct from
     the symbol names of the preceding targets.
     Otherwise, the target must be
     a @(tsee defstruct) or @(tsee defobject) name,
     and it is processed here:
     we check that it is in the @(tsee defstruct) or @(tsee defobject) table;
     furthermore, if it is a @(tsee defobject) target,
     we ensure that it differs from the preceding function targets."))
  (b* ((irrelevant (list nil nil nil nil))
       ((unless (symbolp target))
        (er-soft+ ctx t irrelevant
                  "The target ~x0 is not a symbol."
                  target))
       (functionp (function-symbolp target (w state)))
       (struct-info (defstruct-table-lookup (symbol-name target) (w state)))
       (obj-info (defobject-table-lookup (symbol-name target) (w state)))
       ((when (and functionp struct-info obj-info))
        (er-soft+ ctx t irrelevant
                  "The target ~x0 ambiguously denotes ~
                   a function, a DEFSTRUCT, and a DEFOBJECT."
                  target))
       ((when (and functionp struct-info))
        (er-soft+ ctx t irrelevant
                  "The target ~x0 ambiguously denotes ~
                   a function and a DEFSTRUCT."
                  target))
       ((when (and functionp obj-info))
        (er-soft+ ctx t irrelevant
                  "The target ~x0 ambiguously denotes ~
                   a function and a DEFOBJECT"
                  target))
       ((when (and struct-info obj-info))
        (er-soft+ ctx t irrelevant
                  "The target ~x0 ambiguously denotes ~
                   a DEFSTRUCT and a DEFOBJECT."
                  target))
       ((when functionp)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target function ~x0 has the same name as ~
                         the target function ~x1 that precedes it."
                        target (car previous-fns)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target function ~x0 has the same name as ~
                         the target DEFSTRUCT ~x1 that precedes it."
                        target (car previous-structs)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target function ~x0 has the same name as ~
                         the target DEFOBJECT ~x1 that precedes it."
                        target (car previous-objs)))
             ((mv erp previous-fns uncalled-fns)
              (atc-process-function target
                                    previous-fns
                                    uncalled-fns
                                    (w state)))
             ((when erp) (er-soft+ ctx t irrelevant "~@0" erp)))
          (acl2::value (list previous-structs
                             previous-objs
                             previous-fns
                             uncalled-fns))))
       ((when struct-info)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFSTRUCT ~x0 has the same name as ~
                         the target function ~x1 that precedes it."
                        target (car previous-fns)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFSTRUCT ~x0 has the same name as ~
                         the target DEFSTRUCT ~x1 that precedes it."
                        target (car previous-structs)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFSTRUCT ~x0 has the same name as ~
                         the target DEFOBJECT ~x1 that precedes it."
                        target (car previous-objs)))
             (previous-structs (cons target previous-structs)))
          (acl2::value (list previous-structs
                             previous-objs
                             previous-fns
                             uncalled-fns))))
       ((when obj-info)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFOBJECT ~x0 has the same name as ~
                         the target function ~x1 that precedes it."
                        target (car previous-fns)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFOBJECT ~x0 has the same name as ~
                         the target DEFSTRUCT ~x1 that precedes it."
                        target (car previous-structs)))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (er-soft+ ctx t irrelevant
                        "The target DEFOBJECT ~x0 has the same name as ~
                         the target DEFOBJECT ~x1 that precedes it."
                        target (car previous-objs)))
             (previous-objs (cons target previous-objs)))
          (acl2::value (list previous-structs
                             previous-objs
                             previous-fns
                             uncalled-fns)))))
    (er-soft+ ctx t irrelevant
              "The target ~x0 is a symbol that does not identify ~
               any function or DEFSTRUCT or DEFOBJECT."
              target))
  ///

  (more-returns
   (val true-listp
        :rule-classes :type-prescription))

  (defret len-of-atc-process-target.val
    (equal (len val) 4))

  (defret true-listp-of-atc-process-target.new-previous-structs
    (b* (((list new-previous-structs & & &) val))
      (true-listp new-previous-structs))
    :hyp (true-listp previous-structs)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target.new-previous-objs
    (b* (((list & new-previous-objs & &) val))
      (true-listp new-previous-objs))
    :hyp (true-listp previous-objs)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target.new-previous-fns
    (b* (((list & & new-previous-fns &) val))
      (true-listp new-previous-fns))
    :hyp (true-listp previous-fns)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target.new-uncalled-fns
    (b* (((list & & & new-uncalled-fns) val))
      (true-listp new-uncalled-fns))
    :hyp (true-listp uncalled-fns)
    :rule-classes :type-prescription)

  (defret symbolp-when-atc-process-target
    (Implies (not erp)
             (symbolp target)))

  (in-theory (disable symbolp-when-atc-process-target)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-target-list ((targets true-listp)
                                 (previous-structs symbol-listp)
                                 (previous-objs symbol-listp)
                                 (previous-fns symbol-listp)
                                 (uncalled-fns symbol-listp)
                                 (ctx ctxp)
                                 state)
  :returns (mv erp
               (val (tuple (new-previous-structs symbol-listp)
                           (new-previous-objs symbol-listp)
                           (new-previous-fns symbol-listp)
                           (new-uncalled-fns symbol-listp)
                           val)
                    :hyp (and (symbol-listp previous-structs)
                              (symbol-listp previous-objs)
                              (symbol-listp previous-fns)
                              (symbol-listp uncalled-fns)))
               state)
  :short "Lift @(tsee atc-process-function) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "We thread the lists through."))
  (b* (((when (endp targets)) (acl2::value (list previous-structs
                                                 previous-objs
                                                 previous-fns
                                                 uncalled-fns)))
       ((er (list previous-structs previous-objs previous-fns uncalled-fns))
        (atc-process-target (car targets)
                            previous-structs
                            previous-objs
                            previous-fns
                            uncalled-fns
                            ctx
                            state)))
    (atc-process-target-list (cdr targets)
                             previous-structs
                             previous-objs
                             previous-fns
                             uncalled-fns
                             ctx
                             state))
  ///

  (more-returns
   (val true-listp
        :rule-classes :type-prescription
        :name true-listp-of-atc-process-target-list.val))

  (defret true-listp-of-atc-process-target-list.new-previous-structs
    (b* (((list new-previous-structs & & &) val))
      (true-listp new-previous-structs))
    :hyp (true-listp previous-structs)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target-list.new-previous-objs
    (b* (((list & new-previous-objs & & &) val))
      (true-listp new-previous-objs))
    :hyp (true-listp previous-objs)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target-list.new-previous-fns
    (b* (((list & & new-previous-fns &) val))
      (true-listp new-previous-fns))
    :hyp (true-listp previous-fns)
    :rule-classes :type-prescription)

  (defret true-listp-of-atc-process-target-list.new-uncalled-fns
    (b* (((list & & & new-uncalled-fns) val))
      (true-listp new-uncalled-fns))
    :hyp (true-listp uncalled-fns)
    :rule-classes :type-prescription)

  (defret symbol-listp-when-atc-process-target-list
    (implies (and (not erp)
                  (true-listp targets))
             (symbol-listp targets))
    :hints (("Goal" :in-theory (enable symbolp-when-atc-process-target))))

  (in-theory (disable symbol-listp-when-atc-process-target-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-targets ((targets true-listp) (ctx ctxp) state)
  :returns (mv erp
               (target-fns symbol-listp)
               state)
  :short "Process the targets @('t1'), ..., @('tp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We initialize the lists of
     previous @(tsee defstruct) targets,
     previous @(tsee defobject) targets,
     previous function targets,
     and uncalled recursive functions to be empty,
     and we ensure that the latter list is empty
     after processing all the targets.")
   (xdoc::p
    "We return all the target functions."))
  (b* (((unless (consp targets))
        (er-soft+ ctx t nil
                  "At least one target must be supplied."))
       ((er (list & & previous-fns uncalled-fns) :iferr nil)
        (atc-process-target-list targets nil nil nil nil ctx state))
       ((unless (endp uncalled-fns))
        (er-soft+ ctx t nil
                  "The recursive target functions ~&0 ~
                   are not called by any other target function."
                  uncalled-fns)))
    (acl2::value previous-fns))
  ///

  (defret symbol-listp-when-atc-process-targets
    (implies (and (not erp)
                  (true-listp targets))
             (symbol-listp targets))
    :hints
    (("Goal" :in-theory (enable symbol-listp-when-atc-process-target-list))))

  (in-theory (disable symbol-listp-when-atc-process-targets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-output-dir (output-dir (ctx ctxp) state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':output-dir') input."
  (b* (((er &) (ensure-value-is-string$ output-dir
                                        "The :OUTPUT-DIR input"
                                        t
                                        nil))
       ((mv msg? kind state) (oslib::file-kind output-dir))
       ((when msg?) (er-soft+ ctx t nil
                              "The kind of ~
                               the output directory path ~x0 ~
                               cannot be tested.  ~
                               ~@1"
                              output-dir msg?))
       ((unless (eq kind :directory))
        (er-soft+ ctx t nil
                  "The output directory path ~x0 ~
                   is not a directory; it has kind ~x1 instead."
                  output-dir kind)))
    (acl2::value nil))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-value-is-string)))
  ///

  (defret stringp-when-atc-process-output-dir
    (implies (not erp)
             (stringp output-dir))
    :hints (("Goal" :in-theory (enable acl2::ensure-value-is-string))))

  (in-theory (disable stringp-when-atc-process-output-dir)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-file-name (file-name
                               (file-name? booleanp)
                               (output-dir stringp)
                               (ctx ctxp)
                               state)
  :returns (mv erp
               (file-path stringp)
               state)
  :short "Process the @(':file-name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the full path of the file,
     consisting of the output directory and the extension.")
   (xdoc::p
    "We form the full path, and we make sure that
     either does not exist in the file system
     or is a path to a file and not a directory."))
  (b* (((unless file-name?)
        (er-soft+ ctx t ""
                  "The :FILE-NAME input must be present, ~
                   but it is absent instead."))
       ((er &) (ensure-value-is-string$ file-name
                                        "The :FILE-NAME input"
                                        t
                                        ""))
       ((when (equal file-name ""))
        (er-soft+ ctx t ""
                  "The :FILE-NAME input must not be empty."))
       ((unless (str::letter/digit/uscore/dash-charlist-p
                 (str::explode file-name)))
        (er-soft+ ctx t ""
                  "The :FILE-NAME input must consists of only ~
                   ASCII letters, digits, underscores, and dashes, ~
                   but ~s0 violates this condition."
                  file-name))
       (file-path (oslib::catpath output-dir (str::cat file-name ".c")))
       ((mv msg? existsp state) (oslib::path-exists-p file-path))
       ((when msg?) (er-soft+ ctx t ""
                              "The existence of the file path ~x0 ~
                               cannot be tested.  ~
                               ~@1"
                              file-path msg?))
       ((when (not existsp)) (acl2::value file-path))
       ((mv msg? kind state) (oslib::file-kind file-path))
       ((when msg?) (er-soft+ ctx t ""
                              "The kind of the file path ~x0 ~
                               cannot be tested.  ~
                               ~@1"
                              file-path msg?))
       ((unless (eq kind :regular-file))
        (er-soft+ ctx t ""
                  "The file path ~x0 ~
                   is not a regular file; it has kind ~x1 instead."
                  file-name kind)))
    (acl2::value file-path))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-value-is-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-pretty-printing-options*
  :short "Keyword (sub)options accepted by @(tsee atc)
          for the @(':pretty-printing') option."
  (list :parenthesize-nested-conditionals)
  ///
  (assert-event (keyword-listp *atc-allowed-pretty-printing-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-pretty-printing-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-pretty-printing (pretty-printing
                                     (ctx ctxp)
                                     state)
  :returns (mv erp (options pprint-options-p) state)
  :short "Process the @(':pretty-printing') input."
  (b* ((irrelevant (make-pprint-options))
       ((er &) (ensure-keyword-value-list$ pretty-printing
                                           "The :PRETTY-PRINTING input"
                                           t
                                           irrelevant))
       (alist (keyword-value-list-to-alist pretty-printing))
       (keywords (strip-cars alist))
       (desc (msg "The list of keywords in the :PRETTY-PRINTING input ~x0"
                  keywords))
       ((er &) (ensure-list-has-no-duplicates$ keywords
                                               desc
                                               t
                                               irrelevant))
       ((er &) (ensure-list-subset$ keywords
                                    *atc-allowed-pretty-printing-options*
                                    desc
                                    t
                                    irrelevant))
       (parenthesize-nested-conditionals
        (cdr (assoc-eq :parenthesize-nested-conditionals alist)))
       ((er &) (ensure-value-is-boolean$
                parenthesize-nested-conditionals
                (msg "The value ~x0 of the pretty-printing option ~
                      :PARENTHESIZE-NESTED-CONDITIONALS"
                     parenthesize-nested-conditionals)
                t
                irrelevant)))
    (acl2::value
     (make-pprint-options
      :parenthesize-nested-conditionals parenthesize-nested-conditionals)))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-keyword-value-list
                                           acl2::ensure-value-is-boolean)))
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-const-name (const-name
                                (const-name? booleanp)
                                (target-fns symbol-listp)
                                (proofs booleanp)
                                (ctx ctxp)
                                state)
  :returns (mv erp
               (val (tuple (prog-const symbolp)
                           (wf-thm symbolp)
                           (fn-thms symbol-symbol-alistp)
                           val)
                    :hyp (symbol-listp target-fns)
                    :hints
                    (("Goal" :in-theory (enable acl2::ensure-value-is-symbol))))
               state)
  :short "Process the @(':const-name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this input also determines, indirectly,
     the names of the theorems generated and exported by ATC,
     here we also
     calculate the names of those theorems,
     ensure they are fresh,
     and return them for use in event generation.
     More precisely, we return the name of the program well-formedness theorem
     and the names of the function correctness theorems;
     the latter are returned as an alist from the target functions
     to the respective theorem names.")
   (xdoc::p
    "The name of each theorem is obtained by
     appending something to the name of the constant.
     The thing appended differs across the theorems:
     thus, their names are all distinct by construction.")
   (xdoc::p
    "If the @(':proofs') input is @('nil'),
     the @(':const-name') input must be absent
     and we return @('nil') for this as well as for the theorem names.
     No constant and theorems are generated when @(':proofs') is @('nil')."))
  (b* (((acl2::fun (irr)) (list nil nil nil))
       ((when (not proofs))
        (if const-name?
            (er-soft+ ctx t (irr)
                      "Since the :PROOFS input is NIL, ~
                       the :CONST-NAME input must be absent, ~
                       but it is ~x0 instead."
                      const-name)
          (acl2::value (list nil nil nil))))
       ((er &) (ensure-value-is-symbol$ const-name
                                        "The :CONST-NAME input"
                                        t
                                        (irr)))
       (prog-const (if (eq const-name :auto)
                       'c::*program*
                     const-name))
       ((er &) (ensure-symbol-is-fresh-event-name$
                prog-const
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input"
                     prog-const)
                'acl2::const
                nil
                t
                (irr)))
       (wf-thm (add-suffix prog-const "-WELL-FORMED"))
       ((er &) (ensure-symbol-is-fresh-event-name$
                wf-thm
                (msg "The generated theorem name ~x0 ~
                      indirectly specified by the :CONST-NAME input"
                     wf-thm)
                nil
                nil
                t
                (irr)))
       ((er fn-thms :iferr (irr))
        (atc-process-const-name-aux target-fns prog-const ctx state)))
    (acl2::value (list prog-const
                       wf-thm
                       fn-thms)))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-value-is-symbol)))

  :prepwork

  ((local (in-theory (disable packn)))

   (define atc-process-const-name-aux ((target-fns symbol-listp)
                                       (prog-const symbolp)
                                       (ctx ctxp)
                                       state)
     :returns (mv erp
                  (val symbol-symbol-alistp :hyp (symbol-listp target-fns))
                  state)
     (b* (((when (endp target-fns)) (acl2::value nil))
          (fn (car target-fns))
          (fn-thm (packn (list prog-const "-" (symbol-name fn) "-CORRECT")))
          ((er &) (ensure-symbol-is-fresh-event-name$
                   fn-thm
                   (msg "The generated theorem name ~x0 ~
                         indirectly specified by the :CONST-NAME input"
                        fn-thm)
                   nil
                   nil
                   t
                   nil))
          ((er fn-thms) (atc-process-const-name-aux
                         (cdr target-fns) prog-const ctx state)))
       (acl2::value (acons fn fn-thm fn-thms)))
     :verify-guards :after-returns))

  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-options*
  :short "Keyword options accepted by @(tsee atc)."
  (list :output-dir
        :file-name
        :pretty-printing
        :proofs
        :const-name
        :print)
  ///
  (assert-event (keyword-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) (ctx ctxp) state)
  :returns
  (mv erp
      (val (tuple (targets symbol-listp)
                  (file-path stringp)
                  (pretty-printing pprint-options-p)
                  (proofs booleanp)
                  (prog-const symbolp)
                  (wf-thm symbolp)
                  (fn-thms symbol-symbol-alistp)
                  (print evmac-input-print-p)
                  val)
           :hyp (true-listp args)
           :hints
           (("Goal"
             :in-theory (enable stringp-when-atc-process-output-dir
                                evmac-process-input-print
                                acl2::ensure-value-is-boolean)
             :use
             ((:instance symbol-listp-when-atc-process-targets
                         (targets
                          (mv-nth 1 (partition-rest-and-keyword-args
                                     args *atc-allowed-options*)))
                         (ctx ctx)
                         (state state))))))
      state)
  :short "Process all the inputs."
  (b* (((acl2::fun (irr))
        (list nil
              ""
              (with-guard-checking :none
                                   (ec-call (pprint-options-fix :irrelevant)))
              nil
              nil
              nil
              nil
              nil))
       ((mv erp targets options)
        (partition-rest-and-keyword-args args *atc-allowed-options*))
       ((when erp) (er-soft+ ctx t (irr)
                             "The inputs must be the targets ~
                              followed by the options ~&0."
                             *atc-allowed-options*))
       ((er target-fns :iferr (irr)) (atc-process-targets targets ctx state))
       (output-dir-option (assoc-eq :output-dir options))
       (output-dir (if output-dir-option
                       (cdr output-dir-option)
                     "."))
       ((er & :iferr (irr)) (atc-process-output-dir output-dir ctx state))
       (file-name-option (assoc-eq :file-name options))
       ((mv file-name file-name?)
        (if file-name-option
            (mv (cdr file-name-option) t)
          (mv :irrelevant nil)))
       ((er file-path :iferr (irr))
        (atc-process-file-name file-name file-name? output-dir ctx state))
       (pretty-printing-option (assoc-eq :pretty-printing options))
       (pretty-printing (if pretty-printing-option
                            (cdr pretty-printing-option)
                          nil))
       ((er pretty-printing :iferr (irr))
        (atc-process-pretty-printing pretty-printing ctx state))
       (proofs-option (assoc-eq :proofs options))
       (proofs (if proofs-option
                   (cdr proofs-option)
                 t))
       ((er & :iferr (irr)) (ensure-value-is-boolean$ proofs
                                                      "The :PROOFS input"
                                                      t
                                                      nil))
       (const-name-option (assoc-eq :const-name options))
       ((mv const-name const-name?)
        (if const-name-option
            (mv (cdr const-name-option) t)
          (mv :auto nil)))
       ((er (list prog-const wf-thm fn-thms) :iferr (irr))
        (atc-process-const-name const-name
                                const-name?
                                target-fns
                                proofs
                                ctx
                                state))
       (print-option (assoc-eq :print options))
       (print (if print-option
                  (cdr print-option)
                :result))
       ((er & :iferr (irr)) (evmac-process-input-print print ctx state)))
    (acl2::value (list targets
                       file-path
                       pretty-printing
                       proofs
                       prog-const
                       wf-thm
                       fn-thms
                       print)))
  :guard-hints
  (("Goal" :in-theory (e/d (acl2::ensure-value-is-boolean
                            stringp-when-atc-process-output-dir)
                           (not))))) ; reduce case splits
