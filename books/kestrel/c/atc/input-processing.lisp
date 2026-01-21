; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

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
(include-book "std/system/irecursivep-plus" :dir :system)
(include-book "std/system/ubody-plus" :dir :system)
(include-book "std/system/uguard-plus" :dir :system)
(include-book "std/system/get-well-founded-relation-plus" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "oslib/dirname" :dir :system :ttags ((:quicklisp) :oslib))
(include-book "oslib/file-types" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) :oslib))
(include-book "std/strings/letter-digit-uscore-dash-chars" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "std/util/tuple" :dir :system)

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel alistp-when-symbol-alistp
  (implies (symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel symbol-listp-of-strip-cars-when-symbol-alistp
  (implies (symbol-alistp x)
           (symbol-listp (strip-cars x)))
  :induct t
  :enable symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel true-listp-when-keyword-listp
  (implies (keyword-listp x)
           (true-listp x))
  :induct t
  :enable keyword-listp)

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
                   (not (equal (get-well-founded-relation+ fn wrld)
                               'o<))))
        (reterr (msg "The well-founded relation ~
                      of the recursive target function ~x0 ~
                      must be O<, but it ~x1 instead. ~
                      Only recursive functions with well-founded relation O< ~
                      are currently supported by ATC."
                     fn (get-well-founded-relation+ fn wrld))))
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
                            (wrld plist-worldp))
  :returns (mv erp
               (target$ symbolp)
               (new-previous-structs symbol-listp
                                     :hyp (symbol-listp previous-structs))
               (new-previous-objs symbol-listp
                                  :hyp (symbol-listp previous-objs))
               (new-previous-fns symbol-listp
                                 :hyp (symbol-listp previous-fns))
               (new-uncalled-fns symbol-listp
                                 :hyp (symbol-listp uncalled-fns)))
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
     we ensure that it differs from the preceding function targets.")
   (xdoc::p
    "If all the checks are successful, we also return the target itself,
     with a guaranteed @(tsee symbolp) type,
     so that calling code has that fact readily available."))
  (b* (((reterr) nil nil nil nil nil)
       ((unless (symbolp target))
        (reterr (msg "The target ~x0 is not a symbol." target)))
       (functionp (function-symbolp target wrld))
       (struct-info (defstruct-table-lookup (symbol-name target) wrld))
       (obj-info (defobject-table-lookup (symbol-name target) wrld))
       ((when (and functionp struct-info obj-info))
        (reterr (msg "The target ~x0 ambiguously denotes ~
                      a function, a DEFSTRUCT, and a DEFOBJECT."
                     target)))
       ((when (and functionp struct-info))
        (reterr (msg "The target ~x0 ambiguously denotes ~
                      a function and a DEFSTRUCT."
                     target)))
       ((when (and functionp obj-info))
        (reterr (msg "The target ~x0 ambiguously denotes ~
                      a function and a DEFOBJECT"
                     target)))
       ((when (and struct-info obj-info))
        (reterr (msg "The target ~x0 ambiguously denotes ~
                      a DEFSTRUCT and a DEFOBJECT."
                     target)))
       ((when functionp)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (reterr (msg "The target function ~x0 has the same name as ~
                            the target function ~x1 that precedes it."
                           target (car previous-fns))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (reterr (msg "The target function ~x0 has the same name as ~
                            the target DEFSTRUCT ~x1 that precedes it."
                           target (car previous-structs))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (reterr (msg "The target function ~x0 has the same name as ~
                            the target DEFOBJECT ~x1 that precedes it."
                           target (car previous-objs))))
             ((erp previous-fns uncalled-fns)
              (atc-process-function target
                                    previous-fns
                                    uncalled-fns
                                    wrld)))
          (retok target
                 previous-structs
                 previous-objs
                 previous-fns
                 uncalled-fns)))
       ((when struct-info)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (reterr (msg "The target DEFSTRUCT ~x0 has the same name as ~
                            the target function ~x1 that precedes it."
                           target (car previous-fns))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (reterr (msg "The target DEFSTRUCT ~x0 has the same name as ~
                            the target DEFSTRUCT ~x1 that precedes it."
                           target (car previous-structs))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (reterr (msg "The target DEFSTRUCT ~x0 has the same name as ~
                            the target DEFOBJECT ~x1 that precedes it."
                           target (car previous-objs))))
             (previous-structs (cons target previous-structs)))
          (retok target
                 previous-structs
                 previous-objs
                 previous-fns
                 uncalled-fns)))
       ((when obj-info)
        (b* ((found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-fns)))
             ((when found)
              (reterr (msg "The target DEFOBJECT ~x0 has the same name as ~
                            the target function ~x1 that precedes it."
                           target (car previous-fns))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-structs)))
             ((when found)
              (reterr (msg "The target DEFOBJECT ~x0 has the same name as ~
                            the target DEFSTRUCT ~x1 that precedes it."
                           target (car previous-structs))))
             (found (member-equal (symbol-name target)
                                  (symbol-name-lst previous-objs)))
             ((when found)
              (reterr (msg "The target DEFOBJECT ~x0 has the same name as ~
                            the target DEFOBJECT ~x1 that precedes it."
                           target (car previous-objs))))
             (previous-objs (cons target previous-objs)))
          (retok target
                 previous-structs
                 previous-objs
                 previous-fns
                 uncalled-fns))))
    (reterr (msg "The target ~x0 is a symbol that does not identify ~
                  any function or DEFSTRUCT or DEFOBJECT."
                 target)))
  ///

  (more-returns
   (new-previous-structs true-listp
                         :hyp (true-listp previous-structs)
                         :rule-classes :type-prescription)
   (new-previous-objs true-listp
                      :hyp (true-listp previous-objs)
                      :rule-classes :type-prescription)
   (new-previous-fns true-listp
                     :hyp (true-listp previous-fns)
                     :rule-classes :type-prescription)
   (new-uncalled-fns true-listp
                     :hyp (true-listp uncalled-fns)
                     :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-target-list ((targets true-listp)
                                 (previous-structs symbol-listp)
                                 (previous-objs symbol-listp)
                                 (previous-fns symbol-listp)
                                 (uncalled-fns symbol-listp)
                                 (wrld plist-worldp))
  :returns (mv erp
               (targets symbol-listp)
               (new-previous-structs symbol-listp
                                     :hyp (symbol-listp previous-structs))
               (new-previous-objs symbol-listp
                                  :hyp (symbol-listp previous-objs))
               (new-previous-fns symbol-listp
                                 :hyp (symbol-listp previous-fns))
               (new-uncalled-fns symbol-listp
                                 :hyp (symbol-listp uncalled-fns)))
  :short "Lift @(tsee atc-process-function) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "We thread the lists through.")
   (xdoc::p
    "If successful, we also return the target list itself,
     with a guaranteed @(tsee symbol-listp) type,
     so that calling code has that fact readily available."))
  (b* (((reterr) nil nil nil nil nil)
       ((when (endp targets)) (retok nil
                                     previous-structs
                                     previous-objs
                                     previous-fns
                                     uncalled-fns))
       ((erp
         target
         previous-structs
         previous-objs
         previous-fns
         uncalled-fns)
        (atc-process-target (car targets)
                            previous-structs
                            previous-objs
                            previous-fns
                            uncalled-fns
                            wrld))
       ((erp
         targets
         previous-structs
         previous-objs
         previous-fns
         uncalled-fns)
        (atc-process-target-list (cdr targets)
                                 previous-structs
                                 previous-objs
                                 previous-fns
                                 uncalled-fns
                                 wrld)))
    (retok (cons target targets)
           previous-structs
           previous-objs
           previous-fns
           uncalled-fns))
  ///

  (more-returns
   (new-previous-structs true-listp
                         :hyp (true-listp previous-structs)
                         :rule-classes :type-prescription)
   (new-previous-objs true-listp
                      :hyp (true-listp previous-objs)
                      :rule-classes :type-prescription)
   (new-previous-fns true-listp
                     :hyp (true-listp previous-fns)
                     :rule-classes :type-prescription)
   (new-uncalled-fns true-listp
                     :hyp (true-listp uncalled-fns)
                     :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-targets ((targets true-listp) (wrld plist-worldp))
  :returns (mv erp
               (targets symbol-listp)
               (target-fns symbol-listp))
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
    "We return all the target functions.
     We also return all the targets,
     with a guaranteed @(tsee symbol-listp) type for use by the caller."))
  (b* (((reterr) nil nil)
       ((unless (consp targets))
        (reterr "At least one target must be supplied."))
       ((erp targets-as-symbols & & previous-fns uncalled-fns)
        (atc-process-target-list targets nil nil nil nil wrld))
       ((unless (endp uncalled-fns))
        (reterr (msg "The recursive target functions ~&0 ~
                      are not called by any other target function."
                     uncalled-fns))))
    (retok targets-as-symbols previous-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-output-dir ((options symbol-alistp) state)
  :returns (mv erp (output-dir stringp) state)
  :short "Process the @(':output-dir') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the input itself,
     with a guaranteed @(tsee stringp) type."))
  (b* (((reterr) "" state)
       (output-dir-option (assoc-eq :output-dir options))
       (output-dir (if output-dir-option
                       (cdr output-dir-option)
                     "."))
       ((unless (stringp output-dir))
        (reterr (msg "The :OUTPUT-DIR input must be a string, ~
                      but ~x0 is not a string."
                     output-dir)))
       ((mv msg? kind state) (oslib::file-kind output-dir))
       ((when msg?) (reterr (msg "The kind of ~
                                  the output directory path ~x0 ~
                                  cannot be tested.  ~
                                  ~@1"
                                 output-dir msg?)))
       ((unless (eq kind :directory))
        (reterr (msg "The output directory path ~x0 ~
                      is not a directory; it has kind ~x1 instead."
                     output-dir kind))))
    (retok output-dir state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-file-name ((options symbol-alistp)
                               (output-dir stringp)
                               state)
  :returns (mv erp
               (file-name stringp)
               (path-wo-ext stringp)
               state)
  :short "Process the @(':file-name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return, besides the file name itself as a string,
     the full path of the file(s),
     without the @('.c') or @('.h') extension,
     consisting of the output directory and
     the file name without extension.")
   (xdoc::p
    "We make sure that, after adding each of the @('.h') and @('.c') extensions,
     either the file does not exist in the file system
     or is a file and not a directory (i.e. has the right kind).")
   (xdoc::p
    "Due to the use of the file utilities, we also need to return state."))
  (b* (((reterr) "" "" state)
       (file-name-option (assoc-eq :file-name options))
       ((unless (consp file-name-option))
        (reterr (msg "The :FILE-NAME input must be present, ~
                      but it is absent instead.")))
       (file-name (cdr file-name-option))
       ((unless (stringp file-name))
        (reterr (msg "The :FILE-NAME input must be a string, ~
                      but ~x0 is not a string."
                     file-name)))
       ((when (equal file-name ""))
        (reterr (msg "The :FILE-NAME input must not be the empty string.")))
       ((unless (str::letter/digit/uscore/dash-charlist-p
                 (str::explode file-name)))
        (reterr (msg "The :FILE-NAME input must consists of only ~
                      ASCII letters, digits, underscores, and dashes, ~
                      but ~s0 violates this condition."
                     file-name)))
       (path-wo-ext (oslib::catpath output-dir file-name))
       (path.c (str::cat path-wo-ext ".c"))
       ((mv msg? existsp state) (oslib::path-exists-p path.c))
       ((when msg?) (reterr (msg "The existence of the file path ~x0 ~
                                  cannot be tested.  ~
                                  ~@1"
                                 path.c msg?)))
       ((when (not existsp)) (retok file-name path-wo-ext state))
       ((mv msg? kind state) (oslib::file-kind path.c))
       ((when msg?) (reterr (msg "The kind of the file path ~x0 ~
                                  cannot be tested.  ~
                                  ~@1"
                                 path.c msg?)))
       ((unless (eq kind :regular-file))
        (reterr (msg "The file path ~x0 ~
                      is not a regular file; it has kind ~x1 instead."
                     path.c kind))))
    (retok file-name path-wo-ext state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-header ((options symbol-alistp))
  :returns (mv erp (header booleanp))
  :short "Process the @(':header') input."
  (b* (((reterr) nil)
       (header-option (assoc-eq :header options))
       (header (if header-option
                   (cdr header-option)
                 nil))
       ((unless (booleanp header))
        (reterr (msg "The :HEADER input must be a boolean, ~
                      but ~x0 is not a boolean."
                     header))))
    (retok header)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-pretty-printing-options*
  :short "Keyword (sub)options accepted by @(tsee atc)
          for the @(':pretty-printing') option."
  (list :parenthesize-nested-conditionals)
  ///
  (assert-event (keyword-listp *atc-allowed-pretty-printing-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-pretty-printing-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-pretty-printing ((options symbol-alistp))
  :returns (mv erp (ppoptions pprint-options-p))
  :short "Process the @(':pretty-printing') input."
  (b* (((reterr) (irr-pprint-options))
       (pretty-printing-option (assoc-eq :pretty-printing options))
       (pretty-printing (if pretty-printing-option
                            (cdr pretty-printing-option)
                          nil))
       ((unless (keyword-value-listp pretty-printing))
        (reterr (msg "The :PRETTY-PRINTING input must be a keyword-value list, ~
                      but ~x0 is not a keyword-value list."
                     pretty-printing)))
       (alist (keyword-value-list-to-alist pretty-printing))
       (keywords (strip-cars alist))
       (desc (msg "The list of keywords in the :PRETTY-PRINTING input ~x0"
                  keywords))
       ((unless (no-duplicatesp-eq keywords))
        (reterr (msg "~@0 must have no duplicates." desc)))
       ((unless (subsetp-eq keywords *atc-allowed-pretty-printing-options*))
        (reterr (msg "~@0 must be a subset of ~x1."
                     desc *atc-allowed-pretty-printing-options*)))
       (parenthesize-nested-conditionals
        (cdr (assoc-eq :parenthesize-nested-conditionals alist)))
       ((unless (booleanp parenthesize-nested-conditionals))
        (reterr (msg "The value ~x0 of the pretty-printing option ~
                      :PARENTHESIZE-NESTED-CONDITIONALS must be a boolean."
                     parenthesize-nested-conditionals))))
    (retok
     (make-pprint-options
      :parenthesize-nested-conditionals parenthesize-nested-conditionals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-proofs ((options symbol-alistp))
  :returns (mv erp (proofs booleanp))
  :short "Process the @(':proofs') input."
  (b* (((reterr) nil)
       (proofs-option (assoc-eq :proofs options))
       (proofs (if proofs-option
                   (cdr proofs-option)
                 t))
       ((unless (booleanp proofs))
        (reterr (msg "The :PROOFS input must be a boolean, ~
                      but ~x0 is not a boolean."
                     proofs))))
    (retok proofs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-const-name ((options symbol-alistp)
                                (target-fns symbol-listp)
                                (wrld plist-worldp))
  :returns (mv erp
               (prog-const symbolp)
               (wf-thm symbolp)
               (fn-thms symbol-symbol-alistp
                        :hyp (symbol-listp target-fns))
               (fn-limits symbol-symbol-alistp
                          :hyp (symbol-listp target-fns))
               (fn-body-limits symbol-symbol-alistp
                               :hyp (symbol-listp target-fns)))
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
    "Besides the names of the generated theorems,
     we also return the names of the soon-to-be-generated limit functions.
     There will be one limit function for each target function,
     whose name is obtained by adding @('-limit')
     after the constant name and the target function name:
     this will express a limit sufficient to execute the target function.
     There will be also an additional limit function
     for each recursive target function,
     whose name is obtained by adding @('-body-limit')
     after the constant name and the target function name;
     this will express a limit sufficient to run
     any instance of the loop body."))
  (b* (((reterr) nil nil nil nil nil)
       (const-name-option (assoc-eq :const-name options))
       (const-name (if (consp const-name-option)
                       (cdr const-name-option)
                     :auto))
       ((unless (symbolp const-name))
        (reterr (msg "The :CONST-NAME input must be a symbol, ~
                      but ~x0 is not a symbol."
                     const-name)))
       (prog-const (if (eq const-name :auto)
                       'c::*program*
                     const-name))
       (msg? (acl2::fresh-namep-msg-weak prog-const 'acl2::const wrld))
       ((when msg?)
        (reterr (msg "The constant name ~x0 ~
                      determined by the :CONST-NAME input ~x0 ~
                      is invalid: ~@2"
                     prog-const const-name msg?)))
       (wf-thm (add-suffix prog-const "-WELL-FORMED"))
       (msg? (acl2::fresh-namep-msg-weak wf-thm nil wrld))
       ((when msg?)
        (reterr (msg "The generated theorem name ~x0 ~
                      for the well-formedness theorem is invalid: ~@1"
                     wf-thm msg?)))
       ((erp fn-thms fn-limits fn-body-limits)
        (atc-process-const-name-aux target-fns prog-const wrld)))
    (retok prog-const wf-thm fn-thms fn-limits fn-body-limits))

  :prepwork
  ((define atc-process-const-name-aux ((target-fns symbol-listp)
                                       (prog-const symbolp)
                                       (wrld plist-worldp))
     :returns (mv erp
                  (fn-thms symbol-symbol-alistp
                           :hyp (symbol-listp target-fns))
                  (fn-limits symbol-symbol-alistp
                             :hyp (symbol-listp target-fns))
                  (fn-body-limits symbol-symbol-alistp
                                  :hyp (symbol-listp target-fns)))
     (b* (((reterr) nil nil nil)
          ((when (endp target-fns)) (retok nil nil nil))
          (fn (car target-fns))
          (fn-thm (packn (list prog-const "-" (symbol-name fn) "-CORRECT")))
          (msg? (acl2::fresh-namep-msg-weak fn-thm nil wrld))
          ((when msg?)
           (reterr (msg "The generated theorem name ~x0 ~
                         for the correctness theorem of the function ~x1 ~
                         is invalid: ~@2"
                        fn-thm fn msg?)))
          ((erp fn-thms fn-limits fn-body-limits)
           (atc-process-const-name-aux (cdr target-fns) prog-const wrld))
          (fn-limit (packn (list prog-const "-" (symbol-name fn) "-LIMIT")))
          (msg? (acl2::fresh-namep-msg-weak fn-limit 'function wrld))
          ((when msg?)
           (reterr (msg "The generated function name ~x0 ~
                         for the limit of the function ~x1 ~
                         is invalid: ~@2"
                        fn-limit fn msg?)))
          ((when (not (irecursivep+ fn wrld)))
           (retok (acons fn fn-thm fn-thms)
                  (acons fn fn-limit fn-limits)
                  fn-body-limits))
          (fn-body-limit
           (packn (list prog-const "-" (symbol-name fn) "-BODY-LIMIT")))
          (msg? (acl2::fresh-namep-msg-weak fn-body-limit 'function wrld))
          ((when msg?)
           (reterr (msg "The generated function name ~x0 ~
                         for the body limit of the function ~x1 ~
                         is invalid: ~@2"
                        fn-body-limit fn msg?))))
       (retok (acons fn fn-thm fn-thms)
              (acons fn fn-limit fn-limits)
              (acons fn fn-body-limit fn-body-limits)))
     :prepwork ((local (in-theory (enable acons))))
     :verify-guards nil ; done below
     ///
     (verify-guards atc-process-const-name-aux
       :hints
       (("Goal"
         :in-theory
         (enable acl2::alistp-when-symbol-symbol-alistp-rewrite)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-print ((options symbol-alistp))
  :returns (mv erp (print evmac-input-print-p))
  :short "Process the @(':print') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the @(tsee evmac-input-print-p) type,
     but we exclude the @('nil') case; see the ATC user doc.
     We should probably define a new type for
     the printing levels supported by ATC,
     or perhaps change @(tsee evmac-input-print-p) to be that,
     as it may be more appropriate."))
  (b* (((reterr) nil)
       (print-option (assoc-eq :print options))
       (print (if print-option
                  (cdr print-option)
                :result))
       ((unless (and (evmac-input-print-p print)
                     print))
        (reterr (msg "The :PRINT input must be ~
                      :ERROR, :RESULT, :INFO, or :ALL; ~
                      but it is ~x0 instead."
                     print))))
    (retok print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-options*
  :short "Keyword options accepted by @(tsee atc)."
  (list :output-dir
        :file-name
        :header
        :pretty-printing
        :proofs
        :const-name
        :print)
  ///
  (assert-event (keyword-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) state)
  :returns (mv erp
               (targets symbol-listp)
               (file-name stringp)
               (path-wo-ext stringp)
               (header booleanp)
               (pretty-printing pprint-options-p)
               (proofs booleanp)
               (prog-const symbolp)
               (wf-thm symbolp)
               (fn-thms symbol-symbol-alistp)
               (fn-limits symbol-symbol-alistp)
               (fn-body-limits symbol-symbol-alistp)
               (print evmac-input-print-p)
               state)
  :short "Process all the inputs."
  (b* (((reterr)
        nil "" "" nil (irr-pprint-options)
        nil nil nil nil nil nil nil state)
       (wrld (w state))
       ((mv erp targets options)
        (partition-rest-and-keyword-args args *atc-allowed-options*))
       ((when erp) (reterr (msg "The inputs must be the targets ~
                                 followed by the options ~&0."
                                *atc-allowed-options*)))
       ((erp targets target-fns) (atc-process-targets targets wrld))
       ((erp output-dir state) (atc-process-output-dir options state))
       ((erp file-name path-wo-ext state)
        (atc-process-file-name options output-dir state))
       ((erp header) (atc-process-header options))
       ((erp pretty-printing) (atc-process-pretty-printing options))
       ((erp proofs) (atc-process-proofs options))
       ((erp prog-const wf-thm fn-thms fn-limits fn-body-limits)
        (atc-process-const-name options target-fns wrld))
       ((erp print) (atc-process-print options)))
    (retok targets
           file-name
           path-wo-ext
           header
           pretty-printing
           proofs
           prog-const
           wf-thm
           fn-thms
           fn-limits
           fn-body-limits
           print
           state)))
