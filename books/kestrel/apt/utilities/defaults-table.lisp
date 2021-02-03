; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defaults-table
  :parents (utilities)
  :short "APT defaults table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to the "
    (xdoc::seetopic "acl2::acl2-defaults-table" "ACL2 defaults table")
    ", but it is specific to APT.
     It contains information about various defaults that affect
     certain aspects of the behavior of APT transformations.")
   (xdoc::p
    "Support for more defaults will be added as needed.")
   (xdoc::p
    "We provide event macros to change the defaults.
     These should be used instead of modifying the table directly.")
   (xdoc::p
    "Internally, each default is represented by a pair in the table.
     The key is always a keyword, while the value depends on the default."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defaults-table-name*
  :short "Name of the table of APT defaults."
  'defaults-table
  ///
  (assert-event (symbolp *defaults-table-name*))
  (assert-event (equal (symbol-package-name *defaults-table-name*) "APT")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(table ,*defaults-table-name* nil nil
    :guard (keywordp acl2::key)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-old-to-new-name (kwd)
  (declare (xargs :guard (keywordp kwd)))
  :short "Set the default @(':old-to-new-name') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-to-new-name') input
     that specifies the name of the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the new function.
     When this input is a symbol that is a valid theorem name,
     it is used as the theorem name.
     When this input is a keyword (which is never a valid theorem name),
     the theorem name is the concatenation of
     the old function name, the keyword, and the new function name,
     e.g. @('f-to-g') if
     @('f') is the old function name,
     @('g') is the new function name,
     and @(':-to-') is the keyword passed as the @(':old-to-new-name') input.
     Thus, the keyword specifies a separator
     between old and new function names.
     The concatenated symbol is in the same package as the new function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-to-new-name') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-')."))
  `(table ,*defaults-table-name* :old-to-new-name ,kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-to-new-name ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':old-to-new-name') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-to-new-name).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-to-new-name table))
       ((unless (consp pair))
        (prog2$ (raise "No :OLD-TO-NEW-NAME found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :OLD-TO-NEW-NAME is ~x0, which is not a keyword."
                 kwd)
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-new-name :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-new-to-old-name (kwd)
  (declare (xargs :guard (keywordp kwd)))
  :short "Set the default @(':new-to-old-name') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include a @(':new-to-old-name') input
     that specifies the name of the generated theorem
     that rewrites (a term involving) a call of the new function
     to (a term involving) a call of the old function.
     When this input is a symbol that is a valid theorem name,
     it is used as the theorem name.
     When this input is a keyword (which is never a valid theorem name),
     the theorem name is the concatenation of
     the old function name, the keyword, and the new function name,
     e.g. @('f-to-g') if
     @('f') is the new function name,
     @('g') is the old function name,
     and @(':-to-') is the keyword passed as the @(':new-to-old-name') input.
     Thus, the keyword specifies a separator
     between new and old function names.
     The concatenated symbol is in the same package as the new function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':new-to-old-name') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-')."))
  `(table ,*defaults-table-name* :new-to-old-name ,kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-new-to-old-name ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':new-to-old-name') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-new-to-old-name).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :new-to-old-name table))
       ((unless (consp pair))
        (prog2$ (raise "No :NEW-TO-OLD-NAME found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :NEW-TO-OLD-NAME is ~x0, which is not a keyword."
                 kwd)
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-new-to-old-name :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-old-to-new-enable
  :short "Set the default @(':old-to-new-enable') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-to-new-enable') input
     that specifies whether to enable the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the new function.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-to-new-enable') input.
     It must be a boolean.
     It cannot be @('t')
     if the default @(':new-to-old-enable') is currently @('t').")
   (xdoc::p
    "The initial value of this default is @('nil').")
   (xdoc::@def "set-default-input-old-to-new-enable"))

  (define set-default-input-old-to-new-enable-fn ((bool booleanp) ctx state)
    :returns (mv erp val state)
    :parents nil
    (b* ((table (table-alist+ *defaults-table-name* (w state)))
         (pair (assoc-eq :new-to-old-enable table)))
      (if (and (consp pair)
               (cdr pair)
               bool)
          (er-soft+ ctx t nil
                    "Since the :NEW-TO-OLD-ENABLE default is T, ~
                     the :OLD-TO-NEW-ENABLE default cannot be set to T. ~
                     At most one of these two defaults may be T at any time.")
        (value `(table ,*defaults-table-name* :old-to-new-enable ,bool)))))

  (defmacro set-default-input-old-to-new-enable (bool)
    (declare (xargs :guard (booleanp bool)))
    (b* ((ctx (cons 'set-default-input-old-to-new-enable bool)))
      `(make-event-terse
        (set-default-input-old-to-new-enable-fn ,bool ',ctx state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-to-new-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':old-to-new-enable') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-to-new-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-to-new-enable table))
       ((unless (consp pair))
        (raise "No :OLD-TO-NEW-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :OLD-TO-NEW-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-new-enable nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-new-to-old-enable
  :short "Set the default @(':new-to-old-enable') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include a @(':new-to-old-enable') input
     that specifies whether to enable the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the new function.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':new-to-old-enable') input.
     It must be a boolean.
     It cannot be @('t')
     if the default @(':old-to-new-enable') is currently @('t').")
   (xdoc::p
    "The initial value of this default is @('nil').")
   (xdoc::@def "set-default-input-new-to-old-enable"))

  (define set-default-input-new-to-old-enable-fn ((bool booleanp) ctx state)
    :returns (mv erp val state)
    :parents nil
    (b* ((table (table-alist+ *defaults-table-name* (w state)))
         (pair (assoc-eq :old-to-new-enable table)))
      (if (and (consp pair)
               (cdr pair)
               bool)
          (er-soft+ ctx t nil
                    "Since the :OLD-TO-NEW-ENABLE default is T, ~
                     the :NEW-TO-OLD-ENABLE default cannot be set to T. ~
                     At most one of these two defaults may be T at any time.")
        (value `(table ,*defaults-table-name* :new-to-old-enable ,bool)))))

  (defmacro set-default-input-new-to-old-enable (bool)
    (declare (xargs :guard (booleanp bool)))
    (b* ((ctx (cons 'set-default-input-new-to-old-enable bool)))
      `(make-event-terse
        (set-default-input-new-to-old-enable-fn ,bool ',ctx state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-new-to-old-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':new-to-old-enable') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-new-to-old-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :new-to-old-enable table))
       ((unless (consp pair))
        (raise "No :NEW-TO-OLD-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :NEW-TO-OLD-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-new-to-old-enable nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-old-to-wrapper-name (kwd)
  (declare (xargs :guard (keywordp kwd)))
  :short "Set the default @(':old-to-wrapper-name') input
          of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-to-wrapper-name') input
     that specifies the name of the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the wrapper function;
     this theorem is generated, and this input is allowed,
     only when the wrapper is generated.
     When this input is a symbol that is a valid theorem name,
     it is used as the theorem name.
     When this input is a keyword (which is never a valid theorem name),
     the theorem name is the concatenation of
     the old function name, the keyword, and the wrapper function name,
     e.g. @('f-to-g') if
     @('f') is the old function name,
     @('g') is the wrapper function name, and
     @(':-to-') is the keyword passed as the @(':old-to-wrapper-name') input.
     Thus, the keyword specifies a separator
     between old and wrapper function names.
     The concatenated symbol is in the same package as
     the wrapper function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-to-wrapper-name') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-')."))
  `(table ,*defaults-table-name* :old-to-wrapper-name ,kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-to-wrapper-name ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':old-to-wrapper-name') input
          of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-to-wrapper-name).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-to-wrapper-name table))
       ((unless (consp pair))
        (prog2$ (raise "No :OLD-TO-WRAPPER-NAME found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :OLD-TO-WRAPPER-NAME is ~x0, ~
                  which is not a keyword."
                 kwd)
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-wrapper-name :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-wrapper-to-old-name (kwd)
  (declare (xargs :guard (keywordp kwd)))
  :short "Set the default @(':wrapper-to-old-name') input
          of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':wrapper-to-old-name') input
     that specifies the name of the generated theorem
     that rewrites (a term involving) a call of the wrapper function
     to (a term involving) a call of the old function;
     this theorem is generated, and this input is allowed,
     only when the wrapper is generated.
     When this input is a symbol that is a valid theorem name,
     it is used as the theorem name.
     When this input is a keyword (which is never a valid theorem name),
     the theorem name is the concatenation of
     the old function name, the keyword, and the wrapper function name,
     e.g. @('f-to-g') if
     @('f') is the wrapper function name,
     @('g') is the old function name, and
     @(':-to-') is the keyword passed as the @(':wrapper-to-old-name') input.
     Thus, the keyword specifies a separator
     between wrapper and old function names.
     The concatenated symbol is in the same package as
     the wrapper function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':wrapper-to-old-name') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-')."))
  `(table ,*defaults-table-name* :wrapper-to-old-name ,kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-wrapper-to-old-name ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':wrapper-to-old-name') input
          of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-wrapper-to-old-name).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :wrapper-to-old-name table))
       ((unless (consp pair))
        (prog2$ (raise "No :WRAPPER-TO-OLD-NAME found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :WRAPPER-TO-OLD-NAME is ~x0, ~
                  which is not a keyword."
                 kwd)
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-wrapper-to-old-name :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-old-to-wrapper-enable
  :short "Set the default @(':old-to-wrapper-enable') input
          of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-to-wrapper-enable') input
     that specifies whether to enable the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the wrapper function.
     This theorem is generated, and this input is allowed,
     only when the wrapper is generated.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-to-wrapper-enable') input.
     It must be a boolean.
     It cannot be @('t')
     if the default @(':wrapper-to-old-enable') is currently @('t').")
   (xdoc::p
    "The initial value of this default is @('nil').")
   (xdoc::@def "set-default-input-old-to-wrapper-enable"))

  (define set-default-input-old-to-wrapper-enable-fn ((bool booleanp) ctx state)
    :returns (mv erp val state)
    :parents nil
    (b* ((table (table-alist+ *defaults-table-name* (w state)))
         (pair (assoc-eq :wrapper-to-old-enable table)))
      (if (and (consp pair)
               (cdr pair)
               bool)
          (er-soft+ ctx t nil
                    "Since the :WRAPPER-TO-OLD-ENABLE default is T, ~
                     the :OLD-TO-WRAPPER-ENABLE default cannot be set to T. ~
                     At most one of these two defaults may be T at any time.")
        (value `(table ,*defaults-table-name* :old-to-wrapper-enable ,bool)))))

  (defmacro set-default-input-old-to-wrapper-enable (bool)
    (declare (xargs :guard (booleanp bool)))
    (b* ((ctx (cons 'set-default-input-old-to-wrapper-enable bool)))
      `(make-event-terse
        (set-default-input-old-to-wrapper-enable-fn ,bool ',ctx state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-to-wrapper-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':old-to-wrapper-enable') input
          of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-to-wrapper-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-to-wrapper-enable table))
       ((unless (consp pair))
        (raise "No :OLD-TO-WRAPPER-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :OLD-TO-WRAPPER-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-wrapper-enable nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-wrapper-to-old-enable
  :short "Set the default @(':wrapper-to-old-enable') input
          of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include a @(':wrapper-to-old-enable') input
     that specifies whether to enable the generated theorem
     that rewrites (a term involving) a call of the old function
     to (a term involving) a call of the wrapper function.
     This theorem is generated, and this input is allowed,
     only when the wrapper is generated.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':wrapper-to-old-enable') input.
     It must be a boolean.
     It cannot be @('t')
     if the default @(':old-to-wrapper-enable') is currently @('t').")
   (xdoc::p
    "The initial value of this default is @('nil').")
   (xdoc::@def "set-default-input-wrapper-to-old-enable"))

  (define set-default-input-wrapper-to-old-enable-fn ((bool booleanp) ctx state)
    :returns (mv erp val state)
    :parents nil
    (b* ((table (table-alist+ *defaults-table-name* (w state)))
         (pair (assoc-eq :old-to-wrapper-enable table)))
      (if (and (consp pair)
               (cdr pair)
               bool)
          (er-soft+ ctx t nil
                    "Since the :OLD-TO-WRAPPER-ENABLE default is T, ~
                     the :WRAPPER-TO-OLD-ENABLE default cannot be set to T. ~
                     At most one of these two defaults may be T at any time.")
        (value `(table ,*defaults-table-name* :wrapper-to-old-enable ,bool)))))

  (defmacro set-default-input-wrapper-to-old-enable (bool)
    (declare (xargs :guard (booleanp bool)))
    (b* ((ctx (cons 'set-default-input-wrapper-to-old-enable bool)))
      `(make-event-terse
        (set-default-input-wrapper-to-old-enable-fn ,bool ',ctx state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-wrapper-to-old-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':wrapper-to-old-enable') input
          of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-wrapper-to-old-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :wrapper-to-old-enable table))
       ((unless (consp pair))
        (raise "No :WRAPPER-TO-OLD-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :WRAPPER-TO-OLD-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-wrapper-to-old-enable nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-old-if-new-name (kwd)
  (declare (xargs :guard (keywordp kwd)))
  :short "Set the default @(':old-if-new-name') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-if-new-name') input
     that specifies the name of the generated theorem
     asserting that the old function is implied by the new function.
     When this input is a symbol that is a valid theorem name,
     it is used as the theorem name.
     When this input is a keyword (which is never a valid theorem name),
     the theorem name is the concatenation of
     the old function name, the keyword, and the new function name,
     e.g. @('f-if-g') if
     @('f') is the old function name,
     @('g') is the new function name,
     and @(':-if-') is the keyword passed as the @(':old-if-new-name') input.
     Thus, the keyword specifies a separator
     between old and new function names.
     The concatenated symbol is in the same package as the new function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-if-new-name') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-if-')."))
  `(table ,*defaults-table-name* :old-if-new-name ,kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-if-new-name ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':old-if-new-name') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-if-new-name).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-if-new-name table))
       ((unless (consp pair))
        (prog2$ (raise "No :OLD-IF-NEW-NAME found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :OLD-IF-NEW-NAME is ~x0, which is not a keyword."
                 kwd)
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-if-new-name :-if-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-old-if-new-enable (bool)
  (declare (xargs :guard (booleanp bool)))
  :short "Set the default @(':old-if-new-enable') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-if-new-enable') input
     that specifies whether to enable the generated theorem
     asserting that the old function is implied by the new function.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-if-new-enable') input.
     It must be a boolean.")
   (xdoc::p
    "The initial value of this default is @('nil')."))
  `(table ,*defaults-table-name* :old-if-new-enable ,bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-if-new-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':old-if-new-enable') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-if-new-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-if-new-enable table))
       ((unless (consp pair))
        (raise "No :OLD-IF-NEW-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :OLD-IF-NEW-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-if-new-enable nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-default-input-wrapper-enable (bool)
  (declare (xargs :guard (booleanp bool)))
  :short "Set the default @(':wrapper-enable') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include a @(':wrapper-enable') input
     that specifies whether to enable the generated wrapper function,
     when a wrapper function is in fact generated
     (otherwise, this input is disallowed).")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':wrapper-enable') input.
     It must be a boolean.")
   (xdoc::p
    "The initial value of this default is @('nil')."))
  `(table ,*defaults-table-name* :wrapper-enable ,bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-wrapper-enable ((wrld plist-worldp))
  :returns (bool booleanp)
  :short "Get the default @(':wrapper-enable') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-wrapper-enable).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :wrapper-enable table))
       ((unless (consp pair))
        (raise "No :WRAPPER-ENABLE found in APT defaults table."))
       (bool (cdr pair))
       ((unless (booleanp bool))
        (raise
         "The default :WRAPPER-ENABLE is ~x0, which is not a boolean."
         bool)))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-wrapper-enable nil)
