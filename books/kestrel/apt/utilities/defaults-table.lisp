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

(defsection set-default-input-old-to-new-name
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
    "The initial value of this default is @(':-to-').")
   (xdoc::@def "set-default-input-old-to-new-name"))

  (defmacro set-default-input-old-to-new-name (kwd)
    (declare (xargs :guard (keywordp kwd)))
    `(table ,*defaults-table-name* :old-to-new-name ,kwd)))

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
                 "The default :OLD-TO-NEW-NAME is ~x0, which is not a keyword.")
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-new-name :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-new-to-old-name
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
    "The initial value of this default is @(':-to-').")
   (xdoc::@def "set-default-input-new-to-old-name"))

  (defmacro set-default-input-new-to-old-name (kwd)
    (declare (xargs :guard (keywordp kwd)))
    `(table ,*defaults-table-name* :new-to-old-name ,kwd)))

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
                 "The default :NEW-TO-OLD-NAME is ~x0, which is not a keyword.")
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
         "The default :OLD-TO-NEW-ENABLE is ~x0, which is not a boolean.")))
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
         "The default :NEW-TO-OLD-ENABLE is ~x0, which is not a boolean.")))
    bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-new-to-old-enable nil)
