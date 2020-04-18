; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/std/system/table-alist-plus" :dir :system)
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
    "We provide event-level macros to change the defaults.
     These should be used instead of modifying the table directly.
     Some defaults may have a default (i.e. initial) value.")
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

(defsection set-default-input-old-to-new
  :short "Set the default @(':old-to-new') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include an @(':old-to-new') input
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
     and @(':-to-') is the keyword passed as the @(':old-to-new') input.
     Thus, the keyword specifies a separator
     between old and new function names.
     The concatenated symbol is in the same package as the new function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':old-to-new') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-').")
   (xdoc::@def "set-default-input-old-to-new"))

  (defmacro set-default-input-old-to-new (kwd)
    (declare (xargs :guard (keywordp kwd)))
    `(table ,*defaults-table-name* :old-to-new ,kwd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-old-to-new ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':old-to-new') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-old-to-new).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :old-to-new table))
       ((unless (consp pair))
        (prog2$ (raise "No :OLD-TO-NEW found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :OLD-TO-NEW is ~x0, which is not a keyword.")
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-old-to-new :-to-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-default-input-new-to-old
  :short "Set the default @(':new-to-old') input of APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some APT transformations include a @(':new-to-old') input
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
     and @(':-to-') is the keyword passed as the @(':new-to-old') input.
     Thus, the keyword specifies a separator
     between new and old function names.
     The concatenated symbol is in the same package as the new function name.")
   (xdoc::p
    "This macro sets an entry in the APT defaults table
     that provides the default value of the @(':new-to-old') input.
     It must be a keyword, which is used as a separator as described above.
     It would not make sense to have a complete theorem name as default.")
   (xdoc::p
    "The initial value of this default is @(':-to-').")
   (xdoc::@def "set-default-input-new-to-old"))

  (defmacro set-default-input-new-to-old (kwd)
    (declare (xargs :guard (keywordp kwd)))
    `(table ,*defaults-table-name* :new-to-old ,kwd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-default-input-new-to-old ((wrld plist-worldp))
  :returns (kwd keywordp)
  :short "Get the default @(':new-to-old') input of APT transformations."
  :long
  (xdoc::topstring-p
   "See @(tsee set-default-input-new-to-old).")
  (b* ((table (table-alist+ *defaults-table-name* wrld))
       (pair (assoc-eq :new-to-old table))
       ((unless (consp pair))
        (prog2$ (raise "No :NEW-TO-OLD found in APT defaults table.")
                :irrelevant-keyword-for-unconditional-returns-theorem))
       (kwd (cdr pair))
       ((unless (keywordp kwd))
        (prog2$ (raise
                 "The default :NEW-TO-OLD is ~x0, which is not a keyword.")
                :irrelevant-keyword-for-unconditional-returns-theorem)))
    kwd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-input-new-to-old :-to-)

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
     It must be a boolean.")
   (xdoc::p
    "The initial value of this default is @('nil').")
   (xdoc::@def "set-default-input-old-to-new-enable"))

  (defmacro set-default-input-old-to-new-enable (bool)
    (declare (xargs :guard (booleanp bool)))
    `(table ,*defaults-table-name* :old-to-new-enable ,bool)))

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
