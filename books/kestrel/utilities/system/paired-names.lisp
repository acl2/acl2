; System Utilities -- Paired Names
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/coerce" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc paired-names
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "Utilities for paired names."
  :long
  "<p>
   A <i>paired name</i> is a symbol consisting of three parts, in this order:
   </p>
   <ol>
     <li>
     A non-empty sequence of characters that is the first name of the pair.
     </li>
     <li>
     A non-empty sequence of characters
     that separates the two names of the pair.
     This character sequence is global but customizable.
     </li>
     <li>
     A non-empty sequence of characters that is the second name of the pair.
     </li>
   </ol>
   <p>
   Examples of paired names are:
   </p>
   <ul>
     <li>
     @('F-~>-G'), where
     @('F') is the first name,
     @('-~>') is the separator, and
     @('G') is the second name.
     </li>
     <li>
     @('LOGIC-SORT-IS-EXEC-SORT'), where
     @('LOGIC-SORT') is the first name,
     @('-IS-') is the separator, and
     @('EXEC-SORT') is the second name.
     </li>
   </ul>
   <p>
   Note that if the separator occurs in the first or second name,
   the paired name cannot be uniquely decomposed
   into its three constituents.
   For instance, if the separator is @('<->'),
   there are two different ways to decompose
   @('ABC<->DEF<->GHI').
   </p>
   <p>
   Paired names are useful, for instance,
   to denote theorems that state certain kinds of relations
   between functions (denoted by the first and second names of the pairs),
   where the separator describes the relation,
   e.g. @('F-~>-G') could denote a theorem stating that
   the function @('F') is transformed into an equivalent function @('G').
   </p>")

(defxdoc paired-name-separator
  :parents (paired-names)
  :short "Separator of the names in a paired name."
  :long
  "<p>
   This is stored in a singleton @(tsee table).
   </p>")

(define paired-name-separator-p (x)
  :returns (yes/no booleanp)
  :parents (paired-name-separator)
  :short "Recognize admissible separators for paired names."
  :long
  "<p>
   Any non-empty sequence of characters is allowed.
   </p>"
  (and (stringp x)
       (not (equal x ""))))

(table paired-name-separator nil nil
  :guard (and (equal key 'separator) ; one key => singleton table
              (paired-name-separator-p val)))

(defval *default-paired-name-separator*
  :parents (paired-name-separator)
  :short "Default separator for paired names."
  "-~>-")

(define get-paired-name-separator ((wrld plist-worldp))
  :returns (separator "A @(tsee paired-name-separator-p).")
  :verify-guards nil
  :parents (paired-name-separator)
  :short "Retrieve the current separator for paired names."
  :long
  "<p>
   If the separator is not set yet, the default is returned.
   </p>"
  (let ((pair (assoc-eq 'separator (table-alist 'paired-name-separator wrld))))
    (if pair (cdr pair) *default-paired-name-separator*)))

;; set to default the first time this form is evaluated,
;; then set to current (i.e. no change) when this form is evaluated again
;; (e.g. when this file is redundantly loaded):
(table paired-name-separator
  'separator (get-paired-name-separator world))

(defsection set-paired-name-separator
  :parents (paired-name-separator)
  :short "Set the separator for paired names."
  :long
  "<p>
   This macro generates an event to override
   the default, or the previously set value.
   </p>
   @(def set-paired-name-separator)"
  (defmacro set-paired-name-separator (separator)
    `(table paired-name-separator 'separator ,separator)))

(define make-paired-name ((first-name symbolp)
                          (second-name symbolp)
                          (pkg-from :type (integer 1 2))
                          (wrld plist-worldp))
  :returns (name symbolp)
  :verify-guards nil
  :parents (paired-names)
  :short "Construct a paired name."
  :long
  "<p>
   The resulting name consists of the given first and second names,
   separated by the current separator.
   An additional argument says whether the package of the resulting name
   should be the same as the first or second name
   (immaterial if the first and second names are in the same package).
   </p>"
  (b* ((first-chars (explode (symbol-name first-name)))
       (second-chars (explode (symbol-name second-name)))
       (separator-chars (explode (get-paired-name-separator wrld)))
       (name-chars (append first-chars
                           separator-chars
                           second-chars))
       (pkg-symbol (case pkg-from
                     (1 first-name)
                     (2 second-name)
                     (t (impossible)))))
    (intern-in-package-of-symbol (implode name-chars) pkg-symbol)))
