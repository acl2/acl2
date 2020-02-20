; Untranslation Preprocessing Utilities
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/pseudo-event-formp" :dir :system)
(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection add-const-to-untranslate-preprocess
  :parents (kestrel-utilities user-defined-functions-table)
  :short "Extend @(tsee untranslate-preprocess)
          to keep a constant unexpanded in output."
  :long
  "<p>
   This macro defines a new function
   and stores it into the @(tsee user-defined-functions-table)
   as the untranslation preprocessing function.
   This new function
   recognizes a term that is the expanded value of the given constant @('const')
   and turns it into the symbol that names the constant @('const'),
   while it delegates all other terms
   to the previous untranslation preprocessing function.
   If there was no previous untranslation preprocessing function,
   the new function returns @('nil') on all other terms,
   meaning that untranslation preprocessing is finished.
   The new function is in program mode,
   in case the previous untranslation preprocessing function
   is also in program mode.
   </p>"

  (define add-const-to-untranslate-preprocess-fn ((const symbolp) state)
    :returns (event pseudo-event-formp)
    :verify-guards nil
    (b* ((user-defined-functions-table
          (table-alist 'user-defined-functions-table (w state)))
         (old-untranslate-preprocess
          (cdr (assoc-eq 'untranslate-preprocess user-defined-functions-table)))
         (new-untranslate-preprocess
          (intern-in-package-of-symbol (string-append "UNTRANSLATE-PREPROCESS-"
                                                      (symbol-name const))
                                       const)))
      `(progn
         (defun ,new-untranslate-preprocess (term wrld)
           (declare (xargs :mode :program))
           (if (equal term (list 'quote ,const))
               ',const
             ,(and old-untranslate-preprocess
                   `(,old-untranslate-preprocess term wrld))))
         (table acl2::user-defined-functions-table
           'acl2::untranslate-preprocess
           ',new-untranslate-preprocess))))

  (defmacro add-const-to-untranslate-preprocess (const)
    (declare (xargs :guard (symbolp const)))
    `(make-event (add-const-to-untranslate-preprocess-fn ',const state))))
