; Recognizer for untranslated terms that are variables
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/legal-variablep" :dir :system) ;for legal-variable-name-in-acl2-packagep

;; An untranslated variable is a symbol, with several additional restrictions.
;; For example, t and nil are constants, as are keywords (all of these things
;; get quoted by translate).  Something with the syntax of a constant, like
;; *foo*, is also not an untranslated variable.
(defund untranslated-variablep (x)
  (declare (xargs :guard t))
  (legal-variablep x))

(defthm untranslated-variablep-forward-to-symbolp
  (implies (untranslated-variablep x)
           (symbolp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-variablep legal-variablep))))

;; Very similar to legal-variablep-of-intern-in-package-of-symbol.
(defthm untranslated-variablep-of-intern-in-package-of-symbol
  (implies (and (equal (symbol-package-name sym) "ACL2") ;gen
                (stringp str)
                (symbolp sym))
           (equal (untranslated-variablep (intern-in-package-of-symbol str sym))
                  (legal-variable-name-in-acl2-packagep str)))
  :hints (("Goal" :in-theory (enable untranslated-variablep))))
