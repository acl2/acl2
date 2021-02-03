; Theorems about the functions in imported-symbols.lisp
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These theorems are in a separate book so that they can be included only
;; locally, even when the definitions in imported-symbols.lisp are included
;; non-locally.

(include-book "imported-symbols")

(defthm symbol-listp-of-common-lisp-symbols-from-main-lisp-package
  (symbol-listp (common-lisp-symbols-from-main-lisp-package))
  :hints (("Goal" :in-theory (enable (:e common-lisp-symbols-from-main-lisp-package)))))

(defthm member-equal-of-nil-and-map-symbol-name-of-common-lisp-symbols-from-main-lisp-package
  (member-equal "NIL" (map-symbol-name (common-lisp-symbols-from-main-lisp-package)))
  :hints (("Goal" :in-theory (enable (:e common-lisp-symbols-from-main-lisp-package)))))

(defthm symbol-listp-of-common-lisp-specials-and-constants
  (symbol-listp (common-lisp-specials-and-constants))
  :hints (("Goal" :in-theory (enable (:e common-lisp-specials-and-constants)))))

(defthm member-equal-of-nil-and-map-symbol-name-of-common-lisp-specials-and-constants
  (member-equal "NIL" (map-symbol-name (common-lisp-specials-and-constants)))
  :hints (("Goal" :in-theory (enable (:e common-lisp-specials-and-constants)))))

(defthm member-equal-of-t-and-map-symbol-name-of-common-lisp-specials-and-constants
  (member-equal "T" (map-symbol-name (common-lisp-specials-and-constants)))
  :hints (("Goal" :in-theory (enable (:e common-lisp-specials-and-constants)))))

(defthm subsetp-equal-of-common-lisp-specials-and-constants-and-common-lisp-symbols-from-main-lisp-package
  (subsetp-equal (common-lisp-specials-and-constants)
                 (common-lisp-symbols-from-main-lisp-package))
  :hints (("Goal" :in-theory (enable (:e common-lisp-specials-and-constants)
                                     (:e common-lisp-symbols-from-main-lisp-package)))))

(defthm symbol-listp-of-legal-vars-in-common-lisp-package
  (symbol-listp (legal-vars-in-common-lisp-package))
  :hints (("Goal" :in-theory (enable (:e legal-vars-in-common-lisp-package)))))

(defthm not-member-equal-of-empty-symbol-and-names-of-common-lisp-specials-and-constants
  (not (member-equal '|| (names-of-common-lisp-specials-and-constants)))
  :hints (("Goal" :in-theory (enable (:e names-of-common-lisp-specials-and-constants)))))
