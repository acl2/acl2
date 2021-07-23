; Theorems about legal-variablep
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; STATUS: In-progress

(in-package "ACL2")

(include-book "imported-symbols")
(local (include-book "imported-symbols-theorems"))
(include-book "map-symbol-name")
(local (include-book "../lists-light/member-equal"))

(in-theory (disable legal-variablep))

;make local?
(in-theory (disable intern-in-package-of-symbol-is-identity  ;led to problems (huge constant list)
                    ))

(local (in-theory (disable length char member-equal true-listp)))

(local
 (defthm char-of-0-when-equal-of-len-and-0-cheap
   (implies (equal (length s) 0)
            (equal (char s 0)
                   nil))
   :rule-classes ((:rewrite :backchain-limit-lst (0)))
   :hints (("Goal" ; :cases ((stringp s))
            :expand (len (coerce s 'list))
            :in-theory (enable char length len)))))

(defun all-symbols-have-packagep (syms pkg)
  (declare (xargs :guard (and (stringp pkg)
                              (symbol-listp syms))))
  (if (endp syms)
      t
    (and (equal (symbol-package-name (first syms)) pkg)
         (all-symbols-have-packagep (rest syms) pkg))))

(defthm all-symbols-have-packagep-of-set-difference-equal
  (implies (all-symbols-have-packagep x pkg)
           (all-symbols-have-packagep (set-difference-equal x y) pkg))
  :hints (("Goal" :in-theory (enable all-symbols-have-packagep set-difference-equal))))

(local
 (defthm symbol-listp-of-set-difference-equal
  (implies (symbol-listp x)
           (symbol-listp (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable symbol-listp set-difference-equal)))))

(defthm all-symbols-have-packagep-of-common-lisp-symbols-from-main-lisp-package
  (all-symbols-have-packagep (common-lisp-symbols-from-main-lisp-package) "COMMON-LISP")
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

(defthm all-symbols-have-packagep-of-common-lisp-specials-and-constants
  (all-symbols-have-packagep (common-lisp-specials-and-constants) "COMMON-LISP")
  :hints (("Goal" :in-theory (enable common-lisp-specials-and-constants))))

;; An more clear definition for legal-variablep
(defthmd legal-variablep-alt-def
  (equal (legal-variablep name)
         (and (symbolp name)
              ;; Can't be t:
              (not (equal t name))
              ;; Can't be nil:
              (not (equal nil name))
              (let ((symbol-name (symbol-name name))
                    (package-name (symbol-package-name name)))
                (and ;; Can't be a keyword:
                 (not (equal package-name "KEYWORD"))
                 ;; Name can't start and end with star:
                 (not (and (equal (char symbol-name 0) #\*)
                           (equal (char symbol-name (1- (length symbol-name))) #\*)))
                 ;; Name can't start with &:
                 (not (equal (char symbol-name 0) #\&))
                 ;; Special case for the COMMON-LISP package (must be in a
                 ;; specific set of allowed symbols):
                 (if (equal package-name *main-lisp-package-name*)
                     ;; note that we use name, not symbol-name here:
                     (if (member-equal name (legal-vars-in-common-lisp-package)) t nil)
                   t)))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (e/d (legal-variablep
                                   legal-variable-or-constant-namep
                                   legal-vars-in-common-lisp-package
                                   (:e common-lisp-symbols-from-main-lisp-package)
                                   (:e common-lisp-specials-and-constants))
                                  (set-difference-equal
                                   (:e set-difference-equal))))))

;; Note that a legal variable can sometimes have an empty
;; name. For example, (legal-variablep 'acl2::||) = t.

(defthmd equal-of-intern-in-package-of-symbol
  (implies (and (stringp str)
                (symbolp sym2)
                (not (member-symbol-name str (pkg-imports (symbol-package-name sym2)))))
           (equal (equal sym (intern-in-package-of-symbol str sym2))
                  (and (symbolp sym)
                       (equal str (symbol-name sym))
                       (equal (symbol-package-name sym)
                              (symbol-package-name sym2)))))
  :hints (("Goal" :cases ((symbol-package-name sym2)))))

(defthm member-symbol-name-iff
  (iff (member-symbol-name str l)
       (member-equal str (map-symbol-name l)))
  :hints (("Goal" :in-theory (enable member-symbol-name))))

(defthm car-of-member-symbol-name-iff
  (implies (not (equal "NIL" str))
           (iff (car (member-symbol-name str l))
                (member-equal str (map-symbol-name l))))
  :hints (("GOAL" :in-theory (enable member-symbol-name))))

;; If a string is in the pkg-imports of the ACL2 package, then importing in
;; into the ACL2 package gives a symbol not in the acl2 package.

(defthm intern-in-package-of-symbol-iff
  (implies (and (equal (symbol-package-name sym) "ACL2") ;gen?
                ;; (not (member-symbol-name str (pkg-imports (symbol-package-name sym))))
                (stringp str)
                (symbolp sym))
           (iff (intern-in-package-of-symbol str sym)
                (not (equal str "NIL"))))
  :hints (("Goal" :use (:instance equal-of-intern-in-package-of-symbol (sym2 sym) (sym nil))
           :in-theory (e/d (intern-in-package-of-symbol-is-identity) (equal-of-intern-in-package-of-symbol)))))

;; Yikes!  This applies to terms like (equal x 'foo), due to ACL2's overly aggressive unification of constants.
(defthmd not-equal-of-intern-in-package-of-symbol-when-not-equal-of-symbol-name
  (implies (and (not (equal str (symbol-name sym2)))
                (stringp str)
                (symbolp sym))
           (not (equal sym2 (intern-in-package-of-symbol str sym)))))

;; both cases
(defthm symbol-package-name-of-intern-in-package-of-symbol
  (implies (and (stringp x)
                (symbolp y))
           (equal (symbol-package-name (intern-in-package-of-symbol x y))
                  (if (member-symbol-name
                       x
                       (pkg-imports (symbol-package-name y)))
                      (symbol-package-name (car (member-symbol-name
                                                 x
                                                 (pkg-imports (symbol-package-name y)))))
                    (symbol-package-name y))))
  :hints (("Goal" :in-theory (enable intern-in-package-of-symbol-is-identity))))

(defund map-symbol-package-name (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (cons (symbol-package-name (first syms))
          (map-symbol-package-name (rest syms)))))

(defthm not-equal-of-symbol-package-name-when-not-member-equal-of-map-symbol-package-name
  (implies (and (not (member-equal str (map-symbol-package-name syms)))
                (member-equal sym syms))
           (not (equal (symbol-package-name sym) str)))
  :hints (("Goal" :in-theory (enable member-symbol-name
                                     map-symbol-package-name))))

(defthm member-equal-of-symbol-package-name-and-map-symbol-package-name
  (implies (member-equal sym syms)
           (member-equal (symbol-package-name sym)
                         (map-symbol-package-name syms)))
  :hints (("Goal" :in-theory (enable map-symbol-package-name))))

(defthm member-equal-of-car-of-member-symbol-name
  (implies (member-symbol-name str syms)
           (member-equal (car (member-symbol-name str syms))
                         syms))
  :hints (("Goal" :in-theory (enable member-symbol-name))))

;drop?
(defthm member-equal-of-car-of-member-symbol-name-gen
  (implies (and (member-symbol-name str syms)
                (subsetp-equal syms syms2))
           (member-equal (car (member-symbol-name str syms))
                         syms2))
  :hints (("Goal" :in-theory (enable member-symbol-name))))

(defthmd not-equal-of-symbol-package-name-of-car-of-member-symbol-name-1
  (implies (and (not (member-equal str2 (map-symbol-package-name syms)))
                (member-symbol-name str syms) ;this case
                )
           (equal (equal (symbol-package-name (car (member-symbol-name str syms)))
                         str2)
                  nil)))

(defthmd not-equal-of-symbol-package-name-of-car-of-member-symbol-name-2
  (implies (and (not (member-equal str2 (map-symbol-package-name syms)))
                (not (member-symbol-name str syms)) ;this case
                )
           (equal (equal (symbol-package-name (car (member-symbol-name str syms)))
                         str2)
                  (equal "COMMON-LISP" str2)))
  :hints (("Goal" :in-theory (disable member-symbol-name-iff
                                      MEMBER-EQUAL-OF-SYMBOL-PACKAGE-NAME-AND-MAP-SYMBOL-PACKAGE-NAME))))

(defthm not-equal-of-symbol-package-name-of-car-of-member-symbol-name
  (implies (not (member-equal str2 (map-symbol-package-name syms)))
           (equal (equal (symbol-package-name (car (member-symbol-name str syms)))
                         str2)
                  (if (member-symbol-name str syms)
                      nil
                    (equal "COMMON-LISP" str2))))
  :hints (("Goal" :use (not-equal-of-symbol-package-name-of-car-of-member-symbol-name-2
                        not-equal-of-symbol-package-name-of-car-of-member-symbol-name-1))))

(defthm member-equal-of-t-and-map-symbol-name-of-pkg-imports-of-acl2
  (member-equal "T" (map-symbol-name (common-lisp-symbols-from-main-lisp-package)))
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

(defthm not-member-equal-of-empty-string-and-map-symbol-name-of-pkg-imports-of-acl2
  (not (member-equal "" (map-symbol-name (common-lisp-symbols-from-main-lisp-package))))
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

(defthm car-of-member-symbol-name-of-pkg-imports-of-acl2
  (equal (car (member-symbol-name "T" (common-lisp-symbols-from-main-lisp-package)))
         t)
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

;do we need this?
(defund no-half-starred-strings (strs)
  (if (endp strs)
      t
    (let ((str (first strs)))
      (and (not (and (equal (char str 0) #\*)
                     (not (equal (char str (+ -1 (length str)))
                                 #\*))))
           ;; violated by do*
           ;; (not (and (not (equal (char str 0) #\*))
           ;;           (equal (char str (+ -1 (length str)))
           ;;                  #\*)))
           (no-half-starred-strings (rest strs))))))

;rename
(defthm no-half-starred-strings-of-map-symbol-name-of-pkg-imports-of-acl2
  (no-half-starred-strings (map-symbol-name (common-lisp-symbols-from-main-lisp-package)))
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

(defthm no-half-starred-strings-of-map-symbol-name-of-common-lisp-specials-and-constants
  (no-half-starred-strings (map-symbol-name (common-lisp-specials-and-constants)))
  :hints (("Goal" :in-theory (enable common-lisp-specials-and-constants))))

(defthmd not-member-equal-when-no-half-starred-strings
  (implies (and (no-half-starred-strings strs)
                (equal (char str 0) #\*)
                (not (equal (char str (+ -1 (length str)))
                            #\*)))
           (not (member-equal str strs)))
  :hints (("Goal" :in-theory (enable no-half-starred-strings))))

(defthm pkg-imports-of-acl2
  (equal (pkg-imports "ACL2")
         (common-lisp-symbols-from-main-lisp-package))
  :hints (("Goal" :in-theory (enable common-lisp-symbols-from-main-lisp-package))))

(defthm pkg-imports-of-common-lisp
  (equal (pkg-imports "COMMON-LISP")
         nil))

(defthm symbol-package-name-when-member-equal-and-all-symbols-have-packagep
  (implies (and (member-equal sym syms)
                (all-symbols-have-packagep syms pkg))
           (equal (symbol-package-name sym)
                  pkg))
  :hints (("Goal" :in-theory (enable))))

(defthm symbol-package-name-when-member-equal-of-common-lisp-symbols-from-main-lisp-package
  (implies (member-equal sym (common-lisp-symbols-from-main-lisp-package))
           (equal (symbol-package-name sym)
                  "COMMON-LISP"))
  :hints (("Goal"
           :use (:instance symbol-package-name-when-member-equal-and-all-symbols-have-packagep
                           (pkg "COMMON-LISP")
                           (syms (common-lisp-symbols-from-main-lisp-package)))
           :in-theory (disable symbol-package-name-when-member-equal-and-all-symbols-have-packagep
                               (:e common-lisp-symbols-from-main-lisp-package)))))

(defthm member-equal-of-map-symbol-name-when-member-equal-of-map-symbol-name-of-set-difference-equal
  (implies (member-equal str (map-symbol-name (set-difference-equal syms1 syms2)))
           (member-equal str (map-symbol-name syms1))))

(defthm member-equal-of-symbol-name
  (implies (member-equal sym syms)
           (member-equal (symbol-name sym) (map-symbol-name syms)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthmd symbol-equality-cheap
  (implies (and (equal (symbol-name s1)
                       (symbol-name s2))
                (equal (symbol-package-name s1)
                       (symbol-package-name s2))
                (symbolp s1)
                (symbolp s2)
                )
           (equal (equal s1 s2)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil)))
  :hints (("Goal" :use (:instance symbol-equality))))

(defthm member-equal-of-symbol-name-strong
  (implies (and (all-symbols-have-packagep syms (symbol-package-name sym))
                (symbolp sym)
                (symbol-listp syms))
           (iff (member-equal (symbol-name sym) (map-symbol-name syms))
                (member-equal sym syms)))
  :hints (("Goal" :in-theory (e/d (member-equal symbol-equality-cheap)
                                  (SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-OF-COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE ;looped
                                   )))))

(defthm member-equal-of-map-symbol-name-of-set-difference-equal
  (implies (and (all-symbols-have-packagep syms1 pkg)
                (all-symbols-have-packagep syms2 pkg)
                (symbol-listp syms1)
                (symbol-listp syms2))
           (iff (member-equal str (map-symbol-name (set-difference-equal syms1 syms2)))
                (and (member-equal str (map-symbol-name syms1))
                     (not (member-equal str (map-symbol-name syms2))))))
  :hints (("Goal" :in-theory (enable map-symbol-name map-symbol-name))))

(defthmd member-equal-of-map-symbol-name-of-set-difference-equal-special
  (implies (and (all-symbols-have-packagep syms1 "COMMON-LISP")
                (all-symbols-have-packagep syms2 "COMMON-LISP")
                (symbol-listp syms1)
                (symbol-listp syms2))
           (iff (member-equal str (map-symbol-name (set-difference-equal syms1 syms2)))
                (and (member-equal str (map-symbol-name syms1))
                     (not (member-equal str (map-symbol-name syms2))))))
  :hints (("Goal" :in-theory (enable map-symbol-name map-symbol-name))))

(defthm equal-of-intern-in-package-of-symbol-of-symbol-name-same
  (implies (and ;(symbolp sym)
            (symbolp sym2)
            (not (member-symbol-name (symbol-name sym) (pkg-imports (symbol-package-name sym2)))))
           (equal (equal sym (intern-in-package-of-symbol (symbol-name sym) sym2))
                  (and (symbolp sym)
                       (equal (symbol-package-name sym)
                              (symbol-package-name sym2)))))
  :hints (("Goal" :in-theory (enable equal-of-intern-in-package-of-symbol))))


(defthm car-of-member-symbol-name-when-all-symbols-have-packagep-common-lisp
  (implies (and (member-equal str (map-symbol-name syms))
                (symbol-listp syms)
                (all-symbols-have-packagep syms "COMMON-LISP"))
           (equal (car (member-symbol-name str syms))
                  (intern str "COMMON-LISP")))
  :hints (("Goal" :in-theory (enable member-symbol-name))))

;; (defthm
;;  (implies (member-equal str (map-symbol-name (common-lisp-symbols-from-main-lisp-package)))
;;           (equal (car (member-symbol-name str (common-lisp-symbols-from-main-lisp-package)))
;;                  (intern str "COMMON-LISP")))
;;  :hints (("Goal" :in-theory (disable (:E common-lisp-symbols-from-main-lisp-package)))))

(defthm member-equal-of-intern-in-package-of-symbol-iff
  (implies (and (all-symbols-have-packagep syms (symbol-package-name sym))
                (not (pkg-imports (symbol-package-name sym))) ;true for a symbol whose symbol-package-name is "COMMON-LISP"
                (symbolp sym)
                (stringp str)
                (symbol-listp syms))
           (iff (member-equal (intern-in-package-of-symbol str sym) syms)
                (member-equal str (map-symbol-name syms))))
  :hints (("Goal" :in-theory (e/d (map-symbol-name member-equal)
                                  (symbol-package-name-when-member-equal-of-common-lisp-symbols-from-main-lisp-package)))))

(defthm equal-of-length-and-0-when-stringp
  (implies (stringp x)
           (equal (equal (length x) 0)
                  (equal x "")))
  :hints (("Goal" :expand ((len (coerce x 'list)))
           :use (:instance default-coerce-3 (x (coerce x 'list)))
           :in-theory (e/d (length len)
                           (default-coerce-3
                            (:e coerce))))))

;; Tests whether a string would be a legal variable name when interned into the ACL2 package.
(defund legal-variable-name-in-acl2-packagep (str)
  (declare (xargs :guard (stringp str)))
  (or (equal str "") ; prevents calling char below on the empty string
      (and
       ;; name can't start and end with *:
       (not (and (equal (char str 0) #\*)
                 (equal (char str (1- (length str))) #\*)))
       ;; name can't start with &:
       (not (equal (char str 0) #\&))
       ;; name can't be in this set (for symbols imported from the common-lisp package, includes T and NIL):
       (not (member-equal str (names-of-common-lisp-specials-and-constants)))
       )))

(defthmd equal-of-intern-in-package-of-symbol-other-case
  (implies (and (stringp str)
                (symbolp sym2)
                (member-symbol-name str (pkg-imports (symbol-package-name sym2)))  ;this case
                )
           (equal (equal sym (intern-in-package-of-symbol str sym2))
                  (and (symbolp sym)
                       (equal str (symbol-name sym))
                       (equal (symbol-package-name sym)
                              (symbol-package-name (car (member-symbol-name str (pkg-imports (symbol-package-name sym2)))))))))
  :hints (("Goal" :use (:instance symbol-equality
                                  (s1 sym)
                                  (s2 (INTERN-IN-PACKAGE-OF-SYMBOL (SYMBOL-NAME SYM)
                                             SYM2))))))

(defthmd equal-of-intern-in-package-of-symbol-both
  (implies (and (stringp str)
                (symbolp sym2))
           (equal (equal sym (intern-in-package-of-symbol str sym2))
                  (and (symbolp sym)
                       (equal str (symbol-name sym))
                       ;; the package of sym depends on whether a symbol named str is ported into the package of sym2
                       (equal (symbol-package-name sym)
                              (if (member-symbol-name str (pkg-imports (symbol-package-name sym2)))
                                  ;; sym2's package imports a symbol named str, so the result of intern-in-package-of-symbol has that symbol's package:
                                  (symbol-package-name (car (member-symbol-name str (pkg-imports (symbol-package-name sym2)))))
                                (symbol-package-name sym2))))))
  :hints (("Goal" :in-theory (enable equal-of-intern-in-package-of-symbol-other-case))))

(defthm member-equal-of-map-symbol-name-when-subsetp
  (implies (and (member-equal str (map-symbol-name x))
                (subsetp x y))
           (member-equal str (map-symbol-name y))))

;; Precisely characterizes when interning a symbol in the ACL2 package results
;; in a legal variable.
(defthm legal-variablep-of-intern-in-package-of-symbol
  (implies (and (equal (symbol-package-name sym) "ACL2") ;gen
                (stringp str)
                (symbolp sym))
           (equal (legal-variablep (intern-in-package-of-symbol str sym))
                  (legal-variable-name-in-acl2-packagep str)))
  :hints (("Goal" :in-theory (e/d (legal-variable-name-in-acl2-packagep
                                   legal-variablep-alt-def
                                   legal-vars-in-common-lisp-package
                                   equal-of-intern-in-package-of-symbol
                                   equal-of-intern-in-package-of-symbol-both
                                   intern-in-package-of-symbol-is-identity
                                   names-of-common-lisp-specials-and-constants
                                   member-equal-of-map-symbol-name-of-set-difference-equal-special)
                                  ( ;car-of-member-symbol-name-when-all-symbols-have-packagep-common-lisp
                                   acl2-package
                                   (:e common-lisp-symbols-from-main-lisp-package)
                                   (:e common-lisp-specials-and-constants)
                                   (:e pkg-imports))))))
