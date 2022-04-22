; A lightweight book about intern-in-package-of-symbol
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "map-symbol-name"))

(local (in-theory (disable member-equal)))

;; Should usually be left disabled.
(defthmd symbol-equality-strong
  (implies (or (symbolp s1)
               (symbolp s2))
           (equal (equal s1 s2)
                  (and (equal (symbol-name s1)
                              (symbol-name s2))
                       (equal (symbol-package-name s1)
                              (symbol-package-name s2)))))
  :hints (("Goal" :use (:instance symbol-equality))))

(defthm equal-of-intern-in-package-of-symbol-and-intern-in-package-of-symbol-same-arg2
  (implies (and (stringp x1)
                (stringp x2)
                (symbolp y))
           (equal (equal (intern-in-package-of-symbol x1 y)
                         (intern-in-package-of-symbol x2 y))
                  (equal x1 x2)))
  :hints (("Goal" :use (:instance symbol-equality-strong
                                  (s1 (intern-in-package-of-symbol x1 y))
                                  (s2 (intern-in-package-of-symbol x2 y))))))

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

;; Note that a legal variable can sometimes have an empty
;; name. For example, (legal-variablep 'acl2::||) = t.

(local
 (defthm member-symbol-name-iff
   (iff (member-symbol-name str l)
        (member-equal str (map-symbol-name l)))
   :hints (("Goal" :in-theory (enable member-symbol-name
                                      member-equal)))))

(local
 (defthm car-of-member-symbol-name-iff
   (implies (not (equal "NIL" str))
            (iff (car (member-symbol-name str l))
                 (member-equal str (map-symbol-name l))))
   :hints (("GOAL" :in-theory (enable member-symbol-name
                                      member-equal)))))

;; If a string is in the pkg-imports of the ACL2 package, then importing in
;; into the ACL2 package gives a symbol not in the acl2 package.

(defthm intern-in-package-of-symbol-iff
  (implies (and (equal (symbol-package-name sym) "ACL2") ;gen?
                ;; (not (member-symbol-name str (pkg-imports (symbol-package-name sym))))
                (stringp str)
                ;; (symbolp sym) ; not needed since non-symbols have a symbol-package-name of ""
                )
           (iff (intern-in-package-of-symbol str sym)
                (not (equal str "NIL"))))
  :hints (("Goal" :use (:instance equal-of-intern-in-package-of-symbol (sym2 sym) (sym nil))
           :cases ((symbolp sym))
           :in-theory (e/d (intern-in-package-of-symbol-is-identity) (equal-of-intern-in-package-of-symbol)))))

(defthm symbol-package-name-of-intern-in-package-of-symbol
  (equal (symbol-package-name (intern-in-package-of-symbol str sym))
         (if (and (symbolp sym)
                  (stringp str))
             (if (member-symbol-name str (pkg-imports (symbol-package-name sym)))
                 (symbol-package-name (car (member-symbol-name str (pkg-imports (symbol-package-name sym)))))
               (symbol-package-name sym))
           "COMMON-LISP")))

(defthm keywordp-of-intern-in-package-of-symbol-when-keywordp
  (implies (keywordp sym)
           (equal (keywordp (intern-in-package-of-symbol str sym))
                  (stringp str)))
  :hints (("Goal" :in-theory (enable keywordp member-equal))))
