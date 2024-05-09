; Versions of primitive functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/unguarded-primitives" :dir :system)

;; This book defines functions that are equivalent to ACL2 primitive functions
;; but have guards of t (for use in evaluators).

(defund car-unguarded (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defthm car-unguarded-correct
  (equal (car-unguarded x)
         (car x))
  :hints (("Goal" :in-theory (enable car-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund cdr-unguarded (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defthm cdr-unguarded-correct
  (equal (cdr-unguarded x)
         (cdr x))
  :hints (("Goal" :in-theory (enable cdr-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund char-code-unguarded (x)
  (declare (xargs :guard t))
  (if (characterp x)
      (char-code x)
    0))

(defthm char-code-unguarded-correct
  (equal (char-code-unguarded x)
         (char-code x))
  :hints (("Goal" :in-theory (enable char-code-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund code-char-unguarded (x)
  (declare (xargs :guard t))
  (if (and (integerp x)
           (<= 0 x)
           (< x 256))
      (code-char x)
    (code-char 0)))

(defthm code-char-unguarded-correct
  (equal (code-char-unguarded x)
         (code-char x))
  :hints (("Goal" :in-theory (enable code-char-unguarded)
           :use ((:instance completion-of-code-char)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symbol-package-name-unguarded (x)
  (declare (xargs :guard t))
  (if (symbolp x)
      (symbol-package-name x)
    ""))

(defthm symbol-package-name-unguarded-correct
  (equal (symbol-package-name-unguarded x)
         (symbol-package-name x))
  :hints (("Goal" :in-theory (enable symbol-package-name-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symbol-name-unguarded (x)
  (declare (xargs :guard t))
  (if (symbolp x)
      (symbol-name x)
    ""))

(defthm symbol-name-unguarded-correct
  (equal (symbol-name-unguarded x)
         (symbol-name x))
  :hints (("Goal" :in-theory (enable symbol-name-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pkg-imports-unguarded (pkg)
  (declare (xargs :guard t))
  (if (stringp pkg)
      (pkg-imports pkg)
    nil))

(defthm pkg-imports-unguarded-correct
  (equal (pkg-imports-unguarded pkg)
         (pkg-imports pkg))
  :hints (("Goal" :in-theory (enable pkg-imports-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pkg-witness-unguarded (pkg)
  (declare (xargs :guard t))
  (if (and (stringp pkg)
           (not (equal "" pkg)))
      (pkg-witness pkg)
    'acl2-pkg-witness))

(defthmd equal-when-symbols
  (implies (and (symbolp x)
                (symbolp y))
           (equal (equal x y)
                  (and (equal (symbol-name x) (symbol-name y))
                       (equal (symbol-package-name x) (symbol-package-name y)))))
  :hints (("Goal" :use (:instance symbol-equality
                                  (s1 x)
                                  (s2 y)))))

(defthm pkg-witness-unguarded-correct
  (equal (pkg-witness-unguarded pkg)
         (pkg-witness pkg))
  :hints (("Goal" :in-theory (e/d (pkg-witness-unguarded
                                   equal-when-symbols)
                                  (symbol-package-name-pkg-witness-name
                                   symbol-name-pkg-witness
                                   (:e pkg-witness-unguarded)
                                   (:e pkg-witness) ; prevent introduction of hide
                                   ))
           :use ((:instance symbol-package-name-pkg-witness-name
                            (pkg-name pkg))
                 (:instance symbol-name-pkg-witness
                            (pkg-name pkg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun intern-in-package-of-symbol-unguarded (str sym)
  (declare (xargs :guard t))
  (if (and (stringp str) (symbolp sym))
      (intern-in-package-of-symbol str sym)
    nil))

(defthm intern-in-package-of-symbol-unguarded-correct
  (equal (intern-in-package-of-symbol-unguarded str sym)
         (intern-in-package-of-symbol str sym))
  :hints (("Goal" :in-theory (enable intern-in-package-of-symbol-unguarded))))
