; Strings that indicate methods within collections of classes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in method-designator-strings-tests.lisp

;; TODO: Move this book to the JVM package.  Maybe also include stuff like class-namep?

(include-book "kestrel/utilities/string-utilities" :dir :system)
(include-book "classes") ;reduce?  really we only need stuff about names
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (disable reverse)))

;move
(defthm reverse-of-reverse-when-stringp
  (implies (stringp str)
           (equal (reverse (reverse str))
                  str))
  :hints (("Goal" :in-theory (enable reverse))))

;; example "foo.bar.baz(II)I"
(defun method-designator-stringp (x)
  (declare (xargs :guard t))
  (stringp x) ;todo: could add more checking
  )

;; ;same as in std/lists/reverse.lisp
;; (defthm stringp-of-reverse
;;   (equal (stringp (reverse x))
;;          (stringp x)))

;; (defthm stringp-of-reverse
;;   (implies (stringp str)
;;            (stringp (reverse str)))
;;   :hints (("Goal" :in-theory (enable reverse))))

;; TODO: add guards (or variants) of drop-string-before-char and
;; split-string-before-char that require the char to be in the string

;; Return the method-descriptor of the method.  Example: "(II)I"
(defun extract-method-descriptor (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (drop-string-before-char method-designator-string #\())

(defun extract-method-name (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (mv-let (first rest)
    (split-string-before-char method-designator-string #\() ;strip the signature
    (declare (ignore rest))
    (mv-let (first rest)
      (read-string-to-last-terminator first #\.)
      (declare (ignore first))
      rest)))

;extracts the (possibly qualified) class-name
(defund extract-method-class (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)
                  :guard-hints (("Goal" :in-theory (enable READ-STRING-TO-LAST-TERMINATOR)))))
  (let* ((class-and-method (substring-before-char method-designator-string #\()) ;strip the signature
         (class-name (substring-before-last-occurrence class-and-method #\.)))
    class-name))

(defthm stringp-of-extract-method-class
  (implies (method-designator-stringp method-designator-string)
           (stringp (extract-method-class method-designator-string)))
  :hints (("Goal" :in-theory (enable extract-method-class))))

(defun extract-package-name (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (jvm::extract-package-name-from-class-name (extract-method-class method-designator-string)))
