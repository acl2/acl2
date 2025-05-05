; Strings that indicate methods within collections of classes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A method-designator-string uniquely identifies a method within a set of classes.

;; Example: "foo.bar.baz.ClassName.methodName(II)I"

;; See tests in method-designator-strings-tests.lisp

;; TODO: Move this book to the JVM package.  Maybe also include stuff like class-namep?

(include-book "kestrel/utilities/string-utilities" :dir :system)
(include-book "class-names")
(include-book "method-names")
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(defun method-designator-stringp (x)
  (declare (xargs :guard t))
  (stringp x) ;todo: could add more checking
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add guards (or variants) of drop-string-before-char and
;; split-string-before-char that require the char to be in the string

;; Return the method-descriptor of the method.  Example: "(II)I"
(defund extract-method-descriptor (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (drop-string-before-char method-designator-string #\())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund extract-method-name (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (mv-let (first rest)
    (split-string-before-char method-designator-string #\() ;strip the signature
    (declare (ignore rest))
    (mv-let (first rest)
      (read-string-to-last-terminator first #\.)
      (declare (ignore first))
      rest)))

(defthm method-namep-of-extract-method-name
  (jvm::method-namep (extract-method-name method-designator-string))
  :hints (("Goal" :in-theory (enable extract-method-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm class-namep-of-extract-method-class
  (implies (method-designator-stringp method-designator-string)
           (jvm::class-namep (extract-method-class method-designator-string)))
  :hints (("Goal" :in-theory (enable jvm::class-namep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund extract-package-name (method-designator-string)
  (declare (xargs :guard (method-designator-stringp method-designator-string)))
  (jvm::extract-package-name-from-class-name (extract-method-class method-designator-string)))
