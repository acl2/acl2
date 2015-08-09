(in-package "SYMBOL-FNS")

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'acl2::string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defthm stringp-symbol-list-to-string
  (implies
   (symbol-listp list)
   (stringp (symbol-list-to-string list))))

(defmacro join-symbols (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string (list ,@rst))
				,witness))

(defmacro prefix (&rest rst)
  (let ((base (car (last rst))))
    `(join-symbols ,base ,@rst)))

(defmacro suffix (base &rest rst)
  `(join-symbols ,base ,base ,@rst))

(defthm character-listp-explode-nonnegative-integerp
  (implies
   (character-listp list)
   (character-listp (explode-nonnegative-integer number print-base list))))

(defund make-numbered-symbol (witness symbol number)
  (declare (type (integer 0 *) number)
	   (type (satisfies symbolp) witness symbol))
  (intern-in-package-of-symbol
   (concatenate 'acl2::string
		(symbol-name symbol)
		(coerce (explode-nonnegative-integer number 10 nil) 'acl2::string))
   witness))

(defthm symbolp-make-numbered-symbol
  (implies
   (and
    (integerp number)
    (<= 0 number)
    (symbolp witness)
    (symbolp symbol))
   (symbolp (make-numbered-symbol witness symbol number)))
  :hints (("goal" :in-theory (enable make-numbered-symbol))))

(defun number-symbol-list (witness list number)
  (declare (type (integer 0 *) number)
	   (type (satisfies symbolp) witness)
	   (type (satisfies symbol-listp) list))
  (if (consp list)
      (cons (make-numbered-symbol witness (car list) number)
	    (number-symbol-list witness (cdr list) number))
    nil))

(defthm symbol-listp-number-symbol-list
  (implies
   (and
    (symbolp witness)
    (integerp number)
    (<= 0 number)
    (symbol-listp list))
   (symbol-listp (number-symbol-list witness list number))))

(defund map-symbol-to-package (symbol witness)
  (declare (type symbol witness))
  (if (symbolp symbol)
      (let ((name (symbol-name symbol)))
	(intern-in-package-of-symbol name witness))
    :nil))

(defthm symbolp-map-symbol-to-package
  (symbolp (map-symbol-to-package symbol witness))
  :hints (("goal" :in-theory (enable map-symbol-to-package))))

(defmacro enkey (symbol)
  `(map-symbol-to-package ,symbol :key))

(defun map-symbol-list-to-package (list witness)
  (declare (type symbol witness))
  (if (consp list)
      (cons (map-symbol-to-package (car list) witness)
	    (map-symbol-list-to-package (cdr list) witness))
    nil))

(defthm symbol-listp-map-symbol-list-to-package
  (symbol-listp (map-symbol-list-to-package list witness))
  :rule-classes (:type-prescription :rewrite))

(defmacro enkey-list (list)
  `(map-symbol-list-to-package ,list :key))

(defund symbol-fix (symbol)
  (declare (type t symbol))
  (if (symbolp symbol) symbol :nil))

(defthm symbolp-symbol-fix
  (symbolp (symbol-fix symbol))
  :hints (("goal" :in-theory (enable symbol-fix))))

(defthm idempotent-symbol-fix
  (implies
   (symbolp symbol)
   (equal (symbol-fix symbol) symbol))
  :hints (("goal" :in-theory (enable symbol-fix))))

(defthm symbol-listp-implies-true-listp
  (implies
   (symbol-listp list)
   (true-listp list))
  :rule-classes (:forward-chaining))
