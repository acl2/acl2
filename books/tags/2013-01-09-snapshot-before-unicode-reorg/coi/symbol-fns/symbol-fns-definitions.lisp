#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; symbol-fns-definitions.lisp
;; John D. Powell
;(in-package "SYMBOL-FNS")

;;
;; This file isolates symbol-fns definitions and types. The file currently 
;; contains the following ACL2 constructs as they occur in the symbol-fns book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'acl2::string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defthm stringp-symbol-list-to-string
  (implies
   (symbol-listp list)
   (stringp (symbol-list-to-string list))))

(defun safe-witness (symbol)
  (declare (type symbol symbol))
  (if (equal (symbol-package-name symbol) (symbol-package-name 'common-lisp::mod)) 'acl2::defthm symbol))

(defthm symbolp-safe-witness
  (implies
   (symbolp symbol)
   (symbolp (safe-witness symbol))))

(in-theory (disable safe-witness))

(defthm character-listp-explode-nonnegative-integerp
  (implies
   (character-listp list)
   (character-listp (explode-nonnegative-integer number 10 list))))

(defund to-string (entry)
  (declare (type t entry))
  (cond
   ((symbolp entry) (symbol-name entry))
   ((integerp entry) 
    (if (<= 0 entry)
        (coerce (explode-nonnegative-integer entry 10 nil) 'acl2::string)
      (concatenate 'acl2::string "-" 
                   (coerce (explode-nonnegative-integer (- entry) 10 nil) 'acl2::string))))
   ((stringp entry) entry)
   (t "")))

(defthm stringp-to-string
  (stringp (to-string atom))
  :hints (("Goal" :in-theory (enable to-string))))
  
(defun list-to-string (list)
  (declare (type t list))
  (if (consp list)
      (let ((entry (car list)))
        (let ((entry (to-string entry)))
          (concatenate 'acl2::string entry (list-to-string (cdr list)))))
    ""))

(defthm stringp-list-to-string
  (stringp (list-to-string list)))

(defund make-numbered-symbol (witness symbol number)
  (declare (type (integer 0 *) number)
           (type (satisfies symbolp) witness symbol))
  (intern-in-package-of-symbol 
   (concatenate 'acl2::string 
                (symbol-name symbol)
                (coerce (explode-nonnegative-integer number 10 nil) 'acl2::string)) 
   (safe-witness witness)))

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
        (intern-in-package-of-symbol name (safe-witness witness)))
    :nil))

(defthm symbolp-map-symbol-to-package
  (symbolp (map-symbol-to-package symbol witness))
  :hints (("goal" :in-theory (enable map-symbol-to-package))))

(defun map-symbol-list-to-package (list witness)
  (declare (type symbol witness))
  (if (consp list)
      (cons (map-symbol-to-package (car list) witness)
            (map-symbol-list-to-package (cdr list) witness))
    nil))

(defthm symbol-listp-map-symbol-list-to-package
  (symbol-listp (map-symbol-list-to-package list witness))
  :rule-classes (:type-prescription :rewrite))

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
