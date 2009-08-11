
;;;  help.lisp                              Warren A. Hunt, Jr.

;;;  This little book is a tiny collection of things I need to define
;;;  ACL2 version of DUAL-EVAL.

(in-package "ACL2")

(deflabel help-defuns-section)

;;;  A couple of stupid macros to ease the loading of files.

(defmacro swd (dir)
  `(assign swd ,dir))

(defmacro lwd (file)
  `(ld (string-append (@ swd) ,file)))

;;;  Macros to simplify specifications.

(defmacro b-fix (x)
  (declare (xargs :guard t))
  `(if ,x t nil))

;(defmacro natp (x)
;  (declare (xargs :guard t))
;  `(and (integerp ,x) (<= 0 ,x)))

(defmacro two-symbol-listp (a b)
  (declare (xargs :guard t))
  `(and (symbol-listp ,a)
        (symbol-listp ,b)))

(defmacro consp-n+1 (x n)
  (declare (xargs :guard (natp n)))
  (if (<= n 0)
      `(consp ,x)
    (list 'and
          `(consp ,x)
          `(consp-n+1 (cdr ,x) ,(- n 1)))))

(defmacro true-listp-at-least-n+1 (x n)
  (declare (xargs :guard (natp n)))
  (list 'and
        (list 'true-listp `,x)
        `(consp-n+1 ,x ,n)))

;;;  We now give the definitions for several simple Boolean functions.
;;;  We define NAND and NOR in such a way that they can accept an
;;;  arbitrary number of inputs.

(defmacro nand (&rest args)
 `(not (and ,@args)))

(defmacro nor (&rest args)
 `(not (or ,@args)))

;;;  The atoms of the DE description language are symbols.
;;;  We define function to aid their manipulation.

(defmacro assoc-eq-value (x alist)
  `(cdr (assoc-eq ,x ,alist)))

(defun no-duplicatesp-eq (l)
  (declare (xargs :guard (symbol-listp l)))
  (cond ((endp l) t)
	((member-eq (car l) (cdr l)) nil)
	(t (no-duplicatesp-equal (cdr l)))))

(defun disjoint-eq (a b)
  (declare (xargs :guard (two-symbol-listp a b)))
  (if (endp a)
      t
    (if (member-eq (car a) b)
        nil
      (disjoint-eq (cdr a) b))))

(defun subset-eq (a b)
  (declare (xargs :guard (and (two-symbol-listp a b))))
  (if (endp a)
      t
    (and (member-eq (car a) b)
         (subset-eq (cdr a) b))))

(defun member-eq-names (names lst)
  (declare (xargs :guard (two-symbol-listp names lst)))
  (if (endp names)
      t
    (and (member-eq (car names) lst)
         (member-eq-names (cdr names) lst))))

(defun assoc-eq-values (syms alist)
  (declare (xargs :guard (and (symbol-listp syms)
                              (alistp alist))))
  (if (endp syms)
      nil
    (cons (assoc-eq-value (car syms) alist)
          (assoc-eq-values (cdr syms) alist))))

(defun delete-eq (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (alistp alist))))
  (if (atom alist)
      nil
    (if (eq name (caar alist))
        (cdr alist)
      (cons (car alist)
            (delete-eq name (cdr alist))))))

(defun delete-eq-module (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (alistp alist))))
  (if (atom alist)
      nil
    (if (eq name (caar alist))
        (cdr alist)
      (delete-eq-module name (cdr alist)))))

;;;  Some facts about pairlis$

(defthm alistp-pairlis$
  (alistp (pairlis$ symbols values)))

(defthm symbol-alistp-pairlis$
  (implies (symbol-listp symbols)
	   (symbol-alistp (pairlis$ symbols values))))

(defthm alistp-append
  (implies (and (alistp x)
		(alistp y))
	   (alistp (append x y))))

;;;  A function that sort of works like MEMBER-EQUAL.

(defun assoc-eq-rest (x alist)
  (declare (xargs :guard (if (symbolp x)
			     (alistp alist)
			   (symbol-alistp alist))))
  (cond ((endp alist) nil)
	((eq x (caar alist)) alist)
	(t (assoc-eq-rest x (cdr alist)))))

#|
(defthm assoc-eq-works-like-car-assoc-eq
  (equal (assoc-eq x alist)
	 (car (assoc-eq-rest x alist))))
|#


;;;  Identify a set of symbols for this book.

(deftheory help-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'help-defuns-section)))
