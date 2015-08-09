(in-package "ACL2")

(defun make-sym (s suf)
; Returns the symbol s-suf.
  (declare (xargs :guard (and (symbolp s) (symbolp suf))))
  (intern-in-package-of-symbol
   (concatenate 'string
                (symbol-name s)
		"-"
                (symbol-name suf))
   s))

(defmacro defung (&rest def)
; A function definition that has a declare followed by a list of the
; form ((thm) commands), where commands can be anything that you would
; give to a defthm (look at defthm documentation), specifically it is:
;        :rule-classes rule-classes
;        :instructions instructions
;        :hints        hints
;        :otf-flg      otf-flg
;        :doc          doc-string
;
; The if test checks for documentation strings.
  (list 'progn
	(cons 'defun (append (list (first def)
				   (second def)
				   (third def))
			     (if (stringp (third def))
				 (list (fourth def)
				       (sixth def))
			       (list (fifth def)))))
	(append (list 'defthm (make-sym (car def) 'return-type))
		(if (stringp (third def))
		    (fifth def)
		  (fourth def)))))

#|
Here's an example:

(defung intersect (x y Z)
  "Intersect x and y; union the result to Z"
  (declare (xargs :guard (and (true-listp x) (true-listp y) (true-listp Z))))
  ((implies (true-listp Z) (true-listp (intersect x y Z))))
  (cond ((endp x) Z)
	((in (car x) y)
	 (intersect (cdr x) y (cons (car x) Z)))
	(t (intersect (cdr x) y Z))))

:trans1 of the above is:

(PROGN (DEFUN INTERSECT (X Y Z)
	 "Intersect x and y; union the result to Z"
	 (DECLARE (XARGS :GUARD
			 (AND (TRUE-LISTP X)
			      (TRUE-LISTP Y)
			      (TRUE-LISTP Z))))
	 (COND ((ENDP X) Z)
	       ((IN (CAR X) Y)
		(INTERSECT (CDR X) Y (CONS (CAR X) Z)))
	       (T (INTERSECT (CDR X) Y Z))))
       (DEFTHM INTERSECT-RETURN-TYPE
	 (IMPLIES (TRUE-LISTP Z)
		  (TRUE-LISTP (INTERSECT X Y Z)))))
|#
