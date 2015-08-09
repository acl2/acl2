;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

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

(defung update-valuation (v s val)
"gives val[v <- s] if v is in val, otherwise gives val U [v <- s]"
  (declare (xargs :guard (alistp val)))
  ((implies (alistp val) (alistp (update-valuation v s val))))
  (if (endp val)
      (list (cons v s))
    (if (equal v (caar val))
	(acons v s (cdr val))
      (cons (car val) (update-valuation v s (cdr val))))))

(defun value-of (x alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal x alist)))

(defthm update-val
  (equal (value-of n (update-valuation m z x))
	 (if (equal n m)
	     z
	   (value-of n x))))

(defthm update-valuation-update-valuation-same
  (equal (update-valuation i v1 (update-valuation i v2 l))
	 (update-valuation i v1 l)))

