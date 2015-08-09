;; Exercise file to accompany
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Solution for exercise 6.
;;
;; We rely on the ability to generate a new symbol with respect to a
;; given symbol list in steps 2 and 3 of the search procedure.  In
;; variable renaming, step 2, we generate a new variable.  In
;; Skolemization, step 3, we generate a Skolem function name.  Common
;; Lisp has a function gensym, but it is state dependent and therefore
;; not available in ACL2.  Define an ACL2 function that generates a
;; symbol that is not in a given list of symbols, and prove its
;; correctness.

;; Hint: ACL2 defines functions "coerce" and
;; "intern-in-package-of-symbol."  See ACL2 documentation for more
;; information.

(in-package "ACL2")

;; We assume that there is a list of symbols whose names are
;; "l...ld...d" where l=letter, d=digit.  The string of d's in the
;; symbol name is called an index.  If there is something other than
;; a digit to the right of the leftmost digit in the symbol name,
;; that character is ignored.   For example,
;;
;;        index of v12x3 = 123.
;;
;; How this works:  We used several functions suggested by
;; Matt Kaufmann's functions.  If there is a list of characters that
;; represents an integer the functions generate the list of characters
;; that represents the successor of that integer.
;;
;; Given a list of symbols, we compute the index that represents the
;; largest integer.  Gen-sym produces a symbol whose index is a
;; successor to that integer.

(defun next-int-char (char)
  (declare (xargs :guard t))
  (case char
      (#\1 (mv #\2 nil))
      (#\2 (mv #\3 nil))
      (#\3 (mv #\4 nil))
      (#\4 (mv #\5 nil))
      (#\5 (mv #\6 nil))
      (#\6 (mv #\7 nil))
      (#\7 (mv #\8 nil))
      (#\8 (mv #\9 nil))
      (#\9 (mv #\0 t))
      (otherwise ;; treat as #\0
       (mv #\1 nil))))

(defun next-int-char-list (chars)
  (declare (xargs :guard t))
  (if (atom chars)
      (mv nil t)
    (mv-let (next-chars carryp1)
            (next-int-char-list (cdr chars))
            (if carryp1
                (mv-let (c carryp2)
                        (next-int-char (car chars))
                        (mv (cons c next-chars) carryp2))
              (mv (cons (car chars) next-chars) nil)))))

(defun int-char-listp (chars)
  (declare (xargs :guard t))
  (if (atom chars)
      (null chars)
    (and (member (car chars)
                 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
         (int-char-listp (cdr chars)))))

(defthm next-char-list-gives-charlist
  (implies (character-listp x)
	   (character-listp (car (next-int-char-list x)))))

(defun charlist< (i1 i2)
  (declare (xargs :guard (and (character-listp i1) (character-listp i2))))
  (cond ((atom i2) nil)
	((atom i1) t)
	((> (len i1) (len i2)) nil)
	((< (len i1) (len i2)) t)
	(t (cond ((char< (car i1) (car i2)) t)
		 ((char> (car i1) (car i2)) nil)
		 (t (charlist< (cdr i1) (cdr i2)))))))

(defun next-int-char-list-actual (chars)
  (declare (xargs :guard t))
  (mv-let (next carryp)
          (next-int-char-list chars)
          (if carryp
              (cons #\1 next)
            next)))

(defthm carry-char-list
  (implies (character-listp x)
	   (character-listp (cons #\1 x))))

(defthm next-char-list-actual-gives-charlist
  (implies (character-listp x)
	   (character-listp (next-int-char-list-actual x))))

(defthm carry-int-char-list
  (implies (int-char-listp x)
	   (int-char-listp (cons #\1 x))))

(defthm next-char-list-len
  (equal (len (car (next-int-char-list x)))
	 (len x)))

(defthm next-char-list-actual-gives-greater-list
  (implies (int-char-listp x)
	   (charlist< x (next-int-char-list-actual x)))
  :otf-flg t)

(defun index (l)
  (declare (xargs :guard (character-listp l)))
  (cond ((atom l) nil)
	((member (car l) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
	 (cons (car l) (index (cdr l))))
	(t (index (cdr l)))))

(defthm index-gives-int-char-list
  (int-char-listp (index l)))

(defthm index-gives-charlist
  (character-listp (index l)))

(defun charlist-max (i1 i2)
  (declare (xargs :guard (and (character-listp i1) (character-listp i2))))
  (if (charlist< i1 i2) i2 i1))

(defun max-index (l)
  (declare (xargs :guard (symbol-listp l)))
  (if (atom l)
      nil
      (charlist-max (index (coerce (symbol-name (car l)) 'list))
		    (max-index (cdr l)))))

(local (defthm greater-index-symbol-not-in-list ;; does 3 inductions
	 (implies (and (symbolp sym)
		       (charlist< (max-index l)
				  (index (coerce (symbol-name sym) 'list))))
		  (not (member-equal sym l)))))

(defun gen-sym (sym l)
  (declare (xargs :guard (and (symbolp sym)
			      (character-listp l))))
  (intern-in-package-of-symbol
   (coerce (append (coerce (symbol-name sym) 'list)
		   (next-int-char-list-actual l)) 'string)
   sym))

(defthm consp-index-append
  (implies (and (character-listp x)
		(character-listp y))
	   (equal (index (append x y))
		  (append (index x) (index y)))))

(defthm charlist<-append
  (implies (and (character-listp prefix)
		(character-listp y)
		(charlist< x y))
	   (charlist< x (append prefix y)))
  :hints (("Goal"
	   :do-not generalize
	   ;; When we went from ACL2-v2.3 to 2.4, we had to include the
	   ;; following expand hints.  On the plus side, this reduced
	   ;; the number of inductions from 7 to 1.
	   :expand ((charlist< x (cons (car prefix) (append (cdr prefix) y)))
		    (charlist< x (append prefix2 y))
		    )
	   )))

(defthm intchar-list-next-index
  (implies (int-char-listp l)
	   (equal (index (next-int-char-list-actual l))
		  (next-int-char-list-actual l))))

(defthm max-index-lessthan-gensym-index
  (implies (symbolp sym)
	   (charlist<
	    (max-index l)
	    (index (coerce (symbol-name (gen-sym sym (max-index l))) 'list))))
  :hints (("Goal" :do-not generalize
	   :in-theory (disable next-int-char-list-actual))))

;; top-level gensym: make a symbol (with a prefix sym)
;; that does not occur in the given list l

(defun gen-symbol (sym l)
  (declare (xargs :guard (and (symbolp sym)
			      (symbol-listp l))))
  (gen-sym sym (max-index l)))

;; Main theorem, gen-symbol really makes a NEW symbol

(defthm new-symbol-not-in-list
  (implies (symbolp sym)
	   (not (member-equal (gen-symbol sym l) l)))
  :hints (("Goal" :in-theory (disable gen-sym))))

(in-theory (disable gen-symbol))

;; a few examples
;; (gen-symbol 'v nil) ;; => v1
;; (gen-symbol 'v2- '(x1 v23 y1 x10)) ;; => v2-24
;; (gen-symbol 'v '(x12 v99)) ;; => v100
;; (gen-symbol 'v2 '(x1x3 x10)) ;; => v214









