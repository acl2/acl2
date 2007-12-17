(in-package "ACL2")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

; ---------------------------------------------------------------------------
; Exercise 11.1

; The following is indeed admissible.

(defun f (x)
  (if (endp x)
      0
    (1+ (f (cdr x)))))

; The following is also admissible.  Since the cdr of an atom is nil in the
; ACL2 logic, a non-nil atom will lead to the call (f nil) and hence will
; require more more step for termination than will the call (f nil).  The
; indicated measure accounts for this idea.

(defun f1 (x)
  (declare (xargs :measure
                  (if (true-listp x) (acl2-count x) (1+ (acl2-count x)))))
  (if (null x)
      0
    (1+ (f1 (cdr x)))))

; ---------------------------------------------------------------------------
; Exercise 11.2

(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun rev (x)
  (if (endp x)
      nil
    (app (rev (cdr x)) (list (car x)))))

(defun flatten (x)
  (cond ((atom x) (list x))
	(t (app (flatten (car x))
		(flatten (cdr x))))))

(defun swap-tree (x)
  (if (atom x)
      x
    (cons (swap-tree (cdr x))
	  (swap-tree (car x)))))

(defthm flatten-swap-tree
  (equal (flatten (swap-tree x))
         (rev (flatten x))))

(defun flat (x)
  (declare (xargs :measure
                  (cons (1+ (acl2-count x))
                        (acl2-count (car x)))))
  (cond ((atom x) (list x))
        ((atom (car x)) (cons (car x) (flat (cdr x))))
        (t (flat (cons (caar x)
                       (cons (cdar x) (cdr x)))))))

(defthm flat-flatten
  (equal (flat x)
         (flatten x)))

; ---------------------------------------------------------------------------
; Exercise 11.3

; To prove reverse-reverse, let us first take a look at the functions we are
; dealing with.

#|
ACL2 !>:pe append
      -4090  (DEFMACRO APPEND (X Y &REST RST)
                       (XXXJOIN 'BINARY-APPEND
                                (CONS X (CONS Y RST))))
ACL2 !>:pe binary-append
 V     -391  (DEFUN BINARY-APPEND (X Y)
                    (DECLARE (XARGS :GUARD (TRUE-LISTP X)))
                    (COND ((ENDP X) Y)
                          (T (CONS (CAR X)
                                   (BINARY-APPEND (CDR X) Y)))))
ACL2 !>:pe revappend
 V     -326  (DEFUN REVAPPEND (X Y)
                    (DECLARE (XARGS :GUARD (TRUE-LISTP X)))
                    (IF (ENDP X)
                        Y (REVAPPEND (CDR X) (CONS (CAR X) Y))))
ACL2 !>:pe reverse
 V     -324  (DEFUN REVERSE (X)
                    (DECLARE (XARGS :GUARD (OR (TRUE-LISTP X) (STRINGP X))))
                    (COND ((STRINGP X)
                           (COERCE (REVAPPEND (COERCE X 'LIST) NIL)
                                   'STRING))
                          (T (REVAPPEND X NIL))))
ACL2 !>
|#

; If we try to prove reverse-reverse directly, we obtain the following as the
; first simplification checkpoint:

#|
Subgoal *1/3''
(IMPLIES (AND (CONSP X)
              (EQUAL (REVAPPEND (REVAPPEND (CDR X) NIL) NIL)
                     (CDR X))
              (TRUE-LISTP (CDR X)))
         (EQUAL (REVAPPEND (REVAPPEND (CDR X) (LIST (CAR X)))
                           NIL)
                X))
|#

; Clearly we need to prove some lemma about the application of revappend to
; revappend.  We want the lemma to be sufficiently general so that it has a
; chance of being proved by induction.

(defthm revappend-revappend
  (equal (revappend (revappend x y) z)
         (revappend y (append x z))))

; The following now goes through automatically.

(defthm reverse-reverse
  (implies (true-listp x)
           (equal (reverse (reverse x))
                  x)))

; ---------------------------------------------------------------------------
; Exercise 11.4

; Since (reverse x) is defined in terms of revappend in ACL2 (see above), then
; in order to prove that (rev x) is equal to (reverse x), we will need to prove
; an analogous result for revappend.

(defthm revappend-is-rev
  (equal (revappend x y)
         (app (rev x) y)))

(defthm rev-reverse
  (implies (not (stringp x))
           (equal (rev x)
                  (reverse x))))
