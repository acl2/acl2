(in-package "PACO")

; ---------------------------------------------------------------------------
; Section:  Computing the Types of Terms

(defun def-basic-type-sets1 (lst i)
  (cond ((endp lst) nil)
        (t (cons (list 'defconst (car lst) (list 'the-type-set (expt 2 i)))
                 (def-basic-type-sets1 (cdr lst) (+ i 1))))))

(defmacro def-basic-type-sets (&rest lst)
  (let ((n (length lst)))
    `(progn
       (defconst *actual-primitive-types* ',lst)
       (defconst *min-type-set* (- (expt 2 ,n)))
       (defconst *max-type-set* (- (expt 2 ,n) 1))
       (defmacro the-type-set (x)
         `(the (integer ,*min-type-set* ,*max-type-set*) ,x))
       ,@(def-basic-type-sets1 lst 0))))

(defun list-of-the-type-set (x)
  (cond ((consp x)
         (cons (list 'the-type-set (car x))
               (list-of-the-type-set (cdr x))))
        (t nil)))

(defmacro ts= (a b)
  (list '= (list 'the-type-set a) (list 'the-type-set b)))

(defmacro ts-complement (x)
  (list 'the-type-set (list 'lognot (list 'the-type-set x))))

(defmacro ts-complementp (x)
  (list 'minusp x))

(defun ts-union-fn (x)
  (list 'the-type-set
        (cond ((null x) '*ts-empty*)
              ((null (cdr x)) (car x))
              (t (xxxjoin 'logior
                          (list-of-the-type-set x))))))

(defmacro ts-union (&rest x)
  (declare (xargs :guard (true-listp x)))
  (ts-union-fn x))

(defmacro ts-intersection (&rest x)
  (list 'the-type-set
        (cons 'logand (list-of-the-type-set x))))

(defmacro ts-intersectp (&rest x)
  (list 'not (list 'ts= (cons 'ts-intersection x) '*ts-empty*)))

(defmacro ts-subsetp (ts1 ts2)
  (list 'let (list (list 'ts1 ts1)
                   (list 'ts2 ts2))
        '(ts= (ts-intersection ts1 ts2) ts1)))

(defun ts-builder-macro1 (x case-lst seen)
  (cond ((endp case-lst) nil)
        ((or (eq (caar case-lst) t)
             (eq (caar case-lst) 'otherwise))
         (sublis (list (cons 'x x)
                       (cons 'seen seen)
                       (cons 'ts2 (cadr (car case-lst))))
                 '((cond ((ts-intersectp x (ts-complement (ts-union . seen)))
                          ts2)
                         (t *ts-empty*)))))
        (t (cons (sublis (list (cons 'x x)
                               (cons 'ts1 (caar case-lst))
                               (cons 'ts2 (cadr (car case-lst))))
                         '(cond ((ts-intersectp x ts1) ts2)
                                (t *ts-empty*)))
                 (ts-builder-macro1 x (cdr case-lst) (cons (caar case-lst)
                                                           seen))))))

(defun ts-builder-macro (x case-lst)
  (cons 'ts-union
        (ts-builder-macro1 x case-lst nil)))

(defmacro ts-builder (&rest args)
  (ts-builder-macro (car args) (cdr args)))

(def-basic-type-sets
  *ts-zero*
  *ts-one*
  *ts-integer>1*
  *ts-positive-ratio*
  *ts-negative-integer*
  *ts-negative-ratio*
  *ts-complex-rational*
  *ts-nil*
  *ts-t*
  *ts-non-t-non-nil-symbol*
  *ts-proper-cons*
  *ts-improper-cons*
  *ts-string*
  *ts-character*)

(defconst *ts-positive-integer* (ts-union *ts-one*
                                          *ts-integer>1*))

(defconst *ts-non-negative-integer* (ts-union *ts-zero*
                                              *ts-positive-integer*))

(defconst *ts-non-positive-integer* (ts-union *ts-zero*
                                              *ts-negative-integer*))

(defconst *ts-integer* (ts-union *ts-positive-integer*
                                 *ts-zero*
                                 *ts-negative-integer*))

(defconst *ts-rational* (ts-union *ts-integer*
                                  *ts-positive-ratio*
                                  *ts-negative-ratio*))

(defconst *ts-acl2-number* (ts-union *ts-rational*
                                     *ts-complex-rational*))

(defconst *ts-rational-acl2-number* (ts-union *ts-rational*
                                              *ts-complex-rational*))

(defconst *ts-negative-rational* (ts-union *ts-negative-integer*
                                           *ts-negative-ratio*))

(defconst *ts-positive-rational* (ts-union *ts-positive-integer*
                                           *ts-positive-ratio*))

(defconst *ts-non-positive-rational* (ts-union *ts-zero*
                                               *ts-negative-rational*))

(defconst *ts-non-negative-rational* (ts-union *ts-zero*
                                               *ts-positive-rational*))

(defconst *ts-ratio* (ts-union *ts-positive-ratio*
                               *ts-negative-ratio*))

(defconst *ts-cons* (ts-union *ts-proper-cons*
                              *ts-improper-cons*))

(defconst *ts-boolean* (ts-union *ts-nil* *ts-t*))

(defconst *ts-true-list* (ts-union *ts-nil* *ts-proper-cons*))

(defconst *ts-non-nil* (ts-complement *ts-nil*))

(defconst *ts-symbol* (ts-union *ts-nil*
                                *ts-t*
                                *ts-non-t-non-nil-symbol*))

(defconst *ts-true-list-or-string* (ts-union *ts-true-list* *ts-string*))

(defconst *ts-empty* 0)

(defconst *ts-unknown* -1)

(defun type-set-binary-+-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero* ts2)
              (*ts-one*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-integer>1*)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-non-positive-integer*)
                           (*ts-positive-ratio* *ts-positive-ratio*)
                           (*ts-negative-ratio* *ts-ratio*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-integer>1*)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-integer*)
                           (*ts-positive-ratio* *ts-positive-ratio*)
                           (*ts-negative-ratio* *ts-ratio*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-non-positive-integer*)
                           (*ts-integer>1* *ts-integer*)
                           (*ts-negative-integer* *ts-negative-integer*)
                           (*ts-positive-ratio* *ts-ratio*)
                           (*ts-negative-ratio* *ts-negative-ratio*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-positive-ratio*)
                           (*ts-integer>1* *ts-positive-ratio*)
                           (*ts-negative-integer* *ts-ratio*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-ratio*)
                           (*ts-integer>1* *ts-ratio*)
                           (*ts-negative-integer* *ts-negative-ratio*)
                           (*ts-positive-ratio* *ts-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-complex-rational*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-complex-rational*)
                           (*ts-integer>1* *ts-complex-rational*)
                           (*ts-negative-integer* *ts-complex-rational*)
                           (*ts-positive-ratio* *ts-complex-rational*)
                           (*ts-negative-ratio* *ts-complex-rational*)
                           (*ts-complex-rational* *ts-rational-acl2-number*)
                           ))
              ))

(defun type-set-binary-*-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero* *ts-zero*)
              (*ts-one* ts2)
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-negative-integer*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-negative-integer*)
                           (*ts-negative-integer* *ts-positive-integer*)
                           (*ts-positive-ratio* *ts-negative-rational*)
                           (*ts-negative-ratio* *ts-positive-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-positive-rational*)
                           (*ts-negative-integer* *ts-negative-rational*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-negative-rational*)
                           (*ts-negative-integer* *ts-positive-rational*)
                           (*ts-positive-ratio* *ts-negative-rational*)
                           (*ts-negative-ratio* *ts-positive-rational*)
                           (*ts-complex-rational* *ts-complex-rational*)
                           ))
              (*ts-complex-rational*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-complex-rational*)
                           (*ts-negative-integer* *ts-complex-rational*)
                           (*ts-positive-ratio* *ts-complex-rational*)
                           (*ts-negative-ratio* *ts-complex-rational*)
                           (*ts-complex-rational*
                            (ts-intersection *ts-rational-acl2-number*
                                              (ts-complement *ts-zero*)))
                           ))
              ))

(defun type-set-<-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-nil*)
                           ))
              (*ts-one*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-nil*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)
                           ))
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-nil*)
                           (*ts-integer>1* *ts-boolean*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)
                           ))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* *ts-t*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-boolean*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-boolean*)
                           ))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-boolean*)
                           (*ts-integer>1* *ts-boolean*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)
                           ))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-t*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-boolean*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-boolean*)
                           ))

              ))

(defun numeric-type-set (ts)

; This coerces ts into the type *ts-acl2-number*.  That is, if ts contains
; nonnumeric bits then those bits are shut off and *ts-zero* is turned on.
; Another way to look at it is that if term has type ts then (fix term) has
; type (numeric-type-set ts).

  (let ((numeric-subtype
         (ts-intersection ts *ts-acl2-number*)))
    (if (ts= numeric-subtype ts)
        ts
      (ts-union numeric-subtype *ts-zero*))))

(defun rational-type-set (ts)

; This function is like numeric-type-set, but coerces ts to the
; rationals.

  (let ((rational-subtype
         (ts-intersection ts *ts-rational*)))
    (if (ts= rational-subtype ts)
        ts
      (ts-union rational-subtype *ts-zero*))))

; We start with probably the most complicated primitive type set
; function, that for binary-+.

(defun type-set-binary-+ (term ts1 ts2)

; Because 1- (i.e., SUB1) is so common and often is applied to
; strictly positive integers, it is useful to know that, in such
; cases, the result is a non-negative integer.  We therefore test for
; (+ x -1) and its commuted version (+ -1 x).  To be predictable, we
; also look for (+ x +1), and its commuted version, when x is strictly
; negative.  We specially arrange for the answer type-set to be empty
; if either of the input type-sets is empty.  This occurs when we are
; guessing type sets.  The idea is that some other branch ought to
; give us a nonempty type-set before this one can meaningfully
; contribute to the answer.  Before we added the special processing of
; +1 and -1 we did not have to check for the empty case because the
; array referenced by aref2 has the property that if either type-set
; is empty the result is empty.

  (let ((arg1 (fargn term 1))
        (arg2 (fargn term 2)))
    (cond ((or (ts= ts1 *ts-empty*)
               (ts= ts2 *ts-empty*))
           *ts-empty*)
          ((and (equal arg2 ''-1)
                (ts-subsetp ts1 *ts-positive-integer*))
           *ts-non-negative-integer*)
          ((and (equal arg1 ''-1)
                (ts-subsetp ts2 *ts-positive-integer*))
           *ts-non-negative-integer*)
          (t (type-set-binary-+-alist-entry
              (numeric-type-set ts1)
              (numeric-type-set ts2))))))

(defun type-set-binary-* (ts1 ts2)
  (cond ((or (ts= ts1 *ts-empty*)
             (ts= ts2 *ts-empty*))
         *ts-empty*)
        (t (type-set-binary-*-alist-entry
            (numeric-type-set ts1)
            (numeric-type-set ts2)))))

(defun type-set-not (ts)
  (cond
   ((ts= ts *ts-nil*)
    *ts-t*)
   ((ts-subsetp *ts-nil* ts)
    *ts-boolean*)
   (t *ts-nil*)))

(defun type-set-< (arg1 arg2 ts1 ts2)

  (declare (xargs :measure (+ (acl2-count arg1)
                              (acl2-count arg2))))

; This function is not cut from the standard mold because instead of
; taking term it takes the two args.  This allows us easily to
; implement certain transformations on inequalities: When x is an
; integer,

; (<  x 1) is (not (< 0 x)) and
; (< -1 x) is (not (< x 0)).

; Warning: It is important to assume-true-false that type-set-< make
; these transformations.  See the comments about type-set-< in
; assume-true-false.

  (let* ((nts1 (numeric-type-set ts1))
         (nts2 (numeric-type-set ts2)))
    (cond ((and (equal arg1 *-1*)

; Actually we don't have to add 0 back in, as done by numeric-type-set, before
; making the following test.  But let's keep things simple.

                (ts-subsetp nts1 *ts-integer*))
           (type-set-not
            (type-set-< arg2 *0* ts2 *ts-zero*)))
          ((or (ts-intersectp ts1 *ts-complex-rational*)
               (ts-intersectp ts2 *ts-complex-rational*))
           *ts-boolean*)
          (t (type-set-<-alist-entry nts1 nts2)))))

(defun type-set-unary-- (ts)
  (let ((ts1 (numeric-type-set ts)))
    (cond
     ((ts= ts1 *ts-acl2-number*)
      *ts-acl2-number*)
     (t
      (ts-builder ts1
                  (*ts-zero* *ts-zero*)
                  (*ts-one* *ts-negative-integer*)
                  (*ts-integer>1* *ts-negative-integer*)
                  (*ts-positive-ratio* *ts-negative-ratio*)
                  (*ts-negative-integer* *ts-positive-integer*)
                  (*ts-negative-ratio* *ts-positive-ratio*)
                  (*ts-complex-rational* *ts-complex-rational*))))))

(defun type-set-unary-/ (ts)
  (let* ((ts1 (numeric-type-set ts)))
    (ts-builder ts1
                (*ts-zero* *ts-zero*)
                (*ts-one* *ts-one*)
                (*ts-integer>1* *ts-positive-ratio*)
                (*ts-positive-ratio* *ts-positive-rational*)
                (*ts-negative-rational* *ts-negative-rational*)
                (*ts-complex-rational* *ts-complex-rational*))))

(defun type-set-numerator (ts)
  (let* ((ts1 (rational-type-set ts)))
    (ts-builder ts1
                (*ts-zero* *ts-zero*)
                (*ts-one* *ts-one*)
                (*ts-integer>1* *ts-integer>1*)
                (*ts-positive-ratio* *ts-positive-integer*)
                (*ts-negative-rational* *ts-negative-integer*))))

(defun type-set-denominator (ts)
  (let* ((ts1 (rational-type-set ts)))
    (ts-builder ts1
                (*ts-integer* *ts-one*)
                (*ts-ratio* *ts-integer>1*))))

(defun type-set-realpart (ts)
  (cond ((ts-intersectp ts *ts-complex-rational*)
         *ts-rational*)
        (t (numeric-type-set ts))))

(defun type-set-imagpart (ts)
  (cond ((ts-subsetp ts *ts-complex-rational*)
         (ts-union *ts-positive-rational*
                   *ts-negative-rational*))
        ((ts-intersectp ts *ts-complex-rational*)
         *ts-rational*)
        (t *ts-zero*)))

(defun type-set-complex (ts1 ts2)
  (let ((ts1 (rational-type-set ts1))
        (ts2 (rational-type-set ts2)))
    (cond ((ts= ts2 *ts-zero*)
           ts1)
          ((ts= (ts-intersection ts2 *ts-zero*)
                *ts-empty*)
           *ts-complex-rational*)
          ((ts= ts1 *ts-rational*)
           *ts-acl2-number*)
          (t (ts-union ts1 *ts-complex-rational*)))))

; Essay on the Recognizer-Alist and Recognizer-Tuples

; The recognizer-alist is stored as a global variable in the world w
; and accessed via

; (global-val 'recognizer-alist w).

; The recognizer alist contains records of the following form:

(defrec recognizer-tuple
  (nume (fn . true-ts) . (false-ts . strongp)))

; The initial value of the recognizer alist is shown after we discuss the
; meaning of these records.

; In a recognizer-tuple, fn is the name of some Boolean-valued
; function of one argument.  True-ts and and false-ts are type sets.
; If such a record is on the recognizer-alist then it is the case that
; (fn x) implies that the type set of x is a subset of true-ts and
; (not (fn x)) implies that the type set of x is a subset of false-ts.
; Furthermore, if strongp is t, then true-ts is the complement of
; false-ts; i.e., (fn x) recognizes exactly the subset identified by
; true-ts.

; For example, if we prove that

; (BOOLEANP X) -> (OR (EQUAL X T) (EQUAL X NIL))

; then we can add the following tuple

; (make recognizer-tuple
;       :nume 123
;       :fn BOOLEANP
;       :true-ts *ts-boolean*
;       :false-ts *ts-unknown*
;       :strongp nil)

; to the list.  Observe that the false-ts for this pair does not tell us
; much.  But if we proved the above AND

; (NOT (BOOLEANP X)) -> (NOT (OR (EQUAL X T) (EQUAL X NIL)))

; we could add the tuple:

; (make recognizer-tuple
;       :nume 123
;       :fn BOOLEANP
;       :true-ts *ts-boolean*
;       :false-ts (ts-complement *ts-boolean*)
;       :strongp t)

; And we would know as much about BOOLEANP as we know about integerp.

; Consider the function PRIMEP.  It implies its argument is a positive
; integer.  Its negation tells us nothing about the type of its argument.

; (make recognizer-tuple
;       :nume 123
;       :fn PRIMEP
;       :true-ts *ts-positive-integer*
;       :false-ts *ts-unknown*
;       :strongp nil)

; Suppose now x is a term whose type set we know.  What is the type
; set of (PRIMEP x)?  If the type set for x includes the positive
; integer bit, the type set for (PRIMEP x) may include *ts-t* so we
; will throw that in.  If the type set for x includes any of
; *ts-unknown*'s bits (of course it does) we will throw in *ts-nil*.
; The interesting thing about this is that if the type set of x does
; not include the positive integers, we'll know (PRIME x) is nil.

; If we assume (PRIME x) true, we will restrict the type of x to the
; positive integers.  If we assume (PRIME x) false, we won't restrict
; x at all.

; Consider the function RATTREEP that recognizes cons-trees of
; rational numbers.  We can prove that (RATTREEP x) implies the type
; set of x is in *ts-cons* union *ts-rational*.  We can prove that
; (NOT (RATTREEP x)) implies that the type set of x is not
; *ts-rational*.  That means the false-ts for RATTREEP is the
; complement of the rationals.  If we were asked to get the type set
; of (RATTREEP x) where x is rational, we'd throw in a *ts-t* because
; the type of x intersects the true-ts and we'd not throw in anything
; else (because the type of x does not interesect the false ts).  If
; we were asked to assume (RATTREEP x) then on the true branch x's
; type would be interesected with the conses and the rationals.  On
; the false branch, the rationals would be deleted.

(defun most-recent-enabled-recog-tuple (fn alist ens)

; This function finds the first recognizer-tuple on alist whose :fn is
; fn.

  (cond ((endp alist) nil)
        ((and (eq fn (access recognizer-tuple (car alist) :fn))
              (enabled-numep (access recognizer-tuple (car alist) :nume)
                             ens))
         (car alist))
        (t (most-recent-enabled-recog-tuple fn (cdr alist) ens))))

(defun type-set-recognizer (recog-tuple arg-ts)

; Recog-tuple is a recognizer-tuple.  Then we know that (fn x) implies
; that the type set of x, arg-ts, is a subset of true-ts.
; Furthermore, we know that ~(fn x) implies that arg-ts is a subset of
; false-ts.  In addition, we know that fn is a Boolean valued fn.

; This function is supposed to determine the type set of (fn x) where
; arg-ts is the type set of x.  Observe that if arg-ts intersects with
; true-ts then (fn x) might be true, so we should throw in *ts-t*.
; Conversely, if arg-ts does not intersect with true-ts then (fn x)
; cannot possibly be true.  Exactly analogous statements can be made
; about false-ts.

; We return the type set of (fn x).

  (ts-builder
   arg-ts
   ((access recognizer-tuple recog-tuple :true-ts) *ts-t*)
   ((access recognizer-tuple recog-tuple :false-ts) *ts-nil*)))

(defun type-set-car (ts)
  (cond ((ts-intersectp ts *ts-cons*) *ts-unknown*)
        (t *ts-nil*)))

(defun type-set-cdr (ts)
  (ts-builder ts
              (*ts-proper-cons* *ts-true-list*)
              (*ts-improper-cons* (ts-complement *ts-true-list*))
              (otherwise *ts-nil*)))

(defun type-set-coerce (term ts1 ts2)

  (cond ((equal (fargn term 2) ''list)

; If the first argument is of type *ts-string* then the result could
; be either nil or a proper cons.  But if the first argument isn't
; possibly a string, the result is NIL.

         (cond ((ts-intersectp *ts-string* ts1)
                *ts-true-list*)
               (t *ts-nil*)))
        ((quotep (fargn term 2))
         *ts-string*)
        ((not (ts-intersectp *ts-non-t-non-nil-symbol* ts2))
; Observe that the first argument doesn't matter here.
         *ts-string*)
        (t (ts-union *ts-true-list* *ts-string*))))

(defun type-set-intern-in-package-of-symbol (ts1 ts2)
  (cond ((not (ts-intersectp ts1 *ts-string*))
         *ts-nil*)
        ((not (ts-intersectp ts2 *ts-symbol*))
         *ts-nil*)
        (t *ts-symbol*)))

(defun type-set-length (ts)
  (ts-builder ts
              (*ts-string* *ts-non-negative-integer*)
              (*ts-cons* *ts-positive-integer*)
              (otherwise *ts-zero*)))

(defun type-set-cons (ts2)

; Ts2 is the type set of the second argument of the cons.

  (ts-builder ts2
              (*ts-true-list* *ts-proper-cons*)
              (otherwise *ts-improper-cons*)))

(defconst *singleton-type-sets*
  (list *ts-t* *ts-nil* *ts-zero*))

(defun type-set-equal (ts1 ts2)
  (cond ((member ts1 *singleton-type-sets*)
         (cond ((ts= ts1 ts2) *ts-t*)
               ((ts-intersectp ts1 ts2)
                *ts-boolean*)
               (t *ts-nil*)))
        ((ts-intersectp ts1 ts2)
         *ts-boolean*)
        (t *ts-nil*)))

(defun type-set-quote (evg)
  (cond ((atom evg)
         (cond ((rationalp evg)
                (cond ((integerp evg)
                       (cond ((int= evg 0) *ts-zero*)
                             ((int= evg 1) *ts-one*)
                             ((> evg 0) *ts-integer>1*)
                             (t *ts-negative-integer*)))
                      ((> evg 0) *ts-positive-ratio*)
                      (t *ts-negative-ratio*)))
               ((complex-rationalp evg)
                *ts-complex-rational*)
               ((symbolp evg)
                (cond ((eq evg t) *ts-t*)
                      ((eq evg nil) *ts-nil*)
                      (t *ts-non-t-non-nil-symbol*)))
               ((stringp evg) *ts-string*)
               (t *ts-character*)))
        ((true-listp evg)
         *ts-proper-cons*)
        (t *ts-improper-cons*)))

(defun type-set-char-code (ts)

; (char-code x) is always a non-negative integer.  If x is not a
; characterp, then its code is 0.  If x is a character, its code
; might be 0 or positive.

  (cond ((not (ts-intersectp ts *ts-character*))
         *ts-zero*)
        (t *ts-non-negative-integer*)))

; Type Prescriptions

; A type-prescription is a structure, below, that describes how to
; compute the type of a term.  They are stored on the property list of
; the top function symbol of the term, under the property
; 'type-prescriptions.  Unlike Nqthm's "type-prescription-lst" ANY
; enabled type-prescription in 'type-prescriptions may contribute to
; the type-set of the associated function symbol.

(defrec type-prescription
  (nume (basic-ts . term) . (hyps . vars)))

; Term is a term, hyps is a list of terms, basic-ts is a type-set, and vars is
; a list of variables that occur in term.  Let term' be some instance of term
; under the substitution sigma.  Then, provided the sigma instance of hyps is
; true, the type-set of term' is the union of basic-ts with the type-sets of
; the sigma images of the vars.

; For example, for APP we might have the type-prescription:

; (make type-prescription
;       :nume 123
;       :term (app x y)
;       :hyps ((true-listp x))
;       :basic-ts *ts-cons*
;       :vars '(y))

; The above example corresponds to what we'd get from the lemma:
; (implies (true-listp x)
;          (or (consp (app x y))
;              (equal (app x y) y)))

; When type-set uses :TYPE-PRESCRIPTION rules it will intersect all
; the known type-sets for term.

(defconst *expandable-boot-strap-non-rec-fns*
  '(not
    implies eq atom eql = /= null endp zerop
    synp
    plusp minusp listp prog2$ force case-split))

; Warning: All functions listed above must be defun'd non-recursively
; in axioms.lisp!  In addition, all of the guards involved in the
; guarded bodies of the functions must be satisfied.  In particular,
; we assume that the bodies of these functions could pass
; verify-guards, and in fact that boot-strapping sets their
; 'unnormalized-body properties (see distribute-first-if).
; One "benefit" of being on this list is that type-set expands the
; function inline.  However, for best results, any function used in
; the guard of a function on this list ought to be well understood by
; type-set.  For example, eql is on the list.  The guard of eql
; involves eqlablep.  For best results, eqlablep ought to be well
; understood by type-set, which, in that particular case can be
; arranged by making it a compound recognizer.

; There has been some thought about whether we should put IFF on this
; list.  We have decided not, because type-set knows a lot about it by
; virtue of its being an equivalence relation.  But this position has
; never been seriously scrutinized.

; In a break with nqthm, we have decided to let type-set expand some
; function applications to get better type-sets for them.  The
; functions in question are those listed above.

; In an even more pervasive break, we have decided to make type-set
; keep track of the dependencies between literals of the goal clause
; and the type-sets computed.  The ttree argument to type-set below is
; a running accumulator that is returned as the second value of
; type-set.  Among the tags in the ttree are 'pt tags.  The value of
; the tag is a "parent tree" indicating the set of literals of the
; current-clause upon which the type deduction depends.  See the Essay
; on Parent Trees.  The type-alist in general contains entries of the
; form (term ts . ttree), where ttree is the tag tree encoding all of
; the 'PTs upon which depend the assertion that term has type-set ts.

(defun mv-atf (not-flg mbt mbf tta fta)

; Every exit of assume-true-false is via this function.  See assume-
; true-false for details.

  (if not-flg
      (mv mbf mbt fta tta)
      (mv mbt mbf tta fta)))

(defun non-cons-cdr (term)
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((eq (ffn-symb term) 'cons)
         (non-cons-cdr (fargn term 2)))
        (t term)))

(defun extend-type-alist (term ts type-alist)

; This function extends type-alist, essentially by adding the entry
; (term . ts).  However, this function preserves two important
; invariants on type-alists: no term is bound to *ts-unknown* and no
; constant is ever bound.

  (cond
   ((ts= ts *ts-unknown*) type-alist)
   ((variablep term)
    (cons (cons term ts) type-alist))
   ((fquotep term) type-alist)
   (t (cons (cons term ts) type-alist))))

(defun zip-variable-type-alist (var-lst ts-lst)
  (cond ((endp var-lst) nil)
        (t (extend-type-alist (car var-lst) (car ts-lst)
                              (zip-variable-type-alist (cdr var-lst)
                                                       (cdr ts-lst))))))

(defun assoc-equal-equality (lhs rhs type-alist)
  (cond ((endp type-alist) nil)
        ((and (nvariablep (caar type-alist))
              (not (fquotep (caar type-alist)))
              (eq (ffn-symb (caar type-alist)) 'EQUAL)
              (or (and (equal lhs (fargn (caar type-alist) 1))
                       (equal rhs (fargn (caar type-alist) 2)))
                  (and (equal rhs (fargn (caar type-alist) 1))
                       (equal lhs (fargn (caar type-alist) 2)))))
         (car type-alist))
        (t (assoc-equal-equality lhs rhs (cdr type-alist)))))

(defun look-in-type-alist (term type-alist)

; Look in the type-alist for term (and its commutation if term is an EQUAL)
; and return the type-set to which it is bound or nil.

  (cond ((variablep term) (cdr (assoc-equal term type-alist)))
        ((quotep term) nil)
        ((eq (ffn-symb term) 'EQUAL)
         (cdr (assoc-equal-equality (fargn term 1)
                                    (fargn term 2)
                                    type-alist)))
        (t (cdr (assoc-equal term type-alist)))))

(defun push-ancestor (lit ancestors)

; This function is used to push a new entry onto ancestors.  Lit is a
; term to be assumed true.

; Note:  It is important that the literal, lit, be in the car of the
; frame constructed below.

  (let* ((alit lit)
         (alit-atm (mv-let (not-flg atm)
                           (strip-not alit)
                           (declare (ignore not-flg))
                           atm)))
    (mv-let (fn-cnt-alit-atm p-fn-cnt-alit-atm)
            (fn-count alit-atm)
            (cons (list alit              ; the literal being assumed true
                                          ; (negation of hyp!)
                        alit-atm          ; the atom of that literal
                        fn-cnt-alit-atm   ; the fn-count of that atom
                        p-fn-cnt-alit-atm ; the pseudo-fn-count of that atom
                        )
                  ancestors))))

(defun ancestors-check1 (lit-atm lit fn-cnt p-fn-cnt ancestors)

; Roughly speaking, ancestors is a list of all the things we can
; assume by virtue of our trying to prove their negations.  That is,
; when we backchain from B to A by applying (implies A B), we try to
; prove A and so we put (NOT A) on ancestors and can legitimately
; assume it (i.e., (NOT A)) true.  Roughly speaking, if lit is a
; member-equal of ancestors, we return (mv t t) and if the complement
; of lit is a member-equal we return (mv t nil).  If neither case
; obtains, we return (mv nil nil).

; We implement the complement check as follows.  lit-atm is the atom
; of the literal lit.  Consider a literal of ancestors, alit, and its
; atom, alit-atm.  If lit-atm is alit-atm and lit is not equal to alit,
; then lit and alit are complementary.  The following table supports
; this observation.  It shows all the combinations by considering that
; lit is either a positive or negative p, and alit is a p of either
; sign or some other literal of either sign.  The entries labeled =
; mark those when lit is alit.  The entries labeled comp mark those
; when lit and alit are complementary.

; lit \  alit:    p (not p) q (not q)

; p               =   comp  x    x
; (not p)         comp =    x    x

  (cond
   ((endp ancestors)
    (mv nil nil))
   (t
    (let ((alit              (car (car ancestors)))
          (alit-atm          (cadr (car ancestors)))
          (fn-cnt-alit-atm   (caddr (car ancestors)))
          (p-fn-cnt-alit-atm (cadddr (car ancestors))))
      (cond
       ((equal alit lit)
        (mv t t))
       ((equal lit-atm alit-atm) (mv t nil))
       ((and (or (> fn-cnt fn-cnt-alit-atm)
                 (and (eql fn-cnt fn-cnt-alit-atm)
                      (>= p-fn-cnt p-fn-cnt-alit-atm)))
             (worse-than-or-equal lit-atm alit-atm))
        (mv t nil))
       (t (ancestors-check1 lit-atm lit fn-cnt p-fn-cnt
                            (cdr ancestors))))))))

(defun ancestors-check (lit ancestors)

; We return two values.  The first is whether we should abort trying
; to establish lit.  The second is whether lit is (assumed) true in
; ancestors.

; We abort iff either lit is assumed true or else it is worse than or
; equal to some other literal we're trying to establish.  (Actually,
; we compare the atoms of the two literals in the worse-than check.)

  (mv-let (not-flg lit-atm)
          (strip-not lit)
          (declare (ignore not-flg))
          (mv-let (fn-cnt p-fn-cnt)
                  (fn-count lit-atm)
                  (ancestors-check1 lit-atm lit fn-cnt p-fn-cnt
                                    ancestors))))

(defun search-type-alist (term typ type-alist unify-subst)

; We search type-alist for an instance of term bound to a type-set
; that is a subset of typ.

; For example, if typ is *ts-rational* then we seek an instance of
; term that is known to be a subset of the rationals.  Most commonly,
; typ is *ts-non-nil*.  In that case, we seek an instance of term
; that is non-nil.  Thus, this function can be thought of as trying to
; "make term true."  To use this function to "make term false," use
; the ts-complement of the desired type.  I.e., if you wish to find a
; false instance of term use *ts-nil*.

; By "instance" here we always mean an instance under an extension of
; unify-subst.  The extension is returned when we are successful.

; We return two values.  The first indicates whether we succeeded.
; The second is the final unify-subst.  If we did not succeed, the
; second value is our input unify-subst.  I.e., we are a No-Change
; Loser.

; The No-Change Policy:  Many multi-valued functions here return a
; flag that indicates whether they "won" or "lost" and, in the case
; that they won, return "new values" for certain of their arguments.
; Here for example, we return a new value for unify-subst.  In early
; coding we adopted the policy that when they "lost" the additional
; values were irrelevant and were often nil.  This policy prevented
; the use of such forms as:
; (mv-let (wonp unify-subst)
;         (search-type-alist ... unify-subst ...)
;         (cond (wonp ...)
;               (t otherwise...)))
; because at otherwise... unify-subst was no longer what it had been before
; the search-type-alist.  Instead we had to think of a new name for
; it in the mv-let and use the appropriate one below.

; We then adopted what we now call the "No-Change Policy".  If a
; function returns a won/lost flag and some altered arguments, the
; No-Change Policy is that it returns its input arguments in case it
; loses.  We will note explicitly when a function is a No-Change
; Loser.

  (cond ((endp type-alist)
         (mv nil unify-subst))
        ((ts-subsetp (cdr (car type-alist)) typ)
         (mv-let (ans unify-subst)
           (one-way-unify1 term (car (car type-alist)) unify-subst)
           (cond (ans (mv t unify-subst))
                 (t (search-type-alist term
                                       typ
                                       (cdr type-alist)
                                       unify-subst)))))
        (t (search-type-alist term
                              typ
                              (cdr type-alist)
                              unify-subst))))

(defun term-and-typ-to-lookup (hyp wrld ens)
  (mv-let
    (not-flg term)
    (strip-not hyp)
    (let ((recog-tuple (and (nvariablep term)
                            (not (fquotep term))
                            (not (flambda-applicationp term))
			    (<reduce-id>
			     (most-recent-enabled-recog-tuple
			      (ffn-symb term)
			      (global-val 'recognizer-alist wrld)
			      ens)))))
      (cond ((and recog-tuple
                  (access recognizer-tuple recog-tuple :strongp))
             (mv (fargn term 1)
                 (if not-flg
                     (access recognizer-tuple recog-tuple :false-ts)
                   (access recognizer-tuple recog-tuple :true-ts))))
            (t (mv term
                   (if not-flg *ts-nil* *ts-non-nil*)))))))

(defun lookup-hyp (hyp type-alist wrld unify-subst ens)

; See if hyp is true by type-alist considerations -- possibly
; extending the unify-subst.  If successful we return t and a new
; unify-subst.  No-Change Loser.

  (mv-let (term typ)
          (term-and-typ-to-lookup hyp wrld ens)
          (search-type-alist term typ type-alist unify-subst)))

(mutual-recursion

(defun sublis-var-and-mark-free (alist form)

; This function is rather odd: it is equivalent to (sublis-var alist'
; form) where alist' is derived from alist by adding a pair (var .
; ???-var) for each variable var in form that is not assigned a value
; by alist.  Thus it creates an instance of form.  However, the free
; vars of form are assigned essentially arbitrary variable values and
; while no two free vars are identified by this process, there is no
; guarantee that the variables introduced in their stead are "new."
; For example, ???-var may come into the instantiated term via alist.
; The only reason for this function is to highlight the free vars in a
; term upon which we will split, in the half-hearted hope that the
; user will spot it.

  (cond ((variablep form)
         (let ((a (assoc-eq form alist)))
           (cond (a (cdr a))
                 (t (packn (list "???-" form))))))
        ((fquotep form)
         form)
        (t (cons-term (ffn-symb form)
                      (sublis-var-and-mark-free-lst alist (fargs form))))))

(defun sublis-var-and-mark-free-lst (alist l)
  (if (endp l)
      nil
    (cons (sublis-var-and-mark-free alist (car l))
          (sublis-var-and-mark-free-lst alist (cdr l)))))

)

(defun assume-true-false-<
  (not-flg arg1 arg2 ts1 ts2 type-alist)

; This function returns an extended type-alist by assuming (< ts1 ts2) true if
; not-flg is nil, but assuming (< ts1 ts2) false if not-flg is not nil.  It
; assumes that type-set (and hence type-set-<) was not able to decide the truth
; or falsity of (< ts1 ts2).  We could put this code in-line in
; assume-true-false, but the `true-type-alist' and `false-type-alist' are dealt
; with symmetrically, so it's convenient to share code via this function.

; Here are the cases we handle.  In this sketch we are glib about the
; possibility that arg1 or arg2 is nonnumeric or complex, but our code handles
; the more general situation.

; When we assume (< arg1 arg2) true,
; * if arg1 is positive then arg2 is positive
; * if arg1 is in the nonnegatives then arg2 is strictly positive
; * if arg2 is in the nonpositives then arg1 is strictly negative
; When we say "arg1 is in the nonnegatives" we mean to include the
; case where arg1 is strictly positive.  Note also that if arg1 may be
; negative, then arg2 could be anything (given that we've made the
; normalization for integers above).  Thus, the above two cases are as
; strong as we can be.

; When we assume (< arg1 arg2) false we find it easier to think about
; assuming (<= arg2 arg1) true:
; * if arg1 is negative, then arg2 is negative
; * if arg1 is nonpositive, then arg2 is nonpositive
; * if arg2 is nonnegative, then arg1 is nonnegative
; Note that if arg1 may be positive then arg2 could be anything, so
; there are no other cases we can express.

  (cond
   ((and
     (not not-flg)
     (ts-subsetp ts1
                 (ts-union *ts-non-negative-rational*
                           (ts-complement *ts-acl2-number*)))
     (ts-intersectp
      ts2
      (ts-complement (ts-union *ts-positive-rational* *ts-complex-rational*))))

; The test says: We are dealing with (< arg1 arg2) where arg1 is non-negative
; or a non-number.  We are thus allowed to deduce that arg2 is strictly
; positive or complex.  That is, we may delete the non-positive reals
; and non-numbers from its existing type-set.  If that doesn't change
; anything, we don't want to do it, so we have the third conjunct above that
; says arg2 contains some non-positive reals or some non-numbers.

; A worry is that the intersection below is empty.  Can that happen?  If it
; did, then we would have that arg1 is a non-negative real or a non-number,
; and arg2 is a non-positive real or a non-number.  Supposedly type-set-<
; would have then reported that (< arg1 arg2) must be false and mbf would be t.
; So the empty intersection cannot arise.

    (extend-type-alist
     arg2
     (ts-intersection ts2
                      (ts-union *ts-positive-rational* *ts-complex-rational*))
     type-alist))

; The remaining cases are analogous to that above.

   ((and (not not-flg)
         (ts-subsetp ts2
                     (ts-union *ts-non-positive-rational*
                               (ts-complement *ts-acl2-number*)))
         (ts-intersectp
          ts1
          (ts-complement
           (ts-union *ts-negative-rational* *ts-complex-rational*))))
    (extend-type-alist
     arg1
     (ts-intersection ts1
                      (ts-union *ts-negative-rational*
                                *ts-complex-rational*))
     type-alist))
   ((and not-flg
         (ts-subsetp ts1
                     *ts-negative-rational*)
         (ts-intersectp ts2
                        (ts-complement (ts-union *ts-complex-rational*
                                                 *ts-negative-rational*))))
; We are dealing with (not (< arg1 arg2)) which is (<= arg2 arg1) and we here
; know that arg1 is negative.  Thus, arg2 must be negative or complex.  See the
; case below for more details.

    (extend-type-alist
     arg2
     (ts-intersection ts2
                      (ts-union *ts-complex-rational*
                                *ts-negative-rational*))
     type-alist))
   ((and not-flg
         (ts-subsetp ts1
                     (ts-union *ts-non-positive-rational*
                               (ts-complement *ts-acl2-number*)))
         (ts-intersectp ts2
                        *ts-positive-rational*))

; Here we are dealing with (not (< arg1 arg2)) which is (<= arg2 arg1).  We
; know arg1 is <= 0.  We will thus deduce that arg2 is <= 0, and hence not a
; positive real, if we don't already know it.  But the worry again arises
; that the intersection of arg2's known type and the complement of the
; positive-reals is empty.  Suppose it were.  Then arg2 is a strictly
; positive real.  But if arg1 is a non-positive real or a non-number
; and arg2 is a positive real, then type-set-< knows that (< arg1 arg2) is
; true.  Thus, this worry is again baseless.

    (extend-type-alist
     arg2
     (ts-intersection
      ts2
      (ts-complement *ts-positive-rational*))
     type-alist))
   ((and not-flg
         (ts-subsetp ts2
                     *ts-positive-rational*)
         (ts-intersectp ts1
                        (ts-complement
                         (ts-union *ts-complex-rational*
                                   *ts-positive-rational*))))
    (extend-type-alist
     arg1
     (ts-intersection
      ts1
      (ts-union *ts-complex-rational*
                *ts-positive-rational*))
     type-alist))
   ((and not-flg
         (ts-subsetp
          ts2
          (ts-complement
           (ts-union *ts-complex-rational*
                     *ts-negative-rational*)))
         (ts-intersectp ts1
                        *ts-negative-rational*))
    (extend-type-alist
     arg1
     (ts-intersection
      ts1
      (ts-complement *ts-negative-rational*))
     type-alist))
   (t type-alist)))

(defun mv-atf-2 (not-flg true-type-alist false-type-alist
                         new-term xnot-flg x)

; This function is a variation of mv-atf in which mbt and mbf
; are known to be nil.  The scenario is that there is
; an implicit term that we want to assume true or false, and we have
; generated two other terms x and new-term to assume true or false
; instead, each with its own parity (xnot-flg and not-flg,
; respectively).  We want to avoid putting redundant information on
; the type-alist, which would happen if we are not careful in the case
; that x and new-term are the same term modulo their respective
; parities.

; We assume that new-term is not a call of NOT.

  (let ((tta0 (extend-type-alist
               new-term
               *ts-t*
               true-type-alist))
        (fta0 (extend-type-alist
               new-term
               *ts-nil*
               false-type-alist))
        (same-parity (eq not-flg xnot-flg)))
    (cond
     ((equal new-term ; new-term is not a call of NOT, so we negate x
             (cond (same-parity x)
                   (t (dumb-negate-lit x))))
      (mv-atf not-flg nil nil tta0 fta0))
     (t
      (let ((tta1 (extend-type-alist
                   x
                   (if same-parity *ts-t* *ts-nil*)
                   tta0))
            (fta1 (extend-type-alist
                   x
                   (if same-parity *ts-nil* *ts-t*)
                   fta0)))
        (mv-atf not-flg nil nil tta1 fta1))))))

; I spent a while trying to come up with a measure of terms under
; which lambda expansion reduced the size.  The measure was intended
; to handle the cases in the type-set clique in which the recursion
; was on subcor-var expressions.  However, some of those calls are
; used to expand *expandable-boot-strap-non-rec-fns*.  But for those
; recursions to terminate we must know that every member of that list
; has a non-recursive body in w.  That is a fairly complicated
; invariant of w and I don't want to involve it in the termination
; argument.

; A second termination problem has to do with type-prescription
; lemmas.  Should there be a lemma like (implies (integerp (fn x))
; (integerp (fn x))) in w then we would loop forever -- or at least
; termination would depend on properties of ancestors-check that I
; don't want to analyze.

; The bottom line: I think it is best to add a numeric argument, nnn, to
; handle these two recursions.

(include-book "std/basic/two-nats-measure" :dir :system)

(defun lex4 (i j k l)
  (acl2::nat-list-measure (list i j k l)))

(defthm type-set-admission-lemma1
  (<= (acl2-count (car x))
      (acl2-count x))
  :rule-classes :linear)

(defthm type-set-admission-lemma2
  (<= (acl2-count (cdr x))
      (acl2-count x))
  :rule-classes :linear)

(defthm type-set-admission-lemma3
  (implies (consp x)
           (< (acl2-count (car x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm type-set-admission-lemma4
  (implies (consp x)
           (< (acl2-count (cdr x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm type-set-admission-lemma5
  (implies (car x)
           (< (acl2-count (cdr x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-non-cons-cdr
  (<= (acl2-count (non-cons-cdr x)) (acl2-count x))
  :hints (("Goal" :induct (non-cons-cdr x)))
  :rule-classes :linear)

(mutual-recursion

(defun type-set (x type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count x) 5 0)
                  :hints
                  (("Goal" :in-theory (disable getprop
                                               ancestors-check push-ancestor
                                               sublis-var free-varsp
                                               enabled-numep
                                               look-in-type-alist lookup-hyp
                                               one-way-unify acl2-count
                                               member-eq acl2::member-equal)))))

; X is a term and type-alist is a type alist mapping terms to their
; type-sets and thus encoding the current assumptions.  We return the
; type-set of term under those assumptions.

; Note:  If ancestors is t it means:  don't backchain.  Act as though
; the literal we're backchaining on is worse than everything in sight.
; This is called the ``t-ancestors hack'' and is commented upon below.

  (let ((ts0 (look-in-type-alist x type-alist)))
    (cond
     (ts0 ts0)
     ((variablep x) *ts-unknown*)
     ((fquotep x) (type-set-quote (cadr x)))
     (t
      (let ((fn (ffn-symb x)))
        (cond
         ((or (flambdap fn)
              (member-eq fn *expandable-boot-strap-non-rec-fns*))

; PSIM test: If the lambda expression uses its formals repeatedly in
; the body, this treatment could hammer memoization.

          (if (zp nnn)
              *ts-unknown*
            (type-set (subcor-var (formals fn w)
                                  (fargs x)
                                  (body fn t w))
                      type-alist ancestors ens w (- nnn 1))))
         ((eq fn 'not)
          (type-set-not
           (type-set (fargn x 1) type-alist ancestors ens w nnn)))
         (t
          (let* ((recog-tuple
                  (most-recent-enabled-recog-tuple
                   fn
                   (global-val 'recognizer-alist w)
                   ens)))
            (cond
             (recog-tuple
              (<type-set-id>
               (let ((ts (type-set-recognizer
                          recog-tuple
                          (type-set (fargn x 1)
                                    type-alist ancestors ens w nnn))))
                 (cond
                  ((or (ts= ts *ts-t*)
                       (ts= ts *ts-nil*))
                   ts)
                  (t
                   (ts-intersection
                    ts
                    (type-set-with-rules
                     (getprop fn 'type-prescriptions nil w)
                     x type-alist ancestors ens w *ts-unknown*
                     nnn)))))))
             ((eq fn 'if)
              (mv-let
               (must-be-true must-be-false true-type-alist false-type-alist)
               (assume-true-false (fargn x 1) type-alist ancestors ens w nnn)
               (cond (must-be-true
                      (type-set (fargn x 2)
                                true-type-alist ancestors ens w nnn))
                     (must-be-false
                      (type-set (fargn x 3)
                                false-type-alist ancestors ens w nnn))
                     (t (ts-union (type-set (fargn x 2)
                                            true-type-alist
                                            ancestors ens
                                            w nnn)
                                  (type-set (fargn x 3)
                                            false-type-alist
                                            ancestors ens
                                            w nnn))))))
             (t
              (type-set-with-rules
               (getprop fn 'type-prescriptions nil w)
               x type-alist ancestors ens w *ts-unknown* nnn)))))))))))

(defun type-set-relieve-hyps (hyps alist type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn 0 0 (acl2-count hyps))))

; Hyps is a list of terms, implicitly conjoined.  Alist is a
; substitution mapping variables in hyps to terms governed by
; type-alist.  Consider the result, hyps', of substituting alist into
; each hyp in hyps.  We wish to know whether, by type-set reasoning
; alone, we can get that hyps' are all true in the context of
; type-alist.  We do the substitution one hyp at a time, so we don't
; pay the price of consing up instances beyond the first hyp that
; fails.  We extend alist as necessary to choose free variables in
; hyps.  But we do not return the final extension of the alist because
; type-prescription lemmas never contain free variables in the
; conclusion.  While we are at it, we record in an extension of
; type-alist the type computed for each hyp', so that if subsequent
; rules need that information, they can get it quickly.  We return
; (mv wonp type-alist').

  (cond
   ((endp hyps) (mv t type-alist))
   (t
    (let* ((hyp (car hyps)))
      (mv-let
       (lookup-hyp-ans alist)
       (lookup-hyp hyp type-alist w alist ens)
       (cond
        (lookup-hyp-ans
         (type-set-relieve-hyps (cdr hyps) alist type-alist ancestors
                                ens w nnn))
        ((free-varsp hyp alist)
         (cond ((and (equalityp hyp)
                     (variablep (fargn hyp 1))
                     (not (assoc-eq (fargn hyp 1) alist))
                     (not (free-varsp (fargn hyp 2) alist)))
                (type-set-relieve-hyps
                 (cdr hyps)
                 (cons (cons (fargn hyp 1) (fargn hyp 2)) alist)
                 type-alist ancestors ens w nnn))
               (t (mv nil type-alist))))
        (t
         (mv-let
          (not-flg atm)
          (strip-not hyp)
          (let ((atm1 (sublis-var alist atm)))
            (mv-let
             (on-ancestorsp assumed-true)

; Note: Here is one of two places where we implement the t-ancestors
; hack.

             (if (eq ancestors t)
                 (mv t nil)
               (ancestors-check (if not-flg
                                    (fcons-term* 'not atm1)
                                  atm1)
                                ancestors))
             (cond
              (on-ancestorsp
               (cond
                (assumed-true
                 (type-set-relieve-hyps (cdr hyps)
                                        alist type-alist ancestors ens w nnn))
                (t (mv nil type-alist))))
              ((zp nnn) (mv nil type-alist))
              (t
               (let* ((ts1 (type-set atm1 type-alist

; Here is the other place we enforce the t-ancestors hack.

                                     (if (eq ancestors t)
                                         t
                                       (push-ancestor
                                        (if not-flg
                                            atm1
                                          (fcons-term* 'not atm1))
                                        ancestors)) ens
                                     w (- nnn 1)))
                      (type-alist
                       (cond ((assoc-equal atm1 type-alist)
                              type-alist)
                             (t (extend-type-alist atm1 ts1 type-alist))))
                      (ts (if not-flg
                              (cond ((ts= ts1 *ts-nil*) *ts-t*)
                                    ((ts-intersectp ts1 *ts-nil*)
                                     *ts-boolean*)
                                    (t *ts-nil*))
                            ts1)))
                 (cond
                  ((ts= ts *ts-nil*) (mv nil type-alist))
                  ((ts-intersectp *ts-nil* ts)
                   (mv nil type-alist))
                  (t
                   (type-set-relieve-hyps (cdr hyps)
                                          alist type-alist
                                          ancestors ens w nnn))))))))))))))))

(defun extend-type-alist-with-bindings (alist type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn 0 0 (acl2-count alist))))

; Alist is an alist that pairs variables in some rule with terms.  We compute
; the type-set of each term in the range of alist and extend type-alist with
; new entries that pair each term to its type-set.

  (cond ((endp alist) type-alist)
        ((zp nnn) type-alist)
        (t (extend-type-alist-with-bindings
            (cdr alist)
            (cond ((assoc-equal (cdr (car alist)) type-alist)
                   type-alist)
                  (t
                   (extend-type-alist
                    (cdr (car alist))
                    (type-set (cdr (car alist))
                              type-alist ancestors ens w
                              (- nnn 1))
                    type-alist)))
            ancestors ens w nnn))))

(defun type-set-with-rule (tp term type-alist ancestors ens w nnn)
  (declare (xargs :measure (lex4 nnn (acl2-count term) 3 0)))

; We apply the type-prescription, tp, to term, if possible, and return
; a type-set and an extended type-alist.  If the rule is inapplicable,
; the type-set is *ts-unknown* and the ``extended'' type-alist is the
; original type-alist.

; This is a No Change Loser with respect to type-alist.

  (if (or (zp nnn)
          (not (enabled-numep (access type-prescription tp :nume) ens)))
      (mv *ts-unknown* type-alist)
    (mv-let
     (unify-ans unify-subst)
     (one-way-unify (access type-prescription tp :term)
                    term)
     (cond
      (unify-ans
       (<type-set-with-rule-id>
        (let* ((hyps (access type-prescription tp :hyps))
               (type-alist1
                (cond
                 ((null hyps) type-alist)
                 (t (extend-type-alist-with-bindings unify-subst
                                                     type-alist
                                                     ancestors ens w
                                                     (- nnn 1))))))
          (mv-let
           (relieve-hyps-ans type-alist1)
           (type-set-relieve-hyps hyps
                                  unify-subst
                                  type-alist1
                                  ancestors
                                  ens
                                  w
                                  (- nnn 1))
           (cond
            (relieve-hyps-ans
             (mv (type-set-with-rule1 unify-subst
                                      (access type-prescription tp :vars)
                                      type-alist1 ancestors ens w
                                      (access type-prescription tp :basic-ts)
                                      (- nnn 1))
                 type-alist1))
            (t (mv *ts-unknown* type-alist)))))))
      (t (mv *ts-unknown* type-alist))))))

(defun type-set-with-rule1 (alist vars type-alist ancestors ens w basic-ts nnn)

  (declare (xargs :measure (lex4 nnn 0 0 (acl2-count alist))))

; Alist is an alist that maps variables to terms.  The terms are in
; the context described by type-alist.  Vars is a list of variables.
; We map over the pairs in alist unioning into basic-ts the type-sets
; of those terms whose corresponding vars are in vars.  We ultimately
; return the final basic-ts.

  (cond
   ((endp alist) basic-ts)
   ((zp nnn) basic-ts)
   (t (type-set-with-rule1 (cdr alist) vars type-alist ancestors ens w
                           (if (member-eq (caar alist) vars)
                               (ts-union
                                (type-set (cdar alist) type-alist
                                          ancestors ens w (- nnn 1))
                                basic-ts)
                             basic-ts) nnn))))

(defun type-set-with-rules (tp-lst term type-alist ancestors ens w ts nnn)

  (declare (xargs :measure (lex4 nnn
                                 (acl2-count term)
                                 4
                                 (acl2-count tp-lst))))

; We try to apply each type-prescription in tp-lst, intersecting
; together all the type sets we get.

  (cond
   ((endp tp-lst)
    (ts-intersection (type-set-primitive term type-alist ancestors ens w nnn)
                     ts))
   ((ts-subsetp ts (access type-prescription (car tp-lst) :basic-ts))

; Our goal is to make the final type-set, ts, as small as possible by
; intersecting it with the type-sets returned to the various rules.
; If ts is already smaller than the :basic-ts of a rule, there is no
; point in trying that rule.

    (type-set-with-rules (cdr tp-lst) term type-alist ancestors ens w ts nnn))
   (t
    (mv-let
     (ts1 type-alist)
     (type-set-with-rule (car tp-lst) term type-alist ancestors ens w nnn)
     (type-set-with-rules (cdr tp-lst)
                          term type-alist ancestors ens w
                          (ts-intersection ts1 ts) nnn)))))

(defun type-set-primitive (term type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count term) 3 0)))

; This function should handle
; every non-recognizer function handled in *primitive-formals-and-guards*,
; ev-fncall, and cons-term1, though like cons-term1, we also handle NOT.
; Exception:  Since code-char is so simple type-theoretically, we handle its
; type set computation with rule code-char-type in axioms.lisp.  It is
; perfectly acceptable to handle function symbols here that are not handled by
; the functions above.  For example, we compute a type-set for length in a
; special manner below, but cons-term1 and the others do not know about
; length.

  (case (ffn-symb term)
    (cons
     (type-set-cons
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (equal
     (cond
      ((equal (fargn term 1) (fargn term 2))
       *ts-t*)
      (t (type-set-equal
          (type-set (fargn term 1) type-alist ancestors ens w nnn)
          (type-set (fargn term 2) type-alist ancestors ens w nnn)))))
    (unary--
     (type-set-unary--
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (unary-/
     (type-set-unary-/
      (type-set (fargn term 1)
                type-alist
                ancestors ens
                w nnn)))
    (denominator
     (type-set-denominator
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (numerator
     (type-set-numerator
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (car
     (type-set-car
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (cdr
     (type-set-cdr
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (symbol-name
     *ts-string*)
    (symbol-package-name
     *ts-string*)
    (intern-in-package-of-symbol
     (type-set-intern-in-package-of-symbol
      (type-set (fargn term 1) type-alist ancestors ens w nnn)
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (coerce
     (type-set-coerce
      term
      (type-set (fargn term 1) type-alist ancestors ens w nnn)
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (length
     (type-set-length
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (binary-+
     (type-set-binary-+
      term
      (type-set (fargn term 1) type-alist ancestors ens w nnn)
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (binary-*
     (type-set-binary-*
      (type-set (fargn term 1) type-alist ancestors ens w nnn)
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (<
     (type-set-< (fargn term 1)
                 (fargn term 2)
                 (type-set (fargn term 1) type-alist ancestors ens w nnn)
                 (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (not
     (type-set-not
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (realpart
     (type-set-realpart
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (imagpart
     (type-set-imagpart
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (complex
     (type-set-complex
      (type-set (fargn term 1) type-alist ancestors ens w nnn)
      (type-set (fargn term 2) type-alist ancestors ens w nnn)))
    (char-code
     (type-set-char-code
      (type-set (fargn term 1) type-alist ancestors ens w nnn)))
    (otherwise *ts-unknown*)))

(defun assume-true-false (x type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count x) 12 0)))

; We assume x both true and false, extending type-alist as appropriate.

; We return four values.
; must-be-true     - t iff x is definitely true under type-alist and w.
; must-be-false    - t iff x is definitely false under type-alist and w.
; true-type-alist  - an extension of type-alist encoding the assumption
;                    that x is true; valid only if not must-be-false.
; false-type-alist - and extension of type-alist encoding the assumption
;                    that x is false; valid only if not must-be-true.

  (mv-let
   (xnot-flg x)
   (strip-not x)
   (cond
    ((variablep x)
     (assume-true-false1 xnot-flg x type-alist ancestors ens w nnn))
    ((fquotep x)
     (if (equal x *nil*)
         (mv-atf xnot-flg nil t nil type-alist)
         (mv-atf xnot-flg t nil type-alist nil)))
    ((flambda-applicationp x)
     (assume-true-false1 xnot-flg x type-alist ancestors ens w nnn))
    (t
     (let ((recog-tuple
            (most-recent-enabled-recog-tuple
             (ffn-symb x)
             (global-val 'recognizer-alist w)
             ens)))
       (cond
        (recog-tuple
         (<assume-true-false-id>
          (let* ((ts (type-set (fargn x 1) type-alist ancestors ens w nnn))
                 (t-int (ts-intersection ts (access recognizer-tuple
                                                    recog-tuple :true-ts)))
                 (f-int (ts-intersection ts (access recognizer-tuple
                                                    recog-tuple :false-ts))))
            (cond
             ((ts= t-int *ts-empty*)
              (mv-atf xnot-flg nil t nil type-alist))
             ((ts= f-int *ts-empty*)
              (mv-atf xnot-flg t nil type-alist nil))
             (t

; At this point we know that we can't determine whether (recog arg) is
; true or false.  We therefore will be returning two type-alists which
; restrict arg's type according to the two intersections computed
; above.

              (mv-atf xnot-flg nil nil
                      (extend-with-proper/improper-cons-ts-tuple
                       (fargn x 1) t-int type-alist ancestors
                       (if (access recognizer-tuple recog-tuple :strongp)
                           type-alist
                         (extend-type-alist x *ts-t* type-alist))
                       ens w nnn)
                      (extend-with-proper/improper-cons-ts-tuple
                       (fargn x 1) f-int type-alist ancestors
                       (if (access recognizer-tuple recog-tuple :strongp)
                           type-alist
                         (extend-type-alist x *ts-nil* type-alist))
                       ens w nnn)))))))
        ((member-eq (ffn-symb x) *expandable-boot-strap-non-rec-fns*)
         (if (zp nnn)
             (assume-true-false1 xnot-flg x type-alist ancestors ens w nnn)
           (mv-let
            (mbt mbf tta fta)
            (assume-true-false
             (subcor-var (formals (ffn-symb x) w)
                         (fargs x)
                         (body (ffn-symb x) t w))
             type-alist ancestors ens w (- nnn 1))
            (mv-atf xnot-flg mbt mbf tta fta))))
        ((eq (ffn-symb x) 'equal)
         (let ((arg1 (fargn x 1))
               (arg2 (fargn x 2)))
           (cond
            ((equal arg1 arg2)
             (mv-atf xnot-flg t nil type-alist nil))
            ((and (quotep arg1) (quotep arg2))
             (mv-atf xnot-flg nil t nil type-alist))
            (t
             (let ((ts (look-in-type-alist x type-alist)))
               (cond
                ((and ts (ts= ts *ts-t*))
                 (mv-atf xnot-flg t nil type-alist nil))
                ((and ts (ts= ts *ts-nil*))
                 (mv-atf xnot-flg nil t nil type-alist))
                (t (let* ((ts1 (type-set arg1 type-alist ancestors ens w nnn))
                          (ts2 (type-set arg2 type-alist ancestors ens w nnn))
                          (int (ts-intersection ts1 ts2)))
                     (cond
                      ((ts= int *ts-empty*)
                       (mv-atf xnot-flg nil t nil type-alist))
                      ((and (ts= ts1 ts2)
                            (member ts1 *singleton-type-sets*))
                       (mv-atf xnot-flg t nil type-alist nil))
                      (t
                       (let* ((true-type-alist1
                               (extend-type-alist x *ts-t* type-alist))
                              (true-type-alist2
                               (cond
                                ((ts= ts1 int) true-type-alist1)
                                (t (extend-with-proper/improper-cons-ts-tuple
                                    arg1 int type-alist ancestors
                                    true-type-alist1 ens w nnn))))
                              (true-type-alist3
                               (cond
                                ((ts= ts2 int) true-type-alist2)
                                (t (extend-with-proper/improper-cons-ts-tuple
                                    arg2 int type-alist ancestors
                                    true-type-alist2 ens w nnn))))
                              (false-type-alist1
                               (extend-type-alist x *ts-nil* type-alist))
                              (false-type-alist2
                               (cond
                                ((member ts2 *singleton-type-sets*)
                                 (extend-with-proper/improper-cons-ts-tuple
                                  arg1
                                  (ts-intersection ts1 (ts-complement ts2))
                                  type-alist ancestors
                                  false-type-alist1 ens w nnn))
                                (t false-type-alist1)))
                              (false-type-alist3
                               (cond
                                ((member ts1 *singleton-type-sets*)
                                 (extend-with-proper/improper-cons-ts-tuple
                                  arg2
                                  (ts-intersection ts2 (ts-complement ts1))
                                  type-alist ancestors
                                  false-type-alist2 ens w nnn))
                                (t false-type-alist2))))
                         (mv-atf xnot-flg nil nil
                                 true-type-alist3 false-type-alist3))))))))))))
        ((eq (ffn-symb x) '<)
         (let ((ts0 (type-set x type-alist ancestors ens w nnn)))
           (cond
            ((ts= ts0 *ts-nil*)
             (mv-atf xnot-flg nil t nil type-alist))
            ((not (ts-intersectp ts0 *ts-nil*))
             (mv-atf xnot-flg t nil type-alist nil))
            (t
             (let* ((ts1 (type-set (fargn x 1) type-alist ancestors ens w nnn))
                    (ts2 (type-set (fargn x 2) type-alist ancestors ens w nnn)))

; In the mv-let below we effectively implement the facts that, when x
; is of type *ts-integer* (< x 1) is ~(< 0 x), and (< -1 x) is ~(< x
; 0).  By normalizing such inequalities around 0 we can more easily
; recognize the ones covered by our builtin types.

; WARNING: A bug once lurked here, so beware.  The term we are
; assuming is represented by xnot-flg and x.  We are about to
; re-represent it in terms of not-flg, arg1 and arg2.  Do not
; accidentally use not-flg with x or xnot-flg with (< arg1 arg2)!  In
; the old code, we had only one name for these two flgs.

               (mv-let
                (not-flg arg1 arg2 ts1 ts2)
                (cond
                 ((and (equal (fargn x 2) *1*)
                       (ts-subsetp ts1
                                   (ts-union (ts-complement
                                              *ts-acl2-number*)
                                             *ts-integer*)))
                  (mv (not xnot-flg) *0* (fargn x 1) *ts-zero* ts1))
                 ((and (equal (fargn x 1) *-1*)
                       (ts-subsetp ts2
                                   (ts-union (ts-complement
                                              *ts-acl2-number*)
                                             *ts-integer*)))
                  (mv (not xnot-flg) (fargn x 2) *0* ts2 *ts-zero*))
                 (t (mv xnot-flg (fargn x 1) (fargn x 2) ts1 ts2)))

; Foreshadow 1:  Note that if neither of the newly bound arg1 nor arg2
; is *0* then not-flg is xnot-flg and arg1 and arg2 are the corresponding
; arguments of x.  That is because on the first two of the three branches
; of the cond above, one of the two args is set to *0*.  We use this curious
; fact below.

; In the mv-let below we effectively implement the fact that, when x is of type
; *ts-integer* (< 0 (+ 1 x)) is ~(< x 0).  The symmetric equivalence of (< (+
; -1 x) 0) to ~(< 0 x) is also handled.

; We will assume that the binary-+ has been commuted so that the constant arg,
; if any, is the first.

; Note that the output of this transformation is not subject to the first
; transformation, above, so we do not have to consider repeating that
; transformation.  However, it is conceivable that the output of this
; transformation is subject to its symmetric counterpart.  In particular, if we
; composed this transformation with itself we might reduce (< 0 (+ 1 (+ -1 x)))
; to (< 0 x).  We prefer instead to take the position that some arithmetic
; simplifier will reduce the +-expressions.

                (mv-let
                 (not-flg arg1 arg2 ts1 ts2)
                 (cond ((and (equal arg1 *0*)
                             (ts-subsetp ts2

; It is sound to use (ts-intersection ts2 *ts-acl2-number*) in place of ts2
; above, but since below we see that arg2 is a call of binary-+, we know that
; ts2 is already contained in *ts-acl2-number*.

                                         *ts-integer*)
                             (nvariablep arg2)
                             (not (fquotep arg2))
                             (eq (ffn-symb arg2) 'binary-+)
                             (equal (fargn arg2 1) *1*))

; So the term is of the form (< 0 (+ 1 x)) and we know x is some integer (or a
; non-number).  We transform it to ~(< x 0).  But we must determine the
; type-set of x.  It cannot be done merely by inverting the type-set of (+ 1
; x): the latter might be *ts-integer* and x could either be
; *ts-non-positive-integer* or *ts-integer*, or even a non-number.  Some cases
; we could invert:  if (+ 1 x) is non-positive, then we know x must be strictly
; negative.  But rather than invert, we just call type-set on x.

                        (mv (not not-flg)
                            (fargn arg2 2)
                            *0*
                            (type-set (fargn arg2 2)
                                      type-alist
                                      ancestors ens w nnn)
                            *ts-zero*))
                       ((and (equal arg2 *0*)
                             (ts-subsetp ts1 *ts-integer*)
                             (nvariablep arg1)
                             (not (fquotep arg1))
                             (eq (ffn-symb arg1) 'binary-+)
                             (equal (fargn arg1 1) *-1*))
                        (mv (not not-flg)
                            *0*
                            (fargn arg1 2)
                            *ts-zero*
                            (type-set (fargn arg1 2)
                                      type-alist
                                      ancestors ens w nnn)))
                       (t (mv not-flg arg1 arg2 ts1 ts2)))

; Foreshadow 2:  Observe that if, at this point, neither the newly bound arg1
; nor the newly bound arg2 is *0*, then the newly bound not-flg, arg1 and arg2
; are all equal to their old values (outside this mv-let).  That is because the
; cond above, which determines the new values of not-flg, arg1 and arg2 here,
; has the property that on the two branches that change the not-flg, one of
; the two args is set to *0*.  If neither arg is *0* then we could have only
; come out on the last clause of the cond above and not-flg etc are thus
; unchanged.  We use this curious property below.

; The transformations just carried out have the possibly odd effect of
; assuming (< 0 x) false when asked to assume (< x 1) true, for integral x.
; This effectively sets x's type-set to the non-positives.  One might
; then ask, what happens if we later decide to get the type-set of (<
; x 1).  We would hope that, having assumed it, we would realize it
; was true!  Indeed we do, but only because type-set-< makes the same
; normalization of (< x 1).  This raises the question: Could we reduce
; the size of our code by doing the normalization in only one place,
; either here in assume-true-false or there in type-set-<?  The real
; reason we do it in both places has nothing to do with the subtleties
; discussed here; there is no guarantee that both of these functions
; will be called.  If (< x 1) appears in a test, we will call
; assume-true-false on it and we have to normalize it to produce the
; desired tta and fta.  If (< x 1) appears as the entire resultant
; term, we'll just call type-set on it and we have to normalize it to
; decide it.

; Another question raised is: "What about the second transformation done
; above?"  We assume ~(< x 0) when asked to assume (< 0 (+ 1 x)), with the
; effect that x is given (roughly) the type-set non-negative integer.  Note
; that type-set-< does not make this second transformation.  Will we recognize
; (< 0 (+ 1 x)) as true later?  Yes.  If x is non-negative, then type-set
; determines that (+ 1 x) is positive and hence (< 0 (+ 1 x)) is true.

                 (cond
                  ((equal arg1 *0*)
                   (cond
                    ((ts-subsetp ts2 *ts-positive-rational*)
                     (mv-atf not-flg t nil type-alist nil))
                    ((ts-subsetp ts2
                                 (ts-union (ts-complement *ts-acl2-number*)
                                           *ts-non-positive-rational*))
                     (mv-atf not-flg nil t nil type-alist))
                    (t
                     (let* ((true-type-alist
                             (extend-type-alist
                              arg2
                              (ts-intersection
                               ts2
                               (ts-union *ts-positive-rational*
                                         *ts-complex-rational*))
                              type-alist))
                            (false-type-alist
                             (extend-type-alist
                              arg2
                              (ts-intersection
                               ts2 (ts-complement *ts-positive-rational*))
                              type-alist)))

; We formerly put the inequality explicitly on the type-alist only in
; the case that (ts-intersectp ts2 *ts-complex-rational*).  We leave
; in place the comment regarding that case, below.  However, we now
; put the inequality on the type-alist in all cases, in order to
; assist in relieving hypotheses involving free variables.  Robert
; Krug sent the following relevant example.

                       #|
 (defstub foo (x) t)

 (defaxiom test1
   (implies (and (<= 0 x)
                 (rationalp x))
            (foo y)))

 (thm
  (implies (and (rationalp x)
                (<= 0 x))
           (foo y)))
|#

; The thm fails, because the hypothesis of test1 is not relieved.  The
; following trace excerpt shows why.

                       #|
  1> (SEARCH-TYPE-ALIST (< X '0)    ; Attempt to find that (< X 0)
                        64          ; is false.  Note:
                                    ; (decode-type-set 64) = '*TS-NIL*
                        ((X 7))     ; Type-alist:  X is a non-negative
                                    ; rational.  Note:
                                    ; (decode-type-set 7) =
                                    ; *TS-NON-NEGATIVE-RATIONAL*
                        ((Y . Y))   ; unify-subst
                        NIL)>       ; ttree
  <1 (SEARCH-TYPE-ALIST NIL ((Y . Y)) NIL)>   ; failed to relieve hyp
|#

; As seen below, assume-true-false had failed to put the inequality
; explicitly on the type-alist.

                       #|
  1> (ASSUME-TRUE-FALSE (< X '0) ; condition assumed true or false
                        NIL      ; a tag tree
                        NIL      ; force-flg
                        NIL      ; never mind this one...
                        ((X 31)) ; type-alist: X is rational
                        NIL      ; ancestors
                        |some-enabled-structure|
                        |current-acl2-world|)>
  <1 (ASSUME-TRUE-FALSE NIL             ; must-be-true
                        NIL             ; must-be-false
                        ((X 24) (X 31)) ; true-type-alist:
                                        ; X is negative rational
                        ((X 7) (X 31))  ; false-type-alist:
                                        ; X is non-negative rational
                        NIL)>           ; tag tree
|#

; But wait, there's more!  Robert subsequently sent an example showing
; that it is not enough to put the current inequality with 0, e.g.,
; (fcons-term* '< *0* arg2), on the type-alist.  The original equality
; may need to be there as well.  Here is his example, which ACL2 can
; now prove (see mv-atf-2).

                       #|
 (defstub foo (x) t)

 (defaxiom test
   (implies (and (<= 1 x)
                 (integerp x))
            (foo y)))

 (thm
   (implies (and (integerp x)
                 (<= 1 x))
            (foo y)))
|#

; Start old comment regarding the case that (ts-intersectp ts2
; *ts-complex-rational*).

; Long comment on why we extend the true-type-alist to accommodate complex
; numbers.

; For an example that illustrates why we need to put (fcons-term* '< *0* arg2)
; on the true-type-alist explicitly in this case, try the following.

                       #|
 (encapsulate
  (((foo *) => *))
  (local (defun foo (x) (<= 0 x)))
  (defthm foo-type (implies (<= 0 x) (equal (foo x) t))
    :rule-classes :type-prescription))

 (thm (implies (<= 0 x) (equal (foo x) t)))
|#

; If we simply use true-type-alist here, we'll lose the information that (< 0
; arg2).  That is, we desire that the true-type-alist is sufficient for
; deducing what we are assuming true; but if arg2 can be a complex number, we
; will not be able to make that determination.  So, we put this inequality on
; the type-alist, explicitly.  We do so in the order shown for two reasons,
; probably neither of them particularly important (but at least, we document
; what they are).  For one, we want type-set to find the explicit inequality
; first, in case it ever tries to decide it.  Although we do not expect
; type-set to have any trouble even if we bury the inequality after an entry
; for arg2, this coding seems more robust.  More importantly, however, we want
; to call extend-type-alist, which is a bit complicated, on as short a
; type-alist as possible.

; End old comment regarding the case that (ts-intersectp ts2
; *ts-complex-rational*).

                       (mv-atf-2 not-flg true-type-alist false-type-alist
                                 (fcons-term* '< *0* arg2)
                                 xnot-flg x)))))
                  ((equal arg2 *0*)
                   (cond
                    ((ts-subsetp ts1
                                 *ts-negative-rational*)
                     (mv-atf not-flg t nil type-alist nil))
                    ((ts-subsetp ts1
                                 (ts-union (ts-complement *ts-acl2-number*)
                                           *ts-non-negative-rational*))
                     (mv-atf not-flg nil t nil type-alist))
                    (t
                     (let* ((true-type-alist
                             (extend-type-alist
                              arg1
                              (ts-intersection
                               ts1
                               (ts-union *ts-negative-rational*
                                         *ts-complex-rational*))
                              type-alist))
                            (false-type-alist
                             (extend-type-alist
                              arg1
                              (ts-intersection
                               ts1 (ts-complement
                                    *ts-negative-rational*))
                              type-alist)))
                       (mv-atf-2 not-flg true-type-alist false-type-alist
                                 (fcons-term* '< arg1 *0*)
                                 xnot-flg x)))))
                  (t (mv-let
                      (mbt mbf tta fta)
                      (assume-true-false1
                       xnot-flg ; = not-flg
                       x ; = (fcons-term* '< arg1 arg2)

; Once upon a time we had (fcons-term* '< arg1 arg2), above, instead of x.
; But we claim that not-flg is xnot-flg and that arg1 and arg2 are the
; corresponding arguments of x so that x is equal to (fcons-term* '< arg1 arg2).
; The proof is as follows.  We are in the t clause of a cond.  The preceding
; tests establish that neither arg1 nor arg2 is *0* here.  Hence, by
; Foreshadow 2 above we conclude that not-flg, arg1 and arg2 are
; unchanged from their values at Foreshadow 1.  But at Foreshadow 1 we
; see that if neither arg is *0* not-flg is xnot-flg and arg1 and arg2 are
; the corresponding components of x.  Q.E.D.

                       type-alist ancestors ens w nnn)

; Inefficiency: It is somewhat troubling that we are holding ts1 and
; ts2 in our hands while invoking assume-true-false1 on (< arg1 arg2),
; knowing full-well that it will recompute ts1 and ts2.  Sigh.  It
; would be nice to avoid this duplication of effort.

; PSIM test:  The comment above will not apply to Paco because of memoization.

; We could now return (mv mbt mbf tta fta) as the answer.  But, in the
; case that mbt and mbf are both nil we want to tighten up the returned
; type-alists a little if we can.  Suppose we are dealing with (< a1 a2) and a1
; is known to be positive.  Then a2 is (even more) positive.  We can add that
; to the tta, if it changes the type-set of a2.

                      (cond
                       ((or mbt mbf)

; Just return the already computed answers if we've settled the
; question.

                        (mv mbt mbf tta fta))
                       (t (let ((tta
                                 (assume-true-false-<
                                  not-flg
                                  arg1 arg2 ts1 ts2 tta))
                                (fta
                                 (assume-true-false-<
                                  (not not-flg)
                                  arg1 arg2 ts1 ts2 fta)))
                            (mv nil nil tta fta))))))))))))))
        ((or (eq (ffn-symb x) 'car)
             (eq (ffn-symb x) 'cdr))

; In this comment we assume (ffn-symb x) is car but everything we say is true
; for the cdr case as well.  Suppose xnot-flg is nil.  Then after the
; assume-true-false1 below, tta is the result of assuming (car arg) non-nil.
; But if (car arg) is non-nil, then arg is non-nil too.  That is, (implies (car
; arg) arg) is a theorem: Pf.  Consider the contrapositive, (implies (not arg)
; (not (car arg))). Q.E.D.  So we assume arg onto tta as well as (car arg).
; Fta, on the other hand, is the result of assuming (car arg) nil.  That tells
; us nothing about arg, e.g., arg could be nil, a cons (whose car is nil) or
; anything violating car's guard.  Summarizing this case: if xnot-flg is nil,
; then we assume both (car arg) and arg non-nil onto tta and assume only (car
; arg) nil onto fta.

; Now on the other hand, suppose xnot-flg is t.  Then tta contains
; the assumption that (car arg) is nil and fta contains the
; assumption that (car arg) is non-nil.  We can add to fta the
; assumption that arg is non-nil.  Observe that the two cases are
; symmetric if we simply swap the role of tta and fta before we start
; and after we are done.  The first swap is done by the let below.
; The second is done by mv-atf.

         (mv-let (mbt mbf tta fta)
                 (assume-true-false1
                  xnot-flg x type-alist ancestors ens w nnn)
                 (cond ((or mbt mbf)
                        (mv mbt mbf tta fta))
                       (t (let ((tta (if xnot-flg fta tta))
                                (fta (if xnot-flg tta fta)))
                            (mv-let (mbt1 mbf tta1 fta1)
                                    (assume-true-false
                                     (fargn x 1) tta ancestors ens w nnn)
                                    (declare (ignore mbt1 fta1))
                                    (mv-atf xnot-flg mbt mbf tta1 fta)))))))
        (t (assume-true-false1 xnot-flg x type-alist
                               ancestors ens w nnn))))))))

(defun assume-true-false1 (not-flg x type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count x) 11 0)))

; Roughly speaking, this is the simple assume-true-false, which just
; computes the type-set of x and announces that x must be t, must be
; f, or else announces neither and creates two new type-alists with x
; bound to its type minus *ts-t* and to *ts-nil*.  It returns the
; standard 4 results of assume-true-false.

  (let ((ts (type-set x type-alist ancestors ens w nnn)))
    (cond ((ts= ts *ts-nil*)
           (mv-atf not-flg nil t nil type-alist))
          ((not (ts-intersectp ts *ts-nil*))
           (mv-atf not-flg t nil type-alist nil))
          (t
           (mv-atf not-flg nil nil
                   (extend-with-proper/improper-cons-ts-tuple
                    x
                    (ts-intersection ts *ts-non-nil*)
                    type-alist ancestors type-alist ens w nnn)
                   (extend-type-alist x *ts-nil* type-alist))))))

(defun proper/improper-cons-ts-tuple (term ts type-alist ancestors ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count term) 9 0)))

; We return a tuple of the form (mv term' ts') that asserts the
; assumption that term has type set ts.  Most often, term' and ts' are
; just term and ts, i.e., the function is the identity.  However, if
; term is of the form (cons a x) we do certain auxiliary processing
; related to the existence of *ts-true-list* and its subtypes.

; We make various implicit assumptions about term and ts, all
; summarized by the restriction that this function can only be called
; by assume-true-false after checking the current type-set of term and
; failing to decide the question.

; We start with two examples.  Suppose term is (cons a1 x) and ts is
; *ts-true-list*.  Then the "various implicit assumptions" are
; violated because assume-true-false would never ask us to do this:
; the type-set of term is, at worst, the union of *ts-proper-cons* and
; *ts-improper-cons*, and certainly doesn't include *ts-nil*.  But
; assume-true-false always asks us to assume a type-set that is a
; subset of the current type-set.

; So suppose we are asked to assume that (cons a1 x) is of type
; *ts-proper-cons*.  Then we can deduce that x is of type
; *ts-true-list*.  Indeed, these two are equivalent because if we
; store the latter we can compute the former with type-set.  But
; because x is a subterm of (cons a1 x) we prefer to store the
; assumption about x because it will find greater use.  However, we
; may already know something about the type of x.  For example, x may
; be known to be non-nil.  So we are obliged to intersect the old type
; of x with the newly derived type if we want to keep maximizing what
; we know.  Because of the "implicit assumptions" this intersection
; will never produce the empty type set: if it is impossible for x to
; have the required type, then assume-true-false better not ask us to
; make the assumption.  For example, if x is known not to be a
; true-list, then assume-true-false would never ask us to assume that
; (cons a1 x) is proper.

; The example above is based on the theorem
;    (proper-consp (cons a1 x))   <-> (true-listp x).
; We similarly build in the theorem
;    (improper-consp (cons a1 x)) <-> (not (true-listp x)).

  (cond
   ((and (nvariablep term)
         (not (fquotep term))
         (eq (ffn-symb term) 'cons)
         (or (ts= ts *ts-proper-cons*)
             (ts= ts *ts-improper-cons*)))
    (let* ((x (non-cons-cdr term)))

; Can x be an explicit value?  If it can, then we'd be in trouble because
; we return a type-alist binding that sets the value of x.  But in fact
; x cannot be an explicit value.  If it were, then assume-true-false
; would have decided whether (cons a x) was proper or improper.

      (let ((tsx (type-set x type-alist ancestors ens w nnn)))
        (cond
         ((ts= ts *ts-proper-cons*)
          (mv x (ts-intersection tsx *ts-true-list*)))
         (t
          (mv x (ts-intersection tsx (ts-complement *ts-true-list*))))))))
   (t (mv term ts))))

(defun extend-with-proper/improper-cons-ts-tuple
  (term ts type-alist ancestors type-alist-to-be-extended ens w nnn)

  (declare (xargs :measure (lex4 nnn (acl2-count term) 10 0)))

; Programming Note:

; Our convention is to call this function to extend the type-alist
; unless we know that the supplied ts is neither *ts-proper-cons* nor
; *ts-improper-cons*.  That is, we use this function to construct
; type-alist entries in only some of the cases.  See also
; extend-type-alist-simple and extend-type-alist.

  (mv-let (term ts)
          (proper/improper-cons-ts-tuple term ts type-alist
                                         ancestors ens w nnn)
          (extend-type-alist term ts type-alist-to-be-extended)))

)

(defun type-set-lst (x type-alist ancestors ens w nnn)

; This function computes the type-set of each element of x and returns
; the corresponding list of type-sets.

  (cond
   ((endp x) nil)
   (t (cons (type-set (car x) type-alist ancestors ens w nnn)
            (type-set-lst (cdr x) type-alist ancestors ens w nnn)))))

; This is a completely arbitrary limitation on type-set.  The nnn argument
; limits
; (1) The number of times we can expand a lambda application or a
;     non-rec function in type-set;
; (2) The depth of backchaining in relieving the hyps of type-prescription
;     rules;

; However, (2) is a little misleading because we decrement nnn twice
; in a certain backchaining step.  After the unification of the term
; with a rule's pattern, we create a type-alist pairing the variables
; in the rule with the types of the instantiations of those variables.
; We decrement nnn once when we call the function,
; extend-type-alist-with-bindings, since the alist over which we are
; recursing can be arbitrarily long -- it is a function of the rule.
; Then, when we compute the type-set of each instantiation, we
; decrement nnn again, as though the instantiation could be
; arbitrarily big.  In fact, each instantiation is a subterm of the
; original term and hence strictly smaller.  But proving that they are
; smaller would require proving a theorem about one-way-unify.  Rather
; than do that, we just tick nnn.  So with a small nnn we might get
; *ts-unknown* contributions to the type-sets of the instantiations on
; big terms, even though in principle we need not.  In addition, we
; decrement nnn when we get the type of a hypothesis and when we get
; the types of the variables that the type-prescription rule lists.

(defconst *type-set-nnn* 30)

; ---------------------------------------------------------------------------
; Section:  Elementary Uses of Type-Sets

; Next we develop the idea of type-alist-clause, which converts a
; clause to a type-alist.  The Paco version of this is much simpler
; than ACL2's.  ACL2 is concerned with ordering equivalence relations
; so that it is complete on chains of equalities, tracks the
; dependencies of type-alist entries on literals so we don't have to
; reprocess the same clause subsets repeatedly, and takes care to
; process the resulting type-alist in a way that reduces the
; dependence on the order of the literals in the clause.

(defun type-alist-clause (cl type-alist ens wrld)

; We construct an extension of type-alist in which every literal of cl
; is assumed false.  We return two values.  The first is t or nil and
; indicates whether we found a contradiction, i.e., that some literal
; of cl is true.  The second is the resulting type-alist (or nil if we
; got a contradiction).

  (cond ((endp cl) (mv nil type-alist))
        (t (mv-let
            (mbt mbf tta fta)
            (assume-true-false (car cl)
                               type-alist
                               nil
                               ens
                               wrld
                               *type-set-nnn*)
            (declare (ignore tta))
            (cond
             (mbt (mv t nil))
             (mbf (type-alist-clause (cdr cl) type-alist ens wrld))
             (t (type-alist-clause (cdr cl) fta ens wrld)))))))

(defun known-whether-nil (x type-alist ens wrld)

; This function determines whether we know, from type-set reasoning,
; whether x is nil or not.  It returns two values.  The first is the
; answer to the question "Do we know whether x is nil or not?"  If the
; answer to that question is yes, the second value is the answer to
; the question "Is x nil?"  If the answer to the first question is no,
; the second value is nil.

  (cond ((quotep x)
         (mv t (equal x *nil*)))
        (t (let ((ts (type-set x type-alist nil ens wrld *type-set-nnn*)))
             (cond ((ts= ts *ts-nil*)
                    (mv t t))
                   ((ts-intersectp ts *ts-nil*)
                    (mv nil nil))
                   (t (mv t nil)))))))

(defun ts-booleanp (term type-alist ens wrld)
  (ts-subsetp (type-set term type-alist nil ens wrld *type-set-nnn*)
              *ts-boolean*))

(defun weak-cons-occur (x y)

; Both x and y are terms.  In addition, x is known to be non-quoted
; and not a CONS expression.  Consider the binary tree obtained by
; viewing the term y as a CONS tree.  We return t iff x is a tip of
; that tree.

  (cond ((variablep y) (eq x y))
        ((fquotep y) nil)
        ((eq (ffn-symb y) 'cons)
         (or (weak-cons-occur x (fargn y 1))
             (weak-cons-occur x (fargn y 2))))
        (t (equal x y))))

(defun equal-x-cons-x-yp (lhs rhs)

; We answer the question ``Is (EQUAL lhs rhs) definitely nil?''  If
; our result is t, then the equality is definitely nil, without
; further qualification.  If we say we don't know, i.e., nil, nothing
; is claimed.

; However, we know some things about lhs and rhs that allow us to
; make this function answer ``I don't know'' more quickly and more
; often than it might otherwise.  We assume tht lhs and rhs are not
; identical terms and we know they are not both quoted constants
; (though either may be) and we know that their type sets have a
; non-empty intersection.

; We make our positive decision based on structural reasoning.  For
; example, (EQUAL x (CONS x &)), is NIL because x occurs properly
; within the CONS tree.  This observation does not depend on type-sets or
; anything else.

; However, we don't want to do too much work exploring the two terms.
; For example, if they are both large explicit values we don't want to
; look for them in eachother.  We know that we will eventually apply
; the CONS-EQUAL axiom, which will rewrite the equality of two conses
; (constants or otherwise) to the conjoined equalities of their
; components.  Thus, if both lhs and rhs are CONS expressions (i.e., a
; consityp) or quoted list constants, we just return nil and let the
; :REWRITE rules take care of it.

; One more minor optimization: if one of our args is a consityp and
; the other is a quoted constant then the constant must be a consp or
; else the type sets wouldn't intersect.

  (cond ((variablep lhs)
         (cond ((consityp rhs)
                (or (weak-cons-occur lhs (fargn rhs 1))
                    (weak-cons-occur lhs (fargn rhs 2))))
               (t nil)))
        ((fquotep lhs) nil)
        ((eq (ffn-symb lhs) 'cons)
         (cond ((variablep rhs)
                (or (weak-cons-occur rhs (fargn lhs 1))
                    (weak-cons-occur rhs (fargn lhs 2))))
               ((fquotep rhs) nil)
               ((eq (ffn-symb rhs) 'cons) nil)
               (t (or (weak-cons-occur rhs (fargn lhs 1))
                      (weak-cons-occur rhs (fargn lhs 2))))))
        ((consityp rhs)
         (or (weak-cons-occur lhs (fargn rhs 1))
             (weak-cons-occur lhs (fargn rhs 2))))
        (t nil)))

(defun not-ident (term1 term2 type-alist ens wrld)

; We return t iff (equal term1 term2) is false.

  (cond ((and (quotep term1)
              (quotep term2))
         (not (equal term1 term2)))
        (t (let ((ts1 (type-set term1 type-alist nil ens wrld *type-set-nnn*))
                 (ts2 (type-set term2 type-alist nil ens wrld *type-set-nnn*)))
             (cond
              ((not (ts-intersectp ts1 ts2))
               t)
              ((equal-x-cons-x-yp term1 term2)
               t)
              (t nil))))))

; ---------------------------------------------------------------------------
; Section:  IF-Normalization

(defun first-if (args i)

; This function searches the top level of the list args for an
; top-level IF expression.  If it does not find one, it returns
; 2 nils.  Otherwise, it returns the position of the first one
; it finds and the IF expression found.

  (cond ((endp args) (mv nil nil))
        ((and (nvariablep (car args))
              (not (quotep (car args)))
              (eq (ffn-symb (car args)) 'if))
         (mv i (car args)))
        (t (first-if (cdr args) (1+ i)))))

; We are headed toward the function normalize, which produces a term
; in IF-normal form.  The ACL2 version of this function is problematic
; to admit because it is both mutually recursive and reflexive.  The
; reflexivity comes about because after normalizing alpha in (if alpha
; beta gamma) and getting (if (if a1 a2 a3) beta gamma), we normalize
; (if a1 (if a2 beta gamma) (if a3 beta gamma)).  The reason we have
; to normalize alpha to see the IF is that it might be buried in a
; function call, e.g., (if (foo (if a1 a2 a3)) beta gamma).  After
; spending a while trying to admit the function I punted and recode it
; so that it is not reflexive.  But now it makes several passes.  The
; basic algorithm is: distribute all IFs and then reduce by exploiting
; tests.  To distribute IFs, I distribute IFs in all args
; independently and then create an IF-distributed function
; application.

; We now define the function reduce, which takes a term in which the
; IFs have been completely distributed and simplifies it by using the
; assumptions of the tests in the branches.  Thus, for example, (IF A
; B A) is reduced to (IF A B NIL).

(defun reduce-with-type-set (term iff-flg type-alist ens wrld)
  (let ((ts (type-set term type-alist nil ens wrld *type-set-nnn*)))
    (cond ((ts-intersectp ts *ts-nil*)
           (cond ((ts= ts *ts-nil*) *nil*)
                 (t term)))
          (iff-flg *t*)
          ((ts= ts *ts-t*) *t*)
          ((ts= ts *ts-zero*) *0*)
          (t term))))

(defun cons-term-if (t1 t2 t3 iff-flg type-alist ens wrld)
  (cond ((equal t1 *t*) t2)
        ((equal t1 *nil*) t3)
        ((equal t2 t3) t2)
        ((and (equal t1 t2)
              (equal t3 *nil*))
         t1)
        ((and (equal t2 *t*)
              (equal t3 *nil*))
         (cond
          (iff-flg t1)
          ((ts-booleanp t1 type-alist ens wrld) t1)
          (t (fcons-term* 'if t1 t2 t3))))
        (t (fcons-term* 'if t1 t2 t3))))

(defun cons-term-equal (t1 t2)
  (cond ((equal t1 t2) *t*)
        ((and (quotep t1) (quotep t2)) *nil*)
        (t (fcons-term* 'equal t1 t2))))

(defun reduce (term iff-flg type-alist ens wrld recursivep)
  (declare (xargs :hints (("Goal" :in-theory (disable assume-true-false)))))
  (cond
   ((variablep term)
    (reduce-with-type-set term iff-flg type-alist ens wrld))
   ((fquotep term)
    (if iff-flg
        (if (equal term *nil*) *nil* *t*)
      term))
   ((eq (ffn-symb term) 'IF)
    (if recursivep
        (let ((t1 (fargn term 1)))
          (mv-let
           (mbt mbf tta fta)
           (assume-true-false t1 type-alist nil ens wrld *type-set-nnn*)
           (cond
            (mbt (reduce (fargn term 2) iff-flg type-alist ens wrld t))
            (mbf (reduce (fargn term 3) iff-flg type-alist ens wrld t))
            (t (let ((t2 (reduce (fargn term 2) iff-flg tta ens wrld t))
                     (t3 (reduce (fargn term 3) iff-flg fta ens wrld t)))
                 (cons-term-if t1 t2 t3
                               iff-flg type-alist ens wrld))))))
      term))
   ((or iff-flg
        (eq (ffn-symb term) 'NOT)
        (<reduce-id>
         (most-recent-enabled-recog-tuple
          (ffn-symb term)
          (global-val 'recognizer-alist wrld)
          ens))
        (eq (ffn-symb term) 'EQUAL)
        (eq (ffn-symb term) '<))
    (mv-let (mbt mbf tta fta)
            (assume-true-false term type-alist nil ens wrld *type-set-nnn*)
            (declare (ignore tta fta))
            (cond
             (mbt *t*)
             (mbf *nil*)

; If assume-true-false doesn't categorize this term, we assume that
; reduce-with-type-set wouldn't either.  Is it possible that
; type-set knows more about some terms of the above shape than
; assume-true-false?

             (t term))))
   (t (reduce-with-type-set term iff-flg type-alist ens wrld))))

; Now we define distribute-ifs, which distributes the IFs in a term.

(defthm acl2-count-subst-for-nth
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len args))
                (< (acl2-count new-arg) (acl2-count (nth i args))))
           (< (acl2-count (subst-for-nth new-arg i args))
              (acl2-count args)))
  :rule-classes :linear)

(defthm bounds-on-mv-nth-0-first-if-gen
  (implies (and (integerp z)
                (<= 0 z)
                (car (first-if args z)))
           (and (integerp (car (first-if args z)))
                (<= 0 (car (first-if args z)))
                (< (car (first-if args z)) (+ (len args) z))
                (<= z (car (first-if args z)))))
  :rule-classes nil)

(defthm mv-nth-0-first-if-type-prescription
  (implies (and (integerp z)
                (<= 0 z))
           (or (null (car (first-if args z)))
               (and (integerp (car (first-if args z)))
                    (<= 0 (car (first-if args z))))))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance bounds-on-mv-nth-0-first-if-gen))))

(defthm bounds-on-mv-nth-0-first-if-linear1
  (implies (car (first-if args 0))
           (< (car (first-if args 0)) (len args)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance bounds-on-mv-nth-0-first-if-gen (z 0)))))

(defthm bounds-on-mv-nth-0-first-if-linear2
  (implies (and (integerp z)
                (<= 0 z)
                (car (first-if args z)))
           (<= z (car (first-if args z))))
  :hints (("Goal" :use bounds-on-mv-nth-0-first-if-gen))
  :rule-classes :linear)

(include-book "arithmetic/top-with-meta" :dir :system)

(defthm mv-nth-1-first-if-gen
  (implies (and (integerp z)
                (<= 0 z)
                (car (first-if args z)))
           (equal (MV-NTH 1 (FIRST-IF ARGS z))
                  (nth (- (car (first-if args z)) z)
                       args))))

(defthm consp-nth-mv-nth-0-first-if-gen
  (implies (and (integerp z)
                (<= 0 z)
                (car (first-if args z)))
           (consp (nth (- (car (first-if args z)) z)
                       args)))
  :rule-classes nil)

(defthm consp-nth-mv-nth-0-first-if
  (implies (car (first-if args 0))
           (consp (nth (car (first-if args 0))
                       args)))
  :hints (("Goal" :use (:instance consp-nth-mv-nth-0-first-if-gen (z 0)))))

(defthm acl2-count-caddr
  (implies (consp x)
           (< (acl2-count (caddr x)) (acl2-count x))))

(defun dcons-term (fn args type-alist ens wrld)

; Distributed cons-term: Distribute the IFs in the args as you build
; (fn . args).

  (declare (xargs :measure (acl2-count args)
                  :hints (("Goal" :in-theory (disable assume-true-false)))))

  (cond
   ((and (eq fn 'IF)
         (not (and (nvariablep (car args))
                   (not (fquotep (car args)))
                   (eq (ffn-symb (car args)) 'IF))))

; We could reduce the following expression.  The test, (car args), has
; not been assumed true/false for the two branches -- they were
; distributed independently.  But if we dive here, then we dive
; repeatedly.  I think it is best to do a single reducion from the
; top.

    (cons-term-if (car args) (cadr args) (caddr args)
                  nil type-alist ens wrld))
   (t
    (mv-let
     (n if-expr)
     (first-if args 0)
     (cond
      ((null n)

; There is no IF at the top-level of term, and since all the args are
; distributed, we know there are no IFs at all.  We are thus at the
; bottom of the IF tree and type-alist has on it everything we know.

       (cond ((equal fn 'EQUAL)
              (cons-term-equal (car args) (cadr args)))
             ((equal fn 'IF)
              (cons-term-if (car args) (cadr args) (caddr args)
                            nil type-alist ens wrld))
             (t (cons-term fn args))))

; And here is the code after which this function was named.  We have
; found an if-expr in the args of term at location n.  Since that if
; is in normal form, its test is not an if.  We split on that test and
; distribute the if and continue developing the two branches.  Since
; the type-alist may change as we go but the IF expressions were all
; distributed in advance, their tests may be known in the current
; type-alist.

      (t (let ((t1 (fargn if-expr 1)))
           (mv-let
            (mbt mbf tta fta)
            (assume-true-false t1 type-alist nil ens wrld *type-set-nnn*)
            (cond
             (mbt
              (dcons-term
               fn
               (subst-for-nth (fargn if-expr 2) n args)
               type-alist ens wrld))
             (mbf
              (dcons-term
               fn
               (subst-for-nth (fargn if-expr 3) n args)
               type-alist ens wrld))
             (t
              (let ((t2
                     (dcons-term
                      fn
                      (subst-for-nth (fargn if-expr 2) n args)
                      tta ens wrld))
                    (t3
                     (dcons-term
                      fn
                      (subst-for-nth (fargn if-expr 3) n args)
                      fta ens wrld)))
                (cons-term-if t1 t2 t3 nil type-alist ens wrld))))))))))))

(mutual-recursion

(defun distribute-ifs (term iff-flg type-alist ens wrld)

  (declare (xargs :measure (acl2-count term)
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory
                           (disable assume-true-false
                                    type-set)))))

; This function distributes IFs in term, simplifying with type-set
; reasoning as it goes.  We return a term equivalent to term
; (propositionally equivalent, if the iff-flg is t) under the
; assumptions in type-alist.

  (cond
   ((variablep term)
    (reduce-with-type-set term iff-flg type-alist ens wrld))
   ((fquotep term)
    (cond ((and iff-flg (not (equal term *nil*))) *t*)
          (t term)))
   ((flambda-applicationp term)
    (let* ((dargs (distribute-ifs-lst (fargs term) nil type-alist ens wrld))
           (dbody (distribute-ifs
                   (lambda-body (ffn-symb term))
                   iff-flg
                   (zip-variable-type-alist
                    (lambda-formals (ffn-symb term))
                    (type-set-lst dargs
                                  type-alist
                                  nil
                                  ens
                                  wrld
                                  *type-set-nnn*))
                   ens wrld)))

; We distribute IFs in the args and body of the lambda, but we do not
; expand the lambda.

      (fcons-term (list 'lambda (lambda-formals (ffn-symb term)) dbody)
                  dargs)))
   (t
    (dcons-term (ffn-symb term)
                (distribute-ifs-lst (fargs term)
                                    (if (eq (ffn-symb term) 'IF)
                                        (if iff-flg
                                            t
                                          'IF)
                                      nil)
                                    type-alist ens wrld)
                type-alist ens wrld))))

(defun distribute-ifs-lst (args iff-flg type-alist ens wrld)

  (declare (xargs :measure (acl2-count args)))

; The handling of the iff-flg is unusual here.  Normally the flag is
; either nil or t.  Here it can also take the value IF.  When it is
; IF, the first element of args is distributed with iff-flg = t and
; all others are distributed with iff-flg nil.

  (cond ((endp args) nil)
        (t (cons (distribute-ifs (car args)
                                 (if (eq iff-flg 'IF) t iff-flg)
                                 type-alist ens wrld)
                 (distribute-ifs-lst (cdr args)
                                     (if (eq iff-flg 'IF) nil iff-flg)
                                     type-alist ens wrld)))))

)

(defun normalize (term iff-flg type-alist ens wrld)
  (reduce (distribute-ifs term iff-flg type-alist ens wrld)
          iff-flg type-alist ens wrld t))

; For an interesting test of normalization see normalize-test.lisp.
; For that test, at least, Paco peformed about 10 times better than
; ACL2!  But theorem proving performance measuring is notoriously
; unpredictive of actual behavior because of the variability of
; performance across different combinatoric cases.


