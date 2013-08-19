;; BOZO copyright stuff.

; h-casemacro-raw.lisp
;
; This is allegedly a sometimes-faster version of the Common Lisp CASE
; function.  Jared split this out of memoize-raw.lisp because it has nothing to
; do with memoization.

; [Jared]: I think this should be either (1) submitted to Gary and integrated
; into CCL, or (2) be moved into a ttag-based book so that it can be loaded if
; needed.  We shouldn't be mucking with stuff like this.  It's certainly got
; nothing to do with memoization.


(in-package "ACL2")

#+Clozure
(defmacro fixnum-case (key &body forms)
  ; For use only when key is a symbol known to hold a fixum.
  (multiple-value-bind (less-than-or-equal n greater-than)
    (splitable-case forms)
    (cond (less-than-or-equal
           `(cond ((< (the fixnum ,key) ,n)
                   (fixnum-case ,key ,@less-than-or-equal))
                  (t (fixnum-case ,key ,@greater-than))))
          (t (let ((key-var (gensym)))
               `(let ((,key-var (the fixnum ,key)))
                  (declare (ignorable ,key-var) (fixnum ,key-var))
                  (cond ,@(ccl::case-aux forms key-var nil nil))))))))

#+Clozure
(defun splitable-case (forms)
  (let ((l (length forms)))
    (cond
     ((and (> l 8)
           (loop for x in forms
                 always (and (consp x) (typep (car x) 'fixnum))))
      (let* ((c (sort (copy-list forms) #'< :key #'car))
             (h (floor l 2))
             (s (car (nth h c))))
        (loop for tail on c
              when (and (cdr tail) (eql (car tail) (cadr tail)))
              do (error "CASE: duplicate-keys: ~a." (car tail)))
        (values
         (loop for x in forms when (< (car x) s) collect x)
         s
         (loop for x in forms when (>= (car x) s) collect x)))))))


#+Clozure
(let ((ccl::*warn-if-redefine-kernel* nil))

  #+Clozure
  (defmacro case (key &body forms)

; A modification of the CCL DEFMACRO for CASE.

    "CASE Keyform {({(Key*) | Key} Form*)}* Evaluates the Forms in the
  first clause with a Key EQL to the value of Keyform. If a singleton
  key is T then the clause is a default clause."

    (multiple-value-bind (less-than-or-equal n greater-than)
                         (splitable-case forms)
                         (cond
                          (less-than-or-equal
                           (let ((key-var (gensym)))
                             `(let ((,key-var ,key))
                                (cond ((not (typep ,key-var 'fixnum)) nil)
                                      ((< (the fixnum ,key-var) ,n)
                                       (fixnum-case ,key-var ,@less-than-or-equal))
                                      (t (fixnum-case ,key-var ,@greater-than))))))
                          (t (let ((key-var (gensym)))
                               `(let ((,key-var ,key))
                                  (declare (ignorable ,key-var))
                                  (cond ,@(ccl::case-aux forms key-var nil nil)))))))))

