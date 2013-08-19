;; BOZO copyright stuff.

; h-if-report-raw.lisp
;
; This is a fancy tool for tracing which if-branches are followed throughout
; certain memoized functions.  This is CCL specific.  Jared pulled this out of
; memoize-raw.lisp since it doesn't really have much to do with memoization.

(in-package "ACL2")

(eval-when
 (:execute :compile-toplevel :load-toplevel)

 #-Clozure
 (error "h-if-report-raw.lisp is CCL specific."))


; Automatically clear the ignore-form-ht whenever we're about to compile a new
; function, and record the name of the new function we're going to compile.
; Wow, what a fancy trick this is -- you could probably implement something
; like a __function__ macro this way.  That would be nice to have in ACL2.

(defg *current-compiler-function* 'unknown)

(ccl::advise ccl::compile-named-function
             (when (and (consp ccl::arglist)
                        (consp (cdr ccl::arglist))
                        (consp (cddr ccl::arglist))
                        (symbolp (caddr ccl::arglist)))
               (clrhash *ignore-form-ht*)
               (setq *current-compiler-function* (caddr ccl::arglist))))


(defg *trace-if-compiler-macro* nil)

(defg *if-true-array*
  (make-array 2000
              :element-type '(integer -1 1152921504606846975)
              :initial-element -1))

(defg *if-false-array*
  (make-array 2000
              :element-type '(integer -1 1152921504606846975)
              :initial-element -1))

(declaim (type (simple-array (integer -1 1152921504606846975) (*))
               *if-true-array* *if-false-array*))



(defg *form-ht* (make-hash-table :test 'eq))
(declaim (hash-table *form-ht*))



(defg *if-counter* -1)
(declaim (type (integer -1 1152921504606846975) *if-counter*))



(defun if-report (&optional fn stream)

  "(IF-REPORT) prints information about the execution of every branch
  of every IF, COND, AND, OR, CASE, WHEN, and UNLESS form of every
  memoized/profiled function that was memoized with :WATCH-IFS
  non-NIL.  (IF-REPORT fn) prints the same information, but only about
  the given function name, FN."

  (compute-calls-and-times)
  (let ((*print-level* 4)
        (*print-length* 4)
        (*print-pretty* t)
        last-fn n (ifs-found 0) (if-true 0) (if-false 0)
        (not-called 0)
        (called 0))
    (when (>= *if-counter* 0)
      (format stream "~2%Report on IF branches taken.")
      (let ((form-ar (make-array (the fixnum (1+ *if-counter*))
                                 :initial-element 0)))
        (declare (type (simple-array t (*)) form-ar))
        (maphash (lambda (k v) (declare (ignore k))
                   (when (or (null fn)
                             (eq (cadr v) fn))
                     (setf (aref form-ar (car v))
                           (cons (cddr v) (cadr v)))))
                 *form-ht*)
        (let ((top *if-counter*)
              ref)
          (declare (type fixnum top))
          (loop
           for i from 0 to top
           unless (eql 0 (setq ref (aref form-ar i)))
           do
           (let ((call (car ref))
                 (fn (cdr ref)))
             ;; ref has the form
             ;; (orig-call . function)
             (cond ((not (eq fn last-fn))
                    (setq n (number-of-calls fn))
                    (if (eq n 0)
                        (incf not-called)
                      (incf called))
                    (format stream "~2%~a was called ~a time~:P." fn n)
                    (setq last-fn fn)))
             (cond
              ((> n 0)
               (incf ifs-found)
               (cond
                ((eql 0 (aref *if-true-array* i))
                 (cond
                  ((eql 0 (aref *if-false-array* i))
                   (format stream "~%Neither branch of ~%~a~%was taken." call))
                  (t (incf if-true)
                     (format stream "~%The true branch of ~%~a~%was not taken." call))))
                ((eql 0 (aref *if-false-array* i))
                 (incf if-false)
                 (format stream "~%The false branch of ~%~a~%was not taken." call))
                (t (incf if-true) (incf if-false))))))))
        (format stream
                "~3%~:d ~10tnumber of functions called.~
              ~%~:d ~10tnumber of functions not called.~
              ~%~,2f% ~10tpercentage of functions called.~
              ~%~:d ~10tnumber of branches taken.~
              ~%~:d ~10tnumber of branches not taken.~
              ~%~,2f% ~10tpercentage of branches taken.
              ~%"
                called
                not-called
                (if (eql (+ called not-called) 0)
                    100
                  (* 100
                     (/ called
                        (float (+ called not-called)))))
                (+ if-true if-false)
                (- (* 2 ifs-found) (+ if-true if-false))
                (if (eql ifs-found 0)
                    100
                  (* 100
                     (float
                      (/ (+ if-true if-false)
                         (* 2 ifs-found))))))
        (format stream "~2%End of report on IF branches taken.~%")))))

(defun dump-if-report (&optional (out "if-report.text"))
  (with-open-file (stream
                   out
                   :direction :output
                   :if-exists :supersede)
    (if-report stream))
  "if-report.text")

; The compiler macro for IF in the Clozure Common Lisp sources circa 2008:

; (define-compiler-macro if (&whole call test true &optional false
;                                   &environment env)
;   (multiple-value-bind (test test-win) (nx-transform test env)
;     (multiple-value-bind (true true-win) (nx-transform true env)
;       (multiple-value-bind (false false-win) (nx-transform false env)
;         (if (or (quoted-form-p test) (self-evaluating-p test))
;           (if (eval test)
;             true
;             false)
;           (if (or test-win true-win false-win)
;             `(if ,test ,true ,false)
;             call))))))






(defmacro prinl (&rest r)

  "PRINL is for debugging.  In general, PRINL PRIN1s the members of r
  followed by their values to *STANDARD-OUTPUT*.  The values are first
  followed by =>, to indicate evaluation.

  For example, (prinl a b (+ a b)) might print:
    A => 1
    B => 2
    (+ A B) => 3
  PRINL returns the principal value of the last member of r.  PRINL
  does not evaluate the members of r that are neither symbols nor
  conses, but it does PRINC those members.  PRINL evalutes (oft ...)
  forms, but does not do the printing twice."

  (let ((tem (make-symbol "TEM"))
        (tem2 (make-symbol "TEM2")))
    `(our-syntax-nice
      (let ((,tem nil) (,tem2 nil))
        (declare (ignorable ,tem2))
        ,@(loop for x in r collect
                (cond
                 ((or (symbolp x)
                      (and (consp x) (not (eq (car x) 'oft))))
                  `(progn (format t "~&~:a =>~40t" ',x)
                          (setq ,tem ,x)
                          (cond ((integerp ,tem)
                                 (setq ,tem2 (ofn "~20:d" ,tem)))
                                ((floatp ,tem)
                                 (setq ,tem2 (ofn "~20,4f" ,tem)))
                                ((hash-table-p ,tem)
                                 (let ((l nil))
                                   (maphash (lambda (k v)
                                              (push (cons k v) l))
                                            ,tem)
                                   (setq l (nreverse l))
                                   (setq l (list* 'hash-table-size
                                                  (hash-table-size
                                                   ,tem)
                                                  l))
                                   (setq ,tem l)))
                                (t (setq ,tem2 (ofn "~a" ,tem))))
                          (cond ((and (stringp ,tem2)
                                      (< (length ,tem2) 40))
                                 (format t "~a" ,tem2))
                                (t (format t "~%  ")
                                   (prin1 ,tem *terminal-io*)))))
                 ((and (consp x) (eq (car x) 'oft)) x)
                 (t `(format t "~&~a" (setq ,tem ',x)))))
        ,tem))))

(defmacro very-very-unsafe-aref-incf (ar loc)
 `(setf (aref (the (simple-array mfixnum (*)) ,ar) ,loc)
        (the mfixnum (1+ (aref (the (simple-array mfixnum (*)) ,ar)
                              ,loc)))))



(defun setup-smashed-if ()

; SETUP-SMASHED-IF creates COMPILER-MACRO for IF and OR via calls of
; DEFINE-COMPILER-MACRO, stores the compiler macros, and restores the
; previous values.

  (let ((ccl::*nx-safety* 0)
        (ccl::*nx-speed* 3))

; Warning: In Clozure, (DEFINE-COMPILER-MACRO IF ...) 'seems' to do
; nothing, not even cause an error, if SAFETY=3.

; According to the ANSI standard, one is not supposed to mess with a
; compiler macro for any symbol in the Common Lisp package.  So the
; following hacking of the compiler macros for IF and OR is very
; dubious.  But it seemed easier than writing a code walker for all of
; Common Lisp, with its 50 or so special forms.  Our purpose this is
; to help get statistical performance information, and that is all
; that justifies this dangerous behavior.

 (when (and *unsmashed-if* (null *smashed-if*))
      (unwind-protect
        (progn

(define-compiler-macro if
  (&whole call test true &optional false &environment env)
  (declare (ignorable env))
  (when *trace-if-compiler-macro*
    (prinl call test true false))
  (let
    ((ans
      (cond
       ((gethash call *form-ht*)

; According to the ANSI standard, there is no guarantee that a Common
; Lisp compiler macro ever gets called!  We hope and believe that
; Clozure's compiler arranges that every IF forms gets processed by
; the compiler macro for IF so that we can 'IF-fix' it, when
; approriate.  A form in *FORM-HT* is an IF form that has been
; 'IF-fixed': both its true and false branch first increment a special
; counter for the the number of times that each branch is taken.  We
; do not want to 'IF-fix' again a form that has already been
; 'IF-fixed'; if it has, the new compiler macro for IF returns it as
; the answer.  Any caller of this compiler macro for IF will know, by
; the ANSI rules for compiler macros, not to hope for any further
; improvement on the form.  If an ordinary macro (not a compiler
; macro) returned its input, macro expansion would enter an immediate
; infinite loop.  It is lucky for us that Clozure translates COND and
; CASE into IF via macros.

        call)
       (t

; Although it may seem very hard to tell, we do closely follow the
; code for the compiler-macro for IF from the Clozure compiler.  See
; that code below.

        (multiple-value-bind (test test-win)
            (ccl::nx-transform test env)
        (multiple-value-bind (true true-win)
            (ccl::nx-transform true env)
        (multiple-value-bind (false false-win)
            (ccl::nx-transform false env)
          (cond
           ((or (ccl::quoted-form-p test)
                (ccl::self-evaluating-p test))
            (when *trace-if-compiler-macro*
              (prinl "IF test already settled"))
            (if (eval test) true false))
           ((gethash call *ignore-form-ht*)

; Forms in *IGNORE-FORM-HT* are not to be 'fixed' because they are
; part of the profiling machinery.  See the definition of PROFILER-IF
; and those macros that use PROFILER-IF, such as PROFILER-AND,
; PROFILER-OR, PROFILER-WHEN, and PROFILER-UNLESS.

            (when *trace-if-compiler-macro*
              (prinl "ignore case" test true false))
            (cond ((or test-win true-win false-win)
                   (let ((new `(if ,test ,true ,false)))

; We make ignorability contagious.

                     (setf (gethash new *ignore-form-ht*) t)
                     new))
                  (t call)))
           (t
            (incf *if-counter*)
            (when *trace-if-compiler-macro*
              (prinl "*IF-COUNTER* incremented"
                     call test true false))

; Our code here would be much simpler if in place of *IF-TRUE-ARRAY*
; and *IF-FALSE-ARRAY* we used two adjustable arrays and the function
; VECTOR-PUSH-EXTEND.  However, an adjustable array is not a
; SIMPLE-ARRAY, and so we possibly could lose efficiency, which we
; need when incrementing IF-branch counters.

            (when (>= *if-counter* (length *if-true-array*))
              (let ((ar (make-array
                         (+ (length *if-true-array*) 1000)
                         :element-type 'mfixnum
                         :initial-element -1)))
                (declare (type (simple-array mfixnum (*)) ar))
                (loop for i fixnum
                      below (length *if-true-array*)
                      do (setf (aref ar i)
                               (aref *if-true-array* i)))
                (setq *if-true-array* ar)))
            (when (>= *if-counter* (length *if-false-array*))
              (let ((ar (make-array (+ (length *if-false-array*)
                                       1000)
                                    :element-type 'mfixnum
                                    :initial-element -1)))
                (declare (type (simple-array mfixnum (*)) ar))
                (loop for i fixnum
                      below (length *if-false-array*)
                      do (setf (aref ar i)
                               (aref *if-false-array* i)))
                (setq *if-false-array* ar)))
            (setf (aref *if-true-array* *if-counter*) 0)
            (setf (aref *if-false-array* *if-counter*) 0)
            (let ((new-call `(if ,test
                                 (progn
                                   (very-very-unsafe-aref-incf
                                    *if-true-array*
                                    ,*if-counter*)
                                   ,true)
                               (progn
                                 (very-very-unsafe-aref-incf
                                  *if-false-array*
                                  ,*if-counter*)
                                 ,false))))

; The immediately preceding backquoted form is what we call the
; 'IF-fixing' of an expression.

              (when *trace-if-compiler-macro*
                (prinl new-call call))
              (setf (gethash new-call *form-ht*)
                    (list* *if-counter*
                           *current-compiler-function*
                           call))
              new-call))))))))))
    (when *trace-if-compiler-macro* (prinl ans))
    ans))
(setq *smashed-if* (compiler-macro-function 'if)))
(setf (compiler-macro-function 'if) *unsmashed-if*))

(unwind-protect
  (progn

; Apparently some times in CCL compilation, OR is not expanded to IF,
; so we force it here.

(define-compiler-macro or (&whole call &rest r &environment env)
  (declare (ignore r) (ignorable env))
  (cond ((null (cdr call)) nil)
        ((null (cddr call)) (cadr call))
        ((null (cdddr call))
         (cond ((atom (cadr call))
                `(if ,(cadr call)
                     ,(cadr call)
                   ,(caddr call)))
               (t (let ((v (gensym)))
                    `(let ((,v ,(cadr call)))
                       (if ,v ,v ,(caddr call)))))))
        (t (cond ((atom (cadr call))
                  `(if ,(cadr call) ,(cadr call) (or ,@(cddr call))))
                 (t (let ((v (gensym)))
                      `(let ((,v ,(cadr call)))
                         (if ,v ,v (or ,@(cddr call))))))))))

(setq *smashed-or* (compiler-macro-function 'or)))
(setf (compiler-macro-function 'or) *unsmashed-or*))

)))

