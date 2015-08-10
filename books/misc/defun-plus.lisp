(in-package "ACL2")

;; Copyright Nathan Wetzler and David Rager.

;; ============================================================================
;; Introductions
;;
;; This file defines defun+, which is a macro for defun that allows the user to
;; specify an "output signature" as part of a function's definition.  It works
;; by defining the function as if the output signature did not exist, and then
;; defining a theorem that describes the value[s] returned by calling the
;; function.  The user may optionally pass in an argument :disable, which
;; indicates whether the function should be disabled after the theorem stating
;; the output type is proved.
;;
;; See the end of the file for ideas on how to further extend defun+.
;; ============================================================================

;; ============================================================================
;; The following definitions related to gathering declarations are taken from
;; the ACL2 source code.  The only changes (as of August 2012) is the removal
;; of the guards and defining these functions in program mode.  These changes
;; are necessary, because :output is not one of the fields allowed in an xargs
;; declaration, as tested by ACL2 function plausible-dclsp.
;; ============================================================================

(defun strip-dcls-program-mode1 (fields lst)
  (declare (xargs :mode :program))
  (cond ((endp lst) nil)
        ((member-eq (caar lst) '(type ignore ignorable))
         (cond ((member-eq (caar lst) fields)
                (strip-dcls-program-mode1 fields (cdr lst)))
               (t (cons (car lst) (strip-dcls-program-mode1 fields (cdr lst))))))
        (t
         (let ((temp (strip-keyword-list fields (cdar lst))))
           (cond ((null temp) (strip-dcls-program-mode1 fields (cdr lst)))
                 (t (cons (cons 'xargs temp)
                          (strip-dcls-program-mode1 fields (cdr lst)))))))))

(defun strip-dcls-program-mode (fields lst)
  (declare (xargs :mode :program))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (cond ((member-eq 'comment fields)
                (strip-dcls-program-mode fields (cdr lst)))
               (t (cons (car lst)
                        (strip-dcls-program-mode fields (cdr lst))))))
        (t (let ((temp (strip-dcls-program-mode1 fields (cdar lst))))
             (cond ((null temp) (strip-dcls-program-mode fields (cdr lst)))
                   (t (cons (cons 'declare temp)
                            (strip-dcls-program-mode fields (cdr lst)))))))))

(defun fetch-dcl-fields-program-mode2 (field-names kwd-list acc)
  (declare (xargs :mode :program))
  (cond ((endp kwd-list) acc)
        (t (let ((acc (fetch-dcl-fields-program-mode2 field-names
                                                      (cddr kwd-list)
                                                      acc)))
             (if (member-eq (car kwd-list) field-names)
                 (cons (cadr kwd-list) acc)
               acc)))))

(defun fetch-dcl-fields-program-mode1 (field-names lst)
  (declare (xargs :mode :program))
  (cond ((endp lst) nil)
        ((member-eq (caar lst) '(type ignore ignorable))
         (if (member-eq (caar lst) field-names)
             (cons (cdar lst)
                   (fetch-dcl-fields-program-mode1 field-names (cdr lst)))
           (fetch-dcl-fields-program-mode1 field-names (cdr lst))))
        (t (fetch-dcl-fields-program-mode2 field-names
                                           (cdar lst)
                                           (fetch-dcl-fields-program-mode1
                                            field-names
                                            (cdr lst))))))

(defun fetch-dcl-fields-program-mode (field-names lst)
  (declare (xargs :mode :program))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (if (member-eq 'comment field-names)
             (cons (car lst)
                   (fetch-dcl-fields-program-mode field-names (cdr lst)))
           (fetch-dcl-fields-program-mode field-names (cdr lst))))
        (t (append (fetch-dcl-fields-program-mode1 field-names (cdar lst))
                   (fetch-dcl-fields-program-mode field-names (cdr lst))))))

(defun fetch-dcl-field-program-mode (field-name lst)
  (declare (xargs :mode :program))
  (fetch-dcl-fields-program-mode (list field-name) lst))

;; ============================================================================
;; Some (more) helper functions for defun+
;; ============================================================================

(defun generate-output-lemma-name (name number)
  (if (not number)
      (intern-in-package-of-symbol
       (concatenate 'string (symbol-name name)
                    "-OUTPUT-LEMMA")
       name)
    (intern-in-package-of-symbol
     (concatenate 'string (symbol-name name)
                   "-OUTPUT-LEMMA-"
                   (coerce (explode-atom number 10)
                           'string))
     name)))

(defun generate-output-lemma-single (name guards output output-hints)
  `((defthm ,(generate-output-lemma-name name nil)
      (implies ,guards
               ,output)
      :hints ,output-hints)))

(defun generate-output-lemma-multiple (name guards output number)
  (if (atom output)
      nil
    (cons `(defthm ,(generate-output-lemma-name name number)
               (implies ,guards
                        ,(car output)))
            (generate-output-lemma-multiple name
                                            guards
                                            (cdr output)
                                            (1+ number)))))

(defun generate-output-lemmas (name guards output output-hints)
  (if (not (equal (car output) 'and))
      (generate-output-lemma-single name guards output output-hints)
    (generate-output-lemma-multiple name guards (cdr output) 1)))

;; ============================================================================
;; Definition of defun+
;; ============================================================================

(defmacro defun+ (name formals dcl body &key disable)
  (let* ((guards (car (fetch-dcl-field-program-mode :guard (list dcl))))
         (output (car (fetch-dcl-field-program-mode :output (list dcl))))
         (output-hints (car (fetch-dcl-field-program-mode :output-hints (list dcl))))
         (new-dcls (car (strip-dcls-program-mode '(:output) (list dcl))))
         (new-dcls (car (strip-dcls-program-mode '(:output-hints) (list new-dcls)))))
    `(progn
       (defun ,name ,formals ,new-dcls ,body)
       ,@(if output
             (generate-output-lemmas name guards output output-hints)
           `((value-triple nil)))
       ,(if disable
           `(in-theory (disable ,name))
          '(value-triple nil)))))

;; ============================================================================
;; Some examples
;; ============================================================================

(local
 (defun+ baz (x y z)
   (declare (xargs :guard (and (integerp x)
                               (integerp y)
                               (integerp z))
                   :output (integerp (baz x y z))))
   (+ x y z)))

(local
 (defun+ baz (x y z)
   (declare (xargs :guard (and (integerp x)
                               (integerp y)
                               (integerp z))
                   :output (integerp (baz x y z))
                   :output-hints (("Goal" :do-not-induct t))))
   (+ x y z)))

(local
 (defun+ faz (x y z)
   (declare (xargs :guard (and (integerp x)
                               (integerp y)
                               (integerp z))
                   :output (integerp (faz x y z))))
   (+ x y z)
   :disable t))

(local
 (defun+ foo (x y)
   (declare (xargs :guard (and (integerp x) (integerp y))
                   :output (and (equal (mv-nth 0 (foo x y)) 0)
                                (integerp (mv-nth 1 (foo x y))))))
   (mv 0 (+ x y))
   :disable t))


;; ============================================================================
;; It would be nice to automatically generate lemmas about the functions.  For
;; example, it might be nice to define opener lemmas that hinge off the input
;; to a recursive function being a consp.  However, we think we could have a
;; more general approach to automatically generating lemmas.  As such, for now,
;; we leave the use of this code disabled.
;; ============================================================================

#||

(defmacro generate-lemma-names (fn1 fn2 &optional car-cdr)
  `(intern-in-package-of-symbol
    (concatenate 'string
                 (symbol-name ,fn1)
                 "-IMPLIES-"
                 (symbol-name ,fn2)
                 (if ,car-cdr
                     (concatenate 'string "-" (symbol-name ,car-cdr))
                   ""))
    ,fn1))

(defun generate-lemmas (name formals guards body)
  (declare (ignore formals guards))
  (case-match body
    (('if ('atom x)
         tbr
       (and (fbr-car ('car x))
            (!name ('cdr x))))
     (list `(defthm ,(generate-lemma-names name fbr-car 'car)
              (implies (and (,name ,x)
                            (consp ,x))
                       (,fbr-car (car ,x))))
           `(defthm ,(generate-lemma-names name name 'cdr)
              (implies (and (,name ,x)
                            (consp ,x))
                       (,name (cdr ,x))))))
    (& nil)))



(generate-lemmas 'foo
                 nil
                 nil
                 '(if (atom x)
                      (null x)
                    (and (bar (car x))
                         (foo (cdr x)))))

(defmacro defun+ (name formals dcl body &key disable generate-lemmas)
  (let* ((guards (car (fetch-dcl-field-program-mode :guard (list dcl))))
         (output (car (fetch-dcl-field-program-mode :output (list dcl))))
         (new-dcls (car (strip-dcls-program-mode '(:output) (list dcl)))))
    `(progn
       (defun ,name ,formals ,new-dcls ,body)
       ,@(if output
             (generate-output-lemmas name guards output)
           `((value-triple nil)))
       ,@(if generate-lemmas
            (generate-lemmas name formals guards body)
          `((value-triple nil)))
       ,(if disable
           `(in-theory (disable ,name))
          '(value-triple nil)))))

(defun barp (x) (declare (xargs :guard t)) (integerp x))

(defun+ foop (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (barp (car x))
         (foop (cdr x))))
  :generate-lemmas t)

||#

;; ============================================================================
;; Here are a couple more ideas on how to improve defun+.

;; Add some output to defun+ (and also suppress some of the output) that tells
;; the user the definitions of the lemmas that were produced.

;; Potentially add symbols to output lemma names so that users can quickly
;; identify when the output lemmas are being used by viewing the summary of a
;; proof attempt.  We are uncertain of the consequences of having the output
;; rules automatically generated, so having this extra mechanism for flagging
;; the automatic use of these lemmas, would help us figure out whether they can
;; cause problems.

;; Come up with a way of allowing hints for the output lemmas when there is
;; more than one output lemma.
;; ============================================================================