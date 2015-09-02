; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@aus.edsr.eds.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "bool-ops")

(set-state-ok t)

(program)

; This file deals with parsing a benchmark file into a list of the form

; (list input-vars
;       bindings1
;       output-vars1
;       bindings1
;       output-vars2)

(defmacro rf (file-name &optional name)
  (if name
      `(mv-let (erp val state)
	       (state-global-let*
                ((infixp nil))
                (read-file ,file-name state))
	       (if erp
		   (er soft 'rf "File ~p0 does not seem to exist."
		       ,file-name)
                 (assign ,name val)))
    `(state-global-let*
      ((infixp nil))
      (read-file ,file-name state))))

(defun trunc-lst (sym lst)
  (cond ((null lst) nil)
        ((eq sym (car lst)) nil)
        (t (cons (car lst) (trunc-lst sym (cdr lst))))))

(defconst *be-alist*
  '((not . not)
    (and . b-and)
    (or . b-or)
    (exor . b-xor)))

(mutual-recursion

 (defun convert-be-expr (expr)
   (cond ((atom expr) expr)
         ((null (cdr expr)) (convert-be-expr (car expr)))
         (t (case (car expr)
                  (not (list (cdr (assoc 'not *be-alist*))
                             (convert-be-expr (cadr expr))))
                  ((and or exor)
                   (cond
                    ((null (cddr expr))

; Apparently (AND p) is a legal be expression.  I assume
; (AND p) = (OR p) = (EXOR p) = p.

                     (convert-be-expr (cadr expr)))
                    (t
                     (xxxjoin (cdr (assoc-eq (car expr) *be-alist*))
                              (convert-be-expr-lst (cdr expr))))))
                  (t (er hard 'convert-be-expr
                         "Unexpected operand, ~p0."
                         (car expr)))))))

 (defun convert-be-expr-lst (lst)
   (cond ((null lst) nil)
         (t (cons (convert-be-expr (car lst))
                  (convert-be-expr-lst (cdr lst))))))

 )

(defun make-be-bindings (lst)
  (cond ((null lst) nil)
        (t (cons (list (car lst) (convert-be-expr (caddr lst)))
                 (make-be-bindings (cdddr lst))))))

(defun get-be-out-vars (lst)
  (cond ((null lst) nil)
        (t (cons (car lst) (get-be-out-vars (cdddr lst))))))

(mutual-recursion

 (defun compute-used-vars (expr vars)
   (cond ((atom expr)
          (cond ((or (eq expr t) (eq expr nil))
                 vars)
                (t (add-to-set-eq expr vars))))
         (t (compute-used-vars-lst (cdr expr) vars))))

 (defun compute-used-vars-lst (expr-lst vars)
   (cond ((null expr-lst) vars)
         (t (compute-used-vars-lst
             (cdr expr-lst)
             (compute-used-vars (car expr-lst) vars)))))

 )

(defun delete-ignored-bindings (ignored-vars bindings)
  (cond ((null bindings) nil)
        ((member-eq (caar bindings) ignored-vars)
         (delete-ignored-bindings ignored-vars (cdr bindings)))
        (t (cons (car bindings)
                 (delete-ignored-bindings ignored-vars (cdr bindings))))))

(defun parse-be (lst)

; We return (lambda <invars> (let* <bindings> (list <outputs>)))

  (let* ((invars (cadr (member-eq '@invar lst)))
         (subexprs (trunc-lst '@out (cdr (member-eq '@sub lst))))
         (outexprs (trunc-lst '@end (cdr (member-eq '@out lst))))
         (bindings (append (make-be-bindings subexprs)
                           (make-be-bindings outexprs)))
         (outputs (get-be-out-vars outexprs)))
    `(lambda ,invars
       (let* ,(delete-ignored-bindings
               (set-difference-eq
                (strip-cars bindings)
                (union-eq
                 outputs
                 (compute-used-vars (strip-cadrs bindings) nil)))
               bindings)
         (list ,@outputs)))))

(defun set-equal-varsp (lst1 lst2)
  (and (symbol-listp lst1)
       (no-duplicatesp lst1)
       (symbol-listp lst2)
       (subsetp-eq lst1 lst2)
       (subsetp-eq lst2 lst1)))

(defun parse-be-file (filename state)

; We return (lambda (<invars>) (equal (let* ...) (let* ...))).

  (er-let* ((lst (rf filename)))
           (let* ((be1 (parse-be lst))
                  (be2 (parse-be (member-eq '@be2 lst)))
                  (input-vars1 (cadr be1))
                  (bindings1 (cadr (caddr be1)))
                  (output-vars1 (cdr (caddr (caddr be1))))
                  (input-vars2 (cadr be2))
                  (bindings2 (cadr (caddr be2)))
                  (output-vars2 (cdr (caddr (caddr be2)))))
             (cond ((not (set-equal-varsp input-vars1 input-vars2))
                    (er soft 'parse-be-file
                        "The input vars of BE1 are ~&0 and those of ~
                         BE2 are ~&1.  But these are supposed to be ~
                         set-equal lists of distinct variable names."
                        input-vars1
                        input-vars2))
                   ((not (no-duplicatesp (strip-cars bindings1)))
                    (er soft 'parse-be-file
                        "The bindings of BE1 contain one or more ~
                         duplications, namely, of ~&0."
                        (duplicates (strip-cars bindings1))))
                   ((not (no-duplicatesp (strip-cars bindings2)))
                    (er soft 'parse-be-file
                        "The bindings of BE2 contain one or more ~
                         duplications, namely, of ~&0."
                        (duplicates (strip-cars bindings2))))
                   ((not (set-equal-varsp output-vars1 output-vars2))
                    (er soft 'parse-be-file
                        "The output vars of BE1 are ~&0 and those of ~
                         BE2 are ~&1.  But these are supposed to be ~
                         set-equal lists of distinct variable names."
                        output-vars1
                        output-vars2))
                   (t
                    (value (list input-vars1
                                 bindings1
                                 output-vars1
                                 bindings2)))))))

; The files listed here are all the .be files on cath/ and on ex/.
; There are still other .be files on hachtel/ for which we have
; published comparisons, but I am limiting my attention to these
; for the moment.

(defconst *benchmark-files*
  '("cath/add1.be"
    "cath/add2.be"
    "cath/add3.be"
    "cath/add4.be"
    "cath/addsub.be"
;   "cath/alu.be"     ; has a DCS, so ignored now
;   "ex/ex2.be"       ; has a DCS, so ignored now
    "ex/mul03.be"
    "ex/mul04.be"
    "ex/mul05.be"
    "ex/mul06.be"
    "ex/mul07.be"
    "ex/mul08.be"
    "ex/rip02.be"
    "ex/rip04.be"
    "ex/rip06.be"
    "ex/rip08.be"
    "ex/transp.be"
    "ex/ztwaalf1.be"
    "ex/ztwaalf2.be"))

; Finally, we run the bdd procedure.

(defun cbf (be-directory filename state)
  (er-let*
   ((x (parse-be-file (concatenate 'string be-directory filename) state)))
   (let ((input-vars   (nth 0 x))
         (bindings1    (nth 1 x))
         (output-vars1 (nth 2 x))
         (bindings2    (nth 3 x)))
     (value `(defthm ,(intern filename "ACL2")
               (implies (boolean-listp (list ,@input-vars))
                        (equal (let* ,bindings1 (list ,@output-vars1))
                               (let* ,bindings2 (list ,@output-vars1))))
               :hints (("Goal" :bdd (:vars (,@input-vars))))
               :rule-classes nil)))))

(defun cbf-list (be-directory filename-list channel state)
  (cond
   ((endp filename-list) (value :invisible))
   (t (er-let* ((form (cbf be-directory (car filename-list) state)))
               (pprogn (fms "~p0~%"
                            (list (cons #\0 form))
                            channel state nil)
                       (cbf-list be-directory (cdr filename-list) channel
                                 state))))))

(defun write-benchmark-file (be-directory state)
  (let* ((cbd (cbd))
         (be-directory (if cbd
                           (extend-pathname cbd be-directory state)
                         be-directory)))
    (state-global-let*
     ((infixp nil))
     (mv-let (channel state)
       (open-output-channel (extend-pathname cbd "benchmarks.lisp" state)
                            :object state)
       (pprogn
        (fms "(in-package \"ACL2\")~%" nil channel state nil)
        (fms "(set-ignore-ok t)~%" nil channel state nil)
        (fms "(include-book ~p0)~%"
             (list (cons #\0 "bool-ops"))
             channel state nil)
        (mv-let (erp val state)
          (cbf-list be-directory *benchmark-files* channel state)
          (pprogn (close-output-channel channel state)
                  (mv erp val state))))))))
