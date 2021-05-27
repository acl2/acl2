; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defvar *logic-call-depth* 0)

(defvar *agaa-ht* (make-hash-table))

(defvar *agaa-exceptions*

; These are :logic-mode functions with guards that we know have ill-guarded
; calls.  Ultimately we would like this list to be empty.

  '(newline princ$ prin1$ ; write-expansion-file (wrong kind of channel)
    ))

(defun add-guard-as-assertion (sym)
  (when (not (gethash sym *agaa-ht*)) ; else already done
    (let* ((state *the-live-state*)
           (wrld (w state)))
      (assert (and (symbolp sym)
                   (logicp sym wrld)))
      (let ((formals (formals sym wrld))
            (guard (guard sym t wrld))
            (old-sym (gensym))
            (new-sym (gensym)))
        (setf (symbol-function old-sym)
              (symbol-function sym))
        (eval `(compile
                (defun ,new-sym ,formals
                  (let ((*logic-call-depth*
                         (1+ *logic-call-depth*)))
                    (when (int= *logic-call-depth* 1)
                      (or ,guard
                          (error "Guard failed for ~s" ',sym))
                      (incf (gethash ',sym *agaa-ht*)))
                    (funcall ',old-sym ,@formals)))))
        (setf (symbol-function sym)
              (symbol-function new-sym))
        (setf (gethash sym *agaa-ht*) 0)))))

(defun add-guards-as-assertions-fn (lst)
  (cond ((endp lst) nil)
        ((member (car lst) *agaa-exceptions* :test 'eq)
         (add-guards-as-assertions-fn (cdr lst)))
        (t (cons `(add-guard-as-assertion ',(car lst))
                 (add-guards-as-assertions-fn (cdr lst))))))

(defmacro add-guards-as-assertions-svga ()

; This is a lighter-weight check, based on the guards verified outside the
; boot-strap (with feature :acl2-devel present).

  (cons 'progn (add-guards-as-assertions-fn
                (strip-cars *system-verify-guards-alist*))))

(defun collect-common-lisp-compliant-user-defuns1 (tl wrld ans)

; This is based on ACL2 source function collect-ideal-user-defuns1, modified
; collect guard-verified functions, to exclude function symbols that are in the
; Common Lisp package, and to include boot-strap functions.

  (cond
   ((null tl)
    ans)
   ((and (eq (caar tl) 'cltl-command)
         (eq (cadar tl) 'global-value)
         (equal (caddar tl) 'defuns))
    (collect-common-lisp-compliant-user-defuns1
     (cdr tl)
     wrld
     (cond
      ((null (cadr (cddar tl)))

; Defun-mode-flg = nil means encapsulate or :non-executable.  In this case we
; do not pick up the function, but that's OK because we don't care if it is
; executed efficiently.  Warning: If we decide to pick it up after all, then
; make sure that the symbol-class is not :program, since after Version_4.1 we
; allow non-executable :program mode functions.

       ans)
      (t (let ((sym (caar (cdddr (cddar tl)))))
           (cond
            ((and (not (macro-function sym)) ; rule out e.g. return-last
                  (not (equal (symbol-package-name sym)
                              *main-lisp-package-name*))
                  (eq (symbol-class sym wrld) :common-lisp-compliant))
             (union-eq (strip-cars (cdddr (cddar tl))) ans))
            (t ans)))))))
   (t (collect-common-lisp-compliant-user-defuns1 (cdr tl) wrld ans))))

(defun collect-common-lisp-compliant-user-defuns (wrld)

; This is based on ACL2 source function collect-ideal-user-defuns, modified
; collect guard-verified functions, to exclude function symbols that are in the
; Common Lisp package, and to include boot-strap functions.

  (collect-common-lisp-compliant-user-defuns1 wrld wrld nil))

(defmacro add-guards-as-assertions-all ()

; We add guards as assertions for all guard-verified :logic mode functions.

  (cons 'progn
        (add-guards-as-assertions-fn
         (collect-common-lisp-compliant-user-defuns (w *the-live-state*)))))

; Report how many times each assertion has been checked:

(defun report-guard-checks ()
  (let (ans)
    (maphash (lambda (key val)
               (push (cons key val) ans))
             *agaa-ht*)
    (loop for pair in (sort ans (lambda (x y) (> (cdr x) (cdr y))))
          do
          (format t "~s: ~s~%" (cdr pair) (car pair)))))
