; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The utility make-executable attempts to modify a given term, producing one
; that is logically equivalent and has a given stobjs-out, or at least
; indicates a given stobjs-out.  Since mv is a macro, we can't produce a term
; with a given stobjs-out of length 2 or more.  So instead we introduce an
; identity function mv-marker so that (mv-marker n (cons x1 (cons x2 ... (cons
; xn nil) ...)))  is a (genuine) term that the caller of make-executable could
; transform into an mv "call".  This puts a burden on the caller, in
; particular, if the caller is untranslate.  In that case the
; untranslate-preprocess mechanism could be used, although that might step on
; the existing untranslate-preprocess-fn if such is already installed; if such
; an approach is adopted, consider using the untranslate-patterns interface to
; untranslate-preprocess.  A quick-and-dirty approach to remove mv-marker would
; simply be to scan the term, and we include code for that below.

; Moreover, at this point we make little attempt to deal with stobjs.  Later we
; may consider, for example given stobj (defstobj st fld), replacing (nth '0
; st) by (fld st).  We also avoid handling a few other cases from translate11,
; including translate-and-test, check-vars-not-free, pargs,

(in-package "ACL2")

(defconst *ordinary-stobjs-out*
  '(nil))

(defun mv-marker (n x)

; Logically, (mv-marker n x) is x.  But we expect x to be an expression whose
; stobjs-out has length n.  We expect to untranslate (mv-marker n (cons x1 ...))
; to (mv x1 ...), where (cons ...) denotes a formal list with n elements x1,
; x2, ....

  (declare (ignore n)
           (xargs :mode :logic :guard t))
  x)

(mutual-recursion

(defun make-executable (term stobjs-out wrld)

; For now we keep this simple, in that we don't wrap (the translation of)
; non-exec around non-executable terms.  But that could change in the future if
; need be.

  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld)
                              (symbol-listp stobjs-out))))
  (cond
   ((variablep term)
    term)
   ((fquotep term)
    (cond
     ((equal stobjs-out *ordinary-stobjs-out*)
      term)
     (t (fcons-term* 'mv-marker
                     (kwote (length stobjs-out))
                     term))))
   ((flambdap (ffn-symb term))
    (let* ((fn (ffn-symb term))
           (new-body (make-executable (lambda-body fn) stobjs-out wrld))
           (new-args (make-executable-lst (fargs term) wrld)))
      (fcons-term (make-lambda (lambda-formals fn)
                               new-body)
                  new-args)))
   ((or (eq (ffn-symb term) 'if)
        (and (eq (ffn-symb term) 'return-last)
             (equal (fargn term 1) ''mbe1-raw)))
    (fcons-term* (ffn-symb term)
                 (make-executable (fargn term 1) *ordinary-stobjs-out* wrld)
                 (make-executable (fargn term 2) stobjs-out wrld)
                 (make-executable (fargn term 3) stobjs-out wrld)))
   ((eq (ffn-symb term) 'return-last)

; For relevant background see translate11.

    (cond
     ((throw-nonexec-error-p1 (fargn term 1) (fargn term 2) :non-exec nil)

; Term was already marked as non-executable, so we simply preserve it.

      term)
     (t
      (fcons-term* 'return-last
                   (make-executable (fargn term 1) *ordinary-stobjs-out* wrld)
                   (make-executable (fargn term 2) *ordinary-stobjs-out* wrld)
                   (make-executable (fargn term 3) stobjs-out wrld)))))
   (t
    (let* ((fn (ffn-symb term))
           (fn-stobjs-out (stobjs-out fn wrld))
           (args (make-executable-lst (fargs term) wrld))
           (term2 (fcons-term fn args)))
      (cond
       ((and (consp fn-stobjs-out) ; for guard
             (cdr fn-stobjs-out) ; fn returns multiple values
             (equal stobjs-out *ordinary-stobjs-out*))
        (fcons-term* 'mv-list
                     (kwote (len fn-stobjs-out))
                     term2))
       ((equal stobjs-out *ordinary-stobjs-out*)
        term2)
       (t (fcons-term* 'mv-marker (kwote (length stobjs-out)) term2)))))))

(defun make-executable-lst (lst wrld)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp wrld))))
  (cond ((endp lst) nil)
        (t (cons (make-executable (car lst) *ordinary-stobjs-out* wrld)
                 (make-executable-lst (cdr lst) wrld)))))
)

(defun maybe-kwote (x)

; We return an untranslated term that represents (quote x).

  (declare (xargs :guard t))
  (cond ((or (acl2-numberp x)
             (booleanp x)
             (keywordp x)
             (stringp x)
             (characterp x))
         x)
        (t (kwote x))))

(defun maybe-kwote-lst (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons (maybe-kwote (car x))
                 (maybe-kwote-lst (cdr x))))))

(defun mv-marker-args (n x)
  (declare (xargs :guard t))
  (and (integerp n)
       (< 1 n)
       (true-listp x) ; always true?
       (cond ((eq (car x) 'list)
              (and (eql n (length (cdr x)))
                   (cdr x)))
             ((eq (car x) 'quote)
              (and (true-listp (cadr x))
                   (eql n (length (cadr x)))
                   (maybe-kwote-lst (cadr x))))
             (t nil))))

(mutual-recursion

(defun remove-mv-marker-from-untranslated-term (x)
  (declare (xargs :guard t

; It doesn't seem worth the trouble at the moment to find a suitable measure
; and prove termination.  The problem is that (mv-marker-args (cadr x) (caddr
; x)) can actually (I think) have a larger acl2-count than x.

                  :mode :program))
  (cond
   ((or (not (true-listp x)) ; impossible?
        (atom x)
        (eq (car x) 'quote))
    x)
   ((and (eq (car x) 'mv-marker)
         (eql (length x) 3))
    (or (let ((args (mv-marker-args (cadr x) (caddr x))))
          (and args
               (cons 'mv
                     (remove-mv-marker-from-untranslated-term-lst args))))
        (caddr x)))
   (t (cons (car x)
            (remove-mv-marker-from-untranslated-term-lst (cdr x))))))

(defun remove-mv-marker-from-untranslated-term-lst (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (remove-mv-marker-from-untranslated-term (car lst))
                 (remove-mv-marker-from-untranslated-term-lst (cdr lst))))))
)
