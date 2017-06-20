; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The utility make-executable attempts to modify a given term, producing one
; that is logically equivalent and has a given stobjs-out.

; This is very preliminary!  In particular, we don't attempt to replace cons
; nests by calls of mv -- of course, we can't even do that since mv is a macro
; if we insist on producing a term, which currently is the case.  We could
; consider defining a function (mv* x), where the caller can for example
; transform (mv* (cons a (cons b (cons c 'nil)))) into (mv a b c).  But that's
; for another day, if at all.

; Moreover, at this point we make little attempt to deal with stobjs.  Later we
; may consider, for example given stobj (defstobj st fld), replacing (nth '0
; st) by (fld st).  We also avoid handling a few other cases from translate11,
; including translate-and-test, check-vars-not-free, pargs,

(in-package "ACL2")

(defconst *ordinary-stobjs-out*
  '(nil))

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
     (t term)))
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
       (t term2))))))

(defun make-executable-lst (lst wrld)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp wrld))))
  (cond ((endp lst) nil)
        (t (cons (make-executable (car lst) *ordinary-stobjs-out* wrld)
                 (make-executable-lst (cdr lst) wrld)))))
)
