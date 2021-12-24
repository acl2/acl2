; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The macro NLD passes a given form to the ACL2 loop, optionally passing along
; LD keyword arguments as well.  It returns a value (mv nil (erp . x) state)
; where erp is non-nil for certain errors but when erp is nil, then x has the
; following form:

;   (stobjs-out . result(s))

; as returned by running trans-eval on the form.  See :DOC trans-eval for an
; explanation, but briefly put:

; - stobjs-out is a list of symbols, all of which are either nil or stobj
;   names, to represent the output signature of form; and

; - results is the value returned if stobjs-out is a one-element list, and
;   otherwise results is the list of multiple values returned but where each
;   stobj is replaced by a symbolthat represents the stobj.

; For example, in each case below we see some output followed by the return
; value, where the return value is on a line that starts with a single space to
; indicate an error triple (see :DOC error-triple).  Below is a log with some
; examples; in particular, the first example returns
;   (mv nil (NIL (NIL) . 7) state)
; where (NIL (NIL) . 7) is of the form (erp stobjs-out . result), where:
;   erp = NIL;
;   stobjs-out = (NIL); and
;   result = 7.

#||
ACL2 !>(nld '(+ 3 4))
7
 (NIL (NIL) . 7)
ACL2 !>(nld '(mv 6 (+ 3 4)))
(6 7)
 (NIL (NIL NIL) 6 7)
ACL2 !>(nld '(mv 6 state (+ 3 4)))
(6 <state> 7)
 (NIL (NIL STATE NIL) 6 REPLACED-STATE 7)
ACL2 !>(nld '(er hard "ouch"))


ACL2 Error in macro expansion:  Wrong number of args in macro expansion
of (ER HARD "ouch").

 (T)
ACL2 !>
||#

; The implementation feels dodgy to me since I don't like calling LD inside a
; function call, but I don't see an actual problem with this macro.

; If NLD gets some use then I may add a :DOC topic for it.

; Note that NLD may be called either from the ACL2 loop or from raw Lisp, but
; in raw Lisp a reference to STATE may cause a ompiler warning about STATE
; being an undeclared free variable.  With some effort that might be fixable;
; anyhow, it probably is reasonably harmless.

; The function prepend-ld-result anticipates a particular "error stack" form
; for the error case that is not yet implemented.  If we settle on a form for
; the error stack, then we can add suitable guards and guard-verify the
; functions, and we will likely document the form (if nothing else, by writing
; a predicate to recognize the error stack, used in those guards).

(in-package "ACL2")

(defun error-stack-summary (s)
  (let* ((d (assoc-eq :free-variables s))
         (l (and d (cadr (assoc-keyword :location (cdr d))))))
    (cond
     ((equal l "body of")
      :free-variables-body)
     ((equal l "guard for")
      :free-variables-guard)
     ((assoc-eq :termination-proof s)
      :termination-proof)
     ((assoc-eq :guard-proof s)
      :guard-proof)
     (t
      :other-error))))

(defun prepend-ld-result (ld-history)
  (let* ((entry (car ld-history))
         (error-flg (ld-history-entry-error-flg entry))
         (stobjs-out/value (ld-history-entry-stobjs-out/value entry)))
    (cond (error-flg (assert$ (eq stobjs-out/value nil)
                              (cons error-flg stobjs-out/value)))
          (t (case-match stobjs-out/value
               ((stobjs-out
                 ((:ERROR-STACK . error-stack)
                  . er)
                 . rest)
                `(,stobjs-out
                  (,(error-stack-summary error-stack)
                   (:ERROR-STACK . ,error-stack)
                   . ,er)
                  . ,rest))
               (& (cons error-flg stobjs-out/value)))))))

(defmacro nld (form &rest args)
  (cond ((keyword-value-listp args)
         (let* ((tail (assoc-keyword :ld-verbose args))
                (args (if tail
                          args
                        (list* :ld-verbose nil args)))
                (tail (assoc-keyword :ld-prompt args))
                (args (if tail
                          args
                        (list* :ld-prompt nil args))))
           `(er-progn (ld (list ,form) ,@args)
                      (value (prepend-ld-result
                              (ld-history state))))))
        (t (er hard 'nld
               "Bad call of nld, since this is not a keyword-value-listp:~&~s"
               args))))
