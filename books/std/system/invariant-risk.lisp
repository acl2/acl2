; Matt Kaufmann
; Copyright (C) 2021, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; To be documented... but probably the comments suffice for the following three
; utilities.

; (invariant-risk-callees fn wrld)
; (invariant-risk-call-path fn exceptions wrld)
; (invariant-risk-call-path-alist fns exceptions alist wrld)

(in-package "ACL2")

(defun tbody (fn wrld)
  (declare (xargs :mode :program))
  (or (body fn nil wrld)
      (let ((ev (get-defun-event fn wrld)))
        (and ev
             (mv-let (erp body)
               (translate-cmp (car (last ev))
                              t                ; stobjs-out
                              nil              ; logic-modep
                              t                ; known-stobjs
                              'tbody           ; ctx
                              wrld
                              (default-state-vars nil
                                :temp-touchable-fns t))
               (cond (erp (er hard 'tbody
                              "Unable to translate the body of ~x0."
                              fn))
                     (t body)))))))

(defun invariant-risk-callees1 (body-fns fn wrld acc)
  (declare (xargs :guard (and (symbol-listp body-fns)
                              (symbolp fn)
                              (plist-worldp wrld)
                              (true-listp acc))))
  (cond
   ((endp body-fns) acc)
   (t (invariant-risk-callees1
       (cdr body-fns)
       fn
       wrld
       (if (and (getpropc (car body-fns) 'invariant-risk nil wrld)
                (not (member-eq (car body-fns) acc))
                (not (eq (car body-fns) fn)))
           (cons (car body-fns) acc)
         acc)))))

(defun invariant-risk-callees (fn wrld)

; Return fn itself if it has been invariant-risk directly, nil if fn does not
; have invariant-risk, and otherwise the list of callees other than fn (and
; other than its mutual-recursion siblings, if any) that contribute
; invariant-risk to fn.

; This is patterned after put-invariant-risk and put-invariant-risk1, since we
; want to know which function symbols are responsible for fn having
; invariant-risk.  In particular, for a subterm (mbe :logic L :exec E) we are
; not interest in function symbols occurring in L.

  (declare (xargs :mode :program ; because of body and get-defun-event
                  :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (let ((prop (getpropc fn 'invariant-risk nil wrld)))
    (cond
     ((null prop) nil)
     ((eq prop fn) prop)
     (t (invariant-risk-callees1
         (all-fnnames1-exec nil (tbody fn wrld) nil)
         fn
         wrld
         nil)))))

(defun invariant-risk-call-path-rec (fns exceptions wrld)

; We return one branch through the call tree from some function in fns that
; leads to a primitive function having invariant-risk, or nil if there is none.
; For any function f in exceptions, we consider there to be no invariant-risk
; for f nor any invariant-risk for any function executed on behalf of a call of
; f.

  (declare (xargs :mode :program ; because of body and get-defun-event
                  :guard (and (symbol-listp fns)
                              (symbol-listp exceptions)
                              (plist-worldp wrld))))
  (cond
   ((endp fns) (mv nil exceptions))
   (t (let* ((fn (car fns))
             (e (member-eq fn exceptions))
             (prop (and (not e)
                        (getpropc fn 'invariant-risk nil wrld))))
        (cond
         ((null prop)
          (invariant-risk-call-path-rec (cdr fns)
                                        (if e
                                            exceptions
                                          (cons fn exceptions))
                                        wrld))
         ((eq prop fn) (mv (list fn) exceptions))
         (t (mv-let (path exceptions)
              (invariant-risk-call-path-rec (all-fnnames1-exec nil
                                                               (tbody fn wrld)
                                                               nil)
                                            (add-to-set-eq fn exceptions)
                                            wrld)
              (cond
               (path (mv (cons fn path) exceptions))
               (t
                (invariant-risk-call-path-rec (cdr fns)
                                              (add-to-set-eq fn exceptions)
                                              wrld))))))))))

(defun invariant-risk-call-path (fn exceptions wrld)

; We return one branch through the call tree from fn that leads to a primitive
; function having invariant-risk, or nil if there is no invariant-risk.  We
; consider a function not to have invariant-risk if it's among exceptions.

  (declare (xargs :mode :program ; because of body and get-defun-event
                  :guard (and (symbolp fn)
                              (symbol-listp exceptions)
                              (plist-worldp wrld))))
  (mv-let (path exceptions)
    (invariant-risk-call-path-rec (list fn) exceptions wrld)
    (declare (ignore exceptions))
    path))

(defun invariant-risk-call-path-alist (fns exceptions alist wrld)

; Partial summary: At the top level, alist and exceptions are typically nil and
; fns is a list of function symbols such that each member, fn, is to be
; associated with a calling path from fn to a primitive that has invariant-risk
; (either a built-in or a stobj primitive).

; More thorough explanation:

; We return a pair (mv paths exceptions), where we accumulate into alist a call
; path for each fn in fns leading to a primitive with invariant-risk, when such
; a call path exists, and we accumulate the rest of fns into exceptions.  For
; purposes of this function, no function symbol in the input list, exceptions,
; is considered to have invariant-risk.

; We reverse the accumulated alist and exceptions at the end, so if you care
; about their ordering, then you may want to reverse such inputs.

  (declare (xargs :mode :program ; because of body and get-defun-event
                  :guard (and (symbol-listp fns)
                              (symbol-listp exceptions)
                              (true-listp alist)
                              (plist-worldp wrld))))
  (cond
   ((endp fns)
    (mv (reverse alist) (reverse exceptions)))
   ((member-eq (car fns) exceptions)
    (invariant-risk-call-path-alist (cdr fns) exceptions alist wrld))
   (t
    (mv-let (path exceptions)
      (invariant-risk-call-path-rec (list (car fns)) exceptions wrld)
      (cond
       (path (invariant-risk-call-path-alist (cdr fns)
                                             exceptions
                                             (cons path alist)
                                             wrld))
       (t
        (invariant-risk-call-path-alist (cdr fns) exceptions alist wrld)))))))

; It would probably also be straightforward to define
; (invariant-risk-call-tree fn wrld)
; to give the full call tree rather than just a single path, and similarly for
; a list of functions and an exceptions argument (as above).
