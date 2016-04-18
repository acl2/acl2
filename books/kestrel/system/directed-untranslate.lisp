; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(mutual-recursion

(defun directed-untranslate-rec (uterm tterm sterm iff-flg wrld)
  (cond
   ((or (variablep sterm)
        (fquotep sterm)
        (variablep tterm)
        (fquotep tterm)
        (atom uterm))
    (untranslate sterm iff-flg wrld))
   ((and (member-eq (car uterm) '(or and))
         (consp (cddr uterm)) ; at least two arguments
         (eq (ffn-symb sterm) 'if))
    (or 

; First a special case: for (if (not test) tbr fbr), rewrite-if will take the
; rewritten test -- presumably (if test' nil t) -- and then switch tbr and fbr
; to give us (if test' fbr tbr).  !! I'll do this next.

     (case-match sterm       ; following similar handling in untranslate1

; We could also require more; for example, in the OR case, (eq (ffn-symb tterm)
; 'if) and (equal (fargn tterm 1) (fargn tterm 2)).  But any such requirements
; are probably always true, and even if not, we are happy to try to recover an
; OR or AND directly from sterm as follows.

       (('if & *nil* *t*)    ; generate a NOT, not an AND or OR
        nil)
       (('if x1 x2 *nil*)
        (and (eq (car uterm) 'and)
             (untranslate-and
              (directed-untranslate-rec (cadr uterm)
                                        (fargn tterm 1)
                                        x1
                                        t
                                        wrld)
              (directed-untranslate-rec (if (consp (cdddr uterm)) ; >= 3 args
                                            (cons 'and (cddr uterm))
                                          (caddr uterm))
                                        (fargn tterm 2)
                                        x2
                                        iff-flg
                                        wrld)
              iff-flg)))
       (('if x1 *nil* x2) ; (thm (equal (and (not (not x)) y) (and x y)))

; Presumably tterm has a form corresponding to something like (if x1' x3 x4)
; for some x3 and x4 that have nothing to do with x2.  So we don't bother to
; try to direct the untranslation of x2.

        (and (eq (car uterm) 'and)
             (untranslate-and
              (negate-untranslated-form
               (directed-untranslate-rec (cadr uterm)
                                         (fargn tterm 1)
                                         x1
                                         t
                                         wrld)
               t)
              (untranslate x2 iff-flg wrld)
              iff-flg)))
       (('if x1 x1 x2)
        (and (eq (car uterm) 'or)
             (untranslate-or
              (directed-untranslate-rec (cadr uterm)
                                        (fargn tterm 1)
                                        x1
                                        iff-flg
                                        wrld)
              (directed-untranslate-rec (if (consp (cdddr uterm)) ; >= 3 args
                                            (cons 'or (cddr uterm))
                                          (caddr uterm))
                                        (fargn tterm 3)
                                        x2
                                        iff-flg
                                        wrld))))
       (('if x1 x2 *t*)

; Observe that (if x1 x2 t) = (if x1 x2 (not nil)) = (if x1 x2 (not x1)) =
; (if (not x1) (not x1) x2) = (or (not x1) x2).

; Presumably tterm has a form corresponding to something like (if x1' x1' x3)
; for some x3 that has nothing to do with x2.  So we don't bother to try to
; direct the untranslation of x2.

        (and (eq (car uterm) 'or)
             (untranslate-or
              (negate-untranslated-form
               (directed-untranslate-rec (cadr uterm)
                                         (fargn tterm 1)
                                         x1
                                         t
                                         wrld)
               iff-flg)
              (untranslate x2 iff-flg wrld))))
       (('if x1 *t* x2)
        (and (eq (car uterm) 'or)
             (cond
              ((or iff-flg
                   (and (nvariablep x1)
                        (not (fquotep x1))
                        (member-eq (ffn-symb x1)
                                   *untranslate-boolean-primitives*)))
               (untranslate-or
                (directed-untranslate-rec (cadr uterm)
                                          (fargn tterm 1)
                                          x1
                                          t
                                          wrld)
                (directed-untranslate-rec (if (consp (cdddr uterm)) ; >= 3 args
                                              (cons 'or (cddr uterm))
                                            (caddr uterm))
                                          (fargn tterm 3)
                                          x2
                                          iff-flg
                                          wrld)))
              (t nil))))
       (& nil))
     (untranslate sterm iff-flg wrld)))
   ((eq (car uterm) 'cond)
    (let ((clauses (directed-untranslate-into-cond-clauses
                    (cdr uterm) tterm sterm iff-flg wrld)))
      (and clauses
           (case-match clauses
             ((('t x))
              x)
             (& (cons 'cond clauses))))))
   ((and (eq (car uterm) '>)
         (eql (length uterm) 3) ; (> x0 y0)
         (eq (car sterm) '<)    ; (< y1 x1)
         (eq (car tterm) '<))   ; (< y2 x2)
    (cons '> (directed-untranslate-lst
              (list (caddr uterm) (cadr uterm)) ; (y0 x0)
              (fargs tterm) (fargs sterm) wrld)))
   ((eq (car uterm) '<=) ; (<= x0 y0), translates as (not (< y0 x0))
    (or (case-match tterm
          (('not ('< y1 x1))
           (case-match sterm
             (('not ('< y2 x2))
              (cons '<= (directed-untranslate-lst
                         (cdr uterm)  ; (x0 y0)
                         (list x1 y1) ; from tterm
                         (list x2 y2) ; from sterm
                         wrld)))
             (& nil)))
          (& nil))
        (untranslate sterm iff-flg wrld)))
   ((eq (car uterm) '>=) ; (>= x0 y0), translates as (not (< x0 y0))
    (or (case-match tterm
          (('not ('< x1 y1))
           (case-match sterm
             (('not ('< x2 y2))
              (cons '>= (directed-untranslate-lst
                         (cdr uterm)  ; (x0 y0)
                         (list x1 y1) ; from tterm
                         (list x2 y2) ; from sterm
                         wrld)))
             (& nil)))
          (& nil))
        (untranslate sterm iff-flg wrld)))
   (t
    (or
     (case-match uterm
       (('list) uterm)
       (('list x)
        (case-match sterm
          (('cons a *nil*)
           (list 'list
                 (directed-untranslate-rec x (fargn tterm 1) a nil wrld)))
          (& nil)))
       (('list x . y) ; (cons x (list . y))
        (case-match sterm
          (('cons a b)
           (let ((tmp1 (directed-untranslate-rec x
                                                 (fargn tterm 1) a nil wrld))
                 (tmp2 (directed-untranslate-rec `(list ,@y)
                                                 (fargn tterm 2) b nil wrld)))
             (if (and (consp tmp2) (eq (car tmp2) 'list))
                 `(list ,tmp1 ,@(cdr tmp2))
               `(cons ,tmp1 ,tmp2))))
          (& nil)))
       (('list* x)
        (list 'list*
              (directed-untranslate-rec x tterm sterm nil wrld)))
       (('list* x . y) ; (cons x (list* . y))
        (case-match sterm
          (('cons a b)
           (let ((tmp1 (directed-untranslate-rec x
                                                 (fargn tterm 1) a nil wrld))
                 (tmp2 (directed-untranslate-rec `(list* ,@y)
                                                 (fargn tterm 2) b nil wrld)))
             (if (and (consp tmp2) (eq (car tmp2) 'list*))
                 `(list* ,tmp1 ,@(cdr tmp2))
               `(cons ,tmp1 ,tmp2))))
          (& nil)))
       (& nil))
     (let* ((pair (cdr (assoc-eq (ffn-symb sterm)
                                 (untrans-table wrld))))
            (op (if pair
                    (car pair)
                  (or (cdr (assoc-eq (ffn-symb sterm)
                                     (table-alist 'std::define-macro-fns wrld)))
                      (ffn-symb sterm)))))
       (cond
        ((and (not (eq op (car uterm)))
              (symbolp (car uterm))
              (not (eq (getpropc (car uterm) 'macro-body t wrld)
                       t))
              (equal sterm tterm))

; Leave macro calls in place when nothing has changed, except for calls of
; macros that we handle ourselves or represent function symbols.

         uterm)
        ((and (symbolp (ffn-symb sterm))
              (eql (length (fargs sterm))
                   (length (fargs tterm))))
         (cond ((and (cdr pair) ; hence pair, and we might right-associate
                     (case-match uterm
                       ((!op & & & . &) t) ; we want to flatten
                       (& nil)))           ; (op x (op y ...))
                (let ((arg1 (directed-untranslate-rec
                             (cadr uterm)
                             (fargn tterm 1) (fargn sterm 1) nil
                             wrld))
                      (arg2 (directed-untranslate-rec
                             (cons 'op (cddr uterm))
                             (fargn tterm 2) (fargn sterm 2) nil wrld)))
                  (cond ((and (consp arg2)
                              (eq (car arg2) op))
                         (list* op arg1 (cdr arg2)))
                        (t (list op arg1 arg2)))))
               (t (cons op (directed-untranslate-lst
                            (cdr uterm) (fargs tterm) (fargs sterm) wrld)))))
        (t (untranslate sterm iff-flg wrld))))))))

(defun directed-untranslate-lst (uargs targs sargs wrld)
  (cond ((endp uargs) nil)
        (t (cons (directed-untranslate-rec (car uargs)
                                           (car targs)
                                           (car sargs)
                                           nil wrld)
                 (directed-untranslate-lst (cdr uargs)
                                           (cdr targs)
                                           (cdr sargs)
                                           wrld)))))

(defun directed-untranslate-into-cond-clauses (cond-clauses tterm sterm iff-flg
                                                            wrld)

; This is based on ACL2 source function untranslate-into-cond-clauses.  It
; returns new cond-clauses C (with luck, similar in structure to the input
; cond-clauses) such that (cond . C) translates to sterm.  See
; directed-untranslate.

  (cond
   ((not (and (nvariablep sterm)
;             (not (fquotep sterm))
              (eq (ffn-symb sterm) 'if)

; We expect the following always to be true, because tterm gave rise to
; cond-clauses; but we check, to be sure.

              (nvariablep tterm)
;             (not (fquotep tterm))
              (eq (ffn-symb tterm) 'if)))
    (list (list t
                (untranslate sterm iff-flg wrld))))
   ((endp (cdr cond-clauses))
    (cond
     ((eq (caar cond-clauses) t)
      (directed-untranslate-rec (cadar cond-clauses)
                                tterm sterm iff-flg
                                wrld))
     ((equal (fargn sterm 3) *nil*)
      (list (list (directed-untranslate-rec (caar cond-clauses)
                                            (fargn tterm 1)
                                            (fargn sterm 1)
                                            t wrld)
                  (directed-untranslate-rec (cadar cond-clauses)
                                            (fargn tterm 2)
                                            (fargn sterm 2)
                                            iff-flg wrld))))
     (t (list (list t
                    (untranslate sterm iff-flg wrld))))))
   (t
    (cons (list (directed-untranslate-rec (caar cond-clauses)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          t wrld)
                (directed-untranslate-rec (cadar cond-clauses)
                                          (fargn tterm 2)
                                          (fargn sterm 2)
                                          iff-flg wrld))
          (directed-untranslate-into-cond-clauses
           (cdr cond-clauses)
           (fargn tterm 3)
           (fargn sterm 3)
           iff-flg wrld)))))
)

(defun directed-untranslate (uterm tterm sterm iff-flg wrld)

; Uterm is an untranslated form that translates to the term, tterm.  Sterm is a
; term, which may largely agree with tterm.  The result is an untranslated form
; whose translation is sterm, with the goal that the sharing of structure
; between tterm and sterm is reflected in similar sharing between uterm and
; that result.

; Current limitations include:

; - If sterm has similar structure to a proper subterm of tterm rather than to
;   tterm itself, then uterm will probably be useless in the untranslation.

; - Let, let*, case, and perhaps some other useful constructs could probably be
;   reasonably handled, but aren't yet.

  (directed-untranslate-rec uterm tterm sterm iff-flg wrld))
