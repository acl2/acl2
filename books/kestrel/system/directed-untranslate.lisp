; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(mutual-recursion

(defun directed-untranslate-rec (uterm tterm sterm iff-flg macro-aliases wrld)

; Uterm is an untranslated form that translates to the term, tterm.  Sterm is a
; term, which may largely agree with tterm.  The result is an untranslated form
; whose translation is sterm, with the goal that the sharing of structure
; between tterm and sterm is reflected in similar sharing between uterm and
; that result.

; Current limitations include:

; - If sterm has similar structure to a proper subterm of tterm rather than to
;   tterm itself, then uterm will probably be useless in the untranslation.

; - Let and let* are not yet handled.

  (cond
   ((equal sterm tterm) uterm)
   ((or (variablep sterm)
        (fquotep sterm)
        (variablep tterm)
        (fquotep tterm)
        (atom uterm))
    (untranslate sterm iff-flg wrld))
   ((eq (car uterm) 'and)
    (cond
     ((and (consp (cddr uterm)) ; at least two arguments
           (eq (ffn-symb sterm) 'if)
           (eq (ffn-symb tterm) 'if)
           (equal (fargn sterm 3) *nil*)
           (equal (fargn tterm 3) *nil*))
      (let ((u1 (directed-untranslate-rec (cadr uterm)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          iff-flg ; or t
                                          macro-aliases wrld))
            (u2 (directed-untranslate-rec (if (consp (cdddr uterm)) ; >= 3 args
                                              (cons 'and (cddr uterm))
                                            (caddr uterm))
                                          (fargn tterm 2)
                                          (fargn sterm 2)
                                          iff-flg
                                          macro-aliases wrld)))
        (untranslate-and u1 u2 iff-flg)))
     (t (untranslate sterm iff-flg wrld))))
   ((eq (car uterm) 'or)
    (cond
     ((and (consp (cddr uterm)) ; at least two arguments
           (eq (ffn-symb sterm) 'if)
           (eq (ffn-symb tterm) 'if)
           (or (equal (fargn sterm 1)
                      (fargn sterm 2))
               (and iff-flg
                    (equal *t*
                           (fargn sterm 2))))
           (equal (fargn tterm 1)
                  (fargn tterm 2)))
      (let ((u1 (directed-untranslate-rec (cadr uterm)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          iff-flg
                                          macro-aliases wrld))
            (u3 (directed-untranslate-rec (if (consp (cdddr uterm)) ; >= 3 args
                                              (cons 'or (cddr uterm))
                                            (caddr uterm))
                                          (fargn tterm 3)
                                          (fargn sterm 3)
                                          iff-flg
                                          macro-aliases wrld)))
        (untranslate-or u1 u3)))
     (t (untranslate sterm iff-flg wrld))))
   ((eq (car uterm) 'cond)
    (let ((clauses (directed-untranslate-into-cond-clauses
                    (cdr uterm) tterm sterm iff-flg macro-aliases wrld)))
      (case-match clauses
        ((('t x))
         x)
        (& (cons 'cond clauses)))))
   ((and (eq (car uterm) '>)
         (eql (length uterm) 3) ; (> x0 y0)
         (eq (car sterm) '<)    ; (< y1 x1)
         (eq (car tterm) '<))   ; (< y2 x2)
    (let ((tmp (directed-untranslate-lst
                (list (caddr uterm) (cadr uterm)) ; (y0 x0)
                (fargs tterm) (fargs sterm) macro-aliases wrld)))
      (cons '> tmp)))
   ((and (eq (car uterm) '<=) ; (<= x0 y0), translates as (not (< y0 x0))
         (case-match tterm
           (('not ('< y1 x1))
            (case-match sterm
              (('not ('< y2 x2))
               (let ((tmp (directed-untranslate-lst
                           (cdr uterm)  ; (x0 y0)
                           (list x1 y1) ; from tterm
                           (list x2 y2) ; from sterm
                           macro-aliases wrld)))
                 (cons '<= tmp)))
              (& nil)))
           (& nil))))
   ((and (eq (car uterm) '>=) ; (>= x0 y0), translates as (not (< x0 y0))
         (case-match tterm
           (('not ('< x1 y1))
            (case-match sterm
              (('not ('< x2 y2))
               (let ((tmp (directed-untranslate-lst
                           (cdr uterm)  ; (x0 y0)
                           (list x1 y1) ; from tterm
                           (list x2 y2) ; from sterm
                           macro-aliases wrld)))
                 (cons '>= tmp)))
              (& nil)))
           (& nil))))
   ((symbolp (ffn-symb sterm))
    (cond
     ((and (eql (length (fargs sterm))
                (length (fargs tterm)))
           (eql (length (fargs sterm))
                (length (fargs uterm))))
      (let ((fn (if (eq (car uterm)
                        (deref-macro-name (ffn-symb sterm) macro-aliases))
                    (car uterm)
                  (ffn-symb sterm))))
        (cons fn
              (directed-untranslate-lst (cdr uterm) (fargs tterm) (fargs sterm)
                                        macro-aliases wrld))))
     (t (untranslate sterm iff-flg wrld))))
   ((symbolp (ffn-symb tterm)) ; somehow produced a lambda from a non-lambda
    (untranslate sterm iff-flg wrld))
   ((eq (car uterm) 'let)             ; and both tterm and uterm are lambdas
    (untranslate sterm iff-flg wrld)) ; can probably do better
   ((eq (car uterm) 'let*)            ; and both tterm and uterm are lambdas
    (untranslate sterm iff-flg wrld)) ; can probably do better
   (t ; could add more cases, e.g., for more macros
    (untranslate sterm iff-flg wrld))))

(defun directed-untranslate-lst (uargs targs sargs macro-aliases wrld)
  (cond ((endp uargs) nil)
        (t (cons (directed-untranslate-rec (car uargs)
                                           (car targs)
                                           (car sargs)
                                           nil macro-aliases wrld)
                 (directed-untranslate-lst (cdr uargs)
                                           (cdr targs)
                                           (cdr sargs)
                                           macro-aliases wrld)))))

(defun directed-untranslate-into-cond-clauses (cond-clauses tterm sterm iff-flg
                                                            macro-aliases wrld)

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
      (list (list t
                  (directed-untranslate-rec (cadar cond-clauses)
                                            tterm sterm iff-flg macro-aliases
                                            wrld))))
     ((equal (fargn sterm 3) *nil*)
      (list (list (directed-untranslate-rec (caar cond-clauses)
                                            (fargn tterm 1)
                                            (fargn sterm 1)
                                            t macro-aliases wrld)
                  (directed-untranslate-rec (cadar cond-clauses)
                                            (fargn tterm 2)
                                            (fargn sterm 2)
                                            iff-flg macro-aliases wrld))))
     (t (list (list t
                    (untranslate sterm iff-flg wrld))))))
   (t
    (cons (list (directed-untranslate-rec (caar cond-clauses)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          t macro-aliases wrld)
                (directed-untranslate-rec (cadar cond-clauses)
                                          (fargn tterm 2)
                                          (fargn sterm 2)
                                          iff-flg macro-aliases wrld))
          (directed-untranslate-into-cond-clauses
           (cdr cond-clauses)
           (fargn tterm 3)
           (fargn sterm 3)
           iff-flg macro-aliases wrld)))))
)

(defun directed-untranslate (uterm tterm sterm iff-flg wrld)
  (directed-untranslate-rec uterm tterm sterm iff-flg (macro-aliases wrld)
                            wrld))
