; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc directed-untranslate
  :parents (kestrel-system-utilities system-utilities)
  :short "Create a user-level form that reflects a given user-level form's
 structure."
  :long "<p>See @(see term) for relevant background about user-level ``terms''
 and actual ``translated'' terms.</p>

 @({
 Example Form:
 (directed-untranslate
  '(and a (if b c nil))         ; uterm
  '(if a (if b c 'nil) 'nil)    ; tterm
  '(if a2 (if b2 c2 'nil) 'nil) ; sterm, a form to be untranslated
  nil
  (w state))
 })

 <p>The returned value from the example above is:</p>

 @({
 (AND A2 (IF B2 C2 NIL))
 })

 <p>Compare this with the value returned by calling the system function
 @('untranslate') instead on the final three arguments:</p>

 @({
 ACL2 !>(untranslate '(if a2 (if b2 c2 'nil) 'nil) nil (w state))
 (AND A2 B2 C2)
 ACL2 !>
 })

 <p>The original structure of the given ``uterm'', @('(and a (if b c nil))'),
 has been preserved by @('directed-untranslate'), but not by @('untranslate').
 Thus, @('directed-untranslate') may be particularly useful when a given form,
 @('uterm'), translates to a term, @('tterm'), which in turn simplifies to a
 related term, @('sterm'), and your goal is to untranslate @('sterm') in a way
 that preserves structure from @('uterm').</p>

 @({
 General Form:
 (directed-untranslate uterm tterm sterm iff-flg wrld)
 })

 <p>where:</p>

 <ul>

 <li>@('uterm') is an untranslated form that translates to the term,
 @('tterm');</li>

 <li>@('sterm') is a term, which might share a lot of structure with
 @('tterm') (intuitively, we may think of @('sterm') as a simplified version
 of @('tterm'));</li>

 <li>@('iff-flg') is a Boolean; and</li>

 <li>@('wrld') is a logical @('world'), typically @('(w state)').</li>

 </ul>

 <p>The returned form is an untranslated form whose translation is provably
 equal to @('sterm'), except that if @('iff-flg') is true then these need only
 be Boolean equivalent rather than equal.  The goal is that the shared
 structure between @('tterm') and @('sterm') is reflected in similar sharing
 between @('uterm') and the returned form.</p>")

(program)

(defun check-du-inv-fn (uterm tterm wrld)
  (mv-let (erp val)
    (translate-cmp uterm t nil t 'check-du-inv-fn wrld
                   (default-state-vars nil))
    (and (not erp)
         (equal val tterm))))

(defmacro check-du-inv (uterm tterm wrld form)
  #-skip-check-du-inv
  `(assert$ (check-du-inv-fn ,uterm ,tterm ,wrld) ,form)
  #+skip-check-du-inv
  (declare (ignore uterm tterm wrld))
  #+skip-check-du-inv
  form)

(defun macro-abbrev-p-rec (sym body wrld)

; Sym is a macro name with the indicated body.  If this macro simply expands to
; a call of another symbol on its formals, return that symbol unless it is
; another macro, in which case, recur.  Otherwise return nil.

  (let ((args (macro-args sym wrld)))
    (and (null (collect-lambda-keywordps args))
         (case-match body
           (('cons ('quote fn) formal-args)
            (and (equal formal-args (make-true-list-cons-nest args))
                 (let ((new-body (getpropc fn 'macro-body t wrld)))
                   (cond ((eq new-body t) fn)
                         (t (macro-abbrev-p-rec fn new-body wrld))))))
           (& nil)))))

(defun macro-abbrev-p (sym wrld)
  (let ((body (getpropc sym 'macro-body t wrld)))
    (and (not (eq body t))
         (macro-abbrev-p-rec sym body wrld))))

(defun directed-untranslate-drop-conjuncts-rec (conjuncts tterm sterm)

; Tterm is the translation of uterm, where uterm is (and . conjuncts), say,
; (and x1 x2 ... xn), and sterm is of the form (if a b *nil*).  If sterm is the
; translation for some k of (and xk . rest), even if subsequent conjuncts
; differ, then return (xk ... xn) and the corresponding subterm of tterm; else
; return (mv nil nil).

  (case-match tterm
    (('if tterm-1 tterm-2 *nil*)
     (cond ((equal tterm-1 (fargn sterm 1))
            (mv conjuncts tterm))
           (t (directed-untranslate-drop-conjuncts-rec
               (cdr conjuncts) tterm-2 sterm))))
    (& (mv nil nil))))

(defun directed-untranslate-drop-conjuncts (uterm tterm sterm)
  (mv-let (new-conjuncts new-tterm)
    (directed-untranslate-drop-conjuncts-rec (cdr uterm) tterm sterm)
    (if new-tterm
        (mv new-conjuncts new-tterm)
      (mv (cdr uterm) tterm))))

(defun directed-untranslate-drop-disjuncts-rec (disjuncts tterm sterm)

; Tterm is the translation of uterm, where uterm is (or . disjuncts), say, (or
; x1 x2 ... xn), and sterm is of the form (if a a b) or (if a *t* b).  If sterm
; is the translation for some k of (or xk . rest), even if subsequent disjuncts
; differ, then return (xk ... xn) and the corresponding subterm of tterm; else
; return (mv nil nil).

  (case-match tterm
    (('if tterm-1 tterm-1 tterm-2)
     (cond ((equal tterm-1 (fargn sterm 1))
            (mv disjuncts tterm))
           (t (directed-untranslate-drop-disjuncts-rec
               (cdr disjuncts) tterm-2 sterm))))
    (& (mv nil nil))))

(defun directed-untranslate-drop-disjuncts (uterm tterm sterm)
  (mv-let (new-disjuncts new-tterm)
    (directed-untranslate-drop-disjuncts-rec (cdr uterm) tterm sterm)
    (if new-tterm
        (mv new-disjuncts new-tterm)
      (mv (cdr uterm) tterm))))

(defun boolean-fnp (fn wrld)
  (let ((tp (cert-data-tp-from-runic-type-prescription fn wrld)))
    (and tp
         (null (access type-prescription tp :vars))
         (assert$ (null (access type-prescription tp :hyps))
                  (ts-subsetp
                   (access type-prescription tp :basic-ts)
                   *ts-boolean*)))))

(defconst *car-cdr-macro-alist*

; We associate each car/cdr macro M, such as CADDR, with a operations f (car or
; cdr) and g such that M(x) = f(g(x)).

; (loop for x in *ca<d^n>r-alist*
;       collect
;       (let ((name (symbol-name (car x))))
;         (list (car x)
;               (intern (coerce (list #\C (char name 1) #\R) 'string)
;                       "ACL2")
;               (intern (concatenate 'string "C" (subseq name 2 (length name)))
;                       "ACL2"))))

  '((CADR CAR CDR) (CDAR CDR CAR) (CAAR CAR CAR) (CDDR CDR CDR)
    (CAADR CAR CADR) (CDADR CDR CADR) (CADAR CAR CDAR) (CDDAR CDR CDAR)
    (CAAAR CAR CAAR) (CDAAR CDR CAAR) (CADDR CAR CDDR) (CDDDR CDR CDDR)
    (CAAADR CAR CAADR) (CADADR CAR CDADR)
    (CAADAR CAR CADAR) (CADDAR CAR CDDAR)
    (CDAADR CDR CAADR) (CDDADR CDR CDADR)
    (CDADAR CDR CADAR) (CDDDAR CDR CDDAR)
    (CAAAAR CAR CAAAR) (CADAAR CAR CDAAR)
    (CAADDR CAR CADDR) (CADDDR CAR CDDDR)
    (CDAAAR CDR CAAAR) (CDDAAR CDR CDAAR)
    (CDADDR CDR CADDR) (CDDDDR CDR CDDDR)))

(mutual-recursion

(defun directed-untranslate-rec (uterm tterm sterm iff-flg wrld)

; Tterm is the translation of uterm (as may be checked by check-du-inv).  We
; return a form whose translation, with respect to iff-flg, is provably equal
; to sterm.  There may be many such untranslations, but we attempt to return
; one that is similar in structure to uterm.  See also directed-untranslate.

  (check-du-inv
   uterm tterm wrld
   (cond

; The following case is sound, and very reasonable.  However, we anticipate
; applying this function in cases where uterm is not a nice untranslation.
; This may change in the future.

;   ((equal tterm sterm)
;    uterm)

    ((or (variablep sterm)
         (fquotep sterm)
         (variablep tterm)
         (fquotep tterm)
         (atom uterm))
     (untranslate sterm iff-flg wrld))
    (t
     (or
      (and (not (member-eq (car uterm) ; handled elsewhere; avoid looping
                           '(or and)))
           (case-match tterm
             (('if ('not &) & &)
              (case-match sterm
                (('if tst tbr fbr)
                 (case-match tst
                   (('not &) nil)
                   (('if & *nil* *t*) nil)
                   (& (directed-untranslate-rec uterm
                                                tterm
                                                (fcons-term* 'if
                                                             (dumb-negate-lit tst)
                                                             fbr
                                                             tbr)
                                                iff-flg wrld))))
                (& nil)))
             (& nil)))
      (and (ffn-symb-p tterm 'not)
           (case-match sterm
             (('if x *nil* *t*)
              (directed-untranslate-rec uterm
                                        tterm
                                        (dumb-negate-lit x)
                                        iff-flg wrld))
             (& nil)))
      (cond
       ((eq (car uterm) 'cond)
        (let ((clauses (directed-untranslate-into-cond-clauses
                        (cdr uterm) tterm sterm iff-flg wrld)))
          (case-match clauses
            ((('t x))
             x)
            (& (cons 'cond clauses)))))
       ((eq (car uterm) 'implies)
        (mv-let (flg x y)
          (case-match sterm
            (('if x ('if y *t* *nil*) *t*)
             (mv t x y))
            (('if x y *t*)
             (mv t x y))
            (('if x *t* ('if y *t* *nil*))
             (mv t (list 'not x) y))
            (&
             (mv nil nil nil)))
          (cond (flg (list 'implies
                           (directed-untranslate-rec (cadr uterm)
                                                     (fargn tterm 1)
                                                     x
                                                     t
                                                     wrld)
                           (directed-untranslate-rec (caddr uterm)
                                                     (fargn tterm 2)
                                                     y
                                                     t
                                                     wrld)))
                (t (untranslate sterm nil wrld)))))
       ((and (member-eq (car uterm) '(or and))
             (consp (cddr uterm)) ; at least two arguments
             (eq (ffn-symb sterm) 'if)
             (case-match sterm ; following similar handling in untranslate1

; We could also require more; for example, in the OR case, (eq (ffn-symb tterm)
; 'if) and (equal (fargn tterm 1) (fargn tterm 2)).  But any such requirements
; are probably always true, and even if not, we are happy to try to recover an
; OR or AND directly from sterm as follows.

               (('if & *nil* *t*) ; generate a NOT, not an AND or OR
                nil)
               (('if x1 x2 *nil*)
                (and (eq (car uterm) 'and) ; tterm has the form (if x1' x2' *nil*)
                     (mv-let
                       (conjuncts tterm)
                       (directed-untranslate-drop-conjuncts uterm tterm sterm)
                       (untranslate-and
                        (directed-untranslate-rec (car conjuncts)
                                                  (fargn tterm 1)
                                                  x1
                                                  t
                                                  wrld)
                        (directed-untranslate-rec (if (consp (cddr conjuncts))
                                                      (cons 'and (cdr conjuncts))
                                                    (cadr conjuncts))
                                                  (fargn tterm 2)
                                                  x2
                                                  iff-flg
                                                  wrld)
                        iff-flg))))
               (('if x1 *nil* x2)
                (and (eq (car uterm) 'and) ; tterm has the form (if x1' x3' *nil*)
                     (directed-untranslate-rec uterm
                                               tterm
                                               (fcons-term* 'if
                                                            (dumb-negate-lit x1)
                                                            x2
                                                            *nil*)
                                               iff-flg
                                               wrld)))
               (('if x1 x1 x2)
                (and (eq (car uterm) 'or) ; tterm has the form (if x1' x1' x2')
                     (mv-let
                       (disjuncts tterm)
                       (directed-untranslate-drop-disjuncts uterm tterm sterm)
                       (untranslate-or
                        (directed-untranslate-rec (car disjuncts)
                                                  (fargn tterm 1)
                                                  x1
                                                  iff-flg
                                                  wrld)
                        (directed-untranslate-rec (if (consp (cddr disjuncts))
                                                      (cons 'or (cdr disjuncts))
                                                    (cadr disjuncts))
                                                  (fargn tterm 3)
                                                  x2
                                                  iff-flg
                                                  wrld)))))
               (('if x1 x2 *t*)
                (directed-untranslate-rec uterm
                                          tterm
                                          (fcons-term* 'if
                                                       (dumb-negate-lit x1)
                                                       *t*
                                                       x2)
                                          iff-flg
                                          wrld))
               (('if x1 *t* x2)
                (and (eq (car uterm) 'or) ; tterm has the form (if x1' t x2')
                     (cond
                      ((or iff-flg
                           (and (nvariablep x1)
                                (not (fquotep x1))
                                (boolean-fnp (ffn-symb x1) wrld)))
                       (mv-let
                         (disjuncts tterm)
                         (directed-untranslate-drop-disjuncts uterm tterm sterm)
                         (untranslate-or
                          (directed-untranslate-rec (car disjuncts)
                                                    (fargn tterm 1)
                                                    x1
                                                    t
                                                    wrld)
                          (directed-untranslate-rec (if (consp (cddr disjuncts))
                                                        (cons 'or (cdr disjuncts))
                                                      (cadr disjuncts))
                                                    (fargn tterm 3)
                                                    x2
                                                    iff-flg
                                                    wrld))))
                      (t nil))))
               (& nil))))
       ((and (eq (car uterm) '>) ; (> x0 y0)
             (eq (car sterm) '<) ; (< y1 x1)
             (eq (car tterm) '<)) ; (< y2 y1)
        (list '>
              (directed-untranslate-rec
               (cadr uterm)
               (fargn tterm 2) (fargn sterm 2) nil wrld)
              (directed-untranslate-rec
               (caddr uterm)
               (fargn tterm 1) (fargn sterm 1) nil wrld)))
       ((eq (car uterm) '<=) ; (<= x0 y0), translates as (not (< y1 x1))
        (or (case-match tterm
              (('not ('< y1 x1)) ; should always match
               (case-match sterm
                 (('not ('< y2 x2))
                  (cons '<= (directed-untranslate-lst
                             (cdr uterm) ; (x0 y0)
                             (list x1 y1) ; from tterm
                             (list x2 y2) ; from sterm
                             nil
                             wrld)))
                 (& nil)))
              (& nil))
            (untranslate sterm iff-flg wrld)))
       ((eq (car uterm) '>=) ; (>= x0 y0), translates as (not (< x1 y1))
        (or (case-match tterm
              (('not ('< x1 y1))
               (case-match sterm
                 (('not ('< x2 y2))
                  (cons '>= (directed-untranslate-lst
                             (cdr uterm) ; (x0 y0)
                             (list x1 y1) ; from tterm
                             (list x2 y2) ; from sterm
                             nil
                             wrld)))
                 (& nil)))
              (& nil))
            (untranslate sterm iff-flg wrld)))
       (t
        (or
         (case-match uterm
           (('list) uterm)
           (('list x) ; tterm is (cons x' nil)
            (case-match sterm
              (('cons a *nil*)
               (list 'list
                     (directed-untranslate-rec x (fargn tterm 1) a nil wrld)))
              (& nil)))
           (('list x . y) ; same translation as for (cons x (list . y))
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
           (('list* x) ; same transation as for x
            (list 'list*
                  (directed-untranslate-rec x tterm sterm nil wrld)))
           (('list* x . y) ; same translation as for (cons x (list* . y))
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
         (and (member-eq (ffn-symb tterm) '(car cdr))
              (directed-untranslate-car-cdr-nest uterm tterm sterm wrld))
         (and (eql (length (fargs sterm))
                   (length (fargs tterm)))
              (let* ((pair (cdr (assoc-eq (ffn-symb sterm)
                                          (untrans-table wrld))))
                     (op (if pair
                             (car pair)
                           (or (cdr (assoc-eq (ffn-symb sterm)
                                              (table-alist
                                               'std::define-macro-fns
                                               wrld)))
                               (ffn-symb sterm)))))
                (cond
                 ((symbolp (ffn-symb sterm))
                  (cond ((and (cdr pair) ; hence pair, and we might right-associate
                              (case-match uterm
                                ((!op & & & . &) t) ; we want to flatten
                                (& nil)))           ; (op x (op y ...))
                         (let ((arg1 (directed-untranslate-rec
                                      (cadr uterm)
                                      (fargn tterm 1) (fargn sterm 1) nil
                                      wrld))
                               (arg2 (directed-untranslate-rec
                                      (cons op (cddr uterm))
                                      (fargn tterm 2) (fargn sterm 2) nil wrld)))
                           (cond ((and (consp arg2)
                                       (eq (car arg2) op))
                                  (list* op arg1 (cdr arg2)))
                                 (t (list op arg1 arg2)))))
                        ((or (eq (car uterm) op)
                             (eq (car uterm) (ffn-symb tterm))
                             (eq (macro-abbrev-p op wrld) (ffn-symb tterm)))
                         (cons op (directed-untranslate-lst
                                   (cdr uterm) (fargs tterm) (fargs sterm)
                                   (case (ffn-symb sterm)
                                     (if (list t iff-flg iff-flg))
                                     (not '(t))
                                     (otherwise nil))
                                   wrld)))
                        ((equal sterm tterm)

; It's probably better to use the macro at hand than to untranslate.

                         uterm)
                        (t nil)))
                 (t nil))))
         (untranslate sterm iff-flg wrld)))))))))

(defun directed-untranslate-lst (uargs targs sargs iff-flg-lst wrld)
  (cond ((endp uargs) nil)
        (t (cons (directed-untranslate-rec (car uargs)
                                           (car targs)
                                           (car sargs)
                                           (car iff-flg-lst)
                                           wrld)
                 (directed-untranslate-lst (cdr uargs)
                                           (cdr targs)
                                           (cdr sargs)
                                           (cdr iff-flg-lst)
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

(defun directed-untranslate-car-cdr-nest (uterm tterm sterm wrld)

; Tterm is a call of car or cdr.  Uterm may be a name in *ca<d^n>r-alist*, such
; as CADDR.  Ad-len is the number of A and D characters in that name, which is
; 2, 3, or 4.  We return nil or else a suitable result for
; (directed-untranslate uterm tterm sterm wrld)

  (and (eq (ffn-symb tterm) (ffn-symb sterm))
       (let ((triple (assoc-eq (car uterm) *car-cdr-macro-alist*)))
         (and triple
              (let* ((op1 (cadr triple))
                     (op2 (caddr triple)))
                (and (eq op1 (ffn-symb tterm))
                     (let ((x (directed-untranslate-rec
                               (list op2 (cadr uterm))
                               (fargn tterm 1)
                               (fargn sterm 1)
                               nil wrld)))
                       (and (consp x)
                            (eq (car x) op2)
                            (list (car uterm) (cadr x))))))))))
)

(defun directed-untranslate (uterm tterm sterm iff-flg wrld)

; Uterm is an untranslated form that translates to the term, tterm.  Sterm is a
; term, which may largely agree with tterm.  The result is an untranslated form
; whose translation is provably equal to sterm, with the goal that the sharing
; of structure between tterm and sterm is reflected in similar sharing between
; uterm and that result.

; Current limitations include:

; - If sterm has similar structure to a proper subterm of tterm rather than to
;   tterm itself, then uterm will probably be useless in the untranslation.

; - Let, let*, case, and perhaps some other useful constructs could probably be
;   reasonably handled, but aren't yet.

  (directed-untranslate-rec uterm tterm sterm iff-flg wrld))
