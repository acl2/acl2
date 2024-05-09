; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book was renamed from file remove-guard-holders-strong-2.lisp in late
; January, 2023 and also expanded.

; Anyone is welcome to complete this work, BUT: first inform Matt Kaufmann,
; matthew.j.kaufmann@gmail.com, both to avoid potential duplication of effort
; and to ensure that Matt is available to complete integration of this work
; into ACL2.  The latter is especially important if you just ship Matt this and
; modified files, rather than going through the full process described in :doc
; verify-guards-for-system-functions and then either (a) sending Matt a tarball
; with the new and changed files and suitable instructions, or (b) going
; through the additional process described in :doc
; developers-guide-contributing.

; WARNING!  This book has an invalid skip-proofs!  This is explained below.  We
; are nevertheless making this a book, simply so that it continues to be
; certified during regression.  It should certify in normal ACL2 and may
; certify in ACL2 built for the "make devel-check" test.  It makes a start
; towards completing termination and guard verification for
; remove-guard-holders, building on the book remove-guard-holders.lisp.

; The function term-measure was inspired by ACL2 community book
; centaur/meta/lambda-measure.lisp.  It is an attempt to create a suitable
; measure for function clean-up-dirty-lambda-objects.  Unfortunately, it
; doesn't work; this may be close, though, and further explanation is below.

(in-package "ACL2")

(include-book "remove-guard-holders")

(defun sumlist (lst)
  (cond ((atom lst) 0)
        (t (+ (car lst) (sumlist (cdr lst))))))

(defun term-measure (flg x alist)

; Alist maps variables to their measures.  Flg is non-nil if x is a list;
; otherwise x is a single term.

; As noted above, this function was inspired by ACL2 community book
; centaur/meta/lambda-measure.lisp.

  (declare (xargs :guard (and (if flg
                                  (pseudo-term-listp x)
                                (pseudo-termp x))
                              (symbol-alistp alist)
                              (nat-listp (strip-cdrs alist)))
                  :verify-guards nil))
  (cond ((not (mbt (and (if flg
                            (pseudo-term-listp x)
                          (pseudo-termp x))
                        (symbol-alistp alist)
                        (nat-listp (strip-cdrs alist)))))
         (if flg
             (make-list (len x) :initial-element 0)
           0))
        (flg ; x is a list
         (cond ((endp x) nil)
               (t (cons (term-measure nil (car x) alist)
                        (term-measure t (cdr x) alist)))))
        ((variablep x)
         (let ((pair (assoc-eq x alist)))
           (cond (pair (nfix (cdr pair)))
                 (t 0))))
        ((fquotep x)
         (cond ((syntactically-plausible-lambda-objectp nil (cadr x))
                (1+ (term-measure nil (lambda-object-body (cadr x)) nil)))
               (t
; This measure fails to work, but perhaps it could be fixed by replacing 0
; below by something like (1+ (cons-count x)).
                0)))
        ((flambdap (ffn-symb x))
         (+ 1
            (term-measure nil
                          (lambda-body (ffn-symb x))
                          (pairlis$ (lambda-formals (ffn-symb x))
                                    (term-measure t (fargs x) alist)))
            (sumlist (term-measure t (fargs x) alist))
            (len (fargs x))))
        (t (+ 1
              (sumlist (term-measure t (fargs x) alist))
; Accommodate remove-guard-holders1 addition of args to too-short arglist.
              (cond ((eq (ffn-symb x) 'cons-with-hint)
                     (max 2 (len (fargs x))))
                    ((eq (ffn-symb x) 'do$)
                     (max 7 (len (fargs x))))
                    (t (len (fargs x))))))))

(defthm nat-listp-make-list-ac
  (implies (and (natp val)
                (nat-listp ac))
           (nat-listp (make-list-ac n val ac))))

(defthm natp-sumlist
  (implies (nat-listp x)
           (natp (sumlist x)))
  :rule-classes :type-prescription)

(defthm term-measure-type
  (implies (nat-listp (strip-cdrs alist))
           (let ((val (term-measure flg x alist)))
             (if flg
                 (nat-listp val)
               (natp val))))
  :rule-classes nil)

(defthm natp-term-measure-nil
  (natp (term-measure nil x alist))
  :hints (("Goal" :use ((:instance term-measure-type (flg nil)))))
  :rule-classes :type-prescription)

(defthm nat-listp-term-measure-list
  (nat-listp (term-measure t x alist))
  :hints (("Goal" :use ((:instance term-measure-type (flg t)))))
  :rule-classes :type-prescription)

(defthm natp-term-measure-num
  (natp (sumlist (term-measure t x alist)))
  :hints (("Goal" :use ((:instance term-measure-type (flg t)))))
  :rule-classes :type-prescription)

; Start proof of len-term-measure-list.

(local (defthm len-make-list-ac
         (equal (len (make-list-ac n val ac))
                (+ (nfix n) (len ac)))))

(defthm len-term-measure-list
  (equal (len (term-measure t x alist))
         (len x)))

(local (in-theory (disable syntactically-plausible-lambda-objectp)))

; Start proof of term-measure-lemma-1.

(defthm symbol-alistp-pairlis$
  (implies (symbol-listp x)
           (symbol-alistp (pairlis$ x y))))

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))

(defthm nat-listp-strip-cdrs-pairlis$
  (implies (and (nat-listp lst2)
                (<= (len lst1) (len lst2)))
           (nat-listp (strip-cdrs (pairlis$ lst1 lst2)))))

(defun tm-induct-hint (flg x alist1 alist2)
  (cond
   ((not (mbt (and (if flg
                       (pseudo-term-listp x)
                     (pseudo-termp x))
                   (symbol-alistp alist1)
                   (symbol-alistp alist2)
                   (nat-listp (strip-cdrs alist1))
                   (nat-listp (strip-cdrs alist2)))))
    0)
   (flg ; x is a list
    (cond ((endp x) nil)
          (t (cons (tm-induct-hint nil (car x) alist1 alist2)
                   (tm-induct-hint t (cdr x) alist1 alist2)))))
   ((variablep x)
    0)
   ((fquotep x)
    (cond ((syntactically-plausible-lambda-objectp nil (cadr x))
           (tm-induct-hint nil (lambda-object-body (cadr x)) nil nil))
          (t 0)))
   ((flambdap (ffn-symb x))
    (cons (tm-induct-hint nil
                          (lambda-body (ffn-symb x))
                          (pairlis$ (lambda-formals (ffn-symb x))
                                    (term-measure t (fargs x) alist1))
                          (pairlis$ (lambda-formals (ffn-symb x))
                                    (term-measure t (fargs x) alist2)))
          (tm-induct-hint t (fargs x) alist1 alist2)))
   (t (tm-induct-hint t (fargs x) alist1 alist2))))

(defthm strip-cars-pairlis$
  (implies (true-listp x)
           (equal (strip-cars (pairlis$ x y))
                  x)))

(defthm strip-cdrs-pairlis$
  (implies (and (force (equal (len x) (len y)))
                (force (true-listp y)))
           (equal (strip-cdrs (pairlis$ x y))
                  y)))

(defthm consp-strip-cars
  (implies (assoc-equal a x)
           (consp (strip-cars x)))
  :rule-classes :type-prescription)

(defthm member-equal-strip-cars
  (implies (alistp x)
           (iff (member-equal a (strip-cars x))
                (assoc-equal a x))))

(defthm not-strip-cars
  (implies (alistp x)
           (iff (strip-cars x)
                x)))

(defun alist-all<= (x y)
  (if (consp x)
      (and (consp y)
           (equal (caar x) (caar y))
           (<= (cdar x) (cdar y))
           (alist-all<= (cdr x) (cdr y)))
    t))

(defun all<= (x y)
  (if (consp x)
      (and (consp y)
           (<= (car x) (car y))
           (all<= (cdr x) (cdr y)))
    t))

(defthm alist-all<=-implies-<=-assoc-equal
  (implies (and (alist-all<= alist1 alist2)
                (nat-listp (strip-cdrs alist2)))
           (<= (cdr (assoc-equal x alist1))
               (cdr (assoc-equal x alist2)))))

(defthm natp-cdr-assoc-equal
  (implies (and (nat-listp (strip-cdrs alist))
                (assoc-equal x alist))
           (natp (cdr (assoc-equal x alist))))
  :rule-classes :type-prescription)

(defthm all<=-implies-alist-all<=-pairlis&
  (implies (and (all<= x y)
                (nat-listp y))
           (alist-all<= (pairlis$ lst x) (pairlis$ lst y))))

(defthm alist-all-<=-preserves-assoc-equal-iff
  (implies (and (alist-all<= x y)
                (assoc-equal a x)
                (alistp y))
           (assoc-equal a y)))

(defthm <=-sumlist
  (implies (and (all<= x y)
                (nat-listp y))
           (<= (sumlist x) (sumlist y)))
  :rule-classes :linear)

(defthm term-measure-lemma-1-1-general
  (implies (and (if flg
                    (pseudo-term-listp x)
                  (pseudo-termp x))
                (symbol-alistp alist1)
                (symbol-alistp alist2)
                (nat-listp (strip-cdrs alist1))
                (nat-listp (strip-cdrs alist2))
                (alist-all<= alist1 alist2))
           (if flg
               (all<= (term-measure flg x alist1)
                      (term-measure flg x alist2))
             (<= (term-measure flg x alist1)
                 (term-measure flg x alist2))))
  :hints (("Goal" :induct (tm-induct-hint flg x alist1 alist2)
           :expand ((term-measure nil x alist1)
                    (term-measure nil x alist2))))
  :rule-classes nil)

(defthm term-measure-lemma-1-1
  (implies (and (pseudo-termp x)
                (nat-listp (strip-cdrs alist))
                (symbol-alistp alist))
           (<= (term-measure nil x nil)
               (term-measure nil x alist)))
  :hints (("Goal" :use ((:instance term-measure-lemma-1-1-general
                                   (alist1 nil)
                                   (alist2 alist)
                                   (flg nil)))))
  :rule-classes :linear)

(defthm true-listp-term-measure-list
  (true-listp (term-measure t term alist))
  :rule-classes :type-prescription)

(defthm term-measure-lemma-1
  (implies (and (pseudo-termp term)
                (consp term)
                (consp (car term)))
           (< (term-measure nil (caddr (car term)) nil)
              (term-measure nil term nil)))
  :rule-classes :linear)

(defthm term-measure-lemma-2
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal 'quote (car term))))
           (< (sumlist (term-measure t (cdr term) nil))
              (term-measure nil term nil)))
  :rule-classes :linear)

; Start proof of term-measure-lemma-3-1 (for term-measure-lemma-3).

(defthm len-mv-nth-1-remove-guard-holders1-lst
  (equal (len (mv-nth 1 (remove-guard-holders1-lst lst lamp)))
         (len lst)))

(defthm all<=-reflexive
  (all<= x x))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm len-take
  (equal (len (take n x))
         (nfix n)))

(defthm term-measure-flg-t
  (implies (and (syntaxp (not (eq flg *t*)))
                flg)
           (equal (term-measure flg x alist)
                  (term-measure t x alist))))

(defthm pseudo-term-listp-append
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (append x y))))

(defthm term-measure-t-append
  (implies (and flg
                (force (pseudo-term-listp x))
                (force (pseudo-term-listp y))
                (force (symbol-alistp alist))
                (force (nat-listp (strip-cdrs alist))))
           (equal (term-measure flg (append x y) alist)
                  (append (term-measure flg x alist)
                          (term-measure flg y alist)))))

(defthm sumlist-append
  (equal (sumlist (append x y))
         (+ (sumlist x) (sumlist y))))

(defthm +-hack-1
  (implies (and (syntaxp (and (quotep i) (integerp (unquote i))))
                (syntaxp (and (quotep j) (integerp (unquote j))))
                (syntaxp (< (unquote i) (unquote j))))
           (iff (< (+ i x)
                   j)
                (< x
                   (- j i)))))

(defthm pseudo-term-listp-take
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (take n x))))

(defthm term-measure-t-take
  (implies (and (pseudo-term-listp lst)
                (symbol-alistp alist)
                (nat-listp (strip-cdrs alist))
                (<= n (len lst)))
           (equal (term-measure t (take n lst) alist)
                  (take n (term-measure t lst alist))))
  :hints (("Goal" :induct (take n lst))))

(defthm sumlist-take
  (implies (nat-listp lst)
           (<= (sumlist (take n lst))
               (sumlist lst)))
  :rule-classes :linear)

(defthm consp-mv-nth-1-remove-guard-holders1-lst
  (equal (consp (mv-nth 1 (remove-guard-holders1-lst x lamp)))
         (consp x))
  :hints (("Goal" :expand ((remove-guard-holders1-lst x lamp)))))

(defun rgh-flg-exit (changedp1 changedp2 a b x)
  (cond ((or changedp1 changedp2)
         (mv t (cons a b)))
        (t (mv nil x))))

(defun rgh-base (x)
  (or (variablep x)
      (fquotep x)
      (and (eq (ffn-symb x) 'HIDE)
           (remove-guard-holders-blocked-by-hide-p))))

(defun rgh-lambda-case (x)
  (case-match
    x
    ((('LAMBDA ('VAR) ('THE-CHECK & & 'VAR))
      val)
     (mv 0 val nil nil nil))
    ((('LAMBDA formals ('RETURN-LAST ''MBE1-RAW & logic))
      . args)
     (mv 1 nil formals logic args))
    (&
     (mv 2 nil nil nil nil))))

(defun rgh-lambda-exit (lamp lambda-formals lambda-body args
                             changedp0 changedp1 changedp2 x)
  (cond ((and lamp
              (consp lambda-formals)
              (null (cdr lambda-formals))
              (eq (car lambda-formals) lambda-body))
         (mv t (car args)))
        ((and lamp
              (trivial-lambda-p lambda-formals args lambda-body))
         (mv t lambda-body))
        ((or changedp1 changedp2)
         (mv t
             (mcons-term
              (if changedp1
                  (make-lambda lambda-formals lambda-body)
                (ffn-symb x))
              args)))
        (t (mv changedp0 x))))

(defun rgh-symbolp-exit (x args changedp0 changedp1)
  (cond ((and (eq (ffn-symb x) 'DO$)
              (quotep (fargn x 6))
              (quotep (fargn x 7))
              (unquote (fargn x 6))
              (unquote (fargn x 7)))
         (mv t (mcons-term 'DO$ (append (take 5 args) (list *nil* *nil*)))))
        ((null changedp1)
         (cond ((quote-listp args)
                (let ((new-x (mcons-term (ffn-symb x)
                                         args)))
                  (cond ((equal x new-x) ; even if not eq
                         (mv changedp0 x))
                        (t (mv t new-x)))))
               (t (mv changedp0 x))))
        (t (mv t (mcons-term (ffn-symb x) args)))))

(defun remove-guard-holders1-flg (flg changedp0 x lamp)
  (cond
   (flg (cond ((endp x) (mv nil nil))
              (t (mv-let (changedp1 a)
                   (remove-guard-holders1-flg nil nil (car x) lamp)
                   (mv-let (changedp2 b)
                     (remove-guard-holders1-flg t nil (cdr x) lamp)
                     (rgh-flg-exit changedp1 changedp2 a b x))))))
   ((rgh-base x) (mv changedp0 x))
   ((member-eq (ffn-symb x) '(RETURN-LAST MV-LIST THE-CHECK))
    (remove-guard-holders1-flg nil t (car (last (fargs x))) lamp))
   ((eq (ffn-symb x) 'CONS-WITH-HINT)
    (mv-let
      (changedp1 arg1)
      (remove-guard-holders1-flg nil nil (fargn x 1) lamp)
      (declare (ignore changedp1))
      (mv-let
        (changedp2 arg2)
        (remove-guard-holders1-flg nil nil (fargn x 2) lamp)
        (declare (ignore changedp2))
        (mv t (mcons-term* 'cons arg1 arg2)))))
   ((eq (ffn-symb x) 'TO-DF)
    (let ((arg (fargn x 1)))
      (cond ((and (quotep arg)
                  (dfp (unquote arg)))
             (mv t arg))
            (t (mv-let
                 (changedp1 arg1)
                 (remove-guard-holders1 nil arg lamp)
                 (mv changedp1
                     (fcons-term* 'TO-DF arg1)))))))
   ((eq (ffn-symb x) 'FROM-DF)
    (mv-let (changedp1 arg1)
      (remove-guard-holders1 nil (fargn x 1) lamp)
      (declare (ignore changedp1))
      (mv t arg1)))
   ((eq (ffn-symb x) 'DF0)
    (mv t *0*))
   ((eq (ffn-symb x) 'DF1)
    (mv t *1*))
   ((flambdap (ffn-symb x))
    (mv-let (case val formals logic args)
      (rgh-lambda-case x)
      (case case
        (0
         (remove-guard-holders1-flg nil t val lamp))
        (1
         (mv-let
           (changedp1 args1)
           (remove-guard-holders1-flg t nil args lamp)
           (declare (ignore changedp1))
           (mv-let
             (changedp2 logic2)
             (remove-guard-holders1-flg nil nil logic lamp)
             (declare (ignore changedp2))
             (mv t (subcor-var formals args1 logic2)))))
        (otherwise
         (mv-let
           (changedp1 lambda-body)
           (remove-guard-holders1-flg nil nil
                                      (lambda-body (ffn-symb x))
                                      lamp)
           (let ((lambda-formals (lambda-formals (ffn-symb x))))
             (mv-let
               (changedp2 args)
               (remove-guard-holders1-flg t nil (fargs x) lamp)
               (rgh-lambda-exit lamp lambda-formals lambda-body args
                                changedp0 changedp1 changedp2 x))))))))
   (t (mv-let
        (changedp1 args)
        (remove-guard-holders1-flg t nil (fargs x) lamp)
        (rgh-symbolp-exit x args changedp0 changedp1)))))

(in-theory (disable cons-term))

(defthmd remove-guard-holders-flg-elim
  (equal (remove-guard-holders1-flg flg changedp0 x lamp)
         (if flg
             (remove-guard-holders1-lst x lamp)
           (remove-guard-holders1 changedp0 x lamp))))

(defthm symbol-forward-to-rgh-base
  (implies (symbolp x)
           (rgh-base x))
  :rule-classes :forward-chaining)

(defthm fquotep-forward-to-rgh-base
  (implies (equal (car x) 'quote)
           (rgh-base x))
  :rule-classes :forward-chaining)

(defthm hide-forward-to-rgh-base
  (implies (and (equal (ffn-symb x) 'HIDE)
                (remove-guard-holders-blocked-by-hide-p))
           (rgh-base x))
  :rule-classes :forward-chaining)

; The following event, term-measure-lemma-3-1-1, was intended to support the
; proof of term-measure-lemma-3-1 (below it) as an immediate corollary, which
; in turn supports term-measure-lemma-3 (below that as an immediate corollary).
; There were a lot of cases in term-measure-lemma-3-1-1, but then I found a
; counterexample to the real goal, term-measure-lemma-3, as noted below.

#|
(defthm term-measure-lemma-3-1-1
  (if flg
      (implies (pseudo-term-listp x)
               (all<= (term-measure flg
                                    (mv-nth 1
                                            (remove-guard-holders1-flg flg c x lamp))
                                    nil)
                      (term-measure flg x nil)))
    (implies (pseudo-termp x)
             (<= (term-measure nil
                               (mv-nth 1
                                       (remove-guard-holders1-flg flg c x lamp))
                               nil)
                 (term-measure nil x nil))))
  :hints (("Goal"
           :in-theory (disable rgh-flg-exit
                               rgh-base
                               rgh-lambda-case
                               rgh-lambda-exit
                               rgh-symbolp-exit)
           :induct (remove-guard-holders1-flg flg c x lamp)
           :do-not '(eliminate-destructors)))
  :rule-classes nil)

(skip-proofs
(defthm term-measure-lemma-3-1
  (implies (pseudo-termp term)
           (<= (term-measure nil
                             (mv-nth 1 (remove-guard-holders1 c term lamp))
                             nil)
               (term-measure nil term nil)))
  :rule-classes :linear)
)
|#

;;; UGH!  Here is a counterexample to term-measure-lemma-3.
(thm
 (let ((term (cons 'cons '('lambda '((X) (CONS X X))))))
   (not (implies (pseudo-termp term)
                 (<= (term-measure nil (remove-guard-holders-weak term nil) nil)
                     (term-measure nil term nil))))))

; False; see above.  But let's see if it suffices to finish the proof; maybe a
; tweak to term-measure will allow everything to go through....
(skip-proofs
(defthm term-measure-lemma-3
  (implies (pseudo-termp term)
           (<= (term-measure nil (remove-guard-holders-weak term lamp) nil)
               (term-measure nil term nil)))
  :rule-classes :linear)
)

(defthm
  well-formed-lambda-objectp-implies-syntactically-plausible-lambda-objectp
  (implies (well-formed-lambda-objectp x wrld)
           (syntactically-plausible-lambda-objectp nil x)))

(defthm term-measure-lemma-4
  (implies (and (not (pseudo-termp term9))
                (well-formed-lambda-objectp (list 'lambda term7 term9)
                                            wrld))
           (< (term-measure nil
                            (remove-guard-holders-weak term9 lamp)
                            nil)
              1))
  :hints (("Goal" :in-theory (enable syntactically-plausible-lambda-objectp))))

(defthm term-measure-lemma-5
  (implies (and (not (pseudo-termp term11))
                (well-formed-lambda-objectp (list 'lambda term7 term9 term11)
                                            wrld))
           (< (term-measure nil
                            (remove-guard-holders-weak term11 lamp)
                            nil)
              1))
  :hints (("Goal" :in-theory (enable syntactically-plausible-lambda-objectp))))

(in-theory (disable well-formed-lambda-objectp
                    syntactically-plausible-lambda-objectp
                    remove-guard-holders-weak))

(verify-termination
  (clean-up-dirty-lambda-objects
   (declare (xargs :measure (term-measure nil term nil)
                   :hints (("Goal" :expand ((term-measure nil term nil))))
                   :verify-guards nil)))
  (clean-up-dirty-lambda-objects-lst
   (declare (xargs :measure (+ (sumlist (term-measure t terms nil))
                               (len terms))
                   :hints (("Goal" :expand ((term-measure nil term nil))))
                   :verify-guards nil))))

(verify-termination may-contain-dirty-lambda-objectsp
	 (declare (xargs :verify-guards nil)))

(verify-termination possibly-clean-up-dirty-lambda-objects)
(verify-termination remove-guard-holders
  (declare (xargs :verify-guards nil)))
