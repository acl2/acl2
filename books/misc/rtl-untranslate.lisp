; Copyright (C) 2004-2015 Advanced Micro Devices, Inc.
; All rights reserved.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Matt Kaufmann, included starting with ACL2 Version 2.8.

; Replacement function rtl-untranslate for predefined untranslate, suitable for
; untranslating (foo$ x $path) to (foo x) and e.g. (land a (land b c)) to
; (land a b c).  Additional documentation may be written if requested.

(in-package "ACL2")

; We assume that all signal names end in $, and that a corresponding macro
; leaves off the $ to represent "optional" argument $path.  Example:

; (sig$ n $path) <=> (sig n).

(program)

(include-book "symbol-btree")

(defun rtl-untrans-lop (lop x y width)
  (cond ((and (consp y)
              (eq (car y) lop)
              (equal (car (last y)) width))

; This is the case (lop x (lop y1 y2 ... yk width) width).

         (list* lop x (cdr y)))
        (t
         (list lop x y width))))

(defun sum-cat-sizes (lst acc)
  (if (endp lst)
      acc
    (if (acl2-numberp (cadr lst))
        (sum-cat-sizes (cddr lst)
                        (+ (cadr lst) acc))
      nil)))

(defun rtl-untrans-cat (x xsize y ysize)
  (cond ((and (consp y)
              (eq (car y) 'cat)
              (integerp ysize)
              (eql ysize
                   (sum-cat-sizes (cdr y) 0)))

; This is the case (lop x (lop y1 y2 ... yk width) width).

         (list* 'cat x xsize (cdr y)))
        (t
         (list 'cat x xsize y ysize))))

(defun cond1-length (term)
  (case-match term
    (('if1 & & z) (1+ (cond1-length z)))
    (& 1)))

(defmacro rtl-untrans-and (&rest args)
  (cons 'untranslate-and args))

(defmacro rtl-untrans-or (&rest args)
  (cons 'untranslate-or args))

(defconst *rtl-untrans-boolean-primitives*
  *untranslate-boolean-primitives*)

(mutual-recursion

; Changes from the original untranslate1 nest are indicated with:
;;; START addition for rtl-untrans1
; .....
;;; END addition for rtl-untrans1
; (not including obvious changes, like *untranslate-boolean-primitives* to
; *rtl-untrans-boolean-primitives*, untranslate1 to rtl-untrans1, and
; untranslate-if to rtl-untrans-if).

(defun rtl-untrans1 (term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)

; Warning: It would be best to keep this in sync with
; obviously-iff-equiv-terms, specifically, giving similar attention in both to
; functions like implies, iff, and not, which depend only on the propositional
; equivalence class of each argument.

; Warning: Keep in sync with ACL2 source function untranslate1.

; We return a Lisp form that translates to term if iff-flg is nil and
; that translates to a term iff-equivalent to term if iff-flg is t.
; Wrld is an ACL2 logical world, which may be used to improve the
; appearance of the result, in particular to allow (nth k st) to be
; printed as (nth *field-name* st) if st is a stobj name and
; field-name is the kth field name of st; similarly for update-nth.
; It is perfectly appropriate for wrld to be nil if such extra
; information is not important.

; Note: The only reason we need the iff-flg is to let us translate (if
; x1 t x2) into (or x1 x2) when we are in an iff situation.  We could
; ask type-set to check that x1 is Boolean, but that would require
; passing wrld into untranslate.  That, in turn, would require passing
; wrld into such syntactic places as prettyify-clause and any other
; function that might want to print a term.

; Warning: This function may not terminate.  We should consider making it
; primitive recursive by adding a natural number ("count") parameter.

  (let ((term (if preprocess-fn
                  (mv-let (erp term1)
                          (ev-fncall-w! preprocess-fn
                                       (list term wrld)
                                       wrld
                                       nil ; user-stobj-alist
                                       nil ; safe-mode
                                       nil ; gc-off
                                       nil ; hard-error-returns-nilp
                                       t   ; okp
                                       )
                          (or (and (null erp) term1)
                              term))
                term)))
    (cond ((variablep term) term)
          ((fquotep term)
           (cond ((or (acl2-numberp (cadr term))
                      (stringp (cadr term))
                      (characterp (cadr term))
                      (eq (cadr term) nil)
                      (eq (cadr term) t)
                      (keywordp (cadr term)))
                  (cadr term))
                 (t term)))
          ((flambda-applicationp term)
           (make-let-or-let*
            (collect-non-trivial-bindings (lambda-formals (ffn-symb term))
                                          (rtl-untrans1-lst (fargs term)
                                                            nil
                                                            untrans-tbl sigs-btree lops-alist
                                                            preprocess-fn
                                                            wrld))
            nil ; type-dcls; setting to nil to match legacy (pre-2022) behavior
            (rtl-untrans1 (lambda-body (ffn-symb term)) iff-flg untrans-tbl sigs-btree lops-alist
                          preprocess-fn wrld)))
          ((and (eq (ffn-symb term) 'nth)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 2)
                                               wrld)))
             (list 'nth
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (rtl-untrans1 (fargn term 2) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld))))
          ((and (eq (ffn-symb term) 'update-nth)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 3)
                                               wrld)))
             (list 'update-nth
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (rtl-untrans1 (fargn term 2) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld)
                   (rtl-untrans1 (fargn term 3) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld))))
          ((and (eq (ffn-symb term) 'update-nth-array)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 4)
                                               wrld)))
             (list 'update-nth-array
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (rtl-untrans1 (fargn term 2) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld)
                   (rtl-untrans1 (fargn term 3) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld)
                   (rtl-untrans1 (fargn term 4) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                 wrld))))
          ((eq (ffn-symb term) 'binary-+)
           (cons '+
                 (rtl-untrans1-lst (right-associated-args 'binary-+ term)
                                   nil untrans-tbl sigs-btree lops-alist preprocess-fn wrld)))
          ((eq (ffn-symb term) 'unary-/)
           (list '/ (rtl-untrans1 (fargn term 1) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                  wrld)))
          ((eq (ffn-symb term) 'unary--)
           (list '- (rtl-untrans1 (fargn term 1) nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                  wrld)))
          ((eq (ffn-symb term) 'if)
           (case-match term
             (('if x1 *nil* *t*)
              (list 'not (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist preprocess-fn wrld)))
             (('if x1 x2  *nil*)
              (rtl-untrans-and (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
                               (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 *nil* x2)
              (rtl-untrans-and (list 'not (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist
                                                        preprocess-fn wrld))
                               (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 x1 x2)
              (rtl-untrans-or (rtl-untrans1 x1 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                            wrld)
                              (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                            wrld)))
             (('if x1 x2 *t*)

; Observe that (if x1 x2 t) = (if x1 x2 (not nil)) = (if x1 x2 (not x1)) =
; (if (not x1) (not x1) x2) = (or (not x1) x2).

              (rtl-untrans-or (list 'not (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist
                                                       preprocess-fn wrld))
                              (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                            wrld)))
             (('if x1 *t* x2)
              (cond
               ((or iff-flg
                    (and (nvariablep x1)
                         (not (fquotep x1))
                         (member-eq (ffn-symb x1)
                                    *rtl-untrans-boolean-primitives*)))
                (rtl-untrans-or (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist
                                              preprocess-fn wrld)
                                (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist
                                              preprocess-fn wrld)))
               (t (rtl-untrans-if term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld))))
             (& (rtl-untrans-if term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld))))
;;; START addition for rtl-untrans1
        ((eq (ffn-symb term) 'if1)
         (cond ((> (cond1-length term) 2)
                (cons 'cond1 (rtl-untrans-into-cond1-clauses term untrans-tbl sigs-btree lops-alist
                                                             preprocess-fn wrld)))
               (t (list 'if1
                        (rtl-untrans1 (fargn term 1) nil untrans-tbl sigs-btree
                                      lops-alist preprocess-fn wrld)
                        (rtl-untrans1 (fargn term 2) nil untrans-tbl sigs-btree
                                      lops-alist preprocess-fn wrld)
                        (rtl-untrans1 (fargn term 3) nil untrans-tbl sigs-btree
                                      lops-alist preprocess-fn wrld)))))
;;; END addition for rtl-untrans1
          ((and (eq (ffn-symb term) 'not)
                (nvariablep (fargn term 1))
                (not (fquotep (fargn term 1)))
                (member-eq (ffn-symb (fargn term 1)) '(< o<)))
           (list (if (eq (ffn-symb (fargn term 1)) '<) '<= 'o<=)
                 (rtl-untrans1 (fargn (fargn term 1) 2) nil untrans-tbl sigs-btree lops-alist
                               preprocess-fn wrld)
                 (rtl-untrans1 (fargn (fargn term 1) 1) nil untrans-tbl sigs-btree lops-alist
                               preprocess-fn wrld)))
          ((eq (ffn-symb term) 'not)
           (dumb-negate-lit (rtl-untrans1 (fargn term 1) t untrans-tbl sigs-btree lops-alist
                                          preprocess-fn wrld)))
          ((member-eq (ffn-symb term) '(implies iff))
           (fcons-term* (ffn-symb term)
                        (rtl-untrans1 (fargn term 1) t untrans-tbl sigs-btree lops-alist preprocess-fn
                                      wrld)
                        (rtl-untrans1 (fargn term 2) t untrans-tbl sigs-btree lops-alist preprocess-fn
                                      wrld)))
          ((eq (ffn-symb term) 'cons) (rtl-untrans-cons term untrans-tbl sigs-btree lops-alist
                                                        preprocess-fn wrld))
          ((and (eq (ffn-symb term) 'synp)

; Even though translate insists that the second argument of synp is quoted, can
; we really guarantee that every termp given to rtl-untrans came through
; translate?  Not necessarily; for example, maybe substitution was performed
; for some reason (say, in the proof-builder one replaces the quoted argument
; by a variable known to be equal to it).

                (quotep (fargn term 2)))

; We store the quotation of the original form of a syntaxp or bind-free
; hypothesis in the second arg of its expansion.  We do this so that we
; can use it here and output something that the user will recognise.

           (cadr (fargn term 2)))
;;; START addition for rtl-untrans1
        ((eq (ffn-symb term) 'binary-cat) ; (cat x xsize y ysize)
         (rtl-untrans-cat
          (rtl-untrans1 (fargn term 1) nil untrans-tbl
                        sigs-btree lops-alist preprocess-fn wrld)
          (rtl-untrans1 (fargn term 2) nil untrans-tbl
                        sigs-btree lops-alist preprocess-fn wrld)
          (rtl-untrans1 (fargn term 3) nil untrans-tbl
                        sigs-btree lops-alist preprocess-fn wrld)
          (rtl-untrans1 (fargn term 4) nil untrans-tbl
                        sigs-btree lops-alist preprocess-fn wrld)))
        ((and (eq (fargn term 2) '$path)
              (let ((fn (symbol-btree-lookup (ffn-symb term) sigs-btree)))
                (and fn
                     (list fn
                           (rtl-untrans1 (fargn term 1) nil untrans-tbl
                                         sigs-btree lops-alist preprocess-fn wrld))))))
;;; END addition for rtl-untrans1
          ((and (eq (ffn-symb term) 'return-last)
                (quotep (fargn term 1))
                (let* ((key (unquote (fargn term 1)))
                       (fn (and (symbolp key)
                                key
                                (let ((tmp (return-last-lookup key
                                                               wrld)))
                                  (if (consp tmp) (car tmp) tmp)))))
                  (and fn
                       (cons fn
                             (rtl-untrans1-lst (cdr (fargs term)) nil
                                               untrans-tbl
                                               sigs-btree lops-alist
                                               preprocess-fn wrld))))))
          (t
           (let* ((pair (cdr (assoc-eq (ffn-symb term)
                                       untrans-tbl)))
                  (op (car pair))
                  (flg (cdr pair)))
             (cond
              (op (cons op
                          (rtl-untrans1-lst
                           (cond
                            ((and flg
                                  (cdr (fargs term))
                                  (null (cddr (fargs term))))
                             (right-associated-args (ffn-symb term)
                                                    term))
                            (t (fargs term)))
                           nil untrans-tbl sigs-btree lops-alist
                           preprocess-fn wrld)))
              (t
;;; START addition for rtl-untrans1
             (let ((op (cdr (assoc-eq (ffn-symb term) lops-alist))))
               (cond
                (op (rtl-untrans-lop op
                                     (rtl-untrans1 (fargn term 1) nil untrans-tbl
                                                   sigs-btree lops-alist
                                                   preprocess-fn wrld)
                                     (rtl-untrans1 (fargn term 2) nil untrans-tbl
                                                   sigs-btree lops-alist
                                                   preprocess-fn wrld)
                                     (rtl-untrans1 (fargn term 3) nil untrans-tbl
                                                   sigs-btree lops-alist
                                                   preprocess-fn wrld)))
                (t
;;; END addition for rtl-untrans1
                 (mv-let
                  (ad-list base)
                  (make-reversed-ad-list term nil)
                  (cond (ad-list
                         (pretty-parse-ad-list
                          ad-list '(#\R) 1
                          (rtl-untrans1 base nil untrans-tbl
                                        sigs-btree lops-alist
                                        preprocess-fn wrld)))
                        (t (cons (ffn-symb term)
                                 (rtl-untrans1-lst (fargs term) nil
                                                   untrans-tbl
                                                   sigs-btree lops-alist
                                                   preprocess-fn
                                                   wrld)))))))))))))))

(defun rtl-untrans-cons1 (term untrans-tbl sigs-btree lops-alist preprocess-fn wrld)

; This function digs through a 'cons nest, untranslating each of the
; elements and the final non-cons cdr.  It returns two results:  the
; list of untranslated elements and the untranslated final term.

  (cond ((variablep term) (mv nil (rtl-untrans1 term nil untrans-tbl sigs-btree lops-alist
                                                preprocess-fn wrld)))
        ((fquotep term) (mv nil (rtl-untrans1 term nil untrans-tbl sigs-btree lops-alist preprocess-fn
                                              wrld)))
        ((eq (ffn-symb term) 'cons)
         (mv-let (elements x)
                 (rtl-untrans-cons1 (fargn term 2) untrans-tbl sigs-btree lops-alist preprocess-fn
                                    wrld)
                 (mv (cons (rtl-untrans1 (fargn term 1) nil untrans-tbl sigs-btree lops-alist
                                         preprocess-fn wrld)
                           elements)
                     x)))
        (t (mv nil (rtl-untrans1 term nil untrans-tbl sigs-btree lops-alist preprocess-fn wrld)))))

(defun rtl-untrans-cons (term untrans-tbl sigs-btree lops-alist preprocess-fn wrld)

; Term is a non-quote term whose ffn-symb is 'cons.  We untranslate
; it into a CONS, a LIST, or a LIST*.

  (mv-let (elements x)
          (rtl-untrans-cons1 term untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
          (cond ((eq x nil) (cons 'list elements))
                ((null (cdr elements)) (list 'cons (car elements) x))
                (t (cons 'list* (append elements (list x)))))))

(defun rtl-untrans-if (term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
  (cond ((> (case-length nil term) 2)
         (case-match term
                     (('if (& key &) & &)
                      (list* 'case key
                             (rtl-untrans-into-case-clauses
                              key term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                              wrld)))))
        ((> (cond-length term) 2)
         (cons 'cond (rtl-untrans-into-cond-clauses term iff-flg untrans-tbl sigs-btree lops-alist
                                                    preprocess-fn
                                                    wrld)))
        (t (list 'if
                 (rtl-untrans1 (fargn term 1) t untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
                 (rtl-untrans1 (fargn term 2) iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                               wrld)
                 (rtl-untrans1 (fargn term 3) iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                               wrld)))))

(defun rtl-untrans-into-case-clauses (key term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                          wrld)

; We generate the clauses of a (case key ...) stmt equivalent to term.
; We only call this function when the case-length of term is greater
; than 1.  If we called it when case-length were 1, it would not
; terminate.

  (case-match term
              (('if (pred !key ('quote val)) x y)
               (cond ((and (or (eq pred 'equal)
                               (eq pred 'eql))
                           (eqlablep val))
                      (cond ((or (eq val t)
                                 (eq val nil)
                                 (eq val 'otherwise))
                             (cons (list (list val)
                                         (rtl-untrans1 x iff-flg untrans-tbl sigs-btree lops-alist
                                                       preprocess-fn wrld))
                                   (rtl-untrans-into-case-clauses
                                    key y iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
                                  ))
                            (t (cons (list val (rtl-untrans1 x iff-flg
                                                             untrans-tbl sigs-btree lops-alist
                                                             preprocess-fn
                                                             wrld))
                                     (rtl-untrans-into-case-clauses
                                      key y iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                      wrld)))))
                     ((and (eq pred 'member)
                           (eqlable-listp val))
                      (cons (list val (rtl-untrans1 x iff-flg untrans-tbl sigs-btree lops-alist
                                                    preprocess-fn wrld))
                            (rtl-untrans-into-case-clauses
                             key y iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)))
                     (t (list (list 'otherwise
                                    (rtl-untrans1 term iff-flg untrans-tbl sigs-btree lops-alist
                                                  preprocess-fn wrld))))))
              (& (list (list 'otherwise
                             (rtl-untrans1 term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                           wrld))))))

(defun rtl-untrans-into-cond-clauses (term iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                           wrld)

; We know cond-length is greater than 1; else this doesn't terminate.

  (case-match term
              (('if x1 x2 x3)
               (cons (list (rtl-untrans1 x1 t untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
                           (rtl-untrans1 x2 iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                         wrld))
                     (rtl-untrans-into-cond-clauses x3 iff-flg untrans-tbl sigs-btree lops-alist
                                                    preprocess-fn wrld)))
              (& (list (list t (rtl-untrans1 term iff-flg untrans-tbl sigs-btree lops-alist
                                             preprocess-fn wrld))))))

;;; START addition for rtl-untrans1
(defun rtl-untrans-into-cond1-clauses (term untrans-tbl sigs-btree lops-alist
                                            preprocess-fn wrld)

; We know cond1-length is greater than 1; else this doesn't terminate.

  (case-match term
              (('if1 x1 x2 x3)
               (cons (list (rtl-untrans1 x1 nil untrans-tbl sigs-btree lops-alist
                                         preprocess-fn wrld)
                           (rtl-untrans1 x2 nil untrans-tbl sigs-btree lops-alist
                                         preprocess-fn wrld))
                     (rtl-untrans-into-cond1-clauses x3 untrans-tbl sigs-btree lops-alist
                                                     preprocess-fn wrld)))
              (& (list (list t (rtl-untrans1 term nil untrans-tbl sigs-btree
                                             lops-alist preprocess-fn wrld))))))
;;; END addition for rtl-untrans1

(defun rtl-untrans1-lst (lst iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
  (cond ((null lst) nil)
        (t (cons (rtl-untrans1 (car lst) iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn wrld)
                 (rtl-untrans1-lst (cdr lst) iff-flg untrans-tbl sigs-btree lops-alist preprocess-fn
                                   wrld)))))

;; RAG - I relaxed the guards for < and complex to use realp instead
;; of rationalp.  I also added complexp, realp, and floor1.

)

; Sigs-btree should associate each signals with any non-nil value.
; Lops-alist should contain (binary-land . land) etc.

; Here's how we manage that.

(defun str=-up-to (str1 str2 i bound)
  (declare (xargs :mode :program))
  (if (>= i bound)
      t
    (and (eql (char str1 i)
              (char str2 i))
         (str=-up-to str1 str2 (1+ i) bound))))

(defun all-dollar-symbs (alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :mode :program))
  (if (endp alist)
      t
    (and (let* ((name (symbol-name (caar alist)))
                (len (length name)))
           (and (not (eql len 0))
                (eql (char name (1- len))
                     #\$)
                (symbolp (cdar alist))
                (let* ((name2 (symbol-name (cdar alist)))
                       (len2 (length name2)))
                  (and (eql len2 (1- len))
                       (str=-up-to name name2 0 len2)))))
         (all-dollar-symbs (cdr alist)))))

(table rtl-tbl nil nil :guard
       (cond
        ((eq key 'lops-alist)
         t)
        ((eq key 'sigs-btree)

; It is tempting to require the following:

;        (and (symbol-btreep val)
;             (all-dollar-symbs (symbol-btree-to-alist val)))

; But for performance reasons we won't make any check.
         t)

        (t nil)))

(table rtl-tbl 'lops-alist
       '((binary-land . land)
         (binary-lior . lior)
         (binary-lxor . lxor)))

#|
; Example:

(defun cons-all-to-strip-$ (lst acc)
  (declare (xargs :guard (true-listp lst)
                  :mode :program))
  (if (endp lst)
      acc ; this function doesn't reverse
    (cons-all-to-strip-$ (cdr lst)
                   (cons (cons (car lst)
                               (intern-in-package-of-symbol
                                (coerce
                                 (butlast
                                  (coerce (symbol-name (car lst)) 'list)
                                  1)
                                 'string)
                                (car lst)))
                         acc))))

(table rtl-tbl 'sigs-btree
       (symbol-alist-to-btree
        (cons-all-to-strip-$
         '(a$ b$ c$)
         nil)))

; Another example, using the next definitions below:

(table rtl-tbl 'sigs-btree
       (symbol-alist-to-btree
        (dollar-alist '(a b c) nil)))

|# ; |

(defun dollarfy (sym)
  (declare (xargs :mode :logic
                  :guard (symbolp sym)))

; The extra effort below is so that, for example, (dollarfy 'exp) evaluates to
; acl2::exp$ rather than common-lisp::exp$.

  (let* ((old-name (symbol-name sym))
         (name (concatenate 'string old-name "$")))
    (if (eq (intern old-name "ACL2") sym)
        (intern name "ACL2")
      (intern-in-package-of-symbol name sym))))

(defun dollar-alist (syms acc)
  (declare (xargs :mode :logic
                  :guard (and (symbol-listp syms) (alistp acc))))
  (if (endp syms)
      acc
    (dollar-alist (cdr syms)
                  (acons (dollarfy (car syms))
                         (car syms)
                         acc))))

(defun rtl-untranslate (term iff-flg wrld)
  (let ((rtl-tbl (table-alist 'rtl-tbl wrld)))
    (rtl-untrans1 term iff-flg
                  (untrans-table wrld)
                  (cdr (assoc 'sigs-btree rtl-tbl))
                  (cdr (assoc 'lops-alist rtl-tbl))
                  (untranslate-preprocess-fn wrld)
                  wrld)))

(defun rtl-untranslate-lst (lst iff-flg wrld)
  (let ((rtl-tbl (table-alist 'rtl-tbl wrld)))
    (rtl-untrans1-lst lst
                      iff-flg
                      (untrans-table wrld)
                      (cdr (assoc-eq 'sigs-btree rtl-tbl))
                      (cdr (assoc-eq 'lops-alist rtl-tbl))
                      (untranslate-preprocess-fn wrld)
                      wrld)))

(table user-defined-functions-table
       'untranslate 'rtl-untranslate)

(table user-defined-functions-table
       'untranslate-lst 'rtl-untranslate-lst)

(defmacro extend-sigs-btree (name)

; Extend rtl-untranslate so that (name$ n $path) appears as (name n).

  (let ((name$ (dollarfy name)))
    `(table rtl-tbl 'sigs-btree
            (rebalance-symbol-btree
             (symbol-btree-update
              ',name$ ',name
              (cdr (assoc 'sigs-btree (table-alist 'rtl-tbl world))))))))

(defmacro rebalance-sigs-btree ()
  `(table rtl-tbl 'sigs-btree
          (rebalance-symbol-btree
           (cdr (assoc 'sigs-btree (table-alist 'rtl-tbl world))))))

; Finally, we deal with the right-assoc-macros-table, so that DV and numeric
; dive commands will work in the proof-builder.

(defun expand-address-cat (car-addr raw-term term wrld)
  (declare (ignore term wrld))
  (cond
   ((member car-addr '(1 2))
    (list car-addr))
   ((evenp car-addr)
    (msg "It is illegal to dive to arguments in even-numbered positions of a ~
          CAT expression, after the first.  Hence, address ~x0 is illegal for ~
          (untranslated) term~|~x1."
         car-addr raw-term))
   ((eql car-addr (- (length raw-term) 2))
    (make-list (floor (1- car-addr) 2) :initial-element 3))
   (t (append (make-list (floor (1- car-addr) 2) :initial-element 3)
              (list 1)))))

(add-dive-into-macro cat expand-address-cat)

(defun expand-address-lxor (car-addr raw-term term wrld)

; For example, (lxor a b c d 7) is the untranslated form of the term
; (binary-lxor a (binary-lxor b (binary-lxor c d '7) '7) '7), in which case (dv
; 2) expands to (dive 2 1), (dv 3) to (dive 2 2 1), (dv 4) to (dive 2 2 2), and
; (dv 5) to, say, (dive 3).

  (declare (ignore term wrld))
  (let* ((diff (- car-addr
                  (- (length raw-term) 2))))
    (cond ((eql diff 0)
           (make-list (1- car-addr) :initial-element 2))
          ((< diff 0)
           (append (make-list (1- car-addr) :initial-element 2)
                   '(1)))
          ((eql diff 1)
           (list 3))
          (t (msg "Argument position ~x0 is too big for diving into ~
                   (untranslated) term~|~x1."
                  car-addr raw-term)))))

(add-dive-into-macro lxor expand-address-lxor)
(add-dive-into-macro lior expand-address-lxor)
(add-dive-into-macro land expand-address-lxor)
