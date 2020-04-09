; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Alessandro Coglio, Eric Smith, and Stephen Westfold for discussions
; that contributed to the design of the utility, address-subterm-governors-lst.

; An extended address is a list each of whose elements is either 0, denoting a
; lambda for which we are to dive into its body, or a one-based argument
; position.

; This book introduces the following key functions:

; -- ext-fdeposit-term, to substitute a term at a given address, even possibly
;    diving inside lambda bodies

; -- ext-geneqv-at-subterm, to find the generated equivalence relation at a
;    specified subterm, which may be inside lambda bodies

; -- ext-address-subterm-governors-lst, to locate all :@-subterms upon a match
;    of an untranslated pattern in a translated term.  It returns a
;    context-message pair (mv erp val), where val is a list of tuples (list* A
;    U B G+) for address A, subterm U at A, bindings alist B, and corresponding
;    governors G+ (with bindings B already applied).

; See pattern-matching-ext-support.lisp for code comments and supporting
; lemmas.  A nice challenge is to make all functions guard-verified; several
; remain in :program mode.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-non-cl" :dir :system)

(local (include-book "pattern-matching-ext-support"))

(set-enforce-redundancy t)

(defun drop-formals (formals actuals vars acc-f acc-a)

  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals)
                              (true-listp vars)
                              (true-listp acc-f)
                              (true-listp acc-a))))
  (cond ((endp formals)
         (cond ((equal acc-f acc-a)
                (mv nil nil))
               (t
                (mv (reverse acc-f) (reverse acc-a)))))
        ((not (member-eq (car formals) vars))
         (drop-formals (cdr formals) (cdr actuals) vars acc-f acc-a))
        (t
         (drop-formals (cdr formals) (cdr actuals) vars
                       (cons (car formals) acc-f)
                       (cons (car actuals) acc-a)))))

(defun ext-make-lambda-application (formals body actuals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-termp body)
                              (true-listp actuals)
                              (eql (len formals) (len actuals)))))
  (b* ((vars (all-vars body))
       ((mv formals actuals)
        (drop-formals formals actuals vars nil nil))
       ((when (null formals))
        (assert$ (null actuals)
                 body))
       (extra-vars (set-difference-eq vars formals))
       (formals (append? formals extra-vars))
       (actuals (append? actuals extra-vars)))
    (fcons-term (make-lambda formals body)
                actuals)))

(defun ext-new-formal (root-var n)
  (declare (xargs :mode :program))
  (intern$ (concatenate 'string
                        (symbol-name root-var)
                        "{"
                        (coerce (explode-nonnegative-integer n 10 nil)
                                'string)
                        "}")
           (symbol-package-name-non-cl root-var)))

(defun ext-maybe-rename-formal (root-var var avoid-vars n)
  (declare (xargs :mode :program))
  (cond ((member-eq var avoid-vars)
         (let ((new-var (ext-new-formal root-var n)))
           (ext-maybe-rename-formal root-var new-var avoid-vars (1+ n))))
        (t var)))

(defun ext-rename-formals (formals avoid-vars)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t (cons (ext-maybe-rename-formal (car formals) (car formals)
                                          avoid-vars 1)
                 (ext-rename-formals (cdr formals) avoid-vars)))))

(defun ext-restore-formals (old-formals new-formals bad-formals)
  (declare (xargs :mode :program))
  (cond ((endp old-formals) (mv nil nil))
        (t (mv-let (formals1 alist-new-to-old)
             (ext-restore-formals (cdr old-formals)
                                  (cdr new-formals)
                                  bad-formals)
             (cond ((member-eq (car old-formals) bad-formals)
                    (mv (cons (car new-formals) formals1)
                        alist-new-to-old))
                   (t
                    (mv (cons (car old-formals) formals1)
                        (acons (car new-formals)
                               (car old-formals)
                               alist-new-to-old))))))))

(defun ext-rename-for-substitution (formals actuals subterm body)
  (declare (xargs :mode :program))
  (b* ((subterm-vars (all-vars subterm))
       (formals0 (ext-rename-formals formals subterm-vars))
       (new-subterm (sublis-expr (pairlis$ actuals formals0) subterm))
       (bad-formals (intersection-eq (all-vars new-subterm) formals))
       ((mv formals1 alist-new-to-old)
        (ext-restore-formals formals formals0 bad-formals))
       (body1 (sublis-expr (pairlis$ formals formals1) body))
       (subterm1 (sublis-expr alist-new-to-old new-subterm)))
    (mv formals1 subterm1 body1)))

(mutual-recursion

; This mutual-recursion is based on deposit-term(-lst) from the ACL2 sources.

(defun ext-fdeposit-term-rec (term addr subterm)
  (declare (xargs :mode :program))
  (cond
   ((endp addr) subterm)
   ((eql (car addr) 0)
    (assert$
     (lambda-applicationp term)
     (b* ((fn (ffn-symb term))
          (formals (lambda-formals fn))
          (body (lambda-body fn))
          (actuals (fargs term))
          ((mv formals1 subterm1 body1)
           (ext-rename-for-substitution formals actuals subterm body))
          (body2 (ext-fdeposit-term-rec body1
                                        (cdr addr)
                                        subterm1)))
       (ext-make-lambda-application formals1 body2 actuals))))
   (t
    (fcons-term
     (ffn-symb term)
     (ext-fdeposit-term-lst (fargs term) (car addr) (cdr addr) subterm)))))

(defun ext-fdeposit-term-lst (lst n addr subterm)
  (declare (xargs :mode :program))
  (cond ((= 1 n)
         (cons (ext-fdeposit-term-rec (car lst) addr subterm)
               (cdr lst)))
        (t (cons (car lst)
                 (ext-fdeposit-term-lst (cdr lst) (1- n) addr subterm)))))

)

; KEY TOP-LEVEL FUNCTION:
(defun ext-fdeposit-term (term addr subterm)
  (declare (xargs :mode :program))
  (ext-fdeposit-term-rec term addr subterm))

(defconst *ext-failure*
  '(:failure))

(mutual-recursion

(defun ext-preprocess-pat (pat inside-@)
  (declare (xargs :guard t
                  :measure (acl2-count pat)))
  (cond ((symbolp pat)
         (let ((name (symbol-name pat)))
           (cond ((equal name "@")
                  (if inside-@
                      *ext-failure*
                    (list :@ '_)))
                 ((equal name "") pat)
                 ((equal (char name 0) #\@)
                  (if inside-@
                      *ext-failure*
                    (list :@
                          (intern-in-package-of-symbol
                           (concatenate 'string
                                        "_@"
                                        (subseq name 1 (length name)))
                           pat))))
                 (t pat))))
        ((atom pat) pat)
        ((or (eq (car pat) 'quote)
             (not (consp (cdr pat))))
         pat)
        ((eq (car pat) :@)
         (if inside-@
             *ext-failure*
           (let ((pat2 (ext-preprocess-pat (cadr pat) t)))
             (if (equal pat2 *ext-failure*)
                 *ext-failure*
               (list :@ pat2)))))
        ((and (member-eq (car pat) '(let let*))
              (true-listp pat))
         `(,(car pat)
           ,(ext-preprocess-pat-let-bindings (cadr pat) inside-@)
           ,@(butlast (cddr pat) 1)
           ,(ext-preprocess-pat (car (last pat)) inside-@)))
        (t (let ((args (ext-preprocess-pat-lst (cdr pat) inside-@)))
             (if (null args)
                 *ext-failure*
               (cons (car pat) args))))))

(defun ext-preprocess-pat-let-bindings (bindings inside-@)
  (declare (xargs :guard t))
  (cond ((atom bindings) bindings)
        (t (cons (let ((b (car bindings)))
                   (cond ((true-listp b)
                          (list (car b)
                                (ext-preprocess-pat (cadr b) inside-@)))
                         (t b)))
                 (ext-preprocess-pat-let-bindings (cdr bindings) inside-@)))))

(defun ext-preprocess-pat-lst (pat inside-@)
  (declare (xargs :guard (consp pat)
                  :measure (acl2-count pat)
                  :ruler-extenders :lambdas))
  (let ((x1 (and (mbt (consp pat))
                 (ext-preprocess-pat (car pat) inside-@))))
    (cond
     ((equal x1 *ext-failure*)
      nil)
     ((atom (cdr pat))
      (cons x1 (cdr pat)))
     (t
      (let ((x2 (ext-preprocess-pat-lst (cdr pat) inside-@)))
        (and x2
             (cons x1 x2)))))))
)

; KEY TOP-LEVEL FUNCTION:
(defun ext-geneqv-at-subterm (term addr geneqv pequiv-info ens wrld)
  (declare (xargs :mode :program))
  (cond ((null addr)
         geneqv)
        ((zerop (car addr))
         (assert$
          (lambda-applicationp term)
          (ext-geneqv-at-subterm (lambda-body (ffn-symb term))
                                 (cdr addr)
                                 geneqv pequiv-info ens wrld)))
        (t
         (let ((child-geneqv0
                (nth (1- (car addr))
                     (geneqv-lst (ffn-symb term) geneqv ens wrld))))
           (mv-let
            (deep-pequiv-lst shallow-pequiv-lst)
            (pequivs-for-rewrite-args (ffn-symb term) geneqv pequiv-info wrld
                                      ens)
            (mv-let
             (pre-rev cur/post)
             (split-at-position (car addr) (fargs term) nil)
             (mv-let
              (child-geneqv child-pequiv-info)
              (geneqv-and-pequiv-info-for-rewrite
               (ffn-symb term)
               (car addr)
               pre-rev cur/post
               nil
               geneqv child-geneqv0
               deep-pequiv-lst shallow-pequiv-lst
               wrld)
              (ext-geneqv-at-subterm (car cur/post)
                                     (cdr addr)
                                     child-geneqv child-pequiv-info
                                     ens wrld))))))))

(defun pat-var-p (term)
  (declare (xargs :guard (symbolp term)))
  (let ((name (symbol-name term)))
    (and (not (equal name ""))
         (eql (char name 0) #\_))))

(mutual-recursion

; These are based on ACL2 source functions all-vars1 and all-vars1-lst.

(defun non-pat-vars1 (term ans)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))))
  (cond ((variablep term)
         (if (pat-var-p term)
             ans
           (add-to-set-eq term ans)))
        ((fquotep term) ans)
        (t (non-pat-vars1-lst (fargs term) ans))))

(defun non-pat-vars1-lst (lst ans)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((endp lst) ans)
        (t (non-pat-vars1-lst (cdr lst)
                              (non-pat-vars1 (car lst) ans)))))

)

(defun pat-unify-subst (pat)
  (declare (xargs :guard (pseudo-termp pat)
                  :mode :program))
  (let ((vars (non-pat-vars1 pat nil)))
    (pairlis$ vars vars)))

(defun equal-mod-patvars (pat-formals fn-formals)
  (declare (xargs :guard (and (symbol-listp pat-formals)
                              (symbol-listp fn-formals))))
  (cond ((or (endp fn-formals)
             (endp pat-formals))
         t)
        ((eq (car pat-formals) (car fn-formals))
         (equal-mod-patvars (cdr pat-formals) (cdr fn-formals)))
        ((pat-var-p (car pat-formals))
         (equal-mod-patvars (cdr pat-formals) fn-formals))
        (t (let ((rest-fn-formals (member-eq (car pat-formals) fn-formals)))
             (and rest-fn-formals
                  (equal-mod-patvars (cdr pat-formals)
                                     (cdr rest-fn-formals)))))))

(mutual-recursion

(defun ext-one-way-unify1-simple (pat term alist)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp alist))
                  :measure (acl2-count term)))
  (cond
   ((variablep pat)
    (cond ((equal (symbol-name pat) "_")
           (mv t alist))
          (t (let ((pair (assoc-eq pat alist)))
               (cond (pair (cond ((equal (cdr pair) term)
                                  (mv t alist))
                                 (t (mv nil nil))))
                     (t (mv t (cons (cons pat term) alist))))))))
   ((fquotep pat)
    (mv (equal pat term) alist))
   ((variablep term) (mv nil nil))
   ((fquotep term) (mv nil nil))
   (t (let ((fn-pat (ffn-symb pat))
            (fn-term (ffn-symb term)))
        (cond
         ((and (symbolp fn-pat)
               (eq fn-pat fn-term))
          (ext-one-way-unify1-simple-lst (fargs pat) (fargs term) alist))
         ((and (flambdap fn-pat)
               (flambdap fn-term)
               (equal-mod-patvars (lambda-formals fn-pat)
                                  (lambda-formals fn-term)))
          (mv-let (ans alist)
            (ext-one-way-unify1-simple-lst
             (take (length (lambda-formals fn-term)) (fargs pat))
             (fargs term)
             alist)
            (cond (ans (ext-one-way-unify1-simple (lambda-body fn-pat)
                                                  (lambda-body fn-term)
                                                  alist))
                  (t (mv nil nil)))))
         (t (mv nil nil)))))))

(defun ext-one-way-unify1-simple-lst (pl tl alist)
  (declare (xargs :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp alist))
                  :measure (acl2-count tl)))
  (cond ((endp tl) (mv t alist))
        (t (mv-let (ans alist)
             (ext-one-way-unify1-simple (car pl) (car tl) alist)
             (cond (ans (ext-one-way-unify1-simple-lst (cdr pl) (cdr tl) alist))
                   (t (mv nil alist)))))))
)

(defun extend-bindings (formals actuals bindings)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (eql (len formals) (len actuals))
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings)))))
  (cond ((endp formals) bindings)
        (t (acons (car formals)
                  (sublis-var bindings (car actuals))
                  (extend-bindings (cdr formals) (cdr actuals) bindings)))))

(mutual-recursion

(defun ext-address-subterm-governors-lst2 (pat term alist posn-lst bindings
                                               govs)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (cond
   ((or (variablep pat)
        (fquotep pat))
    (mv-let (flg unify-subst)
      (ext-one-way-unify1-simple pat term alist)
      (cond (flg (mv t nil unify-subst))
            (t (mv nil nil nil)))))
   ((eq (ffn-symb pat) :@)
    (mv-let (flg unify-subst)
      (ext-one-way-unify1-simple (fargn pat 1) term alist)
      (cond (flg (mv t
                     (list (list* (reverse posn-lst)
                                  term
                                  bindings
                                  (reverse govs)))
                     unify-subst))
            (t (mv nil nil nil)))))
   ((or (variablep term)
        (fquotep term))
    (mv nil nil nil))
   ((and (flambdap (ffn-symb pat))
         (flambdap (ffn-symb term))
         (equal-mod-patvars (lambda-formals (ffn-symb pat))
                            (lambda-formals (ffn-symb term))))
    (b* (((mv flg lst1 alist)
          (ext-address-subterm-governors-lst2
           (lambda-body (ffn-symb pat))
           (lambda-body (ffn-symb term))
           alist
           (cons 0 posn-lst)
           (extend-bindings (lambda-formals (ffn-symb term))
                            (fargs term)
                            bindings)
           govs))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst2 alist)
          (ext-address-subterm-governors-lst2-lst
           (fargs pat) (fargs term) alist 1 posn-lst bindings govs))
         ((when (not flg))
          (mv nil nil nil)))
      (mv t (append lst1 lst2) alist)))
   ((not (equal (ffn-symb pat) (ffn-symb term)))
    (mv nil nil nil))
   ((eq (ffn-symb pat) 'if)
    (b* (((mv flg lst1 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 1)
                                              (fargn term 1)
                                              alist
                                              (cons 1 posn-lst)
                                              bindings
                                              govs))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst2 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 2)
                                              (fargn term 2)
                                              alist
                                              (cons 2 posn-lst)
                                              bindings
                                              (cons (sublis-var
                                                     bindings
                                                     (fargn term 1))
                                                    govs)))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst3 alist)
          (ext-address-subterm-governors-lst2 (fargn pat 3)
                                              (fargn term 3)
                                              alist
                                              (cons 3 posn-lst)
                                              bindings
                                              (cons (sublis-var
                                                     bindings
                                                     (dumb-negate-lit
                                                      (fargn term 1)))
                                                    govs)))
         ((when (not flg))
          (mv nil nil nil)))
      (mv t (append lst1 lst2 lst3) alist)))
   (t (ext-address-subterm-governors-lst2-lst
       (fargs pat) (fargs term) alist 1 posn-lst bindings govs))))

(defun ext-address-subterm-governors-lst2-lst (pat-lst term-lst alist posn
                                                       posn-lst bindings govs)
  (declare (xargs :guard (and (pseudo-term-listp pat-lst)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (cond ((endp pat-lst) (mv t nil alist))
        (t (b* (((mv flg lst1 alist)
                 (ext-address-subterm-governors-lst2 (car pat-lst)
                                                     (car term-lst)
                                                     alist
                                                     (cons posn posn-lst)
                                                     bindings
                                                     govs))
                ((when (not flg))
                 (mv nil nil nil))
                ((mv flg lst2 alist)
                 (ext-address-subterm-governors-lst2-lst (cdr pat-lst)
                                                         (cdr term-lst)
                                                         alist
                                                         (1+ posn)
                                                         posn-lst
                                                         bindings
                                                         govs))
                ((when (not flg))
                 (mv nil nil nil)))
             (mv t (append lst1 lst2) alist)))))
)

(mutual-recursion

(defun ext-address-subterm-governors-lst1 (pat term alist posn-lst bindings
                                               govs)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (mv-let (flg tuples unify-subst)
    (ext-address-subterm-governors-lst2 pat term alist posn-lst bindings govs)
    (declare (ignore unify-subst))
    (cond
     (flg tuples)
     (t
      (and (nvariablep term)
           (not (fquotep term))
           (cond
            ((eq (ffn-symb term) 'if)
             (or (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 1)
                                                     alist
                                                     (cons 1 posn-lst)
                                                     bindings
                                                     govs)
                 (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 2)
                                                     alist
                                                     (cons 2 posn-lst)
                                                     bindings
                                                     (cons (sublis-var
                                                            bindings
                                                            (fargn term 1))
                                                           govs))
                 (ext-address-subterm-governors-lst1 pat
                                                     (fargn term 3)
                                                     alist
                                                     (cons 3 posn-lst)
                                                     bindings
                                                     (cons (sublis-var
                                                            bindings
                                                            (dumb-negate-lit
                                                             (fargn term 1)))
                                                           govs))))
            ((flambdap (ffn-symb term))
             (or
              (ext-address-subterm-governors-lst1-lst pat (fargs term) alist
                                                      1 posn-lst
                                                      bindings govs)
              (ext-address-subterm-governors-lst1
               pat
               (lambda-body (ffn-symb term))
               alist
               (cons 0 posn-lst)
               (extend-bindings (lambda-formals (ffn-symb term))
                                (fargs term)
                                bindings)
               govs)))
            (t (ext-address-subterm-governors-lst1-lst pat (fargs term) alist
                                                       1 posn-lst
                                                       bindings govs))))))))

(defun ext-address-subterm-governors-lst1-lst (pat term-lst alist posn posn-lst
                                                   bindings govs)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (nat-listp posn-lst)
                              (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (true-listp govs))))
  (cond
   ((endp term-lst)
    nil)
   (t
    (or (ext-address-subterm-governors-lst1 pat (car term-lst) alist
                                            (cons posn posn-lst)
                                            bindings govs)
        (ext-address-subterm-governors-lst1-lst pat (cdr term-lst) alist
                                                (1+ posn) posn-lst
                                                bindings govs)))))
)

(defun ext-address-subterm-governors-lst-world (untrans-pat term ctx wrld
                                                            state-vars)
  (declare (xargs :mode :program
                  :guard (and (pseudo-termp term)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (b* ((untrans-pat1
        (ext-preprocess-pat untrans-pat nil))
       ((when (equal untrans-pat1 *ext-failure*))
        (er-cmp ctx
                "The :simplify-body pattern must not specify nested ~
                 simplification sites (using @ or (:@ ...))."))
       ((mv erp pat) (translate-cmp untrans-pat1
                                    t
                                    t
                                    t
                                    ctx
                                    (cons '(:@ FORMALS X) wrld)
                                    state-vars))
       ((when erp)
        (mv erp pat))
       ((when (not (member-eq :@ (all-ffn-symbs pat nil))))
        (er-cmp ctx
                "The :simplify-body pattern must specify at least one ~
                 simplification site (using @ or (:@ ...)).  The ~
                 user-specified pattern is equivalent to~|  ~y0, which is ~
                 thus illegal."
                pat))
       (unify-subst (pat-unify-subst pat))
       (lst (ext-address-subterm-governors-lst1 pat term unify-subst
                                                nil nil nil)))
    (cond
     ((null lst)
      (er-cmp ctx
              "No subterm of ~x0 matches the pattern ~x1."
              (untranslate term nil wrld)
              pat))
     (t (value-cmp lst)))))

; KEY TOP-LEVEL FUNCTION:
(defun ext-address-subterm-governors-lst (untrans-pat term ctx state)
  (declare (xargs :mode :program
                  :guard (pseudo-termp term)
                  :stobjs state))
  (ext-address-subterm-governors-lst-world untrans-pat term ctx
                                           (w state)
                                           (default-state-vars t)))

(defun ext-address-subterm-governors-lst-state (untrans-pat term ctx state)
  (declare (xargs :mode :program
                  :guard (pseudo-termp term)
                  :stobjs state))
  (cmp-to-error-triple
   (ext-address-subterm-governors-lst untrans-pat term ctx state)))
