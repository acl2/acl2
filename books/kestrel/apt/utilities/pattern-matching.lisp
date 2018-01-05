; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Alessandro Coglio, Eric Smith, and Stephen Westfold for discussions
; that contributed to the design of the utility, address-subterm-governors-lst.

; The goal of this file is to match a pattern with a term to produce a list of
; triples (list* A U G) for address A, subterm U at A, and corresponding
; governors G.  The first function, fdeposit-term(-lst), isn't part of that --
; but it may well be needed in order to take advantage of those triples, so we
; include it here.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(program)

(mutual-recursion

; This mutual-recursion is based on deposit-term(-lst) from the ACL2 sources.
; But here, we use fcons-term instead of cons-term, to avoid any
; normalization.

(defun fdeposit-term (term addr subterm)

; This function returns the result of putting subterm at address addr in term.
; It assumes that error checking is not necessary, i.e. that addr is given
; correctly relative to term.  Here, addr is a list of one-based argument
; positions, and term is traversed top-down.  Here is an example.

;   ACL2 !>(fdeposit-term '(f a (g a (h b) (h (f2 x y))) c)
;                         '(2 3 1)
;                         '(f3 y x))
;   (F A (G A (H B) (H (F3 Y X))) C)
;   ACL2 !>

  (cond ((null addr) subterm)
        (t
         (fcons-term
          (ffn-symb term)
          (fdeposit-term-lst (fargs term) (car addr) (cdr addr) subterm)))))

(defun fdeposit-term-lst (lst n addr subterm)
  (cond ((= 1 n)
         (cons (fdeposit-term (car lst) addr subterm) (cdr lst)))
        (t (cons (car lst) (fdeposit-term-lst (cdr lst) (1- n) addr subterm)))))

)

(mutual-recursion

(defun preprocess-pat (pat inside-@)

; Pat is a pseudo-termp.  We return a new pseudo-termp, where we replace each @
; with (:@ _) and each @xx with (:@ _xx).  We preserve the package in the
; second case but we don't bother in the first, since _ is handled as a
; completely anonymous variable.

; We return nil (which is not a pseudo-termp) if there are nested :@ calls
; after eliminating @ and @xx.  More precisely: that description is accurate if
; inside-@ is nil (as is the case for a top-level call), but if inside-@ is
; non-nil, then we allow no :@ calls.

  (declare (xargs :guard (pseudo-termp pat)))
  (cond ((variablep pat)
         (let ((name (symbol-name pat)))
           (cond ((equal name "@")
                  (and (not inside-@)
                       (list :@ '_)))
                 ((equal name "") pat)
                 ((equal (char name 0) #\@)
                  (and (not inside-@)
                       (list :@
                             (intern-in-package-of-symbol
                              (concatenate 'string
                                           "_@"
                                           (subseq name 1 (length name)))
                              pat))))
                 (t pat))))
        ((fquotep pat) pat)
        ((null (fargs pat))
         (fcons-term* (ffn-symb pat)))
        ((eq (ffn-symb pat) :@)
         (and (not inside-@)
              (let ((pat2 (preprocess-pat (fargn pat 1) t)))
                (and pat2
                     (fcons-term* :@ pat2)))))
        (t (let ((args (preprocess-pat-lst (fargs pat) inside-@)))
             (and args
                  (fcons-term (ffn-symb pat) args))))))

(defun preprocess-pat-lst (pat inside-@)
  (cond ((endp pat) nil)
        (t (let ((x1 (preprocess-pat (car pat) inside-@)))
             (and x1
                  (cond ((cdr pat)
                         (let ((x2 (preprocess-pat-lst (cdr pat) inside-@)))
                           (and x2 (cons x1 x2))))
                        (t (cons x1 nil))))))))
)

(defun pat-var-p (term)

; Term is an argument of :@.

  (declare (xargs :guard (symbolp term)))
  (let ((name (symbol-name term)))
    (and (not (equal name ""))
         (eql (char name 0) #\_))))

(mutual-recursion

; These are based on ACL2 source functions all-vars1 and all-vars1-lst.

(defun non-pat-vars1 (term ans)

; Term is a translated pattern to which preprocess-pat has already been
; applied; so there may be calls of :@, but there are no variables whose name
; begins with "@".  We collect into ans all variables of term that do not start
; with underscore (_).

  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))))
  (cond ((variablep term)
         (if (pat-var-p term)
             ans
           (add-to-set-eq term ans)))
        ((fquotep term) ans)
        (t (non-pat-vars1-lst (fargs term) ans))))

(defun non-pat-vars1-lst (lst ans)

; Lst is a list of subterms of a translated pattern to which preprocess-pat has
; already been applied; so there may be calls of :@, but there are no variables
; whose name begins with "@".

  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((endp lst) ans)
        (t (non-pat-vars1-lst (cdr lst)
                              (non-pat-vars1 (car lst) ans)))))

)

(defun pat-unify-subst (pat)

; When instantiating a pattern, only variables starting with the underscore
; character (_) may be instantiated.  So we "seed" our matching algorithm with
; a substitution that binds all other variables of pat to themselves.

  (declare (xargs :guard (pseudo-termp pat)
                  :mode :program))
  (let ((vars (non-pat-vars1 pat nil)))
    (pairlis$ vars vars)))

(mutual-recursion

(defun one-way-unify1-simple (pat term alist)

; This function is adapted from one-way-unify1 in the ACL2 sources, but it
; differs by avoiding special treatment for constants and EQUAL, and it allows
; variables named "_" to match anything without extending alist.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp alist))))
  (cond ((variablep pat)
         (cond ((equal (symbol-name pat) "_")
                (mv t alist))
               (t (let ((pair (assoc-eq pat alist)))
                    (cond (pair (cond ((equal (cdr pair) term)
                                       (mv t alist))
                                      (t (mv nil alist))))
                          (t (mv t (cons (cons pat term) alist))))))))
        ((fquotep pat)
         (mv (equal pat term) alist))
        ((variablep term) (mv nil alist))
        ((fquotep term) (mv nil alist))
        ((equal (ffn-symb pat) (ffn-symb term))
         (mv-let (ans alist1)
           (one-way-unify1-simple-lst (fargs pat) (fargs term) alist)
           (cond (ans (mv ans alist1))
                 (t (mv nil alist)))))
        (t (mv nil alist))))

(defun one-way-unify1-simple-lst (pl tl alist)
  (declare (xargs :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp alist))))
  (cond ((null pl) (mv t alist))
        (t (mv-let (ans alist)
             (one-way-unify1-simple (car pl) (car tl) alist)
             (cond (ans (one-way-unify1-simple-lst (cdr pl) (cdr tl) alist))
                   (t (mv nil alist)))))))
)

(mutual-recursion

(defun address-subterm-governors-lst2 (pat term alist posn-lst govs)

; If term is an instance of pat/alist, viewing :@ as invisible, then return (mv
; t alist' lst) where alist' extends alist such that term = pat/alist', and lst
; is a list of triples (list* A U G) for address A, subterm U of term at A, and
; corresponding governors G.  Note that A and govs are accumulated in reverse
; order into posn-lst and govs, respectively, but they are put in proper order
; as they are returned.  There is one triple for each position of an :@ call in
; pat; an input assumption on pat is that these are not nested.

; If however term is not an instance of pat/alist, return (mv nil nil nil).

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (pos-listp posn-lst)
                              (pseudo-term-listp govs))))
  (cond
   ((or (variablep pat)
        (fquotep pat))
    (mv-let (flg unify-subst)
      (one-way-unify1-simple pat term alist)
      (cond (flg (mv t nil unify-subst))
            (t (mv nil nil nil)))))
   ((eq (ffn-symb pat) :@)
    (mv-let (flg unify-subst)
      (one-way-unify1-simple (fargn pat 1) term alist)
      (cond (flg (mv t
                     (list (list* (reverse posn-lst)
                                  term
                                  (reverse govs)))
                     unify-subst))
            (t (mv nil nil nil)))))
   ((not (and (nvariablep term)
              (not (fquotep term))
              (equal (ffn-symb pat) (ffn-symb term))))
    (mv nil nil nil))
   ((eq (ffn-symb pat) 'if)
    (b* (((mv flg lst1 alist1)
          (address-subterm-governors-lst2 (fargn pat 1)
                                          (fargn term 1)
                                          alist
                                          (cons 1 posn-lst)
                                          govs))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst2 alist2)
          (address-subterm-governors-lst2 (fargn pat 2)
                                          (fargn term 2)
                                          alist1
                                          (cons 2 posn-lst)
                                          (cons (fargn term 1)
                                                govs)))
         ((when (not flg))
          (mv nil nil nil))
         ((mv flg lst3 alist3)
          (address-subterm-governors-lst2 (fargn pat 3)
                                          (fargn term 3)
                                          alist2
                                          (cons 3 posn-lst)
                                          (cons (dumb-negate-lit
                                                 (fargn term 1))
                                                govs)))
         ((when (not flg))
          (mv nil nil nil)))
      (mv t (append lst1 lst2 lst3) alist3)))
   (t (address-subterm-governors-lst2-lst
       (fargs pat) (fargs term) alist 1 posn-lst govs))))

(defun address-subterm-governors-lst2-lst (pat-lst term-lst alist posn posn-lst
                                                   govs)
  (declare (xargs :guard (and (pseudo-term-listp pat-lst)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (pos-listp posn-lst)
                              (pseudo-term-listp govs))))
  (cond ((endp pat-lst) (mv t nil alist))
        (t (b* (((mv flg lst1 alist1)
                 (address-subterm-governors-lst2 (car pat-lst)
                                                 (car term-lst)
                                                 alist
                                                 (cons posn posn-lst)
                                                 govs))
                ((when (not flg))
                 (mv nil nil nil))
                ((mv flg lst2 alist2)
                 (address-subterm-governors-lst2-lst (cdr pat-lst)
                                                     (cdr term-lst)
                                                     alist1
                                                     (1+ posn)
                                                     posn-lst
                                                     govs))
                ((when (not flg))
                 (mv nil nil nil)))
             (mv t (append lst1 lst2) alist2)))))
)

(mutual-recursion

(defun address-subterm-governors-lst1 (pat term alist posn-lst govs)

; We do a pre-order traversal to find the first subterm S matching pat to term
; with respect to alist, and return the corresponding list of triples (list* A
; U G) for address A, subterm U of term at A, and corresponding governors G,
; but where the reverses of A and G extend posn-lst and govs (resp.) by pushing
; new elements on the front as we dive into term.  Important: that list is
; non-empty if pat has at least one call of :@ (which it does at the top
; level), and all returned triples are viewed with respect to the input, term,
; even though they all point to subterms of S.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (symbol-alistp alist)
                              (pos-listp posn-lst)
                              (pseudo-term-listp govs))))
  (mv-let (flg triples unify-subst)
    (address-subterm-governors-lst2 pat term alist posn-lst govs)
    (declare (ignore unify-subst))
    (cond
     (flg triples)
     (t
      (and (nvariablep term)
           (not (fquotep term))
           (cond
            ((eq (ffn-symb term) 'if)
             (or (address-subterm-governors-lst1 pat
                                                 (fargn term 1)
                                                 alist
                                                 (cons 1 posn-lst)
                                                 govs)
                 (address-subterm-governors-lst1 pat
                                                 (fargn term 2)
                                                 alist
                                                 (cons 2 posn-lst)
                                                 (cons (fargn term 1)
                                                       govs))
                 (address-subterm-governors-lst1 pat
                                                 (fargn term 3)
                                                 alist
                                                 (cons 3 posn-lst)
                                                 (cons (dumb-negate-lit
                                                        (fargn term 1))
                                                       govs))))
            (t (address-subterm-governors-lst1-lst pat (fargs term) alist 1
                                                   posn-lst govs))))))))

(defun address-subterm-governors-lst1-lst (pat term-lst alist posn posn-lst
                                               govs)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-term-listp term-lst)
                              (symbol-alistp alist)
                              (posp posn)
                              (pos-listp posn-lst)
                              (pseudo-term-listp govs))))
  (cond
   ((endp term-lst)
    nil)
   (t
    (or (address-subterm-governors-lst1 pat (car term-lst) alist
                                        (cons posn posn-lst) govs)
        (address-subterm-governors-lst1-lst pat (cdr term-lst) alist (1+ posn)
                                            posn-lst govs)))))
)

(defun address-subterm-governors-lst (untrans-pat term ctx state)

; Untrans-pat, a user-supplied pattern, translates to a pseudo-termp, pat.  See
; :doc simplify-defun, specifically the documentation for :simplify-body, for a
; discussion of translation and the matching algorithm.

; Example (after defstub for each function symbol used):

;   ACL2 !>(address-subterm-governors-lst
;            '(if (p _x)
;                 (g (if (q (:@ a0)) _ (f3 y @)))
;               _v)
;            '(if (p x0)
;                 (g (if (q a0) w0 (f3 y (h x))))
;               v0)
;            'top state)
;    (((1 1 1 2) A0 (P X0))
;     ((2 3 1 2) (H X) (NOT (Q A0)) (P X0)))
;   ACL2 !>

  (declare (xargs :guard (pseudo-termp term) :stobjs state))
  (b* ((wrld (w state))
       ((mv erp pat0) (translate-cmp untrans-pat
                                     t ; stobjs-out
                                     t ; logic-modep
                                     t ; known-stobjs
                                     ctx
                                     (cons '(:@ FORMALS X) wrld)
                                     (default-state-vars t)))
       ((when erp)
        (mv erp pat0))
       (pat (preprocess-pat pat0 nil)) ; change @ to (:@ _), @xx to (:@ _@xx)
       ((when (null pat))
        (er-cmp ctx
                "The :simplify-body pattern must not specify nested ~
                 simplification sites (using @ or (:@ ...)).  The ~
                 user-specified pattern has translated to~|  ~y0, which is ~
                 thus illegal."
                pat0))
       ((when (not (member-eq :@ (all-ffn-symbs pat nil))))

; Note: we could code a faster test by avoiding building a list of all function
; symbols in pat, but the extra computation is probably trivial so why bother.

        (er-cmp ctx
                "The :simplify-body pattern must specify at least one ~
                 simplification site (using @ or (:@ ...)).  The ~
                 user-specified pattern is equivalent to~|  ~y0, which is ~
                 thus illegal."
                pat))
       (unify-subst (pat-unify-subst pat))
       (lst (address-subterm-governors-lst1 pat term unify-subst nil nil)))
    (cond
     ((null lst)
      (er-cmp ctx
              "No subterm of ~x0 matches the pattern ~x1."
              (untranslate term nil wrld)
              pat))
     (t (value-cmp lst)))))

(defun address-subterm-governors-lst-state (untrans-pat term ctx state)
  (declare (xargs :guard (pseudo-termp term) :stobjs state))
    (cmp-to-error-triple
     (address-subterm-governors-lst untrans-pat term ctx state)))
