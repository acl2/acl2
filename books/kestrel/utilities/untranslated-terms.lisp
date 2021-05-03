; Utilities for dealing with untranslated terms
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This book includes some utilities for dealing with untranslated terms, so
;; that we don't have the translate them, process them, and then try to
;; untranslate them (which can lose information, especially non-logical
;; information related to, e.g., execution).  The set of macros we will have to
;; support is unfortunately open-ended.  We currently support let, let*, b*
;; (partially), cond, case, and case-match.

;; TODO: Add support for expanding away any macros for which we do not have
;; special handling (e.g., calls of b* with b* binders that we do not yet
;; handle).  Or perhaps many (hygienic?) macros can just be treated like
;; function calls for many purposes (e.g., when replacing variables with new
;; terms in a term).

;; TODO: Replace more of the hand-written functions with calls to def-untranslated-term-fold

(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system)
(include-book "map-symbol-name")
(include-book "legal-variable-listp")
(include-book "quote")
(include-book "lets")
(include-book "lambdas")
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
;(include-book "../sequences/defforall") ;drop (after replacing the defforall-simple below)?
;(include-book "../sequences/generics-utilities") ;for make-pairs (TODO: move that and rename to mention doublets)
;(include-book "kestrel/library-wrappers/my-make-flag" :dir :system)
(include-book "legal-variablep") ;for legal-variable-name-in-acl2-packagep
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/union" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(include-book "std/alists/remove-assocs" :dir :system)

;;=== stuff to move to libraries:

(in-theory (disable butlast))
(in-theory (disable last))
(in-theory (disable member-equal))

(defthm acl2-count-of-car-of-last-of-fargs
  (implies (consp x)
           (< (ACL2-COUNT (CAR (LAST (fargs x))))
              (ACL2-COUNT x)))
  :rule-classes (:rewrite :linear))

;; Test for a list of non-dotted pairs
;TODO: Aren't these doublets?
(defund pair-listp (pairs)
  (declare (xargs :guard t))
  (if (atom pairs)
      (equal nil pairs)
    (and (eql 2 (len (car pairs)))
         (pair-listp (cdr pairs)))))

(defthm alistp-when-pair-listp-cheap
  (implies (PAIR-LISTP x)
           (alistp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pair-listp))))

(defthm >=-LEN-rewrite
  (implies (natp n)
           (equal (>=-LEN x n)
                  (>= (len x) n))))

(defthmd all->=-len-when-pair-listp
  (implies (pair-listp x)
           (all->=-len x 2))
  :hints (("Goal" :in-theory (enable pair-listp))))

(defthm ALL->=-LEN-when-pair-listp-cheap
  (implies (PAIR-LISTP x)
           (ALL->=-LEN x 2))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pair-listp))))

(defthm acl2-count-of-strip-cars-when-pair-listp
  (implies (and (pair-listp x)
                (consp x))
           (< (acl2-count (strip-cars x))
              (acl2-count x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable pair-listp))))

(defthm ACL2-COUNT-of-STRIP-CARS-weak
  (<= (ACL2-COUNT (STRIP-CARS x))
      (ACL2-COUNT x))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-of-strip-cadrs-when-pair-listp
  (implies (and (pair-listp x)
                (consp x))
           (< (acl2-count (strip-cadrs x))
              (acl2-count x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable pair-listp))))

(defthm ACL2-COUNT-of-STRIP-CAdRS-weak
  (<= (ACL2-COUNT (STRIP-CAdRS x))
      (ACL2-COUNT x))
  :rule-classes (:rewrite :linear))

(defthmd car-of-last-when-len-is-1
  (implies (equal 1 (len x))
           (equal (CAR (LAST x))
                  (car x)))
  :hints (("Goal" :expand ((LEN (CDR X)))
           :in-theory (enable last len))))

(defthm acl2-count-of-last-bound
  (<= (acl2-count (last x)) (acl2-count x))
  :rule-classes ((:linear)))

(defthm acl2-count-of-last-bound-rewrite
  (not (< (acl2-count x) (acl2-count (last x)))))

(defthm acl2-count-of-car-bound
  (IMPLIES (AND (CONSP TERM))
           (< (ACL2-COUNT (CAR term))
              (ACL2-COUNT TERM)))
  :rule-classes ((:linear))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm acl2-count-of-cdr-bound
  (IMPLIES (AND (CONSP TERM))
           (< (ACL2-COUNT (CdR term))
              (ACL2-COUNT TERM)))
  :rule-classes ((:linear))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm acl2-count-of-car-lemma
  (implies (<= (acl2-count term1) (acl2-count term2))
           (equal (< (acl2-count (car term1))
                     (acl2-count term2))
                  (if (consp term1)
                      t
                    (< 0
                       (acl2-count term2))))))

(defthm acl2-count-of-cdr-lemma
  (implies (<= (acl2-count term1) (acl2-count term2))
           (equal (< (acl2-count (cdr term1))
                     (acl2-count term2))
                  (if (consp term1)
                      t
                    (< 0
                       (acl2-count term2))))))

;todo: replace pair-listp with something standard:
(defthm pair-listp-of-make-doublets
  (pair-listp (make-doublets x y))
  :hints (("Goal" :in-theory (enable pair-listp make-doublets))))

;todo: this must exist
(defthm len-of-append-lemma
  (equal (len (append x y))
         (+ (len x) (len y))))


;; (defthm last-of-append
;;   (implies (and (true-listp x)
;;                 (true-listp y)
;;                 )
;;            (equal (last (append x y))
;;                   (if (consp y)
;;                       (last y)
;;                     (last x))))
;;   :hints (("Goal" :in-theory (enable append))))


(defthm car-car-of-make-doublets
  (equal (car (car (make-doublets x y)))
         (car x)))

(defthm strip-cadrs-of-make-doublets
  (equal (strip-cadrs (make-doublets x y))
         (take (len x) y)))

(in-theory (disable make-doublets))

(defthm strip-cars-of-cdr-of-make-doublets
  (implies (and ; (consp x)
            (true-listp x))
           (equal (strip-cars (cdr (make-doublets x y)))
                  (cdr x)))
  :hints (("Goal" :in-theory (enable make-doublets))))


;todo: looped with LIST::LEN-WHEN-AT-MOST-1
(defthmd consp-when-len-known
  (implies (and (equal free (len x))
;                (syntaxp (quotep free))
                (posp free) ;gets evaluated
                )
           (consp x)))

;move
(defthm member-equal-of-cons-drop
  (implies (not (equal item a))
           (equal (member-equal item (cons a b))
                  (member-equal item b)))
  :hints (("Goal" :in-theory (enable member-equal))))

;move
(defthm not-member-equal-of-nil
  (not (member-equal item nil))
  :hints (("Goal" :in-theory (enable member-equal))))

;;
;; end of library lemmas
;;

(in-theory (disable legal-variablep))

;(defforall-simple untranslated-TERM-supported-bstar-binderp)
;(verify-guards all-untranslated-TERM-supported-bstar-binderp)

;;;
;;; untranslated-variablep
;;;

;; An untranslated variable is a symbol, with several additional restrictions.
;; For example, t and nil are constants, as are keywords (all of these things
;; get quoted by translate).  Something with the syntax of a constant, like
;; *foo*, is also not an untranslated variable.
(defund untranslated-variablep (x)
  (declare (xargs :guard t))
  (legal-variablep x))

(defthm untranslated-variablep-forward-to-symbolp
  (implies (untranslated-variablep x)
           (symbolp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-variablep legal-variablep))))

;; Very similar to legal-variablep-of-intern-in-package-of-symbol.
(defthm untranslated-variablep-of-intern-in-package-of-symbol
  (implies (and (equal (symbol-package-name sym) "ACL2") ;gen
                (stringp str)
                (symbolp sym))
           (equal (untranslated-variablep (intern-in-package-of-symbol str sym))
                  (legal-variable-name-in-acl2-packagep str)))
  :hints (("Goal" :in-theory (enable untranslated-variablep))))

;;;
;;; untranslated-constantp
;;;

;; Recognize an untranslated term that is a constant
(defund untranslated-constantp (x)
  (declare (xargs :guard t))
  (or (acl2-numberp x) ;unquoted
      (characterp x) ;unquoted
      (stringp x) ;unquoted
      (and (symbolp x)
           (or (keywordp x) ;; unquoted keywords are constants
               ;; t, nil, and symbols that begin and end with * are constants:
               ;; TODO: Consider disallowing *
               (legal-constantp1 x)))
      (myquotep x)))

;; (defthm car-when-untranslated-constantp
;;   (implies (untranslated-constantp x)
;;            (equal (car x)
;;                   (if (consp x)
;;                       'quote
;;                     nil)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-forward-to-true-listp
  (implies (and (untranslated-constantp term)
                (consp term))
           (true-listp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-forward-to-equal-of-car-and-quote
  (implies (and (untranslated-constantp term)
                (consp term))
           (equal (car term) 'quote))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-of-cons
  (equal (untranslated-constantp (cons x y))
         (and (equal x 'quote)
              (true-listp y)
              (equal 1 (len y))))
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

;;these are terms that may contain let/let*/b*/cond/case-match/case/mv-let, etc.
;ttodo: add support for case, mv-let, and more constructs.



;; Sanity check: Nothing can be an untranslated-constant and an
;; untranslated-variable.
(defthm not-and-of-untranslated-constantp-and-untranslated-variablep
  (not (and (untranslated-constantp x)
            (untranslated-variablep x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable untranslated-variablep
                                     untranslated-constantp
                                     legal-variablep
                                     legal-variable-or-constant-namep))))

(mutual-recursion

 ;; test for (lambda (...vars...) ...declares... body)
 ;; Example with (two!) declares: (lambda (x y) (declare (ignore y)) (declare (ignore y)) (+ x))
 (defun untranslated-lambda-exprp (expr)
   (declare (xargs :hints (("Goal" :in-theory (enable ulambda-body)))))
   (and (call-of 'lambda expr)
        (true-listp (fargs expr))
        (<= 2 (len (fargs expr)))
        (symbol-listp (ulambda-formals expr)) ;the lambda is not necessarily complete (as it will be once translated)!
        ;todo: check the declares?
        (untranslated-termp (ulambda-body expr))))

 (defun untranslated-termp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (or (untranslated-constantp x)
       (untranslated-variablep x)
       (and (consp x)
            (let ((fn (ffn-symb x))) ;todo: what are the legal FNs?
              (case fn
                ((let let*) ;;(let <bindings> <body>) ;todo: what about declares?!
                 (and (true-listp (fargs x))
                      ;;(eql 2 (len (fargs x)))
                      (var-untranslated-term-pairsp (farg1 x))
                      ;;declares can intervene - todo: check their form
                      (untranslated-termp (car (last (fargs x))))))
                (b* ;;(b* <bindings> <form>+)
                    (and (true-listp (fargs x))
                         ;;(untranslated-term-pairsp (farg1 x)) ;TTODO: check the binder-forms more carefully
                         (pair-listp (farg1 x)) ;FIXME: These are not necessarily pairs (consider binders like when)
                         (or (not (farg1 x))    ;for termination
                             (all-untranslated-term-supported-bstar-binderp (strip-cars (farg1 x))))
                         (untranslated-term-listp (strip-cadrs (farg1 x)))
                         (untranslated-term-listp (rest (fargs x)))))
                (cond ;; (cond ...pairs...)
                 (and (true-listp (fargs x))
                      (untranslated-term-pairsp (fargs x))))
                ((case case-match) ; (case-match tm ...pat-term-pairs...) or (case tm ...symbol-term-pairs...)
                 (and (true-listp (fargs x))
                      (untranslated-termp (farg1 x))
                      (pat-untranslated-term-pairsp (cdr (fargs x)))))
                (quote nil) ;; disallow quotes bot covered by the untranslated-constantp call above
                (otherwise
                 ;;regular function call or lambda application:
                 (and (untranslated-term-listp (fargs x)) ;;first check the args
                      (or (symbolp fn)
                          (and (untranslated-lambda-exprp fn)
                               (equal (len (ulambda-formals fn))
                                      (len (fargs x))))))))))))

 (defun untranslated-term-supported-bstar-binderp (binder)
   (declare (xargs :guard t :measure (acl2-count binder)))
   (cond ((symbolp binder) t) ;includes binding a variable like x and binding - (means no binding)
         ((call-of 'mv binder) ;; (mv a b c)
          (symbol-listp (fargs binder)))
         ((call-of 'list binder) ;; (list a b c)
          (symbol-listp (fargs binder)))
         ((call-of 'er binder)
          (and (eql 1 (len (fargs binder)))
               (symbolp (first (fargs binder)))))
         ((or (call-of 'when binder)
              (call-of 'if binder)
              (call-of 'unless binder))
          (untranslated-term-listp (fargs binder)))
         (t nil)))

 (defun all-untranslated-term-supported-bstar-binderp (binders)
   (declare (xargs :guard t :measure (acl2-count binders)))
   (cond ((atom binders) (equal binders nil))
         (t (and (untranslated-term-supported-bstar-binderp (car binders))
                 (all-untranslated-term-supported-bstar-binderp (cdr binders))))))

 ;; recognize a list of non-dotted pairs of untranslated-terms (this occurs in
 ;; a cond and I guess in b*)
 (defun untranslated-TERM-pairsp  (pairs)
   (DECLARE (XARGS :GUARD T :measure (acl2-count pairs)))
   (if (atom pairs)
       (eq nil pairs)
     (let ((pair (first pairs)))
       (and (consp pair)
            (true-listp pair)
            (eql 2 (len pair))
            (untranslated-TERMp (first pair))
            (untranslated-TERMp (second pair))
            (untranslated-TERM-pairsp (rest pairs))))))

 (defun pat-untranslated-term-pairsp  (pairs)
   (declare (xargs :guard t :measure (acl2-count pairs)))
   (if (atom pairs)
       (eq nil pairs)
     (let ((pair (first pairs)))
       (and (consp pair)
            (true-listp pair)
            (>= (len pair) 2)
            (untranslated-TERMp (car (last pair)))
            (pat-untranslated-term-pairsp (rest pairs))))))

 ;; This occurs in a let/let*
 (defun var-untranslated-TERM-pairsp (pairs)
   (DECLARE (XARGS :GUARD T :measure (acl2-count pairs)))
   (if (atom pairs)
       (eq nil pairs)
     (let ((pair (first pairs)))
       (and (consp pair)
            (true-listp pair)
            (eql 2 (len pair))
            (untranslated-variablep (first pair))
            (untranslated-TERMp (second pair))
            (var-untranslated-TERM-pairsp (rest pairs))))))

 (DEFUN untranslated-TERM-LISTP (LST)
   (DECLARE (XARGS :GUARD T :measure (acl2-count lst)))
   (COND ((ATOM LST) (EQUAL LST NIL))
         (T (AND (untranslated-TERMP (CAR LST))
                 (untranslated-TERM-LISTP (CDR LST)))))))

(defthm untranslated-termp-when-legal-variablep-cheap
  (implies (legal-variablep x)
           (untranslated-termp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable untranslated-termp
                                     untranslated-variablep))))

(defthm untranslated-term-listp-when-legal-variable-listp-cheap
  (implies (legal-variable-listp x)
           (untranslated-term-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable legal-variable-listp))))

(defthm untranslated-termp-of-cons
  (equal (untranslated-termp (cons x y))
         (if (eq 'quote x)
             (and (true-listp y)
                  (equal 1 (len y)))
           (if (member-eq x '(let let*))
               (and (true-listp y)
                    ;;(eql 2 (len y))
                    (var-untranslated-term-pairsp (first y))
                    ;;declares can intervene - todo: check their form
                    (untranslated-termp (car (last y))))
             (if (eq 'b* x)
                 (and (true-listp y)
                      ;;(untranslated-term-pairsp (farg1 x)) ;TTODO: check the binder-forms more carefully
                      (pair-listp (first y))
                      (or (not y) ;for termination
                          (all-untranslated-term-supported-bstar-binderp (strip-cars (first y))))
                      (untranslated-term-listp (strip-cadrs (first y)))
                      (untranslated-term-listp (rest y)))
               (if (eq 'cond x)
                   (and (true-listp y)
                        (untranslated-term-pairsp y))
                 (if (member-eq x '(case case-match))
                     (and (true-listp y)
                          (untranslated-termp (car y))
                          (pat-untranslated-term-pairsp (cdr y)))
                   (and (untranslated-term-listp y)
                        (or (symbolp x)
                            (and (untranslated-lambda-exprp x)
                                 (equal (len (ulambda-formals x))
                                        (len y))))))))))))

(defthm untranslated-termp-of-cons-normal-case
  (implies (and (symbolp fn)
                (not (member-equal fn '(let let* b* cond case case-match)))
                (not (equal fn 'quote))
                )
           (equal (untranslated-termp (cons fn args))
                  (untranslated-term-listp args)))
  :hints (("Goal" :expand (untranslated-termp (cons fn args))
           :in-theory (enable member-equal))))

(defthm untranslated-termp-of-ulambda-body
  (implies (untranslated-lambda-exprp lambda)
           (untranslated-termp (ulambda-body lambda)))
  :hints (("Goal" :expand (untranslated-lambda-exprp lambda)
           :in-theory (enable ulambda-body untranslated-lambda-exprp))))

(defthm untranslated-lambda-exprp-of-make-ulambda
  (equal (untranslated-lambda-exprp (make-ulambda formals declares body))
         (and (symbol-listp formals)
              (untranslated-termp body)))
  :hints (("Goal"
           :in-theory (enable make-ulambda untranslated-lambda-exprp ulambda-body ulambda-formals))))

(defthm ulambda-formals-of-make-ulambda
  (equal (ulambda-formals (make-ulambda formals declares body))
         formals)
  :hints (("Goal"
           :in-theory (enable make-ulambda ulambda-formals))))

(defthm untranslated-termp-of-car-of-last-of-fargs
  (implies (and (untranslated-termp term)
                (member-equal (car term) '(let let*)))
           (untranslated-termp (car (last (fargs term)))))
  :hints (("Goal" :expand ((untranslated-termp term)))))

(defthm var-untranslated-term-pairsp-of-cadr
  (implies (and (untranslated-termp term)
                (member-equal (car term) '(let let*)))
           (var-untranslated-term-pairsp (cadr term))))

(local (in-theory (enable UNTRANSLATED-TERMP)))

(defthm untranslated-termp-of-cdr-of-assoc-equal
  (implies (and (assoc-equal key alist)
                (untranslated-term-listp (strip-cdrs alist)))
           (untranslated-termp (cdr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defun symbol-or-untranslated-lambda-exprp (item)
  (declare (xargs :guard t))
  (or (symbolp item)
      (untranslated-lambda-exprp item)))

;(defforall-simple symbol-or-untranslated-lambda-exprp)
;(verify-guards all-symbol-or-untranslated-lambda-exprp)
(DEFUN ALL-SYMBOL-OR-UNTRANSLATED-LAMBDA-EXPRP
  (X)
  (DECLARE (XARGS :guard t))
  (IF (ATOM X)
      T
      (AND (SYMBOL-OR-UNTRANSLATED-LAMBDA-EXPRP (FIRST X))
           (ALL-SYMBOL-OR-UNTRANSLATED-LAMBDA-EXPRP (REST X)))))

;(in-theory (disable untranslated-lambda-exprp))

 ;; test for ((lambda (...vars...) ...declares... body) ...args...)
(defun untranslated-lambda-applicationp (expr)
  (declare (xargs :guard t))
  (and (consp expr)
       (untranslated-lambda-exprp (ffn-symb expr))
       (untranslated-term-listp (fargs expr))))


;; (defthm UNTRANSLATED-TERM-PAIRSP-of-cadr
;;   (IMPLIES (AND (UNTRANSLATED-TERMP TERM)
;;                 (EQUAL (CAR TERM) 'B*))
;;            (UNTRANSLATED-TERM-PAIRSP (CADR TERM)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
;;   :hints (("Goal" :expand ((UNTRANSLATED-TERMP TERM))
;;            )))


(defthm UNTRANSLATED-TERMP-of-car
  (IMPLIES (AND (UNTRANSLATED-TERM-LISTP TERMS)
                (CONSP TERMS))
           (UNTRANSLATED-TERMP (CAR TERMS))))

(defthm UNTRANSLATED-TERM-listP-of-cdr
  (IMPLIES (AND (UNTRANSLATED-TERM-LISTP TERMS)
                (CONSP TERMS))
           (UNTRANSLATED-TERM-listP (CdR TERMS))))

(defthm UNTRANSLATED-TERM-LISTP-forward-to-true-listp
  (implies (UNTRANSLATED-TERM-LISTP TERMS)
           (true-listp terms))
  :rule-classes (:forward-chaining))

(defthm untranslated-term-listp-of-take
  (implies (untranslated-term-listp x)
           (untranslated-term-listp (take n x)))
  :hints (("Goal" :in-theory (e/d (untranslated-term-listp take)
                                  (;take-of-cdr-becomes-subrange
                                   )))))

(defthm untranslated-termp-of-cadr
  (implies (and (untranslated-term-listp terms)
                (<= 2 (len terms)))
           (untranslated-termp (cadr terms))))

(defthm untranslated-termp-of-car-of-last-gen
  (implies (untranslated-term-listp lst)
           (untranslated-termp (car (last lst))))
  :hints (("Goal" :in-theory (enable last))))

(defthm UNTRANSLATED-TERM-LISTP-of-remove
  (implies (UNTRANSLATED-TERM-LISTP x)
           (UNTRANSLATED-TERM-LISTP (REMOVE-EQUAL a x))))

(local (in-theory (disable symbol-alistp)))

;; This one cannot be replaced with a call to def-untranslated-term-fold because it is used to define it!
(mutual-recursion
 ;;rename all function calls in TERM according to ALIST
 (defun rename-fns-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (let ((bindings (farg1 term))
                   (declares (let-declares term))
                   (body (car (last (fargs term)))))
               `(,fn ,(rename-fns-in-var-untranslated-term-pairs bindings alist)
                     ,@declares ;; I think these can only be IGNORE declares, so nothing to do here.
                     ,(rename-fns-in-untranslated-term body alist)))
           (if (eq fn 'b*) ;; (b* (...bindings...) ...result-forms...)
               (let* ((bindings (farg1 term))
                      (result-forms (rest (fargs term)))
                      (binders (strip-cars bindings))
                      (expressions (strip-cadrs bindings)) ;FIXME: These are not necessarily pairs
                      )
                 `(,fn , ;(rename-fns-in-cadrs-of-untranslated-term-pairs bindings alist)
                   (make-doublets binders ;do nothing to these (TODO: might some have function calls?)
                                  (rename-fns-in-untranslated-term-list expressions alist))
                   ,@(rename-fns-in-untranslated-term-list result-forms alist)))
             (if (eq 'cond fn) ;;(cond <pairs>)
                 `(,fn ,@(rename-fns-in-untranslated-term-pairs (fargs term) alist))
               (if (member-eq fn '(case case-match))
                   `(,fn ,(rename-fns-in-untranslated-term (farg1 term) alist)
                         ,@(rename-fns-in-pat-untranslated-term-pairs (cdr (fargs term)) alist))
                 (let* ((args (fargs term))
                        (args (rename-fns-in-untranslated-term-list args alist))
                        (fn (if (consp fn)
                                ;; ((lambda (...vars...) ...declares... body) ...args...)
                                ;;if it's a lambda application, replace calls in the body:
                                (let* ((lambda-formals (ulambda-formals fn))
                                       (declares (ulambda-declares fn))
                                       (lambda-body (ulambda-body fn))
                                       (new-lambda-body (rename-fns-in-untranslated-term lambda-body alist))
                                       (new-fn (make-ulambda lambda-formals declares new-lambda-body)))
                                  new-fn)
                              ;;if it's not a lambda:
                              (if (assoc-eq fn alist)
                                  (lookup-eq fn alist) ;optimize!
                                fn))))
                   (cons fn args))))))))))

 ;; For the bindings of let and let*
 (defun rename-fns-in-var-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-alistp alist))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var (rename-fns-in-untranslated-term term alist))
             (rename-fns-in-var-untranslated-term-pairs (rest pairs) alist)))))

 ;; ;;currently used for b* (we ignore the b* binders?)
 ;; (defun rename-fns-in-cadrs-of-untranslated-term-pairs (pairs alist)
 ;;   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
 ;;                               (alistp alist))))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (cons (list term1 ;unchanged
 ;;                   (rename-fns-in-untranslated-term term2 alist))
 ;;             (rename-fns-in-cadrs-of-untranslated-term-pairs (rest pairs) alist)))))

 ;; For the pairs in a COND.
 (defun rename-fns-in-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (symbol-alistp alist))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (cons (list (rename-fns-in-untranslated-term term1 alist)
                   (rename-fns-in-untranslated-term term2 alist))
             (rename-fns-in-untranslated-term-pairs (rest pairs) alist)))))

 ;; For CASE and CASE-MATCH
 (defun rename-fns-in-pat-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                               (symbol-alistp alist))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat (first pair))
            (term2 (car (last pair))))
       (cons (list pat
                   (rename-fns-in-untranslated-term term2 alist))
             (rename-fns-in-pat-untranslated-term-pairs (rest pairs) alist)))))

 ;;rename all functions calls in TERMS according to ALIST
 (defun rename-fns-in-untranslated-term-list (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-alistp alist))))
   (if (endp terms)
       nil
     (cons (rename-fns-in-untranslated-term (first terms) alist)
           (rename-fns-in-untranslated-term-list (rest terms) alist)))))

(defthm TRUE-LISTP-of-rename-fns-in-untranslated-term-list
  (TRUE-LISTP (rename-fns-in-untranslated-term-list TERMs ALIST)))


(defthm untranslated-termp-forward-to-true-listp
  (implies (and (untranslated-termp term)
                (consp term))
           (true-listp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable untranslated-termp))))

(defthm untranslated-term-pairsp-of-cdr
  (implies (and (untranslated-termp term)
                (equal 'cond (car term)))
           (untranslated-term-pairsp (cdr term))))

(defthm pat-untranslated-term-pairsp-of-cddr
  (implies (and (untranslated-termp term)
                (member-eq (car term) '(case case-match)))
           (pat-untranslated-term-pairsp (cddr term)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm case-match-untranslated-termp-cadr
  (implies (and (untranslated-termp term)
                (member-eq (car term) '(case case-match)))
           (untranslated-termp (cadr term)))
  :hints (("Goal" :in-theory (enable member-equal))))

; todo: use an accessor
(defthm alistp-of-cadr-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (equal (car term) 'b*))
           (alistp (cadr term)))
  :hints (("Goal" :expand (UNTRANSLATED-TERMP TERM))))

(defthm all->=-len-of-cadr-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (equal (car term) 'b*))
           (all->=-len (cadr term) 2))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-term-listp-of-strip-cadrs-when-b*
  (implies (and (equal (car term) 'b*)
                (untranslated-termp term))
           (untranslated-term-listp (strip-cadrs (cadr term))))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-term-listp-of-cddr
  (implies (and (equal (car term) 'b*)
                (untranslated-termp term))
           (untranslated-term-listp (cddr term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-term-listp-of-cdr-2
  (implies (and (untranslated-termp term)
                (consp term)
                (not (equal 'quote (car term)))
                (not (member-eq (car term) '(let let*)))
                (not (equal (car term) 'b*))
                (not (equal 'cond (car term)))
                (not (member-eq (car term) '(case case-match))))
           (untranslated-term-listp (cdr term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm untranslated-lambda-exprp-of-car
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (untranslated-lambda-exprp (car term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(local (in-theory (disable let-declares)))

;; (defthm untranslated-termp-of-caddr-of-car
;;   (implies (and (untranslated-termp term)
;;                 (consp term)
;;                 (consp (car term)))
;;            (untranslated-termp (CADDR (CAR TERM))))
;;   :hints (("Goal" :expand (untranslated-termp term))))

;slow?
;why are the cars and cdrs getting exposed?
(defthm consp-of-cddr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (consp (cddr (car term))))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthmd cdr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (cdr (car term)))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm consp-of-cdr-of-car-when-untranslated-termp
  (implies (and (untranslated-termp term)
                (consp term)
                (consp (car term)))
           (consp (cdr (car term))))
  :hints (("Goal" :expand (untranslated-termp term))))

(defthm true-listp-of-car-when-UNTRANSLATED-TERMP
  (IMPLIES (AND (UNTRANSLATED-TERMP TERM)
                (CONSP (CAR TERM))
                )
           (TRUE-LISTP (CAR TERM)))
  :hints (("Goal" :expand (untranslated-termp term))))

(verify-guards rename-fns-in-untranslated-term
  :hints (("Goal" ;:expand ((UNTRANSLATED-TERMP TERM))
           :in-theory (e/d ( ;untranslated-lambda-exprp ;UNTRANSLATED-TERMP
                            )
                           (UNTRANSLATED-TERM-LISTP
                            UNTRANSLATED-TERMP
                            ALISTP)))))

(mutual-recursion
 ;;Return a list of all functions called in TERM
 (defun get-called-fns-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       nil
     (if (fquotep term)
         nil
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (union-eq (get-called-fns-in-var-untranslated-term-pairs (farg1 term))
                       (get-called-fns-in-untranslated-term (car (last (fargs term)))))
           (if (eq fn 'b*)
               (union-eq ;(get-called-fns-in-cadrs-of-untranslated-term-pairs (farg1 term))
                (get-called-fns-in-untranslated-term-list (strip-cadrs (farg1 term)))
                (get-called-fns-in-untranslated-term-list (rest (fargs term))))
             (if (eq 'cond fn) ;;(cond <pairs>)
                 (get-called-fns-in-untranslated-term-pairs (fargs term))
               (if (member-eq fn '(case case-match)) ;;(case-match tm <pat-term-pairs>)
                   (union-eq (get-called-fns-in-untranslated-term (farg1 term))
                             (get-called-fns-in-pat-untranslated-term-pairs (cdr (fargs term))))
                 (let ((fn-res (if (consp fn)
                                   ;;if it's a lambda application, examine the body:
                                   (get-called-fns-in-untranslated-term (ulambda-body fn))
                                 ;;if it's not a lambda:
                                 (list fn))))
                   (union-eq fn-res (get-called-fns-in-untranslated-term-list (fargs term))))))))))))

 (defun get-called-fns-in-var-untranslated-term-pairs (pairs)
   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(var (first pair))
            (term (second pair)))
       (union-eq (get-called-fns-in-untranslated-term term)
                 (get-called-fns-in-var-untranslated-term-pairs (rest pairs))))))

 (defun get-called-fns-in-cadrs-of-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term2 (second pair)))
       (union-eq (get-called-fns-in-untranslated-term term2)
                 (get-called-fns-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

 (defun get-called-fns-in-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (union-eq (union-eq (get-called-fns-in-untranslated-term term1)
                           (get-called-fns-in-untranslated-term term2))
                 (get-called-fns-in-untranslated-term-pairs (rest pairs))))))

  (defun get-called-fns-in-pat-untranslated-term-pairs (pairs)
   (declare (xargs :guard (pat-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term2 (car (last pair))))
       (union-eq (get-called-fns-in-untranslated-term term2)
                 (get-called-fns-in-pat-untranslated-term-pairs (rest pairs))))))

 (defun get-called-fns-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (get-called-fns-in-untranslated-term (first terms))
               (get-called-fns-in-untranslated-term-list (rest terms))))))


(make-flag flag-get-called-fns-in-untranslated-term get-called-fns-in-untranslated-term)
(defthm-flag-get-called-fns-in-untranslated-term
  (defthm true-listp-of-get-called-fns-in-untranslated-term
    (implies (untranslated-termp term)
             (symbol-listp (get-called-fns-in-untranslated-term term)))
    :flag get-called-fns-in-untranslated-term)
  (defthm true-listp-of-get-called-fns-in-var-untranslated-term-pairs
    (implies (var-untranslated-term-pairsp pairs)
             (symbol-listp (get-called-fns-in-var-untranslated-term-pairs pairs)))
    :flag get-called-fns-in-var-untranslated-term-pairs)
  (defthm true-listp-of-get-called-fns-in-cadrs-of-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (symbol-listp (get-called-fns-in-cadrs-of-untranslated-term-pairs pairs)))
    :flag get-called-fns-in-cadrs-of-untranslated-term-pairs)
  (defthm true-listp-of-get-called-fns-in-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (symbol-listp (get-called-fns-in-untranslated-term-pairs pairs)))
    :flag get-called-fns-in-untranslated-term-pairs)
  (defthm true-listp-of-get-called-fns-in-pat-untranslated-term-pairs
    (implies (pat-untranslated-term-pairsp pairs)
             (symbol-listp (get-called-fns-in-pat-untranslated-term-pairs pairs)))
    :flag get-called-fns-in-pat-untranslated-term-pairs)
  (defthm true-listp-of-get-called-fns-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (symbol-listp (get-called-fns-in-untranslated-term-list terms)))
    :flag get-called-fns-in-untranslated-term-list))

(verify-guards get-called-fns-in-untranslated-term
               :otf-flg t
               :hints (("Goal" :in-theory (enable true-listp-when-symbol-listp-rewrite-unlimited))))

;; (defun beta-reduce-untranslated (lambda-expr)
;;   (declare (xargs :guard (untranslated-lambda-applicationp lambda-expr)
;;                   :guard-hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)))))
;;   (let* ((lambda-expr (ffn-symb lambda-expr))
;;          (actuals (fargs lambda-expr))
;;          (formals (second lambda-expr))
;;          ;; don't need the declares here
;;          (body (car (last lambda-expr))))
;;         (my-sublis-var (pairlis$ formals actuals) ;;Darn.  We'll need a version of my-sublis-var that handles untranslated terms...
;;                        body)))

(defun def-untranslated-term-fold-fn (base-name
                                      operation-on-term ;; a term with free vars FN and ARGS
                                      extra-args
                                      extra-guards
                                      stobjs
                                      program-mode)
  (let* ((term-processor-fn (pack$ base-name '-in-untranslated-term))
         (term-list-processor-fn (pack$ base-name '-in-untranslated-term-list))
         (term-pairs-processor-fn (pack$ base-name '-in-untranslated-term-pairs))
         (pat-term-pairs-processor-fn (pack$ base-name '-in-pat-untranslated-term-pairs))
         (var-term-pairs-processor-fn (pack$ base-name '-in-var-untranslated-term-pairs))
         (theorems `((make-flag ,term-processor-fn)

                     (defthm ,(pack$ 'len-of- term-list-processor-fn)
                       (equal (len (,term-list-processor-fn terms ,@extra-args))
                              (len terms))
                       :hints (("Goal" :in-theory (enable len) :induct (len TERMS))))

                     (defthm ,(pack$ 'consp-of- term-list-processor-fn)
                       (equal (consp (,term-list-processor-fn terms ,@extra-args))
                              (consp terms))
                       :hints (("Goal" :expand (,term-list-processor-fn terms ,@extra-args))))

                     (,(pack$ 'defthm-flag- term-processor-fn)
                      (defthm ,(pack$ 'untranslated-termp-of- term-processor-fn)
                        (implies (and (untranslated-termp term)
                                      ,@extra-guards)
                                 (untranslated-termp (,term-processor-fn term ,@extra-args)))
                        :flag ,term-processor-fn)
                      (defthm ,(pack$ 'var-untranslated-term-pairsp-of- var-term-pairs-processor-fn)
                        (implies (and (var-untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                                 (var-untranslated-term-pairsp (,var-term-pairs-processor-fn pairs ,@extra-args)))
                        :flag ,var-term-pairs-processor-fn)
                      (defthm ,(pack$ 'untranslated-term-pairsp-of- term-pairs-processor-fn)
                        (implies (and (untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                                 (untranslated-term-pairsp (,term-pairs-processor-fn pairs ,@extra-args)))
                        :flag ,term-pairs-processor-fn)
                      (defthm ,(pack$ 'untranslated-term-pairsp-of- pat-term-pairs-processor-fn)
                        (implies (and (pat-untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                                 (pat-untranslated-term-pairsp (,pat-term-pairs-processor-fn pairs ,@extra-args)))
                        :flag ,pat-term-pairs-processor-fn)
                      (defthm ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn)
                        (implies (and (untranslated-term-listp terms)
                                      ,@extra-guards)
                                 (untranslated-term-listp (,term-list-processor-fn terms ,@extra-args)))
                        :flag ,term-list-processor-fn)
                      :hints (("Goal" :in-theory (enable untranslated-lambda-exprp)
                               :expand ((,term-processor-fn term ,@extra-args)
                                        (untranslated-termp (list* 'b*
                                                                   (make-doublets (strip-cars (cadr term))
                                                                                  (,term-list-processor-fn (strip-cadrs (cadr term)) ,@extra-args))
                                                                   (,term-list-processor-fn (cddr term) ,@extra-args)))))))

                     (verify-guards ,term-processor-fn
                       :hints (("Goal" :in-theory (e/d (untranslated-lambda-exprp
                                                        consp-when-len-known)
                                                       (untranslated-termp
                                                        untranslated-term-listp
                                                        ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn)))
                                :do-not '(generalize eliminate-destructors)
                                :do-not-induct t
                                :use ((:instance ,(pack$ 'untranslated-term-listp-of- term-list-processor-fn) (terms (cdr term))))
                                :expand ((untranslated-term-listp (,term-list-processor-fn (cdr term) ,@extra-args))
                                         (untranslated-termp term)
                                         (untranslated-termp (car (,term-list-processor-fn (cdr term) ,@extra-args)))
                                         )))
                       :otf-flg t))))
    `(progn
       (mutual-recursion
        (defun ,term-processor-fn (term ,@extra-args)
          (declare (xargs :guard (and (untranslated-termp term) ;todo: drop the and if no extra guards
                                      ,@extra-guards)
                          :verify-guards nil ;done below
                          :hints (("Goal" :do-not-induct t))
                          :ruler-extenders :all
                          ,@(and stobjs `(:stobjs ,stobjs))
                          ,@(if program-mode '(:mode :program) nil)))
          (if (atom term)
              term
            (if (fquotep term)
                term
              ;;function call or lambda
              (let* ((fn (ffn-symb term)))
                (if (member-eq fn '(let let*)) ;;(let <bindings> <body>)
                    `(,fn ,(,var-term-pairs-processor-fn (farg1 term) ,@extra-args)
                          ,@(butlast (rest (fargs term)) 1) ;the declares
                          ,(,term-processor-fn (car (last (fargs term))) ,@extra-args))
                  (if (eq fn 'b*)
                      (let* ((pairs (farg1 term))
                             (binders (strip-cars pairs))
                             (terms (strip-cadrs pairs)))
                        `(,fn
                          ,(make-doublets binders (,term-list-processor-fn terms ,@extra-args))
                          ,@(,term-list-processor-fn (rest (fargs term)) ,@extra-args)))
                    (if (eq 'cond fn) ;;(cond <pairs>)
                        `(,fn ,@(,term-pairs-processor-fn (fargs term) ,@extra-args))
                      ;; function call (possibly a lambda):
                      (if (member-eq fn '(case case-match)) ;;(case-match tm <pat-term-pairs>)
                          `(,fn ,(,term-processor-fn (farg1 term) ,@extra-args)
                                ,@(,pat-term-pairs-processor-fn (cdr (fargs term)) ,@extra-args))
                        (let* ((args (fargs term))
                               (args (,term-list-processor-fn args ,@extra-args)))
                          ,(rename-fns-in-untranslated-term operation-on-term (acons :recur term-processor-fn nil)))))))))))

        (defun ,var-term-pairs-processor-fn (pairs ,@extra-args)
          (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                          ,@(and stobjs `(:stobjs ,stobjs))))
          (if (endp pairs)
              nil
            (let* ((pair (first pairs))
                   (var (first pair))
                   (term (second pair)))
              (cons (list var (,term-processor-fn term ,@extra-args))
                    (,var-term-pairs-processor-fn (rest pairs) ,@extra-args)))))

        (defun ,term-pairs-processor-fn (pairs ,@extra-args)
          (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                          ,@(and stobjs `(:stobjs ,stobjs))))
          (if (endp pairs)
              nil
            (let* ((pair (first pairs))
                   (term1 (first pair))
                   (term2 (second pair)))
              (cons (list (,term-processor-fn term1 ,@extra-args)
                          (,term-processor-fn term2 ,@extra-args))
                    (,term-pairs-processor-fn (rest pairs) ,@extra-args)))))

        (defun ,pat-term-pairs-processor-fn (pairs ,@extra-args)
          (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                                      ,@extra-guards)
                          ,@(and stobjs `(:stobjs ,stobjs))))
          (if (endp pairs)
              nil
            (let* ((pair (first pairs))
                   (pat1 (first pair))
                   (term2 (car (last pair))))
              (cons (list pat1
                          (,term-processor-fn term2 ,@extra-args))
                    (,pat-term-pairs-processor-fn (rest pairs) ,@extra-args)))))

        (defun ,term-list-processor-fn (terms ,@extra-args)
          (declare (xargs :guard (and (untranslated-term-listp terms)
                                      ,@extra-guards)
                          ,@(and stobjs `(:stobjs ,stobjs))))
          (if (endp terms)
              nil
            (cons (,term-processor-fn (first terms) ,@extra-args)
                  (,term-list-processor-fn (rest terms) ,@extra-args)))))

       ;; Suppress theorems if program-mode
       ,@(and (not program-mode) theorems))))

;; Operation-on-term should be a term with free vars FN and ARGS.  It should
;; create a new untranslated term from the FN and the already-processed ARGS.
;; It can mention :recur to do a recursive call of the fold function being
;; defined.  It does nothing to atoms or quoted constants.

(defmacro def-untranslated-term-fold (base-name operation-on-term
                                                &key
                                                (extra-args 'nil)
                                                (extra-guards 'nil)
                                                (stobjs 'nil)
                                                (program-mode 'nil)
                                                )
  (def-untranslated-term-fold-fn base-name operation-on-term extra-args extra-guards stobjs program-mode))


;; This version does not require pseudo-terms...
;; a variant of rename-fns-in-untranslated-term that also expands lambdas that any fns get mapped to
(mutual-recursion
 ;; TODO: Do this in 2 steps?
 ;; ALIST maps function symbols to function symbols or lambdas
 (defun rename-fns-and-expand-lambdas-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))
                   :verify-guards nil ;;done below
                   :guard-hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
                                  :expand (UNTRANSLATED-TERMP TERM)))))
   (if (atom term) ;includes variables but also things like unquoted integers
       term
     (if (fquotep term)
         term
       ;;function call or lambda/let/etc.
       (let* (;;Now all we have to do is handle the fn.  It might already be a lambda, or it might be mapped to a lambda (which should be expanded).
              (fn (ffn-symb term)))
         (if (consp fn)
             ;; it's a lambda:
             (let ((args (rename-fns-and-expand-lambdas-in-untranslated-term-lst (fargs term) alist))) ;first, apply to the args
               (if nil ;(not (lambda-exprp fn)) ;TODO: drop this check
                   (hard-error 'rename-fns-and-expand-lambdas-in-untranslated-term "Unexpected form for term ~x0." (acons #\0 term nil))
                 ;;if the original term is a lambda application, replace calls in the lambda body:
                 (let* ((lambda-formals (ulambda-formals fn))
                        (declares (ulambda-declares fn))
                        (lambda-body (ulambda-body fn))
                        (new-lambda-body (rename-fns-and-expand-lambdas-in-untranslated-term lambda-body alist))
                        (fn (make-ulambda lambda-formals declares new-lambda-body)))
                   ;; Don't try to rename the fn because it is a lambda
                   `(,fn ,@args))))
           ;;The original fn is a symbol:
           (if (member-eq fn '(let let*))
               `(,fn
                 ;; the substitution:
                 ,(rename-fns-and-expand-lambdas-in-var-untranslated-term-pairs (farg1 term) alist)
                 ,@(butlast (rest (fargs term)) 1) ;the declares
                 ;; the body:
                 ,(rename-fns-and-expand-lambdas-in-untranslated-term (car (last (fargs term))) alist))
             (if (eq fn 'b*)
                 (let* ((bindings (farg1 term))
                        (result-forms (rest (fargs term)))
                        (binders (strip-cars bindings))
                        (expressions (strip-cadrs bindings)))
                   `(,fn , ;(rename-fns-in-cadrs-of-untranslated-term-pairs bindings alist)
                     (make-doublets binders ;do nothing to these (TODO: might some have function calls?)
                                    (rename-fns-and-expand-lambdas-in-untranslated-term-lst expressions alist))
                     ,@(rename-fns-and-expand-lambdas-in-untranslated-term-lst result-forms alist)))
               (if (eq fn 'cond)
                   `(,fn ,@(rename-fns-and-expand-lambdas-in-untranslated-term-pairs (fargs term) alist))
                 (if (member-eq fn '(case case-match))
                     `(,fn ,(rename-fns-and-expand-lambdas-in-untranslated-term (farg1 term) alist)
                           ,@(rename-fns-and-expand-lambdas-in-pat-untranslated-term-pairs (cdr (fargs term)) alist)) ;; regular function
                   (let ((args (rename-fns-and-expand-lambdas-in-untranslated-term-lst (fargs term) alist)) ;first, apply to the args
                         (res (assoc-eq fn alist))) ;;see if it is renamed
                     (if (not res)
                         `(,fn ,@args)  ;fn isn't renamed to anything
                       (let ((fn (cdr res)))
                         (if (LAMBDA-EXPRP fn) ;; TTODO: weaken to: (consp fn) ;test for a lambda
                             ;;fn is renamed to a lambda
                             (beta-reduce ;-untranslated
                              `(,fn ,@args))
                           ;;fn is mapped to a symbol
                           `(,fn ,@args))))))))))))))

 ;;Rename all functions called in TERMS according that are mapped to new names by ALIST.
 (defun rename-fns-and-expand-lambdas-in-untranslated-term-lst (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms) ;(true-listp terms)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
   (if (atom terms)
       nil
     (cons (rename-fns-and-expand-lambdas-in-untranslated-term (car terms) alist)
           (rename-fns-and-expand-lambdas-in-untranslated-term-lst (cdr terms) alist))))

 ;; these are non-dotted pairs
 (defun rename-fns-and-expand-lambdas-in-var-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var (rename-fns-and-expand-lambdas-in-untranslated-term term alist))
             (rename-fns-and-expand-lambdas-in-var-untranslated-term-pairs (rest pairs) alist)))))

  ;; these are non-dotted pairs
 (defun rename-fns-and-expand-lambdas-in-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (cons (list (rename-fns-and-expand-lambdas-in-untranslated-term term1 alist)
                   (rename-fns-and-expand-lambdas-in-untranslated-term term2 alist))
             (rename-fns-and-expand-lambdas-in-untranslated-term-pairs (rest pairs) alist)))))
 (defun rename-fns-and-expand-lambdas-in-pat-untranslated-term-pairs (pairs alist)
   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (all-symbol-or-untranslated-lambda-exprp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat1 (first pair))
            (term2 (car (last pair))))
       (cons (list pat1
                   (rename-fns-and-expand-lambdas-in-untranslated-term term2 alist))
             (rename-fns-and-expand-lambdas-in-pat-untranslated-term-pairs (rest pairs) alist))))))

(defthm TRUE-LISTP-of-RENAME-FNS-AND-EXPAND-LAMBDAS-IN-UNTRANSLATED-TERM-LST
  (TRUE-LISTP (RENAME-FNS-AND-EXPAND-LAMBDAS-IN-UNTRANSLATED-TERM-LST TERMs ALIST)))

(verify-guards rename-fns-and-expand-lambdas-in-untranslated-term
  :hints  (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
            :expand (UNTRANSLATED-TERMP TERM))))

;;;
;;;Replace 0-ary lambda applications of the form ((lambda () <body>)) with just
;;;<body> (and apply to body recursively).
;;;

(mutual-recursion
 (defun clean-up-0ary-lambdas-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
             `(,fn ,(clean-up-0ary-lambdas-in-var-untranslated-term-pairs (farg1 term))
                   ,@(butlast (rest (fargs term)) 1) ;the declares
                   ,(clean-up-0ary-lambdas-in-untranslated-term (car (last (fargs term)))))
           (if (eq fn 'b*)
               (let* ((pairs (farg1 term))
                      (binders (strip-cars pairs))
                      (terms (strip-cadrs pairs)))
                 `(,fn ;,(clean-up-0ary-lambdas-in-cadrs-of-untranslated-term-pairs (farg1 term))
                   ,(MAKE-DOUBLETS binders (clean-up-0ary-lambdas-in-untranslated-term-list terms))
                   ,@(clean-up-0ary-lambdas-in-untranslated-term-list (rest (fargs term)))))
             (if (eq 'cond fn) ;;(cond <pairs>)
                 `(,fn ,@(clean-up-0ary-lambdas-in-untranslated-term-pairs (fargs term)))
               (if (member-eq fn '(case case-match)) ;;(case-match tm <pat-term-pairs>)
                   `(,fn ,(clean-up-0ary-lambdas-in-untranslated-term (farg1 term))
                         ,@(clean-up-0ary-lambdas-in-pat-untranslated-term-pairs (cdr (fargs term))))
                 (if (consp fn)
                     ;;if it's a lambda application, recur on the body:
                     (let* ((lambda-formals (ulambda-formals fn))
                            (declares (ulambda-declares fn))
                            (lambda-body (ulambda-body fn))
                            (lambda-body (clean-up-0ary-lambdas-in-untranslated-term lambda-body))
                            (args (fargs term))
                            (args (clean-up-0ary-lambdas-in-untranslated-term-list args)))
                       (if (endp lambda-formals) ;test for 0-ary lambda
                           lambda-body
                         `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args)))
                   ;;regular function:
                   (cons fn (clean-up-0ary-lambdas-in-untranslated-term-list (fargs term))))))))))))

 (defun clean-up-0ary-lambdas-in-var-untranslated-term-pairs (pairs)
   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var (clean-up-0ary-lambdas-in-untranslated-term term))
             (clean-up-0ary-lambdas-in-var-untranslated-term-pairs (rest pairs))))))

 ;; ;;currently used for b* (we ignore the b* binders?)
 ;; (defun clean-up-0ary-lambdas-in-cadrs-of-untranslated-term-pairs (pairs)
 ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (cons (list term1 ;unchanged
 ;;                   (clean-up-0ary-lambdas-in-untranslated-term term2))
 ;;             (clean-up-0ary-lambdas-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-0ary-lambdas-in-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (cons (list (clean-up-0ary-lambdas-in-untranslated-term term1)
                   (clean-up-0ary-lambdas-in-untranslated-term term2))
             (clean-up-0ary-lambdas-in-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-0ary-lambdas-in-pat-untranslated-term-pairs (pairs)
   (declare (xargs :guard (pat-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat1 (first pair))
            (term2 (car (last pair))))
       (cons (list pat1
                   (clean-up-0ary-lambdas-in-untranslated-term term2))
             (clean-up-0ary-lambdas-in-pat-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-0ary-lambdas-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (cons (clean-up-0ary-lambdas-in-untranslated-term (first terms))
           (clean-up-0ary-lambdas-in-untranslated-term-list (rest terms))))))

(defthm TRUE-LISTP-of-CLEAN-UP-0ARY-LAMBDAS-IN-UNTRANSLATED-TERM-LIST
  (TRUE-LISTP (CLEAN-UP-0ARY-LAMBDAS-IN-UNTRANSLATED-TERM-LIST terms)))

(verify-guards CLEAN-UP-0ARY-LAMBDAS-IN-UNTRANSLATED-TERM-LIST
  :hints (("Goal" :in-theory (enable UNTRANSLATED-TERMP UNTRANSLATED-TERMP)
           :expand ((UNTRANSLATED-TERMP TERM)
                    (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM)))))
  )


;;TODO: Just write a rewriter for stuff like this?
;;TODO: Could also make a macro to automate the generation of the auxiliary functions in this:
;;;
;;;Replace (implies t x) with just x.
;;;

(mutual-recursion
 (defun clean-up-implies-of-t-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
             `(,fn ,(clean-up-implies-of-t-in-var-untranslated-term-pairs (farg1 term))
                   ,@(butlast (rest (fargs term)) 1) ;the declares
                   ,(clean-up-implies-of-t-in-untranslated-term (car (last (fargs term)))))
           (if (eq fn 'b*)
               (let* ((pairs (farg1 term))
                      (binders (strip-cars pairs))
                      (terms (strip-cadrs pairs)))
                 `(,fn ;,(clean-up-implies-of-t-in-cadrs-of-untranslated-term-pairs (farg1 term))
                   ,(MAKE-DOUBLETS binders (clean-up-implies-of-t-in-untranslated-term-list terms))
                   ,@(clean-up-implies-of-t-in-untranslated-term-list (rest (fargs term)))))
             (if (eq 'cond fn) ;;(cond <pairs>)
                 `(,fn ,@(clean-up-implies-of-t-in-untranslated-term-pairs (fargs term)))
               (if (member-eq fn '(case case-match)) ;;(case-match tm <pat-term-pairs>)
                   `(,fn ,(clean-up-implies-of-t-in-untranslated-term (farg1 term))
                         ,@(clean-up-implies-of-t-in-pat-untranslated-term-pairs (cdr (fargs term))))
                 (if (consp fn)
                     ;;if it's a lambda application, recur on the body:
                     (let* ((lambda-formals (ulambda-formals fn))
                            (declares (ulambda-declares fn))
                            (lambda-body (ulambda-body fn))
                            (lambda-body (clean-up-implies-of-t-in-untranslated-term lambda-body))
                            (args (fargs term))
                            (args (clean-up-implies-of-t-in-untranslated-term-list args)))
                       `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
                   (if (and (eq fn 'implies)
                            (equal *t* (farg1 term)))
                       ;; strip off the implies of t
                       (clean-up-implies-of-t-in-untranslated-term (farg2 term))
                     ;;regular function:
                     (cons fn (clean-up-implies-of-t-in-untranslated-term-list (fargs term)))))))))))))

 (defun clean-up-implies-of-t-in-var-untranslated-term-pairs (pairs)
   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var (clean-up-implies-of-t-in-untranslated-term term))
             (clean-up-implies-of-t-in-var-untranslated-term-pairs (rest pairs))))))

 ;; ;;currently used for b* (we ignore the b* binders?)
 ;; (defun clean-up-implies-of-t-in-cadrs-of-untranslated-term-pairs (pairs)
 ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
 ;;   (if (endp pairs)
 ;;       nil
 ;;     (let* ((pair (first pairs))
 ;;            (term1 (first pair))
 ;;            (term2 (second pair)))
 ;;       (cons (list term1 ;unchanged
 ;;                   (clean-up-implies-of-t-in-untranslated-term term2))
 ;;             (clean-up-implies-of-t-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-implies-of-t-in-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (cons (list (clean-up-implies-of-t-in-untranslated-term term1)
                   (clean-up-implies-of-t-in-untranslated-term term2))
             (clean-up-implies-of-t-in-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-implies-of-t-in-pat-untranslated-term-pairs (pairs)
   (declare (xargs :guard (pat-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat1 (first pair))
            (term2 (car (last pair))))
       (cons (list pat1
                   (clean-up-implies-of-t-in-untranslated-term term2))
             (clean-up-implies-of-t-in-pat-untranslated-term-pairs (rest pairs))))))

 (defun clean-up-implies-of-t-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (cons (clean-up-implies-of-t-in-untranslated-term (first terms))
           (clean-up-implies-of-t-in-untranslated-term-list (rest terms))))))

(defthm TRUE-LISTP-of-CLEAN-UP-implies-of-t-IN-UNTRANSLATED-TERM-LIST
  (TRUE-LISTP (CLEAN-UP-implies-of-t-IN-UNTRANSLATED-TERM-LIST terms)))

(verify-guards CLEAN-UP-implies-of-t-IN-UNTRANSLATED-TERM-LIST
  :hints (("Goal" :in-theory (enable UNTRANSLATED-TERMP UNTRANSLATED-TERMP)
           :expand ((UNTRANSLATED-TERMP TERM)
                    (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM))))))

;; Attempt to prove that every pseudo-term is a proper untranslated-term.  It's
;; not quite true; we need to exclude the special macros LET, etc. from
;; appearing as functions in the pseudo-term.  For example: (pseudo-termp '(let
;; '3)) = t.

;(make-flag pseudo-termp)

;; A stronger version of pseudo-termp that implies untranslated-termp.
;; This disallows supported macros like LET from appearing as
;; function calls in the term.  We'll have to add things to this as we
;; add support for more constructs in untranslated-termp.

;; Make sure this list is kept up to-date (perhaps prove a sanity
;; check that if none of these appear, untranslated-termp acts as we
;; would expect):
(defconst *supported-untranslated-term-macros* '(let let* b* cond case case-match))

(mutual-recursion
 (defund strong-pseudo-termp (x)
   (declare (xargs :guard t :mode :logic))
   (cond ((atom x) (legal-variablep x))
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cdr (cdr x)))))
         ((member-eq (car x) *supported-untranslated-term-macros*)
          nil)
         ((not (true-listp x)) nil)
         ((not (strong-pseudo-term-listp (cdr x))) nil)
         (t (or (symbolp (car x))
                (and (true-listp (car x))
                     (equal (len (car x)) 3)
                     (eq (car (car x)) 'lambda)
                     (symbol-listp (cadr (car x)))
                     (strong-pseudo-termp (caddr (car x)))
                     (equal (len (cadr (car x)))
                            (len (cdr x))))))))
 (defund strong-pseudo-term-listp (lst)
   (declare (xargs :guard t))
   (cond ((atom lst) (equal lst nil))
         (t (and (strong-pseudo-termp (car lst))
                 (strong-pseudo-term-listp (cdr lst)))))))

(make-flag strong-pseudo-termp)

(defthm-flag-strong-pseudo-termp
  (defthmd untranslated-termp-when-strong-pseudo-termp
    (implies (strong-pseudo-termp x)
             (untranslated-termp x))
    :flag strong-pseudo-termp)
  (defthmd untranslated-term-listp-when-strong-pseudo-term-listp
    (implies (strong-pseudo-term-listp lst)
             (untranslated-term-listp lst))
    :flag strong-pseudo-term-listp)
  :hints (("Goal" :in-theory (enable car-of-last-when-len-is-1
                                     strong-pseudo-termp
                                     strong-pseudo-term-listp
                                     member-equal; todo: rule about membership in constant lists when subset
                                     ulambda-body
                                     ulambda-formals)
           :expand ((untranslated-termp x)
                    (untranslated-lambda-exprp (car x))))))

(defthm strong-pseudo-term-listp-of-firstn
  (implies (strong-pseudo-term-listp lst)
           (strong-pseudo-term-listp (firstn n lst)))
  :hints (("Goal" :in-theory (enable strong-pseudo-term-listp
                                     firstn))))

;; Simplify things like (nth 3 (cons a (cons b x)))
(defun simplify-nth-of-cons (n term)
  (declare (xargs :guard (and (natp n)
                              (untranslated-termp term))))
  (if (not (call-of 'cons term))
      `(nth ,n ,term)
    (if (zp n) ;;(nth 0 (cons a x)) => a
        (farg1 term)
      ;;(nth <n> (cons a x)) => (nth <n-1> x)
      (simplify-nth-of-cons (+ -1 n) (farg2 term)))))

;(simplify-nth-of-cons 1 '(cons a (cons b x)))
;(simplify-nth-of-cons 0 '(cons a (cons b x)))
;(simplify-nth-of-cons 3 '(cons a (cons b x)))

(defthm UNTRANSLATED-TERMP-SIMPLIFY-NTH-OF-CONS
  (implies (and (UNTRANSLATED-TERMP term)
                (Natp n))
           (UNTRANSLATED-TERMP (SIMPLIFY-NTH-OF-CONS n term))))

;;TODO: Also abstract out the handling of the lambda body (usually the same, for transformations that don't mess with lambdas)
(def-untranslated-term-fold clean-up-nth-of-cons
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'nth fn)
             (eql 2 (len args)) ;drop?
             (or (natp (first args))
                 (and (quotep (first args))
                      (natp (unquote (first args)))))
             ;; (call-of 'cons (second args))
             ;; (eql 2 (len (fargs (second args))))
             )
        (let* ((arg1 (first args))
               (n (if (natp arg1) arg1 (unquote arg1)))
               (term (simplify-nth-of-cons n (second args))))
          term)
      ;;regular function:
      (cons fn args))))

;; (mutual-recursion
;;  (defun clean-up-nth-of-cons-in-untranslated-term (term)
;;    (declare (xargs :guard (untranslated-termp term)
;;                    :verify-guards nil ;done below
;;                    :hints (("Goal" :do-not-induct t))
;;                    :RULER-EXTENDERS :ALL
;;                    ))
;;      (if (atom term)
;;          term
;;        (if (fquotep term)
;;            term
;;          ;;function call or lambda
;;          (let* ((fn (ffn-symb term)))
;;            (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
;;                `(,fn ,(clean-up-nth-of-cons-in-var-untranslated-term-pairs (farg1 term))
;;                      ,@(butlast (rest (fargs term)) 1) ;the declares
;;                      ,(clean-up-nth-of-cons-in-untranslated-term (car (last term))))
;;              (if (eq fn 'b*)
;;                  (let* ((pairs (farg1 term))
;;                         (binders (strip-cars pairs))
;;                         (terms (strip-cadrs pairs)))
;;                    `(,fn ;,(clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (farg1 term))
;;                      ,(MAKE-DOUBLETS binders (clean-up-nth-of-cons-in-untranslated-term-list terms))
;;                      ,@(clean-up-nth-of-cons-in-untranslated-term-list (rest (fargs term)))))
;;                (if (eq 'cond fn) ;;(cond <pairs>)
;;                    `(,fn ,@(clean-up-nth-of-cons-in-untranslated-term-pairs (fargs term)))
;;                  ;; function call (possibly a lambda):
;;                  (let* ((args (fargs term))
;;                         (args (clean-up-nth-of-cons-in-untranslated-term-list args)))
;;                    (if (consp fn)
;;                        ;;if it's a lambda application, recur on the body:
;;                        (let* ((lambda-formals (ulambda-formals fn))
;;                               (declares (ulambda-declares fn))
;;                               (lambda-body (ulambda-body fn))
;;                               (lambda-body (clean-up-nth-of-cons-in-untranslated-term lambda-body))
;;                               )
;;                          `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;                      (if (and (eq 'nth fn)
;;                               (eql 2 (len args)) ;drop?
;;                               (or (natp (first args))
;;                                   (and (quotep (first args))
;;                                        (natp (unquote (first args)))))
;;                               ;; (call-of 'cons (second args))
;;                               ;; (eql 2 (len (fargs (second args))))
;;                               )
;;                          (let* ((arg1 (first args))
;;                                 (n (if (natp arg1) arg1 (unquote arg1)))
;;                                 (term (simplify-nth-of-cons n (second args))))
;;                            term)
;;                        ;;regular function:
;;                        (cons fn args)))))))))))

;;  (defun clean-up-nth-of-cons-in-var-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (var (first pair))
;;             (term (second pair)))
;;        (cons (list var (clean-up-nth-of-cons-in-untranslated-term term))
;;              (clean-up-nth-of-cons-in-var-untranslated-term-pairs (rest pairs))))))

;;  ;; ;;currently used for b* (we ignore the b* binders?)
;;  ;; (defun clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (pairs)
;;  ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;  ;;   (if (endp pairs)
;;  ;;       nil
;;  ;;     (let* ((pair (first pairs))
;;  ;;            (term1 (first pair))
;;  ;;            (term2 (second pair)))
;;  ;;       (cons (list term1 ;unchanged
;;  ;;                   (clean-up-nth-of-cons-in-untranslated-term term2))
;;  ;;             (clean-up-nth-of-cons-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-nth-of-cons-in-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (term1 (first pair))
;;             (term2 (second pair)))
;;        (cons (list (clean-up-nth-of-cons-in-untranslated-term term1)
;;                    (clean-up-nth-of-cons-in-untranslated-term term2))
;;              (clean-up-nth-of-cons-in-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-nth-of-cons-in-untranslated-term-list (terms)
;;    (declare (xargs :guard (untranslated-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (cons (clean-up-nth-of-cons-in-untranslated-term (first terms))
;;            (clean-up-nth-of-cons-in-untranslated-term-list (rest terms))))))

;; (defthm TRUE-LISTP-of-CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST
;;   (TRUE-LISTP (CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST terms)))

;; ;; (verify-guards CLEAN-UP-nth-of-cons-IN-UNTRANSLATED-TERM-LIST
;; ;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-TERMP UNTRANSLATED-TERMP)
;; ;;            :expand ((UNTRANSLATED-TERMP TERM)
;; ;;                     (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM))))))

;; (make-flag clean-up-nth-of-cons-in-untranslated-term)

;; (defthm len-of-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;   (equal (LEN (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST terms))
;;          (LEN terms)))

;rename the theorems:
;; (defthm-flag-clean-up-nth-of-cons-in-untranslated-term
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (untranslated-termp (clean-up-nth-of-cons-in-untranslated-term term)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-var-untranslated-term-pairs
;;     (implies (var-untranslated-term-pairsp pairs)
;;              (var-untranslated-term-pairsp (clean-up-nth-of-cons-in-var-untranslated-term-pairs pairs)))
;;     :flag clean-up-nth-of-cons-in-var-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term-pairs
;;     (implies (untranslated-term-pairsp pairs)
;;              (untranslated-term-pairsp (clean-up-nth-of-cons-in-untranslated-term-pairs pairs)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-nth-of-cons-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (untranslated-term-listp (clean-up-nth-of-cons-in-untranslated-term-list terms)))
;;     :flag clean-up-nth-of-cons-in-untranslated-term-list)
;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
;;            :expand ((CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM TERM)
;;                     (UNTRANSLATED-TERMP (LIST* 'B*
;;                                                (MAKE-DOUBLETS (STRIP-CARS (CADR TERM))
;;                                                            (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (STRIP-CADRS (CADR TERM))))
;;                                                (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDDR TERM))))))))

;; (defthm consp-of-clean-up-nth-of-cons-in-untranslated-term-list
;;   (equal (consp (clean-up-nth-of-cons-in-untranslated-term-list terms))
;;          (consp terms))
;;   :hints (("Goal" :expand (clean-up-nth-of-cons-in-untranslated-term-list terms))))

;; (verify-guards clean-up-nth-of-cons-in-untranslated-term
;;   :hints (("Goal" :in-theory (disable UNTRANSLATED-TERMP
;;                                       UNTRANSLATED-TERM-LISTP
;;                                       THEOREM-FOR-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;                                       )
;;            :do-not '(generalize eliminate-destructors)
;;            :do-not-induct t
;;            :use ((:instance THEOREM-FOR-CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST
;;                             (terms (cdr term))))
;;            :expand ((UNTRANSLATED-TERMP TERM)
;;                     (UNTRANSLATED-TERMP (CAR (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM))))
;;                     (UNTRANSLATED-TERM-LISTP (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM)))
;; ; (UNTRANSLATED-TERMP (CAR (CLEAN-UP-NTH-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDR TERM))))
;;                     (UNTRANSLATED-LAMBDA-EXPRP (CAR TERM)))))

;;   :otf-flg t)


(defun simplify-true-listp-of-cons (term)
  (declare (xargs :guard (untranslated-termp term)))
  (if (equal nil term)
      t
    (if (equal *nil* term)
        t
      (if (not (call-of 'cons term))
          `(true-listp ,term)
        (simplify-true-listp-of-cons (farg2 term))))))

;(simplify-true-listp-of-cons 'x)
;(simplify-true-listp-of-cons 'nil)
;(simplify-true-listp-of-cons ''nil)
;(simplify-true-listp-of-cons '(cons a (cons b x)))
;(simplify-true-listp-of-cons '(cons a (cons b nil)))

;; (mutual-recursion
;;  (defun clean-up-true-listp-of-cons-in-untranslated-term (term)
;;    (declare (xargs :guard (untranslated-termp term)
;;                    :verify-guards nil ;done below
;;                    :hints (("Goal" :do-not-induct t))
;;                    :RULER-EXTENDERS :ALL
;;                    ))
;;      (if (atom term)
;;          term
;;        (if (fquotep term)
;;            term
;;          ;;function call or lambda
;;          (let* ((fn (ffn-symb term)))
;;            (if (member-eq fn '(let let*)) ;;(let <bindings> <body>) ;TODO: what about declares?!
;;                `(,fn ,(clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (farg1 term))
;;                      ,@(butlast (rest (fargs term)) 1) ;the declares
;;                      ,(clean-up-true-listp-of-cons-in-untranslated-term (car (last term))))
;;              (if (eq fn 'b*)
;;                  (let* ((pairs (farg1 term))
;;                         (binders (strip-cars pairs))
;;                         (terms (strip-cadrs pairs)))
;;                    `(,fn ;,(clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (farg1 term))
;;                      ,(MAKE-DOUBLETS binders (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;                      ,@(clean-up-true-listp-of-cons-in-untranslated-term-list (rest (fargs term)))))
;;                (if (eq 'cond fn) ;;(cond <pairs>)
;;                    `(,fn ,@(clean-up-true-listp-of-cons-in-untranslated-term-pairs (fargs term)))
;;                  ;; function call (possibly a lambda):
;;                  (let* ((args (fargs term))
;;                         (args (clean-up-true-listp-of-cons-in-untranslated-term-list args)))
;;                    (if (consp fn)
;;                        ;;if it's a lambda application, recur on the body:
;;                        (let* ((lambda-formals (ulambda-formals fn))
;;                               (declares (ulambda-declares fn))
;;                               (lambda-body (ulambda-body fn))
;;                               (lambda-body (clean-up-true-listp-of-cons-in-untranslated-term lambda-body))
;;                               )
;;                          `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;                      (if (and (eq 'true-listp fn)
;;                               (eql 1 (len args)) ;drop?
;;                               ;; (call-of 'cons (first args))
;;                               ;; (eql 2 (len (fargs (second args))))
;;                               )
;;                          (let* ((arg1 (first args))
;;                                 (term (simplify-true-listp-of-cons arg1)))
;;                            term)
;;                        ;;regular function:
;;                        (cons fn args)))))))))))

;;  (defun clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (var (first pair))
;;             (term (second pair)))
;;        (cons (list var (clean-up-true-listp-of-cons-in-untranslated-term term))
;;              (clean-up-true-listp-of-cons-in-var-untranslated-term-pairs (rest pairs))))))

;;  ;; ;;currently used for b* (we ignore the b* binders?)
;;  ;; (defun clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (pairs)
;;  ;;   (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;  ;;   (if (endp pairs)
;;  ;;       nil
;;  ;;     (let* ((pair (first pairs))
;;  ;;            (term1 (first pair))
;;  ;;            (term2 (second pair)))
;;  ;;       (cons (list term1 ;unchanged
;;  ;;                   (clean-up-true-listp-of-cons-in-untranslated-term term2))
;;  ;;             (clean-up-true-listp-of-cons-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-true-listp-of-cons-in-untranslated-term-pairs (pairs)
;;    (declare (xargs :guard (untranslated-term-pairsp pairs)))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (term1 (first pair))
;;             (term2 (second pair)))
;;        (cons (list (clean-up-true-listp-of-cons-in-untranslated-term term1)
;;                    (clean-up-true-listp-of-cons-in-untranslated-term term2))
;;              (clean-up-true-listp-of-cons-in-untranslated-term-pairs (rest pairs))))))

;;  (defun clean-up-true-listp-of-cons-in-untranslated-term-list (terms)
;;    (declare (xargs :guard (untranslated-term-listp terms)))
;;    (if (endp terms)
;;        nil
;;      (cons (clean-up-true-listp-of-cons-in-untranslated-term (first terms))
;;            (clean-up-true-listp-of-cons-in-untranslated-term-list (rest terms))))))



;; (make-flag clean-up-true-listp-of-cons-in-untranslated-term)

;; (defthm len-of-clean-up-true-listp-of-cons-in-untranslated-term-list
;;   (equal (len (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;          (len terms)))

;; (defthm consp-of-clean-up-true-listp-of-cons-in-untranslated-term-list
;;   (equal (consp (clean-up-true-listp-of-cons-in-untranslated-term-list terms))
;;          (consp terms))
;;   :hints (("Goal" :expand (clean-up-true-listp-of-cons-in-untranslated-term-list terms))))

;rename the theorems:
;; (defthm-flag-clean-up-true-listp-of-cons-in-untranslated-term
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term
;;     (implies (untranslated-termp term)
;;              (untranslated-termp (clean-up-true-listp-of-cons-in-untranslated-term term)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-var-untranslated-term-pairs
;;     (implies (var-untranslated-term-pairsp pairs)
;;              (var-untranslated-term-pairsp (clean-up-true-listp-of-cons-in-var-untranslated-term-pairs pairs)))
;;     :flag clean-up-true-listp-of-cons-in-var-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term-pairs
;;     (implies (untranslated-term-pairsp pairs)
;;              (untranslated-term-pairsp (clean-up-true-listp-of-cons-in-untranslated-term-pairs pairs)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term-pairs)
;;   (defthm theorem-for-clean-up-true-listp-of-cons-in-untranslated-term-list
;;     (implies (untranslated-term-listp terms)
;;              (untranslated-term-listp (clean-up-true-listp-of-cons-in-untranslated-term-list terms)))
;;     :flag clean-up-true-listp-of-cons-in-untranslated-term-list)
;;   :hints (("Goal" :in-theory (enable UNTRANSLATED-LAMBDA-EXPRP)
;;            :expand ((CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM TERM)
;;                     (UNTRANSLATED-TERMP (LIST* 'B*
;;                                                (MAKE-DOUBLETS (STRIP-CARS (CADR TERM))
;;                                                            (CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (STRIP-CADRS (CADR TERM))))
;;                                                (CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (CDDR TERM))))))))




;; (verify-guards clean-up-true-listp-of-cons-in-untranslated-term
;;   :hints (("Goal" :in-theory (e/d (UNTRANSLATED-LAMBDA-EXPRP
;;                                    consp-when-len-known)
;;                                   (UNTRANSLATED-TERMP
;;                                    UNTRANSLATED-TERM-LISTP
;;                                    THEOREM-FOR-CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST

;;                                    ))
;;            :do-not '(generalize eliminate-destructors)
;;            :do-not-induct t
;;            :use ((:instance THEOREM-FOR-CLEAN-UP-TRUE-LISTP-OF-CONS-IN-UNTRANSLATED-TERM-LIST (terms (cdr term)))
;;                  )
;;            :expand ((UNTRANSLATED-TERMP TERM))))
;;   :otf-flg t)


(def-untranslated-term-fold
  clean-up-true-listp-of-cons
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'true-listp fn)
             (eql 1 (len args)) ;drop?
             ;; (call-of 'cons (first args))
             ;; (eql 2 (len (fargs (second args))))
             )
        (let* ((arg1 (first args))
               (term (simplify-true-listp-of-cons arg1)))
          term)
      ;;regular function:
      (cons fn args))))

;; Drop T from the arguments of an AND
;; introduces CLEAN-UP-AND-OF-T-IN-UNTRANSLATED-TERM
(def-untranslated-term-fold clean-up-and-of-t
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (eq 'and fn)
        (let ((args (remove-equal *t* (remove-equal 't args))))
          (if (consp args)
              `(and ,@args)
            't))
      ;;regular function:
      (cons fn args))))

(defun simplify-equality-of-len-of-cons-nest-and-number (cons-nest num)
  (declare (xargs :guard (and (UNTRANSLATED-TERMP cons-nest)
                              (integerp num))))
  (if (or (equal cons-nest nil)
          (equal cons-nest *nil*))
      (if (eql num 0)
          't
        'nil)
    (if (and (call-of 'cons cons-nest)
             (eql 2 (len (fargs cons-nest))))
        (simplify-equality-of-len-of-cons-nest-and-number (farg2 cons-nest) (+ -1 num))
      ;; nothing more to do:
      `(equal (len ,cons-nest) ,num) ;not quoting num; we are working with untranslated terms
      )))

(defthm untranslated-termp-of-simplify-equality-of-len-of-cons-nest-and-number
 (implies (and (untranslated-termp cons-nest)
               (integerp num))
          (untranslated-termp (simplify-equality-of-len-of-cons-nest-and-number cons-nest num))))

;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b x)) 2)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 2)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 1)
;(simplify-equality-of-len-of-cons-nest-and-number '(cons a (cons b nil)) 3)

;Simplify stuff like (EQUAL (LEN (CONS I (CONS J 'NIL))) 2)
(def-untranslated-term-fold clean-up-equal-of-len-of-cons-nest-and-number
  (if (consp fn)
      ;;if it's a lambda application, recur on the body:
      (let* ((lambda-formals (ulambda-formals fn))
             (declares (ulambda-declares fn))
             (lambda-body (ulambda-body fn))
             (lambda-body (:recur lambda-body))
             )
        `(,(make-ulambda lambda-formals declares lambda-body) ,@args))
    (if (and (eq 'equal fn) ;(equal (len <cons-nest>) <n>)
             (eql 2 (len args))
             (call-of 'len (first args))
             (eql 1 (len (fargs (first args))))
             (or (natp (second args))
                 (and (myquotep (second args)) ;TODO: stronger version of quotep that checks for at least 1 arg
                      (equal 1 (len (fargs (second args))))
                      (natp (unquote (second args))))))
        (let* ((n (second args))
               (n (if (natp n) n (unquote n))))
          (simplify-equality-of-len-of-cons-nest-and-number (farg1 (first args)) n))
      (cons fn args))))



;;TTODO: Add support for lambdas!
;; Doesn't work because it doesn't replace variables (improve def-untranslated-term-fold to take an argument specifying what to do to variables?)
;; (def-untranslated-term-fold replace
;;   (let* (;; (fn (if (consp fn)
;;          ;;         ;;if it's a lambda application, recur on the body:
;;          ;;         (let* ((lambda-formals (ulambda-formals fn))
;;          ;;                (declares (ulambda-declares fn))
;;          ;;                (lambda-body (ulambda-body fn))
;;          ;;                (lambda-body (:recur lambda-body alist))
;;          ;;                )
;;          ;;           `((lambda (,@lambda-formals) ,@declares ,lambda-body) ,@args))
;;          ;;       fn))
;;          (term `(,fn ,@args)))
;;     (if (assoc-equal term alist)
;;         (cdr (assoc-equal term alist))
;;       term))
;;   :extra-args (alist)
;;   :extra-guards ((alistp alist) (untranslated-term-listp (strip-cdrs alist))))

;TODO: Does this handle lambdas right? See what's done with lambdas in replace-params-in-calls-in-term
(mutual-recursion
 (defun replace-in-untranslated-term (term alist)
   (declare (xargs :guard (and (untranslated-termp term)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))
                   :verify-guards nil
                   :hints (("Goal" :do-not-induct t))
                   :ruler-extenders :all))
   (if (assoc-equal term alist)
       (cdr (assoc-equal term alist))
     (if (atom term)
         term
       (if (fquotep term)
           term
         (let* ((fn (ffn-symb term)))
           (if (member-eq fn '(let let*))
               (cons fn
                     (cons (replace-in-var-untranslated-term-pairs (farg1 term)
                                                                   alist)
                           (append (butlast (rest (fargs term)) 1)
                                   (cons (replace-in-untranslated-term (car (last (fargs term)))
                                                                       alist)
                                         'nil))))
             (if (eq fn 'b*)
                 (let* ((pairs (farg1 term))
                        (binders (strip-cars pairs))
                        (terms (strip-cadrs pairs)))
                   (cons fn
                         (cons (make-doublets binders
                                              (replace-in-untranslated-term-list terms alist))
                               (replace-in-untranslated-term-list (rest (fargs term))
                                                                  alist))))
               (if (eq 'cond fn)
                   (cons fn (replace-in-untranslated-term-pairs (fargs term)
                                                                alist))
                 (if (member-eq fn '(case case-match))
                     (list* fn (replace-in-untranslated-term (farg1 term) alist)
                            (replace-in-pat-untranslated-term-pairs (cdr (fargs term))
                                                                    alist))
                   (let* ((args (fargs term))
                          (args (replace-in-untranslated-term-list args alist)))
                     ;;todo: handle lambdas
                     (let* ((term (cons fn args)))
                       term)))))))))))
 (defun replace-in-var-untranslated-term-pairs
   (pairs alist)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
       (let* ((pair (first pairs))
              (var (first pair))
              (term (second pair)))
             (cons (list var (replace-in-untranslated-term term alist))
                   (replace-in-var-untranslated-term-pairs (rest pairs)
                                                           alist)))))
 (defun replace-in-untranslated-term-pairs
   (pairs alist)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
       (let* ((pair (first pairs))
              (term1 (first pair))
              (term2 (second pair)))
             (cons (list (replace-in-untranslated-term term1 alist)
                         (replace-in-untranslated-term term2 alist))
                   (replace-in-untranslated-term-pairs (rest pairs)
                                                       alist)))))
 (defun replace-in-pat-untranslated-term-pairs
   (pairs alist)
   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
       (let* ((pair (first pairs))
              (pat1 (first pair))
              (term2 (car (last pair))))
             (cons (list pat1
                         (replace-in-untranslated-term term2 alist))
                   (replace-in-pat-untranslated-term-pairs (rest pairs)
                                                       alist)))))
 (defun replace-in-untranslated-term-list
   (terms alist)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp terms)
       nil
       (cons (replace-in-untranslated-term (first terms)
                                           alist)
             (replace-in-untranslated-term-list (rest terms)
                                                alist)))))

(make-flag replace-in-untranslated-term)

(defthm len-of-replace-in-untranslated-term-list
  (equal (len (replace-in-untranslated-term-list terms alist))
         (len terms))
  :hints (("Goal" :in-theory (enable len)
           :induct (len terms))))
(defthm consp-of-replace-in-untranslated-term-list
  (equal (consp (replace-in-untranslated-term-list terms alist))
         (consp terms))
  :hints (("Goal" :expand (replace-in-untranslated-term-list terms alist))))

(defthm-flag-replace-in-untranslated-term
  (defthm untranslated-termp-of-replace-in-untranslated-term
    (implies (and (untranslated-termp term)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-termp (replace-in-untranslated-term term alist)))
    :flag replace-in-untranslated-term)
  (defthm var-untranslated-term-pairsp-of-replace-in-var-untranslated-term-pairs
    (implies (and (var-untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (var-untranslated-term-pairsp (replace-in-var-untranslated-term-pairs pairs alist)))
    :flag replace-in-var-untranslated-term-pairs)
  (defthm untranslated-term-pairsp-of-replace-in-untranslated-term-pairs
    (implies (and (untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-pairsp (replace-in-untranslated-term-pairs pairs alist)))
    :flag replace-in-untranslated-term-pairs)
  (defthm pat-untranslated-term-pairsp-of-replace-in-pat-untranslated-term-pairs
    (implies (and (pat-untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (pat-untranslated-term-pairsp (replace-in-pat-untranslated-term-pairs pairs alist)))
    :flag replace-in-pat-untranslated-term-pairs)
  (defthm untranslated-term-listp-ofreplace-in-untranslated-term-list
    (implies (and (untranslated-term-listp terms)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-listp (replace-in-untranslated-term-list terms alist)))
    :flag replace-in-untranslated-term-list)
  :hints (("Goal" :in-theory (enable untranslated-lambda-exprp)
           :expand ((replace-in-untranslated-term term alist)
                    (untranslated-termp (list* 'b*
                                               (make-doublets (strip-cars (cadr term))
                                                              (replace-in-untranslated-term-list (strip-cadrs (cadr term))
                                                                                                 alist))
                                               (replace-in-untranslated-term-list (cddr term)
                                                                                  alist)))))))

(VERIFY-GUARDS REPLACE-IN-UNTRANSLATED-TERM
  :HINTS (("Goal" :IN-THEORY (E/D (UNTRANSLATED-LAMBDA-EXPRP CONSP-WHEN-LEN-KNOWN)
                                  (UNTRANSLATED-TERMP UNTRANSLATED-TERM-LISTP
                                                      UNTRANSLATED-TERM-LISTP-OFREPLACE-IN-UNTRANSLATED-TERM-LIST))
           :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
           :DO-NOT-INDUCT T
           :USE ((:INSTANCE UNTRANSLATED-TERM-LISTP-OFREPLACE-IN-UNTRANSLATED-TERM-LIST
                            (TERMS (CDR TERM))))
           :EXPAND ((UNTRANSLATED-TERM-LISTP (REPLACE-IN-UNTRANSLATED-TERM-LIST (CDR TERM)
                                                                                ALIST))
                    (UNTRANSLATED-TERMP TERM)
                    (UNTRANSLATED-TERMP (CAR (REPLACE-IN-UNTRANSLATED-TERM-LIST (CDR TERM)
                                                                                ALIST))))))
  :OTF-FLG T)
;; test (TODO: Make unranslated-terms-tests and put this there using deftest):
;; (equal (replace-in-untranslated-term '(foo (bar 3)) (acons '(bar 3) '7 nil))
;;        '(foo 7))

(defun vars-bound-in-case-match-pattern (pat)
  (declare (xargs :guard t))
  (mv-let (tests bindings)
      (match-tests-and-bindings :ignore pat nil nil)
    (declare (ignore tests))
    (and (alistp bindings)              ; so we don't have to prover property of match-tests-and-bindings
         (strip-cars bindings))))

;; Only have to worry about the !v case
(defun var-refs-in-case-match-pattern (pat)
  (declare (xargs :guard t))
  (if (symbolp pat)
      (and (> (length (symbol-name pat)) 0)
           (eql #\! (char (symbol-name pat) 0))
           (list (intern-in-package-of-symbol
                  (subseq (symbol-name pat)
                          1 (length (symbol-name pat)))
                  pat)))
    (and (consp pat)
         (append (var-refs-in-case-match-pattern (car pat)) (var-refs-in-case-match-pattern (cdr pat))))))

(mutual-recursion
 ;;Return a list of all variables called in TERM
 (defun get-vars-in-untranslated-term (term)
   (declare (xargs :guard (untranslated-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       (if (symbolp term)
           (if (legal-variablep term) ;excludes t, nil, keywords, etc.
               (list term)
             nil)
         nil) ;must be an unquoted constant
     (if (fquotep term)
         nil
       ;;function call or lambda
       (let* ((fn (ffn-symb term)))
         (if (member-eq fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (union-eq (get-vars-in-var-untranslated-term-pairs (farg1 term))
                       (get-vars-in-untranslated-term (car (last (fargs term)))))
           (if (eq fn 'b*)
               (union-eq ;(get-vars-in-cadrs-of-untranslated-term-pairs (farg1 term))
                (get-vars-in-untranslated-term-list (strip-cadrs (farg1 term)))
                (get-vars-in-untranslated-term-list (rest (fargs term))))
             (if (eq 'cond fn) ;;(cond <pairs>)
                 (get-vars-in-untranslated-term-pairs (fargs term))
               (if (member-eq fn '(case case-match)) ;;(case-match tm <pat-term-pairs>) ;; TODO: add vars only in pattern
                   (union-eq (get-vars-in-untranslated-term (farg1 term))
                             (get-vars-in-pat-untranslated-term-pairs (cdr (fargs term)) (eq fn 'case-match)))
                 (let ((fn-res (if (consp fn)
                                   ;;if it's a lambda application, examine the body:
                                   (let ((lambda-body (ulambda-body fn)))
                                     (get-vars-in-untranslated-term lambda-body))
                                 ;;if it's not a lambda:
                                 nil)))
                   (union-eq fn-res (get-vars-in-untranslated-term-list (fargs term))))))))))))

 (defun get-vars-in-var-untranslated-term-pairs (pairs)
   (declare (xargs :guard (var-untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(var (first pair))
            (term (second pair)))
       (union-eq (get-vars-in-untranslated-term term)
                 (get-vars-in-var-untranslated-term-pairs (rest pairs))))))

 (defun get-vars-in-cadrs-of-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(term1 (first pair))
            (term2 (second pair)))
       (union-eq (get-vars-in-untranslated-term term2)
                 (get-vars-in-cadrs-of-untranslated-term-pairs (rest pairs))))))

 (defun get-vars-in-untranslated-term-pairs (pairs)
   (declare (xargs :guard (untranslated-term-pairsp pairs)))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (union-eq (union-eq (get-vars-in-untranslated-term term1)
                           (get-vars-in-untranslated-term term2))
                 (get-vars-in-untranslated-term-pairs (rest pairs))))))

 (defun get-vars-in-pat-untranslated-term-pairs (pairs case-match-p)
   (declare (xargs :guard (pat-untranslated-term-pairsp pairs))
            (ignorable case-match-p))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat (first pair))
            (term2 (car (last pair))))
       (union-eq (get-vars-in-untranslated-term term2)
                 (and case-match-p
                      (var-refs-in-case-match-pattern pat))
                 (get-vars-in-pat-untranslated-term-pairs (rest pairs) case-match-p)))))

 ;;rename all functions calls in TERMS according to
 (defun get-vars-in-untranslated-term-list (terms)
   (declare (xargs :guard (untranslated-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (get-vars-in-untranslated-term (first terms))
               (get-vars-in-untranslated-term-list (rest terms))))))

(make-flag flag-get-vars-in-untranslated-term get-vars-in-untranslated-term)

(defthm-flag-get-vars-in-untranslated-term
  (defthm symbol-listp-of-get-vars-in-untranslated-term
    (implies (untranslated-termp term)
             (symbol-listp (get-vars-in-untranslated-term term)))
    :flag get-vars-in-untranslated-term)
  (defthm symbol-listp-of-get-vars-in-var-untranslated-term-pairs
    (implies (var-untranslated-term-pairsp pairs)
             (symbol-listp (get-vars-in-var-untranslated-term-pairs pairs)))
    :flag get-vars-in-var-untranslated-term-pairs)
  (defthm symbol-listp-of-get-vars-in-cadrs-of-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (symbol-listp (get-vars-in-cadrs-of-untranslated-term-pairs pairs)))
    :flag get-vars-in-cadrs-of-untranslated-term-pairs)
  (defthm symbol-listp-of-get-vars-in-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (symbol-listp (get-vars-in-untranslated-term-pairs pairs)))
    :flag get-vars-in-untranslated-term-pairs)
  (defthm symbol-listp-of-get-vars-in-pat-untranslated-term-pairs
    (implies (pat-untranslated-term-pairsp pairs)
             (symbol-listp (get-vars-in-pat-untranslated-term-pairs pairs case-match-p)))
    :flag get-vars-in-pat-untranslated-term-pairs)
  (defthm symbol-listp-of-get-vars-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (symbol-listp (get-vars-in-untranslated-term-list terms)))
    :flag get-vars-in-untranslated-term-list))

(defthm-flag-get-vars-in-untranslated-term
  (defthm true-listp-of-get-vars-in-untranslated-term
    (implies (untranslated-termp term)
             (true-listp (get-vars-in-untranslated-term term)))
    :flag get-vars-in-untranslated-term)
  (defthm true-listp-of-get-vars-in-var-untranslated-term-pairs
    (implies (var-untranslated-term-pairsp pairs)
             (true-listp (get-vars-in-var-untranslated-term-pairs pairs)))
    :flag get-vars-in-var-untranslated-term-pairs)
  (defthm true-listp-of-get-vars-in-cadrs-of-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (true-listp (get-vars-in-cadrs-of-untranslated-term-pairs pairs)))
    :flag get-vars-in-cadrs-of-untranslated-term-pairs)
  (defthm true-listp-of-get-vars-in-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (true-listp (get-vars-in-untranslated-term-pairs pairs)))
    :flag get-vars-in-untranslated-term-pairs)
  (defthm true-listp-of-get-vars-in-pat-untranslated-term-pairs
    (implies (pat-untranslated-term-pairsp pairs)
             (true-listp (get-vars-in-pat-untranslated-term-pairs pairs case-match-p)))
    :flag get-vars-in-pat-untranslated-term-pairs)
  (defthm true-listp-of-get-vars-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (true-listp (get-vars-in-untranslated-term-list terms)))
    :flag get-vars-in-untranslated-term-list))

(verify-guards get-vars-in-untranslated-term)

;;;
;;; Get all calls of FN in TERM
;;;

;; Note: This does not handle lets, so vars appearing the the calls returned by
;; this function may not correspond to the free vars in TERM.

(mutual-recursion
 ;; Return a list of all calls in TERM of any of the FNS
 (defun get-calls-in-untranslated-term (term fns)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-listp fns))
                   :verify-guards nil ;done below
                   ))
   (if (atom term)
       nil
     (if (fquotep term)
         nil
       ;;function call or lambda
       (let* ((this-fn (ffn-symb term)))
         (if (member-eq this-fn '(let let*)) ;;(let <bindings> ...declares... <body>)
             (union-equal (get-calls-in-var-untranslated-term-pairs (farg1 term) fns)
                          (get-calls-in-untranslated-term (car (last (fargs term))) fns))
           (if (eq this-fn 'b*)
               (union-equal ;(get-calls-in-cadrs-of-untranslated-term-pairs (farg1 term) fns)
                (get-calls-in-untranslated-term-list (strip-cadrs (farg1 term)) fns)
                (get-calls-in-untranslated-term-list (rest (fargs term)) fns))
             (if (eq 'cond this-fn) ;;(cond <pairs>)
                 (get-calls-in-untranslated-term-pairs (fargs term) fns)
               (if (member-eq this-fn '(case case-match)) ;;(case-match tm <pat-term-pairs>)
                   (union-equal (get-calls-in-untranslated-term (farg1 term) fns)
                                (get-calls-in-pat-untranslated-term-pairs (cdr (fargs term)) fns))
                 (let ((fn-res (if (consp this-fn)
                                   ;;if it's a lambda application, examine the body:
                                   (get-calls-in-untranslated-term (ulambda-body this-fn) fns)
                                 ;;if it's not a lambda:
                                 nil))
                       (res (if (member-eq this-fn fns)
                                (list term)
                              nil)))
                   (union-equal fn-res
                                (union-equal res
                                             (get-calls-in-untranslated-term-list (fargs term) fns))))))))))))

 (defun get-calls-in-var-untranslated-term-pairs (pairs fns)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-listp fns))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(var (first pair))
            (term (second pair)))
       (union-equal (get-calls-in-untranslated-term term fns)
                    (get-calls-in-var-untranslated-term-pairs (rest pairs) fns)))))

 (defun get-calls-in-cadrs-of-untranslated-term-pairs (pairs fns)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (symbol-listp fns))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            ;;(term1 (first pair))
            (term2 (second pair)))
       (union-equal (get-calls-in-untranslated-term term2 fns)
                    (get-calls-in-cadrs-of-untranslated-term-pairs (rest pairs) fns)))))

 (defun get-calls-in-untranslated-term-pairs (pairs fns)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (symbol-listp fns))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (union-equal (union-equal (get-calls-in-untranslated-term term1 fns)
                                 (get-calls-in-untranslated-term term2 fns))
                    (get-calls-in-untranslated-term-pairs (rest pairs) fns)))))

 (defun get-calls-in-pat-untranslated-term-pairs (pairs fns)
   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                               (symbol-listp fns))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term2 (car (last pair))))
       (union-equal (get-calls-in-untranslated-term term2 fns)
                    (get-calls-in-pat-untranslated-term-pairs (rest pairs) fns)))))

 ;;rename all functions calls in TERMS according to
 (defun get-calls-in-untranslated-term-list (terms fns)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-listp fns))))
   (if (endp terms)
       nil
     (union-equal (get-calls-in-untranslated-term (first terms) fns)
                  (get-calls-in-untranslated-term-list (rest terms) fns)))))

(make-flag get-calls-in-untranslated-term)

(defthm-flag-get-calls-in-untranslated-term
  (defthm true-listp-of-get-calls-in-untranslated-term
    (implies (untranslated-termp term)
             (true-listp (get-calls-in-untranslated-term term fns)))
    :flag get-calls-in-untranslated-term)
  (defthm true-listp-of-get-calls-in-var-untranslated-term-pairs
    (implies (var-untranslated-term-pairsp pairs)
             (true-listp (get-calls-in-var-untranslated-term-pairs pairs fns)))
    :flag get-calls-in-var-untranslated-term-pairs)
  (defthm true-listp-of-get-calls-in-cadrs-of-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (true-listp (get-calls-in-cadrs-of-untranslated-term-pairs pairs fns)))
    :flag get-calls-in-cadrs-of-untranslated-term-pairs)
  (defthm true-listp-of-get-calls-in-untranslated-term-pairs
    (implies (untranslated-term-pairsp pairs)
             (true-listp (get-calls-in-untranslated-term-pairs pairs fns)))
    :flag get-calls-in-untranslated-term-pairs)
  (defthm true-listp-of-get-calls-in-pat-untranslated-term-pairs
    (implies (pat-untranslated-term-pairsp pairs)
             (true-listp (get-calls-in-pat-untranslated-term-pairs pairs fns)))
    :flag get-calls-in-pat-untranslated-term-pairs)
  (defthm true-listp-of-get-calls-in-untranslated-term-list
    (implies (untranslated-term-listp terms)
             (true-listp (get-calls-in-untranslated-term-list terms fns)))
    :flag get-calls-in-untranslated-term-list))

(verify-guards get-calls-in-untranslated-term
               :otf-flg t
               :hints (("Goal" :in-theory (enable true-listp-when-symbol-listp-rewrite-unlimited))))

;;;
;;; sublis-var-untranslated-term
;;;


(defthm <=-of-acl2-count-of-car-of-last
  (<= (acl2-count (car (last x)))
      (acl2-count x))
  :rule-classes :linear)

(defund ulet-body (term)
  (declare (xargs :guard (and (untranslated-termp term)
                              (call-of 'let term))))
  ;; skip over the bindings and all the declares
  (car (last (rest (fargs term)))))

(defund ulet-bindings (term)
  (declare (xargs :guard (and (untranslated-termp term)
                              (call-of 'let term))))
  ;; skip over the bindings and all the declares
  (farg1 term))

(defund ulet-declares (term)
  (declare (xargs :guard (and (untranslated-termp term)
                              (call-of 'let term))))
  ;; skip over the bindings get everything but the body
  (butlast (rest (fargs term)) 1))

(defthm <-of-acl2-count-of-ulet-body
  (implies (consp term)
           (< (acl2-count (ulet-body term))
              (acl2-count term)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ulet-body))))

(defthm <-of-acl2-count-of-ulet-bindings
  (implies (consp term)
           (< (acl2-count (ulet-bindings term))
              (acl2-count term)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ulet-bindings))))

(defund all-untranslated-variablep (vars)
;  (declare (xargs :guard t))
  (if (atom vars)
      t
    (and (untranslated-variablep (first vars))
         (all-untranslated-variablep (rest vars)))))

(defthm untranslated-termp-of-ulet-body
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (untranslated-termp (ulet-body term)))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-body))))

(defthm var-untranslated-term-pairsp-of-make-doublets
  (implies (and (all-untranslated-variablep vars)
                (untranslated-term-listp terms))
           (var-untranslated-term-pairsp (make-doublets vars terms)))
  :hints (("Goal" :in-theory (enable make-doublets
                                     all-untranslated-variablep))))

(defthm untranslated-term-listp-of-strip-cadrs-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (untranslated-term-listp (strip-cadrs pairs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm untranslated-term-listp-of-strip-cadrs-of-ulet-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (untranslated-term-listp (strip-cadrs (ulet-bindings term))))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-bindings))))

(defthm all-untranslated-variablep-of-strip-cars-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (all-untranslated-variablep (strip-cars pairs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable ALL-UNTRANSLATED-VARIABLEP))))

(defthm all-untranslated-variablep-of-strip-cars-of-ulet-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (all-untranslated-variablep (strip-cars (ulet-bindings term))))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-bindings))))

(defthm all->=-len-when-var-untranslated-term-pairsp-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (all->=-len pairs 2))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  )

(defthm alistp-when-var-untranslated-term-pairsp-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (alistp pairs))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  )

(defthm symbol-alistp-when-var-untranslated-term-pairsp-cheap
  (implies (var-untranslated-term-pairsp pairs)
           (symbol-alistp pairs))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-alistp)))
  )

(defthm all->=-len-of-ulet-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (all->=-len (ulet-bindings term) 2))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-bindings))))

(defthm alistp-of-ulet-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (alistp (ulet-bindings term)))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-bindings))))

(defthm symbol-alistp-of-ulet-bindings
  (implies (and (untranslated-termp term)
                (call-of 'let term))
           (symbol-alistp (ulet-bindings term)))
  :hints (("Goal" :expand (untranslated-termp term)
           :in-theory (enable ulet-bindings))))

(defthm untranslated-term-listp-of-strip-cdrs-of-remove-assocs-equal
  (implies (untranslated-term-listp (strip-cdrs alist))
           (untranslated-term-listp (strip-cdrs (remove-assocs-equal keys alist))))
  :hints (("Goal" :in-theory (enable remove-assocs-equal))))

(defthm symbol-alistp-of-remove-assocs-equal
  (implies (symbol-alistp alist)
           (symbol-alistp (remove-assocs-equal keys alist)))
  :hints (("Goal" :in-theory (enable remove-assocs-equal symbol-alistp))))

;; It is simpler to replace a variable than a larger term because lambdas are easier to handle.
(mutual-recursion
 (defun sublis-var-untranslated-term (alist term)
   (declare (xargs :guard (and (untranslated-termp term)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))
                   :verify-guards nil
                   :measure (acl2-count term)
                   :hints (("Goal" :do-not-induct t))
                   :ruler-extenders :all))
   (if (untranslated-variablep term)
       (if (assoc-equal term alist)
           (cdr (assoc-equal term alist))
         term)
     (if (atom term)
         term
       (if (fquotep term)
           term
         (let* ((fn (ffn-symb term)))
           (if (eq fn 'let)
               (let* ((bindings (ulet-bindings term))
                      (declares (ulet-declares term))
                      (body (ulet-body term))
                      (vars (strip-cars bindings))
                      (terms (strip-cadrs bindings))
                      ;; Apply the replacement to the terms to which the vars
                      ;; are bound (okay because all bindings happen
                      ;; simultaneously):
                      (new-terms (sublis-var-untranslated-term-list alist terms))
                      ;; Remove any bindings whose vars are shadowed by the let:
                      (alist-for-body (remove-assocs vars alist))
                      (new-body (sublis-var-untranslated-term alist-for-body body)))
                 `(let ,(make-doublets vars new-terms) ,@declares ,new-body))
             (if (eq fn 'let*) ;fffixme
                 (cons fn
                       (cons (sublis-var-var-untranslated-term-pairs alist
                                                                     (farg1 term))
                             (append (butlast (rest (fargs term)) 1)
                                     (cons (sublis-var-untranslated-term alist
                                                                         (car (last (fargs term))))
                                           'nil))))
               (if (eq fn 'b*)
                   (let* ((pairs (farg1 term))
                          (binders (strip-cars pairs))
                          (terms (strip-cadrs pairs)))
                     (cons fn
                           (cons (make-doublets binders
                                                (sublis-var-untranslated-term-list alist terms))
                                 (sublis-var-untranslated-term-list alist
                                                                    (rest (fargs term))))))
                 (if (eq 'cond fn)
                     (cons fn (sublis-var-untranslated-term-pairs alist (fargs term)))
                   (if (member-eq fn '(case case-match))
                       (list* fn (sublis-var-untranslated-term alist (farg1 term))
                              (sublis-var-pat-untranslated-term-pairs alist (cdr (fargs term))
                                                                      (eq 'case-match fn)))
                     (let* ((args (fargs term))
                            (args (sublis-var-untranslated-term-list alist args)))
                       ;;todo: handle lambdas
                       (let* ((term (cons fn args)))
                         term))))))))))))

 (defun sublis-var-var-untranslated-term-pairs (alist pairs)
   (declare (xargs :guard (and (var-untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (var (first pair))
            (term (second pair)))
       (cons (list var
                   (sublis-var-untranslated-term alist term))
             (sublis-var-var-untranslated-term-pairs alist
                                                     (rest pairs))))))

 (defun sublis-var-untranslated-term-pairs (alist pairs)
   (declare (xargs :guard (and (untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (term1 (first pair))
            (term2 (second pair)))
       (cons (list (sublis-var-untranslated-term alist term1)
                   (sublis-var-untranslated-term alist term2))
             (sublis-var-untranslated-term-pairs alist (rest pairs))))))

 (defun sublis-var-pat-untranslated-term-pairs (alist pairs case-match-p)
   (declare (xargs :guard (and (pat-untranslated-term-pairsp pairs)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp pairs)
       nil
     (let* ((pair (first pairs))
            (pat1 (first pair))
            (term2 (car (last pair)))
            (alist-for-body (if case-match-p
                                (remove-assocs (vars-bound-in-case-match-pattern pat1) alist)
                              alist)))
       (cons (list pat1
                   (sublis-var-untranslated-term alist-for-body term2))
             (sublis-var-pat-untranslated-term-pairs alist (rest pairs) case-match-p)))))

 (defun sublis-var-untranslated-term-list
   (alist terms)
   (declare (xargs :guard (and (untranslated-term-listp terms)
                               (symbol-alistp alist)
                               (untranslated-term-listp (strip-cdrs alist)))))
   (if (endp terms)
       nil
     (cons (sublis-var-untranslated-term alist
                                         (first terms))
           (sublis-var-untranslated-term-list alist
                                              (rest terms))))))

(make-flag sublis-var-untranslated-term)

(defthm len-of-sublis-var-untranslated-term-list
  (equal (len (sublis-var-untranslated-term-list alist terms))
         (len terms))
  :hints (("goal" :in-theory (enable len)
           :induct (len terms))))

(defthm consp-of-sublis-var-untranslated-term-list
  (equal (consp (sublis-var-untranslated-term-list alist terms))
         (consp terms))
  :hints (("goal" :expand (sublis-var-untranslated-term-list alist terms))))

(defthm-flag-sublis-var-untranslated-term
  (defthm untranslated-termp-of-sublis-var-untranslated-term
    (implies (and (untranslated-termp term)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-termp (sublis-var-untranslated-term alist term)))
    :flag sublis-var-untranslated-term)
  (defthm var-untranslated-term-pairsp-of-sublis-var-var-untranslated-term-pairs
    (implies (and (var-untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (var-untranslated-term-pairsp (sublis-var-var-untranslated-term-pairs alist pairs)))
    :flag sublis-var-var-untranslated-term-pairs)
  (defthm untranslated-term-pairsp-of-sublis-var-untranslated-term-pairs
    (implies (and (untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-pairsp (sublis-var-untranslated-term-pairs alist pairs)))
    :flag sublis-var-untranslated-term-pairs)
  (defthm untranslated-term-pairsp-of-sublis-var-pat-untranslated-term-pairs
    (implies (and (pat-untranslated-term-pairsp pairs)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (pat-untranslated-term-pairsp (sublis-var-pat-untranslated-term-pairs alist pairs case-match-p)))
    :flag sublis-var-pat-untranslated-term-pairs)
  (defthm untranslated-term-listp-of-sublis-var-untranslated-term-list
    (implies (and (untranslated-term-listp terms)
                  (alistp alist)
                  (untranslated-term-listp (strip-cdrs alist)))
             (untranslated-term-listp (sublis-var-untranslated-term-list alist terms)))
    :flag sublis-var-untranslated-term-list)
  :hints (("goal" :in-theory (enable untranslated-lambda-exprp)
           :expand ((sublis-var-untranslated-term term alist)
                    (untranslated-termp (list* 'b*
                                               (make-doublets (strip-cars (cadr term))
                                                           (sublis-var-untranslated-term-list alist
                                                                                              (strip-cadrs (cadr term))))
                                               (sublis-var-untranslated-term-list alist
                                                                                  (cddr term))))))))
(verify-guards sublis-var-untranslated-term
  :hints (("goal" :in-theory (e/d (untranslated-lambda-exprp consp-when-len-known)
                                  (untranslated-termp untranslated-term-listp
                                                      untranslated-term-listp-of-sublis-var-untranslated-term-list))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :use ((:instance untranslated-term-listp-of-sublis-var-untranslated-term-list
                            (terms (cdr term))))
           :expand ((untranslated-term-listp (sublis-var-untranslated-term-list alist
                                                                                (cdr term)))
                    (untranslated-termp term)
                    (untranslated-termp (car (sublis-var-untranslated-term-list alist
                                                                                (cdr term)))))))
  :otf-flg t)

(defthm alist-when-untranslated-term-pairsp-cheap
  (implies (untranslated-term-pairsp x)
           (alistp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm all->=-len-when-untranslated-term-pairsp-cheap
  (implies (untranslated-term-pairsp x)
           (all->=-len x 2))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm untranslated-term-listp-of-strip-cadrs
  (implies (untranslated-term-pairsp x)
           (untranslated-term-listp (strip-cadrs x))))

;; ;todo: just say farg 2
;; (defthm
;;  (implies (untranslated-lambda-exprp x)
;;           (untranslated-termp (car (last (fargs x)))))
;;  :hints (("Goal" :expand ((untranslated-lambda-exprp x))
;;           :in-theory (enable untranslated-lambda-exprp untranslated-termp))))

(in-theory (disable consp-of-cdr-of-car-when-untranslated-termp
                    cdr-of-car-when-untranslated-termp
                    true-listp-of-car-when-untranslated-termp
                    consp-of-cddr-of-car-when-untranslated-termp
                    untranslated-term-listp-of-cdr-2)) ;bad rules
