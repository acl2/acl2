; Proofs about substitute-constants-in-lambdas.lisp
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Clean up this file

(include-book "substitute-constants-in-lambdas")
(include-book "lambdas-closed-in-termp")
(include-book "no-nils-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(local (include-book "empty-eval-helpers"))
(local (include-book "helpers"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))

(local (in-theory (e/d (;handle-constant-lambda-formals
                        )
                       (quote-listp
                        myquotep
                        mv-nth))))

;clash
(local
  (defthm myquotep-of-cdr-of-assoc-equal
    (implies (and (myquote-listp (strip-cdrs alist))
                  (assoc-equal key alist))
             (myquotep (cdr (assoc-equal key alist))))
    :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs)))))

(local
  (defthm myquotep-of-lookup-equal-when-myquote-listp-of-strip-cdrs
    (implies (and (myquote-listp (strip-cdrs alist))
                  (assoc-equal key alist))
             (myquotep (lookup-equal key alist)))
    :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs)))))

(local
  (defthm not-member-equal-of-mv-nth-0-of-handle-constant-lambda-formals
    (implies (not (member-equal formal formals))
             (not (member-equal formal (mv-nth 0 (handle-constant-lambda-formals formals args)))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm no-duplicatesp-equal-of-mv-nth-0-of-handle-constant-lambda-formals
    (implies (no-duplicatesp-equal formals)
             (no-duplicatesp-equal (mv-nth 0 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm no-nils-in-termsp-of-mv-nth-1-of-handle-constant-lambda-formals
    (implies (and (no-nils-in-termsp args)
                  (equal (len formals) (len args)))
             (no-nils-in-termsp (mv-nth 1 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm lambdas-closed-in-termsp-of-mv-nth-1-of-handle-constant-lambda-formals
    (implies (and (lambdas-closed-in-termsp args)
                  (equal (len formals) (len args)))
             (lambdas-closed-in-termsp (mv-nth 1 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm no-duplicate-lambda-formals-in-termsp-of-mv-nth-1-of-handle-constant-lambda-formals
    (implies (and (no-duplicate-lambda-formals-in-termsp args)
                  (equal (len formals) (len args)))
             (no-duplicate-lambda-formals-in-termsp (mv-nth 1 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

;; (local
;;   (defthm subsetp-equal-of-free-vars-in-terms-of-mv-nth-1-of-handle-constant-lambda-formals
;;     (implies (and; (no-nils-in-termsp args)
;;                   (equal (len formals) (len args)))
;;              (subsetp-equal (free-vars-in-terms (mv-nth 1 (handle-constant-lambda-formals formals args)))
;;                             (free-vars-in-terms args)))
;;     :hints (("Goal" :in-theory (enable free-vars-in-terms)))))

;move
(local
  (defthm no-nils-in-termp-when-myquotep
    (implies (myquotep term)
             (no-nils-in-termp term))
    :hints (("Goal" :in-theory (enable no-nils-in-termp)))))

(local
  (defthm-flag-substitute-constants-in-lambdas-aux
    (defthm no-nils-in-termp-of-substitute-constants-in-lambdas-aux
      (implies (and (no-nils-in-termp term)
                    (myquote-listp (strip-cdrs alist))
                    (pseudo-termp term))
               (no-nils-in-termp (substitute-constants-in-lambdas-aux term alist)))
      :flag substitute-constants-in-lambdas-aux)
    (defthm no-nils-in-termsp-of-substitute-constants-in-lambdas-aux-lst
      (implies (and (no-nils-in-termsp terms)
                    (myquote-listp (strip-cdrs alist))
                    (pseudo-term-listp terms))
               (no-nils-in-termsp (substitute-constants-in-lambdas-aux-lst terms alist)))
      :flag substitute-constants-in-lambdas-aux-lst)
    :hints (("Goal" ;:expand (PSEUDO-TERMP TERM)
             :do-not '(generalize eliminate-destructors)
             :expand   (no-nils-in-termp (cons (car term) (substitute-constants-in-lambdas-aux-lst (cdr term) alist)))
             :in-theory (e/d (substitute-constants-in-lambdas-aux
                              substitute-constants-in-lambdas-aux-lst
                              ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
                              ;; make-lambda-terms-simple
                              ;; ;;make-lambda-term-simple
;                            true-listp-when-symbol-alistp
                              no-nils-in-termp)
                             (;; pairlis$
                              ;; set-difference-equal
                              ))))))

;;adds the A argument
(local
  (mutual-recursion
    (defund induct-substitute-constants-in-lambdas-aux (term alist a)
      (declare (irrelevant a))
      (if (variablep term)
          (let ((res (assoc-eq term alist)))
            (if res
                (cdr res) ; put in the constant for this var
              term))
        (let ((fn (ffn-symb term)))
          (if (eq 'quote fn)
              term
            ;; function call or lambda:
            (let ((new-args (induct-substitute-constants-in-lambdas-aux-lst (fargs term) alist a)))
              (if (consp fn)
                  ;; it's a lambda:
                  (let ((formals (lambda-formals fn))
                        (body (lambda-body fn)))
                    (mv-let (remaining-formals remaining-args var-constant-alist)
                      (handle-constant-lambda-formals formals new-args)
                      ;; Since the lambda is closed, we completely replace the
                      ;; alist passed in when processing the lambda-body:
                      (let ((new-body (induct-substitute-constants-in-lambdas-aux body var-constant-alist (pairlis$ (lambda-formals fn) (empty-eval-list new-args a)))))
                        (if (equal remaining-formals remaining-args)
                            ;; avoid trivial lambda:
                            new-body
                          (cons-with-hint (make-lambda-with-hint remaining-formals new-body fn) remaining-args term)))))
                ;; not a lambda:
                (cons-with-hint fn new-args term)))))))
    (defund induct-substitute-constants-in-lambdas-aux-lst (terms alist a)
      (declare (irrelevant a))
      (if (endp terms)
          nil
        (cons-with-hint (induct-substitute-constants-in-lambdas-aux (first terms) alist a)
                        (induct-substitute-constants-in-lambdas-aux-lst (rest terms) alist a)
                        terms)))))

(local (make-flag induct-substitute-constants-in-lambdas-aux))

;; The -induct functions are equal to the regular functions
(local
 (defthm-flag-induct-substitute-constants-in-lambdas-aux
   (defthm substitute-constants-in-lambdas-aux-induct-removal
     (equal (induct-substitute-constants-in-lambdas-aux term alist a)
            (substitute-constants-in-lambdas-aux term alist))
     :flag induct-substitute-constants-in-lambdas-aux)
   (defthm substitute-constants-in-lambdas-aux-induct-lst-removal
     (equal (induct-substitute-constants-in-lambdas-aux-lst terms alist a)
            (substitute-constants-in-lambdas-aux-lst terms alist))
     :flag induct-substitute-constants-in-lambdas-aux-lst)
   :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas-aux
                                      substitute-constants-in-lambdas-aux-lst
                                      induct-substitute-constants-in-lambdas-aux
                                      induct-substitute-constants-in-lambdas-aux-lst)))))



;move
(defthm empty-eval-when-myquotep
  (implies (myquotep x)
           (equal (empty-eval x a) (cadr x))))

(defthm assoc-equal-of-pairlis$-iff
  (iff (assoc-equal key (pairlis$ keys vals))
       (member-equal key keys)))

(defthm not-assoc-equal-when-not-member-equal-of-strip-cars
  (implies (not (member-equal key (strip-cars alist)))
           (not (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm cdr-of-assoc-equal-of-pairlis$-of-unquote-list
  (equal (cdr (assoc-equal key (pairlis$ keys (unquote-list vals))))
         (unquote (cdr (assoc-equal key (pairlis$ keys vals)))))
  :hints (("Goal" :in-theory (enable unquote-list))))

(defthm pairlis$-of-strip-cars-and-strip-cdrs
  (implies (alistp alist)
           (equal (pairlis$ (strip-cars alist)
                            (strip-cdrs alist))
                  alist)))

(defthm len-of-mv-nth-0-of-handle-constant-lambda-formals-linear
  (<= (len (mv-nth 0 (handle-constant-lambda-formals formals args)))
      (len formals))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable handle-constant-lambda-formals))))

;(local (include-book "kestrel/lists-light/cdr" :dir :system)) ; looped
(local (include-book "kestrel/lists-light/len" :dir :system))

(local
  (defthm mv-nth-2-of-handle-constant-lambda-formals-when-no-constants
    (implies (equal (mv-nth 0 (handle-constant-lambda-formals formals args)) formals)
             (equal (mv-nth 2 (handle-constant-lambda-formals formals args))
                    nil))
    :hints (("subgoal *1/2" :use len-of-mv-nth-0-of-handle-constant-lambda-formals-linear)
            ("Goal" :in-theory (e/d (handle-constant-lambda-formals)
                                    (consp-of-cdr-when-len-known ;loop
                                     true-listp
                                     ))))))

(local
  (defthm mv-nth-1-of-handle-constant-lambda-formals-when-no-constants
    (implies (and (equal (mv-nth 0 (handle-constant-lambda-formals formals args)) formals)
                  (equal (len args) (len formals))
                  (true-listp args))
             (equal (mv-nth 1 (handle-constant-lambda-formals formals args))
                    args))
    :hints (("subgoal *1/2" :use len-of-mv-nth-0-of-handle-constant-lambda-formals-linear)
            ("Goal" :in-theory (e/d (handle-constant-lambda-formals)
                                    (consp-of-cdr-when-len-known ;loop
                                     true-listp))))))

(local
  (defthm equal-of-lookup-equal-and-lookup-equal-special
    (implies (and (member-equal key (strip-cars a1))
                  (alists-equiv-on (strip-cars a1) a1 a2))
             (equal (equal (lookup-equal key a1) (lookup-equal key a2))
                    t))
    :hints (("Goal" :in-theory (enable alists-equiv-on lookup-equal strip-cars)))))

(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(local
  (defthm quotep-when-myquotep
    (implies (myquotep x)
             (quotep x))))

(local
  (defthm subsetp-equal-of-mv-nth-1-of-handle-constant-lambda-formals-return-type
    (implies (and (symbol-listp formals)
                  (pseudo-term-listp args)
                  (equal (len formals) (len args)))
             (subsetp-equal (mv-nth 1 (handle-constant-lambda-formals formals args))
                            args))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(defthm subsetp-equal-of-free-vars-in-terms-and-free-vars-in-terms
  (implies (subsetp-equal x y)
           (subsetp-equal (free-vars-in-terms x) (free-vars-in-terms y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(local
  (defthm free-vars-in-terms-of-mv-nth-1-of-handle-constant-lambda-formals
    (implies (equal (len formals) (len args))
             (equal (free-vars-in-terms (mv-nth 1 (handle-constant-lambda-formals formals args)))
                    (free-vars-in-terms args)))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm alistp-of-mv-nth-2-of-handle-constant-lambda-formals
    (alistp (mv-nth 2 (handle-constant-lambda-formals formals args)))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local (include-book "kestrel/lists-light/remove-equal" :dir :system))

(local
  (defthmd strip-cars-of-mv-nth-2-of-handle-constant-lambda-formals
    (implies (no-duplicatesp-equal formals)
             (equal (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args)))
                    (set-difference-equal formals
                                          (mv-nth 0 (handle-constant-lambda-formals formals args)))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals set-difference-equal)))))


;; (defthm-flag-substitute-constants-in-lambdas-aux
;;   (defthm free-vars-in-term-of-substitute-constants-in-lambdas-aux
;;     (implies (and (pseudo-termp term)
;;                   (myquote-listp (strip-cdrs alist))
;;                   (no-duplicate-lambda-formals-in-termp term)
;;                   (alistp alist))
;;              (equal (free-vars-in-term (substitute-constants-in-lambdas-aux term alist))
;;                     (set-difference-equal (free-vars-in-term term)
;;                                           (strip-cars alist))))
;;     :flag substitute-constants-in-lambdas-aux)
;;   (defthm free-vars-in-terms-of-substitute-constants-in-lambdas-aux-lst
;;     (implies (and (pseudo-term-listp terms)
;;                   (myquote-listp (strip-cdrs alist))
;;                   (no-duplicate-lambda-formals-in-termsp terms)
;;                   (alistp alist))
;;              (equal (free-vars-in-terms (substitute-constants-in-lambdas-aux-lst terms alist))
;;                     (set-difference-equal (free-vars-in-terms terms)
;;                                           (strip-cars alist))))
;;     :flag substitute-constants-in-lambdas-aux-lst)
;;   :hints (("Goal"
;;            :expand (free-vars-in-term term)
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (substitute-constants-in-lambdas-aux
;;                             substitute-constants-in-lambdas-aux-lst
;;                             ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
;;                             ;; make-lambda-terms-simple
;;                             ;; ;;make-lambda-term-simple
;;                             ;;true-listp-when-symbol-alistp
;;                             free-vars-in-terms
;;                             free-vars-in-term-when-quotep
;;                             member-equal-of-strip-cars-iff)
;;                            (;; pairlis$
;;                             ;; set-difference-equal
;;                             )))))


;; (defthm-flag-substitute-constants-in-lambdas-aux
;;   (defthm free-vars-in-term-of-substitute-constants-in-lambdas-aux
;;     (implies (and (pseudo-termp term)
;;                   (myquote-listp (strip-cdrs alist))
;;                   (no-duplicate-lambda-formals-in-termp term))
;;              (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas-aux term alist))
;;                             (free-vars-in-term term)))
;;     :flag substitute-constants-in-lambdas-aux)
;;   (defthm free-vars-in-terms-of-substitute-constants-in-lambdas-aux-lst
;;     (implies (and (pseudo-term-listp terms)
;;                   (myquote-listp (strip-cdrs alist))
;;                   (no-duplicate-lambda-formals-in-termsp terms))
;;              (subsetp-equal (free-vars-in-terms (substitute-constants-in-lambdas-aux-lst terms alist))
;;                             (free-vars-in-terms terms)))
;;     :flag substitute-constants-in-lambdas-aux-lst)
;;   :hints (("Goal"
;;            :expand (free-vars-in-term term)
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (substitute-constants-in-lambdas-aux
;;                             substitute-constants-in-lambdas-aux-lst
;;                             ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
;;                             ;; make-lambda-terms-simple
;;                             ;; ;;make-lambda-term-simple
;;                             ;;true-listp-when-symbol-alistp
;;                             free-vars-in-terms
;;                             free-vars-in-term-when-quotep)
;;                            (;; pairlis$
;;                             ;; set-difference-equal
;;                             )))))

(defthm member-equal-of-car-and-free-vars-in-terms
  (implies (not (consp (car args)))
           (iff (member-equal (car args) (free-vars-in-terms args))
                (consp args))))

(local
  (defthm subsetp-equal-helper-when-all-formals-are-constants-or-trivial
    (implies (and (equal (mv-nth 0 (handle-constant-lambda-formals formals args))
                         (mv-nth 1 (handle-constant-lambda-formals formals args)))
                  (equal (len args) (len formals))
                  (symbol-listp formals)
                  )
             (subsetp-equal (set-difference-equal formals (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))
                            (free-vars-in-terms args)))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals set-difference-equal free-vars-in-terms)))))

(local
  (defthm subsetp-equal-helper-when-all-formals-are-constants-or-trivial-2-gen
    (implies (and (subsetp-equal vars formals) ; e.g., vars is the vars in the lambda body
                  (equal (mv-nth 0 (handle-constant-lambda-formals formals args))
                         (mv-nth 1 (handle-constant-lambda-formals formals args)))
                  (equal (len args) (len formals))
                  (symbol-listp formals)
                  )
             (subsetp-equal (set-difference-equal vars (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))
                            (free-vars-in-terms args)))
    :hints (("Goal" :use subsetp-equal-helper-when-all-formals-are-constants-or-trivial
             :in-theory (disable subsetp-equal-helper-when-all-formals-are-constants-or-trivial)))))

(local
  (defthm-flag-substitute-constants-in-lambdas-aux
    (defthm free-vars-in-term-of-substitute-constants-in-lambdas-aux
      (implies (and (pseudo-termp term)
                    (lambdas-closed-in-termp term)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termp term)
                    (alistp alist))
               (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas-aux term alist))
                              (set-difference-equal (free-vars-in-term term)
                                                    (strip-cars alist))))
      :flag substitute-constants-in-lambdas-aux)
    (defthm free-vars-in-terms-of-substitute-constants-in-lambdas-aux-lst
      (implies (and (pseudo-term-listp terms)
                    (lambdas-closed-in-termsp terms)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termsp terms)
                    (alistp alist))
               (subsetp-equal (free-vars-in-terms (substitute-constants-in-lambdas-aux-lst terms alist))
                              (set-difference-equal (free-vars-in-terms terms)
                                                    (strip-cars alist))))
      :flag substitute-constants-in-lambdas-aux-lst)
    :hints (("subgoal *1/2" :cases ((subsetp-equal (set-difference-equal (free-vars-in-term (caddr (car term)))
                                                                         (strip-cars (mv-nth 2
                                                                                             (handle-constant-lambda-formals (cadr (car term))
                                                                                                                             (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                                       alist)))))
                                                   (free-vars-in-terms (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                 alist)))))
            ("Goal"
             :expand (free-vars-in-term term)
             :do-not '(generalize eliminate-destructors)
             :in-theory (e/d (substitute-constants-in-lambdas-aux
                              substitute-constants-in-lambdas-aux-lst
                              ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
                              ;; make-lambda-terms-simple
                              ;; ;;make-lambda-term-simple
                              ;;true-listp-when-symbol-alistp
                              free-vars-in-terms
                              free-vars-in-term-when-quotep
                              member-equal-of-strip-cars-iff
                              lambdas-closed-in-termp)
                             (;; pairlis$
                              ;; set-difference-equal
                              ))))))

;; (defthm free-vars-in-term-of-substitute-constants-in-lambdas-aux-gen
;;   (implies (and (subsetp-equal (free-vars-in-term term) x)
;;                 (pseudo-termp term)
;;                 (myquote-listp (strip-cdrs alist))
;;                 (no-duplicate-lambda-formals-in-termp term)
;;                 (alistp alist) ; could drop
;;                 )
;;            (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas-aux term alist))
;;                           x))
;;   :hints (("Goal" :use free-vars-in-term-of-substitute-constants-in-lambdas-aux
;;            :in-theory (disable free-vars-in-term-of-substitute-constants-in-lambdas-aux))))

(local
  (defthm free-vars-in-term-of-substitute-constants-in-lambdas-aux-gen
    (implies (and (subsetp-equal (set-difference-equal (free-vars-in-term term)
                                                       (strip-cars alist))
                                 x)
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (myquote-listp (strip-cdrs alist))
                  (no-duplicate-lambda-formals-in-termp term)
                  (alistp alist) ; could drop
                  )
             (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas-aux term alist))
                            x))
    :hints (("Goal" :use free-vars-in-term-of-substitute-constants-in-lambdas-aux
             :in-theory (disable free-vars-in-term-of-substitute-constants-in-lambdas-aux)))))

(local
  (defthm not-consp-of-free-vars-in-term-of-substitute-constants-in-lambdas-aux
    (implies (and (not (consp (free-vars-in-term term)))
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (myquote-listp (strip-cdrs alist))
                  (no-duplicate-lambda-formals-in-termp term)
                  (alistp alist) ; could drop
                  )
             (not (consp (free-vars-in-term (substitute-constants-in-lambdas-aux term alist)))))
    :hints (("Goal" :use free-vars-in-term-of-substitute-constants-in-lambdas-aux
             :in-theory (disable free-vars-in-term-of-substitute-constants-in-lambdas-aux
                                 free-vars-in-term-of-substitute-constants-in-lambdas-aux-gen)))))

;; (thm
;;   (implies (not (consp (free-vars-in-term term)))
;;            (equal (empty-eval term alist)
;;                   (empty-eval term nil))))


(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(defthm empty-eval-when-empty-eval-list-of-cdr-ignores-the-alist
  (implies (and (syntaxp (not (equal a *nil*)))
                (equal (empty-eval-list (cdr x) a)
                       (empty-eval-list (cdr x) nil))
                (consp x) ; drop?
                )
           (equal (empty-eval x a)
                  (empty-eval x nil)))
  :hints (("Goal" :use ((:instance empty-eval-of-fncall-args
                                   (a nil))
                        (:instance empty-eval-of-fncall-args
                                   (a a))))))

(defthm-flag-free-vars-in-term
  (defthm empty-eval-when-not-consp-of-free-vars
    (implies (and (syntaxp (not (equal a *nil*)))
                  (not (consp (free-vars-in-term term))))
             (equal (empty-eval term a)
                    (empty-eval term nil)))
    :flag free-vars-in-term)
  (defthm empty-eval-list-when-not-consp-of-free-vars
    (implies (and (syntaxp (not (equal a *nil*)))
                  (not (consp (free-vars-in-terms terms))))
             (equal (empty-eval-list terms a)
                    (empty-eval-list terms nil)))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (e/d (free-vars-in-term
                                   free-vars-in-terms
                                   ;empty-eval-of-fncall-args
                                   )
                                  (;empty-eval-of-fncall-args-back
                                   )))))

(local
  (defthm not-member-equal-of-mv-nth-2-of-handle-constant-lambda-formals
    (implies (not (member-equal formal formals))
             (not (member-equal formal (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm lookup-equal-of-pairlis$-of-mv-nth-0-of-handle-constant-lambda-formals-and-mv-nth-1-of-handle-constant-lambda-formals
    (implies (and ;(member-equal var (mv-nth 0 (handle-constant-lambda-formals formals args)))
               (no-duplicatesp-equal formals))
             (equal (lookup-equal var (pairlis$ (mv-nth 0 (handle-constant-lambda-formals formals args))
                                                (mv-nth 1 (handle-constant-lambda-formals formals args))))
                    (if (member-equal var (mv-nth 0 (handle-constant-lambda-formals formals args)))
                        (lookup-equal var (pairlis$ formals args))
                      nil)))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(defthm lookup-equal-of-pairlis$-of-unquote-list
  (equal (lookup-equal b (pairlis$ formals (unquote-list args)))
         (unquote (lookup-equal b (pairlis$ formals args))))
  :hints (("Goal" :in-theory (enable pairlis$ unquote-list))))

(local
  (defthm helper
    (implies (and (member-equal formal (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))
                  (no-duplicatesp-equal formals))
             (equal (lookup-equal formal (pairlis$ formals args))
                    (lookup-equal formal (mv-nth 2 (handle-constant-lambda-formals formals args)))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm myquotep-of-lookup-equal-of-mv-nth-2-of-handle-constant-lambda-formals
    (implies (and (no-duplicatesp-equal formals)
                  (pseudo-term-listp args))
             (equal (myquotep (lookup-equal key (mv-nth 2 (handle-constant-lambda-formals formals args))))
                    (if (member-equal key (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))
                        t
                      nil)))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm helper3
    (implies (and (member-equal formal formals)
                  (no-duplicatesp-equal formals))
             (iff (member-equal formal (strip-cars (mv-nth 2 (handle-constant-lambda-formals formals args))))
                  (not (member-equal formal (mv-nth 0 (handle-constant-lambda-formals formals args))))))
    :hints (("Goal" :in-theory (enable handle-constant-lambda-formals)))))

(local
  (defthm helper4
    (implies (and (subsetp-equal vars formals)
                  (no-duplicatesp-equal formals))
             (subsetp-equal (set-difference-equal vars (strip-cars (mv-nth '2 (handle-constant-lambda-formals formals args))))
                            (mv-nth '0 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :in-theory (enable subsetp-equal handle-constant-lambda-formals set-difference-equal)))))

(defthm lambdas-closed-in-termsp-when-myquote-listp
  (implies (myquote-listp terms)
           (lambdas-closed-in-termsp terms)))

(local
  (defthm lambdas-closed-in-termp-of-substitute-constants-in-lambdas-aux-helper
    (implies (and (subsetp-equal (free-vars-in-term body) formals)
                  (no-duplicatesp formals)
                  (lambdas-closed-in-termp body)
                  (pseudo-termp body)
                  (symbol-listp formals)
                  (pseudo-term-listp args)
                  (equal (len formals) (len args))
                  (no-duplicate-lambda-formals-in-termp body))
             (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas-aux body (mv-nth 2 (handle-constant-lambda-formals formals args))))
                            (mv-nth 0 (handle-constant-lambda-formals formals args))))
    :hints (("Goal" :use (:instance free-vars-in-term-of-substitute-constants-in-lambdas-aux (term body)
                                    (alist (mv-nth 2 (handle-constant-lambda-formals formals args))))))))

;move up
(local
  (defthm-flag-substitute-constants-in-lambdas-aux
    (defthm lambdas-closed-in-termp-of-substitute-constants-in-lambdas-aux
      (implies (and (lambdas-closed-in-termp term)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termp term)
                    (pseudo-termp term))
               (lambdas-closed-in-termp (substitute-constants-in-lambdas-aux term alist)))
      :flag substitute-constants-in-lambdas-aux)
    (defthm lambdas-closed-in-termsp-of-substitute-constants-in-lambdas-aux-lst
      (implies (and (lambdas-closed-in-termsp terms)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termsp terms)
                    (pseudo-term-listp terms))
               (lambdas-closed-in-termsp (substitute-constants-in-lambdas-aux-lst terms alist)))
      :flag substitute-constants-in-lambdas-aux-lst)
    :hints (("Goal" ;:expand (PSEUDO-TERMP TERM)
             :do-not '(generalize eliminate-destructors)
             :expand   (lambdas-closed-in-termp (cons (car term) (substitute-constants-in-lambdas-aux-lst (cdr term) alist)))
             :in-theory (e/d (substitute-constants-in-lambdas-aux
                              substitute-constants-in-lambdas-aux-lst
                              ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
                              ;; make-lambda-terms-simple
                              ;; ;;make-lambda-term-simple
;                            true-listp-when-symbol-alistp
                              lambdas-closed-in-termp
                              )
                             (;; pairlis$
                              ;; set-difference-equal
                              ))))))

(defthm no-duplicate-lambda-formals-in-termsp-when-myquote-listp
  (implies (myquote-listp terms)
           (no-duplicate-lambda-formals-in-termsp terms))
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termsp no-duplicate-lambda-formals-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-cdr-of-assoc-equal
  (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist))
           (no-duplicate-lambda-formals-in-termp (cdr (assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;move up
(local
  (defthm-flag-substitute-constants-in-lambdas-aux
    (defthm no-duplicate-lambda-formals-in-termp-of-substitute-constants-in-lambdas-aux
      (implies (and (no-duplicate-lambda-formals-in-termp term)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termp term)
                    (pseudo-termp term))
               (no-duplicate-lambda-formals-in-termp (substitute-constants-in-lambdas-aux term alist)))
      :flag substitute-constants-in-lambdas-aux)
    (defthm no-duplicate-lambda-formals-in-termsp-of-substitute-constants-in-lambdas-aux-lst
      (implies (and (no-duplicate-lambda-formals-in-termsp terms)
                    (myquote-listp (strip-cdrs alist))
                    (no-duplicate-lambda-formals-in-termsp terms)
                    (pseudo-term-listp terms))
               (no-duplicate-lambda-formals-in-termsp (substitute-constants-in-lambdas-aux-lst terms alist)))
      :flag substitute-constants-in-lambdas-aux-lst)
    :hints (("Goal" ;:expand (PSEUDO-TERMP TERM)
             :do-not '(generalize eliminate-destructors)
             :expand   (no-duplicate-lambda-formals-in-termp (cons (car term) (substitute-constants-in-lambdas-aux-lst (cdr term) alist)))
             :in-theory (e/d (substitute-constants-in-lambdas-aux
                              substitute-constants-in-lambdas-aux-lst
                              ;; MEMBER-EQUAL-OF-STRIP-CARS-IFF
                              ;; make-lambda-terms-simple
                              ;; ;;make-lambda-term-simple
;                            true-listp-when-symbol-alistp
                              no-duplicate-lambda-formals-in-termp
                              )
                             (;; pairlis$
                              ;; set-difference-equal
                              ))))))

(local
  (defthm trivial-formal-helper
    (implies (and (member-equal formal (mv-nth 0 (handle-constant-lambda-formals formals args)))
                  (equal (mv-nth 0 (handle-constant-lambda-formals formals args))
                         (mv-nth 1 (handle-constant-lambda-formals formals args)))
                  (equal (len args) (len formals))
                  (symbol-listp formals)
                  (no-duplicatesp-equal formals))
             (equal (lookup-equal formal (pairlis$ formals args))
                    formal))
    :hints (("Goal" :use subsetp-equal-helper-when-all-formals-are-constants-or-trivial
             :in-theory (e/d (handle-constant-lambda-formals) (subsetp-equal-helper-when-all-formals-are-constants-or-trivial))))))


;; Correctness theorem helper
(local
  (defthm-flag-induct-substitute-constants-in-lambdas-aux
    (defthm substitute-constants-in-lambdas-aux-correct
      (implies (and (pseudo-termp term)
                    (no-nils-in-termp term)
                    (no-duplicate-lambda-formals-in-termp term)
                    (lambdas-closed-in-termp term)
                    (myquote-listp (strip-cdrs alist))
                    (alistp alist))
               (equal (empty-eval (substitute-constants-in-lambdas-aux term alist) a)
                      (empty-eval term (append (pairlis$ (strip-cars alist) (unquote-list (strip-cdrs alist)))
                                               a))))
      :flag induct-substitute-constants-in-lambdas-aux)
    (defthm substitute-constants-in-lambdas-aux-lst-correct
      (implies (and (pseudo-term-listp terms)
                    (no-nils-in-termsp terms)
                    (no-duplicate-lambda-formals-in-termsp terms)
                    (lambdas-closed-in-termsp terms)
                    (myquote-listp (strip-cdrs alist))
                    (alistp alist))
               (equal (empty-eval-list (substitute-constants-in-lambdas-aux-lst terms alist) a)
                      (empty-eval-list terms (append (pairlis$ (strip-cars alist) (unquote-list (strip-cdrs alist)))
                                                     a))))
      :flag induct-substitute-constants-in-lambdas-aux-lst)
    :hints (;; ("subgoal *1/3"
            ;;  :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
            ;;                  (term  (caddr (car term)))
            ;;                  (alist1 (pairlis$ (cadr (car term))
            ;;                                    (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
            ;;                                                                                               alist)
            ;;                                                     a)))
            ;;                  (alist2 (append (pairlis$ (strip-cars (mv-nth 2
            ;;                                                                (handle-constant-lambda-formals (cadr (car term))
            ;;                                                                                                (substitute-constants-in-lambdas-aux-lst (cdr term)
            ;;                                                                                                                                          alist))))
            ;;                                            (unquote-list (strip-cdrs (mv-nth 2
            ;;                                                                              (handle-constant-lambda-formals (cadr (car term))
            ;;                                                                                                              (substitute-constants-in-lambdas-aux-lst (cdr term)
            ;;                                                                                                                                                        alist))))))
            ;;                                  (pairlis$ (cadr (car term))
            ;;                                            (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
            ;;                                                                                                       alist)
            ;;                                                             a))))))
            ("subgoal *1/3"
             :use ((:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
                              (term (substitute-constants-in-lambdas-aux (caddr (car term))
                                                                          (mv-nth 2
                                                                                  (handle-constant-lambda-formals (cadr (car term))
                                                                                                                  (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                            alist)))))
                              (alist1 (pairlis$ (cadr (car term))
                                                (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                           alist)
                                                                 a)))
                              (alist2 (pairlis$ (mv-nth 0
                                                        (handle-constant-lambda-formals (cadr (car term))
                                                                                        (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                  alist)))
                                                (empty-eval-list (mv-nth 1
                                                                         (handle-constant-lambda-formals (cadr (car term))
                                                                                                         (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                   alist)))
                                                                 a))))
                   (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
                              (term  (caddr (car term)))
                              (alist1 (pairlis$ (cadr (car term))
                                                (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                           alist)
                                                                 a)))
                              (alist2 (append (pairlis$ (strip-cars (mv-nth 2
                                                                            (handle-constant-lambda-formals (cadr (car term))
                                                                                                            (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                      alist))))
                                                        (unquote-list (strip-cdrs (mv-nth 2
                                                                                          (handle-constant-lambda-formals (cadr (car term))
                                                                                                                          (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                                    alist))))))
                                              (pairlis$ (cadr (car term))
                                                        (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                   alist)
                                                                         a)))))))
            ("subgoal *1/2"
             :use ((:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
                              (term  (caddr (car term)))
                              (alist1 (pairlis$ (cadr (car term))
                                                (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                           alist)
                                                                 a)))
                              (alist2 (append (pairlis$ (strip-cars (mv-nth 2
                                                                            (handle-constant-lambda-formals (cadr (car term))
                                                                                                            (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                      alist))))
                                                        (unquote-list (strip-cdrs (mv-nth 2
                                                                                          (handle-constant-lambda-formals (cadr (car term))
                                                                                                                          (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                                    alist))))))
                                              (pairlis$ (cadr (car term))
                                                        (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                   alist)
                                                                         a)))))
                   (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
                              (term (substitute-constants-in-lambdas-aux (caddr (car term))
                                                                          (mv-nth 2
                                                                                  (handle-constant-lambda-formals (cadr (car term))
                                                                                                                  (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                                                                            alist)))))
                              (alist1 a)
                              (alist2 (pairlis$ (cadr (car term))
                                                (empty-eval-list (substitute-constants-in-lambdas-aux-lst (cdr term)
                                                                                                           alist)
                                                                 a)))))
             )
            ("Goal" :do-not '(generalize eliminate-destructors)
;           :expand (substitute-constants-in-lambdas-aux term alist)
             :in-theory (e/d (substitute-constants-in-lambdas-aux
                              substitute-constants-in-lambdas-aux-lst
                              empty-eval-of-fncall-args
;true-listp-when-symbol-alistp
;                              no-duplicate-lambda-formals-in-termp
;                              no-duplicate-lambda-formals-in-termsp
                              map-lookup-equal-of-pairlis$-of-empty-eval-list
                              alistp-when-symbol-alistp
                              alists-equiv-on-when-agree-on-bad-guy
                              lookup-equal-of-append
                              lookup-equal-of-pairlis$-of-empty-eval-list
                              lambdas-closed-in-termp
                              cdr-of-assoc-equal-becomes-lookup-equal ;lookup-equal
                              no-nils-in-termp
                              )
                             (empty-eval-of-fncall-args-back
                              empty-eval-list-of-map-lookup-equal-of-pairlis$
                              equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special
                              empty-eval-of-lookup-equal-of-pairlis$))))))


;; Correctness theorem for substitute-constants-in-lambdas
(defthm substitute-constants-in-lambdas-correct
  (implies (and (pseudo-termp term)
                (no-nils-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (lambdas-closed-in-termp term))
           (equal (empty-eval (substitute-constants-in-lambdas term) alist)
                  (empty-eval term alist)))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))

(defthm pseudo-termp-of-substitute-constants-in-lambdas
  (implies (pseudo-termp term)
           (pseudo-termp (substitute-constants-in-lambdas term)))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))

(defthm no-nils-in-termp-of-substitute-constants-in-lambdas
  (implies (and (no-nils-in-termp term)
                (pseudo-termp term))
           (no-nils-in-termp (substitute-constants-in-lambdas term)))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))

(defthm no-duplicate-lambda-formals-in-termp-of-substitute-constants-in-lambdas
  (implies (and (no-duplicate-lambda-formals-in-termp term)
                (pseudo-termp term))
           (no-duplicate-lambda-formals-in-termp (substitute-constants-in-lambdas term)))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))

(defthm lambdas-closed-in-termp-of-substitute-constants-in-lambdas
  (implies (and (lambdas-closed-in-termp term)
                (no-duplicate-lambda-formals-in-termp term)
                (pseudo-termp term))
           (lambdas-closed-in-termp (substitute-constants-in-lambdas term)))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))

(defthm free-vars-in-term-of-substitute-constants-in-lambdas-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-duplicate-lambda-formals-in-termp term))
           (subsetp-equal (free-vars-in-term (substitute-constants-in-lambdas term))
                          x))
  :hints (("Goal" :in-theory (enable substitute-constants-in-lambdas))))
