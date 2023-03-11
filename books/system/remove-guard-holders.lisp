; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book was renamed from file remove-guard-holders-strong-3.lsp in late
; January, 2023 and also significantly expanded from that file.

; This book contains progress towards converting ACL2 source function
; remove-guard-holders from :program mode to guard-verified :logic mode.  (Note
; that :logic mode ACL2 source functions must be guard-verified.)  See the book
; remove-guard-holders-future.lisp for additional work, extending the present
; book, towards that task, especially if you are interested in making
; additional such progress.

; The theorems we export are only those that seem safe, in that including this
; book seems unlikely to mess with proofs.  That basically limits the exported
; theorems to :forward-chaining rules and rewrite rules hung on a function
; symbol explicitly addressed by this book; for example,
; weak-splo-extracts-tuple-listp-append is non-local since it is hung on
; weak-splo-extracts-tuple-listp.

; Perhaps it would make sense to eliminate weak-badge-userfn-structure-alistp
; in favor of the new badge-userfn-structure-alistp -- but existing books would
; then need to be modified, notably
; books/system/remove-guard-holders1.lisp and
; books/system/remove-guard-holders-weak.lisp.

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "remove-guard-holders1")
(include-book "remove-guard-holders-weak")
(include-book "termp")
(include-book "subst-var")
(include-book "subcor-var")

(verify-termination flatten-ands-in-lit-lst) ; and guards
(verify-termination translate-declaration-to-guard/integer-gen) ; and guards
(verify-termination subst-each-for-var) ; and guards
(verify-termination possibly-dirty-lambda-objectp1) ; and guards
(verify-termination translate-declaration-to-guard1-gen) ; and guards
(verify-termination translate-declaration-to-guard-gen) ; and guards
(verify-termination subst-each-for-var) ; and guards

(local (in-theory (disable remove-guard-holders-weak)))

; This is needed for (verify-termination executable-badge ...).
(defthm
  badge-userfn-structure-alistp-implies-weak-badge-userfn-structure-alistp
  (implies (badge-userfn-structure-alistp x)
           (weak-badge-userfn-structure-alistp x))
  :rule-classes :forward-chaining)

#+acl2-devel ; avoid error for redundant def. with raw Lisp code
(verify-termination ilks-plist-worldp) ; and guards

(defthm ilks-plist-worldp-forward-to-plist-worldp
  (implies (ilks-plist-worldp w)
           (plist-worldp w))
  :rule-classes :forward-chaining)

(defthm ilks-plist-worldp-forward-to-alistp-for-badge-userfn-structure
  (implies
   (ilks-plist-worldp wrld)
   (and (alistp (fgetprop 'badge-table 'table-alist nil wrld))
        (alistp (cdr (assoc-equal :badge-userfn-structure
                                  (fgetprop 'badge-table 'table-alist nil
                                            wrld))))))
  :rule-classes :forward-chaining)

(local
 (defthm weak-badge-userfn-structure-alistp-implies-consp-cdr-assoc-equal
   (implies (and (weak-badge-userfn-structure-alistp alist)
                 (cdr (assoc-equal fn alist)))
            (consp (cdr (assoc-equal fn alist))))))

(defthm weak-badge-userfn-structure-alistp-forward-to-alistp
  (implies (weak-badge-userfn-structure-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining)

(local
 (defthm consp-assoc-equal-forced
   (implies (and (force (alistp l))
                 (assoc-equal name l))
            (consp (assoc-equal name l)))))

(local
 (defthm weak-badge-userfn-structure-alistp-implies-consp-cddr-assoc-equal
   (implies (and (weak-badge-userfn-structure-alistp alist)
                 (cddr (assoc-equal fn alist)))
            (consp (cddr (assoc-equal fn alist))))))

(verify-termination executable-badge ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

(local
 (defthm executable-tamep-1
; bpf is *badge-prim-falist* value
   (implies (and (apply$-badge-alistp-ilks-t bpf)
                 (cdr (hons-assoc-equal fn bpf)))
            (consp (cdr (hons-assoc-equal fn bpf))))))

(local
 (defthm executable-tamep-2
; bpf is *badge-prim-falist* value
   (implies (and (apply$-badge-alistp-ilks-t bpf)
                 (cddr (hons-assoc-equal fn bpf)))
            (consp (cddr (hons-assoc-equal fn bpf))))))

(local
 (defthm executable-tamep-3
; bpf is *badge-prim-falist* value
   (implies (and (apply$-badge-alistp-ilks-t bpf)
                 (cdddr (hons-assoc-equal fn bpf)))
            (consp (cdddr (hons-assoc-equal fn bpf))))))

(local
 (defthm executable-tamep-4
   (implies (and (weak-badge-userfn-structure-alistp alist)
                 (caddr (assoc-equal fn alist)))
            (consp (caddr (assoc-equal fn alist))))))

(local
 (defthm executable-tamep-5
   (implies (and (weak-badge-userfn-structure-alistp alist)
                 (cdr (caddr (assoc-equal fn alist))))
            (consp (cdr (caddr (assoc-equal fn alist)))))))

(local
 (defthm executable-tamep-6
   (implies (and (weak-badge-userfn-structure-alistp alist)
                 (cddr (caddr (assoc-equal fn alist))))
            (consp (cddr (caddr (assoc-equal fn alist)))))))

(local
 (defthm executable-tamep-7-8
; bpf is *badge-prim-falist* value
   (implies (and (apply$-badge-alistp-ilks-t bpf)
                 (cdr (hons-assoc-equal fn bpf)))
            (natp (caddr (hons-assoc-equal fn bpf))))
   :rule-classes :type-prescription))

(local
 (defthm executable-tamep-8
; bpf is *badge-prim-falist* value
   (implies (and (apply$-badge-alistp-ilks-t bpf)
                 (hons-assoc-equal fn bpf))
            (equal (cddddr (hons-assoc-equal fn bpf))
                   t))))

(local
 (defthm executable-tamep-9
   (implies (and (badge-userfn-structure-alistp alist)
                 (caddr (assoc-equal fn alist)))
            (natp (cadr (caddr (assoc-equal fn alist)))))
   :rule-classes :type-prescription))

(local
 (defthm executable-tamep-10
   (implies (and (badge-userfn-structure-alistp alist)
                 (not (equal (cdddr (caddr (assoc-equal fn alist)))
                             t)))
            (true-listp (cdddr (caddr (assoc-equal fn alist)))))))

(verify-termination executable-tamep ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

(verify-termination weak-splo-extracts-tuple-listp) ; and guards

(verify-termination well-formed-lambda-objectp1
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

; Now working towards verify-termination for
; syntactically-plausible-lambda-objectp.

(verify-termination translate-declaration-to-guard1-gen)

(verify-termination translate-declaration-to-guard-gen)

(local
 (defthm symbol-listp-implies-pseudo-term-listp
   (implies (symbol-listp x)
            (pseudo-term-listp x))))

(local
 (make-flag flag-translate-declaration-to-guard-gen
            translate-declaration-to-guard-gen))

(local
 (defthm-flag-translate-declaration-to-guard-gen
   (defthm pseudo-termp-translate-declaration-to-guard-gen
     (implies (and (pseudo-termp var)
                   (equal tflg t))
              (pseudo-termp
               (translate-declaration-to-guard-gen x var tflg wrld)))
     :flag translate-declaration-to-guard-gen)
   (defthm pseudo-term-listp-translate-declaration-to-guard-gen
     (implies (and (pseudo-termp var)
                   (equal tflg t))
              (pseudo-term-listp
               (translate-declaration-to-guard-gen-lst l var tflg wrld)))
     :flag translate-declaration-to-guard-gen-lst)))

(verify-termination type-expressions-from-type-spec)

(verify-termination syntactically-plausible-lambda-objectp1)

(local
 (defthm syntactically-plausible-lambda-objectp-termination-lemma-1
   (< (acl2-count
       (mv-nth 5
               (syntactically-plausible-lambda-objectp1
                edcls formals ignores ignorables type-exprs satisfies-exprs
                guard)))
      (+ 5
         (acl2-count edcls)
         (acl2-count formals)
         (acl2-count guard)))
   :rule-classes :linear))

; Copied exactly (11/18/2015 and 01/23/2023) from ACL2 source file axioms.lisp,
; towards guard verification for make-lambda-application:
(local
 (encapsulate
  ()

; We wish to prove symbol-listp-all-vars1, below, so that we can verify the
; guards on all-vars1.  But it is in a mutually recursive clique.  Our strategy
; is simple: (1) define the flagged version of the clique, (2) prove that it is
; equal to the given pair of official functions, (3) prove that it has the
; desired property and (4) then obtain the desired property of the official
; function by instantiation of the theorem proved in step 3, using the theorem
; proved in step 2 to rewrite the flagged flagged calls in that instance to the
; official ones.

; Note: It would probably be better to make all-vars1/all-vars1-lst local,
; since it's really not of any interest outside the guard verification of
; all-vars1.  However, since we are passing through this file more than once,
; that does not seem to be an option.

  (local
   (defun all-vars1/all-vars1-lst (flg lst ans)
     (if (eq flg 'all-vars1)
         (cond ((variablep lst) (add-to-set-eq lst ans))
               ((fquotep lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst) ans)))
         (cond ((endp lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst)
                                           (all-vars1/all-vars1-lst 'all-vars1 (car lst) ans)))))))

  (local
   (defthm step-1-lemma
     (equal (all-vars1/all-vars1-lst flg lst ans)
            (if (equal flg 'all-vars1) (all-vars1 lst ans) (all-vars1-lst lst ans)))))

  (local
   (defthm step-2-lemma
     (implies (and (symbol-listp ans)
                   (if (equal flg 'all-vars1)
                       (pseudo-termp lst)
                       (pseudo-term-listp lst)))
              (symbol-listp (all-vars1/all-vars1-lst flg lst ans)))))

  (defthm symbol-listp-all-vars1
    (implies (and (symbol-listp ans)
                  (pseudo-termp lst))
             (symbol-listp (all-vars1 lst ans)))
    :hints (("Goal" :use (:instance step-2-lemma (flg 'all-vars1)))))))

(local
 (defthm arglistp1-implies-symbol-listp
   (implies (arglistp1 x)
            (symbol-listp x))
   :hints (("Goal" :in-theory (enable arglistp1)))))

(local
 (defthm pseudo-term-listp-revappend
   (implies (true-listp x)
            (equal (pseudo-term-listp (revappend x y))
                   (and (pseudo-term-listp x)
                        (pseudo-term-listp y))))))

(set-induction-depth-limit 1)

(local
 (defthm member-symbol-listp-forward-to-symbolp
   (implies (and (member-equal a x)
                 (symbol-listp x))
            (symbolp a))
   :rule-classes :forward-chaining))

; The following gives us pseudo-termp-subst-var.
(include-book "system/subst-var" :dir :system)

(local
 (defthm pseudo-term-listp-subst-each-for-var
   (implies (and (pseudo-term-listp new-lst)
                 (variablep old)
                 (pseudo-termp term))
            (pseudo-term-listp (subst-each-for-var new-lst old term)))))

(local
 (defthm subset-symbol-listp-forward-to-symbol-listp
   (implies (and (subsetp-equal x y)
                 (true-listp x)
                 (symbol-listp y))
            (symbol-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm pseudo-term-listp-mv-nth-3-syntactically-plausible-lambda-objectp1
   (implies
    (and (car (syntactically-plausible-lambda-objectp1
               edcls formals ignores ignorables type-exprs satisfies-exprs
               guard))
         (symbol-listp formals)
         (pseudo-term-listp type-exprs))
    (pseudo-term-listp
     (mv-nth 3
             (syntactically-plausible-lambda-objectp1
              edcls formals ignores ignorables type-exprs satisfies-exprs
              guard))))))

(local
 (defthm symbol-listp-set-difference-equal
   (implies (symbol-listp x)
            (symbol-listp (set-difference-equal x y)))))

(local
 (encapsulate
   ()

   (local (defthm symbol-listp-revappend-lemma
            (implies (not (symbol-listp y))
                     (not (symbol-listp (revappend x y))))))

   (defthm symbol-listp-revappend
     (implies (true-listp x)
              (equal (symbol-listp (revappend x y))
                     (and (symbol-listp x)
                          (symbol-listp y)))))))

(local
 (defthm true-listp-mv-nth-1-syntactically-plausible-lambda-objectp1
   (implies
    (and (car (syntactically-plausible-lambda-objectp1
               edcls formals ignores ignorables type-exprs satisfies-exprs
               guard))
         (symbol-listp ignores)
         (symbol-listp formals))
    (true-listp
     (mv-nth 1
             (syntactically-plausible-lambda-objectp1
              edcls formals ignores ignorables type-exprs satisfies-exprs
              guard))))))

(local
 (defthm true-listp-mv-nth-2-syntactically-plausible-lambda-objectp1
   (implies
    (and (car (syntactically-plausible-lambda-objectp1
               edcls formals ignores ignorables type-exprs satisfies-exprs
               guard))
         (symbol-listp ignorables)
         (symbol-listp formals))
    (true-listp
     (mv-nth 2
             (syntactically-plausible-lambda-objectp1
              edcls formals ignores ignorables type-exprs satisfies-exprs
              guard))))))

(defthm arglistp-forward-to-symbol-listp
  (implies (arglistp x)
           (symbol-listp x ))
  :rule-classes :forward-chaining)

(verify-termination syntactically-plausible-lambda-objectp
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

; Start towards verify-termination for clean-up-dirty-lambda-objects.

(verify-termination expand-all-lambdas)

(local
 (make-flag flag-expand-all-lambdas
            expand-all-lambdas
            :flag-mapping ((expand-all-lambdas term)
                           (expand-all-lambdas-lst terms))))

(local
 (defthm len-expand-all-lambdas-lst
   (equal (len (expand-all-lambdas-lst terms))
          (len terms))))

(local
 (defthm pseudo-termp-forward-to-pseudo-term-listp-cdr
   (implies (and (pseudo-termp x)
                 (consp x)
                 (consp (car x)))
            (pseudo-term-listp (cdr x)))
   :rule-classes :forward-chaining))

(local
 (defthm-flag-expand-all-lambdas
   (defthm type-of-pseudo-termp
     (implies (pseudo-termp term)
              (pseudo-termp (expand-all-lambdas term)))
     :flag term)
   (defthm pseudo-term-listp-expand-all-lambdas-lst
     (implies (pseudo-term-listp terms)
              (pseudo-term-listp (expand-all-lambdas-lst terms)))
     :flag terms)))

(verify-guards expand-all-lambdas)

; Start verify-termination for warrants-for-tamep

(verify-termination find-warrant-function-name)

(verify-termination warrants-for-tamep
  (declare (xargs :verify-guards nil)))

(local
 (make-flag flag-warrants-for-tamep
            warrants-for-tamep
            :flag-mapping ((warrants-for-tamep term)
                           (warrants-for-tamep-functionp fn)
                           (warrants-for-suitably-tamep-listp lst))))

(local
 (defthm-flag-warrants-for-tamep
   (defthm true-listp-car-warrants-for-tamep
     (implies (and (ilks-plist-worldp wrld)
                   (executable-tamep x wrld)
                   (true-listp warrants))
              (true-listp (car (warrants-for-tamep
                                x wrld warrants unwarranteds))))
     :flag term)
   (defthm true-listp-car-warrants-for-tamep-functionp
     (implies (and (ilks-plist-worldp wrld)
                   (executable-tamep-functionp fn wrld)
                   (true-listp warrants))
              (true-listp (car (warrants-for-tamep-functionp
                                fn wrld warrants unwarranteds))))
     :flag fn)
   (defthm true-listp-car-warrants-for-warrants-for-suitably-tamep-listp
     (implies (and (ilks-plist-worldp wrld)
                   (executable-suitably-tamep-listp flags args wrld)
                   (true-listp warrants))
              (true-listp (car (warrants-for-suitably-tamep-listp
                                flags args wrld warrants unwarranteds))))
     :flag lst)))

(local
 (defthm-flag-warrants-for-tamep
   (defthm symbol-listp-mv-nth-1-warrants-for-tamep
     (implies (and (ilks-plist-worldp wrld)
                   (executable-tamep x wrld)
                   (symbol-listp unwarranteds))
              (symbol-listp (mv-nth 1 (warrants-for-tamep
                                       x wrld warrants unwarranteds))))
     :flag term)
   (defthm symbol-listp-mv-nth-1-warrants-for-tamep-functionp
     (implies (and (ilks-plist-worldp wrld)
                   (executable-tamep-functionp fn wrld)
                   (symbol-listp unwarranteds))
              (symbol-listp (mv-nth 1 (warrants-for-tamep-functionp
                                       fn wrld warrants unwarranteds))))
     :flag fn)
   (defthm symbol-listp-mv-nth-1-warrants-for-warrants-for-suitably-tamep-listp
     (implies (and (ilks-plist-worldp wrld)
                   (executable-suitably-tamep-listp flags args wrld)
                   (symbol-listp unwarranteds))
              (symbol-listp (mv-nth 1 (warrants-for-suitably-tamep-listp
                                       flags args wrld warrants unwarranteds))))
     :flag lst)))

(verify-guards warrants-for-tamep)

(verify-termination weak-splo-extracts-tuple-listp) ; and guards

; The following doesn't seem to be needed, but it's probably harmless.
(defthm weak-splo-extracts-tuple-listp-forward-to-true-listp
  (implies (weak-splo-extracts-tuple-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm weak-splo-extracts-tuple-listp-append
  (implies (true-listp x)
           (equal (weak-splo-extracts-tuple-listp (append x y))
                  (and (weak-splo-extracts-tuple-listp x)
                       (weak-splo-extracts-tuple-listp y)))))

(verify-termination type-expressions-from-type-spec)

(verify-termination syntactically-plausible-lambda-objectp1
  (declare (xargs :verify-guards nil)))

(verify-termination syntactically-plausible-lambda-objectp
  (declare (xargs :verify-guards nil)))

(local
 (make-flag flag-syntactically-plausible-lambda-objectp
            syntactically-plausible-lambda-objectp
            :flag-mapping
            ((syntactically-plausible-lambda-objectp main)
             (syntactically-plausible-lambda-objectsp-within within)
             (syntactically-plausible-lambda-objectsp-within-lst listp))))

(local
 (defthm-flag-syntactically-plausible-lambda-objectp
   (defthm weak-splo-extracts-tuple-listp-1
     (implies (syntactically-plausible-lambda-objectp gflg x)
              (weak-splo-extracts-tuple-listp
               (syntactically-plausible-lambda-objectp gflg x)))
     :flag main)
   (defthm weak-splo-extracts-tuple-listp-2
     (let ((ans (syntactically-plausible-lambda-objectsp-within gflg body)))
       (implies ans
                (or (weak-splo-extracts-tuple-listp ans)
                    (equal ans t))))
     :rule-classes nil
     :flag within)
   (defthm weak-splo-extracts-tuple-listp-3
     (let ((ans (syntactically-plausible-lambda-objectsp-within-lst gflg args)))
       (implies ans
                (or (weak-splo-extracts-tuple-listp ans)
                    (equal ans t))))
     :rule-classes nil
     :flag listp)))

(defthm weak-splo-extracts-tuple-listp-of-syntactically-plausible-lambda-objectp
  (implies
   (syntactically-plausible-lambda-objectp nil x)
   (weak-splo-extracts-tuple-listp
    (syntactically-plausible-lambda-objectp nil x))))

(verify-termination well-formed-lambda-objectp)

(verify-termination possibly-dirty-lambda-objectp)
(verify-guards possibly-dirty-lambda-objectp)

; The following events go through, but it will take some work to remove the
; skip-proofs; see system/remove-guard-holders-future.lisp.  Please do not
; convert to logic mode here without also verifying guards, since that could
; slow down the system.

; (skip-proofs (verify-termination clean-up-dirty-lambda-objects))
; (skip-proofs (verify-termination may-contain-dirty-lambda-objectsp))
; (verify-termination possibly-clean-up-dirty-lambda-objects)
; (skip-proofs (verify-guards possibly-clean-up-dirty-lambda-objects))
; (verify-termination remove-guard-holders)

