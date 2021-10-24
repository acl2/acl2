; Syntheto Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "functions")

(include-book "system/pseudo-event-formp" :dir :system)
(include-book "kestrel/utilities/declares1" :dir :system)
(include-book "tools/remove-hyps" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is (a start towards) shallowly embedded Syntheto theorems,
; i.e. event macros corresponding to those Syntheto constructs,
; which will generate and submit the appropriate ACL2 events
; that correspond to the Syntheto function specifications.
; Please feel free to improve this file,
; and to add your name to the file header.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn a typed variable into a term usable as a hypothesis in a theorem.
; The term applies the predicate for the type to the variable.
; This is more general than theorems.

(define s-typed-var-to-hyp-term (tvar) ; element of result of d-->s-typed-vars
  :returns (term pseudo-termp)
  :verify-guards nil
  (b* ((namestring (first tvar))
       (type (second tvar))
       (name (intern-syndef namestring))
       (pred (type-name-to-pred (s-type-to-fty-name-symbol type))))
    `(force (,pred ,name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lift the previous function to lists, homomorphically.

(define s-typed-vars-to-hyp-terms (tvars) ; result of d-->s-typed-vars
  :returns (terms pseudo-term-listp)
  :verify-guards nil
  (cond ((endp tvars) nil)
        (t (cons (s-typed-var-to-hyp-term (car tvars))
                 (s-typed-vars-to-hyp-terms (cdr tvars))))))

(define extract-subst-from-conjs (conjs)
  :returns (mv r (sbst eqlable-alistp))
  (if (atom conjs)
      (mv () ())
    (b* (((cons conj tl-conjs) conjs)
         ((mv r-conjs r-sbst)
          (extract-subst-from-conjs tl-conjs)))
      (case-match conj
        (('equal v e)
         (if (symbolp v)
             (mv r-conjs (cons (cons v e) r-sbst))
           (mv (cons conj r-conjs) r-sbst)))
        (& (mv (cons conj r-conjs) r-sbst))))))

(define get-conds-head (formula-term)
  (case-match formula-term
    (('implies condn head)
     (b* ((conjs (acl2::get-conjuncts-of-untranslated-term condn))
          ((mv conjs sbst)
           (extract-subst-from-conjs conjs)))
       (mv (sublis sbst conjs) (sublis sbst head))))
    (& (mv nil formula-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Function that realizes the functionality of the macro below.
; As a very crude initial strategy, we generate proof hints
; that enable all the functions in the term;
; that is, we say "try and prove this using all the definitions".
; This might actually work well for many theorems,
; but we'll want to use a more elaborate strategy,
; and in any case inevitably support user-defined hints.

(define s-theorem-fn (namestring ; string
                      variables ; result of d-->s-typed-vars
                      formula) ; result of d-->s-expr
  :returns (event pseudo-event-formp)
  :verify-guards nil
  (b* ((name (intern-syndef namestring))
       (hyps (s-typed-vars-to-hyp-terms variables))
       (formula-term (translate-term formula))
       (enable-fns (relevant-fn-names formula-term))
       ((mv conds head-term)
        (get-conds-head formula-term)))
    `(with-output :off :all :on error :gag-mode t
       (progn (local (include-book "kestrel/lists-light/len" :dir :system))
              (acl2::remove-hyps
               (defthm ,name
                 (implies (and ,@conds ,@hyps)
                          ,head-term)
                 :hints (("Goal" :in-theory (enable ,@enable-fns)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Macro for shallowly embedded Syntheto theorems.

(defmacro s-theorem (namestring variables formula)
  `(make-event (s-theorem-fn ',namestring ',variables ',formula)))
