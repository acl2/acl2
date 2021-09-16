; Renaming variables in terms
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "bound-vars-in-term")
(include-book "sublis-var-simple")
(include-book "no-duplicate-lambda-formals-in-termp")
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(defthm symbolp-of-cdr-of-assoc-equal-when-symbol-listp-of-strip-cdrs
  (implies (symbol-listp (strip-cdrs alist))
           (symbolp (cdr (assoc-equal key alist)))))

(defund var-renamingp (renaming)
  (declare (xargs :guard t))
  (and (symbol-alistp renaming)
       (symbol-listp (strip-cdrs renaming))
       ;; must be injective (can't map 2 different vars to the same var):
       (no-duplicatesp (strip-cdrs renaming))))

(local
 (defthm symbol-alistp-when-var-renamingp
   (implies (var-renamingp renaming)
            (symbol-alistp renaming))
   :hints (("Goal" :in-theory (enable var-renamingp)))))

(local
 (defthm true-listp-of-strip-cdrs-when-var-renamingp
   (implies (var-renamingp renaming)
            (true-listp (strip-cdrs renaming)))
   :hints (("Goal" :in-theory (enable var-renamingp)))))

(local
 (defthm symbol-listp-of-strip-cdrs-when-var-renamingp
   (implies (var-renamingp renaming)
            (symbol-listp (strip-cdrs renaming)))
   :hints (("Goal" :in-theory (enable var-renamingp)))))

(defthm var-renamingp-forward-to-symbol-alistp
  (implies (var-renamingp renaming)
           (symbol-alistp renaming))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable var-renamingp))))

(defund any-var-is-renamed-to (target-var vars renaming)
  (declare (xargs :guard (and (symbolp target-var)
                              (symbol-listp vars)
                              (var-renamingp renaming))))
  (if (endp vars)
      nil
    (let* ((var (first vars))
           (res (assoc-eq var renaming)))
      (if (and res (eq target-var (cdr res)))
          t
        (any-var-is-renamed-to target-var (rest vars) renaming)))))

;; The case that can lead to clashes is when a formal is renamed to something
;; that is already a formal and that formal is not being renamed.  (Two formals
;; that get renamed can't clash because the renaming is injective.  Two formals
;; that don't get renamed can't clash because lamdba formals are all
;; different.)  In the clashing case, the 'winner' is the formal being renamed
;; by renaming.  A new name has to be chosen for the other formal.
(defund make-renaming-for-lambda (lambda-formals all-lambda-formals renaming vars-to-avoid)
  (declare (xargs :guard (and (symbol-listp lambda-formals)
                              (symbol-listp all-lambda-formals)
                              (var-renamingp renaming)
                              (symbol-listp vars-to-avoid))))
  (if (endp lambda-formals)
      nil
    (let* ((formal (first lambda-formals))
           (res (assoc-eq formal renaming)))
      (if res
          ;; this formal is getting renamed (any clash with it will be handled
          ;; when we process the formal that it clashes with that isn't being
          ;; renamed):
          (acons formal
                 (cdr res)
                 (make-renaming-for-lambda (rest lambda-formals) all-lambda-formals renaming vars-to-avoid))
        ;; this formal is not getting renamed:
        (if (any-var-is-renamed-to formal all-lambda-formals renaming)
            ;; clash:
            (let* ((rec (make-renaming-for-lambda (rest lambda-formals) all-lambda-formals renaming vars-to-avoid))
                   (vars-to-avoid (append vars-to-avoid ;todo: optimize
                                          all-lambda-formals
                                          (strip-cdrs renaming)
                                          (strip-cdrs rec)))
                   (fresh-name (fresh-var-name formal 2 vars-to-avoid)))
              (acons formal fresh-name rec))
          ;; no clash and no renaming (don't even bother to add an entry):
          (make-renaming-for-lambda (rest lambda-formals) all-lambda-formals renaming vars-to-avoid))))))

;; Any formal in the renaming gets that name in the result of make-renaming-for-lambda
(defthm subsetp-equal-of-make-renaming-for-lambda
  (implies (and (member-equal formal lambda-formals)
                (assoc-equal formal renaming)
                (symbol-listp lambda-formals)
                (symbol-listp all-lambda-formals)
                (var-renamingp renaming)
                (symbol-listp vars-to-avoid))
           (equal (cdr (assoc-equal formal (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid)))
                  (cdr (assoc-equal formal renaming))))
  :hints (("Goal" :in-theory (enable var-renamingp make-renaming-for-lambda)
           :do-not '(generalize eliminate-destructors)
           :induct (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid))))

;;Vars in vars-to-avoid are correctly avoided.
;; (defthm not-member-equal-of-strip-cdrs-of-make-renaming-for-lambda
;;   (implies (and (member-equal var vars-to-avoid)
;;                 (symbol-listp lambda-formals)
;;                 (symbol-listp all-lambda-formals)
;;                 (var-renamingp renaming)
;;                 (symbol-listp vars-to-avoid))
;;            (not (member-equal var (strip-cdrs (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid)))))
;;   :hints (("Goal" :in-theory (enable var-renamingp)
;;            :do-not '(generalize eliminate-destructors)
;;            :induct (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid))))

(defthm not-equal-of-cdr-of-assoc-equal-when-not-member-equal-of-strip-cdrs
  (IMPLIES (AND (NOT (MEMBER-EQUAL val (strip-cdrs alist)))
                (ASSOC-EQUAL KEY alist))
           (NOT (EQUAL val (CDR (ASSOC-EQUAL KEY alist)))))
  :hints (("Goal" :in-theory (enable STRIP-CDRS assoc-equal))))

(defthm equal-of-cdr-of-assoc-equal-and-cdr-of-assoc-equal-when-NO-DUPLICATESP-EQUAL-of-strip-cdrs
  (implies (and (NO-DUPLICATESP-EQUAL (STRIP-CDRS RENAMING))
                (ASSOC-EQUAL key1 RENAMING)
                (ASSOC-EQUAL key2 RENAMING))
           (equal (EQUAL (CDR (ASSOC-EQUAL key1 RENAMING))
                         (CDR (ASSOC-EQUAL key2 RENAMING)))
                  (equal key1 key2)))
  :hints (("Goal" :in-theory (enable STRIP-CDRS assoc-equal))))

(defthm not-member-equal-of-cdr-of-assoc-equal-of-strip-cdrs-of-make-renaming-for-lambda
  (implies (and (assoc-equal var renaming)
                (not (member-equal var lambda-formals))
                (no-duplicatesp-equal (strip-cdrs renaming)))
           (not (member-equal
                 (cdr (assoc-equal var renaming))
                 (strip-cdrs (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid)))))
  :hints (("Goal" :in-theory (enable make-renaming-for-lambda))))

(defthm var-renamingp-of-make-renaming-for-lambda
  (implies (and (symbol-listp lambda-formals)
                (symbol-listp all-lambda-formals)
                (no-duplicatesp-equal lambda-formals)
                (var-renamingp renaming)
                (symbol-listp vars-to-avoid))
           (var-renamingp (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid)))
  :hints (("Goal" :in-theory (enable var-renamingp make-renaming-for-lambda)
           :do-not '(generalize eliminate-destructors)
           :induct (make-renaming-for-lambda lambda-formals all-lambda-formals renaming vars-to-avoid))))

(mutual-recursion
 ;; Apply SUBST to TERM and rename any lambda vars according to RENAMING.
 (defund rename-vars-in-term (subst term renaming)
   (declare (xargs :guard (and (var-renamingp subst)
                               (pseudo-termp term)
                               (no-duplicate-lambda-formals-in-termp term)
                               (var-renamingp renaming))
                   :guard-hints (("Goal" :in-theory (enable PSEUDO-TERMP
                                                            ;var-renamingp
                                                            )
                                  :expand (PSEUDO-TERMP TERM)
                                  ))))
   (if (variablep term)
       (let ((res (assoc-eq term subst)))
         (if res (cdr res) term))
     (let ((fn (ffn-symb term)))
       (if (eq fn 'quote)
           term
         (let ((new-args (rename-vars-in-terms subst (fargs term) renaming)))
           (if (not (consp fn))
               ;; non-lambda case:
               (cons fn new-args)
             ;; lambda case (we've already fixed up the args, so technically we
             ;; could leave the lambda, but we go ahead and try to apply the
             ;; renaming to it):
             (let* ((lambda-formals (lambda-formals fn))
                    (lambda-body (lambda-body fn))
                    ;; don't rename any formals to vars already in scope or vars used deeper in the body (just to avoid confusion and extra work):
                    (vars-to-avoid (append (strip-cdrs subst)
                                           (bound-vars-in-term lambda-body)))
                    (lambda-formal-renaming (make-renaming-for-lambda lambda-formals lambda-formals renaming vars-to-avoid))
                    (new-lambda-formals (sublis-var-simple-lst lambda-formal-renaming lambda-formals))
                    ;; apply the lambda-formal-renaming to the body, passing the same desired global RENAMING for deeper lambda vars:
                    (new-lambda-body (rename-vars-in-term lambda-formal-renaming lambda-body renaming)))
               (cons `(lambda ,new-lambda-formals ,new-lambda-body)
                     new-args))))))))

 (defund rename-vars-in-terms (subst terms renaming)
   (declare (xargs :guard (and (var-renamingp subst)
                               (pseudo-term-listp terms)
                               (no-duplicate-lambda-formals-in-termsp terms)
                               (var-renamingp renaming))))
   (if (endp terms)
       nil
     (cons (rename-vars-in-term subst (first terms) renaming)
           (rename-vars-in-terms subst (rest terms) renaming)))))

(defthm len-of-rename-vars-in-terms
  (equal (len (rename-vars-in-terms subst terms renaming))
         (len terms))
  :hints (("Goal" :in-theory (enable rename-vars-in-terms))))

(make-flag rename-vars-in-term)

(defthm pseudo-termp-when-symbolp
  (implies (symbolp term)
           (pseudo-termp term)))

(defthm-flag-rename-vars-in-term
  (defthm pseudo-termp-of-rename-vars-in-term
    (implies (and (var-renamingp subst)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (var-renamingp renaming))
             (pseudo-termp (rename-vars-in-term subst term renaming)))
    :flag rename-vars-in-term)
  (defthm pseudo-termp-of-rename-vars-in-terms
    (implies (and (var-renamingp subst)
                  (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (var-renamingp renaming))
             (pseudo-term-listp (rename-vars-in-terms subst terms renaming)))
    :flag rename-vars-in-terms)
  :hints (("Goal" :in-theory (enable rename-vars-in-term
                                     rename-vars-in-terms
                                     pseudo-termp-when-symbolp))))
