(in-package "ACL2")

(include-book "substitute-unnecessary-lambda-vars") ;drop?
(include-book "substitute-lambda-formals")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(local (in-theory (disable mv-nth)))

(local (in-theory (disable strip-cdrs
                           strip-cars
                           symbol-alistp)))

(defthm pseudo-termp-of-lookup-equal
  (implies (pseudo-term-listp (strip-cdrs formal-arg-alist))
           (pseudo-termp (lookup-equal var formal-arg-alist)))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs))))

(defthm pseudo-term-listp-of-map-lookup-equal
  (implies (pseudo-term-listp (strip-cdrs formal-arg-alist))
           (pseudo-term-listp (map-lookup-equal vars formal-arg-alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal strip-cdrs))))

(defthm intersection-equal-of-union-equal-arg2-iff
  (iff (intersection-equal x (union-equal y z))
       (or (intersection-equal x y)
           (intersection-equal x z)))
  :hints (("Goal" :in-theory (enable union-equal intersection-equal))))

(defthm subsetp-equal-of-set-difference-equal-and-set-difference-equal
  (implies (and (subsetp-equal x1 x2)
                (subsetp-equal z y))
           (subsetp-equal (set-difference-equal x1 y) (set-difference-equal x2 z)))
  :hints (("Goal" :in-theory (enable subsetp-equal set-difference-equal))))

(local
  (defthm map-lookup-equal-of-reverse-list
    (equal (map-lookup-equal (reverse-list keys) alist)
           (reverse-list (map-lookup-equal keys alist)))
    :hints (("Goal" :in-theory (enable map-lookup-equal reverse-list)))))

(local
  (defthm subsetp-equal-of-free-vars-in-terms-of-reverse-list
    (subsetp-equal (free-vars-in-terms (reverse-list terms))
                   (free-vars-in-terms terms))
    :hints (("Goal" :in-theory (enable (:I len) reverse-list) :induct (len terms)))))

(defthm subsetp-equal-of-free-vars-in-terms-of-reverse
  (implies (true-listp acc)
           (iff (subsetp-equal (free-vars-in-terms (map-lookup-equal (reverse acc) alist)) y)
                (subsetp-equal (free-vars-in-terms (map-lookup-equal acc alist)) y)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm subsetp-equal-of-free-vars-in-terms-of-reverse-alt
  (implies (true-listp acc)
           (iff (subsetp-equal (free-vars-in-terms (map-lookup-equal acc alist)) y)
                (subsetp-equal (free-vars-in-terms (map-lookup-equal (reverse acc) alist)) y)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; May drop some of the formals-to-maybe-subst.
;; whose actuals mention any of the formals-to-keep.
;; Returns (mv formals-to-maybe-subst formals-to-keep).
(defund classify-formals-aux (formals-to-maybe-subst formal-arg-alist formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals-to-maybe-subst)
                              (symbol-alistp formal-arg-alist)
                              (pseudo-term-listp (strip-cdrs formal-arg-alist))
                              (symbol-listp formals-to-keep)
                              (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                              (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))))
  (if (endp formals-to-maybe-subst)
      (mv nil nil)
    (let* ((formal (first formals-to-maybe-subst))
           (arg (lookup-eq formal formal-arg-alist))
           (arg-vars (free-vars-in-term arg)))
      (if (intersection-eq arg-vars formals-to-keep)
          ;; We cannot substitute for this formal, because its arg mentions bad vars.
          ;; todo: optimise by adding it to the formals-to-keep now?
          (mv-let (x y)
            (classify-formals-aux (rest formals-to-maybe-subst) formal-arg-alist formals-to-keep)
            (mv x (cons formal y)))
        ;; No problem currently with this formal:
          (mv-let (x y)
            (classify-formals-aux (rest formals-to-maybe-subst) formal-arg-alist formals-to-keep)
            (mv (cons formal x) y))))))

(defthm symbol-listp-of-mv-nth-0-of-classify-formals-aux
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm symbol-listp-of-mv-nth-1-of-classify-formals-aux
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 1 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(defthm subsetp-equal-of-mv-nth-0-of-classify-formals-aux
  (subsetp-equal (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm classify-formals-aux-correct
  (implies (and (symbol-listp formals-to-maybe-subst)
                (symbol-alistp formal-arg-alist)
                (pseudo-term-listp (strip-cdrs formal-arg-alist))
                (symbol-listp formals-to-keep)
                (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                (subsetp-equal formals-to-keep (strip-cars formal-arg-alist))
                )
           (not (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)) formal-arg-alist))
                                    formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm len-of-mv-nth-0-of-classify-formals-aux-linear
  (<= (len (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
      (len formals-to-maybe-subst))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm classify-formals-aux-stopping
  (iff (equal (len (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
              (len formals-to-maybe-subst))
       (not (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-maybe-subst formal-arg-alist))
                             formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm classify-formals-aux-stopping-2
  (iff (< (len (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
          (len formals-to-maybe-subst))
       (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-maybe-subst formal-arg-alist))
                        formals-to-keep))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm subsetp-equal-of-mv-nth-1-of-classify-formals-aux
  (subsetp-equal (mv-nth 1 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; optimize?
;; Returns (mv reduced-formals-to-maybe-subst extended-formals-to-keep).
(defund classify-formals (formals-to-maybe-subst formal-arg-alist formals-to-keep)
  (declare (xargs :guard (and (symbol-listp formals-to-maybe-subst)
                              (symbol-alistp formal-arg-alist)
                              (pseudo-term-listp (strip-cdrs formal-arg-alist))
                              (symbol-listp formals-to-keep)
                              (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                              (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))
                  :measure (len formals-to-maybe-subst)))
  (mv-let (new-formals-to-maybe-subst extra-formals-to-keep)
    (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)
    (if (>= (len new-formals-to-maybe-subst) (len formals-to-maybe-subst)) ; can't actually be greater
        (mv formals-to-maybe-subst formals-to-keep) ; done!
      (classify-formals new-formals-to-maybe-subst formal-arg-alist (append extra-formals-to-keep formals-to-keep)))))

(defthm classify-formals-correct
  (implies (and (symbol-listp formals-to-maybe-subst)
                (symbol-alistp formal-arg-alist)
                (pseudo-term-listp (strip-cdrs formal-arg-alist))
                (symbol-listp formals-to-keep)
                (subsetp-equal formals-to-maybe-subst (strip-cars formal-arg-alist))
                (subsetp-equal formals-to-keep (strip-cars formal-arg-alist)))
           (not (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)) formal-arg-alist))
                                    (mv-nth 1 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (e/d (classify-formals) (intersection-equal-symmetric-iff)))))

(defthm classify-formals-aux-correct-1
  (subsetp-equal (set-difference-equal formals-to-maybe-subst
                                       (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
                 (mv-nth 1 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))
  :hints (("Goal" :in-theory (enable classify-formals-aux set-difference-equal))))

(defthm subsetp-equal-of-remove-equal-arg2
  (equal (subsetp-equal x (remove-equal a y))
         (if (member-equal a x)
             nil
           (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal member-equal))))

(defthm classify-formals-aux-correct-1-alt
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (subsetp-equal (mv-nth 1 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                          (set-difference-equal formals-to-maybe-subst
                                                (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (enable classify-formals-aux set-difference-equal))))

(local (include-book "kestrel/lists-light/remove-equal" :dir :system))

(defthm equal-of-remove-equal-same
  (equal (equal x (remove-equal a x))
         (and (not (member-equal a x))
              (true-listp x)))
  :hints (("Goal" :in-theory (enable remove-equal member-equal))))

(defthm classify-formals-aux-correct-1-alt-strong
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (equal (mv-nth 1 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))
                  (set-difference-equal formals-to-maybe-subst
                                        (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep)))))
  :hints (("Goal" :in-theory (enable classify-formals-aux set-difference-equal))))

;sanity check
;needed?
(thm
  (implies (and ;(subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
             ;(no-duplicatesp-equal formals-to-maybe-subst)
             )
           (subsetp-equal formals-to-keep
                          (mv-nth 1 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-formals))))

(defthm no-duplicatesp-equal-of-mv-nth-0-of-classify-formals-aux
  (implies (no-duplicatesp-equal formals-to-maybe-subst)
           (no-duplicatesp-equal (mv-nth 0 (classify-formals-aux formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-formals-aux))))

(defthm symbol-listp-of-mv-nth-0-of-classify-formals
  (implies (symbol-listp formals-to-maybe-subst)
           (symbol-listp (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :in-theory (enable classify-formals))))

(defthm set-helper1
  (equal (subsetp-equal (set-difference-equal x this) (append (set-difference-equal y this) z))
         (subsetp-equal (set-difference-equal x this) (append y z)))
  :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

;; (thm
;;   (equal (subsetp-equal (set-difference-equal x this) (append (set-difference-equal y this) z))
;;          (subsetp-equal (set-difference-equal x this) (append y z)))
;;   :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

(defthm set-helper2
  (implies (subsetp-equal (set-difference-equal oformals-to-maybe-subst formals-to-maybe-subst) formals-to-keep)
           (subsetp-equal (set-difference-equal oformals-to-maybe-subst xxx) (append formals-to-maybe-subst formals-to-keep)))
  :hints (("Goal" :in-theory (enable set-difference-equal set-difference-equal))))

;; ;; the final formals-to-keep should include all the formals-to-maybe-subst that we had to drop:
;; (thm
;;   (implies (and; (subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
;;              (subsetp-equal (set-difference-equal formals-to-maybe-subst formals-to-maybe-subst)
;;                             formals-to-keep)
;;              (no-duplicatesp-equal formals-to-maybe-subst)
;;              )
;;            (subsetp-equal (set-difference-equal formals-to-maybe-subst
;;                                                 (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))
;;                           (mv-nth 1 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable classify-formals))))

;; the final formals-to-keep should include all the formals-to-maybe-subst that we had to drop:
(defthm classify-formals-lemma ;rename
    (implies (and (subsetp-equal formals-to-maybe-subst oformals-to-maybe-subst)
                  (subsetp-equal (set-difference-equal oformals-to-maybe-subst formals-to-maybe-subst) formals-to-keep)
                  (no-duplicatesp-equal formals-to-maybe-subst))
             (subsetp-equal (set-difference-equal oformals-to-maybe-subst
                                                  (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)))
                            (mv-nth 1 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (classify-formals) (intersection-equal-symmetric-iff)))))

(defthm call-of-classify-formals-ok
  (implies (and (subsetp-equal try-vars non-trivial-formals)
                (symbol-listp try-vars)
                (symbol-alistp alist)
                (pseudo-term-listp (strip-cdrs alist))
                (symbol-listp non-trivial-formals)
                (subsetp-equal try-vars (strip-cars alist))
                (subsetp-equal non-trivial-formals (strip-cars alist))
                (no-duplicatesp-equal try-vars))
           (not
             (intersection-equal (free-vars-in-terms (map-lookup-equal (mv-nth 0 (classify-formals try-vars alist (set-difference-equal non-trivial-formals try-vars))) alist))
                                 (set-difference-equal non-trivial-formals (mv-nth '0 (classify-formals try-vars alist (set-difference-equal non-trivial-formals try-vars)))))))
  :hints (("Goal" :use (:instance classify-formals-correct
                                  (formals-to-maybe-subst try-vars)
                                  (formal-arg-alist alist)
                                  (formals-to-keep (set-difference-equal non-trivial-formals try-vars)))
           :in-theory (disable classify-formals-correct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: deprecate the other one? but add back special treatment of for mv-nth
(mutual-recursion
 (defun substitute-unnecessary-lambda-vars-in-term2 (term print)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (substitute-unnecessary-lambda-vars-in-terms2 args print)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (substitute-unnecessary-lambda-vars-in-term2 lambda-body print))
                  (formal-arg-alist (pairlis$ formals args))
                  ;; (trivial-formals (trivial-formals formals args))
                  ;; (formals-bound-to-mv-nths (vars-bound-to-mv-nths formals args))
                  (non-trivial-formals (non-trivial-formals formals args))
                  ;; We try to substitute for a lambda var if:
                  ;; 1) It appears only once in the lambda-body
                  ;; and
                  ;; 2) It is not bound to itself (trivial formals
                  ;; don't really "count against" us, since lambdas must be closed)
                  ;; and
                  ;; ;; 3) It is not bound to an mv-nth (to avoid messing up MV-LET patterns)
                  ;; ;; and
                  ;; 4) It is bound to a term that does not mention any of the remaining non-trivial formals.
                  (formals-to-maybe-subst (vars-that-appear-only-once non-trivial-formals lambda-body))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst trivial-formals))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst formals-bound-to-mv-nths)) ; todo: make this optional
                  ;; (formals-to-drop (vars-expressible-without-clashes formals-to-maybe-subst formal-arg-alist non-trivial-formals)) ; would be ok to mention formals we are substituting?
                  ;; We can't subst for any formal whose arg mentions a non-trivial formal that remains:
                  ;(bad-arg-vars (set-difference-eq non-trivial-formals formals-to-maybe-subst))
                  ;; Not being able so subst for a formal means it may block other formals (in whose args it appears):
                  ;(formals-to-subst (maybe-remove-more-formals formals-to-maybe-subst formal-arg-alist bad-arg-vars))
                  (formals-to-keep (set-difference-eq non-trivial-formals formals-to-maybe-subst)) ; may be extended by classify-formals
                  )
             (mv-let (formals-to-subst formals-to-keep)
               (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)
               (declare (ignore formals-to-keep)) ; todo
               (progn$ (and print "Will subst for ~x0 in lambda.~%" formals-to-subst)
                       (subst-formals-in-lambda-application formals lambda-body args formals-to-subst))))
         ;;not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun substitute-unnecessary-lambda-vars-in-terms2 (terms print)
   (declare (xargs :measure (acl2-count terms)
                   :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (substitute-unnecessary-lambda-vars-in-term2 (first terms) print)
                     (substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print)
                     terms))))

(defthm len-of-substitute-unnecessary-lambda-vars-in-terms2
  (equal (len (substitute-unnecessary-lambda-vars-in-terms2 terms print))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len)))))

(make-flag substitute-unnecessary-lambda-vars-in-term2)

(local (in-theory (enable pseudo-term-listp-when-symbol-listp)))

(local (in-theory (disable intersection-equal-symmetric-iff)))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm pseudo-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (pseudo-termp term)
             (pseudo-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm pseudo-term-listp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(include-book "no-duplicate-lambda-formals-in-termp")
;(include-book "no-nils-in-termp")

(defthm subsetp-equal-of-mv-nth-0-of-classify-formals
  (subsetp-equal (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))
                 formals-to-maybe-subst)
  :hints (("Goal" :in-theory (enable classify-formals))))

(defthm subsetp-equal-of-mv-nth-0-of-classify-formals-gen
  (implies (subsetp-equal formals-to-maybe-subst x)
           (subsetp-equal (mv-nth 0 (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep))
                          x))
  :hints (("Goal" :in-theory (enable classify-formals))))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm no-nils-in-termp-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (substitute-unnecessary-lambda-vars-in-term2 term print)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm no-nils-in-termsp-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (no-nils-in-termsp (substitute-unnecessary-lambda-vars-in-terms2 terms print)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm-flag-substitute-unnecessary-lambda-vars-in-term2
  (defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  ;(no-nils-in-termp term)
                  )
             (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print))
                            (free-vars-in-term term)))
    :flag substitute-unnecessary-lambda-vars-in-term2)
  (defthm subsetp-equal-of-free-vars-in-terms-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  ;(no-nils-in-termsp terms)
                  )
             (subsetp-equal (free-vars-in-terms (substitute-unnecessary-lambda-vars-in-terms2 terms print))
                            (free-vars-in-terms terms)))
    :flag substitute-unnecessary-lambda-vars-in-terms2))

(defthm subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2-gen
  (implies (and (subsetp-equal (free-vars-in-term term) x)
                (pseudo-termp term))
           (subsetp-equal (free-vars-in-term (substitute-unnecessary-lambda-vars-in-term2 term print))
                          x))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-substitute-unnecessary-lambda-vars-in-term2))))

;; the point of this is to change the alist used for the lambda case:
(mutual-recursion
 (defun induct-substitute-unnecessary-lambda-vars-in-term2 (term print alist)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil)
            (irrelevant alist))
   (if (or (variablep term)
           (quotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (induct-substitute-unnecessary-lambda-vars-in-terms2 args print alist)) ;process the args first
            (fn (ffn-symb term)))
       (if (consp fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((formals (lambda-formals fn))
                  (lambda-body (lambda-body fn))
                  ;;apply recursively to the lambda body:
                  (lambda-body (induct-substitute-unnecessary-lambda-vars-in-term2 lambda-body print
                                                                                   ;; note this:
                                                                                   (pairlis$ (lambda-formals fn) (empty-eval-list args alist))))
                  (formal-arg-alist (pairlis$ formals args))
                  ;; (trivial-formals (trivial-formals formals args))
                  ;; (formals-bound-to-mv-nths (vars-bound-to-mv-nths formals args))
                  (non-trivial-formals (non-trivial-formals formals args))
                  ;; We try to substitute for a lambda var if:
                  ;; 1) It appears only once in the lambda-body
                  ;; and
                  ;; 2) It is not bound to itself (trivial formals
                  ;; don't really "count against" us, since lambdas must be closed)
                  ;; and
                  ;; ;; 3) It is not bound to an mv-nth (to avoid messing up MV-LET patterns)
                  ;; ;; and
                  ;; 4) It is bound to a term that does not mention any of the remaining non-trivial formals.
                  (formals-to-maybe-subst (vars-that-appear-only-once non-trivial-formals lambda-body))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst trivial-formals))
                  ;; (formals-to-maybe-subst (set-difference-eq formals-to-maybe-subst formals-bound-to-mv-nths)) ; todo: make this optional
                  ;; (formals-to-drop (vars-expressible-without-clashes formals-to-maybe-subst formal-arg-alist non-trivial-formals)) ; would be ok to mention formals we are substituting?
                  ;; We can't subst for any formal whose arg mentions a non-trivial formal that remains:
                  ;(bad-arg-vars (set-difference-eq non-trivial-formals formals-to-maybe-subst))
                  ;; Not being able so subst for a formal means it may block other formals (in whose args it appears):
                  ;(formals-to-subst (maybe-remove-more-formals formals-to-maybe-subst formal-arg-alist bad-arg-vars))
                  (formals-to-keep (set-difference-eq non-trivial-formals formals-to-maybe-subst)) ; may be extended by classify-formals
                  )
             (mv-let (formals-to-subst formals-to-keep)
               (classify-formals formals-to-maybe-subst formal-arg-alist formals-to-keep)
               (declare (ignore formals-to-keep)) ; todo
               (progn$ (and print "Will subst for ~x0 in lambda.~%" formals-to-subst)
                       (subst-formals-in-lambda-application formals lambda-body args formals-to-subst))))
         ;;not a lambda application, so just rebuild the function call:
         (cons-with-hint fn args term)))))

 (defun induct-substitute-unnecessary-lambda-vars-in-terms2 (terms print alist)
   (declare (xargs :measure (acl2-count terms)
                   :guard (pseudo-term-listp terms))
            (irrelevant alist))
   (if (endp terms)
       nil
     (cons-with-hint (induct-substitute-unnecessary-lambda-vars-in-term2 (first terms) print alist)
                     (induct-substitute-unnecessary-lambda-vars-in-terms2 (rest terms) print alist)
                     terms))))

(make-flag induct-substitute-unnecessary-lambda-vars-in-term2)

(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm induct-substitute-unnecessary-lambda-vars-in-term2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-term2 term print alist)
           (substitute-unnecessary-lambda-vars-in-term2 term print))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm induct-substitute-unnecessary-lambda-vars-in-terms2-becomes
    (equal (induct-substitute-unnecessary-lambda-vars-in-terms2 terms print alist)
           (substitute-unnecessary-lambda-vars-in-terms2 terms print))
    :flag induct-substitute-unnecessary-lambda-vars-in-terms2))

;; substitute-unnecessary-lambda-vars-in-term2 does not change the meaning of terms
(defthm-flag-induct-substitute-unnecessary-lambda-vars-in-term2
  (defthm empty-eval-of-substitute-unnecessary-lambda-vars-in-term2
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (equal (empty-eval (substitute-unnecessary-lambda-vars-in-term2 term print) alist)
                    (empty-eval term alist)))
    :flag induct-substitute-unnecessary-lambda-vars-in-term2)
  (defthm empty-eval-list-of-substitute-unnecessary-lambda-vars-in-terms2
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (equal (empty-eval-list (substitute-unnecessary-lambda-vars-in-terms2 terms print) alist)
                    (empty-eval-list terms alist)))
    :flag induct-substitute-unnecessary-lambda-vars-in-terms2)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;empty-eval-of-fncall-args-back ; rename
                            empty-eval-of-fncall-args
                            ;not-member-equal-of-nil-when-no-nils-in-termsp
                            true-listp-when-symbol-listp-rewrite-unlimited
                            ) (;empty-eval-of-fncall-args
                            empty-eval-of-fncall-args-back
                            )))))
