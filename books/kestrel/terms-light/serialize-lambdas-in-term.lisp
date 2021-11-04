; A tool to turn multi-var lambdas into nests of single-var lambdas
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(include-book "sublis-var-simple")
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (in-theory (disable mv-nth symbol-alistp)))

;; We keep the body of the lambda unchanged (for C generation, this must be a
;; call of a function on its formals).
;;
;; First we get the (non-trivial) bindings.  These all happen simultaneously, and the goal is to serialize them.
;; Next, try to find one a "safe" that can go first (because the var it binds is not used by the other bindings).
;; Repeatedly add such safe ones.
;; When no safe ones are left, a temporary must be added.  for example:
;;
;; (let
;;  ((a <expr>) ; not safe because b depends on a
;;   (b ...a...)
;;   ...)
;;  ...)
;;
;; becomes:
;;
;; (let
;;  ((a-temp a) ; save the value of a
;;   (a <expr>)
;;   (b ...a-temp...) ; changed to use a-temp
;;   ...)
;;  ...)
;;
;; Once we add the temporary (and the binding that is now safe), start again looking for additional safe ones.
;; TODO: Can we work harder to minimize the number of temporaries?

;; Makes a nest if lambda applications, one per binding.
(defun make-lambda-nest (bindings body)
  (declare (xargs :guard (symbol-alistp bindings)))
  (if (endp bindings)
      body
    (let* ((binding (first bindings))
           (var (car binding))
           (val (cdr binding)))
      `((lambda (,var) ,(make-lambda-nest (rest bindings) body))
        ,val))))

(defthm pseudo-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (pseudo-termp body))
           (pseudo-termp (make-lambda-nest bindings body))))

;; Returns (mv safe-binding other-bindings) or (mv nil nil) if no safe binding is found.
(defund find-safe-binding (bindings earlier-bindings-rev)
  (declare (xargs :guard (and (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (symbol-alistp earlier-bindings-rev)
                              (pseudo-term-listp (strip-cdrs earlier-bindings-rev)))))
  (if (endp bindings)
      (mv nil nil)
    (let* ((binding (first bindings))
           (var (car binding)))
      (if (and (not (member-eq var (free-vars-in-terms (strip-cdrs (rest bindings)))))
               (not (member-eq var (free-vars-in-terms (strip-cdrs earlier-bindings-rev)))))
          ;; This binding is safe because the var it binds is not used to define any other var in the bindings:
          (mv binding (revappend earlier-bindings-rev (rest bindings)))
        (find-safe-binding (rest bindings) (cons binding earlier-bindings-rev))))))

;; One binding gets removed
(defthm len-of-mv-nth-1-of-find-safe-binding
  (implies (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev))
           (equal (len (mv-nth 1 (find-safe-binding bindings earlier-bindings-rev)))
                  (+ -1 (len bindings) (len earlier-bindings-rev))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm symbol-alistp-of-mv-nth-1-of-find-safe-binding
  (implies (and (symbol-alistp bindings)
                (symbol-alistp earlier-bindings-rev))
           (symbol-alistp (mv-nth 1 (find-safe-binding bindings earlier-bindings-rev))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm pseudo-term-listp-of-strip-cdrs-of-mv-nth-1-of-find-safe-binding
  (implies (and (pseudo-term-listp (strip-cdrs bindings))
                (pseudo-term-listp (strip-cdrs earlier-bindings-rev)))
           (pseudo-term-listp (strip-cdrs (mv-nth 1 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm consp-of-mv-nth-0-of-find-safe-binding
  (implies (symbol-alistp bindings)
           (iff (consp (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))
                (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm symbolp-of-car-of-mv-nth-0-of-find-safe-binding
  (implies (symbol-alistp bindings)
           (symbolp (car (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defthm pseudo-termp-of-cdr-of-mv-nth-0-of-find-safe-binding
  (implies (pseudo-term-listp (strip-cdrs bindings))
           (pseudo-termp (cdr (mv-nth 0 (find-safe-binding bindings earlier-bindings-rev)))))
  :hints (("Goal" :in-theory (enable find-safe-binding))))

(defund serialize-bindings (bindings names-to-avoid)
  (declare (xargs :guard (and (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (symbol-listp names-to-avoid))
                  :verify-guards nil ;done below
                  :measure (len bindings)))
  (if (endp bindings)
      nil
    (mv-let (maybe-safe-binding maybe-other-bindings)
      (find-safe-binding bindings nil)
      (if maybe-safe-binding
          (cons maybe-safe-binding (serialize-bindings maybe-other-bindings names-to-avoid))
        ;; no safe binding, so introduce a temporary for the first binding
        ;; TODO: Might it be better to chose a binding other than the first here?
        (let* ((first-binding (first bindings))
               (first-var (car first-binding))
               (first-val (cdr first-binding))
               (first-var-temp (make-fresh-name (pack$ first-var '-temp) names-to-avoid))
               ;;now fix up the values in later bindings to use first-var-temp instead of first-var:
               (rest-bindings (rest bindings))
               (rest-binding-vars (strip-cars rest-bindings))
               (rest-binding-vals (strip-cdrs rest-bindings))
               (new-rest-binding-vals (sublis-var-simple-lst (acons first-var first-var-temp nil)
                                                             rest-binding-vals))
               (new-rest-bindings (pairlis$ rest-binding-vars new-rest-binding-vals)))
          (acons first-var-temp
                 first-var
                 ;; now safe to overwrite first-var since we've saved its value in the temporary:
                 (acons first-var first-val
                        (serialize-bindings new-rest-bindings (cons first-var-temp names-to-avoid)))))))))

(defthm alistp-of-serialize-bindings
  (implies (symbol-alistp bindings)
           (alistp (serialize-bindings bindings names-to-avoid)))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

(defthm symbol-alistp-of-serialize-bindings
  (implies (symbol-alistp bindings)
           (symbol-alistp (serialize-bindings bindings names-to-avoid)))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

(defthm pseudo-term-listp-of-strip-cdrs-of-serialize-bindings
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings)))
           (pseudo-term-listp (strip-cdrs (serialize-bindings bindings names-to-avoid))))
  :hints (("Goal" :in-theory (enable serialize-bindings))))

(verify-guards serialize-bindings
  :hints (("Goal" :in-theory (enable STRIP-CDRS-OF-CDR))))

;;todo: optimize the case of one non-trivial binding?
(defun serialize-lambda-application-aux (lambda-formals lambda-body args vars-to-avoid)
  (declare (xargs :guard (and (symbol-listp lambda-formals)
                              (pseudo-termp lambda-body)
                              (pseudo-term-listp args)
                              (symbol-listp vars-to-avoid))))
  (let* ((bindings (non-trivial-bindings lambda-formals args)) ; all applied in parallel
         (body-vars (free-vars-in-term lambda-body))
         (serialized-bindings (serialize-bindings bindings (append body-vars vars-to-avoid))))
    ;; Could make a let* here, but then it would not be a pseudo-term
    (make-lambda-nest serialized-bindings lambda-body)))

;; Returns a new term (a nest of lambda applications)
(defun serialize-lambda-application (term vars-to-avoid)
  (declare (xargs :guard (and (pseudo-termp term)
                              (consp term)
                              (consp (ffn-symb term)) ;it's a lambda
                              (symbol-listp vars-to-avoid))))
  (let ((fn (ffn-symb term)))
    (serialize-lambda-application-aux (lambda-formals fn) (lambda-body fn) (fargs term) vars-to-avoid)))

(mutual-recursion
 ;; Consider calling reconstruct-lets-in-term after calling this.
 (defund serialize-lambdas-in-term (term vars-to-avoid)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp vars-to-avoid))
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((fn (ffn-symb term))
            (new-args (serialize-lambdas-in-terms (fargs term) vars-to-avoid)))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((new-lambda-body (serialize-lambdas-in-term (lambda-body fn) vars-to-avoid))) ;;apply recursively to the lambda body
             (serialize-lambda-application-aux (lambda-formals fn) new-lambda-body new-args vars-to-avoid))
         ;; not a lambda application, so just rebuild the function call:
         `(,fn ,@new-args)))))

 (defund serialize-lambdas-in-terms (terms vars-to-avoid)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-listp vars-to-avoid))
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (serialize-lambdas-in-term (first terms) vars-to-avoid)
           (serialize-lambdas-in-terms (rest terms) vars-to-avoid)))))

(make-flag serialize-lambdas-in-term)

;; Serializing lambdas preserves pseudo-termp.
(defthm-flag-serialize-lambdas-in-term
  (defthm pseudo-termp-of-serialize-lambdas-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (serialize-lambdas-in-term term vars-to-avoid)))
    :flag serialize-lambdas-in-term)
  (defthm pseudo-term-listp-of-serialize-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (serialize-lambdas-in-terms terms vars-to-avoid)))
    :flag serialize-lambdas-in-terms)
  :hints (("Goal" :in-theory (enable serialize-lambdas-in-term
                                     serialize-lambdas-in-terms))))

(verify-guards serialize-lambdas-in-term
  :hints (("Goal" :expand ((pseudo-termp term)))))
