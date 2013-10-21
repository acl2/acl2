

(in-package "GL")


(include-book "bfr")
(include-book "defagg")
(include-book "tools/pattern-match" :dir :system)

(include-book "bvecs")

;;(in-theory (disable cutil::tag-forward-to-consp))

(include-book "gobject-types")

;; Mostly obsolete.  Some general utility stuff at the bottom.


;; ;; Recognizer for a well-formed cdr of a g-number.
;; (defun wf-g-numberp (x)
;;   (declare (xargs :guard t))
;;   (and (consp x)
;;        (bfr-listp (car x))
;;        (or (eq (cdr x) nil)
;;            (and (consp (cdr x))
;;                 (bfr-listp (cadr x))
;;                 (or (eq (cddr x) nil)
;;                     (and (consp (cddr x))
;;                          (bfr-listp (caddr x))
;;                          (or (eq (cdr (cddr x)) nil)
;;                              (and (consp (cdr (cddr x)))
;;                                   (bfr-listp (cadr (cddr x)))
;;                                   (eq (cddr (cddr x))
;;                                       nil)))))))))


;; (in-theory (disable wf-g-numberp))



;; (defun wf-g-numberp-bdd (x)
;;   (declare (xargs :guard t))
;;   (and (consp x)
;;        (acl2::ubdd-listp (car x))
;;        (or (eq (cdr x) nil)
;;            (and (consp (cdr x))
;;                 (acl2::ubdd-listp (cadr x))
;;                 (or (eq (cddr x) nil)
;;                     (and (consp (cddr x))
;;                          (acl2::ubdd-listp (caddr x))
;;                          (or (eq (cdr (cddr x)) nil)
;;                              (and (consp (cdr (cddr x)))
;;                                   (acl2::ubdd-listp (cadr (cddr x)))
;;                                   (eq (cddr (cddr x))
;;                                       nil)))))))))

;; (defun wf-g-numberp-aig (x)
;;   (declare (xargs :guard t))
;;   (and (consp x)
;;        (true-listp (car x))
;;        (or (eq (cdr x) nil)
;;            (and (consp (cdr x))
;;                 (true-listp (cadr x))
;;                 (or (eq (cddr x) nil)
;;                     (and (consp (cddr x))
;;                          (true-listp (caddr x))
;;                          (or (eq (cdr (cddr x)) nil)
;;                              (and (consp (cdr (cddr x)))
;;                                   (true-listp (cadr (cddr x)))
;;                                   (eq (cddr (cddr x))
;;                                       nil)))))))))

;; (local
;;  (progn
;;    (defthm norm-listp-is-bfr-listp
;;      (implies (not (bfr-mode))
;;               (iff (acl2::ubdd-listp x)
;;                    (bfr-listp x)))
;;      :hints(("Goal" :in-theory (enable bfr-listp bfr-p))))

;;    (in-theory (disable acl2::ubdd-listp))

;;    (defthm wf-g-numberp-bdd-is-wf-g-numberp
;;      (implies (not (bfr-mode))
;;               (equal (wf-g-numberp-bdd x)
;;                      (wf-g-numberp x)))
;;      :hints(("Goal" :in-theory (enable wf-g-numberp))))

;;    (in-theory (disable wf-g-numberp-bdd))

;;    (local (defthmd true-listp-is-bfr-listp
;;             (implies (bfr-mode)
;;                      (equal (true-listp x)
;;                             (bfr-listp x)))
;;             :hints(("Goal" :in-theory (enable bfr-listp bfr-p)))))

;;    (defthm wf-g-numberp-aig-is-wf-g-numberp
;;      (implies (bfr-mode)
;;               (equal (wf-g-numberp-aig x)
;;                      (wf-g-numberp x)))
;;      :hints(("Goal" :in-theory (enable wf-g-numberp
;;                                        true-listp-is-bfr-listp))))

;;    (in-theory (disable wf-g-numberp-aig))))




;; ;; Recognizer for valid g-objects.
;; (defn gobjectp (x)
;;   (declare (xargs :measure (acl2-count x)))
;;   (if (atom x)
;;       (not (g-keyword-symbolp x))
;;     (case (tag x)
;;       (:g-concrete (g-concrete-p x))
;;       (:g-boolean  (and (g-boolean-p x)
;;                         (bfr-p (g-boolean->bool x))))
;;       (:g-number (and (g-number-p x)
;;                       (wf-g-numberp (g-number->num x))))
;;       (:g-ite (and (g-ite-p x)
;;                    (gobjectp (g-ite->test x))
;;                    (gobjectp (g-ite->then x))
;;                    (gobjectp (g-ite->else x))))
;;       (:g-apply (and (g-apply-p x)
;;                      (symbolp (g-apply->fn x))
;;                      (gobjectp (g-apply->args x))))
;;       (:g-var (g-var-p x))
;;       (otherwise (and (gobjectp (car x))
;;                       (gobjectp (cdr x)))))))


;; Here is a hierarchy of objects, explained below.  Each lower
;; category is a subset of the ones above.

;; -------------------------------------
;;              ACL2 objects
;; -------------------------------------
;;                Gobjects
;; -------------------------------------
;;             General-concretes
;; -------------------------------------
;;      Concretes |  Proper-g-concretes
;; -------------------------------------

;; ACL2 objects: the universe.

;; gobjects:  well-formed symbolic objects

;; general-concretes: symbolic objects which can be syntactically
;; determined to always evaluate to a particular constant.

;; concretes: symbolic objects which always evaluate to themselves.

;; proper-g-concretes: G-CONCRETE objects for which the G-CONCRETE-OBJ
;; is NOT a concrete.

;; Here is a function that distingushes between ACL2 objects,
;; gobjects, general-concretes, and concretes.  Proper-g-concretes are
;; recognized by a wrapper around this function since they are not
;; recursively closed in the same sense as the others.

;; This function returns NIL for ACL2 objects, 'GOBJECT for gobjects
;; which are not general-concretes, 'GENERAL for general-concretes
;; which are not concrete, and 'CONCRETE for concretes.
;; (defn gobject-hierarchy-bdd (x)
;;   (if (atom x)
;;       (and (not (g-keyword-symbolp x)) 'concrete)
;;     (cond
;;      ((g-concrete-p x)       'general)
;;      ((g-boolean-p x)   (and (acl2::ubddp (g-boolean->bool x))
;;                              'gobject))
;;      ((g-number-p x)    (and (wf-g-numberp-bdd (g-number->num x))
;;                              'gobject))
;;      ((g-ite-p x)       (and (gobject-hierarchy-bdd (g-ite->test x))
;;                              (gobject-hierarchy-bdd (g-ite->then x))
;;                              (gobject-hierarchy-bdd (g-ite->else x))
;;                              'gobject))
;;      ((g-apply-p x)     (and (symbolp (g-apply->fn x))
;;                              (gobject-hierarchy-bdd (g-apply->args x))
;;                              'gobject))
;;      ((g-var-p x)            'gobject)
;;      (t (let ((car (gobject-hierarchy-bdd (car x))))
;;           (and car
;;                (let ((cdr (gobject-hierarchy-bdd (cdr x))))
;;                  (and cdr
;;                       (cond ((or (eq car 'gobject) (eq cdr 'gobject))
;;                              'gobject)
;;                             ((or (eq car 'general) (eq cdr 'general))
;;                              'general)
;;                             (t 'concrete))))))))))

;; (defn gobject-hierarchy-aig (x)
;;   (if (atom x)
;;       (and (not (g-keyword-symbolp x)) 'concrete)
;;     (cond
;;      ((g-concrete-p x)       'general)
;;      ((g-boolean-p x)   'gobject)
;;      ((g-number-p x)    (and (wf-g-numberp-aig (g-number->num x))
;;                              'gobject))
;;      ((g-ite-p x)       (and (gobject-hierarchy-aig (g-ite->test x))
;;                              (gobject-hierarchy-aig (g-ite->then x))
;;                              (gobject-hierarchy-aig (g-ite->else x))
;;                              'gobject))
;;      ((g-apply-p x)     (and (symbolp (g-apply->fn x))
;;                              (gobject-hierarchy-aig (g-apply->args x))
;;                              'gobject))
;;      ((g-var-p x)            'gobject)
;;      (t (let ((car (gobject-hierarchy-aig (car x))))
;;           (and car
;;                (let ((cdr (gobject-hierarchy-aig (cdr x))))
;;                  (and cdr
;;                       (cond ((or (eq car 'gobject) (eq cdr 'gobject))
;;                              'gobject)
;;                             ((or (eq car 'general) (eq cdr 'general))
;;                              'general)
;;                             (t 'concrete))))))))))


;; (defun gobject-hierarchy (x)
;;   (declare (xargs :guard t
;;                   :verify-guards nil))
;;   (mbe :logic
;;        ;; We can't use memoization with this function body because it calls
;;        ;; bfr-mode, which is constrained/attached.  So in the :exec version we
;;        ;; instead call one version or the other, neither of which uses an
;;        ;; attached function.
;;        (if (atom x)
;;            (and (not (g-keyword-symbolp x)) 'concrete)
;;          (cond
;;           ((g-concrete-p x)       'general)
;;           ((g-boolean-p x)   (and (bfr-p (g-boolean->bool x))
;;                                   'gobject))
;;           ((g-number-p x)    (and (wf-g-numberp (g-number->num x))
;;                                   'gobject))
;;           ((g-ite-p x)       (and (gobject-hierarchy (g-ite->test x))
;;                                   (gobject-hierarchy (g-ite->then x))
;;                                   (gobject-hierarchy (g-ite->else x))
;;                                   'gobject))
;;           ((g-apply-p x)     (and (symbolp (g-apply->fn x))
;;                                   (gobject-hierarchy (g-apply->args x))
;;                                   'gobject))
;;           ((g-var-p x)            'gobject)
;;           (t (let ((car (gobject-hierarchy (car x))))
;;                (and car
;;                     (let ((cdr (gobject-hierarchy (cdr x))))
;;                       (and cdr
;;                            (cond ((or (eq car 'gobject) (eq cdr 'gobject))
;;                                   'gobject)
;;                                  ((or (eq car 'general) (eq cdr 'general))
;;                                   'general)
;;                                  (t 'concrete)))))))))
;;        :exec (bfr-case :bdd (gobject-hierarchy-bdd x)
;;                        :aig (gobject-hierarchy-aig x))))

;; (local
;;  (progn
;;    (defthmd ubddp-is-bfr-p
;;      (implies (not (bfr-mode))
;;               (iff (acl2::ubddp x)
;;                    (bfr-p x)))
;;      :hints(("Goal" :in-theory (enable bfr-p))))


;;    (defthmd aig-mode-bfr-p
;;      (implies (bfr-mode)
;;               (bfr-p x))
;;      :hints(("Goal" :in-theory (enable bfr-p))))))


;; (defthm gobject-hierarchy-bdd-is-gobject-hierarchy
;;   (implies (not (bfr-mode))
;;            (equal (gobject-hierarchy-bdd x)
;;                   (gobject-hierarchy x)))
;;   :hints(("Goal" :in-theory (enable ubddp-is-bfr-p))))

;; (defthm gobject-hierarchy-aig-is-gobject-hierarchy
;;   (implies (bfr-mode)
;;            (equal (gobject-hierarchy-aig x)
;;                   (gobject-hierarchy x)))
;;   :hints(("Goal" :in-theory (enable aig-mode-bfr-p))))


;; (in-theory (disable gobject-hierarchy-bdd
;;                     gobject-hierarchy-aig))

;; (verify-guards gobject-hierarchy)

;; (in-theory (disable gobject-hierarchy (gobject-hierarchy)))

;; (defthm gobject-hierarchy-of-atomic-constants
;;   (implies (and (syntaxp (quotep x))
;;                 (atom x))
;;            (equal (gobject-hierarchy x)
;;                   (and (not (g-keyword-symbolp x))
;;                        'concrete)))
;;   :hints(("Goal" :in-theory (enable gobject-hierarchy))))

;; (memoize 'gobject-hierarchy-bdd :condition '(consp x))
;; (memoize 'gobject-hierarchy-aig :condition '(consp x))

;; (defn gobjectp (x)
;;   (if (gobject-hierarchy x) t nil))

;; (in-theory (disable gobjectp (gobjectp)))

;; (defthm gobjectp-of-atomic-constants
;;   (implies (and (syntaxp (quotep x))
;;                 (atom x))
;;            (equal (gobjectp x)
;;                   (not (g-keyword-symbolp x))))
;;   :hints(("Goal" :in-theory (enable gobjectp gobject-hierarchy))))

;; ;; GOBJ-FIX: Fix argument into a GOBJECTP
;; (defun gobj-fix (x)
;;   (declare (xargs :guard t))
;;   (if (gobjectp x)
;;       x
;;     (g-concrete x)))

;; (in-theory (disable gobj-fix))

;; (defmacro mbe-gobj-fix (x)
;;   `(mbe :logic (gobj-fix ,x) :exec ,x))


;; (defun gobj-equiv (x y)
;;   (equal (gobj-fix x) (gobj-fix y)))

;; (defequiv gobj-equiv)


;; (defun gobject-listp (x)
;;   (declare (xargs :guard t))
;;   (if (atom x)
;;       (eq x nil)
;;     (and (gobjectp (car x))
;;          (gobject-listp (cdr x)))))

;; (in-theory (disable gobject-listp))

;; #||
;; ;; Example G objects.

;; 1 ;; 1
;; '(1 2 3 . 4) ;; itself
;; `(1 2 3 . (:g-number (,(qv 0)))) ; (1 2 3 . 0) or (1 2 3 . 1)
;; '(1 2 3 :g-concrete . foo) ; (1 2 3 . foo)
;; `(:g-ite (:g-boolean . ,(qv 0)) "abc" . "acd") ; "abc" or "acd"
;; `(:g-ite (:g-boolean . ,(qv 0)) #\a . #\b)     ; #\a or #\b

;; (g-intern `(:g-ite (:g-boolean . ,(qv 0)) "abc" . "acd")
;;           `(:g-ite (:g-boolean . ,(qv 1)) "ACL2" . "COMMON-LISP"))
;; =
;; `(:g-ite (:g-boolean . ,(qv 0))
;;            (:g-ite (:g-boolean . ,(qv 1))
;;                      ACL2::ABC . COMMON-LISP::ABC)
;;            (:g-ite (:g-boolean . ,(qv 1))
;;                      ACL2::ACD . COMMON-LISP::ACD))

;; `(:g-ite (:g-boolean . ,(qv 0)) abc . acd) ; "abc" or "acd"




;; `(:g-boolean . ,(qv 0)) ;; either NIL or T

;; `(:g-number (,(qv 0))) ;; either 0 or 1
;; `(:g-number (t) ,(qv 0)) ;; either 1 or -1
;; `(:g-number (t) nil (t ,(qv 0))) ;; either 1 or 1/3
;; `(:g-number (t) nil nil ((qv 0)) ;; either #C(1 0) or #C(1 1)

;; `(:g-ite (:g-boolean . ,(qv 0)) 'yes . 'no) ;; either YES or NO

;; `(:g-concrete . :g-number) ;; the symbol :G-NUMBER
;; `(:g-concrete . (:g-boolean . ,(qv 0))) ;; the object `(:g-boolean . ,(qv 0))

;; `(:g-apply car (:g-ite (:g-boolean . ,(qv 0)) (1 . 2) . nil))
;;    ;; either 1 or nil   (car of either (1 . 2) or nil)




;; ||#


(defun gl-aside (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defun gl-ignore (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defund gl-error (x)
  (declare (xargs :guard t)
           (ignore x))
  (prog2$ (er hard? 'gl-error "GL-ERROR call encountered; quitting~%")
          nil))

(defthm gl-error-is-nil
  (equal (gl-error x) nil)
  :hints(("Goal" :in-theory (enable gl-error))))

;; (defun gl-lazy-and-fn (terms)
;;   (if (atom terms)
;;       t
;;     (if (atom (cdr terms))
;;         (car terms)
;;       `(let ((gl-lazy-and-term ,(car terms)))
;;          (if gl-lazy-and-term
;;              ,(gl-lazy-and-fn (cdr terms))
;;            (prog2$ (cw "GL-LAZY-AND failed on term: ~x0~%"
;;                        ',(car terms))
;;                    (gl-error gl-lazy-and-term)))))))

;; (defmacro gl-lazy-and (&rest terms)
;;   (gl-lazy-and-fn terms))
