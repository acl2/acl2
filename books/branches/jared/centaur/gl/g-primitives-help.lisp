

(in-package "GL")

(include-book "tools/flag" :dir :system)
(include-book "gl-util")

(program)


;; (defun gobjectp-formals-list (formals)
;;   (if (Atom formals)
;;       nil
;;     (cons `(gobjectp ,(car formals))
;;           (gobjectp-formals-list (cdr formals)))))

(defun acl2-count-formals-list (formals)
  (if (atom formals)
      nil
    (cons `(acl2-count ,(car formals))
          (acl2-count-formals-list (cdr formals)))))

;; (defun mbe-gobj-fix-formals-list (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(,(car formals) (mbe :logic (gobj-fix ,(car formals))
;;                                 :exec ,(car formals)))
;;           (mbe-gobj-fix-formals-list (cdr formals)))))

(defmacro def-g-fn (fn body)
  `(make-event
    (let* ((gfn (gl-fnsym ',fn))
           (world (w state))
           (formals (wgetprop ',fn 'formals)))
      `(progn
         (defun ,gfn (,@formals hyp clk)
           (declare (xargs :guard (natp clk)
                           :measure
                           (+ . ,(acl2-count-formals-list
                                  formals))
                           :verify-guards nil)
                    (ignorable ,@formals hyp clk))
             ,,body)
         (table g-functions ',',fn ',gfn)))))

(defmacro def-g-binary-op (fn body)
  `(make-event
    (let* ((fn ',fn)
           (world (w state))
           (formals (wgetprop ',fn 'formals))
           (a (car formals))
           (b (cadr formals)))
      `(def-g-fn ,fn
         (let ((a ',a) (b ',b) (fn ',fn))
           `(cond ((and (general-concretep ,a) (general-concretep ,b))
                   (mk-g-concrete
                    (ec-call (,fn (general-concrete-obj ,a)
                                  (general-concrete-obj ,b)))))
                  ((or (atom ,a)
                       (not (member-eq (tag ,a) '(:g-ite :g-var :g-apply))))
                   (cond ((or (atom ,b)
                              (not (member-eq (tag ,b) '(:g-ite :g-var :g-apply))))
                          ,',',body)
                         ((eq (tag ,b) :g-ite)
                          (if (zp clk)
                              (g-apply ',fn (gl-list ,a ,b))
                            (let* ((test (g-ite->test ,b))
                                   (then (g-ite->then ,b))
                                   (else (g-ite->else ,b)))
                              (g-if test
                                    (,gfn ,a then hyp clk)
                                    (,gfn ,a else hyp clk)))))
                         (t (g-apply ',fn (gl-list ,a ,b)))))
                  ((eq (tag ,a) :g-ite)
                   (if (zp clk)
                       (g-apply ',fn (gl-list ,a ,b))
                     (let* ((test (g-ite->test ,a))
                            (then (g-ite->then ,a))
                            (else (g-ite->else ,a)))
                       (g-if test
                             (,gfn then ,b hyp clk)
                             (,gfn else ,b hyp clk)))))
                  (t (g-apply ',fn (gl-list ,a ,b)))))))))

;; (defun gobjectp-thmname (fn)
;;   (incat 'gl-thm::foo "GOBJECTP-" (symbol-name fn)))


(defun correct-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT"))

(defun correct-thmname-appalist (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT-APPALIST"))

(defun correct1-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT1"))

;; (defun gobj-fix-thmname (fn)
;;   (incat 'gl-thm::foo (symbol-name fn) "-GOBJ-FIX"))

;; (defun def-gobjectp-thm-fn (gfn fn hints world)
;;   (b* ((formals (wgetprop fn 'formals))
;;        (thmname (gobjectp-thmname gfn)))
;;     `(progn
;;        (defthm ,thmname
;;          (gobjectp (,gfn ,@formals hyp clk))
;;          :hints ,hints)
;;        (add-to-ruleset! g-gobjectp-lemmas '(,thmname)))))


;; (defmacro def-gobjectp-thm (fn &key hints)
;;   `(make-event
;;     (let ((gfn (gl-fnsym ',fn)))
;;       (def-gobjectp-thm-fn gfn ',fn ,hints (w state)))))


(defun ev-formals-list (ev formals)
  (declare (xargs :mode :logic
                  :guard t))
  (if (atom formals)
      nil
    (cons `(,ev ,(car formals) env)
          (ev-formals-list ev (cdr formals)))))

(defun ev-formals-appalist-list (ev formals aps)
  (declare (xargs :mode :logic
                  :guard t))
  (if (atom formals)
      nil
    (cons `(,ev ,(car formals) env ,aps)
          (ev-formals-appalist-list ev (cdr formals) aps))))

;; (defun gobj-fix-formals-list (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(gobj-fix ,(car formals))
;;           (gobj-fix-formals-list (cdr formals)))))

;; (defun pair-gobj-fix-formals-list (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(,(car formals) (gobj-fix ,(car formals)))
;;           (pair-gobj-fix-formals-list (cdr formals)))))

(defun def-g-correct-thm-fn (gfn fn ev hints world)
  (b* ((formals (wgetprop fn 'formals))
       (thmname (correct-thmname gfn))
       (thmname2 (correct-thmname-appalist gfn))
       (ev-appalist
        (cadr (assoc ev (table-alist 'eval-g-table world)))))
    `(encapsulate nil
       (defthm ,thmname
         (implies (bfr-eval hyp (car env))
                  (equal (,ev (,gfn ,@formals hyp clk) env)
                         (,fn . ,(ev-formals-list ev formals))))
         :hints ,hints)
       (in-theory (disable ,gfn))
       (defthm ,thmname2
         (implies (bfr-eval hyp (car env))
                  (equal (,ev-appalist (,gfn ,@formals hyp clk) env appalist)
                         (,fn . ,(ev-formals-appalist-list ev-appalist formals
                                                           'appalist))))
         :hints ((geval-appalist-functional-inst-hint
                  ',thmname ',ev)))
                              
       (table sym-counterparts-table ',fn '(,gfn ,thmname2))
       (table gl-function-info ',fn '(,gfn (,thmname . ,ev))))))

(defmacro def-g-correct-thm (fn ev &key hints)
  `(make-event
    (let ((gfn (gl-fnsym ',fn)))
      (def-g-correct-thm-fn gfn ',fn ',ev ,hints (w state)))))


(defmacro verify-g-guards (fn &key hints)
  `(make-event
    (let ((gfn (gl-fnsym ',fn)))
      `(verify-guards ,gfn :hints ,,hints))))
