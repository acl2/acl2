

(in-package "GL")

(include-book "tools/flag" :dir :system)
(include-book "gl-util")

(program)


(defun gobjectp-formals-list (formals)
  (if (Atom formals)
      nil
    (cons `(gobjectp ,(car formals))
          (gobjectp-formals-list (cdr formals)))))

(defun acl2-count-gobj-fix-formals-list (formals)
  (if (atom formals)
      nil
    (cons `(acl2-count (gobj-fix ,(car formals)))
          (acl2-count-gobj-fix-formals-list (cdr formals)))))

(defun mbe-gobj-fix-formals-list (formals)
  (if (atom formals)
      nil
    (cons `(,(car formals) (mbe :logic (gobj-fix ,(car formals))
                                :exec ,(car formals)))
          (mbe-gobj-fix-formals-list (cdr formals)))))

(defmacro def-g-fn (fn body)
  `(make-event
    (let* ((gfn (gl-fnsym ',fn))
           (world (w state))
           (formals (wgetprop ',fn 'formals)))
      `(progn
         (defun ,gfn (,@formals hyp clk)
           (declare (xargs :guard (and ,@(gobjectp-formals-list formals)
                                       (bfr-p hyp)
                                       (natp clk))
                           :measure
                           (+ . ,(acl2-count-gobj-fix-formals-list
                                  formals))
                           :verify-guards nil)
                    (ignorable hyp clk))
           (let ((hyp (bfrfix hyp))
                 . ,(mbe-gobj-fix-formals-list formals))
             (declare (ignorable ,@formals hyp))
             ,,body))
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
           `(if (and (general-concretep ,a) (general-concretep ,b))
                (mk-g-concrete
                 (ec-call (,fn (general-concrete-obj ,a)
                               (general-concrete-obj ,b))))
              (pattern-match ,a
                ((g-ite test then else)
                 (if (zp clk)
                     (g-apply ',fn (list ,a ,b))
                   (g-if test
                         (,gfn then ,b hyp clk)
                         (,gfn else ,b hyp clk))))
                (& (pattern-match ,b
                     ((g-ite test then else)
                      (if (zp clk)
                          (g-apply ',fn (list ,a ,b))
                        (g-if test
                              (,gfn ,a then hyp clk)
                              (,gfn ,a else hyp clk))))
                     ((g-var &) (g-apply ',fn (list ,a ,b)))
                     ((g-apply & &) (g-apply ',fn (list ,a ,b)))
                     (& (pattern-match ,a
                          ((g-var &) (g-apply ',fn (list ,a ,b)))
                          ((g-apply & &) (g-apply ',fn (list ,a ,b)))
                          (& ,',',body))))))))))))


(defun gobjectp-thmname (fn)
  (incat 'gl-thm::foo "GOBJECTP-" (symbol-name fn)))


(defun correct-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT"))

(defun correct1-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT1"))

(defun gobj-fix-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-GOBJ-FIX"))

(defun def-gobjectp-thm-fn (gfn fn hints world)
  (b* ((formals (wgetprop fn 'formals))
       (thmname (gobjectp-thmname gfn)))
    `(progn
       (defthm ,thmname
         (gobjectp (,gfn ,@formals hyp clk))
         :hints ,hints)
       (add-to-ruleset! g-gobjectp-lemmas '(,thmname)))))


(defmacro def-gobjectp-thm (fn &key hints)
  `(make-event
    (let ((gfn (gl-fnsym ',fn)))
      (def-gobjectp-thm-fn gfn ',fn ,hints (w state)))))


(defun ev-formals-list (ev formals)
  (if (atom formals)
      nil
    (cons `(,ev ,(car formals) env)
          (ev-formals-list ev (cdr formals)))))

(defun gobj-fix-formals-list (formals)
  (if (atom formals)
      nil
    (cons `(gobj-fix ,(car formals))
          (gobj-fix-formals-list (cdr formals)))))

(defun pair-gobj-fix-formals-list (formals)
  (if (atom formals)
      nil
    (cons `(,(car formals) (gobj-fix ,(car formals)))
          (pair-gobj-fix-formals-list (cdr formals)))))

(defun def-g-correct-thm-fn (gfn fn ev hints final-hints world)
  (b* ((formals (wgetprop fn 'formals))
       (thmname (correct-thmname gfn))
       (thmname1 (correct1-thmname gfn))
       (gobj-thmname (gobj-fix-thmname gfn)))
    `(encapsulate nil
       (local
        (defthm ,thmname1
          (implies (and (bfr-eval hyp (car env))
                        ,@(gobjectp-formals-list formals)
                        (bfr-p hyp))
                   (equal (,ev (,gfn ,@formals hyp clk) env)
                          (,fn . ,(ev-formals-list ev formals))))
          :hints ,hints))
       (local
        (defthm ,gobj-thmname
          (equal (,gfn ,@(gobj-fix-formals-list formals)
                       (bfr-fix hyp) clk)
                 (,gfn ,@formals hyp clk))
          :hints (("goal" :expand
                   ((,gfn ,@(gobj-fix-formals-list formals)
                          (bfr-fix hyp) clk)
                    (,gfn ,@formals hyp clk)
                    (:free (x) (hide x)))))))
       (in-theory (disable ,gfn))
       (defthm ,thmname
         (implies (bfr-eval hyp (car env))
                  (equal (,ev (,gfn ,@formals hyp clk) env)
                         (,fn . ,(ev-formals-list ev formals))))
         :hints ,(or final-hints
                     `(("goal" 
                        :use ((:instance
                               ,thmname1
                               (hyp (bfr-fix hyp))
                               . ,(pair-gobj-fix-formals-list
                                   formals)))))))
       (table gl-function-info ',fn '(,gfn (,thmname . ,ev))))))

(defmacro def-g-correct-thm (fn ev &key hints final-hints)
  `(make-event
    (let ((gfn (gl-fnsym ',fn)))
      (def-g-correct-thm-fn gfn ',fn ',ev ,hints ,final-hints (w state)))))


(defmacro verify-g-guards (fn &key hints)
  `(make-event
    (let ((gfn (gl-fnsym ',fn)))
      `(verify-guards ,gfn :hints ,,hints))))
