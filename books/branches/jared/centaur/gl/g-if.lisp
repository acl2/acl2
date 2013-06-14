

(in-package "GL")

(include-book "ite-merge")
(include-book "gtests")

(defun def-g-identity-fn (name top-p)
  (b* (;; (gobjectp-thm (intern-in-package-of-symbol
       ;;                (concatenate 'string "GOBJECTP-" (symbol-name name))
       ;;                'gl::foo))
       (geval-thm (intern-in-package-of-symbol
                   (concatenate 'string "GEVAL-" (symbol-name name))
                   'gl::foo)))
    `(progn (defun-inline ,name (x)
              (declare (xargs :guard t))
              x)
            ;; (defthm ,gobjectp-thm
            ;;   (equal (gobjectp (,name x))
            ;;          ,(if top-p
            ;;               `(,name (gobjectp (hide (,name x))))
            ;;             '(gobjectp x)))
            ;;   :hints (("goal" :expand ((:free (x) (hide x))))))
            (defthm ,geval-thm
              (equal (generic-geval (,name x) env)
                     ,(if top-p
                          `(,name (generic-geval (hide (,name x)) env))
                        '(generic-geval x env)))
              :hints (("goal" :expand ((:free (x) (hide x))))))
            (in-theory (disable ,name (:t ,name)
                                (,name))))))

(defmacro def-g-identity (name top-p)
  (def-g-identity-fn name top-p))
          

(def-g-identity g-if-marker t)
(def-g-identity g-or-marker t)
(def-g-identity g-test-marker nil)
(def-g-identity g-branch-marker nil)

(defun-inline g-hyp-marker (hyp)
  (declare (xargs :guard t))
  hyp)

(defthm bfr-eval-g-hyp-marker
  (equal (bfr-eval (g-hyp-marker x) env)
         (bfr-eval x env)))

(in-theory (disable g-hyp-marker (:t g-hyp-marker)
                    (g-hyp-marker)))

(defthm gtests-g-test-marker
  (equal (gtests (g-test-marker x) hyp) (gtests x hyp))
  :hints(("Goal" :in-theory (enable g-test-marker))))



(defmacro g-if (test then else)
  `(g-if-marker$inline
    (hide
     (b* ((test (g-test-marker$inline ,test))
          (hyp (g-hyp-marker$inline hyp))
          (gtests (gtests test hyp))
          (then-hyp (bfr-and
                     hyp (bfr-or
                          (gtests-unknown gtests)
                          (gtests-nonnil gtests))))
          (else-hyp (bfr-and
                     hyp (bfr-or
                          (gtests-unknown gtests)
                          (bfr-not (gtests-nonnil gtests)))))
          (then
           (and (hide then-hyp)
                (let ((hyp then-hyp))
                  (declare (ignorable hyp))
                  (g-branch-marker$inline ,then))))
          (else
           (and (hide else-hyp)
                (let ((hyp else-hyp))
                  (declare (ignorable hyp))
                  (g-branch-marker$inline ,else))))
          (merge (gobj-ite-merge (gtests-nonnil gtests) then else
                                 (bfr-and (bfr-not (gtests-unknown gtests))
                                                  hyp))))
       (mk-g-bdd-ite (gtests-unknown gtests)
                     (mk-g-ite (gtests-obj gtests) then else)
                     merge hyp)))))

(defmacro g-or (test else)
  `(g-or-marker$inline
    (hide
     (b* ((test (g-test-marker$inline ,test))
          (hyp (g-hyp-marker$inline hyp))
          (gtests (gtests test hyp))
          (else-hyp (bfr-and
                     hyp (bfr-or
                          (gtests-unknown gtests)
                          (bfr-not (gtests-nonnil gtests)))))
          (else
           (and (hide else-hyp)
                (let ((hyp else-hyp))
                  (declare (ignorable hyp))
                  (g-branch-marker$inline ,else))))
          (merge (gobj-ite-merge (gtests-nonnil gtests) test else
                                 (bfr-and (bfr-not (gtests-unknown gtests))
                                                  hyp))))
       (mk-g-bdd-ite (gtests-unknown gtests)
                     (mk-g-ite (gtests-obj gtests) test else)
                     merge hyp)))))
