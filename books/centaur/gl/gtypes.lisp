
(in-package "GL")

(include-book "gobjectp")

(include-book "generic-geval")

;; (defun gobj-count (x)
;;   (declare (xargs :hints (("goal" :in-theory (enable gobj-fix)))))
;;   (let ((x (gobj-fix x)))
;;     (if (atom x)
;;         0
;;       (pattern-match x
;;         ((g-ite & then else)
;;          (+ 1 (gobj-count then) (gobj-count else)))
;;         (& 0)))))

;; (defthm gobj-count-gobj-fix
;;   (<= (gobj-count (gobj-fix x)) (gobj-count x))
;;   :rule-classes (:rewrite :linear))

;; (defthm gobj-count-g-ite->then
;;   (implies (and (gobjectp x) (g-ite-p x))
;;            (< (gobj-count (g-ite->then x))
;;               (gobj-count x)))
;;   :rule-classes (:rewrite :linear))

;; (defthm gobj-count-g-ite->else
;;   (implies (and (gobjectp x) (g-ite-p x))
;;            (< (gobj-count (g-ite->else x))
;;               (gobj-count x)))
;;   :rule-classes (:rewrite :linear))





;; -------------------------
;; Concrete
;; -------------------------

;; (defn concretep (x)
;;   (declare (inline tag))
;;   (or (atom x)
;;       (and (not (g-keyword-symbolp (tag x)))
;;            (concretep (car x))
;;            (concretep (cdr x)))))


;; (memoize 'concretep :condition '(consp x))

;; (defthm eval-concrete-gobjectp
;;   (implies (and (gobjectp x)
;;                 (concretep x))
;;            (equal (eval-g-base x b) x)))

;; (in-theory (disable concretep))

(defn concrete-gobjectp (x)
  (eq (gobject-hierarchy x) 'concrete))


(in-theory (disable concrete-gobjectp))

(defn mk-g-concrete (x)
  (if (concrete-gobjectp x)
      x
    (g-concrete x)))

(in-theory (disable mk-g-concrete))



;; -------------------------
;; ITE
;; -------------------------

(defun mk-g-ite (c x y)
  (declare (xargs :guard (and (gobjectp c)
                              (gobjectp x)
                              (gobjectp y))
                  :guard-hints
                  (("goal" :in-theory (enable gobj-fix
                                              g-concrete-p
                                              tag)))))
  (let ((c (mbe-gobj-fix c))
        (x (mbe-gobj-fix x))
        (y (mbe-gobj-fix y)))
    (cond ((atom c) (if c x y))
          ((hqual x y) x)
          ((not (g-keyword-symbolp (tag c)))
           ;; c is just a cons
           x)
          ((eq (tag c) :g-number) x)
          ((eq (tag c) :g-concrete)
           (if (g-concrete->obj c) x y))
          (t (g-ite c x y)))))
;;      (list* :g-ite c x y))))

(in-theory (disable mk-g-ite))




;; -------------------------
;; Boolean
;; -------------------------

(defun mk-g-boolean (bdd)
  (declare (xargs :guard (bfr-p bdd)))
  (if (booleanp bdd)
      bdd
    (let ((bdd (bfrfix bdd)))
      (g-boolean bdd))))

(in-theory (disable mk-g-boolean))




;; -------------------------
;; Number
;; -------------------------

(defun mk-g-number-fn (rnum rden inum iden)
  (declare (xargs :guard t))
  (if (and (integerp rnum) (natp rden)
           (integerp inum) (natp iden))
      (components-to-number rnum rden inum iden)
    (flet ((to-uvec (n)
                   (if (natp n)
                       (n2v n)
                     n))
           (to-svec (n)
                    (if (integerp n)
                        (i2v n)
                      n)))
      (let* ((rst (and (not (or (eql iden 1) (equal iden '(t)))) (list (to-uvec iden))))
             (rst (and (not (or (eql inum 0) (equal inum '(nil)))) (cons (to-svec inum) rst)))
             (rst (and (or rst (not (or (eql rden 1) (equal rden '(t))))) (cons (to-uvec rden) rst))))
        (g-number (cons (to-svec rnum) rst))))))
            

(defmacro mk-g-number (rnum &optional
                              (rden '1)
                              (inum '0)
                              (iden '1))
  `(mk-g-number-fn ,rnum ,rden ,inum ,iden))

(add-macro-alias mk-g-number mk-g-number-fn)


(in-theory (disable mk-g-number))


;; -------------------------
;; Cons
;; -------------------------

;; A cons of two gobjects is itself a gobject which evaluates to the cons of
;; the evaluations of the two inputs.  We define a wrapper that fixes the
;; inputs to gobjects so that this can be stated hyp-free.

(defun gl-cons (x y)
  (declare (xargs :guard (and (gobjectp x) (gobjectp y))
                  :guard-hints
                  (("Goal" :in-theory (enable gobj-fix)))))
  (cons (mbe-gobj-fix x) (mbe-gobj-fix y)))

(defun gl-list-macro (lst)
  (if (atom lst)
      nil
    `(gl-cons ,(car lst)
              ,(gl-list-macro (cdr lst)))))

(defmacro gl-list (&rest args)
  (gl-list-macro args))
