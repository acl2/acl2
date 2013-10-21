(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")

(defthm nth-index-map-rcfn
  (implies (and (<= 0 index)
                (< index (len p)))
           (equal (nth index (map-rcfn p))
                  (rcfn (nth index p)))))

(defthm nth-index-map-rcfn-refinement
  (implies (and (<= 0 index)
                (< index (len p1)))
  (equal (nth index (map-rcfn-refinement p1 p2))
         (rcfn (next-gte (nth index p1) p2)))))

(encapsulate
 ()
 (local (include-book "rcfn-next-gte-close"))
 (defthm rcfn-next-gte-close
   (implies (and (partitionp p2)
                 (standard-numberp (car p2))
                 (standard-numberp (car (last p2)))
                 (i-small (mesh p2))
                 (<= (car p2) x)
                 (<= x (car (last p2)))
                 (realp x))
            (i-close (rcfn x) (rcfn (next-gte x p2))))
   :rule-classes nil))

(encapsulate
 ()
 (local (include-book "i-close-implies-abs-difference-small"))
 (defthm i-close-implies-abs-difference-small
   (implies (and (realp r)
                 (standard-numberp r)
                 (< 0 r)
                 (realp x)
                 (realp y)
                 (i-close x y))
            (< (abs (- x y)) r))))

(defthm next-gte-keeps-rcfn-below-positive-standard
  (implies (and (partitionp p2)
                (standard-numberp (car p2))
                (standard-numberp (car (last p2)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r)
                (<= (car p2) x)
                (<= x (car (last p2)))
                (realp x))
           (< (abs (- (rcfn x)
                      (rcfn (next-gte x p2))))
              r))
  :hints (("Goal" :use rcfn-next-gte-close
           :in-theory (disable abs partitionp2 mesh next-gte)))
  ;; See comment below, where this lemma is USEd.
  :rule-classes nil)

;;; This could be moved to riemann-lemmas.lisp, but it seems a bit
;;; dangerous to have around in general since presumably we will
;;; ultimately see many member relations holding without partitionp
;;; being involved, and hence this rule could slow down proofs.
(defthm member-partition-forward-to-realp
  (implies (and (member x p)
                (partitionp p))
           (realp x))
  :rule-classes :forward-chaining)

(defthm map-rcfn-close-to-map-rcfn-refinement-crux
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r)
                (member x p1))
           (< (abs (- (rcfn x)
                      (rcfn (next-gte x p2))))
              r))
  :hints (("Goal" :in-theory (disable abs next-gte mesh)
           ;; It seems necessary to USE the following lemma, even with
           ;; last and member disabled, rather than rewriting with it.
           :use next-gte-keeps-rcfn-below-positive-standard)))

(defthm map-rcfn-close-to-map-rcfn-refinement-lemma
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r)
                (<= 0 index)
                (< index (len p1)))
           (< (abs (- (rcfn (nth index p1))
                      (rcfn (next-gte (nth index p1) p2))))
              r))
  :hints (("Goal" :in-theory (disable abs mesh strong-refinement-p nth
                                      map-rcfn map-rcfn-refinement))))

(defthm map-rcfn-close-to-map-rcfn-refinement
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r)
                (<= 0 index)
                (< index (len p1)))
           (< (abs (- (nth index (map-rcfn p1))
                      (nth index (map-rcfn-refinement p1 p2))))
              r))
  :hints (("Goal" :in-theory (disable abs mesh strong-refinement-p nth
                                      map-rcfn map-rcfn-refinement))))
