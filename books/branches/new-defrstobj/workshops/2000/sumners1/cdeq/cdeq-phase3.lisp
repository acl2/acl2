(in-package "ACL2")

;;;; PROVE intr+ <-> intr

;;;; we will need a book on record ops and theorems

(include-book "cdeq-defs")

#|----------------------------------------------------------------------------|#

;;;; BEGIN rep, rank, commit, pick, and suff functions ;;;;

(defun rep-thf (f)
  (>_ :loc (loc f)
      :itm (itm f)
      :ctr (ctr f)))

(defthm additive-factoid2
  (implies (and (integerp x) (integerp y))
           (equal (+ x (- x) y) y)))

(defun rep-tvs (N x)
  (if (zp N) ()
    (-> (rep-tvs (1- N) x) N
        (rep-thf (<- x N)))))

(in-theory (disable rep-thf))
(in-theory (enable indexp))

(defthm rep-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (rep-tvs i (-> x j v))
                  (rep-tvs i x))))

(encapsulate
 ()

 ;; See the analogous comment in cdeq-phase2.lisp; this seems to be an entirely
 ;; analogous situation.
 (local
  (defthm hack
    (implies (and (< 0 i)
                  (<= i n))
             (< 0 n))))

 (defthm rep-tvs-rep-thf-reduce
   (implies (indexp i N)
            (equal (rep-tvs N (-> x i f))
                   (-> (rep-tvs N x) i (rep-thf f))))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/4" :cases ((equal i n)))))

 (defthm rep-tvs-absorbs-update
   (implies (and (indexp i N)
                 (equal (rep-thf (<- x i)) v))
            (equal (-> (rep-tvs N x) i v)
                   (rep-tvs N x)))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/4" :cases ((equal i n)))))

 (defthm rep-tvs-get-is-rep-thf
   (implies (indexp i N)
            (equal (<- (rep-tvs N x) i)
                   (rep-thf (<- x i))))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/4" :cases ((equal i n))))))

(in-theory (disable indexp))
(in-theory (enable rep-thf))

(defun rep-onr (o)
  (>_ :loc (loc o)
      :ctr (ctr o)
      :itm (itm o)
      :dtm (dtm o)
      :xzero (xzero o)))

(defun rep-shr (s)
  (>_ :deq (deq s)
      :ctr (ctr s)
      :ret (ret s)
      :clk (clk s)))

(DEFUN rep (st)
  (>_ :shr (rep-shr (shr st))
      :onr (rep-onr (onr st))
      :tvs (rep-tvs (maxf) (tvs st))))


(DEFUN pick (st in) (declare (ignore st)) in)

(DEFUN rank (st) (declare (ignore st)) 0)

(DEFUN commit (st in) (declare (ignore st in)) t)

(DEFUN suff (st in) (declare (ignore st in)) t)


;;;; END rep, rank, commit, pick, and suff functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN refinement >> proof -- labeling, stuttering, and matching ;;;;

(DEFTHM >>-well-founded
  (e0-ordinalp (rank s)))  ;; (bounded-ordp (rank s) 1)

(DEFTHM >>-label
  (equal (label (rep st)) (label st)))

(DEFTHM >>-stutter1
  (implies (and (suff st in)
                (not (commit st in)))
           (equal (rep (intr+ st in))
                  (rep st))))

(DEFTHM >>-stutter2
  (implies (and (suff st in)
                (not (commit st in)))
           (e0-ord-< (rank (intr+ st in))
                     (rank st))))

(DEFTHM >>-match
  (implies (and (suff st in)
                (commit st in))
           (equal (rep (intr+ st in))
                  (intr (rep st) (pick st in))))
  :hints (("Goal" :in-theory (disable (s))
           :expand ((:free (x) (rep x))
                    (:free (x) (rep-shr x))
                    (:free (x) (rep-onr x))
                    (:free (x) (rep-thf x))))))

;;;; END WEB proof -- labeling, stuttering, and matching ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant defintion ;;;;

(DEFUN inv (st) (declare (ignore st)) t)

;;;; END invariant definition ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant proof ;;;;

(DEFTHM >>-invariant-persistent
  (implies (inv st) (inv (intr+ st in))))

(DEFTHM >>-invariant-sufficient
  (implies (inv st) (suff st in)))

;;;; END invariant proof ;;;;

#|----------------------------------------------------------------------------|#
