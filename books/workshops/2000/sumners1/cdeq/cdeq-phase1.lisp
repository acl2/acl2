(in-package "ACL2")

;;;; PROVE cdeq+ <-> cdeq

;;;; we will need a book on record ops and theorems

(include-book "cdeq-defs")

#|----------------------------------------------------------------------------|#

;;;; BEGIN rep, rank, commit, pick, and suff functions ;;;;

(defun rep-thf (f)
  (>_ :loc (loc f)
      :old (old f)
      :bot (bot f)
      :ret (ret f)
      :new (new f)
      :itm (itm f)))

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

(defthm rep-tvs-rep-thf-reduce
  (implies (indexp i N)
           (equal (rep-tvs N (-> x i f))
                  (-> (rep-tvs N x) i (rep-thf f))))
  :hints (("Subgoal *1/4" :cases ((equal i n)))
          ("Subgoal *1/3" :in-theory (enable posp))))

(defthm rep-tvs-absorbs-update
  (implies (and (indexp i N)
                (equal (rep-thf (<- x i)) v))
           (equal (-> (rep-tvs N x) i v)
                  (rep-tvs N x)))
  :hints (("Subgoal *1/4" :cases ((equal i n)))
          ("Subgoal *1/3" :in-theory (enable posp))))

(defthm rep-tvs-get-is-rep-thf
  (implies (indexp i N)
           (equal (<- (rep-tvs N x) i)
                  (rep-thf (<- x i))))
  :hints (("Subgoal *1/4" :cases ((equal i n)))
          ("Subgoal *1/3" :in-theory (enable posp))))

(in-theory (disable indexp))
(in-theory (enable rep-thf))

(defun rep-onr (o)
  (>_ :loc (loc o)
      :old (old o)
      :bot (bot o)
      :ret (ret o)
      :new (new o)
      :itm (itm o)
      :dtm (dtm o)))

(defun rep-shr (s)
  (>_ :mem (mem s)
      :age (age s)
      :bot (bot s)
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
           (equal (rep (cdeq+ st in))
                  (rep st))))

(DEFTHM >>-stutter2
  (implies (and (suff st in)
                (not (commit st in)))
           (e0-ord-< (rank (cdeq+ st in))
                     (rank st))))

(DEFTHM >>-match
  (implies (and (suff st in)
                (commit st in))
           (equal (rep (cdeq+ st in))
                  (cdeq (rep st) (pick st in))))
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
  (implies (inv st) (inv (cdeq+ st in))))

(DEFTHM >>-invariant-sufficient
  (implies (inv st) (suff st in)))

;;;; END invariant proof ;;;;

#|----------------------------------------------------------------------------|#
