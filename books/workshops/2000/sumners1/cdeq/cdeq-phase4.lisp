(in-package "ACL2")

;;;; PROVE intr+ >> spec

;;;; we will need a book on record ops and theorems

(include-book "cdeq-defs")

#|----------------------------------------------------------------------------|#

;;;; BEGIN rep, rank, commit, pick, and suff functions ;;;;

(defun rep-thf (f)
  (and (= (loc f) 3) (itm f)))

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

(defun rep-onr (o s)
  (>_ :st8 (cond ((= (loc o) 5) 'push)
                 ((or (= (loc o) 2)
                      (= (loc o) 3)
                      (= (loc o) 4))
                  'pop)
                 (t 'idle))
      :itm (and (or (= (loc o) 4)
                    (and (or (= (loc o) 2)
                             (= (loc o) 3))
                         (implies (ctr o)
                                  (= (ctr o) (ctr s)))))
                (itm o))
      :dtm (dtm o)))

(defun rep-shr (s)
  (>_ :deq (deq s)
      :ret (ret s)
      :clk (clk s)))

(DEFUN rep (st)
  (>_ :shr (rep-shr (shr st))
      :onr (rep-onr (onr st) (shr st))
      :tvs (rep-tvs (maxf) (tvs st))))


(defun rank>-thf (f)
  (let ((loc (loc f)))
    (cond ((= loc 1) 3)
          ((= loc 2) 2)
          ((= loc 0) 0)
          (t 1))))

(defun rank>-tvs (N x)
  (if (zp N) 0
    (+ (rank>-thf (<- x N))
       (rank>-tvs (1- N) x))))

(in-theory (disable rank>-thf))
(in-theory (enable indexp))

(defthm rank>-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (rank>-tvs i (-> x j v))
                  (rank>-tvs i x))))

(defthm rank>-tvs-reduces-to-rank-thf
  (implies (indexp i N)
           (iff (> (rank>-tvs N x)
                   (rank>-tvs N (-> x i v)))
                (> (rank>-thf (<- x i))
                   (rank>-thf v))))
  :hints (("Subgoal *1/2" :cases ((equal i n)))))

(in-theory (enable rank>-thf))
(in-theory (disable indexp))


(defun rank0-thf (f)
  (let ((loc (loc f)))
    (cond ((= loc 1) 0)
          ((= loc 2) 3)
          ((= loc 0) 1)
          (t 2))))

(defun rank0-tvs (N x)
  (if (zp N) 0
    (+ (rank0-thf (<- x N))
       (rank0-tvs (1- N) x))))

(in-theory (disable rank0-thf))
(in-theory (enable indexp))

(defthm rank0-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (rank0-tvs i (-> x j v))
                  (rank0-tvs i x))))

(defthm rank0-tvs-reduces-to-rank-thf
  (implies (indexp i N)
           (iff (> (rank0-tvs N x)
                   (rank0-tvs N (-> x i v)))
                (> (rank0-thf (<- x i))
                   (rank0-thf v))))
  :hints (("Subgoal *1/2" :cases ((equal i n)))))

(in-theory (enable rank0-thf))
(in-theory (disable indexp))


(defun miss-count (tvs N ctr)
  (cond ((zp N) 0) ;; return 1 to make miss-count > 0
        ((and (xgo (<- tvs N))
              (equal (ctr (<- tvs N)) ctr))
         (miss-count tvs (1- N) ctr))
        (t (1+ (miss-count tvs (1- N) ctr)))))

(in-theory (enable indexp))

(defthm miss-count-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (miss-count (-> x j v) i ctr)
                  (miss-count x i ctr))))

(encapsulate
 ()

 ;; We seem to have a situation here analogous to the one above that also
 ;; needed this hack lemma.
 (local
  (defthm hack
    (implies (and (< 0 i)
                  (<= i n))
             (< 0 n))))

 (defthm equal-miss-count-->-miss-count-1
   (implies (and (indexp i N)
                 (xgo val)
                 (equal (ctr val) ctr)
                 (not (equal (ctr (<- tvs i)) ctr)))
            (equal (miss-count (-> tvs i val) N ctr)
                   (1- (miss-count tvs N ctr))))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/7" :cases ((equal i n)))
           ("Subgoal *1/4" :cases ((equal i n)))))

 (defthm equal-miss-count-xgo-miss-count-1
   (implies (and (indexp i N)
                 (xgo val)
                 (equal (ctr val) ctr)
                 (not (xgo (<- tvs i))))
            (equal (miss-count (-> tvs i val) N ctr)
                   (1- (miss-count tvs N ctr))))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/7" :cases ((equal i n)))
           ("Subgoal *1/4" :cases ((equal i n)))))

 (defthm equal-miss-count-miss-count-ctr-unchanged
   (implies (and (indexp i N)
                 (equal (xgo val) (xgo (<- tvs i)))
                 (equal (ctr val) (ctr (<- tvs i))))
            (equal (miss-count (-> tvs i val) N ctr)
                   (miss-count tvs N ctr)))
   :hints (("Goal" :in-theory (enable posp))
           ("Subgoal *1/7" :cases ((equal i n)))
           ("Subgoal *1/4" :cases ((equal i n)))
           ("Subgoal *1/4.1''" :expand (miss-count (s i val tvs)
                                                   i (g :ctr val))))))

(in-theory (disable indexp))

(defun rank-onr (o)
  (let ((loc (loc o)))
    (cond ((= loc 2) 5)
          ((= loc 3) 4)
          ((= loc 4) 3)
          ((= loc 0) 2)
          ((or (= loc 1)
               (= loc 5)) 1)
          (t 3))))

(DEFUN rank (st)
  (if (consp (deq (shr st)))
      (cons (cons (rank-onr (onr st))
                  (miss-count (tvs st) (maxf)
                              (ctr (shr st))))
            (rank>-tvs (maxf) (tvs st)))
    (cons (rank-onr (onr st))
          (rank0-tvs (maxf) (tvs st)))))


(DEFUN commit (st in)
  (let ((thf (<- (tvs st)
                 (thf (ndx in))))
        (onr (onr st))
        (shr (shr st)))
    (if (ndx in)
        (case (loc thf) (3 t)
              (1 (atom (deq shr)))
              (2 (and (itm thf)
                      (= (ctr thf) (ctr shr)))))
      (case (loc onr) ((1 4 5) t)
            (0 (psh in))
            (3 (implies (itm onr)
                        (and (ctr onr)
                             (not (= (ctr onr)
                                     (ctr shr))))))))))

(DEFUN pick (st in)
  (let ((onr (onr st))
        (shr (shr st))
        (thf (<- (tvs st)
                 (thf (ndx in)))))
    (>_ :ndx (ndx in)
        :psh (and (not (= (loc onr) 1))
                  (psh in))
        :stl (and (not (= (loc onr) 4))
                  (= (ctr onr) (ctr shr))
                  (= (loc thf) 2)
                  (itm thf)
                  (= (ctr thf) (ctr shr)))
        :dtm (dtm in))))

(defun suff-shr (s)
  (and (true-listp (deq s))
       (natp (ctr s))))

(defun suff-thf-match (f s o)
  (locase (loc f)
          (2 (implies (and (itm f)
                           (= (ctr s) (ctr f)))
                      (if (atom (deq s))
                          (and (= (itm f) (itm o))
                               (= (ctr o) (ctr s)))
                        (= (itm f) (get-top (deq s))))))
          (3 (itm f))))

(defun suff-thf (f s o)
  (and (implies (and (= (loc f) 0)
                     (xgo f))
                (< (ctr f) (ctr s)))
       (suff-thf-match f s o)))

(defun suff-onr (o s)
  (and (in-range (loc o) 0 5)
       (implies (ctr o)
                (<= (ctr o) (ctr s)))
       (locase (loc o)
               (0 1 4 5 (not (ctr o)))
               ((2 3) (implies (= (ctr o) (ctr s))
                               (and (atom (deq s))
                                    (itm o))))
               (4 (itm o)))))

(DEFUN suff (st in)
  (and (suff-shr (shr st))
       (suff-onr (onr st) (shr st))
       (suff-thf (<- (tvs st) (thf (ndx in)))
                 (shr st) (onr st))))

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
                  (rep st)))
  :hints (("Goal" :in-theory (disable suff))))

(DEFTHM >>-stutter2
  (implies (and (suff st in)
                (not (commit st in)))
           (e0-ord-< (rank (intr+ st in))
                     (rank st)))
  :hints (("Goal" :in-theory (disable suff-onr suff-shr
                                      suff-thf-match))))

(DEFTHM >>-match
  (implies (and (suff st in)
                (commit st in))
           (equal (rep (intr+ st in))
                  (spec (rep st) (pick st in)))))

;;;; END WEB proof -- labeling, stuttering, and matching ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant defintion ;;;;

(defthm get-top-nil-implies-atom
  (implies (not (get-top x)) (not (consp x))))

(defthm one-eltp-implies-not-cdr
  (implies (one-eltp x) (not (consp (cdr x))))
  :hints (("Goal" :in-theory (enable one-eltp))))

(defun inv-shr (s)
  (and (true-listp (deq s))
       (natp (ctr s))))

(defun inv-thf (f s o)
  (and (in-range (loc f) 0 3)
       (natp (ctr f))
       (<= (ctr f) (ctr s))
       (locase (loc f)
               (0 (implies (xgo f)
                           (< (ctr f) (ctr s))))
               (2 (if (itm f)
                      (implies (= (ctr s) (ctr f))
                               (if (atom (deq s))
                                   (and (= (itm f) (itm o))
                                        (= (ctr o) (ctr s)))
                                 (= (itm f) (get-top (deq s)))))
                    (not (xgo f))))
               (3 (and (itm f)
                       (< (ctr f) (ctr s)))))))

(defun inv-onr (o s)
  (and (in-range (loc o) 0 5)
       (implies (ctr o)
                (<= (ctr o) (ctr s)))
       (locase (loc o)
               (0 1 4 5 (not (ctr o)))
               ((2 3) (implies (= (ctr o) (ctr s))
                               (and (atom (deq s))
                                    (itm o))))
               (4 (itm o)))))

(defun inv-tvs (x s o N)
  (or (zp N)
      (and (inv-thf (<- x N) s o)
           (inv-tvs x s o (1- N)))))

(in-theory (disable inv-thf))
(in-theory (enable indexp))

(defthm inv-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (inv-tvs (-> x j v) s o i)
                  (inv-tvs x s o i))))

(defthm inv-tvs-implies-inv-thf
  (implies (and (indexp i N)
                (inv-tvs x s o N))
           (inv-thf (<- x i) s o))
  :hints (("Goal" :in-theory (enable posp)))
  :rule-classes nil)

(in-theory (enable inv-thf))
(in-theory (disable indexp))

(DEFUN inv (st)
  (and (inv-shr (shr st))
       (inv-onr (onr st) (shr st))
       (inv-tvs (tvs st) (shr st)
                (onr st) (maxf))))

;;;; END invariant definition ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant proof ;;;;

(defthm thf-inv-shr-thm
  (implies (and (inv-shr s)
                (inv-thf f s o))
           (inv-shr (r-thf-s f s))))

(defthm thf-inv-thf-thm
  (implies (and (inv-shr s)
                (inv-thf f s o))
           (inv-thf (r-thf-f f s)
                    (r-thf-s f s) o)))

(defthm thf-inv-other-thf-thm
  (implies (and (inv-shr s)
                (inv-thf f s o)
                (inv-thf g s o))
           (inv-thf g (r-thf-s f s) o)))

(defthm onr-inv-shr-thm
  (implies (and (inv-shr s)
                (inv-onr o s))
           (inv-shr (r-onr-s o s))))

(defthm onr-inv-onr-thm
  (implies (and (inv-shr s)
                (inv-onr o s))
           (inv-onr (r-onr-o p d o s)
                    (r-onr-s o s))))

(defthm thf-inv-onr-thm
  (implies (and (inv-shr s)
                (inv-onr o s)
                (inv-thf f s o))
           (inv-onr o (r-thf-s f s))))

(defthm onr-inv-thf-thm
  (implies (and (inv-shr s)
                (inv-onr o s)
                (inv-thf f s o))
           (inv-thf f (r-onr-s o s)
                    (r-onr-o p d o s)))
  :hints (("Goal" :in-theory (enable one-eltp))))


(in-theory (enable indexp))

(defthm thf-inv-implies-tvs-inv
  (implies (and (indexp i N)
                (inv-tvs x s o N)
                (inv-shr s)
                (inv-thf f s o))
           (inv-tvs (-> x i (r-thf-f f s))
                    (r-thf-s f s) o
                    N))
  :hints (("Goal" :in-theory
           (disable r-thf-f r-thf-s inv-shr inv-thf))
          ("Subgoal *1/6" :cases ((equal i n)))))

(in-theory (disable indexp))

(defthm onr-inv-implies-tvs-inv
  (implies (and (inv-shr s)
                (inv-onr o s)
                (inv-tvs x s o N))
           (inv-tvs x (r-onr-s o s)
                    (r-onr-o p d o s) N))
  :hints (("Goal" :in-theory
           (disable r-onr-s r-onr-o
                    inv-shr inv-onr inv-thf))))

(defthm inv-tvs-implies-inv-thf-maxf
  (implies (and (indexp i (maxf))
                (inv-tvs x s o (maxf)))
           (inv-thf (<- x i) s o))
  :hints (("Goal" :use
           (:instance inv-tvs-implies-inv-thf
                      (N (maxf))))))

(DEFTHM >>-invariant-persistent
  (implies (inv st) (inv (intr+ st in)))
  :hints (("Goal" :in-theory
           (disable r-thf-f r-thf-s r-onr-o r-onr-s
                    inv-thf inv-shr inv-onr
                    thf-inv-shr-thm)
           :use (:instance thf-inv-shr-thm
                           (f (<- (tvs st) (thf (ndx in))))
                           (s (shr st))
                           (o (onr st))))))

(defthm inv-shr-implies-suff-shr
  (implies (inv-shr s) (suff-shr s)))

(defthm inv-thf-implies-suff-thf
  (implies (and (inv-shr s) (inv-thf f s o))
           (suff-thf f s o)))

(defthm inv-onr-implies-suff-onr
  (implies (and (inv-shr s) (inv-onr o s))
           (suff-onr o s)))

(DEFTHM >>-invariant-sufficient
  (implies (inv st) (suff st in))
  :hints (("Goal" :in-theory
           (disable inv-thf inv-shr inv-onr
                    suff-thf suff-shr suff-onr))))

;;;; END invariant proof ;;;;

#|----------------------------------------------------------------------------|#
