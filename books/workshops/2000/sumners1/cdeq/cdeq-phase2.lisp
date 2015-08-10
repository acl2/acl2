(in-package "ACL2")

;;;; PROVE cdeq+ <-> intr

;;;; the following book contains a cast of definitions we use here..

(include-book "cdeq-defs")

#|----------------------------------------------------------------------------|#

;;;; BEGIN rep, rank, commit, pick, and suff functions ;;;;

(defun rep-thf (f)
  (let ((loc (loc f)))
    (>_ :loc (cond ((= loc 2) 1)
                   ((or (= loc 3) (= loc 5)
                        (= loc 6) (= loc 7)
                        (= loc 8))
                    2)
                   ((or (= loc 10)
                        (and (= loc 9)
                             (equal (old f) (new f))))
                    3)
                   (t 0))
        :itm (xitm f)
        :ctr (xctr f))))

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

 ;; During the development of Version 2.6, a modification was made that
 ;; prevents type-set reasoning from removing true hypotheses.  (See function
 ;; rewrite-atm in source file simplify.lisp.)  While the ACL2 authors believe
 ;; that this modification (developed by Robert Krug) is a good one in general,
 ;; it causes the proof of rep-tvs-rep-thf-reduce below to generate an extra
 ;; case in the proof by induction that causes the proof to fail (even when the
 ;; subgoal hint is appropriately attached to *1/5 instead of *1/4).  The
 ;; following hack causes the rewriter to remove the problematic hypothesis so
 ;; that the original induction takes place and the proof succeeds.  This hack
 ;; is also needed for the two theorems immediately following
 ;; rep-tvs-rep-thf-reduce.
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
  (let ((loc (loc o)))
    (>_ :loc (cond ((or (not (in-range loc 1 22))
                        (= loc 18))
                    0)
                   ((and (= loc 2) (= (bot o) 0)) 2)
                   ((= loc 3) 3)
                   ((or (= loc 9) (= loc 16)
                        (and (= loc 15)
                             (equal (old o) (new o))))
                    4)
                   ((>= loc 19) 5)
                   ((<= loc 5) 1)
                   ((<= loc 7) 2)
                   (t 3))
        :itm (xitm o)
        :ctr (xctr o)
        :dtm (dtm o)
        :xzero (xzero o))))

(defun rep-shr (s)
  (>_ :deq (mend (bot s)
                 (top (age s))
                 (mem s))
      :ctr (xctr s)
      :ret (ret s)
      :clk (clk s)))

(DEFUN rep (st)
  (>_ :shr (rep-shr (shr st))
      :onr (rep-onr (onr st))
      :tvs (rep-tvs (maxf) (tvs st))))


(DEFUN pick (st in) (declare (ignore st)) in)


(defun rank-thf (f)
  (let ((loc (loc f)))
    (cond ((= loc 0) 1)
          ((= loc 1) 0)
          ((in-range loc 2 11)
           (- 15 loc))
          (t 16))))

(defthm rank-thf-type-prescription
  (natp (rank-thf f))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defun rank-tvs (N x)
  (if (zp N) 0
    (+ (rank-thf (<- x N))
       (rank-tvs (1- N) x))))

(in-theory (disable rank-thf))
(in-theory (enable indexp))

(defthm rank-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (rank-tvs i (-> x j v))
                  (rank-tvs i x))))

(defthm rank-tvs-reduces-to-rank-thf
  (implies (indexp i N)
           (iff (> (rank-tvs N x)
                   (rank-tvs N (-> x i v)))
                (> (rank-thf (<- x i))
                   (rank-thf v))))
  :hints (("Subgoal *1/2" :cases ((equal i n)))))

(in-theory (enable rank-thf))
(in-theory (disable indexp))

(defun rank-onr (o)
  (let ((loc (loc o)))
    (cond ((= loc 0) 0)
          ((in-range (loc o) 0 22)
           (- 25 (loc o)))
          (t 26))))

(defthm rank-onr-type-prescription
  (natp (rank-onr o))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(DEFUN rank (st)
  (+ (rank-onr (onr st))
     (rank-tvs (maxf) (tvs st))))



(defun commit-thf (f)
  (case (loc f)
        ((1 2 8 10) t)
        (3 (<= (bot f) (top (old f))))))

(defun commit-onr (o s)
  (case (loc o)
        ((0 3 5 7 9 16 17 22) t)
        ((1 2) (= (bot s) 0))
        (8 (< (top (old o)) (bot o)))
        (14 (equal (old o) (age s)))))

(DEFUN commit (st in)
  (if (ndx in)
      (commit-thf (<- (tvs st) (thf (ndx in))))
    (commit-onr (onr st) (shr st))))



(defun suff-shr (s)
  (and (natp (bot s)) (agep (age s)) (natp (xctr s))))

(defun suff-thf (f s)
  (locase (loc f)
          (3 (implies (= (xctr f) (xctr s))
                      (and (equal (old f) (age s))
                           (iff (xitm f)
                                (> (bot f) (top (old f)))))))
          (8 (and (agep (old f))
                  (natp (itm f))
                  (equal (equal (age s) (old f))
                         (= (xctr f) (xctr s)))
                  (implies (= (xctr f) (xctr s))
                           (natp (xitm f)))
                  (equal (new f) (top+1 (old f)))))
          (10 (= (xitm f) (itm f)))))

(defun suff-onr (o s)
  (locase (loc o)
          (1 (not (xctr o)))
          (2 (and (= (bot o) (bot s))
                  (not (xctr o))
                  (implies (= (bot o) 0)
                           (not (xitm o)))))
          (3 (and (xzero o)
                  (not (xitm o))
                  (not (xctr o))))
          (5 (= (bot o) (1- (bot s))))
          (7 (and (if (= (xctr o) (xctr s))
                      (= (bot o) (top (age s)))
                    (if (xctr o)
                        (not (= (bot o) (top (age s))))
                      (implies (= (bot o) (top (age s)))
                               (xitm o))))
                  (implies (and (< (bot o) (top (age s)))
                                (xitm o))
                           (xctr o))
                  (= (bot o) (bot s))))
          (8 (implies (> (bot o) (top (old o)))
                      (and (xitm o) (not (xctr o)))))
          (9 (= (xitm o) (itm o)))
          (10 (>= (top (age s)) (bot s)))
          (14 (and (xctr o) (= (bot s) 0)
                   (xitm o) (agep (old o))
                   (not (xzero o))
                   (equal (new o)
                          (tag+1 (top=0 (old o))))
                   (equal (= (xctr s) (xctr o))
                          (equal (age s) (old o)))))
          (16 (= (xitm o) (itm o)))
          (17 (and (= (bot s) 0)
                   (agep (new o))
                   (not (xzero o))
                   (implies (xitm o)
                            (and (xctr o)
                                 (not (= (xctr s)
                                         (xctr o)))))))
          (20 (= (bot o) (bot s)))
          (22 (and (= (<- (mem s) (bot s)) (dtm o))
                   (= (bot o) (1+ (bot s)))
                   (<= (top (age s)) (bot s))))))

(DEFUN suff (st in)
  (and (suff-shr (shr st))
       (if (ndx in)
           (suff-thf (<- (tvs st) (thf (ndx in)))
                     (shr st))
         (suff-onr (onr st) (shr st)))))

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

(defthm linear-factoid1
  (iff (< (+ x y) (+ x z))
       (< y z)))

(defthm linear-factoid2
  (iff (< (+ y x) (+ z x))
       (< y z)))

(DEFTHM >>-stutter2
  (implies (and (suff st in)
                (not (commit st in)))
           (e0-ord-< (rank (cdeq+ st in))
                     (rank st)))
  :hints (("Goal" :in-theory
           (disable commutativity-of-+))))

(DEFTHM >>-match
  (implies (and (suff st in)
                (commit st in))
           (equal (rep (cdeq+ st in))
                  (intr (rep st) (pick st in))))
  :hints (("Goal" :in-theory (disable (s)))))

;;;; END WEB proof -- labeling, stuttering, and matching ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant defintion ;;;;

;; a few more macros for predicates for defining the
;; current "state" of the deque.

(defmacro norm? (s) `(and (>= (bot ,s) (top (age ,s)))
                          (not (xsafe ,s))))
(defmacro vald? (s) `(> (bot ,s) (top (age ,s))))
(defmacro safe? (s) `(xsafe ,s))
(defmacro takn? (s) `(< (bot ,s) (top (age ,s))))

(defun inv-shr (s)
  (and (natp (bot s))
       (agep (age s))
       (natp (xctr s))))

(defun inv-thf (f s)
  (locase (loc f)
          ((2 8) (and (agep (old f))
                      (natp (xctr f))
                      (if (equal (age s) (old f))
                          (= (xctr f) (xctr s))
                        (and (age<< (old f) (age s))
                             (< (xctr f) (xctr s))))))
          (3 (implies (equal (old f) (age s))
                      (if (> (bot f) (top (old f)))
                          (and (= (xitm f)
                                  (val (<- (mem s) (top (old f)))))
                               (or (vald? s) (safe? s)))
                        (not (xitm f)))))
          ((5 8) (implies (equal (age s) (old f))
                          (or (vald? s) (safe? s))))
          (5 (implies (equal (old f) (age s))
                      (= (xitm f)
                         (val (<- (mem s) (top (old f)))))))
          ((6 8) (and (natp (itm f))
                      (implies (equal (old f) (age s))
                               (= (xitm f) (itm f)))))
          (7 (equal (new f) (old f)))
          (8 (equal (new f) (top+1 (old f))))
          (9 (implies (equal (old f) (new f))
                      (equal (xitm f) (itm f))))
          (10 (equal (xitm f) (itm f)))))

(defun assume-onr (o s)
  (locase (loc o)
          (5 (and (equal (bot o) (1- (bot s)))
                  (not (xsafe s))))
          (10 (and (xsafe s)
                   (<= (bot s) (top (age s)))))
          (14 17 (and (agep (old o))
                      (equal (tag (new o))
                             (1+ (tag (old o))))
                      (= (tag (old o))
                         (tag (age s)))))
          (20 (and (= (bot o) (bot s)) (norm? s)))
          (22 (equal (bot o) (1+ (bot s))))))


(defun inv-tvs (x s N)
  (or (zp N)
      (and (inv-thf (<- x N) s)
           (inv-tvs x s (1- N)))))

(in-theory (disable inv-thf))
(in-theory (enable indexp))

(defthm inv-tvs-unaffected-addresses
  (implies (and (integerp i) (integerp j) (< i j))
           (equal (inv-tvs (-> x j v) s i)
                  (inv-tvs x s i))))

(defthm inv-tvs-implies-inv-thf
  (implies (and (indexp i N)
                (inv-tvs x s N))
           (inv-thf (<- x i) s))
  :hints (("Goal" :in-theory (enable posp)))
  :rule-classes nil)

(in-theory (enable inv-thf))
(in-theory (disable indexp))

(defun inv-onr (o s)
  (and (in-range (loc o) 0 22)
       (locase (loc o)
               ((0 3) 16 (18 22)
                (equal (xzero o) (= (bot s) 0)))
               ((4 14) 17 (not (xzero o)))
               (15 (equal (equal (old o) (new o))
                          (xzero o)))
               (9 (> (bot o) (top (old o))))
               (3 (= (bot o) 0))
               ((0 5) 9 16 (18 22)
                (and (not (xctr o)) (norm? s)))
               ((2 4) (= (bot o) (bot s)))
               (2 (implies (= (bot o) 0)
                           (not (xitm o))))
               (3 (not (xitm o)))
               ((4 5) (> (bot s) 0))
               (5 (= (bot o) (1- (bot s))))
               ((6 10) (= (bot o) (bot s)))
               ((6 13) (implies (xctr o)
                                (and (natp (xctr o))
                                     (>= (xctr s) (xctr o)))))
               (6 (implies (xitm o)
                           (= (xitm o)
                              (val (<- (mem s) (bot o))))))
               ((6 7) (if (= (xctr o) (xctr s))
                          (= (bot o) (top (age s)))
                        (implies (xctr o) (takn? s))))
               ((6 7) (implies (>= (bot o) (top (age s)))
                               (xitm o)))
               ((6 7) (implies (vald? s) (not (xctr o))))
               ((6 7) (iff (and (xsafe s) (xitm o))
                           (xctr o)))
               ((6 7) (implies (and (takn? s) (xitm o))
                               (and (xctr o)
                                    (> (xctr s) (xctr o)))))
               ((7 16) (implies (xitm o)
                                (= (xitm o) (itm o))))
               (8 (if (> (bot o) (top (old o)))
                      (and (xitm o) (not (xctr o)))
                    (if (= (top (old o)) (bot o))
                        (and (xitm o) (xctr o))
                      (implies (xitm o)
                               (and (xctr o)
                                    (> (xctr s) (xctr o)))))))
               (8 (iff (<= (bot o) (top (old o)))
                       (xsafe s)))
               (8 (if (> (bot o) (top (old o)))
                      (>= (bot o) (top (age s)))
                    (>= (top (age s)) (bot o))))
               ((8 13) (implies (= (bot o) (top (old o)))
                                (and (xctr o)
                                     (if (= (xctr s) (xctr o))
                                         (equal (age s) (old o))
                                       (age<< (old o) (age s))))))
               ((8 17) (agep (old o)))
               (9 (14 16) (xitm o))
               ((10 13) (if (= (top (old o)) (bot o))
                            (and (xitm o) (xctr o))
                          (implies (xitm o)
                                   (and (xctr o)
                                        (> (xctr s) (xctr o))))))
               (10 (and (xsafe s)
                        (>= (top (age s)) (bot s))))
               ((11 17) (= (bot s) 0))
               (12 (equal (new o) (top=0 (old o))))
               ((13 14) (equal (new o) (tag+1 (top=0 (old o)))))
               ((8 14) 17 (= (tag (old o)) (tag (age s))))
               (14 (and (xctr o)
                        (if (= (xctr s) (xctr o))
                            (equal (age s) (old o))
                          (and (age<< (old o) (age s))
                               (> (xctr s) (xctr o))))))
               (15 (and (> (xctr s) (xctr o))
                        (if (equal (old o) (new o))
                            (and (not (xsafe s))
                                 (not (xctr o))
                                 (equal (top (age s)) 0))
                          (and (xctr o)
                               (= (tag (old o)) (tag (age s)))
                               (equal (new o) (tag+1 (top=0 (old o))))))))
               (17 (and (implies (xitm o)
                                 (and (xctr o)
                                      (> (xctr s) (xctr o))))
                        (equal (new o) (tag+1 (top=0 (old o))))))
               ((20 21) (= (bot o) (bot s)))
               ((21 22) (= (<- (mem s) (bot s)) (dtm o)))
               (22      (= (bot o) (1+ (bot s)))))))

(defun assume-thf (f s)
  (locase (loc f)
          (8 (and (agep (old f))
                  (natp (xctr f))
                  (equal (new f) (top+1 (old f)))
                  (implies (equal (age s) (old f))
                           (or (vald? s) (safe? s)))))))

(DEFUN inv (st)
  (and (inv-shr (shr st))
       (inv-tvs (tvs st) (shr st) (maxf))
       (inv-onr (onr st) (shr st))))

;;;; END invariant definition ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN invariant proof ;;;;

(defthm thf-inv-shr-thm
  (implies (and (inv-shr s)
                (inv-thf f s))
           (inv-shr (i-thf-s f s))))

(defthm thf-inv-thf-thm
  (implies (and (inv-shr s)
                (inv-thf f s))
           (inv-thf (i-thf-f f s)
                    (i-thf-s f s))))

(defthm thf-inv-other-thf-thm
  (implies (and (inv-shr s)
                (inv-thf f s)
                (inv-thf g s))
           (inv-thf g (i-thf-s f s))))

(defthm onr-inv-thf-thm
  (implies (and (inv-shr s)
                (assume-onr o s)
                (inv-thf f s))
           (inv-thf f (i-onr-s o s))))


(defthm onr-inv-shr-thm
  (implies (and (inv-shr s)
                (inv-onr o s))
           (inv-shr (i-onr-s o s))))

(defthm onr-inv-onr-thm
  (implies (and (inv-shr s)
                (inv-onr o s))
           (inv-onr (i-onr-o p d o s)
                    (i-onr-s o s))))

(defthm thf-inv-onr-thm
  (implies (and (inv-shr s)
                (inv-onr o s)
                (assume-thf f s))
           (inv-onr o (i-thf-s f s))))


(defthm onr-inv-implies-assume-onr
  (implies (and (inv-shr s)
                (inv-onr o s))
           (assume-onr o s)))

(defthm thf-inv-implies-assume-thf
  (implies (and (inv-shr s)
                (inv-thf f s))
           (assume-thf f s)))

(in-theory (enable indexp))

(defthm thf-inv-implies-tvs-inv
  (implies (and (indexp i N)
                (inv-tvs x s N)
                (inv-shr s)
                (inv-thf f s))
           (inv-tvs (-> x i (i-thf-f f s))
                    (i-thf-s f s)
                    N))
  :hints (("Goal" :in-theory
           (disable i-thf-f i-thf-s inv-shr inv-thf))
          ("Subgoal *1/6" :cases ((equal i n)))))

(in-theory (disable indexp))

(defthm onr-inv-implies-tvs-inv
  (implies (and (inv-shr s)
                (inv-onr o s)
                (inv-tvs x s N))
           (inv-tvs x (i-onr-s o s) N))
  :hints (("Goal" :in-theory
           (disable i-onr-s inv-shr inv-onr inv-thf))))

(defthm inv-tvs-implies-inv-thf-maxf
  (implies (and (indexp i (maxf))
                (inv-tvs x s (maxf)))
           (inv-thf (<- x i) s))
  :hints (("Goal" :use
           (:instance inv-tvs-implies-inv-thf
                      (N (maxf))))))

(DEFTHM >>-invariant-persistent
  (implies (inv st) (inv (cdeq+ st in)))
  :hints (("Goal" :in-theory
           (disable i-thf-f i-thf-s i-onr-o i-onr-s
                    inv-thf inv-shr inv-onr))))


(defthm inv-shr-implies-suff-shr
  (implies (inv-shr s) (suff-shr s)))

(defthm inv-thf-implies-suff-thf
  (implies (and (inv-shr s) (inv-thf f s))
           (suff-thf f s)))

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
