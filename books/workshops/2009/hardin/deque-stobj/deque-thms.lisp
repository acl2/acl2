#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| Some theorems about the deque defined in deque-stobj.lisp                 |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "deque-stobj")
(include-book "arithmetic-5/top" :dir :system)


(defthm update-hd--hd-minus-1--thm
  (implies (not (= (hd dqst) 0))
           (= (HD (UPDATE-HD (+ -1 (HD DQST)) DQST)) (- (hd dqst) 1))))

(defthm update-hd--hd-plus-1--thm
  (implies (< (hd dqst) (tl dqst))
           (= (HD (UPDATE-HD (+ 1 (HD DQST)) DQST)) (+ (hd dqst) 1))))

(defthm hd--update-tl--thm
  (= (HD (UPDATE-TL I dqst)) (hd dqst)))

(defthm nth-hd--update-nth-tl--thm
  (= (NTH *HD* (UPDATE-TL I dqst)) (nth *hd* dqst)))

(defthm tl--update-hd--thm
  (= (TL (UPDATE-HD I dqst)) (tl dqst)))

(defthm nth-tl--update-nth-hd--thm
  (= (NTH *TL* (UPDATE-HD I dqst)) (nth *tl* dqst)))

(defthm tl--update-tl--thm
  (= (TL (UPDATE-TL I dqst)) i))

(defthm hd--update-hd--thm
  (= (HD (UPDATE-HD I dqst)) i))

(defthm arri--update-arri--thm
  (= (arri i (update-arri i e dqst)) e))

(defthm update-arri--hd--thm
  (= (HD (UPDATE-ARRI I E dqst)) (hd dqst)))

(defthm update-arri--nth-hd--thm
  (= (NTH *HD* (UPDATE-ARRI I E dqst))
     (NTH *HD* dqst)))

(defthm update-arri--tl--thm
  (= (TL (UPDATE-ARRI I E dqst)) (tl dqst)))

(defthm update-arri--nth-tl--thm
  (= (NTH *TL* (UPDATE-ARRI I E DQST))
     (NTH *TL* DQST)))

(defthm size-of--update-arri--thm
  (= (size-of (update-arri i e dqst)) (size-of dqst))
  :hints (("Goal" :in-theory (enable size-of))))

(defthmd update-arri--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (UPDATE-ARRI I E dqst))))


(defthm size-of--nat--thm
  (implies (dqstp dqst)
           (natp(size-of dqst)))
  :hints (("Goal" :in-theory (enable size-of))))

(defthm size-of--gt-0-means-not-empty--thm
  (implies (> (size-of dqst) 0)
           (not (is-empty dqst)))
  :hints (("Goal" :in-theory (enable size-of is-empty))))

(defthm size-of--gt-0-means-tl-gt-0--thm
  (implies (and (dqstp dqst) (> (size-of dqst) 0))
           (> (tl dqst) 0))
  :hints (("Goal" :in-theory (enable size-of))))

(defthm shift-up-to--sz--thm
  (equal (size-of (shift-up-to i dqst)) (size-of dqst))
  :hints (("Goal" :in-theory (enable size-of shift-up-to))))

(defthm shift-up-to--hd-same--thm
  (= (hd (shift-up-to i dqst)) (hd dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--nth-hd-same--thm
  (= (nth *hd* (shift-up-to i dqst)) (nth *hd* dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--hd-same-update-tl--thm
  (= (hd (shift-up-to i (update-tl j dqst))) (hd dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--tl-same--thm
  (= (tl (shift-up-to i dqst)) (tl dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--nth-tl-same--thm
  (= (nth *tl* (shift-up-to i dqst)) (nth *tl* dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--tl-same-update-hd--thm
  (= (tl (shift-up-to i (update-hd j dqst))) (tl dqst))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthmd shift-up-to--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (shift-up-to i dqst)))
  :hints (("Goal" :in-theory (enable shift-up-to))))

(defthm shift-up-to--tl--arr-unchanged--thm
  (implies (tail-head-relation dqst)
  (= (nth *arri* (shift-up-to (tl dqst) dqst)) (nth *arri* dqst)))
  :hints (("Goal" :in-theory (enable shift-up-to))))


(defthm shift-down-to--sz--thm
  (equal (size-of (shift-down-to i dqst)) (size-of dqst))
  :hints (("Goal" :in-theory (enable size-of shift-down-to))))

(defthm shift-down-to--hd-same--thm
  (= (hd (shift-down-to i dqst)) (hd dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))

(defthm shift-down-to--nth-hd-same--thm
  (= (nth *hd* (shift-down-to i dqst)) (nth *hd* dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))


(defthm shift-down-to--hd-same-update-tl--thm
  (= (hd (shift-down-to i (update-tl j dqst))) (hd dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))

(defthm shift-down-to--tl-same--thm
  (= (tl (shift-down-to i dqst)) (tl dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))

(defthm shift-down-to--nth-tl-same--thm
  (= (nth *tl* (shift-down-to i dqst)) (nth *tl* dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))



(defthm shift-down-to--tl-same-update-hd--thm
  (= (tl (shift-down-to i (update-hd j dqst))) (tl dqst))
  :hints (("Goal" :in-theory (enable shift-down-to))))

(defthmd shift-down-to--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (shift-down-to i dqst)))
  :hints (("Goal" :in-theory (enable shift-down-to))))


(defthm remove-first--sz-correct--thm
  (implies (and (dqstp dqst) (not (= (size-of dqst) 0)))
           (equal (size-of (remove-first dqst)) (- (size-of dqst) 1)))
  :hints (("Goal" :in-theory (enable size-of remove-first))))

(defthmd remove-first--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (remove-first dqst)))
  :hints (("Goal" :in-theory (enable size-of remove-first))))

(defthm remove-first--correct--thm
  (implies (and (not (is-empty dqst)) (tail-head-relation dqst))
    (equal (update-nth (nth *hd* dqst) (empty) (nth *arri* dqst)) (nth *arri* (remove-first dqst))))
  :hints (("Goal" :in-theory (e/d (remove-first size-of is-empty) ()))))


(defthm remove-last--sz-correct--thm
  (implies (and (dqstp dqst) (not (= (size-of dqst) 0)))
           (equal (size-of (remove-last dqst)) (- (size-of dqst) 1)))
  :hints (("Goal" :in-theory (enable size-of remove-last))))

(defthmd remove-last--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (remove-last dqst)))
  :hints (("Goal" :in-theory (e/d (size-of remove-last) (update-arri)))))

(defthm remove-last--correct--thm
  (implies (and (not (is-empty dqst)) (tail-head-relation dqst))
    (equal (update-nth (+ -1 (nth *tl* dqst)) (empty) (nth *arri* dqst)) (nth *arri* (remove-last dqst))))
  :hints (("Goal" :in-theory (e/d (remove-last size-of is-empty) ()))))


(defthm remove-front--sz-correct--thm
  (implies (and (dqstp dqst) (natp i) (not (is-empty dqst)) (< (+ i (hd dqst)) (tl dqst)))
           (equal (size-of (remove-front i dqst)) (- (size-of dqst) 1)))
  :hints (("Goal" :in-theory (e/d (remove-front remove-first size-of remove-last shift-up-to) (update-arri)))))

(defthmd remove-front--tl-hd--thm
  (implies (and (tail-head-relation dqst) (natp i))
           (tail-head-relation (remove-front i dqst)))
  :hints (("Goal" :in-theory (e/d (size-of remove-front remove-first remove-last) (update-arri)))))


(defthm remove-back--sz-correct--thm
  (implies (and (dqstp dqst) (natp i) (not (is-empty dqst)) (> i 0) (>= (- (- (tl dqst) 1) i) (hd dqst)))
           (equal (size-of (remove-back i dqst)) (- (size-of dqst) 1)))
  :hints (("Goal" :in-theory (e/d (remove-back remove-first remove-last size-of) (update-arri)))))

(defthmd remove-back--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (remove-back i dqst)))
  :hints (("Goal" :in-theory (e/d (size-of remove-back remove-first remove-last) (update-arri)))))


(defthm add-first--sz-correct--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (not (< (tl dqst) (hd dqst))) (dqstp dqst))
           (equal (size-of (add-first e dqst)) (+ (size-of dqst) 1)))
  :hints (("Goal" :in-theory (e/d (size-of add-first is-full is-full-front) (update-arri)))))

(defthmd add-first--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (add-first e dqst)))
  :hints (("Goal" :in-theory (e/d (add-first size-of is-full is-full-front) (update-arri)))))

(defthm add-first--get-first--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (tail-head-relation dqst))
           (equal (get-first (add-first e dqst)) e))
  :hints (("Goal" :in-theory (e/d (size-of add-first get-first is-full is-full-front shift-up-to is-empty) (update-arri)))))


(defthm add-first--remove-first-size--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (tail-head-relation dqst))
    (equal (size-of (remove-first (add-first e dqst))) (size-of dqst)))
  :hints (("Goal" :in-theory (e/d (add-first remove-first size-of is-full is-full-front shift-up-to size-of) (tl hd update-hd update-tl update-arri)))))

(defthm add-first--remove-first--tail-head--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (tail-head-relation dqst))
    (tail-head-relation (remove-first (add-first e dqst))))
  :hints (("Goal" :in-theory (e/d (add-first remove-first size-of is-full is-full-front shift-up-to get-first is-empty) (tl hd update-hd update-tl update-arri)))))

(defthm add-first--correct-1--thm
  (implies (and (not (= e (empty))) (not (is-full-front dqst)) (tail-head-relation dqst))
    (equal (update-nth (+ -1 (nth *hd* dqst)) e (nth *arri* dqst)) (nth *arri* (add-first e dqst))))
  :hints (("Goal" :in-theory (e/d (add-first size-of is-full is-full-front shift-up-to get-first is-empty) ()))))


(defthm add-last--sz-correct--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (not (< (tl dqst) (hd dqst))) (dqstp dqst))
           (equal (size-of (add-last e dqst)) (+ (size-of dqst) 1)))
  :hints (("Goal" :in-theory (e/d (size-of add-last is-full is-full-back) (update-arri)))))

(defthmd add-last--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (add-last e dqst)))
  :hints (("Goal" :in-theory (e/d (add-last size-of is-full is-full-back) (update-arri)))))

(defthm add-last--correct-1--thm
  (implies (and (not (= e (empty))) (not (is-full-back dqst)) (tail-head-relation dqst))
    (equal (update-nth (nth *tl* dqst) e (nth *arri* dqst)) (nth *arri* (add-last e dqst))))
  :hints (("Goal" :in-theory (e/d (add-last size-of is-full is-full-back shift-down-to is-empty) ()))))


(defthm add-last--get-last--thm
  (implies (and (not (is-full dqst)) (not (= e (empty))) (tail-head-relation dqst))
           (equal (get-last (add-last e dqst)) e))
  :hints (("Goal" :in-theory (e/d (size-of add-last get-last is-full is-full-back shift-down-to is-empty) (update-arri)))
          (and stable-under-simplificationp '(:in-theory (enable update-arri)))))


(defthm clear--sz-correct--thm
  (= (size-of (clear dqst)) 0)
  :hints (("Goal" :in-theory (e/d (size-of clear) ()))))

(defthmd clear--tl-hd--thm
  (implies (tail-head-relation dqst)
           (tail-head-relation (clear dqst)))
  :hints (("Goal" :in-theory (e/d (size-of clear) ()))))
