;  chain-leading-to-complete.lisp                       Mihir Mehta

(in-package "ACL2")

(include-book "../abs-separate")

(defun
    chain-leading-to-complete (frame x acc seq)
  (declare
   (xargs
    :measure
    (len (set-difference-equal (strip-cars (frame->frame frame))
                               acc))
    :hints
    (("goal" :in-theory (e/d (set-difference$-redefinition)
                             (set-difference-equal
                              remove-of-set-difference-equal))))
    :guard (natp x)
    :verify-guards nil))
  (b*
      ((x (mbe :exec x :logic (nfix x)))
       ((when (or (atom (assoc-equal x (frame->frame frame)))
                  (member-equal x acc)))
        acc)
       (nexts (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
       ((when (atom nexts)) (cons x acc)))
    (chain-leading-to-complete frame (nth 0 nexts)
                               (cons x acc) seq)))

(defthm subsetp-of-chain-leading-to-complete-1
  (implies (subsetp-equal acc (strip-cars (frame->frame frame)))
           (subsetp-equal (chain-leading-to-complete frame x acc seq)
                          (strip-cars (frame->frame frame)))))

(defthm no-duplicatesp-of-chain-leading-to-complete-1
  (implies (no-duplicatesp-equal acc)
           (no-duplicatesp-equal (chain-leading-to-complete frame x acc seq))))

(defthm nat-listp-of-chain-leading-to-complete
  (implies (nat-listp acc)
           (nat-listp (chain-leading-to-complete frame x acc seq))))

(defthm
  chain-leading-to-complete-correctness-lemma-1
  (implies
   (and
    (<= 0
        (+ (len (frame->frame frame))
           (- (collapse-1st-index frame x))))
    (consp (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (consp
    (assoc-equal
     (car (set-difference-equal
           (frame-addrs-before frame x (collapse-1st-index frame x))
           seq))
     (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-of-frame-addrs-before)
                        (:rewrite member-of-set-difference-equal))
    :use
    ((:instance
      (:rewrite member-of-frame-addrs-before)
      (n (collapse-1st-index frame x))
      (x x)
      (frame frame)
      (y (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))))
     (:instance
      (:rewrite member-of-set-difference-equal)
      (y seq)
      (x (frame-addrs-before frame x (collapse-1st-index frame x)))
      (a (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))))))))

(defthm
  chain-leading-to-complete-correctness-lemma-2
  (implies (consp (set-difference-equal x y))
           (and
            (member-equal (car (set-difference-equal x y))
                          x)
            (not
             (member-equal (car (set-difference-equal x y))
                           y))))
  :hints (("goal" :in-theory (disable member-of-set-difference-equal)
           :use (:instance member-of-set-difference-equal
                           (a (car (set-difference-equal x y))))))
  :rule-classes :forward-chaining)

(defthm
  chain-leading-to-complete-correctness-1
  (implies (and (mv-nth 1 (collapse frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (member-equal y (chain-leading-to-complete frame x acc seq))
                (not (nat-equiv y x))
                (not (member-equal y acc)))
           (< (collapse-1st-index frame y)
              (collapse-1st-index frame x)))
  :hints
  (("goal" :induct (chain-leading-to-complete frame x acc seq)
    :in-theory (e/d ()
                    ((:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)
                     (:rewrite member-of-frame-addrs-before))))
   ("subgoal *1/3"
    :use
    ((:instance
      (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)
      (x (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq)))
      (frame frame))
     (:instance
      (:rewrite member-of-frame-addrs-before)
      (n (collapse-1st-index frame x))
      (x x)
      (frame frame)
      (y (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq)))))))
  :rule-classes :linear)

(defthmd
  chain-leading-to-complete-of-true-list-fix
  (equal (chain-leading-to-complete frame x (true-list-fix acc) seq)
         (true-list-fix (chain-leading-to-complete frame x acc seq)))
  :hints (("goal" :in-theory (enable true-list-fix)
           :induct (chain-leading-to-complete frame x acc seq)
           :expand (chain-leading-to-complete frame x (true-list-fix acc) seq))))

(defcong
  list-equiv list-equiv
  (chain-leading-to-complete frame x acc seq)
  3
  :hints
  (("goal" :use ((:instance chain-leading-to-complete-of-true-list-fix
                            (acc acc-equiv))
                 chain-leading-to-complete-of-true-list-fix))))

(defthm natp-of-car-of-chain-leading-to-complete
  (implies (and (nat-listp (true-list-fix acc))
                (consp (chain-leading-to-complete frame x acc seq)))
           (natp (car (chain-leading-to-complete frame x acc seq))))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (mv-nth 1 (collapse frame))
                   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                   (consp (assoc-equal x (frame->frame frame)))
                   (frame-p frame)
                   (not (member-equal x acc))
                   (not (nat-equiv (car (chain-leading-to-complete frame x acc seq))
                                   x))
                   (nat-listp acc))
              (not (member-equal (car (chain-leading-to-complete frame x acc seq))
                                 acc)))
     :hints
     (("goal" :in-theory (e/d ()
                              ((:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)))
       :induct (chain-leading-to-complete frame x acc seq)
       :do-not-induct t))))

  (defthmd
    chain-ends-in-abs-complete-lemma-3
    (implies (and (mv-nth 1 (collapse frame))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (consp (assoc-equal x (frame->frame frame)))
                  (frame-p frame)
                  (not (member-equal x acc))
                  (not (nat-equiv (car (chain-leading-to-complete frame x acc seq))
                                  x))
                  (nat-listp (true-list-fix acc)))
             (not (member-equal (car (chain-leading-to-complete frame x acc seq))
                                acc)))
    :hints (("goal" :do-not-induct t
             :in-theory (disable lemma)
             :use (:instance lemma (acc (true-list-fix acc)))))))

(defthm
  chain-ends-in-abs-complete-lemma-11
  (implies
   (and
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)
    (integerp x))
   (equal
    (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
    (car
     (chain-leading-to-complete
      frame
      (car (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq))
      (cons x acc)
      seq))))
  :instructions
  (:promote
   (:dive 1 1 1 1)
   := :top (:dive 1)
   (:rewrite
    frame-val->src-of-cdr-of-assoc-when-member-of-frame-addrs-before
    ((x
      (car
       (chain-leading-to-complete
        frame
        (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq))
        (cons x acc)
        seq)))
     (n
      (collapse-1st-index
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq))))))
   (:change-goal nil t)
   :demote
   (:casesplit
    (member-equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     (set-difference-equal
      (frame-addrs-before
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq))
       (collapse-1st-index
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))))
      seq)))
   :bash :contrapose
   :x :bash
   :top :bash))

(defthm
  chain-ends-in-abs-complete-lemma-12
  (implies
   (and
    (<=
     (collapse-1st-index
      frame
      (car
       (chain-leading-to-complete
        frame
        (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq))
        (cons x acc)
        seq)))
     (collapse-1st-index frame x))
    (integerp x)
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame))
   (not
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1))
    :use
    ((:instance
      (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)
      (x
       (car
        (set-difference-equal
         (frame-addrs-before
          frame
          (car
           (chain-leading-to-complete
            frame
            (car
             (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq))
            (cons x acc)
            seq))
          (collapse-1st-index
           frame
           (car
            (chain-leading-to-complete
             frame
             (car
              (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
             (cons x acc)
             seq))))
         seq)))
      (frame frame))))))

(defthm
  chain-ends-in-abs-complete-lemma-13
  (implies
   (and
    (member-equal
     (car
      (chain-leading-to-complete
       frame
       (car (set-difference-equal
             (frame-addrs-before frame x (collapse-1st-index frame x))
             seq))
       (cons x acc)
       seq))
     acc)
    (<
     (collapse-1st-index
      frame
      (car (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq)))
     (collapse-1st-index frame x))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame)
    (subsetp-equal acc (strip-cars (frame->frame frame))))
   (not
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (member-equal))
    :use
    (:instance
     (:rewrite chain-ends-in-abs-complete-lemma-3)
     (seq seq)
     (acc (cons x acc))
     (x (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq)))
     (frame frame))
    :expand
    (chain-leading-to-complete
     frame
     (car (set-difference-equal
           (frame-addrs-before frame x (collapse-1st-index frame x))
           seq))
     (cons x acc)
     seq))))

(defthm
  chain-ends-in-abs-complete-lemma-14
  (implies
   (and
    (member-equal
     (car
      (chain-leading-to-complete
       frame
       (car (set-difference-equal
             (frame-addrs-before frame x (collapse-1st-index frame x))
             seq))
       (cons x acc)
       seq))
     acc)
    (<
     (collapse-1st-index
      frame
      (car (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq)))
     (collapse-1st-index frame x))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame)
    (subsetp-equal acc (strip-cars (frame->frame frame))))
   (not
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (member-equal))
    :use
    (:instance
     (:rewrite chain-ends-in-abs-complete-lemma-3)
     (seq seq)
     (acc (cons x acc))
     (x (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq)))
     (frame frame)))))

(defthm
  chain-ends-in-abs-complete-lemma-15
  (implies
   (and
    (not
     (<
      (collapse-1st-index
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq)))
      (collapse-1st-index frame x)))
    (<
     (collapse-1st-index
      frame
      (car (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq)))
     (collapse-1st-index frame x))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame)
    (subsetp-equal acc (strip-cars (frame->frame frame))))
   (not
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:linear chain-leading-to-complete-correctness-1))
    :use
    (:instance
     (:linear chain-leading-to-complete-correctness-1)
     (y
      (car
       (chain-leading-to-complete
        frame
        (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq))
        (cons x acc)
        seq)))
     (frame frame)
     (x (car (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq)))
     (acc (cons x acc))))))

(defthm
  chain-ends-in-abs-complete-lemma-16
  (implies
   (and
    (<
     (collapse-1st-index
      frame
      (car (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq)))
     (collapse-1st-index frame x))
    (integerp x)
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame)
    (subsetp-equal acc (strip-cars (frame->frame frame))))
   (not
    (equal
     (car
      (set-difference-equal
       (frame-addrs-before
        frame
        (car
         (chain-leading-to-complete
          frame
          (car (set-difference-equal
                (frame-addrs-before frame x (collapse-1st-index frame x))
                seq))
          (cons x acc)
          seq))
        (collapse-1st-index
         frame
         (car
          (chain-leading-to-complete
           frame
           (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           (cons x acc)
           seq))))
       seq))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((>=
      (collapse-1st-index
       frame
       (car
        (set-difference-equal
         (frame-addrs-before
          frame
          (car
           (chain-leading-to-complete
            frame
            (car
             (set-difference-equal
              (frame-addrs-before frame x (collapse-1st-index frame x))
              seq))
            (cons x acc)
            seq))
          (collapse-1st-index
           frame
           (car
            (chain-leading-to-complete
             frame
             (car
              (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
             (cons x acc)
             seq))))
         seq)))
      (collapse-1st-index
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq))))
     (>=
      (collapse-1st-index
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq)))
      (collapse-1st-index frame x))))))

(defthm
  chain-ends-in-abs-complete-lemma-17
  (implies
   (member-equal
    (car (set-difference-equal
          (frame-addrs-before frame x (collapse-1st-index frame x))
          seq))
    acc)
   (member-equal
    (car
     (set-difference-equal
      (frame-addrs-before
       frame
       (car
        (chain-leading-to-complete
         frame
         (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq))
         (cons x acc)
         seq))
       (collapse-1st-index
        frame
        (car
         (chain-leading-to-complete
          frame
          (car
           (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq))
          (cons x acc)
          seq))))
      seq))
    acc))
  :hints
  (("goal"
    :do-not-induct t
    :expand
    (chain-leading-to-complete
     frame
     (car (set-difference-equal
           (frame-addrs-before frame x (collapse-1st-index frame x))
           seq))
     (cons x acc)
     seq))))

(defthm
  chain-ends-in-abs-complete-lemma-1
  (implies
   (and
    (consp (set-difference-equal
            (frame-addrs-before frame x (collapse-1st-index frame x))
            seq))
    (equal (car (set-difference-equal
                 (frame-addrs-before frame x (collapse-1st-index frame x))
                 seq))
           x))
   (equal (collapse-1st-index
           frame
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
          (collapse-1st-index frame x)))
  :instructions (:promote (:dive 1 2 1 1 1)
                          := :top (:dive 1 2)
                          (:rewrite frame-val->src-of-cdr-of-assoc-when-member-of-frame-addrs-before
                                    ((n (collapse-1st-index frame x))
                                     (x x)))
                          :top :bash))

(defthm chain-ends-in-abs-complete-lemma-2
  (implies (and (mv-nth 1 (collapse frame))
                (not (zp x))
                (atom (assoc-equal x (frame->frame frame))))
           (equal (frame-addrs-before frame x n)
                  nil))
  :hints (("goal" :in-theory (enable frame-addrs-before))))

(defthm
  chain-ends-in-abs-complete-lemma-18
  (implies
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame frame))))
    (1st-complete (frame->frame frame))
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))))
   (member-equal
    (1st-complete (frame->frame frame))
    (abs-addrs
     (frame-val->dir$inline
      (cdr
       (assoc-equal (frame-val->src$inline
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
                    (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable ctx-app-ok)
           :do-not-induct t)))

(defthm
  chain-ends-in-abs-complete-lemma-19
 (implies
  (and
   (equal (collapse-1st-index frame x) 0)
   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
   (consp (assoc-equal x (frame->frame frame))))
  (not
   (consp
    (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
 :hints (("goal" :do-not-induct t
          :expand (collapse-1st-index frame x))))

(defthmd
  chain-ends-in-abs-complete-lemma-10
  (implies
   (and (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame)))
        (frame-p frame)
        (abs-separate frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (<= (collapse-1st-index frame x)
            (nfix n)))
   (set-equiv
    (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-addrs-before frame x n)))
  :hints
  (("goal"
    :in-theory
    (e/d (frame-addrs-before collapse-1st-index
                             collapse-iter collapse
                             (:rewrite cons-of-remove-under-set-equiv-1))
         ((:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 2)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)
          (:definition member-equal)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite abs-file-alist-p-correctness-1)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite frame->root-of-collapse-this)
          (:rewrite consp-of-assoc-of-frame->frame)
          (:rewrite abs-fs-p-correctness-1)
          (:rewrite abs-fs-p-when-hifat-no-dups-p)
          (:type-prescription abs-directory-file-p-when-m1-file-p-lemma-1)
          (:rewrite partial-collapse-correctness-lemma-2)
          (:rewrite integerp-of-car-when-integer-listp)
          (:definition integer-listp)
          (:definition nthcdr)))
    :induct (frame-addrs-before frame x n)
    :expand (collapse-iter frame 1))))

(defthm
  chain-ends-in-abs-complete
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (frame-p frame)
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (not (member-equal x acc))
    (subsetp-equal acc (strip-cars (frame->frame frame)))
    (not
     (member-equal
      (car
       (set-difference-equal
        (frame-addrs-before
         frame
         (car (chain-leading-to-complete frame x acc seq))
         (collapse-1st-index frame
                             (car (chain-leading-to-complete frame x acc seq))))
        seq))
      acc)))
   (not
    (consp
     (set-difference-equal
      (abs-addrs
       (frame-val->dir
        (cdr (assoc-equal (car (chain-leading-to-complete frame x acc seq))
                          (frame->frame frame)))))
      seq))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (chain-ends-in-abs-complete-lemma-10)
     ((:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)))
    :do-not-induct t
    :induct (chain-leading-to-complete frame x acc seq)
    :restrict ((chain-ends-in-abs-complete-lemma-10 ((n
                                                      (collapse-1st-index frame x))))))
   ("subgoal *1/3"
    :use
    ((:instance
      (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)
      (x (car (set-difference-equal
               (frame-addrs-before frame x (collapse-1st-index frame x))
               seq)))
      (frame frame))))))

(defthm
  chain-leading-to-complete-correctness-2
  (implies
   (and (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame)))
        (frame-p frame)
        (abs-separate frame))
   (not
    (consp
     (set-difference-equal
      (abs-addrs
       (frame-val->dir
        (cdr (assoc-equal (car (chain-leading-to-complete frame x nil seq))
                          (frame->frame frame)))))
      seq))))
  :hints (("goal" :in-theory (disable chain-ends-in-abs-complete)
           :use (:instance chain-ends-in-abs-complete (acc nil)))))

(defthm
  consp-of-chain-leading-to-complete
  (implies (or (consp acc)
               (consp (assoc-equal (nfix x)
                                   (frame->frame frame))))
           (consp (chain-leading-to-complete frame x acc seq)))
  :rule-classes
  ((:type-prescription
    :corollary (implies (and (natp x)
                             (consp (assoc-equal x (frame->frame frame))))
                        (consp (chain-leading-to-complete frame x acc seq))))))

(defthm
  not-intersectp-of-chain-leading-to-complete-1
  (implies (and (not (intersectp-equal acc seq))
                (not (member-equal x seq)))
           (not (intersectp-equal (chain-leading-to-complete frame x acc seq)
                                  seq)))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative))
           :induct (chain-leading-to-complete frame x acc seq)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (not (intersectp-equal acc seq))
                  (not (member-equal x seq))
                  (consp (chain-leading-to-complete frame x acc seq)))
             (not (member-equal (car (chain-leading-to-complete frame x acc seq))
                                seq)))
    :hints (("goal" :in-theory (e/d (intersectp-equal)
                                    (intersectp-is-commutative)))))))
