(in-package "ACL2S")

(definec gen-below-help (idx :nat below :nat step :pos) :nat-list
  (^ (< idx below)
     (cons idx (gen-below-help (+ step idx) below step))))

(defmacro gen-below (n &key (start '0) (step '1))
  `(gen-below-help ,start ,n ,step))

(defun extract-plist-vals (key l)
  (and (consp l)
       (cons (defdata::extract-kwd-val key (car l))
             (extract-plist-vals key (cdr l)))))

;; A "range" below is a kwd-list which specifies a contiguous range of
;; integers, which may also have a weight.
;; It may contain the following keywords, all of which are optional:
;; - :min (the minimum value for the range, default 0)
;; - :max (the maximum value for the range, default 0)
;; - :weight (the weight of the range, default is the max value minus the min value)

(defun range-size (range)
  (- (defdata::extract-kwd-val :max range :default 0)
     (defdata::extract-kwd-val :min range :default 0)))

(defun range-sizes (ranges)
  (and (consp ranges)
       (cons (range-size (car ranges))
             (range-sizes (cdr ranges)))))

(defun range-weight (range)
  (or (defdata::extract-kwd-val :weight range)
      (range-size range)))

(defun range-weights (ranges)
  (and (consp ranges)
       (cons (range-weight (car ranges))
             (range-weights (cdr ranges)))))

(defun range-offsets (ranges idx)
  (and (consp ranges)
       (cons `(,(if (consp (cdr ranges)) idx t)
               ,(if (> (range-size (car ranges)) 0)
                    `(defdata::random-index-seed ,(range-size (car ranges)) seed)
                  '(mv 0 seed)))
             (range-offsets (cdr ranges) (1+ idx)))))

(defmacro select-from-ranges (ranges seed)
  `(b* (((mv choice seed)
         (defdata::weighted-switch-nat
           ',(range-weights ranges)
           ,seed))
        ((mv range-offset seed)
         (case choice ,@(range-offsets ranges 0))))
     (mv (+ (case choice ,@(append
                            (pairlis$ (gen-below (1- (length ranges)))
                                      (acl2::pairlis-x2 (extract-plist-vals :min (butlast ranges 1)) nil))
                            `((t ,(defdata::extract-kwd-val :min (car (last ranges)))))))
            range-offset)
         seed)))

;; The second value returned by switch-nat is just the given seed
;; divided by nchoices and floored. To ensure that the produced seed
;; has the full possible range, we have this function which generates
;; a seed for switch-nat with genrandom-seed, which also returns a
;; "safe" new seed (safe insofar as the full range of values is
;; possible).
(defun switch-nat-safe-seed (nchoices seed)
  (b* (((mv seed1 seed) (defdata::genrandom-seed (1- (expt 2 63)) seed))
       ((mv val &) (defdata::switch-nat nchoices seed1)))
    (mv val seed)))

;; Generate a random Boolean. Returns a MV that also contains a new
;; seed.
(defun random-bool (seed)
  (mv-let (num seed)
          (defdata::genrandom-seed 2 seed)
          (mv (= 1 num) seed)))

(defthm random-bool-type
  (booleanp (mv-nth 0 (random-bool s)))
  :rule-classes :type-prescription)
