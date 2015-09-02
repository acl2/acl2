(in-package "ACL2")

#|

  programs.lisp
  ~~~~~~~~~~~~~

In this book, we define a "simplified" bakery implementation and an abstract
spec. We will show that the implementation "matches" the spec upto finite
stuttering. Notice that our implementation is "simpler than the exact bakery
defined by Lamport. Lamport claims that bakery does not depend on any
lower-level mutual exclusion. We however, still use a lower-level mutual
exclusion through the "cas" instruction. While this is thus a restricted
implementation, we note that it is still practical since "cas" is an
instruction often provided as atomic on most systems.

|#

(include-book "variables")
(include-book "lexicographic")
(include-book "fairenv")



;; BEGIN simplified Bakery implementation

(defun cas (shared old new)
  (if (<= shared old)
      (list T new)
    (list nil shared)))

(defun successful-cas (shared old new)
  (first (cas shared old new)))

(defun casval (shared old new)
  (second (cas shared old new)))

(defun bake+-p (p in ps max)
  (let ((curr (<- ps (current p))))
      (case (loc p)
	(0 (>p :loc 1 :choosing T))
	(1 (>p :loc 2 :temp max :status 'interested))
	(2 (>p :loc 3 :pos (1+ (temp p))))
	(3 (>p :loc 4 :status 'wait))
	(4 (>p :loc 5 :choosing nil))
	(5 (>p :loc 6 :indices (keys ps)))
	(6 (if (endp (indices p))
	       (>p :loc 9 :status 'go)
	     (>p :loc 7 :current (first (indices p)))))
	(7 (if (choosing curr) p
	     (>p :loc 8)))
	(8 (if (and (pos curr)
		    (lex< (pos curr) (current p) (pos p) in))
	       p
	     (>p :loc 6 :indices (rest (indices p)))))
	(t (>p :loc 0 :pos nil :status 'idle)))))

;; For correspondence with the spec we are dealing with, we need a
;; queue, and a bucket in this implementation. The bucket will
;; periodically be flushed into the queue.

(defun bake+-b (p bucket in max)
  (cond ((equal (loc p) 1) (insert in bucket))
	((and (equal (loc p) 3)
	      (successful-cas max (temp p) (pos p)))
	 nil)
	(t bucket)))


(defun bake+-q (p queue bucket max)
  (cond ((and (equal (loc p) 3)
	      (successful-cas max (temp p) (pos p)))
	 (append queue bucket))
	((equal (loc p) 9) (rest queue))
        (t queue)))

;; Note that the implementation now depends on the shared variable
;; max, which will be set by atomic compare-and-swap operations.

(defun bake+-max (p max)
  (if (equal (loc p) 3)
      (casval max (temp p) (pos p))
    max))

(defun bake+-go (p go id)
  (cond ((and (equal (loc p) 6)
              (endp (indices p)))
         id)
        ((equal (loc p) 9)
         nil)
        (t go)))

;; So we organize the whole step function here.

;; st should be a record of four fields:

;; procs --- a vector of process local variables, as described in the
;;           step function.
;; queue --- a list of waiting processes.
;; bucket --- a list of processes that are interested in getting to
;;            the queue, but have not been flushed to the queue as
;;            yet.
;; max --- a natural number, determining the highest position value
;;         chosen. NOTE: max grows unbounded.


;; Comments on max: We could have chosen an implementation that resets
;;                  max. However, I dont see how to do it and preserve
;;                  correctness, while still preserving boundedness of
;;                  max. So I dont go that route and unduly complicate
;;                  matters. In short, I believe (without proof) that
;;                  unboundedness of max is a negative feature of the
;;                  bakery algorithm in general, and has nothing to do
;;                  with this particular simple implementation.

(defun bake+ (st in)
  (let* ((procs (procs st))
         (max (maxval st))
         (bucket (bucket st))
         (go (get-go st))
         (queue (queue st))
         (proc (<- procs in)))
    (>st :procs (-> procs in (bake+-p proc in procs max))
	 :maxval (bake+-max proc max)
	 :bucket (bake+-b proc bucket in max)
	 :queue (bake+-q proc queue bucket max)
         :go (bake+-go proc go in))))

(defun fair-bake+ (st X)
  (let* ((procs (procs st))
         (max (maxval st))
         (bucket (bucket st))
         (queue (queue st))
         (env (env st))
         (go (get-go st))
         (in (fair-select env X))
         (proc (<- procs in)))
    (>st :env (fair-step env X)
         :procs (-> procs in (bake+-p proc in procs max))
	 :maxval (bake+-max proc max)
	 :bucket (bake+-b proc bucket in max)
	 :queue (bake+-q proc queue bucket max)
         :go (bake+-go proc go in))))




;; END Bakery Implementation

;; BEGIN centralized Bakery. This is the spec we will show
;; correspondence to. It might not be the final spec we will
;; eventually deal with, but it will suffice for now.

(defun cent-p (p q id)
  (case (status p)
        (idle (>p :status 'interested))
        (interested (>p :status 'wait))
	(wait (>p :status (if (equal (first q) id)
                              'go 'wait)))
        (t (>p :status 'idle))))

(defun cent-b (p bucket id)
  (case (status p)
    (idle (insert id bucket))
    (interested (if (memberp id bucket) nil bucket))
    (t bucket)))

(defun cent-q (p q id bucket)
  (case (status p)
        (interested (if (memberp id bucket) (append q bucket) q))
        (go (rest q))
        (t q)))

(defun cent-go (p go q id)
  (cond ((and (equal (status p) 'wait)
              (equal (first q) id))
         id)
        ((equal (status p) 'go)
         nil)
        (t go)))

(defun cent (st in)
  (let* ((procs  (procs st))
	 (bucket (bucket st))
         (queue  (queue st))
         (go (get-go st))
         (proc   (<- procs in)))
    (>st :procs (-> procs in (cent-p proc queue in))
	 :bucket (cent-b proc bucket in)
         :queue (cent-q proc queue in bucket)
         :go (cent-go proc go queue in))))

;; END centralized bakery ;;

;; Now the part about correspondence of the bake+ algorithm with cent is the
;; big problem. However, for reason of cleanliness, we will define a much
;; simpler spec, and show that the cent is a stuttering refinement of tghe
;; spec.

;; Begin spec definition.

(defun add-to-procs (procs i)
  (insert i procs))

(defun spec (st i)
  (>st :go (cond ((and (not (get-go st))
                       (not (memberp i (procs st))))
                  nil)
                 ((get-go st) nil)
                 (t i))
       :procs (add-to-procs (procs st) i)))

(defun legal (st i)
  (and i ;; cannot be nil since we have already taken the nil
         ;; to mark that no one is in critical section.
       (implies (get-go st)
                (equal i (get-go st)))))

