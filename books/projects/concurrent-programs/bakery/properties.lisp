(in-package "ACL2")

#|

  properties.lisp
  ~~~~~~~~~~~~~~~

In this book, we define the functions rep, pick, label, suff, commit, and
inv. These are the main functions whose properties will show that the
implementation is a stuttering bisimulation of the spec. The other function,
rank which will be required to show finiteness of the stuttering, will be
defined and discussed in the book stutter2.lisp

|#


(include-book "lexicographic")
(include-book "measures")
(include-book "properties-of-sets")
(include-book "variables")
(include-book "fairenv")


(defun map-status (keys procs)
  (if (endp keys) ()
    (-> (map-status (rest keys) procs)
	(first keys)
	(>_ :status (status (<- procs (first keys)))))))

;; The representative of an implementation state is simply the vector
;; containing the status field of the states.

(DEFUN rep-b-c (st)
  (let ((procs (procs st)))
    (>_ :procs (map-status (keys procs) procs)
	:bucket (bucket st)
	:queue (queue st)
        :go (get-go st))))

;; We are proving stuttering equivalence. So pick is just the identity
;; function.

(DEFUN pick-b-c (st in)
  (declare (ignore st)) in)

(DEFUN fair-pick-b-c (st X)
  (fair-select (env st) X))

(defun wait-status (p)
  (equal (status p) 'wait))

(defun go-status (p)
  (equal (status p) 'go))

(defun idle-status (p)
     (equal (status p) 'idle))

(defun interested-status (p)
  (equal (status p) 'interested))

(defun legal-loc (p)
  (let ((loc (loc p)))
    (and (integerp loc)
         (>= loc 0)
         (<= loc 9))))

(defun extract-indices-with-pos (procs queue)
  (if (endp queue) nil
    (let ((rest-ind (extract-indices-with-pos procs
                                              (rest queue))))
      (if (pos (<- procs (first queue)))
	  (cons (first queue) rest-ind)
	rest-ind))))

(defun pos=1+temp-aux (procs queue)
  (if (endp queue) T
    (and (equal (pos (<- procs (first queue)))
                (1+ (temp (<- procs (first queue)))))
         (pos=1+temp-aux procs (rest queue)))))

(defun pos=1+temp (procs queue)
  (pos=1+temp-aux procs
                  (extract-indices-with-pos procs queue)))

(defun lexicographic-temp (procs queue)
  (if (endp queue) T
    (if (endp (rest queue)) T
      (and (lex< (temp (<- procs (first queue)))
                 (first queue)
                 (temp (<- procs (second queue)))
                 (second queue))
           (lexicographic-temp procs (rest queue))))))

;; suff is a subset of the set of invariants. This is the amount of
;; invariants which we have to assume to prove stuttering
;; equivalence. However, we need to strengthen the invariants a lot,
;; just in order to show the persistence over an execution.

(defun suff-proc (procs in bucket queue max)
  (let ((p (<- procs in)))
    (case (loc p)
      (0 (not (memberp in queue)))
      (1 (idle-status p))
      (2 t)
      (3 (and (interested-status p)
              (natp (temp p))
              (<= (temp p) max)
              (implies (not (equal max (temp p)))
                       (memberp in queue))
              (implies (equal max (temp p))
                       (memberp in bucket))))
      (4 (memberp in queue))
      (5 (and (memberp in queue)
              (not (choosing p))))
      (6 (and (wait-status p)
              (memberp in queue)
              (not (choosing p))
              (implies (endp (indices p))
                       (and (consp queue)
                            (equal (first queue) in)))))
      (7 (and (not (choosing p))
              (pos p)
              (memberp in queue)
              (memberp (current p)
                       (keys procs))))
      (8 (and (consp (indices p))
              (pos p)
              (not (choosing p))
              (memberp in queue)
              (not (choosing p))
              (memberp (current p)
                       (keys procs))))
      (9 (and (go-status p)
              (not (choosing p))
              (consp queue)))
      (t nil))))

(DEFUN suff-b-c (st in)
  (let* ((procs (procs st))
         (proc (<- procs in))
         (bucket (bucket st))
         (queue (queue st))
         (max (maxval st)))
    (and (disjoint bucket queue)
	 (natp max)
         (pos=1+temp procs queue)
         (lexicographic-temp procs queue)
         (my-subsetp queue (keys procs))
         (implies (consp queue) (suff-proc procs (car queue) bucket queue max))
	 (implies proc (suff-proc procs in bucket queue max)))))

(DEFUN fair-suff-b-c (st X)
  (and (suff-b-c st (fair-select (env st) X))
       (my-subsetp (keys (procs st))
                   (select-que (env st)))))

;; commit is simply a predicate that indicates end of stuttering.

(defun commit-proc (p)
    (or (equal (loc p) 1)
	(equal (loc p) 3)
	(equal (loc p) 9)
	(and (equal (loc p) 6)
	     (endp (indices p)))))

(DEFUN commit-b-c (st in)
  (let ((proc (<- (procs st) in)))
    (implies proc (commit-proc proc))))


;; The labelling function. As indicated earlier in the definition of
;; rep, we need only to pick up the vector of the status field.



(defun status-list (keys r)
  (if (endp keys) ()
    (cons (status (<- r (first keys)))
          (status-list (rest keys) r))))

(DEFUN label (st)
  (get-go st))

;; We now try to define the "strong" invariants.

(defun inv-p-p (procs in bucket queue max)
  (let* ((p (<- procs in))
	 (curr (<- procs (current p))))
    (case (loc p)
      (0 (and (idle-status p)
	      (not (choosing p))
	      (not (pos p))
	      (not (memberp in queue))
	      (not (memberp in bucket))))
      (1 (and (idle-status p)
	      (not (pos p))
	      (choosing p)
	      (not (memberp in queue))
	      (not (memberp in bucket))))
      (2 (and (interested-status p)
	      (natp (temp p))
	      (choosing p)
	      (not (pos p))
	      (implies (not (equal max (temp p)))
		       (memberp in queue))
	      (implies (equal max (temp p))
		       (memberp in bucket))
	      (<= (temp p) max)))
      (3 (and (<= (temp p) max)
	      (natp (temp p))
	      (choosing p)
	      (pos p)
	      (equal (pos p) (1+ (temp p)))
	      (interested-status p)
	      (implies (not (equal max (temp p)))
		       (memberp in queue))
	      (implies (equal max (temp p))
		       (memberp in bucket))))
      (4 (and (wait-status p)
	      (choosing p)
	      (natp (pos p))
	      (equal (pos p) (1+ (temp p)))
	      (not (memberp in bucket))
	      (memberp in queue)))
      (5 (and (wait-status p)
	      (natp (pos p))
	      (equal (pos p) (1+ (temp p)))
	      (not (choosing p))
	      (memberp in queue)))
      (6 (and (wait-status p)
	      (natp (pos p))
	      (equal (pos p) (1+ (temp p)))
	      (not (choosing p))
	      (memberp in queue)
	      (my-subsetp (indices p) (keys procs))
	      (my-subsetp (previous queue in) (indices p))))
      (7 (and (wait-status p)
	      (natp (pos p))
	      (equal (pos p) (1+ (temp p)))
	      (not (choosing p))
	      (consp (indices p))
	      (my-subsetp (previous queue in) (indices p))
	      (my-subsetp (indices p) (keys procs))
	      (equal (current p) (first (indices p)))
	      (memberp in queue)))
      (8 (and (wait-status p)
	      (natp (pos p))
	      (equal (pos p) (1+ (temp p)))
	      (not (choosing p))
	      (consp (indices p))
	      (equal (current p) (first (indices p)))
	      (implies (choosing curr)
		       (not (memberp (current p) (previous queue in))))
	      (my-subsetp (previous queue in) (indices p))
	      (my-subsetp (indices p) (keys procs))
	      (memberp in queue)))
      (9 (and (go-status p)
	      (not (choosing p))
              (equal (pos p) (1+ (temp p)))
	      (consp queue)
	      (not (memberp in bucket))
	      (equal in (first queue))))
      (t nil))))


(defun inv-p-keys (procs keys bucket queue max)
  (if (endp keys) T
    (and (inv-p-p procs (first keys) bucket queue max)
	 (inv-p-keys procs (rest keys) bucket queue max))))



(defun choosing-pos (procs queue)
  (if (endp queue) T
    (and (implies (not (natp (pos (<- procs (first queue)))))
		  (choosing (<- procs (first queue))))
	 (choosing-pos procs (rest queue)))))

(defun choosing-bucket (procs bucket)
  (if (endp bucket) T
    (and (choosing (<- procs (first bucket)))
	 (choosing-bucket procs (rest bucket)))))

(defun q<max (procs queue max)
  (if (endp queue) T
    (and (< (temp (<- procs (first queue))) max)
	 (q<max procs (rest queue) max))))

(defun b=max (procs bucket max)
  (if (endp bucket) T
    (and (equal max (temp (<- procs (first bucket))))
	 (b=max procs (rest bucket) max))))

(defun legal-status (p)
  (or (idle-status p)
      (interested-status p)
      (wait-status p)
      (go-status p)))

(defun legal-status-listp (keys procs)
  (if (endp keys) T
    (and (legal-status (<- procs (first keys)))
	 (legal-status-listp (rest keys) procs))))

(defun legal-pos (p)
  (or (legal-loc p)
      (not (pos p))))

(defun legal-pos-listp (keys procs)
  (if (endp keys) T
    (and (legal-pos (<- procs (first keys)))
         (legal-pos-listp (rest keys) procs))))

(DEFUN inv-b-c (st)
  (let* ((procs (procs st))
         (keys (keys procs))
         (bucket (bucket st))
         (queue (queue st))
         (max (maxval st)))
    (and (natp max)
         (uniquep queue)
         (orderedp bucket)
         (b=max procs bucket max)
         (q<max procs queue max)
         (lexicographic-temp procs queue)
         (choosing-bucket procs bucket)
         (choosing-pos procs queue)
         (my-subsetp queue keys)
         (my-subsetp bucket keys)
         (disjoint bucket queue)
         (legal-status-listp keys procs)
         (inv-p-keys procs keys bucket queue max))))

(DEFUN fair-inv-b-c (st)
  (and (inv-b-c st)
       (my-subsetp (keys (procs st))
                   (select-que (env st)))))

;; END Definitions of Properties.

(defun inv-p-p-c-s (procs in bucket queue go)
  (let ((p (<- procs in)))
    (case (status p)
      (idle (and (not (equal in go))
                 (not (memberp in queue))
                 (not (memberp in bucket))))
      (interested (and (not (equal in go))
                       (or (memberp in bucket)
                           (memberp in queue))))
      (wait (and (not (equal in go))
                 (memberp in queue)))
      (go (and (equal in go)
               (equal in (car queue))))
      (t nil))))

(defun inv-p-keys-c-s (procs keys bucket queue go)
  (if (endp keys) T
    (and (inv-p-p-c-s procs (first keys) bucket queue go)
         (inv-p-keys-c-s procs (rest keys) bucket queue go))))

(defun go-procs (go procs)
  (implies go (equal (status (<- procs go)) 'go)))

(defun go-queue (go queue)
  (implies go
           (equal (car queue) go)))

(defun keys-not-nil (keys)
  (if (endp keys) T
    (and  (first keys)
         (keys-not-nil (rest keys)))))

(DEFUN inv-c-s (st)
  (let* ((procs (procs st))
         (keys (keys procs))
         (bucket (bucket st))
         (queue (queue st))
         (go (get-go st)))
    (and (inv-p-keys-c-s procs keys bucket queue go)
         (go-queue go queue)
         (go-procs go procs)
         (keys-not-nil keys)
         (orderedp bucket)
         (uniquep queue)
         (disjoint bucket queue)
         (my-subsetp bucket keys)
         (my-subsetp queue keys))))

(defun suff-proc-c-s (procs in bucket queue go)
  (let ((p (<- procs in)))
  (case (status p)
    (wait (or (memberp in queue)
              (memberp in bucket)))
    ((idle interested) T)
    (go (equal go in))
    (t nil))))

(defun go-keys (go keys)
  (implies  go
            (memberp go keys)))

(DEFUN suff-c-s (st in)
  (let* ((procs (procs st))
         (keys (keys procs))
         (p (<- (procs st) in))
         (bucket (bucket st))
         (go (get-go st))
         (queue (queue st)))
    (and (go-queue go queue)
         (go-procs go procs)
         (go-keys go keys)
         (implies p (suff-proc-c-s procs in bucket queue go)))))


(defun commit-proc-c-s (p in queue)
  (or (and (equal (status p) 'wait)
           (equal in (first queue)))
      (equal (status p) 'go)))


(DEFUN commit-c-s (st in)
  (let* ((p (<- (procs st) in))
         (queue (queue st)))
    (implies p (commit-proc-c-s p in queue))))


(DEFUN rep-c-s (st)
  (>_ :procs (keys (procs st))
      :go (get-go st)))