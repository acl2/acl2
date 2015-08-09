(in-package "ACL2")

#|

  pos-temp.lisp
  ~~~~~~~~~~~~~

This is an auxilliary book. In this book, we prove properties of a function
pos=1+temp that we define. In particular, we prove that inv-p-keys implies this
function. The use of this function substantially simplifies the proof of
inv-persists->>. However, the results in this book make sure that the function
pos=1+temp will not be required to add as an invariant since it follows from
the invariants

|#

(include-book "variables")
(include-book "properties")

(local
(defun falsifier-pos-temp (procs queue)
  (if (endp queue) nil
    (let ((p (<- procs (first queue))))
      (if (and (pos p)
               (not (equal (pos p) (1+ (temp p)))))
          (first queue)
        (falsifier-pos-temp procs (rest queue))))))
)

(local
(defthm pos=1+temp-auxlillary-property-1
  (implies (implies (pos (<- procs (falsifier-pos-temp procs queue)))
                    (equal (pos (<- procs (falsifier-pos-temp procs queue)))
                           (1+ (temp (<- procs
                                         (falsifier-pos-temp procs
                                                             queue))))))
           (pos=1+temp procs queue)))
)

(local
(defthm pos=1+temp-auxilliary-property-2
  (implies (not (memberp (falsifier-pos-temp procs queue)
                         queue))
           (pos=1+temp procs queue)))
)

(local
(defthm inv-p-p-implies-pos=1+temp
  (implies (inv-p-p procs in bucket queue max)
           (implies (pos (<- procs in))
                    (equal (1+ (temp (<- procs in)))
                           (pos (<- procs in))))))
)

(defthm inv-p-keys-implies-inv-p-p
  (implies (and (inv-p-keys procs keys bucket queue max)
		(memberp in keys))
	   (inv-p-p procs in bucket queue max))
  :rule-classes :forward-chaining)

(local
(in-theory (disable inv-p-p inv-p-keys))
)

(local
(defthm inv-p-keys-to-pos=1+temp-aux
  (implies (and (inv-p-keys procs keys bucket queue max)
                (memberp in keys))
           (implies (pos (<- procs in))
                    (equal (1+ (temp (<- procs in)))
                           (pos (<- procs in))))))
)

(local
(in-theory (enable my-subsetp))
)

(local
(defthm my-subsetp-to-larger
  (implies (and (my-subsetp queue keys)
                (memberp in queue))
           (memberp in keys))
  :rule-classes :forward-chaining)
)

(local
(in-theory (disable my-subsetp))
)

(local
(defthm inv-p-keys-to-pos=1+temp-aux-for-queue
  (implies (and (inv-p-keys procs keys bucket queue max)
                (my-subsetp queue keys)
                (memberp in queue))
           (implies (pos (<- procs in))
                    (equal (1+ (temp (<- procs in)))
                           (pos (<- procs in))))))
)

(defthm inv-p-keys-implies-pos=1+temp
  (implies (and (inv-p-keys procs keys bucket queue max)
                (my-subsetp queue keys))
           (pos=1+temp procs queue))
  :hints (("Goal"
           :cases ((memberp (falsifier-pos-temp procs queue) queue)))
          ("Subgoal 1"
           :in-theory (disable inv-p-keys-to-pos=1+temp-aux-for-queue)
           :use ((:instance inv-p-keys-to-pos=1+temp-aux-for-queue
                            (in (falsifier-pos-temp procs queue))))))
  :rule-classes :forward-chaining)
