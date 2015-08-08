(in-package "ACL2")

#|

  labels.lisp
  ~~~~~~~~~~~

In this book, we prove that theorem labels-equal->>.

|#

(include-book "properties")

;; BEGIN proof of labels-equal->>

(local
(defthm status-listp-map-status-reduction
  (implies (uniquep keys)
	   (equal (status-list keys (map-status keys procs))
		  (status-list keys procs))))
)

(local
(defthm same-keys-are-mapped
  (implies (and (orderedp keys)
		(legal-status-listp keys procs)
		(true-listp keys))
	   (equal (keys (map-status keys procs))
		  keys)))
)

(DEFTHM labels-equal-b-c->>
  (implies (inv-b-c st)
	   (equal (label (rep-b-c st))
		  (label st)))
  :rule-classes nil)

(DEFTHM fair-labels-equal-b-c->>
  (implies (fair-inv-b-c st)
           (equal (label (rep-b-c st))
                  (label st)))
  :rule-classes nil)