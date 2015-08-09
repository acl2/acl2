(in-package "ACL2")

#|

 nth-update-nth.lisp
 ~~~~~~~~~~~~~~~~~~~

We attempt to write a generalized book here, that deals with functions nth and
update-nth, and produces a nice algebra similar to the records book. The goal
is to be able to disable the nth and update-nth functions in dealing with
proofs about stobjs, and work with access and updates using the theorems in
this book.

We also add a few theorems about mv-nth, so as to be able to disable mv-nth and
stop the irritating behavior of ACL2, replacing mv-nth 0 with car.

|#

(in-theory (enable nth update-nth mv-nth))

(defthm mv-nth-0-reduce
  (equal (mv-nth 0 (list x y)) x))

(defthm mv-nth-1-reduce
  (equal (mv-nth 1 (list x y)) y))

(in-theory (disable mv-nth))

(defthm nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (nth n (update-nth m v l)) (nth n l))))

(defthm nth-update-nth-same
  (implies (equal (nfix n) (nfix m))
           (equal (nth n (update-nth m v l)) v)))

(defthm update-nth-update-nth-same
  (equal (update-nth n v (update-nth n x l))
         (update-nth n v l)))

(defthm update-nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n v (update-nth m x l))
                  (update-nth m x (update-nth n v l))))
  :rule-classes ((:rewrite :loop-stopper ((n m)))))

(in-theory (disable nth update-nth))
