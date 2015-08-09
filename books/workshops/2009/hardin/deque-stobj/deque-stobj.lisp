#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| Functional deque with imperative array-backed implementation,             |#
#| using ACL2's single-threaded object (STOBJ) formalism.                    |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
             (seq ,stobj ,@(cdr rst))))))

(defmacro dqsz () 11)
(defmacro maxnode () (expt 2 (dqsz)))
(defmacro empty () "***NOTHING STORED***")


;; Fixed-size deque.
;;
;; hd points to front of the deque; tl points to one beyond the back of the deque.
;; Thus, the maximum capacity of the deque is MAXNODE - 1, not MAXNODE.

(defstobj dqst
  (arr :type (array t (2048)) :initially (empty))
  (hd  :type (unsigned-byte 11) :initially 0)
  (tl  :type (unsigned-byte 11) :initially 0))

;; A useful relation

(defun tail-head-relation (dqst)
         (declare (xargs :stobjs dqst))
         (and (natp (hd dqst))
              (natp (tl dqst))
              (<= (hd dqst) (- (maxnode) 1))
              (<= (tl dqst) (- (maxnode) 1))
              (<= (hd dqst) (tl dqst))))


;; Index subtract with wrap-around
(defun sub1 (x)
  (declare (xargs :guard (natp x)))
  (if (zp x)
      (- (maxnode) 1)
      (- x 1)))


;; Index add with wrap-around
(defun add1 (x)
  (declare (xargs :guard (natp x)))
  (if (> x (- (maxnode) 2))
      0
      (+ x 1)))


(defund size-of (dqst)
  (declare (xargs :stobjs dqst))
  (if (> (tl dqst) (hd dqst))
      (- (tl dqst) (hd dqst))
      0))


(defund is-empty (dqst)
  (declare (xargs :stobjs dqst))
  (equal (hd dqst) (tl dqst)))



;; Utility output functions

(defun get-arr-list-first-n (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  (if (or (zp i) (< (- (tl dqst) i) (hd dqst)))
      nil
      (cons (arri (- (tl dqst) i) dqst)
                  (get-arr-list-first-n (- i 1) dqst))))

(defun pd (dqst)
  (declare (xargs :stobjs dqst))
  (if (not (natp (size-of dqst)))
    nil
    (get-arr-list-first-n (size-of dqst) dqst)))


(defund get-first (dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable is-empty)))))
  (if (is-empty dqst)
      (empty)
      (arri (hd dqst) dqst)))


(defund get-last (dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (if (= (size-of dqst) 0)
      (empty)
      (arri (- (tl dqst) 1) dqst)))


(defund is-full (dqst)
  (declare (xargs :stobjs dqst))
  (equal (size-of dqst) (- (maxnode) 1)))


(defund is-full-front (dqst)
  (declare (xargs :stobjs dqst))
  (equal (hd dqst) 0))


(defund is-full-back (dqst)
  (declare (xargs :stobjs dqst))
  (equal (tl dqst) (- (maxnode) 1)))


;; Index of element e, searching from the head to the tail
(defund index-of--from-front (i e dqst)
  (declare (xargs :stobjs dqst :guard (natp i)
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (if (or (zp i) (> i (size-of dqst)))
      (size-of dqst) ;; Nothing at index size -- failure indication
      (if (equal e (arri (- (tl dqst) i) dqst))
          (- (size-of dqst) i)
          (index-of--from-front (- i 1) e dqst))))


(defthm ioff-nat--thm
  (implies (and (natp i) (dqstp dqst))
           (natp (index-of--from-front i e dqst)))
  :hints (("Goal" :in-theory (enable index-of--from-front size-of))))


;; Index of element e, searching from the tail to the head
(defund index-of--from-back (i e dqst)
  (declare (xargs :stobjs dqst :guard (natp i)
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (if (or (zp i) (> i (size-of dqst)))
      0 ;; Nothing at the 0th index from the tail -- failure indication
      (if (equal e (arri (+ (hd dqst) (- i 1)) dqst))
          (- (size-of dqst) (- i 1))
          (index-of--from-back (- i 1) e dqst))))


(defthm iofb-nat--thm
  (implies (and (natp i) (dqstp dqst))
           (natp (index-of--from-back i e dqst)))
  :hints (("Goal" :in-theory (enable index-of--from-back size-of))))



(defund contains (e dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable index-of--from-back size-of)))))
  (/= 0 (index-of--from-back (size-of dqst) e dqst)))


;; Shift up to the ith offset from the head
(defund shift-up-to (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  (if (or (zp i) (>= (+ (hd dqst) i) (tl dqst)))
      dqst
      (seq dqst
        (update-arri (+ (hd dqst) i) (arri (+ (hd dqst) (- i 1)) dqst) dqst)
        (shift-up-to (- i 1) dqst))))


;; Shift down to the ith offset from the tail
(defund shift-down-to (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  (if (or (zp i) (< (- (- (tl dqst) 1) i) (hd dqst)))
      dqst
      (seq dqst
        (update-arri (- (- (tl dqst) 1) i)
                     (arri (- (- (tl dqst) 1) (- i 1)) dqst) dqst)
        (shift-down-to (- i 1) dqst))))


(defund add-first (e dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of is-full is-full-front)))))
  (if (or (equal e (empty)) (is-full dqst) (< (tl dqst) (hd dqst)))
      dqst
      (if (not (is-full-front dqst))
          (seq dqst
            (update-hd (- (hd dqst) 1) dqst)
            (update-arri (hd dqst) e dqst))
          (seq dqst
            (update-tl (+ (tl dqst) 1) dqst)
            (shift-up-to (- (size-of dqst) 1) dqst)
            (update-arri 0 e dqst)))))


(defund add-last (e dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of is-full is-full-back)))))
  (if (or (equal e (empty)) (is-full dqst) (< (tl dqst) (hd dqst)))
      dqst
      (if (not (is-full-back dqst))
          (seq dqst
            (update-arri (tl dqst) e dqst)
            (update-tl (+ (tl dqst) 1) dqst))
          (seq dqst
            (update-hd (- (hd dqst) 1) dqst)
            (shift-down-to (hd dqst) dqst)
            (update-arri (- (maxnode) 2) e dqst)))))


(defund remove-first (dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (if (= (size-of dqst) 0)
      dqst
      (seq dqst
        (update-arri (hd dqst) (empty) dqst)
        (update-hd (+ (hd dqst) 1) dqst))))


(defund remove-last (dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (if (= (size-of dqst) 0)
      dqst
      (seq dqst
        (update-tl (- (tl dqst) 1) dqst)
        (update-arri (tl dqst) (empty) dqst))))


;; Removes the element at offset i from the front of the deque
(defund remove-front (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  ;; If deque is empty, ignore the request
  (if (is-empty dqst)
      dqst
      (if (= i 0)
          (remove-first dqst)
          (if (= (+ i (hd dqst)) (- (tl dqst) 1))
              (remove-last dqst)
              ;; If i isn't a valid position, ignore the delete request
              (if (>= (+ i (hd dqst)) (tl dqst))
                  dqst
                  (seq dqst
                    (shift-up-to i dqst)
                    (remove-first dqst)))))))


;; Removes the element at offset i from the back of the deque
;; Note that offsets will be >= 1, since offset 0 corresponds
;; to the tail, which indexes beyond valid data.
(defund remove-back (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  ;; If deque is empty, ignore the request
  ;; Likewise, ignore request to delete element at index 0
  (if (or (is-empty dqst) (= i 0))
      dqst
      (if (= i 1)
          (remove-last dqst)
          (if (= (- (- (tl dqst) 1) i) (hd dqst))
              (remove-first dqst)
              ;; If i isn't a valid position, ignore the delete request
              (if (< (- (- (tl dqst) 1) i) (hd dqst))
                  dqst
                  (seq dqst
                    (shift-down-to i dqst)
                    (remove-last dqst)))))))



(defund remove-first-occurrence (e dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (let ((k (index-of--from-front (size-of dqst) e dqst)))
    (if (= k (size-of dqst)) ;; Didn't find e
        dqst
        (remove-front k dqst))))


(defund remove-last-occurrence (e dqst)
  (declare (xargs :stobjs dqst
                  :guard-hints (("Goal" :in-theory (enable size-of)))))
  (let ((k (index-of--from-back (size-of dqst) e dqst)))
    (if (= k 0) ;; Didn't find e
        dqst
        (remove-back k dqst))))


(defund add-element (e dqst)
  (declare (xargs :stobjs dqst))
  (add-last e dqst))


(defund remove-element (e dqst)
  (declare (xargs :stobjs dqst))
  (remove-first-occurrence e dqst))


(defund clear-helper (i dqst)
  (declare (xargs :stobjs dqst :guard (natp i)))
  (if (or (zp i) (> i (maxnode)))
      dqst
      (seq dqst
        (update-arri (- i 1) (empty) dqst)
        (clear-helper (- i 1) dqst))))


(defund clear (dqst)
  (declare (xargs :stobjs dqst))
  (seq dqst
    (clear-helper (maxnode) dqst)
    (update-hd 0 dqst)
    (update-tl 0 dqst)))
