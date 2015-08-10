(in-package "ACL2")

;; Requires set-theory book
;;  (include-book "/accts/dagreve/local/src/acl2-2.6/gcl/books/data-structures/set-theory")

(encapsulate

;; DIA
;; input: memory segment
;; output: list of memory segments from which direct interaction
;;   is allowed
 (((dia *) => *)

;; CURRENT
;; input: machine state
;; output: name of current partition
  ((current *) => *)

;; ALLPARTS
;; input: none
;; output: list of partition names
  ((allparts) => *)

;; KERNEL-NAME
;; input: none
;; output: name of kernel partition
;;  ((kernel-name) => *)

;; SELECT
;; input: memory segment name, machine state
;; output: memory segment values associated segment name
  ((select * *) => *)

;; NEXT
;; input: machine state
;; output: machine state after one step
  ((next *) => *)

;; SEGS
;; input: partition name
;; output: list of memory segment names associated with partition
  ((segs *) => *)

  )

;; direct interation allowed: list of segments that can communicate
;; directly with seg
(local (defun dia (seg) (list seg)))

; (local (defun kernel-name () 'k))

;; current partition name of st
(local (defun current (st) (declare (ignore st)) 'b))

;; list of partition names in st
(local (defun allparts () '(b f)))

(defthm current-is-partition
  (member (current st) (allparts)))

;(defthm kernel-is-partition
;  (member (kernel-name) (allparts)))

;; Select a segment from state
(local (defun select (seg st) (declare (ignore seg st)) nil))

;; Select a list of segments given a list of segment names
(defun selectlist (segs st)
  (if (consp segs)
      (cons
       (select (car segs) st)
       (selectlist (cdr segs) st))
    nil))

(local (defun next (st) st))

(defun run (st n)
  (if (zp n)
      st
    (run (next st) (1- n))))

;; The segments associated with a partition name
(local (defun segs (partname) (declare (ignore partname))  nil))

;; The segments associated with a list of partition names
(defun segslist (partnamelist)
  (if (consp partnamelist)
      (append
       (segs (car partnamelist))
       (segslist (cdr partnamelist)))
    nil))

;; Correctness of underlying separation system
(defthm separation
  (let ((segs (intersection-equal (dia seg) (segs (current st1)))))
    (implies
     (and
      (equal (selectlist segs st1) (selectlist segs st2))
      (equal (current st1) (current st2))
      (equal (select seg st1) (select seg st2)))
     (equal
      (select seg (next st1))
      (select seg (next st2))))))

;;; The "kernel" partition is the partition switch code. It is special
;;; in several ways.  Part of the specification of its correctness is
;;; that it does not change the state of any of the other partitions.

;(defthm kernel-touches-nothing
;  (implies
;   (and
;    (member seg (segs p))
;    (not (equal p (kernel-name))))
;   (equal
;    (intersection-equal (dia seg) (segs (kernel-name)))
;    nil)))

)
