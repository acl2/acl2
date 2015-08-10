
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; memory-acl2.lisp
;;;
;;; An implementation of a memory system, initially by Alan Dunn, and
;;; considerably messed with.
;;;
;;; Memory is modeled as an alist, from 32 bit addresses to 8-bit
;;; values (both unsigned).
;;;
;;; This book can be used in two ways.  For theorem proving, it
;;; includes the definitions memoryp, read-mem-byte, and
;;; write-mem-byte, as well as some theorems about them.  However, if
;;; one wishes to execute concrete programs on a concrete state, it
;;; should be used in conjunction with memory-raw.lisp.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../Utilities/bytes-and-words")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Background

(defun memoryp (x)
  ;; Maps 32 bit addresses to 8 bit values.
  (declare (xargs :guard t))
  (cond ((atom x)
         (null x))
        ((and (consp (car x))
              (n32p (caar x))
              (n08p (cdar x)))
         (memoryp (cdr x)))
        (t
         'NIL)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Our two main definitions

(defun read-mem-byte (addr mem)
  ;; Note that we can't put a proper guard on memory, because we wish
  ;; to be able to use this book with memory-raw where it will really
  ;; be a Common Lisp Array --- not an ACL2 object.
  (declare (xargs :guard t))
  (cond ((atom mem)
         ;; Is this what we want?
         0)
        ((and (consp (car mem))
              (equal (caar mem)
                     addr))
         (cdar mem))
        (t
         (read-mem-byte addr (cdr mem)))))

(defun write-mem-byte (addr val mem)
  ;; Note that we can't put a proper guard on memory, because we wish
  ;; to be able to use this book with memory-raw where it will really
  ;; be a Common Lisp Array --- not an ACL2 object.
  (declare (xargs :guard (integerp addr)))
  ;; We keep the memory sorted
  (cond ((atom mem)
         (list (cons addr val)))
        ((and (consp (car mem))
              (equal (caar mem)
                     addr))
         (cons (cons addr val)
               (cdr mem)))
        ((and (consp (car mem))
              (integerp (caar mem))
              (< (caar mem) addr))
         (cons (car mem)
               (write-mem-byte addr val (cdr mem))))
        (t
         (cons (cons addr val)
               mem))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type theorems

(defthm |(memoryp (write-mem-byte addr val mem))|
  (implies (and (memoryp mem)
                (n32p addr)
                (n08p val))
           (memoryp (write-mem-byte addr val mem))))

(defthm |(n08p (read-mem-byte addr memory))|
  (implies (memoryp mem)
	   (n08p (read-mem-byte addr mem)))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (memoryp mem)
                           (and (integerp (read-mem-byte addr mem))
                                (<= 0 (read-mem-byte addr mem)))))))

;;; The four standard array theorems

(defthm |(read-mem-byte addr (write-mem-byte addr val mem))|
  (equal (read-mem-byte addr (write-mem-byte addr val mem))
         val))

(defthm |(read-mem-byte addr1 (write-mem-byte addr2 val mem))|
  (implies (not (equal addr1 addr2))
           (equal (read-mem-byte addr1 (write-mem-byte addr2 val mem))
                  (read-mem-byte addr1 mem))))

(defthm |(write-mem-byte addr val1 (write-mem-byte addr val2 mem))|
  (equal (write-mem-byte addr val1 (write-mem-byte addr val2 mem))
         (write-mem-byte addr val1  mem)))

(defthm |(write-mem-byte addr1 val1 (write-mem-byte addr2 val2 mem))|
  (implies (and (integerp addr1)
                (integerp addr2)
                (not (equal addr1 addr2)))
           (equal (write-mem-byte addr1 val1 (write-mem-byte addr2 val2 mem))
                  (write-mem-byte addr2 val2 (write-mem-byte addr1 val1 mem))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

(in-theory (disable memoryp
                    read-mem-byte
                    write-mem-byte))
