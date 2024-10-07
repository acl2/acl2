(in-package "JVM")
(acl2::set-verify-guards-eagerness 2)

;----------------------------------------------------------------------
;; internal primitive stack operation
(defun push (item stack)
  (cons item stack))

(defun top (stack)
  (declare (xargs :guard (consp stack)))
  (car stack))

(defun pop (stack)
  (declare (xargs :guard (consp stack)))
  (cdr stack))


(defun deref (ref heap)
  (declare (xargs :guard (and (alistp heap)
                              (bound? ref heap))))
  (binding ref heap))


(defun alloc (heap) 
  (len heap))  ;; simple implementation of memory allocation heap

;-- primitives for dealing with array internal reprsentation ---

;; (acl2::set-verify-guards-eagerness 0) 

;; Tue Jan 13 14:57:51 2004. This is part of class loader!! We need to deal
;; with class loading sometime. 
;;
;; Currently I am working on defining a consistent-state. No hurry on this.


;;; This is also used in raise-exception. Need to Assert it!! Thu Apr  8 20:48:21 2004

;; purely for M6's implementation. forget about guard verificaiton for now.
;; not really these following are for the implementation of loader... which
;; we haven't touched. ... Wed Dec 24 23:19:13 2003

(defun sub-list (l1 s1 len)
  (declare (xargs :guard (and (integerp len)
                              (true-listp l1)
                              (integerp len)
                              (integerp s1)
                              (<= 0 len)
                              (<= 0 s1))))
  
  (if (endp l1)
      nil
    (if (zp s1)
        (if (zp len)
            nil
          (cons (car l1) (sub-list (cdr l1) 0 (- len 1))))
      (sub-list (cdr l1) (- s1 1) len))))


(defun setChars (l1 s1 l2 s2 len)
  (declare (xargs :guard (and (integerp len)
                              (true-listp l1)
                              (true-listp l2)
                              (integerp s1)
                              (integerp s2)
                              (equal (len l1) len)
                              (<= 0 s1)
                              (<= (+ s2 len) (len l2))
                              (<= s1 s2)
                              (<= 0 len)
                              (<= 0 s2))))
                              
  (app (sub-list l2 0 s2)
       (app (sub-list l1 s1 len)
            (sub-list l2 (+ s2 len) (- (len l2) (+ s2 len))))))

(defun charsp (chars)
  (if (not (consp chars)) t
    (and (characterp (car chars))
         (charsp (cdr chars)))))
      

(defun make-acl2-string (chars)
  (declare (xargs :guard (and (true-listp chars)
                              (charsp chars))))
  (coerce chars 'string))

(defun chars-numsp (nums)
  (if (not (consp nums)) t
    (and (and (integerp (car nums))
              (>= (car nums) 0)
              (< (car nums) 256))
         (chars-numsp (cdr nums)))))

(defun code-to-chars (nums)
  (declare (xargs :guard (and (true-listp nums)
                              (chars-numsp nums))))
  (if (endp nums)
      nil
    (cons (code-char (car nums))
          (code-to-chars (cdr nums)))))


;----- add primitives for recording the Heap Object creation order in the AUX
;     component of the State.

;(acl2::set-verify-guards-eagerness 2)

(defun make-trace (th-obj-counters rtrace)
  (list (cons 'th-obj-counters th-obj-counters)
        (cons 'rtrace          rtrace)))
  
(defun th-counters (trace)
  (declare (xargs :guard t))
  (if (not (true-listp trace)) nil
    (if (not (consp (nth 0 trace))) nil
      (cdr (nth 0 trace)))))


(defun rtrace (trace)
  (declare (xargs :guard t))
  (if (not (true-listp trace)) nil
    (if (not (consp (nth 1 trace))) nil
      (cdr (nth 1 trace)))))

(defun init-trace ()
  (make-trace nil nil))

(defun add-obj-th-count (obj-ref th trace)
  (declare (xargs :guard t))
  (if (not (alistp trace)) trace
    (let ((counters (th-counters trace))
          (rtrace   (rtrace      trace)))
      (if (not (alistp counters)) trace
        (if (bound? th counters)
            (if (not (integerp (binding th counters))) trace
              (let* ((new-count  (+ 1 (binding th counters)))
                     (new-counters (bind th new-count counters))
                     (new-trace    (cons (cons obj-ref (cons th new-count)) rtrace)))
                (make-trace new-counters new-trace)))
          (let* ((new-count  0)
                 (new-counters (bind th new-count counters))
                 (new-trace    (cons (cons obj-ref (cons th new-count)) rtrace)))
            (make-trace new-counters new-trace)))))))

  

;; (defconst *jvm-internal-primitives*
;;   '(push 
;;     pop 
;;     pop 
;;     deref 
;;     alloc  
;;     sub-list 
;;     setChars 
;;     make-acl2-string 
;;     code-to-chars 
;;     make-trace 
;;     th-counters 
;;     rtrace 
;;     init-trace 
;;     add-obj-th-count))
  













