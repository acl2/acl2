#|
(certify-book "primitives" 0)
(acl2::set-verify-guards-eagerness 1)
|#
;;
;; This file contains the definition needed by various machine definition. 
;; 
;; Sun Dec 21 22:37:03 2003. Merged from typechecker.lisp (from BCV)
;; no-dup-set-facts.lisp (from M6).
(in-package "ACL2")
(acl2::set-verify-guards-eagerness 2)


;; Sun Dec 21 22:38:17 2003

; interger handling contributed by Robert Krug Mon Dec 22 02:36:15 2003 
;
; The following are constants and functions related to fixed integer sizes
; 
; This set of function is needed by both DJVM and M6.

(defconst *largest-integer-value* (- (expt 2 31) 1))
(defconst *largest-long-value* (- (expt 2 63) 1))
(defconst *most-negative-integer* (- (expt 2 31)))
(defconst *most-negative-long* (- (expt 2 63)))

; Coerce x to an unsigned integer which will fit in n bits.
(defun u-fix (x n)
  (declare (xargs :guard (integerp n)))
  (mod (ifix x) (expt 2 n)))

; Coerce x to a signed integer which will fit in n bits.
(defun s-fix (x n)
  (declare (xargs :guard (integerp n)))
  (let ((temp (mod (ifix x) (expt 2 n))))
    (if (< temp (expt 2 (1- n)))
        temp
      (- temp (expt 2 n)))))

(defun byte-fix (x)
  (s-fix x 8))

(defun ubyte-fix (x)
  (u-fix x 8))

(defun short-fix (x)

  (s-fix x 16))

(defun int-fix (x)
  (s-fix x 32))

(defun uint-fix (x)
  (u-fix x 32))

(defun long-fix (x)
  (s-fix x 64))

(defun ulong-fix (x)
  (u-fix x 64))

(defun char-fix (x)
  (u-fix x 16))

(defun 6-bit-fix (x)
  (u-fix x 6))

(defun 5-bit-fix (x)
  (u-fix x 5))

(defun expt2 (n)
  (declare (xargs :guard (integerp n)))  
  (expt 2 n))



(defun shl (x n)
  (declare (xargs :guard (and (integerp n)
                              (integerp x))))
  (* x (expt2 n)))

(defun shr (x n)
  (declare (xargs :guard (and (integerp n)
                              (integerp x))))
  (floor (* x (expt2 (- n))) 1))

;-----------------------------------------
; provides what DJVM will also need. 

;----------------------------------------------------------------------
; 
; Mon Dec 22 21:46:49 2003

(defun bound? (x l)
  (declare (xargs :verify-guards t :guard (alistp l)))
  (assoc-equal x l))

(defun binding (x l)
  (declare (xargs :verify-guards t :guard (and (alistp l)
                                               (bound? x l))))
  (cdr (assoc-equal x l)))

(defun bind (x y alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) (list (cons x y)))
        ((equal x (car (car alist)))
         (cons (cons x y) (cdr alist)))
        (t (cons (car alist) (bind x y (cdr alist))))))



;----------------------------------------------------------------------


(defun int32p (v)
  (declare (xargs :guard t))
  (and (integerp v)
       (<= v *largest-integer-value*)
       (>= v *most-negative-integer*)))


(defun int64p (v)
  (declare (xargs :guard t))
  (and (integerp v)
       (<= v *largest-long-value*)
       (>= v *most-negative-long*)))

;----------------------------------------------------------------------

;; Tue Dec 23 14:49:11 2003 macros that expands a term with a list of
;; abbrevation

(mutual-recursion
 (defun expand-mylet*-2-l (binding term-l)
   (declare (xargs :verify-guards nil
                   :measure (acl2-count term-l)))
   (if (endp term-l) nil
     (cons (expand-mylet*-2 binding (car term-l))
           (expand-mylet*-2-l binding (cdr term-l)))))

 (defun expand-mylet*-2 (binding term)
   (declare (xargs :verify-guards nil
                   :measure (acl2-count term)))
   (let ((key (car binding))
         (value (cdr binding)))
     (cond ((atom term) 
            (if (equal term key)
                value
              term))
           ((consp term)
            (if (consp term)
                (cons (car term) 
                      (expand-mylet*-2-l binding (cdr term)))
              term))
           (t term)))))
                
; (expand-mylet*-2 '(x . (f (+ x y))) 
;                  '(G (f (x x))))

(defun expand-mylet*-1 (binding alist)
  (declare (xargs :verify-guards nil))
  (if (endp alist) nil
    (cons (cons (caar alist)
                (expand-mylet*-2 binding (cdar alist)))
          (expand-mylet*-1 binding (cdr alist)))))
          

(defun expand-mylet* (bindings topTerm)
  (declare (xargs :verify-guards nil
                  :measure (len bindings)))
  (if (endp bindings) 
      topTerm
    (expand-mylet* (expand-mylet*-1 (car bindings) (cdr bindings))
                   (expand-mylet*-2 (car bindings) topTerm))))

;; this is a flaky substitution implementation. 
;; Only used by myself. It is ok.

; (expand-mylet* '((x . (f x)) 
;                  (y . (f x (f (+ x y)))))
;                '(G (f (+ x y) (y y x))))

(defun extract-bindings (assignments)
  (declare (xargs :verify-guards nil))
  (if (endp assignments) nil
    (cons (cons (caar assignments) (cadar assignments))
          (extract-bindings (cdr assignments)))))

; (extract-bindings 
;  '((cid (current-thread s))
;    (tt  (thread-table s))
;    (thread (thread-by-id cid tt))
;    (callstack (thread-call-stack thread))
;    (topframe  (top callstack))))


(defmacro mylet* (assignments theTerm)
 (let ((expanded (expand-mylet* (extract-bindings assignments) theTerm)))
      `,expanded))

;;(defmacro debug-print (&rest args)
;;   `(acl2::cw ,@args))

;; (acl2::set-ignore-ok :warn)

(defmacro debug-print (&rest args)
  (declare (ignore args))
   t)




(defun ADDRp (v) 
  (integerp v))

(defun CHARp (v)
  ;; temp implementation
  ;; should be 16 bit unsigned integer.
  ;;
  (INT32p v))

(defun jvmBOOLEANp (v)
  ;; temp implementation
  ;; should be 1 bit unsigned integer.
  (INT32p v))


(defun SHORTp (v)
  (INT32p v)) ;; Mon May 30 14:40:10 2005

(defun BYTEp (v)
  (INT32p v))

(defun jvmFLOATp (v) 
  (stringp v))

(defun DOUBLEp (v) 
  (stringp v))


;----------------------------------------------------------------------

(include-book "gen-guards")

(defconst *primitives* 
  '(mem 
    notMem 
    subset 
    del 
    app 
    u-fix 
    s-fix 
    byte-fix 
    ubyte-fix 
    short-fix 
    int-fix 
    uint-fix 
    long-fix 
    ulong-fix 
    char-fix 
    6-bit-fix 
    5-bit-fix 
    expt2 
    shl 
    shr 
    bound? 
    binding 
    bind
    int32p 
    int64p
    mylet*
    ADDRp
    CHARp
    jvmBOOLEANp
    SHORTp
    BYTEp
    jvmFLOATp
    DOUBLEp
    defpredicate
    debug-print))

(defconst *base-bind-free*
  '(replace-occurance-binding
    default-bind-free
    ))
;----------------------------------------------------------------------


