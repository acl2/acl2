(in-package "ACL2")
;; A proof that an implementation of the Fibonacci function
;; on Tiny, a small stack-machine, is correct.

(include-book "tiny")
;(include-book "tiny-rewrites")
;(include-book "stream-fib")

(set-verify-guards-eagerness 0)

(defun tiny-loaded () t)

;; Addresses of fib's temporary variables
(defconst *fib-adr* 20)
(defconst *fib-1-adr* (1+ *fib-adr*))

;; The start-of-program address
(defconst *prog-start-address* 100)

;; Replaces label placeholders in a program fragment with
;; their final computed values. Label placeholders should
;; be negative integers, to prevent conflicts with opcodes
;; and address references in the program being patched.
(defun patch-prog-labels (prog label-map)
  (cond ((endp prog)
	 prog)
	((assoc-equal (car prog) label-map)
	 (cons (cdr (assoc-equal (car prog) label-map))
	       (patch-prog-labels (cdr prog) label-map)))
	(t
	 (cons (car prog)
	       (patch-prog-labels (cdr prog) label-map)))))

#|
NOTE: I am using Hoare triples to document the pre- and post-conditions
      of basic blocks. To describe the contents of the stack I am overloading
      the predicate symbol (<=) to compare stacks. Given stacks xs and ys,
      xs <= ys holds when xs is a prefix of ys. I write the contents of
      a stack using Haskell notation, so that [1,2,3] represents a three
      element stack with 1 as the top element. I use the special constant
      'stack' to represent tiny's current value stack.

      I also define an operator on memory that takes a stack of addresses
      and returns a stack of values consisting of the current contents of
      memory at those addresses. So if the contents of memory at address
      1 is 3 and the contents of memory at address 5 is 12, then
      mem[1,3] = [5,12].
|#

;; {[N] <= stack}
;; *init-block*
;; {[N-1] <= stack /\ mem[*fib-adr*,*fib-adr-1*] = [1,1]}
(defconst *init-block*
  (assemble `(pushsi 1
              dup
	      dup
	      pop ,*fib-adr*
	      pop ,*fib-1-adr*
	      sub)))


;; {[N] <= stack /\ mem[*fib-adr*,*fib-adr-1*] = [M,K]}
;; *loop-block*
;; {   (N=0 /\ [0] <= stack /\ mem[*fib-adr*] = M)
;;  \/ ([N-1] <= stack /\ mem[*fib-adr*,*fib-adr-1*] = [M+K,M])}
(defconst *loop-label-hole* -2)
(defconst *done-label-hole* -3)
(defconst *unpatched-loop-block*
  (assemble `(; loop-label-hole:
              dup
	      jumpz ,*done-label-hole*
	      pushs ,*fib-adr*
	      dup
	      pushs ,*fib-1-adr*
	      add
	      pop ,*fib-adr*
	      pop ,*fib-1-adr*
	      pushsi 1
	      sub
	      jump ,*loop-label-hole*
              ; done-label-hole:
              )))

; Calculate the actual program labels to patch
(defconst *loop-label*        (+ *prog-start-address*
				 (len *init-block*)))
(defconst *done-label*        (+ *loop-label*
				 (len *unpatched-loop-block*)))

(defconst *label-patches*
     `((,*loop-label-hole* . ,*loop-label*)
       (,*done-label-hole* . ,*done-label*)))

(defconst *loop-block*
  (patch-prog-labels *unpatched-loop-block* *label-patches*))

;; {[0] <= stack /\ mem[*fib-adr*] = M)
;; *done-block*
;; {[M] <= stack}
(defconst *done-block*
  (assemble `(pushs ,*fib-adr*
              add
	      halt)))

(defconst *prog-halt-address* (+ *done-label*
				 (1- (len *done-block*))))

;; The Fibonacci program
(defconst *fib-prog*
  (append *init-block*
	  *loop-block*
	  *done-block*))


;;; ;;========== Test harness for evaluating *fib-prog* on tiny =============

;; ;; Initialize the state of the tiny interpreter so
;; ;; that it will calculate the n'th Fibonacci number.
;; ;; The variable 'tiny-state' is a stobj defined in tiny.lisp.
;; (defun init-tiny-fib (tiny-state n)
;;   (declare (xargs :stobjs (tiny-state)))
;;   (load-tiny *prog-start-address*
;; 	     `((,*prog-start-address* . ,*fib-prog*) ; Load program into memory
;; 	       (901 . (,n)))                         ; Initialize TOS with n
;; 	     tiny-state))

;; ;; Initialize the current tiny machine state
;; (defconst *fib-input* 4)
;; (init-tiny-fib tiny-state *fib-input*)

;; ;;Execute exactly enough TINY steps to have the
;; ;; fib program halt.
;; (tiny tiny-state (+ (len *init-block*)
;; 		    (* (1- *fib-input*) (len *loop-block*))
;; 		    (len *done-block*)))

;; ; Examine the returned Fibonacci number
;; (dtos-val tiny-state 0)

;; ; Check that the returned number matches
;; ;  the Fibonacci specification.
;; (equal (dtos-val tiny-state 0) (fib-spec *fib-input*))

;; ; Check that the program has halted.
;; (equal (memi (progc tiny-state) tiny-state) (encode 'halt))

;; ;;Execute these commands in ACL2's repl-loop to probe
;; ;; the contents of the TINY machine state.
;; *prog-start-address*
;; (memi *prog-start-address* tiny-state)
;; (dtos-val tiny-state 0)  ; data TOS
;; (progc tiny-state)       ; program counter
;; (ctos tiny-state)        ; return value TOS

(defconst *fib-cutpoints*
  `(,*prog-start-address*
    ,*loop-label*
    ,*done-label*
    ,*prog-halt-address*))

;;The initial top-of-stack address. Note that the stack already
;; contains a single input value, namely the parameter to fib.
(defconst *init-dtos* 899)
