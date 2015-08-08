(in-package "ACL2")

;; Author: Lee Pike

;; A proof that an implementation of the triangle function
;; on Tiny, a small stack-machine, is correct.

(include-book "../tiny-fib/tiny")

;; if you open tiny-triangle-correct, this will already
;; be included.
;; (include-book "tiny-rewrites")

(set-verify-guards-eagerness 0)

(defun tiny-loaded () t)

;; Address of idx's temporary variable
(defconst *idx-adr* 20)

;; Address of tri's temporary variable
(defconst *tri-adr* (1+ *idx-adr*))

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


;; ----------ASSEMBLY BLOCKS --------------------------------
(defconst *init-block*
  (assemble `(pushsi 1
	      add
	      pushsi 1
	      pop ,*idx-adr*
	      pushsi 0
	      pop ,*tri-adr*
	      pushsi 1
	      sub
	      )))

(defconst *loop-label-hole* -2)
(defconst *done-label-hole* -3)

;; I've got just n sitting on top now.
(defconst *unpatched-loop-block*
  (assemble `(; loop-label-hole:
	      dup
	      jumpz ,*done-label-hole*
	      pushs ,*idx-adr*
	      dup
	      pushs ,*tri-adr*
	      add
	      pop ,*tri-adr*
	      pushsi 1
	      add
	      pop ,*idx-adr*
	      pushsi 1
	      sub
	      jump ,*loop-label-hole*
	      ; done-label-hole:
	      )))

(defconst *done-block*
  (assemble `(pushs ,*tri-adr*
	      add
	      halt)))
;; ------------------------------------------------------------

(defconst *loop-label*        (+ *prog-start-address*
				 (len *init-block*)))
(defconst *done-label*        (+ *loop-label*
				 (len *unpatched-loop-block*)))

(defconst *label-patches*
     `((,*loop-label-hole* . ,*loop-label*)
       (,*done-label-hole* . ,*done-label*)))

(defconst *loop-block*
  (patch-prog-labels *unpatched-loop-block* *label-patches*))

(defconst *prog-halt-address* (+ *done-label*
				 (1- (len *done-block*))))

;; ------------------------------------------------------------

;; I command you to Triangluate, TINY!
(defconst *tri-prog*
  (append *init-block*
	  *loop-block*
	  *done-block*))

;;; ;;========== Test harness
;; ;; Initialize the state of the tiny interpreter so
;; ;; that it will calculate the n'th triangluation number.
;; ;; The variable 'tiny-state' is a stobj defined in tiny.lisp.

;; (defun init-tiny-tri (tiny-state n)
;;   (declare (xargs :stobjs (tiny-state)))
;;   (load-tiny *prog-start-address*
;; 	     `((,*prog-start-address* . ,*tri-prog*) ; Load program into memory
;; 	       (901 . (,n)))                         ; Initialize TOS with n
;; 	     tiny-state))

;; ;; Initialize the current tiny machine state
;; (defconst *tri-input* 3)
;; (init-tiny-tri tiny-state *tri-input*)

;;Execute exactly enough TINY steps to have the
;; tri program halt.
;; (tiny tiny-state (+ (len *init-block*)
;;		    (* *tri-input* (len *loop-block*))
;;		    (len *done-block*)))

;; ;; ;; Examine the returned triangulation number
;;  (dtos-val tiny-state 0)

;; ;; Check that the returned number matches
;; ;;  the triangulation specification.
;; ;; (equal (dtos-val tiny-state 0) (tri-spec *tri-input*))

;; ; Check that the program has halted.
;; (equal (memi (progc tiny-state) tiny-state) (encode 'halt))

;; ;;Execute these commands in ACL2's repl-loop to probe
;; ;; the contents of the TINY machine state.
;; *prog-start-address*
;; (memi *prog-start-address* tiny-state)
;; (dtos-val tiny-state 0)  ; data TOS
;; (progc tiny-state)       ; program counter
;; (ctos tiny-state)        ; return value TOS

(defconst *tri-cutpoints*
  `(,*prog-start-address*
    ,*loop-label*
    ,*done-label*
    ,*prog-halt-address*))

;;The initial top-of-stack address. Note that the stack already
;; contains a single input value, namely the parameter to tri.
(defconst *init-dtos* 899)
