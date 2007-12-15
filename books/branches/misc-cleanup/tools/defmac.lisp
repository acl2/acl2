; Matt Kaufmann, July 2006

; Here we define defmac, which can be used interchangeably with defmacro but
; can be significantly more efficient on large problems.  The idea is to have a
; small macro body for ACL2's evaluator to crawl through, putting all the work
; in a corresponding function (for a macro named mac, the function is mac-FN).
; Example:

; ACL2 !>(defmacro foo (fn1 fn2 &optional y &rest z)
; 	 (list fn1 (cons fn2 y) z))
; 
; Summary
; Form:  ( DEFMACRO FOO ...)
; Rules: NIL
; Warnings:  None
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;  FOO
; ACL2 !>:trans1 (foo h atom (a) g b)
;  (H (ATOM A) (G B))
; ACL2 !>:u
; 
;           0:x(EXIT-BOOT-STRAP-MODE)
; ACL2 !>(defmac foo (fn1 fn2 &optional y &rest z)
; 	 (list fn1 (cons fn2 y) z))
; 
; Since FOO-FN is non-recursive, its admission is trivial.  We observe
; that the type of FOO-FN is described by the theorem 
; (AND (CONSP (FOO-FN FN1 FN2 Y Z)) (TRUE-LISTP (FOO-FN FN1 FN2 Y Z))).
; We used primitive type reasoning.
; 
; Summary
; Form:  ( DEFUN FOO-FN ...)
; Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
; Warnings:  None
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
; 
; Summary
; Form:  ( DEFMACRO FOO ...)
; Rules: NIL
; Warnings:  None
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
; 
; Summary
; Form:  ( PROGN (DEFUN FOO-FN ...) ...)
; Rules: NIL
; Warnings:  None
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;  FOO
; ACL2 !>:trans1 (foo h atom (a) g b)
;  (H (ATOM A) (G B))
; ACL2 !>:pcb! :x
;           1:x(DEFMAC FOO (FN1 FN2 &OPTIONAL Y &REST Z)
;                      (LIST FN1 (CONS FN2 Y) Z))
;  L            (DEFUN FOO-FN (FN1 FN2 Y Z)
;                      (LIST FN1 (CONS FN2 Y) Z))
;               (DEFMACRO FOO (FN1 FN2 &OPTIONAL Y &REST Z)
;                         (FOO-FN FN1 FN2 Y Z))
; ACL2 !>

(in-package "ACL2")

(defmacro defmac (name args &rest rest)
  (let ((fn (packn (list name "-FN")))
        (fn-args (macro-vars args)))
    `(progn (defun ,fn ,fn-args
              ,@rest)
            (defmacro ,name ,args
              (,fn ,@fn-args)))))
