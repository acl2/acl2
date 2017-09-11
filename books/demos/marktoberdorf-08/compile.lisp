; (include-book "m1")
; (certify-book "compile" 1)

(in-package "M1")

(defun collect-at-end (x e)
  (if (member e x)
      x
    (append x (cons e nil))))

(defun collect-vars-in-expr (vars expr)
  (if (atom expr)
      (if (symbolp expr)
          (collect-at-end vars expr)
        vars)
    (collect-vars-in-expr
     (collect-vars-in-expr vars
                           (nth 0 expr))
     (nth 2 expr))))

(mutual-recursion

 (defun collect-vars-in-stmt* (vars stmt-list)
   (if (endp stmt-list)
       vars
     (collect-vars-in-stmt*
      (collect-vars-in-stmt vars (car stmt-list))
      (cdr stmt-list))))

 (defun collect-vars-in-stmt (vars stmt)
   (if (equal (nth 1 stmt) '=)
       (collect-vars-in-expr
        (collect-at-end vars (nth 0 stmt))
        (nth 2 stmt))
     (if (equal (nth 0 stmt) 'WHILE)
         (collect-vars-in-stmt*
          (collect-vars-in-expr vars (nth 1 stmt))
          (cdr (cdr stmt)))
       (if (equal (nth 0 stmt) 'RETURN)
           (collect-vars-in-expr vars (nth 1 stmt))
         vars))))
)

(defun index (vars var)
  (if (endp vars)
      0
    (if (equal var (car vars))
        0
      (+ 1 (index (cdr vars) var)))))

(defun OP! (op)
  (if (equal op '+)
      '((ADD))
    (if (equal op '-)
        '((SUB))
      (if (equal op '*)
          '((MUL))
        '((ILLEGAL))))))

(defun LOAD! (vars var)
  (cons (cons 'LOAD (cons (index vars var) nil))
        nil))

(defun PUSH! (n)
  (cons (cons 'PUSH (cons n nil))
        nil))

(defun expr! (vars expr)
  (if (atom expr)
      (if (symbolp expr)
          (LOAD! vars expr)
        (PUSH! expr))
    (append (expr! vars (nth 0 expr))
            (append (expr! vars (nth 2 expr))
                    (OP! (nth 1 expr))))))

(defun IFLE! (offset)
  (cons (cons 'IFLE (cons offset nil))
        nil))

(defun GOTO! (offset)
  (cons (cons 'GOTO (cons offset nil))
        nil))

(defun while! (test-code body-code)
  (append test-code
          (append (IFLE! (+ 2 (len body-code)))
                  (append body-code
                          (GOTO! (- (+ (len test-code)
                                       1
                                       (len body-code))))))))

(defun test! (vars test)
  (if (equal (nth 1 test) '>)
      (if (equal (nth 2 test) 0)
          (expr! vars (nth 0 test))
        (append (expr! vars (nth 0 test))
                (append (expr! vars (nth 2 test))
                        '((SUB)))))
    '((ILLEGAL))))

(defun STORE! (vars var)
  (cons (cons 'STORE (cons (index vars var) nil))
        nil))

(mutual-recursion

 (defun stmt*! (vars stmt-list)
   (if (endp stmt-list)
       nil
     (append (stmt! vars (car stmt-list))
             (stmt*! vars (cdr stmt-list)))))

 (defun stmt! (vars stmt)
   (if (equal (nth 1 stmt) '=)
       (append (expr! vars (nth 2 stmt))
               (STORE! vars (nth 0 stmt)))
     (if (equal (nth 0 stmt) 'WHILE)
         (while!
          (test! vars (nth 1 stmt))
          (stmt*! vars (cdr (cdr stmt))))
       (if (equal (nth 0 stmt) 'RETURN)
           (append (expr! vars (nth 1 stmt))
                   '((RETURN)))
         '((ILLEGAL))))))
 )

(defun compile (formals stmt-list)
  (stmt*! (collect-vars-in-stmt* formals stmt-list)
          stmt-list))

(defthm example-compilation-1
  (equal (compile '(n)
                  '((a = 1)
                    (while (n > 0)
                      (a = (n * a))
                      (n = (n - 1)))
                    (return a)))
         '((PUSH 1)
           (STORE 1)
           (LOAD 0)
           (IFLE 10)
           (LOAD 0)
           (LOAD 1)
           (MUL)
           (STORE 1)
           (LOAD 0)
           (PUSH 1)
           (SUB)
           (STORE 0)
           (GOTO -10)
           (LOAD 1)
           (RETURN)))
  :rule-classes nil)