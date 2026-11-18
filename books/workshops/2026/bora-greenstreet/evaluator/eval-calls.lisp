; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-world")
(include-book "erl-state")
(include-book "eval-clauses")

(set-induction-depth-limit 1)

; Local Function Calls ---------------------------------------------------------

; Evaluate a 'local' function call. This means the call was made to a function
; declared within or imported to the current module. Find the corresponding 
; function, its macthing clause, and return the function body. Otherwise, throw
; the function_clause exception.
;
; - rs: is used to return exceptions, rejections, and BIF results, in which case 
;   the body is set to nil.
; - body: will be set to the body of the matching function clause if there is one.
;
; Order of function lookup:
; - First, check the local definitions. Assumed that there are no duplicate
;   function definitions.
; - If not found locally, then check the imported functions. If there is a match,
;   then check if the remote module has the said function and also exports it.
;   (TODO: This should be property of world-p) If there is still no match, check
;   if the function is a BIF.
; - Else, throw the function_clause exception.
;
; Remarks: 
;  - The Erlang reference manual states that the exception stack is
;    only for debugging purposes and has no guarantees. The only exception 
;    to this rule is the class 'error' with the reason 'undef' is 
;    guaranteed to include the Module, Function, and Arity of the attempted
;    function as the first stacktrace entry.
;
;  - Local calls to undefined functions are discovered during compilation.
;    This means that for an undefined function x:
;    + If x is defined locally, x() will return a rejection.
;    + If x is imported, x() will return an undef exception. This is 
;      also true if the module x was imported from is undefined.  
;
(define eval-local-call ((s erl-state-p) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))

       ; Some useful bindings for simplification 
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       
       ; Rejection to throw when the function is not defined and would have
       ; caused a compile error.
       (reject 
        (update-erl-state->in 
          s
          (make-erl-val-reject :err "eval-local-call: function is not defined.")))

       ; Exception to throw when a function is defined but there 
       ; are no matching clauses 
       (function-clause
         (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-atom :val 'function_clause))))

       ; The module must exist.
       ((unless (omap::assoc s.module s.world)) (mv reject nil))

       ((module module) (omap::lookup s.module s.world))
       (imports (attrs->import module.attrs))
      
       ; Check the module's defintions for the function
       ; The body of the function will not have access to current bindings
       ((if (omap::assoc fn module.fn-defns))
        (b* (((mv (erl-state rs) body) 
              (eval-clauses 
                args 
                (omap::lookup fn module.fn-defns)
                (update-erl-state->bind s nil)))
             ((if (not (wf-state-p rs))) (mv rs nil))
             ((if (null body)) 
              (mv function-clause nil)))
            (mv rs body)))
      
       ; Check the module's imports for the function
       ((if (omap::assoc fn imports))
        (b* ((imod-name (omap::lookup fn imports))
             
             ; Exception to throw when the function is not defined and would not ahve
             ; caused a compile error.
             (undef
               (update-erl-state->in s
                 (make-erl-val-excpt
                   :err-class (make-erl-val-atom :val 'error)
                   :err-reason (make-erl-val-atom :val 'undef)
                   :err-stack
                      (list (make-erl-val-atom :val imod-name)
                            (make-erl-val-atom :val call)
                            (make-erl-val-integer :val arity)))))

             ((unless (omap::assoc imod-name s.world)) (mv undef nil))
             ((module imod) (omap::lookup imod-name s.world))
             (exports (attrs->export imod.attrs))

             ; If the function was not exported, throw an undef error
             ((unless (member fn exports :test 'equal)) (mv undef nil))
            
             ; If the function was exported, the Erlang compiler
             ; would have ensured that it is defined.
             ((unless (omap::assoc fn imod.fn-defns)) 
              (mv
                (update-erl-state->in
                  s
                  (make-erl-val-reject 
                    :err "eval-local-call: module exports function, but it is not defined."))
                 nil))
             
             ; The body of the function will not have access to current bindings
             ((mv (erl-state rs) body)
              (eval-clauses
                args
                (omap::lookup fn imod.fn-defns)
                (update-erl-state->bind-mod s nil 'imod-name)))
              ((if (not (wf-state-p rs))) (mv rs nil))
              ((if (null body)) (mv function-clause nil)))
            (mv rs body)))

       ; Check if the function is a BIF
       ((if (erl-bif-p fn)) (mv (update-erl-state->in s (eval-bif fn args s)) nil)))
    (mv reject nil))
  
  ///
    (defcong erl-state-equiv equal (eval-local-call s f args) 1)
    (defcong symbol-equiv equal (eval-local-call s f args) 2)
    (defcong erl-vlst-equiv equal (eval-local-call s f args) 3))

; Remote Function Calls --------------------------------------------------------

; Evaluate a 'remote' function call. This means the call was made to a function
; declared outisde current module. Find the corresponding function, its macthing 
; clause, and return the function body. Otherwise, throw the function_clause exception.
;
; - rs: is used to return exceptions and rejections, in which case body is set to nil.
; - body: will be set to the body of the matching function clause if there is one.
;
; Implementation:
; - Check that the module exists, has the function in its definitions,
;   and exports it.
; - Evaluate the function clauses with the given args. 
;
(define eval-remote-call ((s erl-state-p) (module symbolp) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
       (module (symbol-fix module))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       
       ; Exception to throw when the function is not defined and would not ahve
       ; caused a compile error.
       (undef
         (update-erl-state->in s
          (make-erl-val-excpt
            :err-class (make-erl-val-atom :val 'error)
            :err-reason (make-erl-val-atom :val 'undef)
            :err-stack
              (list (make-erl-val-atom :val module)
                    (make-erl-val-atom :val call)
                    (make-erl-val-integer :val arity)))))
       
       ; Exception to throw when a function is defined but there 
       ; are no matching clauses 
       (function-clause 
         (update-erl-state->in s 
           (make-erl-val-excpt
                   :err-class (make-erl-val-atom :val 'error)
                   :err-reason (make-erl-val-atom :val 'function_clause))))

       ; The module must exist.
       ((unless (omap::assoc module s.world)) (mv undef nil))
       
       ; Get the remote module.
       ((module rmod) (omap::lookup module s.world))
       (exports (attrs->export rmod.attrs))
      
       ; Check the module's defintions for the function
       ; - The function also needs to have been exported
       ; - The function will not have access to local bindings
       ((if (and (omap::assoc fn rmod.fn-defns) (member fn exports :test 'equal)))
        (b* (((mv (erl-state rs) body) 
              (eval-clauses
               args
               (omap::lookup fn rmod.fn-defns)
               (update-erl-state->bind-mod s nil module)))
             ((if (not (wf-state-p rs))) (mv rs nil))
             ((if (null body)) (mv function-clause nil)))
            (mv rs body))))
    (mv undef nil))
  ///
    (defcong erl-state-equiv equal (eval-remote-call s m f args) 1)
    (defcong symbol-equiv equal (eval-remote-call s m f args) 2)
    (defcong symbol-equiv equal (eval-remote-call s m f args) 3)
    (defcong erl-vlst-equiv equal (eval-remote-call s m f args) 4))

; Anonymous Function Calls -----------------------------------------------------

; The Erlang reference manual defines anonymous functions (fun expressions) as:
; 
; - A fun expression begins with the keyword fun and ends with the keyword end. 
;   Between them is to be a function declaration, similar to a regular function 
;   declaration, except that the function name is optional and is to be a 
;   variable, if any.
;
; - Variables in a fun head shadow the function name and both shadow variables in
;   the function clause surrounding the fun expression. Variables bound in a fun
;   body are local to the fun body.
;
; - The return value of the expression is the resulting fun.
;
; Implementation:
; - Any call that is not a local or remote call must be a fun call. So, as a 
;   precondition, it assumed that any function that has an expression to be called
;   that is not an Atom or {remote, Atom}, has been parsed as a (:fun-call Expr Args)
;   when converted to ACL2.
; - If the Expr to be called does not evaluate to a fun expression, then the badfun 
;   exception is thrown.
; - Otherwise, the fun call is treated as a local call. If the fun was defined in a
;   module, it will be treated as local call within that module, i.e. it will have
;   access to the functions in that module.
;
; Not Supported:
; - Named funs are currently not supported. However, adding them should be trivial
; - funs of the form 'fun Module:Name/Arity" are not currently supported.

(define eval-fun-call ((s erl-state-p) (fun erl-val-p) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  :guard-hints (("Goal" :in-theory (enable erl-fun-p)))
  (b* ((s (erl-state-fix s))
       (fun (erl-val-fix fun))
       (args (erl-vlst-fix args))
       (arity (len args))

       ; Throw the badfun exception if the called expression is not a fun.
       ((if (not (erl-fun-p fun)))
        (mv 
          (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst (list (make-erl-val-atom :val 'bafun) fun))))
          nil))
        
       ; Throw the badarity exception if the arities of the fun and the
       ; arguments do not match.
       ((if (not (equal (erl-val-fun->arity fun) arity)))
        (mv 
          (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst (list (make-erl-val-atom :val 'badarity) fun))))
          nil))

       ; Exception to throw when the fun is well-formed but there 
       ; are no matching clauses 
       (function-clause 
         (update-erl-state->in s 
           (make-erl-val-excpt
                   :err-class (make-erl-val-atom :val 'error)
                   :err-reason (make-erl-val-atom :val 'function_clause))))

       ((mv (erl-state rs) body)
        (eval-clauses
          args
          (erl-val-fun->cls fun)
          (update-erl-state->bind-mod s 
            (erl-val-fun->bind fun)
            (erl-val-fun->module fun))))
       ((if (not (wf-state-p rs))) (mv rs nil))
       ((if (null body)) (mv function-clause nil))

       ; Remark: Badmatch exceptions are supposed to return the value that failed to 
       ; match. This is currently not supported. Instead, return the whole fun.
       ((unless (omap::compatiblep rs.bind (erl-val-fun->bind fun))) 
        (mv
         (update-erl-state->in s 
           (make-erl-val-excpt
                   :err-class (make-erl-val-atom :val 'error)
                   :err-reason (make-erl-val-tuple :lst (list (make-erl-val-atom :val 'badmatch) fun))))
        nil)))
    (mv rs body))
  ///
    (defcong erl-state-equiv equal (eval-fun-call s f args) 1)
    (defcong erl-val-equiv equal (eval-fun-call s f args) 2)
    (defcong erl-vlst-equiv equal (eval-fun-call s f args) 3))