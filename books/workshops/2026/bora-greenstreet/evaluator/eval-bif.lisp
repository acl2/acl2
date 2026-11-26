; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-state")

; Evaluate BIF Calls -----------------------------------------------------------

(define eval-bif ((fn erl-bif-p) (args erl-vlst-p) (s erl-state-p))
  :returns (v erl-val-p)
  :ignore-ok t
  (b* (((fn fn) (fn-fix fn))
       (args (erl-vlst-fix args))
       (s (erl-state-fix s))

       ; The arity of the args must match the arity of the function
       ((if (not (equal (len args) fn.arity))) 
        (make-erl-val-reject :err "eval-bif: bad arity")))
     
     ; Match and evaluate the BIF
      (cond
        ((equal fn (make-fn :name 'is_atom :arity 1))
         (if (equal (erl-val-kind (car args)) :atom)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_boolean :arity 1))
         (if (erl-boolean-p (car args))
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_function :arity 1))
         (if (equal (erl-val-kind (car args)) :fun)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_function :arity 2))
         (b* (((unless (equal (erl-val-kind (cadr args)) :integer))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg)))
              ((unless (equal (erl-val-kind (car args)) :fun))
                (make-erl-val-atom :val 'false))
              (fun-arity (erl-val-fun->arity (car args)))
              (given-arity (erl-val-integer->val (cadr args))))
            (if (equal fun-arity given-arity)
                (make-erl-val-atom :val 'true)
                (make-erl-val-atom :val 'false))))
        ((equal fn (make-fn :name 'is_integer :arity 1))
         (if (equal (erl-val-kind (car args)) :integer)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_list :arity 1))
         (if (equal (erl-val-kind (car args)) :cons)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_number :arity 1))
         (if (equal (erl-val-kind (car args)) :integer)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_pid :arity 1))
         (if (pid-p (car args))
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'is_tuple :arity 1))
         (if (equal (erl-val-kind (car args)) :tuple)
             (make-erl-val-atom :val 'true)
             (make-erl-val-atom :val 'false)))
        ((equal fn (make-fn :name 'element :arity 2))
         (b* (((unless (equal (erl-val-kind (car args)) :integer))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg)))
              (n (erl-val-integer->val (car args)))
              ((unless 
                (and (equal (erl-val-kind (cadr args)) :tuple)
                     (> n 0)
                     (<= n (len (erl-val-tuple->lst (cadr args))))))
                (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg))))
              (nth (1- n) (erl-val-tuple->lst (cadr args)))))
        ((equal fn (make-fn :name 'hd :arity 1))
         (b* (((unless (and (equal (erl-val-kind (car args)) :cons)
                            (consp (erl-val-cons->lst (car args)))))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg))))
             (car (erl-val-cons->lst (car args)))))
        ((equal fn (make-fn :name 'length :arity 1))
         (b* (((unless (equal (erl-val-kind (car args)) :cons))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg)))
              (l (len (erl-val-cons->lst (car args)))))
             (make-erl-val-integer :val l)))
        ((equal fn (make-fn :name 'max :arity 2))
         (b* ((left (car args))
              (right (cadr args))
              (cmp (erl-compare left right)))
             (if (or (equal cmp 0) (equal cmp 1))
                 left
                 right)))
        ((equal fn (make-fn :name 'min :arity 2))
         (b* ((left (car args))
              (right (cadr args))
              (cmp (erl-compare left right)))
             (if (or (equal cmp 0) (equal cmp -1))
                 left
                 right)))
        ((equal fn (make-fn :name 'self :arity 0)) (erl-state->self s))
        ((equal fn (make-fn :name 'tl :arity 1))
         (b* (((unless (and (equal (erl-val-kind (car args)) :cons)
                            (consp (erl-val-cons->lst (car args)))))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg))))
             (make-erl-val-cons :lst (cdr (erl-val-cons->lst (car args))))))
        ((equal fn (make-fn :name 'tuple_size :arity 1))
         (b* (((unless (equal (erl-val-kind (car args)) :tuple))
               (make-erl-val-excpt
                 :err-class (make-erl-val-atom :val 'error)
                 :err-reason (make-erl-val-atom :val 'badarg)))
              (l (len (erl-val-tuple->lst (car args)))))
             (make-erl-val-integer :val l)))
        (t (make-erl-val-reject :err "eval-bif: bad bif"))))
  ///
    (defcong fn-equiv equal (eval-bif fn args s) 1)
    (defcong erl-vlst-equiv equal (eval-bif fn args s) 2)
    (defcong erl-state-equiv equal (eval-bif fn args s) 3))