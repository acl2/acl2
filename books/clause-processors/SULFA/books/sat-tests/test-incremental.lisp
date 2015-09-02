
;; test-incremental.lisp

;; A test suite containing both valid and invalid theorems, as well
;; as events testing the incremental SAT interface.
;;
;; The suite cannot be certified in its current state, so it isn't made
;; with the makefile.  However, you should be able to load it successfully
;; at the top-level.

(in-package "ACL2")

(include-book "test-help" :ttags (sat sat-cl))
(set-state-ok t)

;; -----------------------------------------------------------------
;; Definitions



(defun bv-not (n x)
  (if (zp n)
      nil
    (cons (not (car x))
          (bv-not (1- n) (cdr x)))))

(defun n-bleq (n x y)
  (if (zp n)
      t
    (and (iff (car x) (car y))
         (n-bleq (1- n) (cdr x) (cdr y)))))

(defun xor3 (x y z)
  (xor x (xor y z)))

(defun maj3 (x y z)
  (if x (or y z)
    (and y z)))

;; Returns a n+1 length sum of the first
;; n bits of a and b (plus the carray).
(defun v-adder (n c a b)
  (if (zp n)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (1- n)
                   (maj3 c (car a) (car b))
                   (cdr a) (cdr b)))))

(defun nth-cdr (n x)
  (if (zp n)
      x
    (nth-cdr (1- n) (cdr x))))

(defun nth-sublist (n lst)
  (if (zp n)
      nil
    (cons (car lst) (nth-sublist (1- n) (cdr lst)))))

(defun append-n (n x y)
  (if (zp n)
      y
    (cons (car x) (append-n (1- n) (cdr x) y))))

(defun n-nills (n)
  (if (zp n)
      nil
    (cons nil (n-nills (1- n)))))

(defun rev-n (n x ans)
  (if (zp n)
      ans
    (rev-n (1- n) (cdr x) (cons (car x) ans))))

(defun mux-n-help (n in rsel)
  (if (zp n)
      (car in)
    (if (car rsel)
        (mux-n-help (1- n) (nth-cdr (expt 2 (1- n)) in) (cdr rsel))
      (mux-n-help (1- n) in (cdr rsel)))))

(defun mux-n (n in sel)
  (mux-n-help n in (rev-n n sel nil)))

(defun mux-n-w-help (n w in)
  (if (zp n)
      nil
    (cons (car in) (mux-n-w-help (1- n) w (nth-cdr w in)))))

(defun mux-n-w1 (nw sn w in sel)
  (if (zp nw)
      nil
    (cons (mux-n sn (mux-n-w-help (expt 2 sn) w in) sel)
          (mux-n-w1 (1- nw) sn w (cdr in) sel))))

(defun mux-n-w (n w in sel)
  (mux-n-w1 w n w in sel))

(defun shift-mux-help (n w reg)
  (if (zp n)
      nil
    (append-n w reg (shift-mux-help (1- n) w (cons nil reg)))))

(defun shifter (sn rn rshift reg)
  (if (zp sn)
      reg
    (mux-n-w sn rn (shift-mux-help (expt 2 sn) rn reg) rshift)))

(defun increment (n x)
  (if (zp n)
      nil
    (if (car x)
        (cons nil (increment (1- n) (cdr x)))
      (cons t (cdr x)))))

(defun next_digit_counter_state (x)
  (if (n-bleq 4 x '(t nil nil t))
      (list '(nil nil nil nil) t)
    (list (increment 4 x) nil)))

(defun next_counter_state (n x)
  (let* ((curr_d_out (next_digit_counter_state (car x)))
         (curr_d_val (car curr_d_out))
         (curr_d_reset (cadr curr_d_out)))
    (if (zp n)
        nil
      (if curr_d_reset
          (cons curr_d_val (next_counter_state (1- n) (cdr x)))
        (cons curr_d_val (cdr x))))))

(defun valid_digit (a)
  (let ((a1 (cadr a))
        (a2 (caddr a))
        (a3 (cadddr a)))
    (not (and a3 (or a2 a1)))))

(defun valid_digits (n x)
  (if (zp n)
      (not (consp x))
    (and (valid_digit (car x))
         (valid_digits (1- n) (cdr x)))))

(defun n-nth (n x)
  (if (zp n)
      (car x)
    (n-nth (1- n) (cdr x))))

;; Return true if bv is a bit vector of length n.

(defun bvp (n bv)
  (if (zp n)
      (not bv)
    (and (consp bv)
         (booleanp (car bv))
         (bvp (1- n) (cdr bv)))))

;; A similar function, but in our decidable subset.
;; Note that we don't guarantee that the bit-vector
;; is boolean.  While that is a guard of most of our
;; functions, it should only be necessary when we need
;; to jump from n-bleq to equality---and booleanp
;; is not in our decidable subset.  Of course, it's
;; not a big deal to have a function with an unknown
;; definition...it just generates a bunch of ugly messages.

(defun bv-hyp (n bv)
  (if (zp n)
      (not bv)
    (bv-hyp (1- n) (cdr bv))))

;; Reverse an n bit list

(defun rev-n (n x ans)
  (if (zp n)
      ans
    (rev-n (1- n) (cdr x) (cons (car x) ans))))

;; Add pairs of A and B to list
(defun add-pairlist (A B list)
  (if (endp A)
      list
    (add-pairlist (cdr A) (cdr B)
                  (cons (cons (car A) (car B))
                        list))))

;; Whether a given signal is high
;; (usually represented as 't)
(defun highp (x)
  (if (consp x) nil (if x t nil)))

;; Whether a given signal is low
;; (represented as 'nil)
(defun lowp (x)
  (not x))

;; Whether a given signal is unknown
;; (usually represented as '(X))
(defun xValp (x)
  (consp x))

(defun xVal ()
  (cons 'x nil))

;; A tbit vector is represented as a list of values that
;; represent the following four values:
;;
;; under-constrained: 'x
;; nil: 'nil
;; true: anything else... generally true.
;;
;; We represent any value as equivalent to a value with nil
;; appended on the end.  Thus, a vector '(nil t x t) is equivalent
;; to the vector '(nil t x t nil nil nil).  This equivalence
;; leads to simpler functions that take advantage of the fact that
;; (car nil)=nil.  However, within a correctly typed-DE expression,
;; a bit vectur will take on a well-known length, and only be compared to
;; equal length vectors.

(defun bbit-and (x y)
  (if x (if y t nil) nil))

(defun tbit-and (x y)
  (cond
   ((or (lowp x) (lowp y))
    'nil)
   ((or (xValp x) (xValp y))
    (xval))
   (t 't)))

(defund unary-and-help (n lst)
  (if (zp n)
      t
    (bbit-and (car lst) (unary-and-help (1- n) (cdr lst)))))

(defun unary-and (n x)
  (list (unary-and-help n x)))

(defun bbit-or (x y)
  (if x t (if y t nil)))

(defun tbit-or (x y)
  (cond
   ((or (highp x) (highp y))
    't)
   ((or (xValp x) (xValp y))
    (xval))
   (t 'nil)))

(defund unary-or-help (n lst)
  (if (zp n)
      nil
    (bbit-or (car lst) (unary-or-help (1- n) (cdr lst)))))

(defun unary-or (n x)
  (list (unary-or-help n x)))

(defund bv-and (n x y)
  (if (zp n)
      nil
    (cons (bbit-and (car x) (car y)) (bv-and (1- n) (cdr x) (cdr y)))))

(defund bv-or (n x y)
  (if (zp n)
      nil
    (cons (bbit-or (car x) (car y)) (bv-or (1- n) (cdr x) (cdr y)))))

(defun bbit-xor (x y)
  (if x (if y nil t) (if y t nil)))

(defun tbit-xor (x y)
  (cond
   ((and (lowp x) (lowp y))
    'nil)
   ((or (xValp x) (xValp y))
    (xval))
   ((or (lowp x) (lowp y))
    't)
   (t 'nil)))

(defund bv-xor (n x y)
  (if (zp n)
      nil
    (cons (bbit-xor (car x) (car y)) (bv-xor (1- n) (cdr x) (cdr y)))))

(defun bbit-not (x)
  (not x))

(defun tbit-not (x)
  (cond
   ((lowp x)
    't)
   ((xValp x)
    (xval))
   (t 'nil)))

(defun bv-eq (n x y)
  (unary-and n (bv-not n (bv-xor n x y))))

(defun append-n (n x y)
  (if (zp n)
      y
    (cons (car x) (append-n (1- n) (cdr x) y))))

(defun a-n (n A B)
  (append-n n A B))

(defun bit-2-bool (n)
  (if (zp n) nil t))

(defund bv-const (w x)
  (if (zp w)
      nil
    (cons (bit-2-bool (mod x 2))
          (bv-const (1- w) (floor x 2)))))

(defun nth-sublist (n lst)
  (if (zp n)
      nil
    (cons (car lst) (nth-sublist (1- n) (cdr lst)))))

(defun get-sublist-h (lst lbit hbit)
  (if (zp lbit)
      (nth-sublist (1+ hbit) lst)
    (get-sublist-h (cdr lst) (1- lbit) (1- hbit))))


(defun np (x)
  (if (integerp x)
      (< x 0)
    t))

(defun nnfix (x)
  (if (np x)
      -1
    x))


(defun n-nils (n)
  (if (zp n)
      nil
    (cons nil (n-nils (1- n)))))


(defun nth-cdr (n x)
  (if (zp n)
      x
    (nth-cdr (1- n) (cdr x))))

(defun get-sublist (lst lbit hbit)
  (if (<= (nfix lbit) (nnfix hbit))
      (get-sublist-h lst lbit hbit)
    nil))

(defun g (lst lbit hbit)
  (get-sublist lst lbit hbit))

(defun update-sublist-h (lst lbit hbit val)
  (if (zp lbit)
      (append-n (1+ hbit)
                (get-sublist val lbit hbit)
                (nth-cdr (1+ hbit) lst))
    (cons (car lst)
          (update-sublist-h (cdr lst) (1- lbit) (1- hbit)
                            val))))

(defun update-sublist (lst lbit hbit val)
  (if (<= (nfix lbit) (nnfix hbit))
      (update-sublist-h lst lbit hbit val)
    lst))

(defun us (lst lbit hbit val)
  (update-sublist lst lbit hbit val))


(defund bv-decode-help (n rev-x)
  (declare (xargs :measure (nfix (1+ n))))
  (let ((len-h-ans (expt 2 (1- n)))) ;; half of the length of the answer
    (cond
     ((zp n)
      '(t))
     ((car rev-x)
      (append-n len-h-ans (n-nils len-h-ans) (bv-decode-help (1- n) (cdr rev-x))))
     (t
      (append-n len-h-ans (bv-decode-help (1- n) (cdr rev-x)) (n-nils len-h-ans))))))

(defund bv-duplicate (n w x)
  (cond
   ((zp n) nil)
   (t (append-n w x (bv-duplicate (1- n) w x)))))

(defund expand-mask (n flush_mask)
  (if (zp n)
      nil
    (if (car flush_mask)
        (a-n 32 (bv-duplicate 32 1 (bv-const 1 1))
             (expand-mask (1- n) (cdr flush_mask)))
      (a-n 32 (bv-duplicate 32 1 (bv-const 1 0))
           (expand-mask (1- n) (cdr flush_mask))))))

(defun true-bvp (x) (car x))

(defund submaskp (n x y)
  (cond ((zp n)
         t)
        ((or (not (car x)) (car y))
         (submaskp (1- n) (cdr x) (cdr y)))
        (t nil)))

(defun simple-mult1 (n sz a curr-b ans)
  (if (zp n)
      ans
    (simple-mult1
     (1- n)
     (1+ sz)
     (cdr a)
     (cons nil curr-b)
     (if (car a) (v-adder sz nil curr-b ans) ans))))

;; Multiply the n, bit, bit-vectors a and b using
;; n adders.
(defun simple-mult (n a b)
  (simple-mult1 n n a b nil))

;; ----------------------------------------------------------
;;
;; Test helper functions

;;(define-external-tool sat)


(defmacro new-problem ()
  `(sat-new-problem $sat state))

(defmacro sat-add-conc (x)
  `(sat-add-expr t (quote ,x) $sat state))

(defmacro sat-add-hyp (x)
  `(sat-add-expr nil (quote ,x) $sat state))

(defmacro sat-check ()
  `(sat-solve $sat state))

(defun sat-assert (pred test-string expr prop-name)
  (prog2$
   (cond
    ((not expr)
     nil)
    (t (cw "~s0 expression: ~x1~%" test-string expr)))
   (prog2$
    (cond
     (prop-name
      (cw (concat-str test-string ": " (symbol-name prop-name) "~%")))
     (t
      (cw (concat-str test-string "~%"))))
    (cond
     (pred
      0)
     (t
      (er hard 'sat-assert "Assertion failed~%"))))))

(defmacro check-sat-invalid (&key name)
  `(mv-let
    (erp soln $sat state)
    (sat-solve $sat state)
    (let ((val (sat-assert (equal soln 'acl2::sat)
                           "Invalid test"
                           nil
                           ,name)))
      (declare (ignore val))
      (mv erp $sat state))))

(defmacro check-sat-valid (&key name)
  `(mv-let
    (erp soln $sat state)
    (sat-solve $sat state)
    (let ((val (sat-assert (equal soln 'acl2::unsat)
                           "Valid test"
                           nil
                           ,name)))
      (declare (ignore val))
      (mv erp $sat state))))

(defun translate-list (expr-list ans state)
  (declare (xargs :mode :program))
  (cond
   ((endp expr-list)
    (mv ans state))
   (t
    (mv-let
     (flg trans-expr bindings state)
     ;; I'm not sure if this is the right translate function, I got
     ;; it by following the :trans functionality.
     (translate1 (car expr-list) nil nil t 'translate-list (w state) state)
     (declare (ignore flg bindings))
     (translate-list (cdr expr-list)
                     (cons trans-expr ans)
                     state)))))

(defun parse-hyp-list (expr-list ans)
  (cond
   ((endp expr-list)
    ans)
   (t
    (let ((expr (car expr-list)))
      (cond
       ((atom expr)
        (parse-hyp-list (cdr expr-list) (cons expr ans)))
       ((eq 'and (car expr))
        (parse-hyp-list (append (cdr expr) (cdr expr-list))
                        ans))
       (t
        (parse-hyp-list (cdr expr-list) (cons expr ans))))))))

(defun parse-property (expr)
  (cond
   ((atom expr)
    (mv nil (list expr)))
   ((eq (car expr) 'implies)
    (mv (parse-hyp-list (list (cadr expr)) nil)
        (list (caddr expr))))
   (t
    (mv nil (list expr)))))

(defun parse-and-translate (property state)
  (declare (xargs :mode :program))
  (mv-let
   (hyp-list conc-list)
   (parse-property property)
   (mv-let
    (hyp-list state)
    (translate-list hyp-list nil state)
    (mv-let
     (conc-list state)
     (translate-list conc-list nil state)
     (mv hyp-list conc-list state)))))

(set-irrelevant-formals-ok t)
(defun check-counter-example1 (name hyp-list conc-list ce-alist state)
  (declare (xargs :mode :program))
  (cond
   ((and (endp hyp-list) (endp conc-list))
    (mv nil state))
   ((endp hyp-list)
    (mv-let
     (erp eval-output state)
     (simple-translate-and-eval (car conc-list)
                                ce-alist
                                nil ;;'($sat)
                                "Counter-example check"
                                "run-ce"
                                (w state)
                                state

; Matt K.: I added the argument aok=nil for v4-0.  Thus, attachments are
; disallowed.  That's the conservative thing to do, but I don't know if it's
; necessary here (probably is but not sure).  This decision could be revisited
; if there is interest.

                                nil)
     (cond
      (erp
       (mv (er hard 'run-clause
               "Counter example check failed.  Perhaps the formula is not ~
                executable.")
           state))
      (t
       (let ((val (sat-assert (not (cdr eval-output))
                              "Checking counter-example"
                              (car conc-list)
                              name)))
         (declare (ignore val))
         (check-counter-example1 name nil (cdr conc-list) ce-alist state))))))
   (t
    (mv-let
     (erp eval-output state)
     (simple-translate-and-eval (car hyp-list)
                                ce-alist
                                nil ;;'($sat)
                                "Counter-example check"
                                "run-ce"
                                (w state)
                                state
                                nil) ; see comment about aok above
     (cond
      (erp
       (mv (er hard 'run-clause
               "Counter example check failed.  Perhaps the formula is not ~
                executable.")
           state))
      (t
       (let ((val (sat-assert (cdr eval-output)
                              "Checking counter-example"
                              (car hyp-list)
                              name)))
         (declare (ignore val))
         (check-counter-example1 name (cdr hyp-list) conc-list ce-alist
                                 state))))))))

;; I'm turning off guard-checking before running the counter-example, since
;; there is no guarantee that the counter-example will obey the guard
;; restrictions
(defun check-counter-example (name no-ce-check hyp-list conc-list $sat state)
  (declare (xargs :stobjs $sat
                  :mode :program))
  (cond
   (no-ce-check
    (mv $sat state))
   (t
    (let* ((curr-flg (get-global 'guard-checking-on state))
           (state (put-global 'guard-checking-on nil state)))
      (mv-let
       (erp $sat state)
       (sat-generate-satisfying-instance $sat state)
       (declare (ignore erp))
       (mv-let
        (erp ce-alist $sat state)
        (sat-si-input-alist $sat state)
        (declare (ignore erp))
        (mv-let
         (erp state)
         (check-counter-example1 name hyp-list conc-list ce-alist state)
         (declare (ignore erp))
         (let ((state (put-global 'guard-checking-on curr-flg state)))
           (mv $sat state)))))))))

(defun check-invalid-hyp-list-inc (name expr-list partial-valid no-ce-check added-hyp-list
                                        added-conc-list $sat state)
  (declare (xargs :stobjs $sat
                  :mode :program))
  (cond
   ((endp expr-list)
    (mv $sat state))
   (t
    (let* ((added-hyp-list (cons (car expr-list) added-hyp-list)))
      (mv-let
       (erp $sat state)
       (sat-add-expr nil (car expr-list) $sat state)
       (declare (ignore erp))
       (mv-let
        (erp soln $sat state)
        (sat-solve $sat state)
        (declare (ignore erp))
        (cond
         ((and partial-valid (equal soln 'acl2::unsat))
          (check-invalid-hyp-list-inc name (cdr expr-list) partial-valid
                                      no-ce-check added-hyp-list added-conc-list $sat
                                      state))
         (t
          (let ((val (sat-assert (equal soln 'acl2::sat)
                                 "Incremental invalidity test"
                                 (car expr-list)
                                 name)))
            (declare (ignore val))
            (mv-let
             ($sat state)
             (check-counter-example name no-ce-check added-hyp-list
                                    added-conc-list $sat state)
             (check-invalid-hyp-list-inc name (cdr expr-list) partial-valid
                                         no-ce-check added-hyp-list
                                         added-conc-list $sat state)))))))))))

(defun check-invalid-conc-list-inc (name expr-list partial-valid no-ce-check added-hyp-list
                                         added-conc-list $sat state)
  (declare (xargs :stobjs $sat
                  :mode :program))
  (cond
   ((endp expr-list)
    (mv $sat state))
   (t
    (let* ((added-conc-list (cons (car expr-list) added-conc-list)))
      (mv-let
       (erp $sat state)
       (sat-add-expr t (car expr-list) $sat state)
       (declare (ignore erp))
       (mv-let
        (erp soln $sat state)
        (sat-solve $sat state)
        (declare (ignore erp))
        (cond
         ((and partial-valid (equal soln 'acl2::unsat))
          (check-invalid-conc-list-inc name (cdr expr-list) partial-valid
                                       no-ce-check added-hyp-list added-conc-list $sat
                                       state))
         (t
          (let ((val (sat-assert (equal soln 'acl2::sat)
                                 "Incremental invalidity test"
                                 (car expr-list)
                                 name)))
            (declare (ignore val))
            (mv-let
             ($sat state)
             (check-counter-example name no-ce-check added-hyp-list
                                    added-conc-list $sat state)
             (check-invalid-conc-list-inc name (cdr expr-list) partial-valid
                                          no-ce-check added-hyp-list
                                          added-conc-list $sat state)))))))))))

(defun thm-sat-valid-inc1 (property name partial-valid no-ce-check $sat state)
  (declare (xargs :stobjs $sat
                  :mode :program))
  (mv-let
   (erp $sat state)
   (sat-new-problem $sat state)
   (declare (ignore erp))
   (mv-let
    (hyp-list conc-list state)
    (parse-and-translate property state)
    (let* ((last-conc (car conc-list))
           (conc-list (cdr conc-list)))
      (mv-let
       ($sat state)
       (check-invalid-hyp-list-inc name hyp-list partial-valid no-ce-check nil nil $sat state)
       (mv-let
        ($sat state)
        (check-invalid-conc-list-inc name conc-list partial-valid no-ce-check hyp-list nil $sat state)
        (mv-let
         (erp $sat state)
         (sat-add-expr t last-conc $sat state)
         (declare (ignore erp))
         (mv-let
          (erp soln $sat state)
          (sat-solve $sat state)
          (declare (ignore erp))
          (let ((val (sat-assert (equal soln 'acl2::unsat)
                                 "Final validity test"
                                 last-conc
                                 name)))
            (declare (ignore val))
            (mv $sat state))))))))))

;; An incremental version of thm-sat-valid
(defmacro thm-sat-valid-inc (property &key name partial-valid no-ce-check)
  `(make-event
    (mv-let
     ($sat state)
     (thm-sat-valid-inc1 (quote ,property) (quote ,name) (quote ,partial-valid)
                         (quote ,no-ce-check) $sat state)
     (mv nil `(value-triple 'valid) state $sat))))

(defun thm-sat-invalid-inc1 (property name no-ce-check $sat state)
  (declare (xargs :stobjs $sat
                  :mode :program))
  (mv-let
   (erp $sat state)
   (sat-new-problem $sat state)
   (declare (ignore erp))
   (mv-let
    (hyp-list conc-list state)
    (parse-and-translate property state)
    (mv-let
     ($sat state)
     (check-invalid-hyp-list-inc name hyp-list nil no-ce-check nil nil $sat state)
     (check-invalid-conc-list-inc name conc-list nil no-ce-check hyp-list nil $sat state)))))

;; An incremental version of thm-sat-invalid
(defmacro thm-sat-invalid-inc (property &key name no-ce-check)
  `(make-event
    (mv-let
     ($sat state)
     (thm-sat-invalid-inc1 (quote ,property) (quote ,name) (quote ,no-ce-check)
                           $sat state)
     (mv nil `(value-triple 'invalid) state $sat))))

(defmacro assert-no-error1 (expr)
  `(make-event
    (let (($sat ,expr))
      (mv nil `(value-triple 'no-error) state $sat))))

(defmacro assert-no-error3 (expr)
  `(make-event
    (mv-let
     (erp $sat state)
     ,expr
     (if erp (mv erp nil state $sat)
       (mv nil `(value-triple 'no-error) state $sat)))))

(defmacro assert-no-error4 (expr)
  `(make-event
    (mv-let
     (erp soln $sat state)
     ,expr
     (if erp (mv erp nil state $sat)
       (mv nil (list 'value-triple (list 'quote soln)) state $sat)))))

;; Now we have uninterpreted functions!

(defstub uf1 (*) => *)
(defstub uf3 (* * *) => *)

;; ... thm-sat-invalid-inc...

;;:comp t

;;(i-am-here)

;; -----------------------------------------------------------------
;; Testing new interface

(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(equal x y) $sat state))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-generate-satisfying-instance $sat state))
(assert-no-error4 (sat-si-input-alist $sat state))

(assert-no-error3 (sat-add-expr nil '(equal x (quote t)) $sat state))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-generate-satisfying-instance $sat state))
(assert-no-error4 (sat-si-input-alist $sat state))

(assert-no-error3 (sat-add-expr nil '(equal x (quote nil)) $sat state))
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(iff x y) $sat state))
(assert-no-error3 (sat-add-expr nil '(equal x (quote nil)) $sat state))
(assert-no-error3 (sat-add-expr nil 'y $sat state))
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(iff x y) $sat state))
(assert-no-error3 (sat-add-expr nil 'x $sat state))
(assert-no-error3 (sat-add-expr nil 'y $sat state))
(assert-no-error3 (sat-add-expr t '(equal x y) $sat state))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-generate-satisfying-instance $sat state))
(assert-no-error4 (sat-si-input-alist $sat state))

(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(equal x y) $sat state))
(assert-no-error3 (sat-add-expr t '(equal (uf1 x) (uf1 y)) $sat state))
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(equal (uf1 x) (uf1 y)) $sat state))
(assert-no-error3 (check-sat-invalid))

(assert-no-error3 (sat-instance-exploration-begin $sat state))
(assert-no-error4 (sat-ie-emptyp $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-set 4 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-emptyp $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-set 5 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-set 6 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-emptyp $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-find-val $sat state))
(assert-no-error4 (sat-ie-set 6 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-emptyp $sat state))
(assert-no-error3 (sat-instance-exploration-end $sat state))


(assert-no-error3 (sat-new-problem $sat state))
(assert-no-error3 (sat-add-expr nil '(equal (uf1 x) (uf1 y)) $sat state))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-instance-exploration-begin $sat state))
(assert-no-error4 (sat-ie-emptyp $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-set 4 $sat state))
(assert-no-error4 (sat-ie-set 5 $sat state))
(assert-no-error3 (sat-instance-exploration-end $sat state))
(assert-no-error3 (sat-add-expr nil '(booleanp (uf1 x)) $sat state))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-instance-exploration-begin $sat state))
(assert-no-error4 (sat-ie-current-expr $sat state))
(assert-no-error4 (sat-ie-set 4 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-set 5 $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-find-val $sat state))
(assert-no-error4 (sat-ie-set 6 $sat state))
(assert-no-error4 (sat-ie-set t $sat state))
(assert-no-error3 (sat-ie-next $sat state))
(assert-no-error4 (sat-ie-set t $sat state))
(assert-no-error3 (sat-instance-exploration-end $sat state))
(assert-no-error3 (sat-add-expr nil '(uf1 x) $sat state))

;; -----------------------------------------------------------------

;; -----------------------------------------------------------------
;; Testing incrementality

;; Not embedded events...
(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-conc (iff x y)))
(assert-no-error3 (check-sat-invalid))

(assert-no-error3 (sat-add-hyp (equal x y)))
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-conc (n-nth '500 x)))
(assert-no-error3 (sat-add-hyp (n-nth '500 x)))
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-conc (n-nth '500 x)))
(assert-no-error3 (sat-add-hyp (n-nth '500 y)))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-add-hyp (n-nth '500 (bv-not '1000 (bv-not '1000 x)))))
(assert-no-error3 (check-sat-valid))
(assert-no-error3 (sat-add-hyp (n-nth '500 y)))
;; Number of variables really should only go up by 1!
;; Number of clauses really should also only go up by 1!
(assert-no-error3 (check-sat-valid))

(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-hyp (consp x)))
(assert-no-error3 (sat-add-hyp (consp y)))
(assert-no-error3 (sat-add-hyp (implies a (equal (car x) (car y)))))
(assert-no-error3 (sat-add-hyp (implies a (equal (cdr x) (cdr y)))))
(assert-no-error3 (sat-add-hyp (implies b (equal (car y) 't))))
(assert-no-error3 (sat-add-hyp (implies c (equal (car y) '4))))
(assert-no-error3 (sat-add-hyp (implies d (equal (car y) a))))
(assert-no-error3 (sat-add-hyp (implies b (equal (cdr y) 't))))
(assert-no-error3 (sat-add-hyp (implies c (equal (cdr y) '4))))
(assert-no-error3 (sat-add-hyp (implies d (equal (cdr y) a))))
(assert-no-error3 (sat-add-conc (equal x y)))
(assert-no-error3 (check-sat-invalid))
(assert-no-error3 (sat-add-hyp a))
(assert-no-error3 (check-sat-valid))
;; These shouldn't create more and more variables...
(assert-no-error3 (sat-add-hyp (equal (car y) '5)))
(assert-no-error3 (check-sat-valid))
(assert-no-error3 (sat-add-hyp (equal (car y) '6)))
(assert-no-error3 (check-sat-valid))
(assert-no-error3 (sat-add-hyp (equal (car y) 'nil)))
(assert-no-error3 (check-sat-valid))
(assert-no-error3 (sat-add-hyp (equal (car y) '7)))
(assert-no-error3 (check-sat-valid))

;; A Simple COI Check
(thm-sat-valid-inc
  (iff (n-nth 500 (bv-not 1000 (bv-not 1000 x)))
       (n-nth 500 x))
  :name coi-check-0)

(thm-sat-unknown
  (n-bleq 2 x x)
  :hint-arg '(:uninterpreted-functions (n-bleq)))

(assert-no-error3 (sat-end-problem! $sat state))

;; Start with something easy
(thm-sat-valid-inc
  (n-bleq 2 x x))

(thm-sat-invalid-inc
  (n-bleq 2 x y))

(thm-sat-valid-inc
  (n-bleq 2 (bv-not 4 x) (bv-not 4 x)))

(thm-sat-valid-inc
 (implies
  (equal x y)
  (equal (uf1 x) (uf1 y)))
 :name un-fn-axiom)

(thm-sat-invalid-inc
 (equal (uf1 x) (uf1 y))
 :no-ce-check t)

(thm-sat-valid-inc
 (implies
  (and (equal x0 y0)
       (equal x1 y1)
       (equal x2 y2))
  (equal (uf3 x0 x1 x2) (uf3 y0 y1 y2)))
 :name un-fn-axiom3)

(thm-sat-invalid-inc
 (implies
  (and (equal x0 y0)
       (equal x1 y1))
  (equal (uf3 x0 x1 x2) (uf3 y0 y1 y2)))
 :no-ce-check t)

(thm-sat-invalid
 (implies
  (and (equal x0 y0)
       (equal x1 y1))
  (equal (uf3 x0 x1 x2) (uf3 y0 y1 y2)))
 :hint-arg '(:check-counter-example nil))

(thm-sat-valid
 (implies
  (and (equal x0 y0)
       (equal x1 y1)
       (equal x2 y2))
  (equal (uf3 x0 x1 x2) (uf3 y0 y1 y2))))

(thm-sat-valid
 (implies
  (and (equal x0 (uf1 a))
       (equal y0 (uf1 c))
       (equal a b)
       (equal b c))
  (equal (uf3 x0 x1 x2) (uf3 y0 x1 x2))))


(thm-sat-invalid
 (implies
  (and (equal x0 (uf1 a))
       (equal y0 (uf1 c))
       (equal b c))
  (equal (uf3 x0 x1 x2) (uf3 y0 x1 x2)))
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (and (uf1 e)
       (equal (uf1 e) (uf3 a b c)))
  nil)
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (and (equal x0 (uf1 a))
       (equal y0 (uf1 c))
       (uf1 d)
       (uf1 e)
       (equal (uf1 e) (uf3 a b c))
       (equal b c))
  (equal (uf3 x0 x1 x2) (uf3 y0 x1 x2)))
 :hint-arg '(:check-counter-example nil))

; The rest are commented out by Matt K. because SBCL Version 1.0.16 with
; #+sb-thread has caused the following error on 32-bit linux running on a
; 64-bit machine:

; Error:  Heap exhausted: 6393856 bytes available, 12000016 requested. PROCEED WITH CAUTION!

; A similar error seems to occur for the first few forms after the first below,
; as well, so we comment them all out.

#||
(thm-sat-valid
 (implies
  (and (equal x0 (uf1 a))
       (equal y0 (uf1 c))
       (uf1 d)
       (uf1 e)
       (equal (uf1 e) (uf3 a b c))
       (equal b c)
       (equal a c))
  (equal (uf3 x0 x1 x2) (uf3 y0 x1 x2))))

(thm-sat-invalid
 (implies
  (and (car (unary-and 8 (uf1 a)))
       (car (unary-and 8 (uf1 b))))
  (equal (uf1 a) (uf1 b)))
 :hint-arg '(:check-counter-example nil))

(thm-sat-valid
 (implies
  (and (true-bvp (unary-and 8 (uf1 a)))
       (true-bvp (unary-and 8 (uf1 b))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b)))))

(thm-sat-invalid
 (implies
  (and (true-bvp (unary-and 7 (cdr (uf1 a))))
       (true-bvp (unary-and 8 (uf1 b))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (and (true-bvp (unary-and 7 (cdr (uf1 a))))
       (true-bvp (unary-and 8 (uf1 b))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))

(defun uf1-if-t (x a)
  (if x
      (uf1 a)
    nil))

(thm-sat-invalid
 (implies
  (and (true-bvp (unary-and 7 (cdr (uf1-if-t t a))))
       (true-bvp (unary-and 8 (uf1-if-t t b))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))

(thm-sat-valid
 (implies
  (and (true-bvp (unary-and 8 (uf1-if-t t a)))
       (true-bvp (unary-and 8 (uf1-if-t t b))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b)))))

(thm-sat-valid
 (implies
  (and (not (true-bvp (unary-or 8 (uf1-if-t t a))))
       (not (true-bvp (unary-or 8 (uf1-if-t t b)))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b)))))

(thm-sat-invalid
 (implies
  (and (not (true-bvp (unary-or 8 (uf1-if-t nil a))))
       (not (true-bvp (unary-or 8 (uf1-if-t t b)))))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (and (not (true-bvp (unary-or 8 (uf1-if-t nil a))))
       (not (true-bvp (unary-or 8 (uf1-if-t t b))))
       (true-bvp (bv-eq 8 a b)))
  (true-bvp (bv-eq 8 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (true-bvp (bv-eq 3 a b))
  (true-bvp (bv-eq 3 (uf1 a) (uf1 b))))
 :hint-arg '(:check-counter-example nil))


(thm-sat-valid
 (implies
  (and (true-bvp (bv-eq 3 a b))
       (bvp 3 a)
       (bvp 3 b))
  (true-bvp (bv-eq 3 (uf1 a) (uf1 b)))))

(thm-sat-invalid
 (implies
  (car (uf1 b))
  (equal (car (uf1 b)) nil))
 :hint-arg '(:check-counter-example nil))

(thm-sat-invalid
 (implies
  (and (uf3 (uf1 x0) y1 y2)
       (equal x0 nil)
       (equal x1 nil))
  (uf3 x1 y1 y2))
 :hint-arg '(:check-counter-example nil))

(thm-sat-valid
 (implies
  (and (uf3 (uf1 x0) y1 y2)
       (equal x0 nil)
       (equal x1 nil))
  (uf3 (uf1 x1) y1 y2)))

(thm-sat-invalid
 (implies
  (and (uf3 (uf1 x0) y1 (uf1 x1))
       (equal x0 nil)
       (equal x1 nil))
  (uf3 (uf1 x1) y1 y2))
 :hint-arg '(:check-counter-example nil))

;;(i-am-here)

(thm-sat-valid
 (implies
  (and (equal x1 (uf1 x1)))
  (equal (uf3 (uf1 x1) x2 x3) (uf3 x1 x2 x3))))

(thm-sat-valid
 (implies
  (and (true-bvp (unary-and 2000 (uf1 a)))
       (true-bvp (unary-and 2000 (uf1 b))))
  (true-bvp (bv-eq 2000 (uf1 a) (uf1 b)))))

(thm-sat-valid
 (implies
  (and (true-bvp (unary-and 2000 a))
       (true-bvp (unary-and 2000 b)))
  (true-bvp (bv-eq 2000 a b))))

;; Now we have equality!

(thm-sat-invalid-inc
  (equal x y))

(thm-sat-invalid-inc
  (implies
   (and (not (Booleanp x))
        (not (Booleanp y)))
   (equal x y))
  :name boolean-implies-equal)

(thm-sat-valid-inc
  (implies (and (equal x y)
                (equal y z))
           (equal x z)))

(thm-sat-invalid-inc
  (implies (and (equal x 6)
                (equal y z))
           (equal z 6))
  :name bad-transitivity)

(thm-sat-valid-inc
  (implies (and (equal y 6)
                (equal y z))
           (equal z 6)))

(thm-sat-invalid-inc
  (implies (and (equal x0 6)
                (equal x0 x1)
                (equal x2 x3)
                (equal x3 6))
           (not (equal x1 x2))))

(thm-sat-valid-inc
  (implies (and (equal x0 6)
                (equal x0 x1)
                (equal x2 x3)
                (equal x3 6))
           (equal x1 x2)))

(thm-sat-valid-inc
  (implies (and (equal x0 6)
                (equal x0 x1)
                (equal x2 x3)
                (equal x3 7))
           (not (equal x1 x2))))

(thm-sat-invalid-inc
  (implies (and (equal x0 6)
                (equal x0 x1)
                (equal x2 x3))
           (not (equal x1 x2))))

(thm-sat-invalid-inc
  (implies (and (equal x0 6)
                (equal x0 x1)
                (equal x2 x3)
                (not (Booleanp x2)))
           (equal x1 x2)))

(thm-sat-valid-inc
 (implies (and (consp x)
               (consp y)
               (implies a (equal (car x) (car y)))
               (implies a (equal (cdr x) (cdr y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies c (equal (cdr y) 4))
               (implies d (equal (cdr y) a))
               a)
          (equal x y)))

(thm-sat-valid-inc
 (implies (and (consp x)
               (consp y)
               (implies a (equal (car x) (car y)))
               (implies a (equal (cdr x) (cdr y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies d (equal (cdr y) a))
               a)
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (implies a (equal (car x) (car y)))
               (implies a (equal (cdr x) (cdr y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies c (equal (cdr y) 4))
               (implies d (equal (cdr y) a))
               a)
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp y)
               (implies a (equal (cdr x) (cdr y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies c (equal (cdr y) 4))
               (implies d (equal (cdr y) a))
               a)
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp y)
               (implies a (equal (car x) (car y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies c (equal (cdr y) 4))
               (implies d (equal (cdr y) a))
               a)
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp y)
               (implies a (equal (car x) (car y)))
               (implies a (equal (cdr x) (cdr y)))
               (implies b (equal (car y) t))
               (implies c (equal (car y) 4))
               (implies d (equal (car y) a))
               (implies b (equal (cdr y) t))
               (implies c (equal (cdr y) 4))
               (implies d (equal (cdr y) a)))
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (equal (car x) (car y))
               (equal (car y) (car z))
               (equal (cdr x) (cdr y))
               (equal (cdr y) (cdr z)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp z)
               (equal (car x) (car y))
               (equal (car y) (car z))
               (equal (cdr x) (cdr y))
               (equal (cdr y) (cdr z)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp z)
               (equal (car y) (car z))
               (equal (cdr x) (cdr y))
               (equal (cdr y) (cdr z)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp z)
               (equal (car x) (car y))
               (equal (cdr x) (cdr y))
               (equal (cdr y) (cdr z)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp z)
               (equal (car x) (car y))
               (equal (car y) (car z))
               (equal (cdr y) (cdr z)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp z)
               (equal (car x) (car y))
               (equal (car y) (car z))
               (equal (cdr x) (cdr y)))
          (equal x z)))

(thm-sat-invalid-inc
 (implies (and (consp y)
               (equal (car x) (car y))
               (equal (cdr x) (cdr y)))
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (equal (car x) (car y))
               (equal (cdr x) (cdr y)))
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp y)
               (equal (cdr x) (cdr y)))
          (equal x y)))

(thm-sat-invalid-inc
 (implies (and (consp x)
               (consp y)
               (equal (car x) (car y)))
          (equal x y)))

(thm-sat-valid-inc
 (implies (and (equal a (car x))
               (equal (car x) (cdr x))
               (equal (cdr x) b))
          (equal a b))
 :name transitivity-through-car-cdr)

(thm-sat-valid-inc
 (implies (and (equal a (car x))
               (equal (cdr x) (car x))
               (equal (cdr x) b))
          (equal a b))
 :name transitivity-through-cdr-car)

(thm-sat-invalid-inc
 (implies (and (equal a (car x))
               (equal (cdar x) (caar x))
               (equal (cdr x) b))
          (equal a b)))

;; nil implies anything.
(thm-sat-valid-inc
  (implies (and (equal x0 6)
                (equal x0 7))
           (equal y 5))
  :partial-valid t
  :name nil-implies-anything)

(thm-sat-invalid-inc
  (implies (and (equal (car x) 4)
                (equal (cdr x) 5)
                (equal x y))
           (equal y '(4 5))))

(thm-sat-valid-inc
  (implies (and (equal (car x) 4)
                (equal (cdr x) 5)
                (equal x y))
           (equal y '(4 . 5))))

(thm-sat-invalid-inc
  (implies (and (consp x)
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-invalid-inc
  (implies (and (not (consp x))
                (not (consp y))
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (equal x y))
  :name not-consp-doesnt-imply-equal)

(thm-sat-valid-inc
  (implies (and (consp x)
                (consp y)
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-valid-inc
  (implies (and (consp (car x))
                (consp y)
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-invalid-inc
  (implies (and (consp (car x))
                (consp y)
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (not (equal x y))))

(thm-sat-valid-inc
  (implies (and (consp (car x))
                (consp (cdr y))
                (equal (car x) (car y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-invalid-inc
  (implies (and (consp (car x))
                (consp (cdr y))
                (equal (caar x) (caar y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

;; Not embedded Events
(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-hyp (consp (car x))))
(assert-no-error3 (sat-add-hyp (consp (cdr y))))
(assert-no-error3 (sat-add-hyp (equal (car (car x)) (car (car y)))))
(assert-no-error3 (sat-add-hyp (not (equal (car (car x)) '0))))
(assert-no-error3 (sat-add-hyp (not (equal (car (car x)) '1))))
(assert-no-error3 (sat-add-hyp (not (equal (car (car x)) 'nil))))
(assert-no-error3 (sat-add-hyp (not (equal (car (car x)) 't))))
(assert-no-error3 (sat-add-hyp (not (equal (cdr (car y)) 'nil))))
(assert-no-error3 (sat-add-hyp (equal (cdr x) (cdr y))))
(assert-no-error3 (sat-add-conc (equal x y)))
(assert-no-error3 (check-sat-invalid))

(thm-sat-invalid-inc
  (implies (and (consp (car x))
                (consp (cdr y))
                (equal (caar x) (caar y))
                (not (equal (caar x) 0))
                (not (equal (caar x) 1))
                (not (equal (caar x) nil))
                (not (equal (caar x) t))
                (not (equal (cdar y) nil))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-valid-inc
  (implies (and (consp (car x))
                (consp (cdr y))
                (equal (caar x) (caar y))
                (not (equal (caar x) 0))
                (not (equal (caar x) 1))
                (not (equal (caar x) nil))
                (not (equal (caar x) t))
                (not (equal (cdar y) nil))
                (equal (cdar x) (cdar y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-valid-inc
  (implies (and (consp x)
                (consp (cdr y))
                (equal (caar x) (caar y))
                (not (equal (caar x) 0))
                (not (equal (caar x) 1))
                (not (equal (caar x) nil))
                (not (equal (caar x) t))
                (not (equal (cdar y) nil))
                (equal (cdar x) (cdar y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-invalid-inc
  (implies (and (consp x)
                (consp (cdr y))
                (equal (caar x) (caar y))
                (not (equal (caar x) 0))
                (not (equal (caar x) 1))
                (not (equal (caar x) t))
                (equal (cdar x) (cdar y))
                (equal (cdr x) (cdr y)))
           (equal x y)))

(thm-sat-valid-inc
  (implies
   (and (not (equal (caaar x) nil)))
   (consp x))
  :name caaar-x-nil)

(thm-sat-invalid-inc
  (implies
   (and (not (equal (caar x) nil))
        (not (equal (cddr y) nil)))
   (equal x y)))

(thm-sat-invalid-inc
  (implies
   (and (not (equal (caar x) nil))
        (not (equal (cddr y) nil)))
   (not (equal x y))))

(thm-sat-valid-inc
  (equal x x))

(thm-sat-invalid-inc
  (equal x (not x)))

(thm-sat-valid-inc
  (not (equal x (not x))))

(thm-sat-invalid-inc
  (not (equal x (car x))))

(thm-sat-valid-inc
  (implies (not (equal x nil))
           (not (equal x (car x)))))

(thm-sat-invalid-inc
  (implies (not (equal x nil))
           (equal x t)))

(thm-sat-valid-inc
  (implies (and (or (equal x 0) (equal x 1))
                (equal x y)
                (not (equal y 0)))
           (equal x 1)))

(thm-sat-valid-inc
  (implies (and (equal (car x) 4)
                (equal (cdr x) 3)
                (equal y x))
           (equal y (cons 4 3))))

(thm-sat-invalid-inc
  (implies (and (equal (car x) nil)
                (equal (cdr x) nil)
                (equal y x))
           (equal y (cons nil nil))))

(thm-sat-valid-inc
  (implies (and (equal x nil))
           (equal (car x) nil)))

(thm-sat-valid-inc
  (implies (and (equal x 3))
           (equal (car x) nil)))

(thm-sat-valid-inc
  (implies (and (equal x y)
                (equal y z)
                (equal z a)
                (equal a b))
           (equal (car x) (car b))))

(thm-sat-invalid-inc
  (implies (and (equal x y)
                (equal y z)
                (equal a b))
           (equal (car x) (car b))))

(thm-sat-valid-inc
  (implies (and (equal z a)
                (equal y z)
                (equal x y)
                (equal a b))
           (equal (car x) (car b))))

(thm-sat-valid-inc
  (implies (and (not (equal x y))
                (or (equal x 0) (equal x 1))
                (equal y 0))
           (equal x 1)))

(thm-sat-valid-inc
  (implies (and (not (equal x y))
                (or (equal x 0) (equal x 1))
                (equal y 0))
           (equal (car x) nil)))

(thm-sat-invalid-inc
  (implies (and (not (equal x y))
                (or (equal (car x) nil) (equal (car x) t))
                (equal y 4))
           (equal (car x) nil)))

(thm-sat-valid-inc
  (implies (and (not (equal x y))
                (equal (cdr x) (cdr y))
                (consp x)
                (or (equal (car x) nil) (equal (car x) t))
                (equal y (cons nil nil)))
           (equal (car x) t)))

(thm-sat-valid-inc
  (implies (and (not (equal a b))
                (or (equal a nil) (equal a t))
                (equal x (cons a b))
                (equal y (cons b b))
                (equal (car y) nil))
           (equal (car x) t)))

(thm-sat-invalid-inc
  (not (equal x (car x)))
  :name x-equal-car-x)

(thm-sat-valid-inc
  (implies (consp x)
           (not (equal x (car x)))))

(thm-sat-valid-inc
  (implies (equal (caar x) 4)
           (not (equal x (car x)))))

(thm-sat-valid-inc
  (implies
   (and (equal x (cons y z))
        (equal y a)
        (equal a b))
   (equal x (cons b z))))

(thm-sat-invalid-inc
  (implies
   (and (equal x (cons y z))
        (equal y a)
        (equal a b))
   (equal x (cons b t))))

(thm-sat-invalid-inc
  (implies
   (and (equal x (cons (cons a b) (cons c d)))
        (equal y (cons (cons d c) (cons b a))))
   (equal (car x) (car y))))

(thm-sat-valid-inc
  (implies
   (and (equal x (equal a c))
        (equal a c)
        (equal b c))
   (equal x t)))

(thm-sat-valid-inc
  (implies
   (equal x (equal a c))
   (or (equal x t) (equal x nil))))

(thm-sat-valid-inc
  (not (equal (cons a b) (equal a c))))

(thm-sat-valid-inc
  (implies
   (equal x (consp y))
   (equal (car x) nil)))

(thm-sat-invalid-inc
  (implies
   (equal x (consp y))
   (not (equal (car x) nil))))

(thm-sat-invalid-inc
  (implies
   (equal x (consp y))
   (not (equal (car x) nil))))

(defun n-rev-append (n x y)
  (if (or (zp n) (atom x))
      y
    (n-rev-append (1- n) (cdr x) (cons (car x) y))))

(thm-sat-invalid-inc
  (equal x
         (n-rev-append 4 (n-rev-append 4 x nil) nil)))

(defun n-true-listp (n x)
  (if (or (zp n) (atom x))
      (equal x nil)
    (n-true-listp (1- n) (cdr x))))

(thm-sat-invalid-inc
  (implies
   (not (equal x t))
   (equal x
          (n-rev-append 4 (n-rev-append 4 x nil) nil))))

(thm-sat-invalid-inc
  (implies
   (consp x)
   (equal x
          (n-rev-append 4 (n-rev-append 4 x nil) nil))))

(thm-sat-valid-inc
  (implies
   (n-true-listp 4 x)
   (equal x
          (n-rev-append 4 (n-rev-append 4 x nil) nil))))

(thm-sat-invalid-inc
  (implies
   (n-true-listp 6 x)
   (equal x
          (n-rev-append 4 (n-rev-append 4 x nil) nil))))

(thm-sat-valid-inc
  (iff
   (equal (cons a b) (cons c d))
   (and (equal a c) (equal b d))))

(thm-sat-invalid-inc
  (implies
   (equal a c)
   (equal (cons a b) (cons c d))))

(thm-sat-valid-inc
  (not (equal (cons a b) (consp c))))

(thm-sat-valid-inc
  (not (equal (cons a b) nil)))

(thm-sat-invalid-inc
  (not (equal (cons a b) '(4))))

(thm-sat-valid-inc
  (not (equal (cons a b) '4)))

(thm-sat-valid-inc
  (implies
   (consp x)
   (equal x (cons (car x) (cdr x)))))

(thm-sat-invalid-inc
  (equal x (cons (car x) (cdr x))))

(defun n-boolean-listp (n x)
  (cond
   ((zp n)
    (equal x nil))
   ((atom x)
    nil)
   ((Booleanp (car x))
    (n-Boolean-listp (1- n) (cdr x)))
   (t
    nil)))

(thm-sat-invalid-inc
  (equal (bv-not 4 (bv-not 4 x)) x))

;; Commented out because it takes a while (and
;; a lot of disk space)
;;(thm-sat-valid-inc
;;   (implies
;;    (n-Boolean-listp 5000 x)
;;    (equal (bv-not 5000 (bv-not 5000 x)) x)))

;; Current results: Num-vars: 8003, Num-clauses: 1519506
;; Next step: Optimize (eq x nil) traversal.  If (eq x nil)
;; or (consp x) exist, I shouldn't have to keep going.
;; (thm-sat-valid-inc
;;   (implies
;;    (n-Boolean-listp 1000 x)
;;    (equal (bv-not 1000 (bv-not 1000 x)) x)))

;; (thm-sat-valid-inc
;;   (n-bleq 2 (bv-not 2 (bv-not 2 x)) x))

;;(thm-sat-valid-inc
;; (n-bleq 5000 (bv-not 5000 (bv-not 5000 x)) x))

(defun foo (x) (cons x 4))

(thm-sat-invalid-inc
  (implies
   (and (equal x (foo y))
        (equal (car y) (car z)))
   (equal (car x) (car z))))

(thm-sat-valid-inc
  (implies
   (and (equal x (foo y))
        (equal (car y) (car z)))
   (equal (caar x) (car z))))

(assert-no-error3 (new-problem))
(assert-no-error3 (sat-add-hyp (equal x (if a y z))))
(assert-no-error4 (sat-check))
(assert-no-error3 (sat-add-hyp (equal (car y) (car z))))
(assert-no-error4 (sat-check))

(thm-sat-valid-inc
  (implies
   (and (equal x (if a y z))
        (equal (car y) (car z)))
   (equal (car x) (car z)))
  :name car-x-equals-car-z-either-way)

(thm-sat-valid-inc
  (implies
   (and (equal (cons x0 x1) (if a y z))
        (equal (car y) (car z)))
   (equal x0 (car z))))

(thm-sat-invalid-inc
  (implies
   (and (equal (cons x0 x1) (if a y z))
        (equal (car y) (car z)))
   (equal x0 z)))

(thm-sat-valid-inc
  (implies
   (and (equal x y)
        (equal (car y) (car z)))
   (equal (car x) (car z))))

(thm-sat-invalid-inc
  (implies
   (equal x (cons a b))
   (consp a)))

(thm-sat-valid-inc
  (implies
   (equal x (cons a b))
   (consp x)))

(thm-sat-valid-inc
  (implies
   (and (equal x (cons a b))
        (equal x y))
   (consp y)))

(thm-sat-valid-inc
  (implies
   (and (equal x (cons a b))
        (equal x y))
   (equal (cdr y) b)))

(thm-sat-invalid-inc
  (not (equal (car x) (consp x))))

(thm-sat-invalid-inc
  (not (equal (consp y) (consp x))))

(thm-sat-invalid-inc
  (not (equal (equal a b) (consp x))))

(thm-sat-invalid-inc
  (not (equal (equal a b) (equal a c))))

(thm-sat-invalid-inc
  (implies
   (and (not (Booleanp a))
        (not (Booleanp b))
        (not (Booleanp c)))
   (not (equal (equal a b) (equal a c)))))

(thm-sat-invalid-inc
  (implies
   (consp x)
   (not (equal (car x) (cdr x)))))

(thm-sat-valid-inc
  (implies
   (and (equal (car x) (cons a b))
        (equal (cdr x) (cons c d)))
   (equal x (cons (cons a b) (cons c d)))))

(thm-sat-valid-inc
  (implies
   (and (equal (car x) (cons a b))
        (equal (cdr x) (cons c d))
        (equal 4 (cdr x)))
   nil)
  :partial-valid t
  :name nil-implies-nil)

(thm-sat-invalid-inc
  (implies
   (and (equal (car x) (cons a b))
        (equal (cdr x) (cons c d))
        (equal '(4) (cdr x)))
   nil))

(thm-sat-valid-inc
  (implies
   (and (equal (car x) (cons a b))
        (equal (cdr x) (cons c d))
        (equal '(4) (cdr x)))
   (equal c 4)))

(thm-sat-valid-inc
  (implies
   (and (equal (cons a b) (car x))
        (equal (cons c d) (cdr x))
        (equal '(4) (cdr x)))
   (equal c 4)))

(thm-sat-valid-inc
  (implies
   (and (equal (cons a b) (cons c d))
        (equal (car x) a)
        (equal (cdr x) b)
        (equal (car y) c)
        (equal (cdr y) d)
        (not (equal a nil)))
   (equal x y)))

(thm-sat-invalid-inc
  (implies
   (and (equal a c)
        (equal b d)
        (equal (car x) a)
        (equal (cdr x) b)
        (equal (car y) c)
        (equal (cdr y) d)
        (consp x))
   (equal x y)))

;; ... test some wierd cases, like (equal (consp x) (equal a b))!

;; Now I can prove things about Booleanp!
(thm-sat-valid-inc
  (implies (not (Booleanp x))
           x)
  :name first-property)

(thm-sat-invalid-inc
  (implies (not (Booleanp x))
           (not x)))

(thm-sat-invalid-inc
  (implies (Booleanp x)
           (Booleanp y)))

(thm-sat-invalid-inc
  (implies (equal x 1)
           (Booleanp y)))

(thm-sat-valid-inc
  (implies (equal x 1)
           (equal x 1)))

(thm-sat-valid-inc
  (implies (and (equal x 1)
                (not (equal y nil))
                (not (equal y t)))
           (not (Booleanp y))))

(thm-sat-valid-inc
  (implies (not (equal (car x) nil))
           (consp x)))

(thm-sat-invalid-inc
  (implies (consp x)
           (not (equal (car x) nil))))

(thm-sat-valid-inc
  (implies (and (equal (car x) 4)
                (equal (cdr x) 5))
           (equal x (cons 4 5))))

(thm-sat-valid-inc
  (implies (equal x '0)
           (not (equal x '4))))

(thm-sat-invalid-inc
  (implies (and (equal (car x) nil)
                (equal (cdr x) nil))
           (equal x (cons nil nil))))

(thm-sat-valid-inc
  (implies (and (equal (caar x) 0)
                (equal (cdar x) 1))
           (equal (car x) (cons 0 1))))

(thm-sat-invalid-inc
  (implies (and (equal (caar x) t)
                (equal (cdar x) t))
           (equal (car x) (cons t 1))))

(thm-sat-invalid-inc
  (implies (and (equal (caar x) 0)
                (equal (cdar x) 1))
           (equal x (cons (cons 0 1) nil))))

(thm-sat-valid-inc
 (implies (and (equal (caar x) 0)
                (equal (cdar x) 1))
           x))

(thm-sat-valid-inc
  (implies (and (equal (caar x) 4)
                (equal (cdar x) 5))
           (not (equal x 5))))

(thm-sat-valid-inc
  (implies (and (equal (caar x) 4)
                (equal (cdar x) 5))
           (consp x)))

(thm-sat-valid-inc
  (implies (eq (caar x) t)
           (not (eq (car x) (cons 6 7)))))

(thm-sat-valid-inc
  (implies (eq (car x) (cons 6 (cons 7 nil)))
           (consp (cdar x))))

;; A Simple COI Check
(thm-sat-valid-inc
  (iff (n-nth 500 (bv-not 1000 (bv-not 1000 x)))
       (n-nth 500 x))
  :name coi-check-1)
||#
