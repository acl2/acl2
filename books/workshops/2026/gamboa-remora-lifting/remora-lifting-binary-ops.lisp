(in-package "REMORA")

(include-book "kestrel/remora/top" :dir :system)
;; (include-book "std/omaps/submap" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

#|
(parse-from-string "(entry (main) (+ 3 4))")
->
((IMPORTS)
 (DECLS (:ENTRY "main" NIL NIL
                (:APPN (:VAR "+")
                       ((:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\3)))))
                        (:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\4))))))))))

(file->decls (parse-from-string "(entry (main) (+ 3 4))"))
->
((:ENTRY "main" NIL NIL
         (:APPN (:VAR "+")
                ((:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\3)))))
                 (:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\4)))))))))

(decl-entry->expr (car (file->decls (parse-from-string "(entry (main) (+ 3 4))"))))
->
(:APPN (:VAR "+")
       ((:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\3)))))
        (:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\4)))))))

(expr-appn->fun (decl-entry->expr (car (file->decls (parse-from-string "(entry (main) (+ 3 4))")))))
->
(:VAR "+")

(expr-appn->args (decl-entry->expr (car (file->decls (parse-from-string "(entry (main) (+ 3 4))")))))
->
((:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\3)))))
 (:ATOM (:BASE (:INT ((SIGN?) (DIGITS #\4))))))

;;; Gets binding from environment or NIL if not bound
(defun get-var-value (var denv)
  (b* ((var+val (omap::assoc var (denv->expr-vars denv)))
       ((unless var+val) nil))
    (cdr var+val)))
|#

(defconst *program-full*
  "(entry (main)
          (let ((fun (@dotpr (&t) ($n) (v [Int $n]) (w [Int $n]) : [Int])
                  (@reduce (Int) ((- $n 1) []) + (* v w)))
                (fun (@norm (&t) ($n) (v [Int $n]) : Int)
                  (@dotpr (&t) ($n) (v v))))
            (@dotpr (Int) (3) [1 2 3])))")

(defconst *program*
  "(entry (main)
          (* [[1 2 3] [4 5 6]] 2))")

(defconst *expr*
  (decl-entry->expr (car (file->decls (parse-from-string *program*)))))

(eval-expr *expr* (init-expr-denv) 10000)

(defconst *program-2*
  "(entry (main)
          (* [[1 2 3] [4 5 6]] [2 3]))")

(defconst *expr-2*
  (decl-entry->expr (car (file->decls (parse-from-string *program-2*)))))

(eval-expr *expr-2* (init-expr-denv) 10000)



;;; Checks whether the given environment extends
;;; the initial Remora dynamic environment without
;;; hiding any of the initial bindings
(defund valid-remora-denv-p (denv)
  (and (expr-denv-wfp denv)
       (omap::submap (expr-denv->exprs (init-expr-denv))
                     (expr-denv->exprs denv))
       (expr-value-listp (omap::values (expr-denv->exprs denv)))))

(defthm valid-remora-denv-p-expr-init-denv
    (valid-remora-denv-p (init-expr-denv)))

(defthm expr-value-p-assoc-valid-remora-denv
    (implies (and (valid-remora-denv-p denv)
                  (omap::assoc key
                               (expr-denv->exprs denv)))
             (expr-valuep (cdr (omap::assoc key
                                            (expr-denv->exprs denv))))))

(defthm values-are-not-errors
    (implies (expr-valuep x)
             (not (reserrp x))))

(defthm not-reserrp-assoc-valid-remora-denv
    (implies (and (valid-remora-denv-p denv)
                  (omap::assoc key
                               (expr-denv->exprs denv)))
             (not (reserrp (cdr (omap::assoc key
                                             (expr-denv->exprs denv)))))))

;; (defund primitive-operation-p (op)
;;   (omap::assoc op (expr-denv->exprs (init-expr-denv))))

(defthm eval-var
    ;;; Cf: eval-expr-when-var
    ;;; Instead of relying on the "limit", we do a partial correctness
    ;;; on eval-expr not returning an error. I think this will eneralize
    ;;; better
    (implies (and (exprp expr)
                  (valid-remora-denv-p denv)
                  (expr-case expr :var)
                  (not (reserrp (eval-expr expr denv limit)))
                  ;; (omap::assoc (expr-var->name expr)
                  ;;              (expr-denv->exprs denv))
                  ;; (posp limit)
                  ;; (<= 1 limit)
                  )
             (equal (eval-expr expr denv limit)
                    (expr-denv-lookup-expr (expr-var->name expr)
                                                denv)))
  :otf-flg t
  :hints (("Goal"
           :expand ((EVAL-EXPR EXPR DENV LIMIT))))
  )

(defun eval-int-binary-primop (op x y)
  (let ((ix (int-value->int
             (base-value-int->val
              (expr-value-base->val
               x))))
        (iy (int-value->int
             (base-value-int->val
              (expr-value-base->val
               y)))))
    (expr-value-base
     (base-value-int
      (int-value
       (int-binary-primop-case
        op
        :add (+ ix iy)
        :sub (- ix iy)
        :mul (* ix iy)
        :div (floor ix iy)
        :expt (expt ix iy)
        :mod (mod ix iy)
        :max (max ix iy)
        :min (min ix iy)
        :bit-and (logand ix iy)
        :bit-or (logior ix iy)
        :bit-xor (logxor ix iy)
        :shl (ash ix iy)
        :shr (ash ix (- iy))))))))

(defun list-of-base-values  (xs)
  (if (endp xs)
      t
      (and (expr-valuep (car xs))
           (expr-value-case (car xs) :base)
           (list-of-base-values (cdr xs)))))

(defthm base-values-are-well-formed
    (implies (list-of-base-values xs)
             (expr-value-list-wfp xs))
  :hints (("Goal"
           :in-theory (enable expr-value-list-wfp
                              expr-value-wfp
                              CHECK-DIMS-OF-EXPR-VALUE
                              ))))

(defun list-of-primop-int-binary (xs)
  (if (endp xs)
      t
      (and (expr-valuep (car xs))
           (expr-value-case (car xs) :primop)
           (primop-value-case (expr-value-primop->val (car xs)) :int-binary)
           (list-of-primop-int-binary (cdr xs)))))

(defun list-of-primop-int-binary-x (xs)
  (if (endp xs)
      t
      (and (expr-valuep (car xs))
           (expr-value-case (car xs) :primop)
           (primop-value-case (expr-value-primop->val (car xs)) :int-binary-x)
           (expr-value-case (primop-value-int-binary-x->xval (expr-value-primop->val (car xs))) :base)
           (list-of-primop-int-binary-x (cdr xs)))))

(defun list-of-list-of-base-values (xss)
  (if (endp xss)
      t
      (and (list-of-base-values (car xss))
           (list-of-list-of-base-values (cdr xss)))))

(defun list-of-list-of-primop-int-binary (xss)
  (if (endp xss)
      t
      (and (list-of-primop-int-binary (car xss))
           (list-of-list-of-primop-int-binary (cdr xss)))))

(defun list-of-list-of-primop-int-binary-x (xss)
  (if (endp xss)
      t
      (and (list-of-primop-int-binary-x (car xss))
           (list-of-list-of-primop-int-binary-x (cdr xss)))))

(defun pairwise-curry-binary-fn (funcells argcells)
  (if (endp funcells)
      nil
      (cons (expr-value-primop
             (primop-value-int-binary-x (primop-value-int-binary->op
                                         (expr-value-primop->val (car funcells)))
                                        (car argcells)))
            (pairwise-curry-binary-fn (cdr funcells) (cdr argcells)))))

(defun pairwise-curry-binary-x-fn (funcells argcells)
  (if (endp funcells)
      nil
      (cons (eval-int-binary-primop
             (primop-value-int-binary-x->op
              (expr-value-primop->val (car funcells)))
             (primop-value-int-binary-x->xval
              (expr-value-primop->val (car funcells)))
             (car argcells))
            (pairwise-curry-binary-x-fn (cdr funcells) (cdr argcells)))))

;; (defthm not-reserrp-car-base-values
;;     (implies (and (consp xs)
;;                   (list-of-base-values xs))
;;              (not (reserrp (car xs)))))

;; (defthm expr-value-wfpn-car-base-values
;;     (implies (and (consp xs)
;;                   (list-of-base-values xs))
;;              (expr-value-wfp (car xs)))
;;   :hints (("Goal"
;;            :in-theory (enable expr-value-wfp
;;                               check-dims-of-expr-value)))
;;   )

(local
 (defun eval-app-list-induction (fns args limit)
   (if (zp limit)
       args
       (if (endp fns)
           1
           (eval-app-list-induction (cdr fns) (cdr args) (1- limit))))))

;; (defthm eval-app-list-when-funcells-null
;;     (implies (and (not (consp funcells))
;;                   (not (zp limit)))
;;              (equal (eval-app-list funcells argcells limit)
;;                     nil))
;;   :hints (("Goal"
;;            :expand ((eval-app-list funcells argcells limit)))))

;; (defthm not-reserrp-list-primop
;;     (not (reserrp (list :primop x)))
;;   :hints (("Goal"
;;            :in-theory (enable reserrp))))

;; (defthm not-reserrp-pairwise-curry-binary-fn
;;     (not (reserrp (pairwise-curry-binary-fn xs ys)))
;;   :hints (("Goal"
;;            :in-theory (enable reserrp))))

(defthm primop-value-funp-when-kind-is-int-binary
    (implies (equal (primop-value-kind x) :int-binary)
             (primop-value-funp x))
  :hints (("Goal"
           :in-theory (enable primop-value-funp))))

(defthm primop-value-funp-when-kind-is-int-binary-x
    (implies (equal (primop-value-kind x) :int-binary-x)
             (primop-value-funp x))
  :hints (("Goal"
           :in-theory (enable primop-value-funp))))

(defthm eval-app-list-when-primop-binary-and-bases
     (implies (and (list-of-primop-int-binary funcells)
                   (list-of-base-values argcells)
                   (equal (len funcells) (len argcells))
                   (not (reserrp (eval-app-list funcells argcells limit))))
             (equal (eval-app-list funcells argcells limit)
                    (pairwise-curry-binary-fn funcells argcells)))
  :otf-flg t
  :hints (("Goal"
           ;; :use ((:instance base-values-are-well-formed
           ;;                  (xs ARGCELLS)))
           :in-theory (E/D (eval-app-list
                            eval-app-cell
                            expr-value-primop
                            eval-primop-fun
                            EVAL-PRIMOP-FUN-FO)
                           (base-values-are-well-formed
                            ))
           :expand ((EVAL-APP-CELL (CAR FUNCELLS)
                                   (CAR ARGCELLS)
                                   (+ -1 LIMIT))
                    (EVAL-APP-LIST FUNCELLS ARGCELLS LIMIT))
           :induct (eval-app-list-induction funcells argcells limit))
          )
  )

(defthm dims-of-primop
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  )
             (equal (dims-of-expr-value funval)
                    nil))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value))))

(defthm fun-value-param-dims-primop
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (not (reserrp (fun-value-param-dims funval))))
             (equal (fun-value-param-dims funval)
                    '(nil nil)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable fun-value-param-dims
                              expr-value-first-fun
                              EXPR-VALUE-PRIMOP->VAL
                              TYPE-OF-PRIMOP-VALUE-FUN))))

(defthm check-list-suffix-dims-nil
    (implies (true-listp arg-dims)
             (equal (check-list-suffix arg-dims nil)
                    (mv t arg-dims)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable check-list-suffix))))


(defthm list-prefix-join-nil-dims
    (implies (true-listp arg-dims)
             (equal (list-prefix-join (list nil arg-dims))
                    (mv t arg-dims)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable list-prefix-join))))

(defthm not-reserrp-list-expr-value-fix
    (implies (expr-valuep val)
             (not (reserrp (list val))))
  :hints (("Goal"
           :in-theory (enable reserrp
                              expr-value-fix))))

(defthm lift-expr-value-to-frame-when-scalar
    (implies (and (null frame)
                  (expr-valuep val))
             (equal (lift-expr-value-to-frame val frame pframe)
                    (repeat (nat-list-product pframe)
                            val)))
  :hints (("Goal"
           :in-theory (enable lift-expr-value-to-frame
                              CELLS-AT-DEPTH-IN-EXPR-VALUE
                              repeat-each))))

(mutual-recursion

 (defun get-cells-from-expr-value (val)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-COUNT VAL)))
   (expr-value-case val
                    :vector
                    (get-cells-from-expr-value-list val.elems)
                    :otherwise (list val)))

 (defun get-cells-from-expr-value-list (lst)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-LIST-COUNT lst)))
   (if (endp lst)
       nil
       (append (get-cells-from-expr-value (car lst))
               (get-cells-from-expr-value-list (cdr lst)))))
 )



(mutual-recursion

 (defun get-cells-hint (val depth)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-COUNT VAL)))
   (expr-value-case val
                    :vector
                    (get-cells-hint-list val.elems (1- depth))
                    :otherwise (list depth)))

 (defun get-cells-hint-list (lst depth)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-LIST-COUNT lst)))
   (if (endp lst)
       nil
       (append (get-cells-hint (car lst) depth)
               (get-cells-hint-list (cdr lst) depth))))
 )

(acl2::make-flag flag-get-cells get-cells-hint
                 :flag-mapping ((get-cells-hint      term)
                                (get-cells-hint-list list)))

(defun dims-expr-list-bounded (lst depth)
  (if (endp lst)
      t
      (and (equal depth (len (dims-of-expr-value (car lst))))
           (dims-expr-list-bounded (cdr lst) depth))))

(defun check-dims-of-expr-value-list-all-equal (lst dims)
  (if (endp lst)
      t
      (and (equal dims (check-dims-of-expr-value (car lst)))
           (check-dims-of-expr-value-list-all-equal (cdr lst) dims))))

(defthm propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector
    (implies (and (equal (expr-value-kind val) :vector)
                  (expr-value-wfp val)
                  (not (reserrp (cells-at-depth-in-expr-value val depth)))
                  (equal depth (len (dims-of-expr-value val))))
             (not
              (reserrp
               (cells-at-depth-in-expr-value-list (expr-value-vector->elems val)
                                                  (+ -1 depth)))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable cells-at-depth-in-expr-value
                              DIMS-OF-EXPR-VALUE
                              EXPR-VALUE-WFP
                              CHECK-DIMS-OF-EXPR-VALUE))))

(defthm car-check-dims-of-expr-value-list
  (implies (and (consp vals)
                (not (reserrp (check-dims-of-expr-value-list vals))))
           (equal (car (check-dims-of-expr-value-list vals))
                  (check-dims-of-expr-value (car vals))))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list)))
  )

(defthm cdr-check-dims-of-expr-value-list
  (implies (and (consp vals)
                (not (reserrp (check-dims-of-expr-value-list vals))))
           (equal (cdr (check-dims-of-expr-value-list vals))
                  (check-dims-of-expr-value-list (cdr vals))))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list)))
  )

(defthm propagate-list-repeatp-check-dims-of-expr-value-list
    (implies (and (consp vals)
                  (not (reserrp (check-dims-of-expr-value-list vals)))
                  (list-repeatp (check-dims-of-expr-value-list vals)))
             (list-repeatp (check-dims-of-expr-value-list (cdr vals))))
  :hints (("Goal"
           :use ((:instance list-repeatp-of-cdr
                            (x (check-dims-of-expr-value-list vals))))
           :in-theory (disable list-repeatp-of-cdr)
           )))

(defthm propagate-not-reserrp-check-dims-of-expr-value-list
    (implies (and (consp vals)
                  (not (reserrp (check-dims-of-expr-value-list vals))))
             (not (reserrp (check-dims-of-expr-value-list (cdr vals)))))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list)
           )))

(defthmd car-check-dims-of-expr-value-list-cdr-lemma
    (implies (and (consp lst)
                  (list-repeatp lst))
             (equal (car (cdr lst))
                    (if (consp (cdr lst))
                        (car lst)
                        nil)))
  :hints (("Goal"
           :expand ((list-repeatp lst))))
  )

(defthm car-check-dims-of-expr-value-list-cdr
    (implies (and (consp vals)
                  (not (reserrp (check-dims-of-expr-value-list vals)))
                  (list-repeatp (check-dims-of-expr-value-list vals)))
             (equal (CAR (CHECK-DIMS-OF-EXPR-VALUE-LIST (CDR VALS)))
                    (if (consp (cdr vals))
                        (CHECK-DIMS-OF-EXPR-VALUE (CAR VALS))
                        nil)))
  :hints (("Goal"
           :use ((:instance car-check-dims-of-expr-value-list-cdr-lemma
                            (lst (check-dims-of-expr-value-list vals))))
           )))


(defthmd check-dims-of-expr-value-list-when-vector-elems
    (implies (and (not (reserrp (CHECK-DIMS-OF-EXPR-VALUE-LIST vals)))
                  (list-repeatp (CHECK-DIMS-OF-EXPR-VALUE-LIST vals)))
             (check-dims-of-expr-value-list-all-equal vals (car (CHECK-DIMS-OF-EXPR-VALUE-LIST vals)))))

(defthmd check-dims-of-expr-value-list-all-equal-implies-dims-expr-list-bounded
    (implies (and (not (reserrp (CHECK-DIMS-OF-EXPR-VALUE-LIST lst)))
                  (check-dims-of-expr-value-list-all-equal lst dims))
             (dims-expr-list-bounded lst (len dims)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value
                              check-dims-of-expr-value-list
                              expr-value-wfp)))
  )

(defthm dims-expr-list-bounded-when-vector-elems
    (implies (and (not (reserrp (CHECK-DIMS-OF-EXPR-VALUE-LIST vals)))
                  (list-repeatp (CHECK-DIMS-OF-EXPR-VALUE-LIST vals))
                  (consp vals))
             (dims-expr-list-bounded
              vals
              (len (check-dims-of-expr-value (car vals)))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  check-dims-of-expr-value-list-all-equal-implies-dims-expr-list-bounded
                  (lst vals)
                  (dims (car (CHECK-DIMS-OF-EXPR-VALUE-LIST vals))))
                 (:instance check-dims-of-expr-value-list-when-vector-elems)))))

(defthm len-dims-expr-list-when-vector
    (implies (and (EXPR-VALUE-WFP VAL)
                  (EXPR-VALUEP VAL)
                  (EQUAL (EXPR-VALUE-KIND VAL) :VECTOR)
                  (EQUAL DEPTH (LEN (DIMS-OF-EXPR-VALUE VAL))))
             (and (not (reserrp (check-dims-of-expr-value-list
                                 (EXPR-VALUE-VECTOR->ELEMS VAL))))
                  (consp (check-dims-of-expr-value-list
                          (EXPR-VALUE-VECTOR->ELEMS VAL)))
                  (list-repeatp (check-dims-of-expr-value-list
                                 (EXPR-VALUE-VECTOR->ELEMS VAL)))
                  (equal (len (dims-of-expr-value
                               (car (EXPR-VALUE-VECTOR->ELEMS VAL))))
                         (1- depth))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable expr-value-wfp
                              check-dims-of-expr-value
                              dims-of-expr-value)))
  )

(defthm expr-value-wfp-implies-dims-expr-list-bounded-when-vector
    (implies (and (not (reserrp (check-dims-of-expr-value val)))
                  (equal (expr-value-kind val) :vector)
                  (expr-valuep val)
                  )
             (dims-expr-list-bounded
              (expr-value-vector->elems val)
              (len
               (car (check-dims-of-expr-value-list
                     (expr-value-vector->elems val))))))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance dims-expr-list-bounded-when-vector-elems
                            (vals (EXPR-VALUE-VECTOR->ELEMS val)))
                 (:instance len-dims-expr-list-when-vector
                            (depth (len (dims-of-expr-value val))))
                 (:instance propagate-not-reserrp-check-dims-of-expr-value-list
                            (vals (expr-value-vector->elems val)))
                 (:instance car-check-dims-of-expr-value-list
                            (vals (expr-value-vector->elems val)))
                 )
           :in-theory (e/d (expr-value-wfp)
                           (propagate-not-reserrp-check-dims-of-expr-value-list
                            car-check-dims-of-expr-value-list))
           )))

(defthm-flag-get-cells
    (defthm cells-at-depth-in-expr-value-when-depth-is-val-depth
        (implies (and (not (reserrp (cells-at-depth-in-expr-value val depth)))
                      (integerp depth)
                      (equal depth (len (dims-of-expr-value val)))
                      (expr-value-wfp val)
                      (expr-valuep val)
                      )
                 (equal (CELLS-AT-DEPTH-IN-EXPR-VALUE val depth)
                        (get-cells-from-expr-value val)))
      :flag term)
    (defthm cells-at-depth-in-expr-value-list-to-frame-when-depth=is-val-depth
        (implies (and (not (reserrp (cells-at-depth-in-expr-value-list lst depth)))
                      (integerp depth)
                      (dims-expr-list-bounded lst depth)
                      (expr-value-list-wfp lst)
                      (expr-value-listp lst)
                      )
                  (equal (CELLS-AT-DEPTH-IN-EXPR-VALUE-list lst depth)
                         (get-cells-from-expr-value-list lst)))
      :flag list)
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable CELLS-AT-DEPTH-IN-EXPR-VALUE
                              CELLS-AT-DEPTH-IN-EXPR-VALUE-list
                              dims-of-expr-value
                              EXPR-VALUE-WFP
                              CHECK-DIMS-OF-EXPR-VALUE
                              CHECK-DIMS-OF-EXPR-VALUE-list
                              )))
  )


(defthm nthcdr-len-lst
    (implies (true-listp lst)
             (equal (nthcdr (len lst) lst)
                    nil)))

(defthm true-listp-dims-of-expr-value
    (true-listp (dims-of-expr-value val)))

(defthm repeat-each-1
    (equal (repeat-each 1 lst) (true-list-fix lst))
  :hints (("Goal"
           :in-theory (enable repeat-each)))
  )

(defthm lift-expr-value-to-frame-when-frame-is-pframe-and-frame-of-val
    (implies (and (not (reserrp (lift-expr-value-to-frame val frame pframe)))
                  (equal frame pframe)
                  (equal frame (dims-of-expr-value val))
                  (expr-value-wfp val)
                  (expr-valuep val)
                  )
             (equal (lift-expr-value-to-frame val frame pframe)
                    (get-cells-from-expr-value val)))
  :hints (("Goal"
           :use ((:instance
                  cells-at-depth-in-expr-value-when-depth-is-val-depth
                  (depth (len (dims-of-expr-value val))))
                 )
           :in-theory (enable LIFT-EXPR-VALUE-TO-FRAME)
           )
          ))


(defthm list-of-primop-int-binary-when-repeated
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  )
             (list-of-primop-int-binary (repeat n funval)))
  :hints (("Goal"
           :in-theory (enable repeat)))
  )

(defthm list-of-primop-int-binary-lift-of-int-binary
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (equal fun-frame (dims-of-expr-value funval))
                  )
             (list-of-primop-int-binary
              (lift-expr-value-to-frame funval fun-frame pframe)))
  )

(mutual-recursion

 (defun expr-is-nested-vectors-of-base-values (val)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-COUNT VAL)))
   (expr-value-case val
                    :base      t
                    :vector    (and (consp val.elems)
                                    (expr-is-nested-vectors-of-base-values-list val.elems))
                    :otherwise nil))

 (defun expr-is-nested-vectors-of-base-values-list (lst)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-LIST-COUNT lst)))
   (if (endp lst)
       t
       (and (expr-is-nested-vectors-of-base-values (car lst))
            (expr-is-nested-vectors-of-base-values-list (cdr lst)))))
 )

(mutual-recursion

 (defun expr-is-nested-vectors-of-binary-primops (val)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-COUNT VAL)))
   (expr-value-case val
                    :primop    (or (primop-value-case val.val :int-binary)
                                   (primop-value-case val.val :int-binary-x))
                    :vector    (and (consp val.elems)
                                    (expr-is-nested-vectors-of-binary-primops-list val.elems))
                    :otherwise nil))

 (defun expr-is-nested-vectors-of-binary-primops-list (lst)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-LIST-COUNT lst)))
   (if (endp lst)
       t
       (and (expr-is-nested-vectors-of-binary-primops (car lst))
            (expr-is-nested-vectors-of-binary-primops-list (cdr lst)))))
 )

(mutual-recursion

 (defun expr-is-nested-vectors-of-curried-base-values (val)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-COUNT VAL)))
   (expr-value-case val
                    :primop    (and (primop-value-case val.val :int-binary-x)
                                    (equal (expr-value-kind
                                            (primop-value-int-binary-x->xval
                                             val.val))
                                           :base))
                    :vector    (and (consp val.elems)
                                    (expr-is-nested-vectors-of-curried-base-values-list val.elems))
                    :otherwise nil))

 (defun expr-is-nested-vectors-of-curried-base-values-list (lst)
   (DECLARE (XARGS :MEASURE (EXPR-VALUE-LIST-COUNT lst)))
   (if (endp lst)
       t
       (and (expr-is-nested-vectors-of-curried-base-values (car lst))
            (expr-is-nested-vectors-of-curried-base-values-list (cdr lst)))))
 )

(defthm list-of-base-values-append
    (implies (and (list-of-base-values xs)
                  (list-of-base-values ys))
             (list-of-base-values (append xs ys))))

(defthm propagate-reserrp-to-cells-at-depth-car-list
    (implies (and (consp vals)
                  (reserrp (CELLS-AT-DEPTH-IN-EXPR-VALUE (car VALS)
                                                         DEPTH)))
             (reserrp (CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST VALS
                                                         DEPTH)))
  :hints (("Goal"
           :in-theory (enable CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST)))
  )

(defthm propagate-reserrp-to-cells-at-depth-cdr-list
    (implies (reserrp (CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST (CDR VALS)
                                                         DEPTH))
             (reserrp (CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST VALS
                                                         DEPTH)))
  :hints (("Goal"
           :in-theory (enable CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST)))
  )

(defthm dims-expr-list-bounded-whtn-list-repeat-check-dims
    (implies (and (consp lst)
                  (not (reserrp (check-dims-of-expr-value-list lst)))
                  (expr-value-list-wfp lst)
                  (list-repeatp
                   (check-dims-of-expr-value-list lst)))
             (dims-expr-list-bounded lst
                                     (len (dims-of-expr-value (car lst)))))
  :INSTRUCTIONS
  (:INDUCT :BASH (:CHANGE-GOAL NIL T)
           :BASH (:CASESPLIT (CONSP (CDR LST)))
           (:CHANGE-GOAL NIL T)
           :BASH :PRO (:FORWARDCHAIN 3)
           (:CASESPLIT (EQUAL (DIMS-OF-EXPR-VALUE (CADR LST))
                              (DIMS-OF-EXPR-VALUE (CAR LST))))
           (:= T)
           (:CONTRAPOSE 9)
           (:DEMOTE 7)
           (:DV 1)
           :X
           (:CLAIM (CONSP (CHECK-DIMS-OF-EXPR-VALUE-LIST (CDR LST))))
           :S (:DV 1)
           (:DV 2)
           (:DV 1)
           :X :TOP (:DEMOTE 5)
           (:DV 1)
           (:DV 1)
           (:DV 1)
           :X :UP :UP :S :TOP :PROMOTE (:DV 1)
           (:DV 1)
           (:DV 2)
           (:DV 1)
           :S :TOP (:DEMOTE 10)
           (:DV 1)
           (:DV 1)
           (:DV 1)
           :X :UP :UP :S :TOP :PROMOTE (:DV 1)
           :S :TOP :PRO (:DV 1)
           :X :NX :X :BK (:DV 1)
           (:= T)
           :TOP :S)
  )

(defthm dims-expr-list-bounded-of-child
    (implies (and (EXPR-VALUE-WFP VAL)
                  (EQUAL (EXPR-VALUE-KIND VAL) :VECTOR)
                  (EQUAL DEPTH (LEN (DIMS-OF-EXPR-VALUE VAL)))
                  )
             (DIMS-EXPR-LIST-BOUNDED (EXPR-VALUE-VECTOR->ELEMS VAL)
                                     (+ -1 DEPTH)))
  :hints (("Goal"
           :expand ((EXPR-VALUE-WFP VAL)
                    (expr-value-wfp val)
                    (check-dims-of-expr-value val))
           :use ((:instance dims-expr-list-bounded-whtn-list-repeat-check-dims
                            (lst (expr-value-vector->elems val))))
           :in-theory (e/d (dims-of-expr-value)
                           (dims-expr-list-bounded-whtn-list-repeat-check-dims))
           )))

(defthm propagate-reserrp-from-cells-at-depth-to-cells-at-depth-list
    (implies (and (expr-valuep val)
                  (expr-value-wfp val)
                  (equal (expr-value-kind val) :vector)
                  (not
                   (reserrp
                    (cells-at-depth-in-expr-value val (len (dims-of-expr-value
                                                            val)))))
                  )
             (not (reserrp (get-cells-from-expr-value-list
                            (expr-value-vector->elems val)))))
  :instructions
  (:pro
   (:use (:instance cells-at-depth-in-expr-value-when-depth-is-val-depth
                    (depth (len (dims-of-expr-value val)))))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   (:= t)
   :up
   (:=
    (equal (cells-at-depth-in-expr-value val (len (dims-of-expr-value val)))
           (get-cells-from-expr-value val)))
   :top :pro (:demote 4)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   := :top
   :pro :bash)
  )

(defthm-flag-get-cells
    (defthm list-of-base-values-when-expr-is-nested-vectors-of-base-values
        (implies (and (expr-value-wfp val)
                      (expr-valuep val)
                      (expr-is-nested-vectors-of-base-values val)
                      )
                 (list-of-base-values
                  (get-cells-from-expr-value val)))
      :flag term)
    (defthm list-of-base-values-when-expr-is-nested-vectors-of-base-values-list
        (implies (and (consp lst)
                      (expr-value-list-wfp lst)
                      (expr-value-listp lst)
                      (expr-is-nested-vectors-of-base-values-list lst)
                      )
                 (list-of-base-values
                  (get-cells-from-expr-value-list lst)))
      :flag list)
  :otf-flg t
  )

(defthm list-of-primop-int-binary-x-append
    (implies (and (list-of-primop-int-binary-x xs)
                  (list-of-primop-int-binary-x ys))
             (list-of-primop-int-binary-x (append xs ys))))

(defthm-flag-get-cells
    (defthm list-of-primop-int-binary-x-when-expr-is-nested-vectors-of-curried-base-values
        (implies (and (expr-value-wfp val)
                      (expr-valuep val)
                      (expr-is-nested-vectors-of-curried-base-values val)
                      )
                 (list-of-primop-int-binary-x
                  (get-cells-from-expr-value val)))
      :flag term)
    (defthm list-of-base-values-when-expr-is-nested-vectors-of-curried-base-values-list
        (implies (and (expr-value-list-wfp lst)
                      (expr-value-listp lst)
                      (expr-is-nested-vectors-of-curried-base-values-list lst)
                      )
                 (list-of-primop-int-binary-x
                  (get-cells-from-expr-value-list lst)))
      :flag list)
  :otf-flg t
  )

(defthm-flag-get-cells
    (defthmd get-cells-from-expr-value-is-list-of-expr-values
        (implies (expr-valuep val)
                 (expr-value-listp (get-cells-from-expr-value val)))
      :flag term)
    (defthmd get-cells-from-expr-value-is-list-of-expr-values-list
        (implies (expr-value-listp lst)
                 (expr-value-listp (get-cells-from-expr-value-list lst)))
      :flag list)
  :otf-flg t
  )

(defthm not-reserrp-get-cells-from-valid-expr-value
    (implies (expr-valuep val)
             (not (reserrp (get-cells-from-expr-value val))))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance get-cells-from-expr-value-is-list-of-expr-values))
           ))
  )

(defthm reserrp-append
    (implies (and (expr-value-listp xs)
                  (expr-value-listp ys)
                  (not (reserrp xs))
                  (not (reserrp ys)))
             (not (reserrp (append xs ys))))
  :hints (("Goal"
           :in-theory (enable reserrp))))


(defthm depth-reduces-for-nested-expressions
    (implies (and (expr-value-listp lst)
                  (expr-value-list-wfp lst)
                  (<= DEPTH
                      (LEN (DIMS-OF-EXPR-VALUE (CAR LST))))
                  (DIMS-EXPR-LIST-BOUNDED LST DEPTH)
                  (consp lst)
                  (consp (cdr lst))
                  )
             (equal (len (DIMS-OF-EXPR-VALUE (CADR LST)))
                    (len (DIMS-OF-EXPR-VALUE (CAR LST)))))
  :hints (("Goal"
           :do-not-induct t))
  )

(local
 (defthm subgoal-1/3-propagate-reserrp-cells-at-depth-to-dims-of-expr-value
     (implies (and (not (equal flag 'term))
                   (consp lst)
                   (if t
                       (implies
                        (and (expr-valuep (car lst))
                             (expr-value-wfp (car lst))
                             (or (expr-is-nested-vectors-of-base-values (car lst))
                                 (expr-is-nested-vectors-of-curried-base-values (car lst)))
                             (equal depth
                                    (len (dims-of-expr-value (car lst)))))
                        (not (reserrp (cells-at-depth-in-expr-value (car lst)
                                                                    depth))))
                       (implies
                        (and (expr-value-listp nil)
                             (expr-value-list-wfp nil)
                             (or (expr-is-nested-vectors-of-base-values-list nil)
                                 (expr-is-nested-vectors-of-curried-base-values-list nil))
                             (equal depth (len (dims-of-expr-value nil)))
                             (dims-expr-list-bounded nil depth)
                             (expr-value-listp nil))
                        (not (reserrp (cells-at-depth-in-expr-value-list nil depth)))))
                   (if nil
                       (implies (and (expr-valuep nil)
                                     (expr-value-wfp nil)
                                     (or (expr-is-nested-vectors-of-base-values nil)
                                         (expr-is-nested-vectors-of-curried-base-values nil))
                                     (equal depth (len (dims-of-expr-value nil))))
                                (not (reserrp (cells-at-depth-in-expr-value nil depth))))
                       (implies
                        (and (expr-value-listp (cdr lst))
                             (expr-value-list-wfp (cdr lst))
                             (or (expr-is-nested-vectors-of-base-values-list (cdr lst))
                                 (expr-is-nested-vectors-of-curried-base-values-list (cdr lst)))
                             (equal depth
                                    (len (dims-of-expr-value (cadr lst))))
                             (dims-expr-list-bounded (cdr lst) depth)
                             (expr-value-listp (cdr lst)))
                        (not (reserrp (cells-at-depth-in-expr-value-list (cdr lst)
                                                                         depth))))))
              (if (equal flag 'term)
                  (implies (and (expr-valuep val)
                                (expr-value-wfp val)
                                (or (expr-is-nested-vectors-of-base-values val)
                                    (expr-is-nested-vectors-of-curried-base-values val))
                                (equal depth (len (dims-of-expr-value val))))
                           (not (reserrp (cells-at-depth-in-expr-value val depth))))
                  (implies
                   (and (expr-value-listp lst)
                        (expr-value-list-wfp lst)
                        (or (expr-is-nested-vectors-of-base-values-list lst)
                            (expr-is-nested-vectors-of-curried-base-values-list lst))
                        (equal depth
                               (len (dims-of-expr-value (car lst))))
                        (dims-expr-list-bounded lst depth)
                        (expr-value-listp lst))
                   (not (reserrp (cells-at-depth-in-expr-value-list lst depth))))))
   :instructions
   (:pro
    (:= (implies
         (and (expr-value-listp lst)
              (expr-value-list-wfp lst)
              (or (expr-is-nested-vectors-of-base-values-list lst)
                  (expr-is-nested-vectors-of-curried-base-values-list lst))
              (equal depth
                     (len (dims-of-expr-value (car lst))))
              (dims-expr-list-bounded lst depth)
              (expr-value-listp lst))
         (not (reserrp (cells-at-depth-in-expr-value-list lst depth)))))
    :pro (:casesplit (consp (cdr lst)))
    (:change-goal nil t)
    (:demote 3)
    (:dv 1)
    (:=
     (implies
      (and (expr-valuep (car lst))
           (expr-value-wfp (car lst))
           (or (expr-is-nested-vectors-of-base-values (car lst))
               (expr-is-nested-vectors-of-curried-base-values (car lst)))
           (equal depth
                  (len (dims-of-expr-value (car lst)))))
      (not (reserrp (cells-at-depth-in-expr-value (car lst)
                                                  depth)))))
    (:dv 1)
    (:= t)
    :up :s :top :pro (:dv 1)
    (:dv 1)
    :x (:dv 1)
    (:dv 1)
    :x :up :up
    (:= (append (cells-at-depth-in-expr-value (car lst)
                                              depth)
                (cells-at-depth-in-expr-value-list nil depth)))
    (:dv 2)
    :x :up
    (:= (cells-at-depth-in-expr-value (car lst)
                                      depth))
    :top :s (:demote 4)
    (:dv 1)
    (:=
     (implies
      (and (expr-value-listp (cdr lst))
           (expr-value-list-wfp (cdr lst))
           (or (expr-is-nested-vectors-of-base-values-list (cdr lst))
               (expr-is-nested-vectors-of-curried-base-values-list (cdr lst)))
           (equal depth
                  (len (dims-of-expr-value (cadr lst))))
           (dims-expr-list-bounded (cdr lst) depth)
           (expr-value-listp (cdr lst)))
      (not (reserrp (cells-at-depth-in-expr-value-list (cdr lst)
                                                       depth)))))
    (:dv 1)
    (:= t)
    :up :s :top :pro (:demote 3)
    (:dv 1)
    (:=
     (implies
      (and (expr-valuep (car lst))
           (expr-value-wfp (car lst))
           (or (expr-is-nested-vectors-of-base-values (car lst))
               (expr-is-nested-vectors-of-curried-base-values (car lst)))
           (equal depth
                  (len (dims-of-expr-value (car lst)))))
      (not (reserrp (cells-at-depth-in-expr-value (car lst)
                                                  depth)))))
    (:dv 1)
    (:= t)
    :up :s :top :pro (:dv 1)
    (:dv 1)
    :x :up (:rewrite reserrp-append)
    (:= t)
    (:= t)))
 )

(DEFTHM-flag-get-cells
    (defthm propagate-reserrp-cells-at-depth-to-dims-of-expr-value
        (implies (and (expr-valuep val)
                      (expr-value-wfp val)
                      (or (expr-is-nested-vectors-of-base-values val)
                          (expr-is-nested-vectors-of-curried-base-values val))
                      ;; (natp depth)
                      (equal depth (len (dims-of-expr-value val)))
                      ;; (not (reserrp (dims-of-expr-value val)))
                      )
                 (not (reserrp (cells-at-depth-in-expr-value val depth))))
      :flag term)
    (defthm propagate-reserrp-cells-at-depth-to-dims-of-expr-value-list
        (implies (and (expr-value-listp lst)
                      (expr-value-list-wfp lst)
                      (or (expr-is-nested-vectors-of-base-values-list lst)
                          (expr-is-nested-vectors-of-curried-base-values-list lst))
                      (equal depth (len (dims-of-expr-value (car lst))))
                      (dims-expr-list-bounded lst depth)
                      (expr-value-listp lst)
                      )
                 (not (reserrp (cells-at-depth-in-expr-value-list lst depth))))
      :flag list)
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (CELLS-AT-DEPTH-IN-EXPR-VALUE
                            CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST
                            reserrp
                            expr-valuep)
                           (CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST-TO-FRAME-WHEN-DEPTH=IS-VAL-DEPTH
                            CELLS-AT-DEPTH-IN-EXPR-VALUE-WHEN-DEPTH-IS-VAL-DEPTH)
                           ))
          ("Subgoal *1/3"
           :by (:instance subgoal-1/3-propagate-reserrp-cells-at-depth-to-dims-of-expr-value))
          )
  )

(defthm dims-of-base-or-binary-x-value
    (implies (and (expr-valuep val)
                  (or (equal (expr-value-kind val) :base)
                      (equal (expr-value-kind val) :int-binary-x))
                  )
             (equal (dims-of-expr-value val)
                    nil))
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value
                              check-dims-of-expr-value)))
  )

(defthm depth-reduces-for-nested-expressions
    (implies (and (expr-value-listp lst)
                  (expr-value-list-wfp lst)
                  (<= DEPTH
                      (LEN (DIMS-OF-EXPR-VALUE (CAR LST))))
                  (DIMS-EXPR-LIST-BOUNDED LST DEPTH)
                  (consp lst)
                  (consp (cdr lst))
                  )
             (equal (len (DIMS-OF-EXPR-VALUE (CADR LST)))
                    (len (DIMS-OF-EXPR-VALUE (CAR LST)))))
  :hints (("Goal"
           :do-not-induct t))
  )

(defthm check-dims-of-expr-value-list-all-equal-when-vector-of-wfp-lemma
    (implies (and (expr-value-wfp val)
                  (expr-is-nested-vectors-of-base-values val)
                  (equal (expr-value-kind val) :vector))
             (and (not (reserrp (check-dims-of-expr-value-list (expr-value-vector->elems val))))
                  (consp (expr-value-vector->elems val))
                  (list-repeatp
                   (check-dims-of-expr-value-list (expr-value-vector->elems val)))
                  (not
                   (reserrp
                    (cons
                     (len (expr-value-vector->elems val))
                     (check-dims-of-expr-value (car (expr-value-vector->elems val))))))))
  :instructions (:pro (:demote 1)
                      (:dv 1)
                      :x :top :pro (:dv 1)
                      :top
                      (:in-theory (enable check-dims-of-expr-value))
                      (:dv 1)
                      (:= t)
                      :nx (:= t)
                      :nx (:= t)
                      :nx (:= t)))

(defthm not-reserrp-check-dims-of-expr-value-list
    (implies (expr-value-list-wfp lst)
             (not (reserrp (check-dims-of-expr-value-list lst))))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list
                              expr-value-wfp
                              expr-value-list-wfp
                              reserrp))))

(defthm car-check-dims-of-expr-value-list-better
    (implies (and (expr-value-list-wfp lst)
                  (consp lst))
             (equal (car (check-dims-of-expr-value-list lst))
                    (check-dims-of-expr-value (car lst))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EXPR-VALUE-LIST-WFP LST)
                    (EXPR-VALUE-WFP (car LST))
                    (CHECK-DIMS-OF-EXPR-VALUE-LIST LST))
           :in-theory (enable check-dims-of-expr-value-list
                              expr-value-wfp
                              expr-value-list-wfp))))

(defthm check-dims-of-epr-value-list-all-equal-for-special-lists
    (implies (and (consp lst)
                  (expr-value-list-wfp lst)
                  (list-repeatp
                   (check-dims-of-expr-value-list lst))
                  )
             (check-dims-of-expr-value-list-all-equal
              lst
              (car (check-dims-of-expr-value-list lst))))
  :hints (("Goal"
           :in-theory (enable list-repeatp
                              expr-value-list-wfp
                              expr-value-wfp
                              check-dims-of-expr-value-list))
          ("Subgoal *1/6"
           :expand ((LIST-REPEATP (CHECK-DIMS-OF-EXPR-VALUE-LIST LST)))))
  )


(defthm check-dims-of-expr-value-list-all-equal-when-vector-of-wfp
    (implies (and (expr-value-wfp val)
                  (expr-is-nested-vectors-of-base-values val)
                  (equal (expr-value-kind val) :vector)
                  )
             (check-dims-of-expr-value-list-all-equal
              (expr-value-vector->elems val)
              (car (check-dims-of-expr-value-list (expr-value-vector->elems val)))))
  :hints (("Goal"
           :use ((:instance
                  check-dims-of-epr-value-list-all-equal-for-special-lists
                  (lst (expr-value-vector->elems val))))
           :in-theory (disable check-dims-of-epr-value-list-all-equal-for-special-lists)
           ))
  )

(defthm first-two-elements-of-dime-list-all-equal-have-same-dims
    (implies (and (consp lst)
                  (consp (cdr lst))
                  (expr-value-list-wfp lst)
                  (check-dims-of-expr-value-list-all-equal lst dims))
             (equal (dims-of-expr-value (cadr lst))
                    (dims-of-expr-value (car lst))))
  :hints (("Goal"
           :expand ((check-dims-of-expr-value-list-all-equal lst dims)
                    ;;(check-dims-of-expr-value-list-all-equal (cdr lst) dims)
                    )
           :in-theory (enable dims-of-expr-value
                              expr-value-wfp))))

(defthm len-pairwise-curry-binary-fn
    (equal (len (pairwise-curry-binary-fn funcells argcells))
           (len funcells)))

(defthm expr-value-list-wfp-of-pairwise-curry-binary-fn
    (implies (and (list-of-base-values argcells)
                  (list-of-primop-int-binary funcells)
                  )
             (expr-value-list-wfp
              (pairwise-curry-binary-fn funcells argcells)))
  :hints (("Goal"
           :in-theory (enable expr-value-wfp
                              CHECK-DIMS-OF-EXPR-VALUE
                              ))
          )
)

(defthm dims-of-expr-value-curry-primop
    (implies (and (expr-valuep argcell)
                  (expr-value-case argcell :base)
                  (expr-valuep funcell)
                  (expr-value-case funarg :primop)
                  (primop-value-case (expr-value-primop->val funcell)
                                     :int-binary)
                  )
             (equal (dims-of-expr-value
                     (expr-value-primop
                      (primop-value-int-binary-x
                       (primop-value-int-binary->op (expr-value-primop->val funcell))
                       argcell)))
                    nil))
  :hints (("Goal"
           :in-theory (enable expr-value-wfp
                              dims-of-expr-value
                              dims-of-expr-value-list
                              CHECK-DIMS-OF-EXPR-VALUE
                              check-dims-of-primop-value
                              )))
  )

(defthm cons-repeat-nil-len
    (implies (natp n)
             (equal (cons nil (repeat n nil))
                    (repeat (1+ n) nil)))
  :hints (("Goal"
           :do-not-induct t
           :expand (repeat (1+ n) nil)))
  )

(defthm list-repeatp-dims-of-expr-value-pairwise-curry-lemma
    (implies (and (list-of-base-values argcells)
                  (list-of-primop-int-binary funcells)
                  (equal (len argcells) (len funcells))
                  )
             (equal (dims-of-expr-value-list
                     (pairwise-curry-binary-fn funcells argcells))
                    (repeat (len funcells) nil)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable expr-value-wfp
                              dims-of-expr-value
                              dims-of-expr-value-list
                              CHECK-DIMS-OF-EXPR-VALUE
                              check-dims-of-primop-value
                              ))
          )
)

(defthm list-repeatp-dims-of-expr-value-pairwise-curry
    (implies (and (list-of-base-values argcells)
                  (list-of-primop-int-binary funcells)
                  (equal (len argcells) (len funcells))
                  )
             (list-repeatp
              (dims-of-expr-value-list
               (pairwise-curry-binary-fn funcells argcells))))
  :hints (("Goal"
           :in-theory (enable expr-value-wfp
                              dims-of-expr-value
                              dims-of-expr-value-list
                              CHECK-DIMS-OF-EXPR-VALUE
                              check-dims-of-primop-value
                              ))
          )
)

(defthm-flag-get-cells
    (defthm expr-has-nonzero-dims-when-nested-array
        (implies (expr-is-nested-vectors-of-base-values val)
                 (not (member-equal 0 (dims-of-expr-value val))))
      :flag term)
     (defthm as-nonzero-dims-when-nested-array-list
        (implies (expr-is-nested-vectors-of-base-values-list lst)
                 (not (member-equal 0 (dims-of-expr-value (car lst)))))
      :flag list)
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value
                              CHECK-DIMS-OF-EXPR-VALUE
                              CHECK-DIMS-OF-EXPR-VALUE-list
                              )))
  )

(defthm-flag-get-cells
    (defthm expr-has-nonzero-dims-when-nested-array-of-primop
        (implies (expr-is-nested-vectors-of-curried-base-values val)
                 (not (member-equal 0 (dims-of-expr-value val))))
      :flag term)
     (defthm as-nonzero-dims-when-nested-array-of-primop-list
        (implies (expr-is-nested-vectors-of-curried-base-values-list lst)
                 (not (member-equal 0 (dims-of-expr-value (car lst)))))
      :flag list)
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value
                              CHECK-DIMS-OF-EXPR-VALUE
                              CHECK-DIMS-OF-EXPR-VALUE-list
                              CHECK-DIMS-OF-PRIMOP-VALUE
                              )))
  )

(defthm member-equal-of-list-prefix-join
    (implies (and (not (member-equal x xs))
                  (not (member-equal x ys)))
             (not (member-equal x (cadr (list-prefix-join (list xs ys))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable list-prefix-join)))
  )

(defthm member-equal-of-check-list-suffix
    (implies (not (member-equal x xs))
             (not (member-equal x (cadr (check-list-suffix xs suffix)))))
  :hints (("Goal"
           :in-theory (enable check-list-suffix)))
  )

(defthm mv-nth-1
    (equal (mv-nth 1 xs)
           (cadr xs))
  :hints (("Goal"
           :expand ((mv-nth 1 xs)
                    (MV-NTH 0 (CDR XS))))))

(defthm propagate-reserrp-from-eval-app-to-eval-app-list
    (implies (and (not (reserrp (eval-app funval argvals limit)))
                  (or (expr-is-nested-vectors-of-base-values funval)
                      (expr-is-nested-vectors-of-curried-base-values funval))
                  (equal param-dims (fun-value-param-dims funval))
                  (consp argvals)
                  (equal argval (car argvals))
                  (expr-is-nested-vectors-of-base-values argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame (cadr (check-list-suffix arg-dims (car
                                                                      param-dims))))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal pframe (cadr (list-prefix-join (list fun-frame
                                                              arg-frame))))
                  (equal fun-cells (lift-expr-value-to-frame funval fun-frame pframe))
                  (equal arg-cells (lift-expr-value-to-frame argval arg-frame pframe))
                  )
             (not (reserrp (eval-app-list fun-cells arg-cells (1- limit)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance member-equal-of-list-prefix-join
                            (x 0)
                            (xs (DIMS-OF-EXPR-VALUE FUNVAL))
                            (ys (cadr (CHECK-LIST-SUFFIX (DIMS-OF-EXPR-VALUE argval)
                                                         (CAR
                                                          (FUN-VALUE-PARAM-DIMS
                                                           FUNVAL))))))
                 (:instance member-equal-of-check-list-suffix
                            (x 0)
                            (xs (DIMS-OF-EXPR-VALUE argval))
                            (suffix (CAR (FUN-VALUE-PARAM-DIMS FUNVAL))))
                 )
           :expand ((EVAL-APP FUNVAL ARGVALS LIMIT))
           :in-theory (disable member-equal-of-list-prefix-join
                               member-equal-of-check-list-suffix))))


(defthm list-of-primop-int-binary-x-pairwise-curry-binary-fn
    (implies (and (list-of-primop-int-binary funcells)
                  (list-of-base-values argcells))
             (list-of-primop-int-binary-x
              (pairwise-curry-binary-fn funcells argcells))))

(defthm expr-value-listp-pairwise-curry-binary-fn
    (implies (and (list-of-primop-int-binary funcells)
                  (list-of-base-values argcells))
             (expr-value-listp
              (pairwise-curry-binary-fn funcells argcells))))

(defthm eval-app-list-when-primop-binary-x-and-bases
    (implies (and (list-of-primop-int-binary-x funcells)
                  (list-of-base-values argcells)
                  (equal (len funcells) (len argcells))
                  (not (reserrp (eval-app-list funcells argcells limit))))
             (equal (eval-app-list funcells argcells limit)
                    (pairwise-curry-binary-x-fn funcells argcells)))
  :instructions
  ((:in-theory (enable eval-app-list eval-app-cell
                       expr-value-primop eval-primop-fun
                       eval-primop-fun-fo primop-value-fun-fo-p
                       prim-int-add prim-int-sub
                       prim-int-mul prim-int-div prim-int-expt
                       prim-int-mod prim-int-max prim-int-min
                       prim-int-bit-and prim-int-bit-or
                       prim-int-bit-xor prim-int-shl
                       prim-int-shr check-expr-value-int))
   (:induct (eval-app-list-induction funcells argcells limit))
   (:change-goal nil t)
   :bash :bash :pro (:forwardchain 3)
   (:demote 6)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up :s :top :pro (:dv 1)
   :x :nx :x-dumb
   (:=
    (cons
     (eval-int-binary-primop
      (primop-value-int-binary-x->op (expr-value-primop->val (car funcells)))
      (primop-value-int-binary-x->xval
       (expr-value-primop->val (car funcells)))
      (car argcells))
     (pairwise-curry-binary-x-fn (cdr funcells)
                                 (cdr argcells))))
   :up
   (:=
    (equal
     (eval-app-cell (car funcells)
                    (car argcells)
                    (+ -1 limit))
     (eval-int-binary-primop
      (primop-value-int-binary-x->op (expr-value-primop->val (car funcells)))
      (primop-value-int-binary-x->xval
       (expr-value-primop->val (car funcells)))
      (car argcells))))
   (:demote 9)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up :s :top
   (:claim (equal (expr-value-kind (car funcells))
                  :primop))
   (:dv 1)
   :s :top :pro (:dv 1)
   :x :top (:demote 14)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up :s
   (:claim (equal (primop-value-kind (expr-value-primop->val (car funcells)))
                  :int-binary-x))
   :s :top :pro (:dv 1)
   :x
   :top :bash)
  )

(defthm undo-expr-value-with-nonempty-dims-1
    (implies (and (expr-value-listp cells)
                  (expr-value-list-wfp cells)
                  (equal (len cells)
                         (nat-list-product frame))
                  (equal frame nil)
                  )
             (equal (lift-expr-value-to-frame
                     (expr-value-with-nonempty-dims frame cells)
                     frame
                     pframe)
                    (repeat (nat-list-product pframe) (car cells))))
  :hints (("Goal"
           :in-theory (enable EXPR-VALUE-WITH-NONEMPTY-DIMS)))
  )

(defun all-lists-of-len-n (lists n)
  (if (endp lists)
      t
      (and (equal (len (car lists)) n)
           (all-lists-of-len-n (cdr lists) n))))

(defun appendall (lists)
  (if (endp lists)
      nil
      (append (car lists)
              (appendall (cdr lists)))))

(defun EXPR-VALUE-LIST-list-COUNT (lst)
  (if (endp lst)
      1
      (+ (expr-value-list-count (car lst))
         (expr-value-list-list-count (cdr lst)))))

(defthm expr-value-count-decreases-when-list
    (IMPLIES (CONSP LST)
             (< (EXPR-VALUE-COUNT (CAR LST))
                (EXPR-VALUE-LIST-COUNT LST)))
  :hints (("Goal"
           :in-theory (enable EXPR-VALUE-LIST-COUNT))))

(mutual-recursion

 (defun undo-expr-value-hint (cells frame)
   (DECLARE (XARGS :MEASURE (two-nats-measure (acl2-count frame)
                                              (expr-value-list-count cells))))
   (if (endp frame)
       cells
       (undo-expr-value-hint-list
        (list-split (expr-value-list-fix cells)
                    (/ (len cells) (car frame)))
        (cdr frame))))

 (defun undo-expr-value-hint-list (cellss frame)
   (DECLARE (XARGS :MEASURE (two-nats-measure (acl2-count frame)
                                              (EXPR-VALUE-LIST-list-COUNT cellss))))
   (if (endp cellss)
       nil
       (append (undo-expr-value-hint (car cellss) frame)
               (undo-expr-value-hint-list (cdr cellss) frame))))
 )

(acl2::make-flag undo-expr-value-hint
                 :flag-mapping ((undo-expr-value-hint      term)
                                (undo-expr-value-hint-list list)))

(defthm nat-list-prouct-of-nil
    (implies (not (consp frame))
             (equal (nat-list-product frame) 1))
  :hints (("Goal"
           :expand ((nat-list-product frame))))
  )

(defthm expr-value-fix-caar-expr-value-listp
    (implies (and (expr-value-listp cells)
                  (consp cells))
             (equal (expr-value-fix (car cells))
                    (car cells))))

(defthm expr-value-fix-caar-expr-value-listp-actual-goal
    (implies (and (expr-value-listp cells)
                  (not (equal (len cells) 0)))
             (equal (expr-value-fix (car cells))
                    (car cells)))
  :hints (("Goal"
           :use ((:instance expr-value-fix-caar-expr-value-listp))))
  )

(defthmd len-list-1-of-true-listp
    (implies (and (true-listp xs)
                  (equal (len xs) 1))
             (and (consp xs)
                  (not (consp (cdr xs))))))

(defthm list-car-of-len-1
    (implies (and (true-listp xs)
                  (equal (len xs) 1))
             (equal (list (car xs)) xs))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance len-list-1-of-true-listp))))
  )

(defthm len-cells-not-zero-when-consp
    (implies (consp cells)
             (not (equal (len cells) 0))))

(defthmd len-nthcdr
    (implies (and (natp n)
                  (<= n (len cells)))
             (equal (len (nthcdr n cells))
                    (- (len cells) n))))

(defthm len-nthcdr-specialized
    (implies (and (natp n)
                  (consp cells)
                  (equal (mod (len cells) n) 0))
             (equal (len (nthcdr n cells))
                    (- (len cells) n)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance len-nthcdr))))
  )

(defthm expr-value-list-listp-list-split
    (implies (and (expr-value-listp cells)
                  (posp n)
                  (equal (mod (len cells) n) 0))
             (expr-value-list-listp (list-split cells n)))
  :hints (("Goal"
           :induct (list-split cells n)
           :in-theory (enable list-split
                              expr-value-list-listp)))

  )

(defthm integer-divide-natlist-product-by-car
    (implies (and (nat-listp xs)
                  (consp xs))
             (integerp (* (/ (car xs)) (nat-list-product xs))))
  :hints (("Goal"
           :cases ((equal (car xs) 0))
           :in-theory (enable nat-list-product))))

(defthm integer-divide-natlist-product-by-car-as-mod
    (implies (and (nat-listp xs)
                  (consp xs))
             (equal (mod (nat-list-product xs)
                         (* (/ (car xs)) (nat-list-product xs)))
                    0))
  :hints (("Goal"
           :in-theory (enable nat-list-product))))


(defthm integer-divide-natlist-product-by-cdr
    (implies (and (nat-listp xs)
                  (consp xs))
             (integerp (* (/ (nat-list-product (cdr xs))) (nat-list-product xs))))
  :hints (("Goal"
           :cases ((equal (car xs) 0))
           :in-theory (enable nat-list-product))))

(defthm integer-divide-natlist-product-by-cdr-as-mod
    (implies (and (nat-listp xs)
                  (consp xs))
             (equal (mod (nat-list-product xs)
                         (* (/ (nat-list-product (cdr xs))) (nat-list-product xs)))
                    0))
  :hints (("Goal"
           :in-theory (enable nat-list-product))))

(defun pos-listp (xs)
  (if (endp xs)
      (eq xs nil)
      (and (posp (car xs))
           (pos-listp (cdr xs)))))

(defthm all-lists-of-len-n-list-split
    (implies (posp n)
             (all-lists-of-len-n (list-split cells n) n))
  :hints (("Goal"
           :in-theory (enable list-split)))
  )

(defthm nat-list-product-cdr
    (implies (and (pos-listp frame)
                  (consp frame)
                  (equal n (nat-list-product frame)))
             (equal (* (/ (car frame)) n)
                    (nat-list-product (cdr frame))))
  :hints (("Goal"
           :in-theory (enable nat-list-product)))
  )

(defthm posp-nat-list-product
    (implies (pos-listp frame)
             (< 0 (nat-list-product frame)))
  :hints (("Goal"
           :in-theory (enable nat-list-product))))

(defthm append-take-nthcdr
    (implies (and (true-listp cells)
                  (natp n)
                  (<= n (len cells)))
             (equal (append (take n cells) (nthcdr n cells))
                    cells)))

(defthm smaller-when-integer-quotient
    (implies (and (posp m)
                  (posp n)
                  (integerp (* (/ n) m)))
             (<= n  m))
  )

(defthm appendall-list-split
    (implies (and (true-listp cells)
                  (posp n)
                  (integerp (* (/ n) (len cells))))
             (equal (appendall (list-split cells n))
                    cells))
  :hints (("Goal"
           :in-theory (enable list-split)
           :induct (list-split cells n))
          ("Subgoal *1/2"
           :use ((:instance append-take-nthcdr)
                 (:instance smaller-when-integer-quotient
                            (n n)
                            (m (len cells))))
           :in-theory (e/d (list-split)
                           (append-take-nthcdr
                            smaller-when-integer-quotient)))
          )
  )


(defthm pos-listp->nat-listp
    (implies (pos-listp frame)
             (nat-listp frame)))

(defthm pos-listp->true-listp
    (implies (pos-listp frame)
             (true-listp frame)))

(defthm expr-value-list-listp-list-split-specialized
    (implies (and (expr-value-listp cells)
                  (consp frame)
                  (acl2-numberp (car frame))
                  (INTEGERP (CAR FRAME))
                  (< 0 (car frame))
                  (pos-listp (cdr frame))
                  (equal (len cells)
                         (nat-list-product frame)))
             (EXPR-VALUE-LIST-LISTP
              (LIST-SPLIT CELLS (NAT-LIST-PRODUCT (CDR FRAME)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance expr-value-list-listp-list-split
                            (n (NAT-LIST-PRODUCT (CDR FRAME))))
                 (:instance integer-divide-natlist-product-by-car-as-mod
                            (xs frame))
                 )
           :in-theory (disable expr-value-list-listp-list-split
                               integer-divide-natlist-product-by-car-as-mod)))

  )

(defthm-flag-undo-expr-value-hint
    (defthm undo-expr-value-with-nonempty-dims-2-lemma
        (implies (and (expr-value-listp cells)
                      (expr-value-list-wfp cells)
                      (pos-listp frame)
                      (equal (len cells)
                             (nat-list-product frame))
                      (not (reserrp
                            (cells-at-depth-in-expr-value
                             (expr-value-with-nonempty-dims frame cells)
                             (len frame))))
                      )
                 (equal (cells-at-depth-in-expr-value
                         (expr-value-with-nonempty-dims frame cells)
                         (len frame))
                        cells))
      :flag term
      )
    (defthm undo-expr-value-list-with-nonempty-dims-2-lemma
        (implies (and (expr-value-list-listp cellss)
                      (expr-value-list-list-wfp cellss)
                      (pos-listp frame)
                      (all-lists-of-len-n cellss (nat-list-product frame))
                      (not (reserrp
                            (cells-at-depth-in-expr-value-list
                             (expr-value-list-with-nonempty-dims frame cellss)
                             (len frame))))
                      )
                 (equal (cells-at-depth-in-expr-value-list
                         (expr-value-list-with-nonempty-dims frame cellss)
                         (len frame))
                        (appendall cellss)))
      :flag list
      )
  :hints (("Goal"
           :in-theory (enable cells-at-depth-in-expr-value
                              cells-at-depth-in-expr-value-list
                              EXPR-VALUE-WITH-NONEMPTY-DIMS
                              EXPR-VALUE-list-WITH-NONEMPTY-DIMS))
          ("Subgoal *1/1"
           :use ((:instance posp-nat-list-product
                            (frame (cdr frame)))
                 (:instance appendall-list-split
                            (n (NAT-LIST-PRODUCT (CDR FRAME))))
                 (:instance integer-divide-natlist-product-by-cdr
                            (xs frame))
                 )
           :in-theory (e/d (cells-at-depth-in-expr-value
                            cells-at-depth-in-expr-value-list
                            EXPR-VALUE-WITH-NONEMPTY-DIMS
                            EXPR-VALUE-list-WITH-NONEMPTY-DIMS)
                           (posp-nat-list-product
                            appendall-list-split
                            integer-divide-natlist-product-by-cdr)))))

(defthm undo-expr-value-with-nonempty-dims-2
    (implies (and (expr-value-listp cells)
                  (expr-value-list-wfp cells)
                  (pos-listp frame)
                  (equal (len cells)
                         (nat-list-product frame))
                  (equal frame pframe)
                  (not (reserrp
                        (cells-at-depth-in-expr-value
                         (expr-value-with-nonempty-dims frame cells)
                         (len frame))))
                  )
             (equal (lift-expr-value-to-frame
                     (expr-value-with-nonempty-dims frame cells)
                     frame
                     pframe)
                    cells))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance undo-expr-value-with-nonempty-dims-2-lemma))
           :in-theory (e/d (lift-expr-value-to-frame)
                           (undo-expr-value-with-nonempty-dims-2-lemma))))
  )

(defthm undo-expr-value-with-nonempty-dims-3
    (implies (and (expr-value-listp cells)
                  (expr-value-list-wfp cells)
                  (pos-listp frame)
                  (equal (len cells)
                         (nat-list-product frame))
                  (prefixp frame pframe)
                  (not (reserrp
                        (cells-at-depth-in-expr-value
                         (expr-value-with-nonempty-dims frame cells)
                         (len frame))))
                  )
             (equal (lift-expr-value-to-frame
                     (expr-value-with-nonempty-dims frame cells)
                     frame
                     pframe)
                    (repeat-each (nat-list-product
                                  (nthcdr (len frame) pframe))
                                 cells)
                    ))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance undo-expr-value-with-nonempty-dims-2-lemma))
           :in-theory (e/d (lift-expr-value-to-frame)
                           (undo-expr-value-with-nonempty-dims-2-lemma))))
  )

(defun all-elements-of-dims (lst dims)
  (if (endp lst)
      t
      (and (equal (dims-of-expr-value (car lst)) dims)
           (all-elements-of-dims (cdr lst) dims))))

(defthm list-of-base-values-car-cellss
    (implies (and (consp cellss)
                  (list-of-list-of-base-values cellss))
             (list-of-base-values (car cellss)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((list-of-list-of-base-values cellss))))
  )

(defthm list-of-base-values-nthcdr
    (implies (list-of-base-values cells)
             (list-of-base-values (nthcdr n cells))))

(defthm list-of-base-values-take
    (implies (and (list-of-base-values cells)
                  (<= n (len cells)))
             (list-of-base-values (take n cells))))

(defthm n-<=-m-when-m-mod-n-0
    (implies (and (posp m)
                  (posp n)
                  (equal (mod m n) 0))
             (<= n m)))

(defthm mod-len-nat-list-product-cdr-frame
    (implies (and (equal (len cells) (nat-list-product frame))
                  (pos-listp frame)
                  (consp frame)
                  )
             (equal (mod (len cells) (nat-list-product (cdr frame)))
                    0))
  :otf-flg t
  :instructions (:pro (:claim (posp (len cells)))
                      (:generalize ((len cells) len-cells))
                      (:demote 1)
                      (:dv 1)
                      (:dv 2)
                      :x
                      (:= (* (car frame)
                             (nat-list-product (cdr frame))))
                      (:claim (posp (car frame)))
                      (:claim (posp (nat-list-product (cdr frame))))
                      :top
                      (:generalize ((car frame) x)
                                   ((nat-list-product (cdr frame)) y))
                      :bash)
  )

(defthm list-of-list-of-base-values-list-split
    (implies (and (list-of-base-values cells)
                  (posp n)
                  (equal (mod (len cells) n) 0))
             (list-of-list-of-base-values (list-split cells n)))
  :otf-flg t
  :hints (("Goal"
           :induct (list-split cells n)
           :in-theory (enable list-split
                              list-of-list-of-base-values))
          ("Subgoal *1/2"
           :use ((:instance n-<=-m-when-m-mod-n-0
                            (m (MOD (LEN CELLS) N))
                            (n n))
                 (:instance list-of-base-values-take))
           :in-theory (e/d (list-split
                            list-of-list-of-base-values)
                           (n-<=-m-when-m-mod-n-0)))
          )

  )

(defthm list-of-primop-int-binary-x-nthcdr
    (implies (list-of-primop-int-binary-x cells)
             (list-of-primop-int-binary-x (nthcdr n cells))))

(defthm list-of-primop-int-binary-x-take
    (implies (and (list-of-primop-int-binary-x cells)
                  (<= n (len cells)))
             (list-of-primop-int-binary-x (take n cells))))

(defthm list-of-list-of-primop-int-binary-x-list-split
    (implies (and (list-of-primop-int-binary-x cells)
                  (posp n)
                  (equal (mod (len cells) n) 0))
             (list-of-list-of-primop-int-binary-x (list-split cells n)))
  :otf-flg t
  :hints (("Goal"
           :induct (list-split cells n)
           :in-theory (enable list-split
                              list-of-list-of-primop-int-binary-x))
          ("Subgoal *1/2"
           :use ((:instance n-<=-m-when-m-mod-n-0
                            (m (MOD (LEN CELLS) N))
                            (n n))
                 (:instance list-of-primop-int-binary-x-take))
           :in-theory (e/d (list-split
                            list-of-list-of-primop-int-binary-x)
                           (n-<=-m-when-m-mod-n-0)))
          )

  )

(defthm list-of-primop-int-binary-nthcdr
    (implies (list-of-primop-int-binary cells)
             (list-of-primop-int-binary (nthcdr n cells))))

(defthm list-of-primop-int-binary-take
    (implies (and (list-of-primop-int-binary cells)
                  (<= n (len cells)))
             (list-of-primop-int-binary (take n cells))))

(defthm list-of-list-of-primop-int-binary-list-split
    (implies (and (list-of-primop-int-binary cells)
                  (posp n)
                  (equal (mod (len cells) n) 0))
             (list-of-list-of-primop-int-binary (list-split cells n)))
  :otf-flg t
  :hints (("Goal"
           :induct (list-split cells n)
           :in-theory (enable list-split
                              list-of-list-of-primop-int-binary))
          ("Subgoal *1/2"
           :use ((:instance n-<=-m-when-m-mod-n-0
                            (m (MOD (LEN CELLS) N))
                            (n n))
                 (:instance list-of-primop-int-binary-take))
           :in-theory (e/d (list-split
                            list-of-list-of-primop-int-binary)
                           (n-<=-m-when-m-mod-n-0)))
          )

  )

(defthm check-dims-of-expr-value-vector-expr-value-list-with-nonempty-dims
    (implies (and (consp cells)
                  (all-elements-of-dims cells dims)
                  (expr-value-wfp (expr-value-vector cells))
                  )
             (equal (check-dims-of-expr-value
                     (expr-value-vector cells))
                    (cons (len cells) dims)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :expand ((CHECK-DIMS-OF-EXPR-VALUE
                     (LIST :VECTOR (EXPR-VALUE-LIST-FIX CELLS)))
                    (ALL-ELEMENTS-OF-DIMS CELLS DIMS)
                    (CHECK-DIMS-OF-EXPR-VALUE-LIST CELLS))
           :in-theory (enable CHECK-DIMS-OF-EXPR-VALUE
                              DIMS-OF-EXPR-VALUE
                              expr-value-vector
                              all-elements-of-dims
                              expr-value-wfp
                              expr-value-kind
                              EXPR-VALUE-VECTOR->ELEMS
                              )))
  )

(defthm not-member-equal-0-of-pos-list
    (implies (pos-listp frame)
             (not (member-equal 0 frame))))

(defthm not-reserrp-check-dims-of-primop-value
    (implies (and (expr-value-wfp cell)
                  (equal (expr-value-kind cell)
                         :primop)
                  )
             (not (RESERRP (CHECK-DIMS-OF-PRIMOP-VALUE (EXPR-VALUE-PRIMOP->VAL
                                                        CELL)))))
  :hints (("Goal"
           :expand ((CHECK-DIMS-OF-EXPR-VALUE CELL))
           :in-theory (enable CHECK-DIMS-OF-PRIMOP-VALUE
                              EXPR-VALUE-PRIMOP->VAL
                              expr-value-wfp
                              expr-value-kind)))
  )

(mutual-recursion

 (defun cells-to-expr-value-hint (cells frame)
   (DECLARE (XARGS :MEASURE (two-nats-measure (acl2-count frame)
                                              (expr-value-list-count cells))))
   (if (endp frame)
       cells
       (cells-to-expr-value-hint-list
         (list-split (expr-value-list-fix cells)
                     (/ (len cells) (car frame)))
         (cdr frame))))

 (defun cells-to-expr-value-hint-list (cellss frame)
   (DECLARE (XARGS :MEASURE (two-nats-measure (acl2-count frame)
                                              (EXPR-VALUE-LIST-list-COUNT cellss))))
   (if (endp cellss)
       nil
       (cons (cells-to-expr-value-hint (car cellss) frame)
             (cells-to-expr-value-hint-list (cdr cellss) frame))))
 )

(acl2::make-flag flag-cells-to-expr-value-hint cells-to-expr-value-hint
                 :flag-mapping ((cells-to-expr-value-hint      term)
                                (cells-to-expr-value-hint-list list)))

(defun all-dims-of-expr-value (values frame)
  (declare (xargs :guard (expr-value-listp values)))
  (if (endp values)
      t
      (and (equal (check-dims-of-expr-value (car values)) frame)
           (all-dims-of-expr-value (cdr values) frame))))

(defthm check-dims-not-reserrp-when-all-dims-of-expr-value
    (implies (and (pos-listp frame)
                  (all-dims-of-expr-value cells frame)
                  )
             (not (reserrp (check-dims-of-expr-value-list cells))))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list
                              reserrp)))
  )


(defthm list-repeatp-check-dims-when-all-dims-of-expr-value
    (implies (and (pos-listp frame)
                  (all-dims-of-expr-value cells frame)
                  )
             (list-repeatp (check-dims-of-expr-value-list cells)))
  :hints (("Goal"
           :in-theory (enable check-dims-of-expr-value-list
                              list-repeatp)))
  )

(defthm subgoal-1-of-check-dims-of-expr-value-with-nonempty-dims
 (implies
  (and
   (equal flag 'term)
   (consp frame)
   (if nil
    (implies
     (and (expr-value-listp nil)
          (expr-value-list-wfp nil)
          (or (list-of-base-values nil)
              (list-of-primop-int-binary nil)
              (list-of-primop-int-binary-x nil))
          (pos-listp (cdr frame))
          (equal (len nil)
                 (nat-list-product (cdr frame)))
          (not (reserrp (expr-value-with-nonempty-dims (cdr frame)
                                                       nil))))
     (equal
         (check-dims-of-expr-value (expr-value-with-nonempty-dims (cdr frame)
                                                                  nil))
         (cdr frame)))
    (implies
     (and
      (expr-value-list-listp (list-split (expr-value-list-fix cells)
                                         (* (len cells) (/ (car frame)))))
      (expr-value-list-list-wfp (list-split (expr-value-list-fix cells)
                                            (* (len cells) (/ (car frame)))))
      (or (list-of-list-of-base-values
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame)))))
          (list-of-list-of-primop-int-binary
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame)))))
          (list-of-list-of-primop-int-binary-x
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame))))))
      (pos-listp (cdr frame))
      (all-lists-of-len-n (list-split (expr-value-list-fix cells)
                                      (* (len cells) (/ (car frame))))
                          (nat-list-product (cdr frame)))
      (not (reserrp (expr-value-list-with-nonempty-dims
                         (cdr frame)
                         (list-split (expr-value-list-fix cells)
                                     (* (len cells) (/ (car frame))))))))
     (all-dims-of-expr-value
          (expr-value-list-with-nonempty-dims
               (cdr frame)
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame)))))
          (cdr frame)))))
  (if
   (equal flag 'term)
   (implies
    (and (expr-value-listp cells)
         (expr-value-list-wfp cells)
         (or (list-of-base-values cells)
             (list-of-primop-int-binary cells)
             (list-of-primop-int-binary-x cells))
         (pos-listp frame)
         (equal (len cells)
                (nat-list-product frame))
         (not (reserrp (expr-value-with-nonempty-dims frame cells))))
    (equal
       (check-dims-of-expr-value (expr-value-with-nonempty-dims frame cells))
       frame))
   (implies
    (and (expr-value-list-listp cellss)
         (expr-value-list-list-wfp cellss)
         (or (list-of-list-of-base-values cellss)
             (list-of-list-of-primop-int-binary cellss)
             (list-of-list-of-primop-int-binary-x cellss))
         (pos-listp frame)
         (all-lists-of-len-n cellss (nat-list-product frame))
         (not (reserrp (expr-value-list-with-nonempty-dims frame cellss))))
    (all-dims-of-expr-value (expr-value-list-with-nonempty-dims frame cellss)
                            frame))))
 :instructions
 (:pro
  (:demote 3)
  (:dv 1)
  (:=
   (implies
    (and
      (expr-value-list-listp (list-split (expr-value-list-fix cells)
                                         (* (len cells) (/ (car frame)))))
      (expr-value-list-list-wfp (list-split (expr-value-list-fix cells)
                                            (* (len cells) (/ (car frame)))))
      (or (list-of-list-of-base-values
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame)))))
          (list-of-list-of-primop-int-binary
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame)))))
          (list-of-list-of-primop-int-binary-x
               (list-split (expr-value-list-fix cells)
                           (* (len cells) (/ (car frame))))))
      (pos-listp (cdr frame))
      (all-lists-of-len-n (list-split (expr-value-list-fix cells)
                                      (* (len cells) (/ (car frame))))
                          (nat-list-product (cdr frame)))
      (not (reserrp (expr-value-list-with-nonempty-dims
                         (cdr frame)
                         (list-split (expr-value-list-fix cells)
                                     (* (len cells) (/ (car frame))))))))
    (all-dims-of-expr-value
         (expr-value-list-with-nonempty-dims
              (cdr frame)
              (list-split (expr-value-list-fix cells)
                          (* (len cells) (/ (car frame)))))
         (cdr frame))))
  :up :pro
  (:=
   (implies
    (and (expr-value-listp cells)
         (expr-value-list-wfp cells)
         (or (list-of-base-values cells)
             (list-of-primop-int-binary cells)
             (list-of-primop-int-binary-x cells))
         (pos-listp frame)
         (equal (len cells)
                (nat-list-product frame))
         (not (reserrp (expr-value-with-nonempty-dims frame cells))))
    (equal
       (check-dims-of-expr-value (expr-value-with-nonempty-dims frame cells))
       frame)))
  :pro (:demote 3)
  (:dv 1)
  (:dv 1)
  (:= t)
  :up :s :top :pro (:dv 1)
  (:dv 1)
  :x :x (:dv 2)
  (:dv 1)
  (:dv 1)
  (:= t)
  :up :s (:dv 1)
  (:in-theory (enable pos-listp))
  :top (:demote 6)
  (:dv 1)
  :x :top :pro :s
  (:claim (expr-value-listp
               (expr-value-list-with-nonempty-dims
                    (cdr frame)
                    (list-split cells (nat-list-product (cdr frame))))))
  :s (:dv 1)
  :x
  (:in-theory (enable expr-value-vector->elems
                      expr-value-kind))
  :s :top (:demote 8)
  (:dv 1)
  (:dv 1)
  (:dv 2)
  (:dv 2)
  (:= (nat-list-product (cdr frame)))
  :top :pro (:dive 1)
  (:dive 1)
  (:rewrite check-dims-not-reserrp-when-all-dims-of-expr-value)
  :up :s (:dv 1)
  (:dv 1)
  :x-dumb :s (:claim (consp cells))
  :s :up :s :up :s (:dv 1)
  (:rewrite len-of-list-split)
  (:dv 1)
  := :x :up :s (:= (car frame))
  :nx :top (:demote 12)
  (:dv 1)
  :x :top
  (:claim (consp (list-split cells (nat-list-product (cdr frame)))))
  :s (:dv 1)
  (:dv 1)
  :x-dumb :s :up :s :up :s (:= t)
  (:dv 1)
  (:dv 1)
  := :x
  :up :s
  :up (:= t)))

(defthm-flag-cells-to-expr-value-hint
    (defthm check-dims-of-expr-value-with-nonempty-dims-explicit
        (implies (and (expr-value-listp cells)
                      (expr-value-list-wfp cells)
                      (or (list-of-base-values cells)
                          (list-of-primop-int-binary cells)
                          (list-of-primop-int-binary-x cells))
                      (pos-listp frame)
                      (equal (len cells)
                             (nat-list-product frame))
                      (not (reserrp (expr-value-with-nonempty-dims frame cells)))
                      )
                 (equal (check-dims-of-expr-value
                         (expr-value-with-nonempty-dims frame cells))
                        frame))
      :flag term
      )
    (defthm check-dims-of-expr-value-list-with-nonempty-dims-explicit
        (implies (and (expr-value-list-listp cellss)
                      (expr-value-list-list-wfp cellss)
                      (or (list-of-list-of-base-values cellss)
                          (list-of-list-of-primop-int-binary cellss)
                          (list-of-list-of-primop-int-binary-x cellss))
                      (pos-listp frame)
                      (all-lists-of-len-n cellss (nat-list-product frame))
                      (not (reserrp
                            (expr-value-list-with-nonempty-dims frame cellss)))
                      )
                 (all-dims-of-expr-value
                  (expr-value-list-with-nonempty-dims frame cellss)
                  frame))
      :flag list
      )
  :hints (("Goal"
           :in-theory (enable EXPR-VALUE-WFP
                              dims-of-expr-value
                              CHECK-DIMS-OF-EXPR-VALUE
                              CHECK-DIMS-OF-EXPR-VALUE-list
                              EXPR-VALUE-WITH-NONEMPTY-DIMS
                              EXPR-VALUE-list-WITH-NONEMPTY-DIMS))
          ("Subgoal *1/1"
           :by (:instance subgoal-1-of-check-dims-of-expr-value-with-nonempty-dims))
          ))

(defthm-flag-cells-to-expr-value-hint
    (defthm expr-valuep-expr-value-with-nonempty-dims
        (implies (and (expr-value-listp cells)
                      (expr-value-list-wfp cells)
                      (or (list-of-base-values cells)
                          (list-of-primop-int-binary cells)
                          (list-of-primop-int-binary-x cells))
                      (pos-listp frame)
                      (equal (len cells)
                             (nat-list-product frame))
                      (not (reserrp (expr-value-with-nonempty-dims frame cells)))
                      )
                 (expr-valuep
                  (expr-value-with-nonempty-dims frame cells)))
      :flag term
      )
    (defthm expr-value-listp-expr-value-list-with-nonempty-dims
        (implies (and (expr-value-list-listp cellss)
                      (expr-value-list-list-wfp cellss)
                      (or (list-of-list-of-base-values cellss)
                          (list-of-list-of-primop-int-binary cellss)
                          (list-of-list-of-primop-int-binary-x cellss))
                      (pos-listp frame)
                      (all-lists-of-len-n cellss (nat-list-product frame))
                      (not (reserrp
                            (expr-value-list-with-nonempty-dims frame cellss)))
                      )
                 (expr-value-listp
                  (expr-value-list-with-nonempty-dims frame cellss)))
      :flag list
      )
  :hints (("Goal"
           :in-theory (enable EXPR-VALUE-WFP
                              dims-of-expr-value
                              CHECK-DIMS-OF-EXPR-VALUE
                              CHECK-DIMS-OF-EXPR-VALUE-list
                              EXPR-VALUE-WITH-NONEMPTY-DIMS
                              EXPR-VALUE-list-WITH-NONEMPTY-DIMS))
          ))

(defthm expr-value-wfp-expr-value-with-nonempty-dims
    (implies (and (expr-value-listp cells)
                  (expr-value-list-wfp cells)
                  (or (list-of-base-values cells)
                      (list-of-primop-int-binary cells)
                      (list-of-primop-int-binary-x cells))
                  (pos-listp frame)
                  (equal (len cells)
                         (nat-list-product frame))
                  (not (reserrp (expr-value-with-nonempty-dims frame cells)))
                  )
             (expr-value-wfp
              (expr-value-with-nonempty-dims frame cells)))
  :instructions
  ((:use (:instance check-dims-of-expr-value-with-nonempty-dims-explicit))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   :s (:= t)
   :up
   (:=
    (equal
     (check-dims-of-expr-value (expr-value-with-nonempty-dims frame cells))
     frame))
   :up :pro
   :x-dumb
   (:= (not (reserrp (check-dims-of-expr-value
                      (expr-value-with-nonempty-dims frame cells)))))
   :s (:= t))
  )

(defthm expr-value-listp-when-all-dims-of-expr-value
    (implies (and (pos-listp frame)
                  (all-dims-of-expr-value lst frame))
             (expr-value-list-wfp lst))
  :hints (("Goal"
           :in-theory (enable expr-value-list-wfp expr-value-wfp))))

(defthm expr-value-list-wfp-expr-value-with-nonempty-dims
    (implies (and (expr-value-list-listp cellss)
                  (expr-value-list-list-wfp cellss)
                  (or (list-of-list-of-base-values cellss)
                      (list-of-list-of-primop-int-binary cellss)
                      (list-of-list-of-primop-int-binary-x cellss))
                  (pos-listp frame)
                  (all-lists-of-len-n cellss (nat-list-product frame))
                  (not (reserrp
                        (expr-value-list-with-nonempty-dims frame cellss)))
                  )
             (expr-value-list-wfp
              (expr-value-list-with-nonempty-dims frame cellss)))
  :hints (("Goal"
           :use ((:instance
                  check-dims-of-expr-value-list-with-nonempty-dims-explicit))
           ))
  )

(defthm fun-value-param-dims-expr-value-with-nonempty-dims
    (implies (and (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal fval (expr-value-first-fun funval))
                  (expr-value-case fval :primop)
                  (primop-value-case (expr-value-primop->val fval)
                                     :int-binary-x)
                  (not (reserrp (fun-value-param-dims funval)))
                  )
             (equal (fun-value-param-dims funval)
                    '(nil)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable fun-value-param-dims
                              EXPR-VALUE-PRIMOP->VAL
                              TYPE-OF-PRIMOP-VALUE-FUN))))

(defthm dims-of-expr-value-with-nonempty-dims-explicit
    (implies (and (expr-value-listp cells)
                  (expr-value-list-wfp cells)
                  (or (list-of-base-values cells)
                      (list-of-primop-int-binary cells)
                      (list-of-primop-int-binary-x cells))
                  (pos-listp frame)
                  (equal (len cells)
                         (nat-list-product frame))
                  (not (reserrp (expr-value-with-nonempty-dims frame cells)))
                  )
             (equal (dims-of-expr-value
                     (expr-value-with-nonempty-dims frame cells))
                    frame))
  :hints (("Goal"
           :do-not-induct t
           :expand ((dims-of-expr-value
                     (expr-value-with-nonempty-dims frame cells)))
           :use ((:instance
                  check-dims-of-expr-value-with-nonempty-dims-explicit)))
          )
  )


(defthm cons-list-split
    (equal (consp (list-split cells n))
           (consp cells))
  :hints (("Goal"
           :expand ((list-split cells n)))))

(defthm cons-expr-value-list-with-nonempty-dims
    (equal (consp (expr-value-list-with-nonempty-dims dims valss))
           (consp valss))
  :hints (("Goal"
           :expand ((expr-value-list-with-nonempty-dims dims valss)))))

(defthm when-expr-is-nested-vectors-of-curried-base-values-and-frame-is-null
    (implies (and (equal fun-frame (dims-of-expr-value funval))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (equal fun-frame nil)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  )
             (and (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary-x)))
  :hints (("Goal"
           :expand ((expr-is-nested-vectors-of-curried-base-values funval)
                    (dims-of-expr-value funval)
                    (check-dims-of-expr-value funval)
                    (expr-valuep funval)
                    (expr-value-wfp funval))
           :in-theory (enable expr-value-kind)
           ))
  )

(defthm list-of-primop-int-binary-x-of-repeat
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary-x)
                  (expr-value-case (primop-value-int-binary-x->xval (expr-value-primop->val funval)) :base)
                  )
             (list-of-primop-int-binary-x
              (repeat n funval)))
  :hints (("Goal"
           :in-theory (enable repeat)))
  )

(defthm list-prefix-join-cases-for-two-lists
    (implies (mv-nth 0 (list-prefix-join (list fun-frame arg-frame)))
             (equal (list-prefix-join (list fun-frame arg-frame))
                    (mv t
                        (if (prefixp fun-frame arg-frame)
                            (true-list-fix arg-frame)
                            (true-list-fix fun-frame)))))
  :hints (("Goal"
           :in-theory (enable list-prefix-join)))
  )

(defthmd list-prefix-for-prefix
    (equal (list-prefix-join (list xs ys))
           (if (prefixp xs ys)
               (mv t (true-list-fix ys))
               (if (prefixp ys xs)
                   (mv t (true-list-fix xs))
                   (mv nil nil))))
  :hints (("Goal"
           :in-theory (enable list-prefix-join)))
  )

(defthm lift-expr-value-to-frame-when-frame-is-prefix-and-frame-of-val
    (implies (and (not (reserrp (lift-expr-value-to-frame val frame pframe)))
                  (equal frame (dims-of-expr-value val))
                  (prefixp frame pframe)
                  (expr-value-wfp val)
                  (expr-valuep val))
             (equal (lift-expr-value-to-frame val frame pframe)
                    (repeat-each (nat-list-product
                                  (nthcdr (len frame) pframe))
                                 (get-cells-from-expr-value val))))
  :hints (("Goal"
           :use ((:instance
                  cells-at-depth-in-expr-value-when-depth-is-val-depth
                  (depth (len (dims-of-expr-value val)))))
           :in-theory (enable lift-expr-value-to-frame))))

(defthm list-of-primop-int-binary-x-repeat-each
    (implies (and (consp lst)
                  (list-of-primop-int-binary-x lst))
             (list-of-primop-int-binary-x
              (repeat-each n lst)))
  :hints (("Goal"
           :in-theory (enable list-of-primop-int-binary-x
                              repeat-each)))
  )



(defthm list-of-base-values-repeat
    (implies (and (expr-valuep val)
                  (EQUAL (EXPR-VALUE-KIND val)
                         :BASE))
             (list-of-base-values
              (repeat n val)))
  :hints (("Goal"
           :in-theory (enable list-of-base-values
                              repeat)))
  )

(defthm list-of-base-values-repeat-each
    (implies (list-of-base-values lst)
             (list-of-base-values (repeat-each n lst)))
  :hints (("Goal"
           :in-theory (enable list-of-base-values
                              repeat-each)))
  )


(defthm-flag-get-cells
    (defthm consp-get-cells-when-expr-is-nested-vectors
        (implies (and (EXPR-VALUEP VAL)
                      (EXPR-VALUE-WFP VAL)
                      (or (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES VAL)
                          (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES VAL))
                      )
                 (CONSP (GET-CELLS-FROM-EXPR-VALUE VAL)))
      :flag term)
    (defthm consp-get-cells-when-expr-list-is-nested-vectors
        (implies (and (consp lst)
                      (EXPR-VALUE-listP lst)
                      (EXPR-VALUE-list-WFP lst)
                      (or (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-list lst)
                          (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-list lst))
                      )
                 (CONSP (GET-CELLS-FROM-EXPR-VALUE-list lst)))
      :flag list)

  :hints (("Goal"
           :in-theory (enable get-cells-from-expr-value
                              get-cells-from-expr-value-list
                              expr-is-nested-vectors-of-curried-base-values
                              expr-is-nested-vectors-of-base-values
                              expr-is-nested-vectors-of-curried-base-values-list
                              expr-is-nested-vectors-of-base-values-list
                              expr-value-wfp
                              expr-valuep))))

(defun length-of-all-elements-in-list-is-correct (lst)
  (if (endp lst)
      t
      (and (equal (len (get-cells-from-expr-value (car lst)))
                  (nat-list-product (dims-of-expr-value (car lst))))
           (length-of-all-elements-in-list-is-correct (cdr lst)))))

(defun length-of-all-elements-in-list-is-constant (lst c)
  (if (endp lst)
      t
      (and (equal (len (get-cells-from-expr-value (car lst)))
                  c)
           (length-of-all-elements-in-list-is-constant (cdr lst) c))))

(defthm not-reserrp-check-dims-of-expr-value-list-when-expr-value-list-wfp
    (implies (expr-value-list-wfp lst)
             (not (reserrp (check-dims-of-expr-value-list lst))))
  :hints (("Goal"
           :in-theory (enable expr-value-list-wfp
                              expr-value-wfp
                              check-dims-of-expr-value-list)))
  )


(DEFTHM len-get-cells-from-expr-value-subgoal-1/3
 (IMPLIES
  (AND
   (NOT (EQUAL FLAG 'TERM))
   (CONSP LST)
   (IF T
    (IMPLIES
         (AND (EXPR-VALUEP (CAR LST))
              (EXPR-VALUE-WFP (CAR LST))
              (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES (CAR LST))
                  (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES (CAR LST))))
         (EQUAL (LEN (GET-CELLS-FROM-EXPR-VALUE (CAR LST)))
                (NAT-LIST-PRODUCT (DIMS-OF-EXPR-VALUE (CAR LST)))))
    (IMPLIES
         (AND (EXPR-VALUE-LISTP NIL)
              (EXPR-VALUE-LIST-WFP NIL)
              (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-LIST NIL)
                  (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-LIST NIL)))
         (LENGTH-OF-ALL-ELEMENTS-IN-LIST-IS-CORRECT NIL)))
   (IF NIL
     (IMPLIES (AND (EXPR-VALUEP NIL)
                   (EXPR-VALUE-WFP NIL)
                   (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES NIL)
                       (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES NIL)))
              (EQUAL (LEN (GET-CELLS-FROM-EXPR-VALUE NIL))
                     (NAT-LIST-PRODUCT (DIMS-OF-EXPR-VALUE NIL))))
    (IMPLIES
     (AND
         (EXPR-VALUE-LISTP (CDR LST))
         (EXPR-VALUE-LIST-WFP (CDR LST))
         (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-LIST (CDR LST))
             (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-LIST (CDR LST))))
     (LENGTH-OF-ALL-ELEMENTS-IN-LIST-IS-CORRECT (CDR LST)))))
  (IF (EQUAL FLAG 'TERM)
      (IMPLIES (AND (EXPR-VALUEP VAL)
                    (EXPR-VALUE-WFP VAL)
                    (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES VAL)
                        (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES VAL)))
               (EQUAL (LEN (GET-CELLS-FROM-EXPR-VALUE VAL))
                      (NAT-LIST-PRODUCT (DIMS-OF-EXPR-VALUE VAL))))
    (IMPLIES
         (AND (EXPR-VALUE-LISTP LST)
              (EXPR-VALUE-LIST-WFP LST)
              (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-LIST LST)
                  (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-LIST LST)))
         (LENGTH-OF-ALL-ELEMENTS-IN-LIST-IS-CORRECT LST))))
 :INSTRUCTIONS
 (:PRO
  (:=
     (IMPLIES
          (AND (EXPR-VALUE-LISTP LST)
               (EXPR-VALUE-LIST-WFP LST)
               (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-LIST LST)
                   (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-LIST LST)))
          (LENGTH-OF-ALL-ELEMENTS-IN-LIST-IS-CORRECT LST)))
  :PRO (:DEMOTE 3)
  (:DV 1)
  (:=
    (IMPLIES
         (AND (EXPR-VALUEP (CAR LST))
              (EXPR-VALUE-WFP (CAR LST))
              (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES (CAR LST))
                  (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES (CAR LST))))
         (EQUAL (LEN (GET-CELLS-FROM-EXPR-VALUE (CAR LST)))
                (NAT-LIST-PRODUCT (DIMS-OF-EXPR-VALUE (CAR LST))))))
  (:DV 1)
  (:= T)
  :UP :S :TOP :PRO (:DEMOTE 3)
  (:DV 1)
  (:=
   (IMPLIES
    (AND (EXPR-VALUE-LISTP (CDR LST))
         (EXPR-VALUE-LIST-WFP (CDR LST))
         (OR (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES-LIST (CDR LST))
             (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES-LIST (CDR LST))))
    (LENGTH-OF-ALL-ELEMENTS-IN-LIST-IS-CORRECT (CDR LST))))
  (:DV 1)
  (:= T)
  :UP
  :S :TOP
  :PRO :X))

(defthm len-get-cells-from-expr-value-subgoal-1/1a
    (implies (and (expr-value-list-wfp lst)
                  (consp lst)
                  (list-repeatp (check-dims-of-expr-value-list lst))
                  (length-of-all-elements-in-list-is-correct lst))
             (length-of-all-elements-in-list-is-constant
              lst
              (nat-list-product (dims-of-expr-value (car lst)))))
  :instructions
  (:induct (:change-goal nil t)
           (:change-goal nil t)
           :bash (:dv 1)
           (:dv 4)
           :x :top :s :pro (:demote 3)
           (:dv 1)
           (:dv 1)
           (:= t)
           :up :s :top (:demote 5)
           (:dv 1)
           (:dv 1)
           :x :top (:demote 3)
           (:dv 1)
           :x (:casesplit (consp (cdr lst)))
           (:change-goal nil t)
           :top :bash (:dv 2)
           :x :top :pro
           (:in-theory (enable expr-value-wfp))
           (:demote 9)
           (:dv 1)
           (:dv 1)
           (:= (cons (check-dims-of-expr-value (car lst))
                     (check-dims-of-expr-value-list (cdr lst))))
           (:dv 2)
           :x
           (:= (cons (check-dims-of-expr-value (cadr lst))
                     (check-dims-of-expr-value-list (cddr lst))))
           :up :up :x :top :pro :x-dumb
           (:= (and (equal (len (get-cells-from-expr-value (car lst)))
                           (nat-list-product (dims-of-expr-value (car lst))))
                    (length-of-all-elements-in-list-is-constant
                     (cdr lst)
                     (nat-list-product (dims-of-expr-value (car lst))))))
           (:dv 1)
           (:= t)
           :nx (:dv 2)
           (:dv 1)
           :x
           (:= (check-dims-of-expr-value (car lst)))
           :top :s (:demote 9)
           (:dv 1)
           (:dv 2)
           (:dv 1)
           :x (:= (check-dims-of-expr-value (car lst)))
           :top :s))

(defthm len-get-cells-from-expr-value-subgoal-1/1b
    (implies (length-of-all-elements-in-list-is-constant lst n)
             (equal (len (get-cells-from-expr-value-list lst))
                    (* n (len lst)))))

(defthm-flag-get-cells
    (defthm len-get-cells-from-expr-value
        (implies (and (expr-valuep val)
                      (expr-value-wfp val)
                      (or (expr-is-nested-vectors-of-base-values val)
                          (expr-is-nested-vectors-of-curried-base-values val))
                      )
                 (equal (len (get-cells-from-expr-value val))
                        (nat-list-product (dims-of-expr-value val))))
      :flag term
      )

    (defthm len-get-cells-from-expr-value-list
        (implies (and (expr-value-listp lst)
                      (expr-value-list-wfp lst)
                      (or (expr-is-nested-vectors-of-base-values-list lst)
                          (expr-is-nested-vectors-of-curried-base-values-list lst))
                      )
                  (length-of-all-elements-in-list-is-correct lst))
      :flag list
      )
  :hints (("Goal"
           :in-theory (e/d (dims-of-expr-value
                              nat-list-product
                              get-cells-from-expr-value
                              expr-is-nested-vectors-of-base-values
                              expr-is-nested-vectors-of-curried-base-values
                              CHECK-DIMS-OF-EXPR-VALUE)
                           (len-get-cells-from-expr-value-subgoal-1/1a
                            len-get-cells-from-expr-value-subgoal-1/1b))
           )
          ("Subgoal *1/3"
           :by len-get-cells-from-expr-value-subgoal-1/3)
          ("Subgoal *1/1"
           :use ((:instance len-get-cells-from-expr-value-subgoal-1/1a
                            (lst (EXPR-VALUE-VECTOR->ELEMS VAL)))
                 (:instance len-get-cells-from-expr-value-subgoal-1/1b
                            (lst (EXPR-VALUE-VECTOR->ELEMS VAL))
                            (n (len (get-cells-from-expr-value
                                     (car (EXPR-VALUE-VECTOR->ELEMS VAL))))))))
          )
  )

(defthm len-cells-at-depth-in-expr-value
    (implies (and (expr-valuep val)
                  (expr-value-wfp val)
                  (or (expr-is-nested-vectors-of-base-values val)
                      (expr-is-nested-vectors-of-curried-base-values val))
                  (equal frame (dims-of-expr-value val))
                  )
             (equal (len (cells-at-depth-in-expr-value val (len frame)))
                    (nat-list-product frame)))
  :hints (("Goal"
           :in-theory (enable nat-list-product
                              lift-expr-value-to-frame
                              dims-of-expr-value)))
  )

(defthm nat-list-product-prefix
    (implies (and (prefixp xs ys))
             (equal (nat-list-product ys)
                    (* (nat-list-product xs)
                       (nat-list-product (nthcdr (len xs) ys)))))
  :hints (("Goal"
           :induct (prefixp xs ys)
           :in-theory (enable prefixp
                              nat-list-product)
           ))
  )

(defthm len-lift-expr-value-to-frame
    (implies (and (expr-valuep val)
                  (expr-value-wfp val)
                  (or (expr-is-nested-vectors-of-base-values val)
                      (expr-is-nested-vectors-of-curried-base-values val))
                  (equal frame (dims-of-expr-value val))
                  (prefixp frame pframe)
                  )
             (equal (len (lift-expr-value-to-frame val frame pframe))
                    (nat-list-product pframe)))
  :hints (("Goal"
           :in-theory (enable nat-list-product
                              lift-expr-value-to-frame
                              dims-of-expr-value)))
  )


(defun not-reserrp-eval-app-list-bigger-limit-hint (funcells argcells limit)
  (if (endp funcells)
      (list argcells limit)
      (not-reserrp-eval-app-list-bigger-limit-hint (cdr funcells)
                                                   (cdr argcells)
                                                   (1- limit))))

(defthm not-reserrp-eval-app-list-bigger-limit-lemma
    (implies (and (integerp limit)
                  (consp funcells)
                  (list-of-base-values argcells)
                  (or (list-of-primop-int-binary funcells)
                      (list-of-primop-int-binary-x funcells))
                  (not (reserrp (eval-app-cell (car funcells)
                                               (car argcells)
                                               (1- limit)))))
             (not (reserrp (eval-app-cell (car funcells)
                                          (car argcells)
                                          limit))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-app-cell (car funcells)
                                   (car argcells)
                                   (1- limit))
                    (eval-app-cell (car funcells)
                                   (car argcells)
                                   limit)
                    (EVAL-PRIMOP-FUN (EXPR-VALUE-PRIMOP->VAL (CAR FUNCELLS))
                                     (CAR ARGCELLS)
                                     (+ -2 LIMIT))
                    (EVAL-PRIMOP-FUN (EXPR-VALUE-PRIMOP->VAL (CAR FUNCELLS))
                                     (CAR ARGCELLS)
                                     (+ -1 LIMIT))
                    ))))

(defthmd not-reserrp-eval-app-list-bigger-limit
    (implies (and (integerp limit)
                  (list-of-base-values argcells)
                  (or (list-of-primop-int-binary funcells)
                      (list-of-primop-int-binary-x funcells))
                  (equal (len funcells) (len argcells))
                  (not (reserrp (eval-app-list funcells argcells (1- limit)))))
             (not (reserrp (eval-app-list funcells argcells limit))))
 :instructions
 ((:in-theory (enable eval-app-list))
  (:induct
       (not-reserrp-eval-app-list-bigger-limit-hint funcells argcells limit))
  :pro (:demote 7)
  (:dv 1)
  (:dv 1)
  (:dv 1)
  :x :up
  :s :top :pro (:claim (< 0 (+ -1 limit)))
  (:claim (consp argcells))
  (:demote 7)
  (:dv 1)
  :s :top :pro (:demote 2)
  (:dv 1)
  (:dv 1)
  (:dive 1)
  (:= t)
  :nx (:= t)
  :nx (:= t)
  :nx (:= t)
  :nx :s :up :s :top :pro (:dv 1)
  (:dv 1)
  :x (:claim (not (zp limit)))
  :s (:dv 1)
  (:rewrite not-reserrp-eval-app-list-bigger-limit-lemma)
  :up :s :top :s (:dv 1)
  :x (:dv 1)
  (:= nil)
  :top :s
  :s :bash))

(defthm propagage-error-to-dims-of-expr-value
    (implies (not (reserrp (eval-app funval argvals limit)))
             (not (reserrp (dims-of-expr-value argval)))))

(defthm member-0-list-prefix-join
    (implies (and (not (member-equal 0 xs))
                  (not (member-equal 0 ys))
                  (mv-nth 0 (list-prefix-join (list fun-frame arg-frame)))
                  )
             (not (member-equal 0 (mv-nth 0 (list-prefix-join (list fun-frame arg-frame)))))))

(defthm firt-fun-is-binary-x-when-funval-is-nested-curries-base-values
    (implies (expr-is-nested-vectors-of-curried-base-values funval)
             (and (not (reserrp (expr-value-first-fun funval)))
                  (equal (expr-value-kind (expr-value-first-fun funval))
                         :primop)
                  (equal (primop-value-kind
                          (expr-value-primop->val (expr-value-first-fun funval)))
                         :int-binary-x)))
  :hints (("Goal"
           :in-theory (enable expr-value-first-fun)))
  )

(defthm not-reserrp-first-fun-when-funval-is-nested-curries-base-values
    (IMPLIES (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES funVAL)
             (NOT (RESERRP (EXPR-VALUE-FIRST-FUN FUNVAL))))
  :hints (("Goal"
           :in-theory (enable expr-value-first-fun)))
  )

(defthm fun-value-param-dims-of-nested-curried-base-values
    (implies (expr-is-nested-vectors-of-curried-base-values funval)
             (equal (fun-value-param-dims funval)
                    '(nil)))
  :hints (("Goal"
           :use ((:instance
                  firt-fun-is-binary-x-when-funval-is-nested-curries-base-values))
           :in-theory (e/d (TYPE-OF-PRIMOP-VALUE-FUN)
                           (firt-fun-is-binary-x-when-funval-is-nested-curries-base-values))
           :expand ( (fun-value-param-dims funval))))
  )

(defthm check-list-suffix-for-nil
    (implies (true-listp arg-frame)
             (equal (CHECK-LIST-SUFFIX ARG-FRAME NIL)
                    (mv t arg-frame)))
  :hints (("Goal" :in-theory (enable CHECK-LIST-SUFFIX))))

(defthm not-reserrp-lift-expr-value-for-large-frames
    (implies (and (or (expr-is-nested-vectors-of-base-values val)
                      (expr-is-nested-vectors-of-curried-base-values val))
                  (expr-valuep val)
                  (expr-value-wfp val)
                  (prefixp (dims-of-expr-value val) pframe)
                  )
             (not (reserrp (lift-expr-value-to-frame val
                                                     (dims-of-expr-value val)
                                                     pframe))))
  :hints (("Goal"
           :in-theory (enable lift-expr-value-to-frame)))
  )

(defthmd propagate-error-to-eval-app-list-1
  (implies (and (integerp limit)
                (not (reserrp (eval-app funval argvals limit)))
                (expr-is-nested-vectors-of-curried-base-values funval)
                (equal param-dims (fun-value-param-dims funval))
                (equal fun-frame (dims-of-expr-value funval))
                (equal (car argvals) argval)
                (expr-is-nested-vectors-of-base-values argval)
                (expr-valuep argval)
                (expr-value-wfp argval)
                ;; (equal arg-frame (dims-of-expr-value argval))
                (equal arg-dims (dims-of-expr-value argval))
                (equal arg-frame
                       (cadr (check-list-suffix arg-dims (car param-dims))))
                (equal (list-prefix-join (list fun-frame arg-frame))
                       (mv t pframe))
                (equal funcells
                       (lift-expr-value-to-frame funval fun-frame pframe))
                (equal argcells
                       (lift-expr-value-to-frame argval arg-frame pframe)))
           (not (reserrp (dims-of-expr-value argval))))
  :instructions (:bash))


(defthm check-list-suffix-nil
    (implies (true-listp l)
             (equal (check-list-suffix l nil)
                    (mv t l))))

(defthm list-prefix-join-when-prefix
    (implies (prefixp xs ys)
             (equal (list-prefix-join (list xs ys))
                    (mv t (true-list-fix ys))))
  :hints (("Goal" :in-theory (enable list-prefix-join))))

(defthmd expr-value-first-fun-of-nested-vectors-of-curried-base-values
    (implies (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES FUNVAL)
             (let ((firstfun (expr-value-first-fun FUNVAL)))
               (EXPR-VALUE-CASE
                firstfun
                :PRIMOP
                (AND (PRIMOP-VALUE-CASE firstfun.VAL :INT-BINARY-X)
                     (EQUAL (EXPR-VALUE-KIND
                             (PRIMOP-VALUE-INT-BINARY-X->XVAL firstfun.VAL))
                            :BASE))
                :OTHERWISE NIL)))
  :hints (("Goal"
           :in-theory (enable EXPR-VALUE-FIRST-FUN
                              ))))

(defthm fun-value-param-dims-of-nested-vectors-of-curried-base-values
    (implies (EXPR-IS-NESTED-VECTORS-OF-CURRIED-BASE-VALUES FUNVAL)
             (equal (FUN-VALUE-PARAM-DIMS FUNVAL)
                    (list nil)))
  :hints (("Goal"
           :use ((:instance
                  expr-value-first-fun-of-nested-vectors-of-curried-base-values))
           )))

(defthmd propagate-error-to-eval-app-list-2a
    (implies (and (integerp limit)
                  (not (reserrp (eval-app funval argvals limit)))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells
                         (lift-expr-value-to-frame funval fun-frame pframe))
                  (equal argcells
                         (lift-expr-value-to-frame argval arg-frame pframe)))
             (not (reserrp (eval-app-list funcells argcells (1- limit)))))
  :instructions
  (:bash
   (:use (:instance list-prefix-for-prefix
                    (xs (dims-of-expr-value funval))
                    (ys (dims-of-expr-value (car argvals)))))
   :pro
   (:claim (or (prefixp (dims-of-expr-value (car argvals))
                        (dims-of-expr-value funval))
               (prefixp (dims-of-expr-value funval)
                        (dims-of-expr-value (car argvals)))))
   (:casesplit (prefixp (dims-of-expr-value funval)
                        (dims-of-expr-value (car argvals))))
   (:change-goal nil t)
   (:use (:instance check-list-suffix-nil
                    (l (dims-of-expr-value (car argvals)))))
   :pro (:forwardchain 1)
   (:claim (true-listp (dims-of-expr-value funval)))
   (:demote 8)
   (:dv 1)
   (:dv 1)
   :=
   (:= (list t
             (true-list-fix (dims-of-expr-value funval))))
   (:dv 2)
   (:= (dims-of-expr-value funval))
   :top :pro
   (:claim (equal pframe (dims-of-expr-value funval)))
   (:dv 1)
   (:dv 1)
   (:dv 1)
   (:dv 3)
   := :up :nx (:dv 3)
   := :top (:demote 3)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up :s (:claim (consp argvals))
   :s :top :pro (:demote 17)
   (:dive 1)
   (:dive 1)
   (:dv 2)
   (:dv 1)
   := :up :up
   (:= (dims-of-expr-value (car argvals)))
   :up (:= nil)
   :up :s :top :bash (:demote 3)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up
   :s :top :pro (:claim (consp argvals))
   (:demote 11)
   (:dv 1)
   :s :top :pro (:demote 14)
   (:dv 1)
   (:dive 1)
   (:dv 2)
   (:dv 1)
   (:rewrite check-list-suffix-dims-nil)
   (:change-goal nil t)
   (:= t)
   :up :up :s :up (:= t)
   :up :s
   (:claim (equal (cadr (check-list-suffix (dims-of-expr-value (car argvals))
                                           nil))
                  (dims-of-expr-value (car argvals))))
   :s
   :top :bash))

(defthm frames-are-compatible
    (implies (equal (list-prefix-join (list fun-frame arg-frame))
                    (list t pframe))
             (or (prefixp fun-frame arg-frame)
                 (prefixp arg-frame fun-frame)))
  :hints (("Goal"
           :use ((:instance list-prefix-for-prefix
                            (Xs fun-frame)
                            (Ys arg-frame)))
           :IN-THEORY (DISABLE list-prefix-for-prefix)))
  :rule-classes nil)

(defthm list-prefix-join-single-list
    (equal (list-prefix-join (list xs))
           (mv t (true-list-fix xs)))
  :hints (("Goal"
           :expand ((list-prefix-join (list xs))))))

(defthm list-prefix-join-is-prefix
    (implies (equal (list-prefix-join (list fun-frame arg-frame))
                    (list t pframe))
             (and (prefixp fun-frame pframe)
                  (prefixp arg-frame pframe)))
  :hints (("Goal"
           :expand ((list-prefix-join (list fun-frame arg-frame)))
           :use ((:instance list-prefix-join-when-prefix
                            (Ys arg-frame)
                            (Xs fun-frame)))))

  )

(defthmd list-of-base-values-lift-expr-value-when-expr-is-nested-vectors-of-base-values
    (implies (and (expr-is-nested-vectors-of-curried-base-values funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal argcells
                         (lift-expr-value-to-frame argval arg-frame pframe))
                  )
             (list-of-base-values argcells))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fun-value-param-dims-of-nested-curried-base-values)
                 (:instance LIST-PREFIX-JOIN-CASES-FOR-TWO-LISTS)
                 (:instance frames-are-compatible)
                 )
           :in-theory (disable
                       fun-value-param-dims-of-nested-curried-base-values
                       FUN-VALUE-PARAM-DIMS-OF-NESTED-VECTORS-OF-CURRIED-BASE-VALUES
                       list-prefix-join-cases-for-two-lists
                       len-lift-expr-value-to-frame
                       )
           ))
  )

(defthmd propagate-error-to-eval-app-list-2
    (implies (and (integerp limit)
                  (not (reserrp (eval-app funval argvals limit)))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells
                         (lift-expr-value-to-frame funval fun-frame pframe))
                  (equal argcells
                         (lift-expr-value-to-frame argval arg-frame pframe)))
             (and (not (reserrp (eval-app-list funcells argcells (1- limit))))
                  (not (reserrp (eval-app-list funcells argcells limit)))))
  :hints (("Goal"
           :use ((:instance propagate-error-to-eval-app-list-2a)
                 (:instance not-reserrp-eval-app-list-bigger-limit)
                 (:instance
                  list-of-base-values-lift-expr-value-when-expr-is-nested-vectors-of-base-values)
                 (:instance len-lift-expr-value-to-frame
                            (val funval)
                            (frame (dims-of-expr-value funval)))
                 (:instance len-lift-expr-value-to-frame
                            (val argval)
                            (frame (dims-of-expr-value argval)))
                 (:instance frames-are-compatible
                            (fun-frame (DIMS-OF-EXPR-VALUE FUNVAL))
                            (arg-frame (DIMS-OF-EXPR-VALUE (CAR ARGVALS))))
                 (:instance list-prefix-join-is-prefix)
                 (:instance lift-expr-value-to-frame-when-frame-is-prefix-and-frame-of-val
                            (val funval)
                            (frame (dims-of-expr-value funval)))
                 )
           :in-theory (disable len-lift-expr-value-to-frame
                               list-prefix-join-is-prefix
                               NAT-LIST-PRODUCT-PREFIX))))



(defthmd propagate-error-to-eval-app-list-3
    (implies (and (integerp limit)
                  (not (reserrp (eval-app funval argvals limit)))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells
                         (lift-expr-value-to-frame funval fun-frame pframe))
                  (equal argcells
                         (lift-expr-value-to-frame argval arg-frame pframe)))
             (not (reserrp (lift-expr-value-to-frame argval arg-frame pframe))))
  :hints (("Goal"
           :expand ((eval-app funval argvals limit)))))

(defthmd PROPAGATE-ERROR-TO-EVAL-APP-LIST-4
    (implies (and (integerp limit)
                  (not (reserrp (eval-app funval argvals limit)))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells
                         (lift-expr-value-to-frame funval fun-frame pframe))
                  (equal argcells
                         (lift-expr-value-to-frame argval arg-frame pframe)))
             (not (reserrp (lift-expr-value-to-frame funval fun-frame pframe))))
  :hints (("Goal"
           :expand ((eval-app funval argvals limit)))))

(defthm propagate-error-to-eval-app-list
    (implies (and (not (reserrp (eval-app funval argvals limit)))
                  (expr-is-nested-vectors-of-curried-base-values funval)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (equal (car argvals) argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (expr-valuep argval)
                  (expr-value-wfp argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells (lift-expr-value-to-frame funval fun-frame
                                                            pframe))
                  (equal argcells (lift-expr-value-to-frame argval arg-frame
                                                            pframe)))
             (and (not (reserrp (dims-of-expr-value argval)))
                  (not (reserrp (eval-app-list funcells argcells (1- limit))))
                  (not (reserrp (eval-app-list funcells argcells limit)))
                  (not (reserrp (lift-expr-value-to-frame argval arg-frame
                                                          pframe)))
                  (not (reserrp (lift-expr-value-to-frame funval fun-frame
                                                          pframe)))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((integerp limit)))
          ("Subgoal 2"
           :expand ((EVAL-APP FUNVAL ARGVALS LIMIT))
           )
          ("Subgoal 1"
           :use ((:instance propagate-error-to-eval-app-list-1)
                 (:instance propagate-error-to-eval-app-list-2)
                 (:instance propagate-error-to-eval-app-list-3)
                 (:instance propagate-error-to-eval-app-list-4))))
  )

(defthm len-repeat-each
    (implies (and (natp n)
                  )
             (equal (len (repeat-each n lst))
                    (* n (len lst))))
  :hints (("Goal"
           :in-theory (enable repeat-each)))
  )

(defthm eval-app-list-when-funcells-is-binary-op
    (implies (and (equal fun-frame (dims-of-expr-value funval))
                  (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp argval)
                  (expr-valuep argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (equal arg-frame (dims-of-expr-value argval))
                  (equal pframe arg-frame)
                  (equal funcells (lift-expr-value-to-frame funval fun-frame
                                                            pframe))
                  (equal argcells (lift-expr-value-to-frame argval arg-frame
                                                            pframe))
                  (not (reserrp (dims-of-expr-value argval)))
                  (not (reserrp (eval-app-list funcells argcells limit)))
                  (not (reserrp (lift-expr-value-to-frame argval arg-frame pframe)))
                  )
             (equal (eval-app-list funcells argcells limit)
                    (pairwise-curry-binary-fn funcells argcells)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-app-list-when-primop-binary-and-bases
                            (funcells (lift-expr-value-to-frame funval fun-frame pframe))
                            (argcells (lift-expr-value-to-frame argval
                                                                arg-frame
                                                                pframe))
                            (limit limit))
                 (:instance
                  lift-expr-value-to-frame-when-frame-is-pframe-and-frame-of-val
                  (val argval)
                  (frame (dims-of-expr-value argval)))
                 (:instance
                  list-of-base-values-when-expr-is-nested-vectors-of-base-values
                  (val argval))
                 )
           :in-theory (disable
                       list-of-base-values-when-expr-is-nested-vectors-of-base-values
                       lift-expr-value-to-frame-when-frame-is-pframe-and-frame-of-val
                       eval-app-list-when-primop-binary-and-bases)
           )
          )
  )

(defthm eval-app-when-funval-is-binary-op
    (implies (and (equal fun-frame (dims-of-expr-value funval))
                  (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (equal argval (car argvals))
                  (expr-value-wfp argval)
                  (expr-valuep argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (equal arg-frame (dims-of-expr-value argval))
                  (equal pframe arg-frame)
                  (equal funcells (lift-expr-value-to-frame funval fun-frame
                                                            pframe))
                  (equal argcells (lift-expr-value-to-frame argval arg-frame
                                                            pframe))
                  (not (reserrp (eval-app funval argvals limit)))
                  )
             (equal (eval-app funval argvals limit)
                    (eval-app (expr-value-with-nonempty-dims
                               pframe
                               (pairwise-curry-binary-fn funcells argcells))
                              (cdr argvals)
                              (1- limit))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :expand ((EVAL-APP FUNVAL ARGVALS LIMIT))
           :use ((:instance eval-app-list-when-funcells-is-binary-op
                            (argval (car argvals))
                            (limit (1- limit)))
                 )
           :in-theory (disable eval-app-list-when-funcells-is-binary-op))))

(defthm not-reserrp-pairwise-curry-binary-x-fn
    (not (reserrp (pairwise-curry-binary-x-fn xs ys)))
  :hints (("Goal"
           :in-theory (enable reserrp))))

(defthmd nat-list-product-of-product
    (implies (prefixp xs ys)
             (equal (nat-list-product ys)
                    (* (nat-list-product xs)
                       (nat-list-product (nthcdr (len xs) ys))))))

(defthm eval-app-list-when-funcells-is-curried-base-values
    (implies (and (expr-is-nested-vectors-of-curried-base-values funval)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (expr-valuep funval)
                  (equal (car argvals) argval)
                  (expr-value-wfp argval)
                  (expr-valuep argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells (lift-expr-value-to-frame funval fun-frame
                                                            pframe))
                  (equal argcells (lift-expr-value-to-frame argval arg-frame
                                                            pframe))
                  (not (reserrp (eval-app funval argvals limit)))
                  )
             (and (equal (eval-app-list funcells argcells (1- limit))
                         (pairwise-curry-binary-x-fn funcells argcells))
                  (equal (eval-app-list funcells argcells limit)
                         (pairwise-curry-binary-x-fn funcells argcells))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-app-list-when-primop-binary-x-and-bases
                            (funcells (lift-expr-value-to-frame funval fun-frame pframe))
                            (argcells (lift-expr-value-to-frame argval
                                                                arg-frame
                                                                pframe))
                            (limit limit))
                 (:instance eval-app-list-when-primop-binary-x-and-bases
                            (funcells (lift-expr-value-to-frame funval fun-frame pframe))
                            (argcells (lift-expr-value-to-frame argval
                                                                arg-frame
                                                                pframe))
                            (limit (1- limit)))
                 (:instance propagate-error-to-eval-app-list)
                 (:instance list-prefix-join-is-prefix)
                 (:instance nat-list-product-of-product
                            (xs (DIMS-OF-EXPR-VALUE FUNVAL))
                            (ys PFRAME))
                 (:instance nat-list-product-of-product
                            (xs (DIMS-OF-EXPR-VALUE argVAL))
                            (ys PFRAME))
                 (:instance
                  lift-expr-value-to-frame-when-frame-is-prefix-and-frame-of-val
                  (val argval)
                  (frame arg-frame))
                 (:instance
                  list-of-base-values-when-expr-is-nested-vectors-of-base-values
                  (val argval))
                 )
           :in-theory (disable
                       propagate-error-to-eval-app-list
                       list-prefix-join-is-prefix
                       list-of-base-values-when-expr-is-nested-vectors-of-base-values
                       lift-expr-value-to-frame-when-frame-is-pframe-and-frame-of-val
                       eval-app-list-when-primop-binary-x-and-bases)
           )
          )
  )

(defthm eval-app-when-funcells-is-curried-base-values
    (implies (and (expr-is-nested-vectors-of-curried-base-values funval)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (expr-valuep funval)
                  (equal (car argvals) argval)
                  (expr-value-wfp argval)
                  (expr-valuep argval)
                  (expr-is-nested-vectors-of-base-values argval)
                  (equal arg-dims (dims-of-expr-value argval))
                  (equal arg-frame
                         (cadr (check-list-suffix arg-dims (car param-dims))))
                  (equal (list-prefix-join (list fun-frame arg-frame))
                         (mv t pframe))
                  (equal funcells (lift-expr-value-to-frame funval fun-frame
                                                            pframe))
                  (equal argcells (lift-expr-value-to-frame argval arg-frame
                                                            pframe))
                  (not (reserrp (eval-app funval argvals limit)))
                  )
             (equal (eval-app funval argvals limit)
                    (eval-app (expr-value-with-nonempty-dims
                               pframe
                               (pairwise-curry-binary-x-fn funcells argcells))
                              (cdr argvals)
                              (1- limit))))
  :instructions
  ((:use (:instance eval-app-list-when-funcells-is-curried-base-values))
   :pro (:forwardchain 1)
   (:demote 17)
   :pro (:demote 16)
   (:dv 1)
   (:dv 1)
   (:dv 1)
   :x :up :up :s :top :pro (:demote 19)
   (:claim (consp argvals))
   (:dv 1)
   :s :top :pro
   (:claim (equal (cadr (check-list-suffix arg-dims nil))
                  arg-dims))
   (:demote 22)
   (:dv 1)
   :s
   (:casesplit (prefixp fun-frame arg-dims))
   :s :up :pro (:dv 1)
   :x :top :bash :s :top :pro (:dv 1)
   :x :top :bash
   (:use (:instance frames-are-compatible
                    (fun-frame (dims-of-expr-value funval))
                    (arg-frame (dims-of-expr-value (car argvals)))))
   :pro (:forwardchain 1)
   (:claim (prefixp (dims-of-expr-value (car argvals))
                    (dims-of-expr-value funval)))
   (:use (:instance list-prefix-join-cases-for-two-lists
                    (fun-frame (dims-of-expr-value funval))
                    (arg-frame (dims-of-expr-value (car argvals)))))
   :pro (:forwardchain 1)
   (:demote 21)
   (:dv 1)
   (:dv 1)
   := :up :s (:dv 2)
   (:= (dims-of-expr-value funval))
   :top :pro :s
   (:=
    (equal
     (eval-app-list
      (get-cells-from-expr-value funval)
      (lift-expr-value-to-frame (car argvals)
                                (dims-of-expr-value (car argvals))
                                pframe)
      (+ -1 limit))
     (pairwise-curry-binary-x-fn
      (repeat-each (nat-list-product (nthcdr (len pframe) pframe))
                   (get-cells-from-expr-value funval))
      (repeat-each
       (nat-list-product (nthcdr (len (dims-of-expr-value (car argvals)))
                                 pframe))
       (get-cells-from-expr-value (car argvals))))))
   (:demote 8)
   (:dv 1)
   :s (:dv 1)
   (:dv 1)
   (:dv 1)
   (:= 1)
   :up (:rewrite repeat-each-1)
   (:= (get-cells-from-expr-value funval))
   :up :up
   :up :bash))

(acl2::make-flag flag-value-with-nonempty-dims expr-value-with-nonempty-dims
                 :flag-mapping ((EXPR-VALUE-WITH-NONEMPTY-DIMS      term)
                                (EXPR-VALUE-LIST-WITH-NONEMPTY-DIMS list)))

(defthm-flag-value-with-nonempty-dims
    (defthm expr-is-nested-vectors-expr-value-with-nonempty-dims
        (implies (and (list-of-primop-int-binary-x vals)
                      (expr-value-listp vals)
                      (pos-listp dims)
                      (equal (nat-list-product dims)
                             (len vals)))
                 (expr-is-nested-vectors-of-curried-base-values
                  (expr-value-with-nonempty-dims dims vals)))
      :flag term)

    (defthm expr-is-nested-vectors-expr-value-with-nonempty-dims-list
        (implies (and (all-lists-of-len-n valss (nat-list-product dims))
                      (pos-listp dims)
                      (expr-value-list-listp valss)
                      (list-of-list-of-primop-int-binary-x valss))
                 (expr-is-nested-vectors-of-curried-base-values-list
                  (expr-value-list-with-nonempty-dims dims valss)))
      :flag list)

  :hints (("Subgoal *1/3"
           :expand ((EXPR-VALUE-LIST-WITH-NONEMPTY-DIMS DIMS VALSS)))
          ("Subgoal *1/2"
           :expand ((EXPR-VALUE-WITH-NONEMPTY-DIMS DIMS VALS)
                    (EXPR-VALUE-WITH-NONEMPTY-DIMS NIL VALS)
                    (LIST-OF-PRIMOP-INT-BINARY-X VALS)))
          ("Subgoal *1/1"
           :expand ((EXPR-VALUE-WITH-NONEMPTY-DIMS DIMS VALS)
                    (LIST-OF-PRIMOP-INT-BINARY-X VALS)))
          )
  )

(defthmd posp-list-when-nat-list-with-no-zeros
    (implies (and (nat-listp list)
                  (not (member-equal 0 list)))
             (pos-listp list)))

(defthm pos-listp-dims-of-expr-value-when-nested-vectors-of-base
    (implies (EXPR-IS-NESTED-VECTORS-OF-BASE-VALUES val)
             (pos-listp (dims-of-expr-value val)))
  :hints (("Goal"
           :use ((:instance posp-list-when-nat-list-with-no-zeros
                            (list (dims-of-expr-value val))))))
  )

(defthm expr-value-with-nonempty-dims-nil
    (equal (expr-value-with-nonempty-dims nil vals)
           (expr-value-fix (car vals)))
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims))))


(defthm posp-limit-when-not-reserrp-eval-app
    (implies (NOT (RESERRP (EVAL-APP FUNVAL args LIMIT)))
             (and (integerp limit)
                  (< 0 limit)))
  :hints (("Goal"
           :expand ((EVAL-APP FUNVAL args LIMIT))))
  )

(defthm propagate-eval-app-reserrp-to-second-argument
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (not (reserrp
                   (eval-app
                    (expr-value-with-nonempty-dims
                     (dims-of-expr-value arg1)
                     (pairwise-curry-binary-fn
                      (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                                (dims-of-expr-value arg1))
                      (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg1))))
                    (list arg2)
                    (+ -1 limit)))))
  :instructions (:pro (:demote 13)
                      (:dv 1)
                      (:dv 1)
                      (:dv 1)
                      :x :up :up :s :top :pro
                      (:claim (equal (cadr (check-list-suffix arg1-frame nil))
                                     arg1-frame))
                      (:demote 17)
                      (:dv 1)
                      :s (:claim (not (member-equal 0 arg1-frame)))
                      :s :top
                      :pro :bash))

(defthm propagate-eval-app-reserrp-past-second-argument
    (implies (and (expr-is-nested-vectors-of-curried-base-values funval)
                  (expr-valuep funval)
                  (expr-value-wfp funval)
                  (equal param-dims (fun-value-param-dims funval))
                  (equal fun-frame (dims-of-expr-value funval))
                  (expr-valuep funval)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list fun-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg2) limit)))
                  )
             (not (reserrp (eval-app (expr-value-with-nonempty-dims
                                      pframe
                                      (eval-app-list
                                       (lift-expr-value-to-frame funval fun-frame pframe)
                                       (lift-expr-value-to-frame arg2 arg2-frame pframe)
                                       (+ -1 limit)))
                                     nil (+ limit -1)))))
  :instructions
  (:pro (:demote 12)
        (:dv 1)
        (:dv 1)
        (:dv 1)
        :x :up :up :s :top :pro
        (:claim (equal (cadr (check-list-suffix arg2-frame nil))
                       arg2-frame))
        (:claim (not (member-equal 0 arg2-frame)))
        (:demote 15)
        (:dv 1)
        :s :top :pro :bash
        (:use (:instance list-prefix-for-prefix
                         (xs (dims-of-expr-value funval))
                         (ys (dims-of-expr-value arg2))))
        :pro
        (:claim (equal (list-prefix-join (list (dims-of-expr-value funval)
                                               (dims-of-expr-value arg2)))
                       (list t
                             (true-list-fix (dims-of-expr-value funval)))))
        (:claim (equal pframe
                       (true-list-fix (dims-of-expr-value funval))))
        (:claim (equal pframe (dims-of-expr-value funval)))
        :s :bash)
  )

(defthm propagate-eval-app-reserrp-to-limit
    (implies (not (reserrp (eval-app funval argvals limit)))
             (not (zp limit)))
  :hints (("Goal"
           :expand ((eval-app funval argvals limit)))))

(defthm propagate-eval-app-reserrp-to-second-argument-limit
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (not (zp (- limit 2))))
  :instructions
  (:pro
   (:use (:instance propagate-eval-app-reserrp-to-second-argument))
   :pro (:forwardchain 1)
   (:use
    (:instance
     propagate-eval-app-reserrp-past-second-argument
     (funval
      (expr-value-with-nonempty-dims
       (dims-of-expr-value arg1)
       (pairwise-curry-binary-fn
        (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                  (dims-of-expr-value arg1))
        (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                  (dims-of-expr-value arg1)))))
     (limit (+ limit -1))
     (fun-frame arg1-frame)
     (param-dims
      (fun-value-param-dims
       (expr-value-with-nonempty-dims
        (dims-of-expr-value arg1)
        (pairwise-curry-binary-fn
         (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                   (dims-of-expr-value arg1))
         (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                   (dims-of-expr-value arg1))))))
     (arg2-frame (dims-of-expr-value arg2))
     (pframe (cadr (list-prefix-join (list arg1-frame arg2-frame))))))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   :s (:dv 1)
   (:= t)
   :nx (:= t)
   :nx (:= t)
   :up :s (:claim (acl2-numberp limit))
   :s (:= t)
   :up :s :top :pro
   (:use
    (:instance
     propagate-eval-app-reserrp-to-limit
     (funval
      (expr-value-with-nonempty-dims
       pframe
       (eval-app-list
        (lift-expr-value-to-frame
         (expr-value-with-nonempty-dims
          arg1-frame
          (pairwise-curry-binary-fn
           (repeat (nat-list-product arg1-frame)
                   funval)
           (lift-expr-value-to-frame arg1 arg1-frame arg1-frame)))
         arg1-frame pframe)
        (lift-expr-value-to-frame arg2 arg2-frame pframe)
        (+ -2 limit))))
     (argvals nil)
     (limit (+ limit -2))))
   :bash))

(defthm not-reserrp-expr-value-with-nonempty-dims
    (not (reserrp (expr-value-with-nonempty-dims frame cells))))

(acl2::make-flag flag-cells-at-depth cells-at-depth-in-expr-value
                 :flag-mapping ((cells-at-depth-in-expr-value      term)
                                (cells-at-depth-in-expr-value-list list)))

(defthm-flag-cells-at-depth
     (defthm not-reserrp-cells-at-depth-in-expr-value-when-well-formed
         (implies (and (or (expr-is-nested-vectors-of-base-values val)
                           (expr-is-nested-vectors-of-binary-primops val))
                       (expr-value-wfp val)
                       (equal depth (len (dims-of-expr-value val)))
                       )
                  (not (reserrp
                        (cells-at-depth-in-expr-value val depth))))
       :flag term)
     (defthm theorem-for-cells-at-depth-in-expr-value-list
       (implies (and (or (expr-is-nested-vectors-of-base-values-list vals)
                         (expr-is-nested-vectors-of-binary-primops-list vals))
                     (expr-value-list-wfp vals)
                     (dims-expr-list-bounded vals depth))
                (not (reserrp (cells-at-depth-in-expr-value-list vals depth))))
       :flag list)
  :hints (("Subgoal *1/13"
           :expand ((CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST VALS DEPTH)))
          ("Subgoal *1/12"
           :expand ((CELLS-AT-DEPTH-IN-EXPR-VALUE-LIST VALS (LEN (DIMS-OF-EXPR-VALUE (CAR VALS))))))
          ("Subgoal *1/8"
           :use ((:instance dims-expr-list-bounded-of-child))
           :expand ((CELLS-AT-DEPTH-IN-EXPR-VALUE VAL (LEN (DIMS-OF-EXPR-VALUE val))))
           :in-theory (disable dims-expr-list-bounded-of-child))
          ("Subgoal *1/1"
           :expand ((CELLS-AT-DEPTH-IN-EXPR-VALUE VAL 0))))
  )

(defthm dims-of-expr-value-with-nonempty-dims-1
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-is-nested-vectors-of-base-values arg1)
                  )
             (equal (dims-of-expr-value
                     (expr-value-with-nonempty-dims
                      (dims-of-expr-value arg1)
                      (pairwise-curry-binary-fn
                       (repeat (nat-list-product (dims-of-expr-value arg1))
                               funval)
                       (get-cells-from-expr-value arg1))))
                    (dims-of-expr-value arg1)))
  :hints (("goal"
           :use ((:instance dims-of-expr-value-with-nonempty-dims-explicit
                            (cells (pairwise-curry-binary-fn
                                    (repeat (nat-list-product (dims-of-expr-value arg1))
                                            funval)
                                    (get-cells-from-expr-value arg1)))
                            (frame (dims-of-expr-value arg1))))
           :in-theory (disable dims-of-expr-value-with-nonempty-dims-explicit))))

(defthm eval-app-when-funval-is-binary-op-fully
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (equal (eval-app funval (list arg1 arg2) limit)
                    (expr-value-with-nonempty-dims
                     pframe
                     (pairwise-curry-binary-x-fn
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg1-frame) pframe))
                                   (pairwise-curry-binary-fn
                                    (lift-expr-value-to-frame funval
                                                              nil
                                                              arg1-frame)
                                    (lift-expr-value-to-frame arg1
                                                              arg1-frame
                                                              arg1-frame)))
                      (lift-expr-value-to-frame arg2
                                                arg2-frame
                                                pframe)))))
  :instructions
  (:pro
   (:use
    (:instance
     eval-app-when-funval-is-binary-op
     (argvals (list arg1 arg2))
     (argval arg1)
     (arg-frame arg1-frame)
     (pframe (dims-of-expr-value arg1))
     (funcells (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                         (dims-of-expr-value arg1)))
     (argcells (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                         (dims-of-expr-value arg1)))
     (fun-frame (dims-of-expr-value funval))))
   :pro (:forwardchain 1)
   (:dv 1)
   := (:dv 2)
   :s :top
   (:use
    (:instance
     eval-app-when-funcells-is-curried-base-values
     (funval
      (expr-value-with-nonempty-dims
       (dims-of-expr-value arg1)
       (pairwise-curry-binary-fn
        (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                  (dims-of-expr-value arg1))
        (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                  (dims-of-expr-value arg1)))))
     (argvals (list arg2))
     (limit (+ -1 limit))
     (param-dims
      (fun-value-param-dims
       (expr-value-with-nonempty-dims
        (dims-of-expr-value arg1)
        (pairwise-curry-binary-fn
         (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                   (dims-of-expr-value arg1))
         (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                   (dims-of-expr-value arg1))))))
     (fun-frame
      (dims-of-expr-value
       (expr-value-with-nonempty-dims
        (dims-of-expr-value arg1)
        (pairwise-curry-binary-fn
         (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                   (dims-of-expr-value arg1))
         (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                   (dims-of-expr-value arg1))))))
     (argval arg2)
     (arg-frame
      (cadr
       (check-list-suffix
        (dims-of-expr-value arg2)
        (car
         (fun-value-param-dims
          (expr-value-with-nonempty-dims
           (dims-of-expr-value arg1)
           (pairwise-curry-binary-fn
            (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                      (dims-of-expr-value arg1))
            (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                      (dims-of-expr-value arg1)))))))))
     (arg-dims (dims-of-expr-value arg2))
     (funcells
      (lift-expr-value-to-frame
       (expr-value-with-nonempty-dims
        (dims-of-expr-value arg1)
        (pairwise-curry-binary-fn
         (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                   (dims-of-expr-value arg1))
         (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                   (dims-of-expr-value arg1))))
       (dims-of-expr-value
        (expr-value-with-nonempty-dims
         (dims-of-expr-value arg1)
         (pairwise-curry-binary-fn
          (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                    (dims-of-expr-value arg1))
          (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                    (dims-of-expr-value arg1)))))
       (cadr
        (list-prefix-join
         (list
          (dims-of-expr-value
           (expr-value-with-nonempty-dims
            (dims-of-expr-value arg1)
            (pairwise-curry-binary-fn
             (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                       (dims-of-expr-value arg1))
             (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                       (dims-of-expr-value arg1)))))
          (cadr
           (check-list-suffix
            (dims-of-expr-value arg2)
            (car
             (fun-value-param-dims
              (expr-value-with-nonempty-dims
               (dims-of-expr-value arg1)
               (pairwise-curry-binary-fn
                (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                          (dims-of-expr-value arg1))
                (lift-expr-value-to-frame
                 arg1 (dims-of-expr-value arg1)
                 (dims-of-expr-value arg1)))))))))))))
     (argcells
      (lift-expr-value-to-frame
       arg2
       (cadr
        (check-list-suffix
         (dims-of-expr-value arg2)
         (car
          (fun-value-param-dims
           (expr-value-with-nonempty-dims
            (dims-of-expr-value arg1)
            (pairwise-curry-binary-fn
             (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                       (dims-of-expr-value arg1))
             (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                       (dims-of-expr-value arg1))))))))
       (cadr
        (list-prefix-join
         (list
          (dims-of-expr-value
           (expr-value-with-nonempty-dims
            (dims-of-expr-value arg1)
            (pairwise-curry-binary-fn
             (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                       (dims-of-expr-value arg1))
             (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                       (dims-of-expr-value arg1)))))
          (cadr
           (check-list-suffix
            (dims-of-expr-value arg2)
            (car
             (fun-value-param-dims
              (expr-value-with-nonempty-dims
               (dims-of-expr-value arg1)
               (pairwise-curry-binary-fn
                (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                          (dims-of-expr-value arg1))
                (lift-expr-value-to-frame
                 arg1 (dims-of-expr-value arg1)
                 (dims-of-expr-value arg1)))))))))))))
     (pframe
      (cadr
       (list-prefix-join
        (list
         (dims-of-expr-value
          (expr-value-with-nonempty-dims
           (dims-of-expr-value arg1)
           (pairwise-curry-binary-fn
            (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                      (dims-of-expr-value arg1))
            (lift-expr-value-to-frame arg1 (dims-of-expr-value arg1)
                                      (dims-of-expr-value arg1)))))
         (cadr
          (check-list-suffix
           (dims-of-expr-value arg2)
           (car
            (fun-value-param-dims
             (expr-value-with-nonempty-dims
              (dims-of-expr-value arg1)
              (pairwise-curry-binary-fn
               (lift-expr-value-to-frame funval (dims-of-expr-value funval)
                                         (dims-of-expr-value arg1))
               (lift-expr-value-to-frame
                arg1 (dims-of-expr-value arg1)
                (dims-of-expr-value arg1))))))))))))))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   :s (:dv 1)
   (:= t)
   :nx (:= t)
   :nx (:= t)
   :top (:dv 1)
   (:dv 1)
   :s (:claim (acl2-numberp limit))
   :s :top :pro
   (:use (:instance propagate-eval-app-reserrp-to-second-argument))
   :pro (:forwardchain 1)
   (:demote 16)
   (:dv 1)
   (:dv 1)
   (:= t)
   :up :s :top :pro
   (:claim (equal (car (list-prefix-join (list arg1-frame arg2-frame)))
                  t))
   (:demote 12)
   (:dv 1)
   (:dv 1)
   (:rewrite list-prefix-join-cases-for-two-lists)
   :s :top
   (:casesplit (prefixp arg1-frame arg2-frame))
   (:dv 1)
   (:dv 2)
   :top :pro :bash (:dv 1)
   := :top
   (:use
    (:instance
     propagate-eval-app-reserrp-to-second-argument-limit
     (arg1-frame (dims-of-expr-value arg1))
     (arg2-frame (dims-of-expr-value arg2))
     (pframe (cadr (list-prefix-join (list (dims-of-expr-value arg1)
                                           (dims-of-expr-value arg2)))))))
   :pro (:forwardchain 1)
   (:dv 1)
   :x :top :bash (:dv 1)
   :s (:dv 1)
   (:= arg1-frame)
   :top :pro
   (:use
    (:instance
     propagate-eval-app-reserrp-to-second-argument-limit
     (arg1-frame (dims-of-expr-value arg1))
     (arg2-frame (dims-of-expr-value arg2))
     (pframe (cadr (list-prefix-join (list (dims-of-expr-value arg1)
                                           (dims-of-expr-value arg2)))))))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   :s (:dv 1)
   (:rewrite list-prefix-join-cases-for-two-lists)
   :nx (:dv 1)
   :up (:dv 2)
   (:dv 1)
   (:rewrite list-prefix-join-cases-for-two-lists)
   :up :up :up :up
   :up :s :up :s :top :pro :bash (:dv 1)
   := :x (:dv 1)
   (:= t)
   :up :s :top :bash (:change-goal nil t)
   (:in-theory (enable mv-nth))
   :s (:in-theory (enable mv-nth))
   :s (:in-theory (enable mv-nth))
   :s
   (:use (:instance list-prefix-join-cases-for-two-lists
                    (fun-frame (dims-of-expr-value arg1))
                    (arg-frame (dims-of-expr-value arg2))))
   :pro (:demote 1)
   (:dv 1)
   (:dv 1)
   :x :up :s (:dv 2)
   (:dv 2)
   (:= (dims-of-expr-value arg1))
   :up :top :pro :s (:dv 1)
   (:dv 2)
   (:dv 1)
   (:rewrite undo-expr-value-with-nonempty-dims-2)
   :top
   :bash :bash
   :bash :bash
   :bash :bash)
  )

(defthm repeat-each-singleton
    (equal (repeat-each n (list x))
           (repeat n x))
  :hints (("Goal"
           :in-theory (enable repeat-each))))

(defthm eval-app-when-funval-is-binary-op-fully-1
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (equal (eval-app funval (list arg1 arg2) limit)
                    (expr-value-with-nonempty-dims
                     pframe
                     (pairwise-curry-binary-x-fn
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg1-frame) pframe))
                                   (pairwise-curry-binary-fn
                                    (repeat-each
                                     (nat-list-product arg1-frame)
                                     (get-cells-from-expr-value funval))
                                    (get-cells-from-expr-value arg1))
                                   )
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg2-frame) pframe))
                                   (get-cells-from-expr-value arg2))
                      ))))
  :instructions
  (:pro
   (:dv 1)
   (:rewrite eval-app-when-funval-is-binary-op-fully)
   (:dv 2)
   (:dv 2)
   (:rewrite lift-expr-value-to-frame-when-frame-is-prefix-and-frame-of-val)
   :top
   :bash :bash
   :bash :bash
   :bash :bash)
  )


(defthm pairwise-curry-binary-fn-append
    (implies (equal (len xs1) (len ys1))
             (equal (pairwise-curry-binary-fn (append xs1 xs2)
                                              (append ys1 ys2))
                    (append (pairwise-curry-binary-fn xs1 ys1)
                            (pairwise-curry-binary-fn xs2 ys2)))))

(defthmd repeat-m*n-times
    (implies (and (natp m)
                  (posp n))
             (equal (repeat (* m n) x)
                    (append (repeat m x)
                            (repeat (* m (1- n)) x)))))

(defthm repeat-each-pairwise-curry-binary-fn
    (implies (natp m)
             (equal (repeat-each m
                                 (pairwise-curry-binary-fn
                                  (repeat (len ys) x)
                                  ys))
                    (pairwise-curry-binary-fn
                     (repeat (* m (len ys)) x)
                     (repeat-each m ys))))
  :instructions ((:in-theory (enable pairwise-curry-binary-fn repeat-each))
                 (:induct (repeat-each m ys))
                 (:change-goal nil t)
                 :bash :pro (:forwardchain 2)
                 (:dv 1)
                 (:dv 2)
                 :x (:dv 1)
                 (:= t)
                 :up :s :up :x (:dv 2)
                 (:dv 2)
                 (:dv 1)
                 (:dv 1)
                 :x (:dv 1)
                 (:= t)
                 :up :s :up :s (:dv 1)
                 (:= (len (cdr ys)))
                 :up :up :up := :up :nx (:dv 1)
                 (:rewrite repeat-m*n-times)
                 (:dv 2)
                 (:dv 1)
                 (:dv 2)
                 (:= (len (cdr ys)))
                 :up :up :up :nx :x :up
                 (:rewrite pairwise-curry-binary-fn-append)
                 :up :s (:generalize ((car ys) y))
                 (:claim (equal (car (repeat (len ys) x)) x))
                 :s (:in-theory (enable repeat))
                 (:drop 3 4)
                 (:drop 1)
                 (:= t)
                 (:= t)
                 (:= t))
  )



(defthm eval-app-when-funval-is-binary-op-fully-2
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (equal (eval-app funval (list arg1 arg2) limit)
                    (expr-value-with-nonempty-dims
                     pframe
                     (pairwise-curry-binary-x-fn
                      (pairwise-curry-binary-fn
                       (repeat-each (nat-list-product pframe)
                                    (get-cells-from-expr-value funval))
                       (repeat-each (nat-list-product
                                     (nthcdr (len arg1-frame) pframe))
                                    (get-cells-from-expr-value arg1)))
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg2-frame) pframe))
                                   (get-cells-from-expr-value arg2))
                      ))))
  :INSTRUCTIONS (:PRO (:DV 1)
                      (:REWRITE EVAL-APP-WHEN-FUNVAL-IS-BINARY-OP-FULLY-1)
                      (:CHANGE-GOAL NIL T)
                      :BASH :BASH :BASH (:DV 2)
                      (:DV 1)
                      (:DV 2)
                      (:DV 1)
                      (:DV 2)
                      :X :UP :UP :UP (:DV 2)
                      (:DV 1)
                      (:DV 1)
                      (:= (LEN (GET-CELLS-FROM-EXPR-VALUE ARG1)))
                      :UP (:REWRITE REPEAT-EACH-SINGLETON)
                      :UP :UP
                      (:REWRITE REPEAT-EACH-PAIRWISE-CURRY-BINARY-FN)
                      (:DV 1)
                      (:DV 1)
                      (:DV 2)
                      (:REWRITE LEN-GET-CELLS-FROM-EXPR-VALUE)
                      (:DV 1)
                      := :UP
                      :UP (:CLAIM (PREFIXP ARG1-FRAME PFRAME))
                      :TOP
                      (:USE (:INSTANCE NAT-LIST-PRODUCT-PREFIX (XS ARG1-FRAME)
                                       (YS PFRAME)))
                      :PRO (:FORWARDCHAIN 1)
                      (:DV 1)
                      (:DV 2)
                      (:DV 1)
                      (:DV 1)
                      (:DV 1)
                      (:= (NAT-LIST-PRODUCT PFRAME))
                      :TOP :BASH)
  )

(defun pairwise-binary-args-fn (funcells arg1cells arg2cells)
  (if (endp funcells)
      nil
      (cons (eval-int-binary-primop
             (primop-value-int-binary->op
              (expr-value-primop->val (car funcells)))
             (car arg1cells)
             (car arg2cells))
            (pairwise-binary-args-fn (cdr funcells)
                                     (cdr arg1cells)
                                     (cdr arg2cells)
                                     ))))

(defthm pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn
    (equal (pairwise-curry-binary-x-fn
            (pairwise-curry-binary-fn funcells arg1cells)
            arg2cells)
           (pairwise-binary-args-fn funcells arg1cells arg2cells))
  )

(defthm eval-app-when-funval-is-binary-op-fully-3
    (implies (and (expr-valuep funval)
                  (expr-value-case funval :primop)
                  (primop-value-case (expr-value-primop->val funval)
                                     :int-binary)
                  (expr-value-wfp arg1)
                  (expr-valuep arg1)
                  (expr-value-wfp arg2)
                  (expr-valuep arg2)
                  (expr-is-nested-vectors-of-base-values arg1)
                  (expr-is-nested-vectors-of-base-values arg2)
                  (equal arg1-frame (dims-of-expr-value arg1))
                  (equal arg2-frame (dims-of-expr-value arg2))
                  (equal (list-prefix-join (list arg1-frame arg2-frame))
                         (mv t pframe))
                  (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                  )
             (equal (eval-app funval (list arg1 arg2) limit)
                    (expr-value-with-nonempty-dims
                     pframe
                     (pairwise-binary-args-fn
                      (repeat-each (nat-list-product pframe)
                                   (get-cells-from-expr-value funval))
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg1-frame) pframe))
                                   (get-cells-from-expr-value arg1))
                      (repeat-each (nat-list-product
                                    (nthcdr (len arg2-frame) pframe))
                                   (get-cells-from-expr-value arg2))))))
  :hints (("Goal"
           :use ((:instance eval-app-when-funval-is-binary-op-fully-2))
           :in-theory '(pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn))))
