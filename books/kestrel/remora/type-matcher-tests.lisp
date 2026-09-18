; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-matcher")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of TYPE-VAR-MATCH, TYPE-MATCH, TYPE-LIST-MATCH,
; TYPE-MATCH-VARS, and TYPE-LIST-MATCH-VARS.
; Each test compares the results (success flag and substitutions)
; with the expected ones.
; The substitutions are, in order, for
; dimension variables, shape variables,
; atom-kind type variables, and array-kind type variables;
; TYPE-VAR-MATCH has only the two type substitutions.
; The pattern variables are
; i and j for dimensions, s for shapes,
; a and b for atom-kind types, and x and y for array-kind types;
; the types being matched use the variables
; k for dimensions, w for shapes,
; u for atom-kind types, and v for array-kind types.
; The variables bound by binders have the names of pattern variables,
; to test that they are treated as bound variables, not pattern variables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (array-of elem d1 d2 ...) is the array type
; with element type elem and dimensions d1 d2 ...

(defmacro array-of (elem &rest dims)
  `(make-type-array :elem ,elem
                    :ispace (ispace-shape (shape-dims (list ,@dims)))))

(defconst *int* (type-base (base-type-int)))
(defconst *bool* (type-base (base-type-bool)))

(defconst *atom-a* (type-var (type-var-atom "a")))
(defconst *atom-b* (type-var (type-var-atom "b")))
(defconst *array-x* (type-var (type-var-array "x")))
(defconst *array-y* (type-var (type-var-array "y")))
(defconst *atom-u* (type-var (type-var-atom "u")))
(defconst *array-v* (type-var (type-var-array "v")))

(defconst *scalar-int* (array-of *int*))
(defconst *scalar-bool* (array-of *bool*))
(defconst *int-vec3* (array-of *int* (dim-const 3)))
(defconst *int-fun* (make-type-fun :in *int* :out *int*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern variables (TYPE-VAR-MATCH).

; An unbound atom-kind pattern variable matches an atom-kind type,
; and is bound to it.

(assert-equal
 (mv-list 3 (type-var-match *int* (type-var-atom "a") nil nil))
 (list t (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 3 (type-var-match *int-fun* (type-var-atom "a") nil nil))
 (list t (omap::update "a" *int-fun* nil) nil))

(assert-equal
 (mv-list 3 (type-var-match *atom-u* (type-var-atom "a") nil nil))
 (list t (omap::update "a" *atom-u* nil) nil))

; An atom-kind pattern variable does not match an array-kind type,
; not even a scalar one.

(assert-equal
 (mv-list 3 (type-var-match *int-vec3* (type-var-atom "a") nil nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (type-var-match *scalar-int* (type-var-atom "a") nil nil))
 (list nil nil nil))

(assert-equal
 (mv-list 3 (type-var-match *array-v* (type-var-atom "a") nil nil))
 (list nil nil nil))

; A bound atom-kind pattern variable matches only the type bound to it.

(assert-equal
 (mv-list 3 (type-var-match *int*
                            (type-var-atom "a")
                            (omap::update "a" *int* nil)
                            nil))
 (list t (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 3 (type-var-match *bool*
                            (type-var-atom "a")
                            (omap::update "a" *int* nil)
                            nil))
 (list nil nil nil))

; An unbound array-kind pattern variable matches an array-kind type,
; and is bound to it.

(assert-equal
 (mv-list 3 (type-var-match *int-vec3* (type-var-array "x") nil nil))
 (list t nil (omap::update "x" *int-vec3* nil)))

(assert-equal
 (mv-list 3 (type-var-match *array-v* (type-var-array "x") nil nil))
 (list t nil (omap::update "x" *array-v* nil)))

; An unbound array-kind pattern variable also matches an atom-kind type,
; and is bound to the lifting of the type to a scalar array type.

(assert-equal
 (mv-list 3 (type-var-match *int* (type-var-array "x") nil nil))
 (list t nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 3 (type-var-match *int-fun* (type-var-array "x") nil nil))
 (list t nil (omap::update "x" (array-of *int-fun*) nil)))

(assert-equal
 (mv-list 3 (type-var-match *atom-u* (type-var-array "x") nil nil))
 (list t nil (omap::update "x" (array-of *atom-u*) nil)))

; A bound array-kind pattern variable matches only the type bound to it,
; where an atom-kind type is lifted before the comparison.

(assert-equal
 (mv-list 3 (type-var-match *scalar-int*
                            (type-var-array "x")
                            nil
                            (omap::update "x" *scalar-int* nil)))
 (list t nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 3 (type-var-match *int*
                            (type-var-array "x")
                            nil
                            (omap::update "x" *scalar-int* nil)))
 (list t nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 3 (type-var-match *int*
                            (type-var-array "x")
                            nil
                            (omap::update "x" *int-vec3* nil)))
 (list nil nil nil))

; The substitution for the other kind is unchanged.

(assert-equal
 (mv-list 3 (type-var-match *int*
                            (type-var-atom "a")
                            nil
                            (omap::update "x" *int-vec3* nil)))
 (list t (omap::update "a" *int* nil) (omap::update "x" *int-vec3* nil)))

(assert-equal
 (mv-list 3 (type-var-match *int-vec3*
                            (type-var-array "x")
                            (omap::update "a" *int* nil)
                            nil))
 (list t (omap::update "a" *int* nil) (omap::update "x" *int-vec3* nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern variables (TYPE-MATCH).

; A pattern variable is matched via TYPE-VAR-MATCH;
; the ispace substitutions are unchanged.

(assert-equal
 (mv-list 5 (type-match *int*
                        *atom-a*
                        (omap::update "i" (dim-const 3) nil)
                        (omap::update "s" (shape-var "w") nil)
                        nil
                        nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       (omap::update "s" (shape-var "w") nil)
       (omap::update "a" *int* nil)
       nil))

(assert-equal
 (mv-list 5 (type-match *int* *array-x* nil nil nil nil))
 (list t nil nil nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 5 (type-match *int-vec3* *atom-a* nil nil nil nil))
 (list nil nil nil nil nil))

; The initial substitutions constrain the match.

(assert-equal
 (mv-list 5 (type-match *bool*
                        *atom-a*
                        nil
                        nil
                        (omap::update "a" *int* nil)
                        nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Base types.

; A pattern base type matches only the same base type.

(assert-equal
 (mv-list 5 (type-match *int* *int* nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match *bool* *int* nil nil nil nil))
 (list nil nil nil nil nil))

; Variables in the type being matched are not pattern variables:
; a variable type does not match a base type pattern.

(assert-equal
 (mv-list 5 (type-match *atom-u* *int* nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Array and bracket types.

; The element type and the ispace are matched,
; the latter via the ispace matcher.

(assert-equal
 (mv-list 5 (type-match *int-vec3*
                        (array-of *atom-a* (dim-var "i"))
                        nil nil nil nil))
 (list t
       (omap::update "i" (dim-const 3) nil)
       nil
       (omap::update "a" *int* nil)
       nil))

(assert-equal
 (mv-list 5 (type-match (array-of *int* (dim-var "k"))
                        (array-of *atom-a* (dim-var "i"))
                        nil nil nil nil))
 (list t
       (omap::update "i" (dim-var "k") nil)
       nil
       (omap::update "a" *int* nil)
       nil))

(assert-equal
 (mv-list 5 (type-match (make-type-array
                         :elem *int*
                         :ispace (ispace-shape
                                  (shape-append (list (shape-dims
                                                       (list (dim-const 2)))
                                                      (shape-var "w")))))
                        (make-type-array
                         :elem *atom-a*
                         :ispace (ispace-shape (shape-var "s")))
                        nil nil nil nil))
 (list t
       nil
       (omap::update "s"
                     (shape-append (list (shape-dims (list (dim-const 2)))
                                         (shape-var "w")))
                     nil)
       (omap::update "a" *int* nil)
       nil))

; The dimensions must match.

(assert-equal
 (mv-list 5 (type-match (array-of *int* (dim-const 3) (dim-const 4))
                        (array-of *atom-a* (dim-var "i"))
                        nil nil nil nil))
 (list nil nil nil nil nil))

; A pattern array type matches only an array type:
; the matching is syntactical, so it does not match an atom type,
; even though the latter stands for a scalar array type.

(assert-equal
 (mv-list 5 (type-match *int* (array-of *atom-a*) nil nil nil nil))
 (list nil nil nil nil nil))

; Bracket types are matched analogously, with lists of ispaces.

(assert-equal
 (mv-list 5 (type-match (make-type-bracket
                         :elem *int*
                         :ispaces (list (ispace-dim (dim-const 2))
                                        (ispace-shape
                                         (shape-dims (list (dim-const 3))))))
                        (make-type-bracket
                         :elem *atom-a*
                         :ispaces (list (ispace-dim (dim-var "i"))
                                        (ispace-shape
                                         (shape-dims (list (dim-const 3))))))
                        nil nil nil nil))
 (list t
       (omap::update "i" (dim-const 2) nil)
       nil
       (omap::update "a" *int* nil)
       nil))

; Array and bracket types are distinct.

(assert-equal
 (mv-list 5 (type-match *int-vec3*
                        (make-type-bracket
                         :elem *atom-a*
                         :ispaces (list (ispace-shape
                                         (shape-dims (list (dim-const 3))))))
                        nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Function types.

; The input and output types are matched, threading the substitutions.

(assert-equal
 (mv-list 5 (type-match (make-type-fun :in *int-vec3* :out *bool*)
                        (make-type-fun :in *array-x* :out *array-y*)
                        nil nil nil nil))
 (list t
       nil
       nil
       nil
       (omap::update "x" *int-vec3*
                     (omap::update "y" *scalar-bool* nil))))

; A repeated pattern variable must match equal types,
; modulo the lifting of atom types to scalar array types.

(assert-equal
 (mv-list 5 (type-match (make-type-fun :in *int* :out *scalar-int*)
                        (make-type-fun :in *array-x* :out *array-x*)
                        nil nil nil nil))
 (list t nil nil nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 5 (type-match (make-type-fun :in *int* :out *bool*)
                        (make-type-fun :in *array-x* :out *array-x*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Unary and n-ary function types are distinct.

(assert-equal
 (mv-list 5 (type-match (make-type-funn :in (list *int*) :out *bool*)
                        (make-type-fun :in *array-x* :out *array-y*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

; The input types of n-ary function types are matched element-wise.

(assert-equal
 (mv-list 5 (type-match (make-type-funn :in (list *int* *int-vec3*)
                                        :out *bool*)
                        (make-type-funn :in (list *array-x* *array-y*)
                                        :out *atom-a*)
                        nil nil nil nil))
 (list t
       nil
       nil
       (omap::update "a" *bool* nil)
       (omap::update "x" *scalar-int*
                     (omap::update "y" *int-vec3* nil))))

(assert-equal
 (mv-list 5 (type-match (make-type-funn :in (list *int*) :out *bool*)
                        (make-type-funn :in (list *array-x* *array-y*)
                                        :out *atom-a*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Universal types.

; The bound variable of the pattern is not a pattern variable:
; it matches only the same variable, bound by the same binder,
; and it does not appear in the resulting substitutions.

(assert-equal
 (mv-list 5 (type-match (make-type-forall :param (type-var-atom "a")
                                          :body *atom-a*)
                        (make-type-forall :param (type-var-atom "a")
                                          :body *atom-a*)
                        nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match (make-type-forall :param (type-var-atom "a")
                                          :body *int*)
                        (make-type-forall :param (type-var-atom "a")
                                          :body *atom-a*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

; The binders must be the same.

(assert-equal
 (mv-list 5 (type-match (make-type-forall :param (type-var-atom "b")
                                          :body *atom-b*)
                        (make-type-forall :param (type-var-atom "a")
                                          :body *atom-a*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Free pattern variables in the body are matched as usual.

(assert-equal
 (mv-list 5 (type-match (make-type-forall
                         :param (type-var-atom "a")
                         :body (make-type-fun :in *atom-a* :out *int-vec3*))
                        (make-type-forall
                         :param (type-var-atom "a")
                         :body (make-type-fun :in *atom-a* :out *array-x*))
                        nil nil nil nil))
 (list t nil nil nil (omap::update "x" *int-vec3* nil)))

; A binder shadows a pattern variable with the same name:
; the binding of the pattern variable, made before the binder,
; is not consulted inside the binder, and is restored after the binder.

(assert-equal
 (mv-list 5 (type-match (make-type-fun
                         :in *int*
                         :out (make-type-forall :param (type-var-atom "a")
                                                :body *atom-a*))
                        (make-type-fun
                         :in *atom-a*
                         :out (make-type-forall :param (type-var-atom "a")
                                                :body *atom-a*))
                        nil nil nil nil))
 (list t nil nil (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 5 (type-match (make-type-fun
                         :in *int*
                         :out (make-type-forall :param (type-var-atom "a")
                                                :body *int*))
                        (make-type-fun
                         :in *atom-a*
                         :out (make-type-forall :param (type-var-atom "a")
                                                :body *atom-a*))
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Capture is not checked:
; matching (Forall (&a) (-> &a &a)) to the pattern (Forall (&a) (-> &a &b))
; binds &b to &a, which is bound in the type.

(assert-equal
 (mv-list 5 (type-match (make-type-forall
                         :param (type-var-atom "a")
                         :body (make-type-fun :in *atom-a* :out *atom-a*))
                        (make-type-forall
                         :param (type-var-atom "a")
                         :body (make-type-fun :in *atom-a* :out *atom-b*))
                        nil nil nil nil))
 (list t nil nil (omap::update "b" *atom-a* nil) nil))

; The parameters of n-ary universal types must be the same, in the same order.

(assert-equal
 (mv-list 5 (type-match (make-type-foralln
                         :params (list (type-var-atom "a") (type-var-array "x"))
                         :body (make-type-fun :in *atom-a* :out *array-x*))
                        (make-type-foralln
                         :params (list (type-var-atom "a") (type-var-array "x"))
                         :body (make-type-fun :in *atom-a* :out *array-x*))
                        nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match (make-type-foralln
                         :params (list (type-var-array "x") (type-var-atom "a"))
                         :body (make-type-fun :in *atom-a* :out *array-x*))
                        (make-type-foralln
                         :params (list (type-var-atom "a") (type-var-array "x"))
                         :body (make-type-fun :in *atom-a* :out *array-x*))
                        nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Product and sum types.

; The bound ispace variable of the pattern is not a pattern variable.

(assert-equal
 (mv-list 5 (type-match (make-type-pi :param (ispace-var-dim "n")
                                      :body (array-of *int* (dim-var "n")))
                        (make-type-pi :param (ispace-var-dim "n")
                                      :body (array-of *int* (dim-var "n")))
                        nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match (make-type-pi :param (ispace-var-dim "n")
                                      :body *int-vec3*)
                        (make-type-pi :param (ispace-var-dim "n")
                                      :body (array-of *int* (dim-var "n")))
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Free pattern variables in the body are matched as usual.

(assert-equal
 (mv-list 5 (type-match (make-type-pi
                         :param (ispace-var-dim "n")
                         :body (array-of *int* (dim-var "n") (dim-const 4)))
                        (make-type-pi
                         :param (ispace-var-dim "n")
                         :body (array-of *atom-a* (dim-var "n") (dim-var "i")))
                        nil nil nil nil))
 (list t
       (omap::update "i" (dim-const 4) nil)
       nil
       (omap::update "a" *int* nil)
       nil))

; A binder shadows a pattern variable with the same name.

(assert-equal
 (mv-list 5 (type-match (make-type-fun
                         :in *int-vec3*
                         :out (make-type-pi
                               :param (ispace-var-dim "i")
                               :body (array-of *int* (dim-var "i"))))
                        (make-type-fun
                         :in (array-of *int* (dim-var "i"))
                         :out (make-type-pi
                               :param (ispace-var-dim "i")
                               :body (array-of *int* (dim-var "i"))))
                        nil nil nil nil))
 (list t (omap::update "i" (dim-const 3) nil) nil nil nil))

(assert-equal
 (mv-list 5 (type-match (make-type-fun
                         :in *int-vec3*
                         :out (make-type-pi
                               :param (ispace-var-dim "i")
                               :body *int-vec3*))
                        (make-type-fun
                         :in (array-of *int* (dim-var "i"))
                         :out (make-type-pi
                               :param (ispace-var-dim "i")
                               :body (array-of *int* (dim-var "i"))))
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Bound shape variables are treated like bound dimension variables.

(assert-equal
 (mv-list 5 (type-match (make-type-sigma
                         :param (ispace-var-shape "s")
                         :body (make-type-array
                                :elem *int*
                                :ispace (ispace-shape (shape-var "s"))))
                        (make-type-sigma
                         :param (ispace-var-shape "s")
                         :body (make-type-array
                                :elem *int*
                                :ispace (ispace-shape (shape-var "s"))))
                        nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match (make-type-sigma
                         :param (ispace-var-shape "s")
                         :body *int-vec3*)
                        (make-type-sigma
                         :param (ispace-var-shape "s")
                         :body (make-type-array
                                :elem *int*
                                :ispace (ispace-shape (shape-var "s"))))
                        nil nil nil nil))
 (list nil nil nil nil nil))

; Product and sum types are distinct.

(assert-equal
 (mv-list 5 (type-match (make-type-pi :param (ispace-var-dim "n")
                                      :body *int*)
                        (make-type-sigma :param (ispace-var-dim "n")
                                         :body *int*)
                        nil nil nil nil))
 (list nil nil nil nil nil))

; The parameters of n-ary product types must be the same, in the same order.

(defconst *n++w*
  (ispace-shape (shape-append (list (shape-dims (list (dim-var "n")))
                                    (shape-var "w")))))

(assert-equal
 (mv-list 5 (type-match (make-type-pin
                         :params (list (ispace-var-dim "n")
                                       (ispace-var-shape "w"))
                         :body (make-type-array :elem *int* :ispace *n++w*))
                        (make-type-pin
                         :params (list (ispace-var-dim "n")
                                       (ispace-var-shape "w"))
                         :body (make-type-array :elem *atom-a* :ispace *n++w*))
                        nil nil nil nil))
 (list t nil nil (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 5 (type-match (make-type-pin
                         :params (list (ispace-var-shape "w")
                                       (ispace-var-dim "n"))
                         :body (make-type-array :elem *int* :ispace *n++w*))
                        (make-type-pin
                         :params (list (ispace-var-dim "n")
                                       (ispace-var-shape "w"))
                         :body (make-type-array :elem *atom-a* :ispace *n++w*))
                        nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists of types.

; Empty lists match, and the lists must have the same length.

(assert-equal
 (mv-list 5 (type-list-match nil nil nil nil nil nil))
 (list t nil nil nil nil))

(assert-equal
 (mv-list 5 (type-list-match (list *int*) nil nil nil nil nil))
 (list nil nil nil nil nil))

(assert-equal
 (mv-list 5 (type-list-match nil (list *atom-a*) nil nil nil nil))
 (list nil nil nil nil nil))

; The substitutions are threaded through the elements.

(assert-equal
 (mv-list 5 (type-list-match (list *int* *scalar-int*)
                             (list *array-x* *array-x*)
                             nil nil nil nil))
 (list t nil nil nil (omap::update "x" *scalar-int* nil)))

(assert-equal
 (mv-list 5 (type-list-match (list *int* *bool*)
                             (list *atom-a* *atom-a*)
                             nil nil nil nil))
 (list nil nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matching with respect to given pattern variables
; (TYPE-MATCH-VARS and TYPE-LIST-MATCH-VARS).

; Only the given variables are pattern variables;
; the other free variables of the pattern are rigid,
; i.e. they match only themselves,
; and they do not appear in the resulting substitutions.

(assert-equal
 (mv-list 5 (type-match-vars (make-type-fun :in *int* :out *atom-u*)
                             (make-type-fun :in *atom-a* :out *atom-u*)
                             nil
                             (set::insert (type-var-atom "a") nil)))
 (list t nil nil (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 5 (type-match-vars (make-type-fun :in *int* :out *bool*)
                             (make-type-fun :in *atom-a* :out *atom-u*)
                             nil
                             (set::insert (type-var-atom "a") nil)))
 (list nil nil nil nil nil))

; A variable that TYPE-MATCH would treat as a pattern variable
; is rigid if it is not among the given ones.

(assert-equal
 (mv-list 5 (type-match-vars *int* *atom-a* nil nil))
 (list nil nil nil nil nil))

(assert-equal
 (mv-list 5 (type-match-vars *atom-a* *atom-a* nil nil))
 (list t nil nil nil nil))

; A rigid array-kind variable does not match an atom-kind type.

(assert-equal
 (mv-list 5 (type-match-vars *int* *array-v* nil nil))
 (list nil nil nil nil nil))

; Rigid ispace variables.

(assert-equal
 (mv-list 5 (type-match-vars (array-of *int* (dim-const 3) (dim-var "k"))
                             (array-of *atom-a* (dim-var "i") (dim-var "k"))
                             (set::insert (ispace-var-dim "i") nil)
                             (set::insert (type-var-atom "a") nil)))
 (list t
       (omap::update "i" (dim-const 3) nil)
       nil
       (omap::update "a" *int* nil)
       nil))

(assert-equal
 (mv-list 5 (type-match-vars (array-of *int* (dim-const 3) (dim-const 4))
                             (array-of *atom-a* (dim-var "i") (dim-var "k"))
                             (set::insert (ispace-var-dim "i") nil)
                             (set::insert (type-var-atom "a") nil)))
 (list nil nil nil nil nil))

; A pattern variable that does not occur free in the pattern
; is not bound in the resulting substitutions,
; including when it is shadowed by a binder.

(assert-equal
 (mv-list 5 (type-match-vars *int*
                             *atom-a*
                             (set::insert (ispace-var-dim "i") nil)
                             (set::insert (type-var-atom "a")
                                          (set::insert (type-var-array "x")
                                                       nil))))
 (list t nil nil (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 5 (type-match-vars (make-type-forall :param (type-var-atom "a")
                                               :body *atom-a*)
                             (make-type-forall :param (type-var-atom "a")
                                               :body *atom-a*)
                             nil
                             (set::insert (type-var-atom "a") nil)))
 (list t nil nil nil nil))

; Lists: the substitutions are threaded through the elements.

(assert-equal
 (mv-list 5 (type-list-match-vars (list *int-vec3*
                                        (array-of *bool* (dim-const 3)))
                                  (list (array-of *atom-a* (dim-var "i"))
                                        (array-of *atom-b* (dim-var "i")))
                                  (set::insert (ispace-var-dim "i") nil)
                                  (set::insert (type-var-atom "a")
                                               (set::insert (type-var-atom "b")
                                                            nil))))
 (list t
       (omap::update "i" (dim-const 3) nil)
       nil
       (omap::update "a" *int* (omap::update "b" *bool* nil))
       nil))

(assert-equal
 (mv-list 5 (type-list-match-vars (list *int-vec3*
                                        (array-of *bool* (dim-const 4)))
                                  (list (array-of *atom-a* (dim-var "i"))
                                        (array-of *atom-b* (dim-var "i")))
                                  (set::insert (ispace-var-dim "i") nil)
                                  (set::insert (type-var-atom "a")
                                               (set::insert (type-var-atom "b")
                                                            nil))))
 (list nil nil nil nil nil))

; Lists: the rigid variables are the free variables of all the patterns.

(assert-equal
 (mv-list 5 (type-list-match-vars (list *int* *atom-u*)
                                  (list *atom-a* *atom-u*)
                                  nil
                                  (set::insert (type-var-atom "a") nil)))
 (list t nil nil (omap::update "a" *int* nil) nil))

(assert-equal
 (mv-list 5 (type-list-match-vars (list *int* *bool*)
                                  (list *atom-a* *atom-u*)
                                  nil
                                  (set::insert (type-var-atom "a") nil)))
 (list nil nil nil nil nil))
