; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "monomorphize")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the ispace-argument machinery: the sequence MONO-IFUN-INSTANCE
; and MONO-CFUN-INSTANCE perform when they create an instance from a
; recorded request.
;
;   ivals    = (eval-iargs iargs denv)                ; evaluate arguments
;   ext-denv = (extend-ispace-denv params ivals denv) ; bind parameters
;   new-type = (type-partial-eval-dims type ext-denv) ; substitute
;
; EVAL-IARGS evaluates each ispace argument to ONE ispace value, and
; EXTEND-ISPACE-DENV binds each parameter to one value, of the matching
; sort.  So a shape parameter receives a whole shape, however many
; dimensions it has.

(defconst *empty-denv* (ispace-denv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A multi-dimensional shape argument is ONE ispace value, not one value
; per dimension.

(acl2::assert-equal
 (mv-list 2 (eval-iargs
             (list (ispace-shape
                    (shape-dims (list (dim-const 2) (dim-const 3)))))
             *empty-denv*))
 (list nil (list (ispace-value-shape (list 2 3)))))

; The one shape parameter is bound to the whole 2-by-3 shape.

(acl2::assert-equal
 (mv-list 2 (extend-ispace-denv (list (ispace-var-shape "s"))
                                (list (ispace-value-shape (list 2 3)))
                                *empty-denv*))
 (list nil (ispace-denv-add-ispace (ispace-var-shape "s")
                                   (ispace-value-shape (list 2 3))
                                   *empty-denv*)))

; So substituting the shape parameter yields the FULL two-dimensional
; shape.  (Before ispace arguments were evaluated per argument, the
; parameter was bound to the first dimension alone and this came out as
; the one-dimensional shape (dims 2).)

(acl2::assert-equal
 (b* (((mv & denv) (extend-ispace-denv
                    (list (ispace-var-shape "s"))
                    (list (ispace-value-shape (list 2 3)))
                    *empty-denv*)))
   (shape-partial-eval-dims (shape-var "s") denv))
 (shape-dims (list (dim-const 2) (dim-const 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The same thing end to end: an :IFUN with a shape parameter S, declared
; to return an array of shape S, applied to the shape 2-by-3.

(acl2::assert-equal
 (b* ((params (list (ispace-var-shape "s")))
      (decl-type (type-array (type-base (base-type-int))
                             (ispace-shape (shape-var "s"))))
      (iargs (list (ispace-shape
                    (shape-dims (list (dim-const 2) (dim-const 3))))))
      ((mv & ivals) (eval-iargs iargs *empty-denv*))
      ((mv & ext-denv) (extend-ispace-denv params ivals *empty-denv*)))
   (type-partial-eval-dims decl-type ext-denv))
 (type-array (type-base (base-type-int))
             (ispace-shape (shape-dims (list (dim-const 2) (dim-const 3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A compound dim argument is evaluated, not decomposed: (+ 2 3) is one
; value, 5.

(acl2::assert-equal
 (mv-list 2 (eval-iargs
             (list (ispace-dim (dim-add (list (dim-const 2) (dim-const 3)))))
             *empty-denv*))
 (list nil (list (ispace-value-dim 5))))

(acl2::assert-equal
 (b* (((mv & denv) (extend-ispace-denv (list (ispace-var-dim "n"))
                                       (list (ispace-value-dim 5))
                                       *empty-denv*)))
   (dim-partial-eval-dims (dim-var "n") denv))
 (dim-const 5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A shape with no dimensions is the empty shape, not the absence of an
; argument: the parameter is bound, to the empty list of dimensions.

(acl2::assert-equal
 (mv-list 2 (eval-iargs (list (ispace-shape (shape-dims nil))) *empty-denv*))
 (list nil (list (ispace-value-shape nil))))

(acl2::assert-equal
 (b* (((mv & denv) (extend-ispace-denv (list (ispace-var-shape "s"))
                                       (list (ispace-value-shape nil))
                                       *empty-denv*)))
   (shape-partial-eval-dims (shape-var "s") denv))
 (shape-dims nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Arity and sort are both checked.  Too many arguments, too few, and an
; argument of the wrong sort for its parameter are all rejected.

(acl2::assert-equal
 (b* (((mv err &) (extend-ispace-denv (list (ispace-var-shape "s"))
                               (list (ispace-value-shape (list 2))
                                     (ispace-value-dim 3))
                               *empty-denv*)))
   err)
 t)

(acl2::assert-equal
 (b* (((mv err &) (extend-ispace-denv (list (ispace-var-shape "s")
                                     (ispace-var-dim "n"))
                               (list (ispace-value-shape (list 2)))
                               *empty-denv*)))
   err)
 t)

; A :SHAPE value does not instantiate a :DIM parameter, nor conversely.

(acl2::assert-equal
 (b* (((mv err &) (extend-ispace-denv (list (ispace-var-dim "n"))
                               (list (ispace-value-shape (list 2 3)))
                               *empty-denv*)))
   err)
 t)

(acl2::assert-equal
 (b* (((mv err &) (extend-ispace-denv (list (ispace-var-shape "s"))
                               (list (ispace-value-dim 2))
                               *empty-denv*)))
   err)
 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dimension and shape variables are in separate namespaces, as they are
; everywhere else in the library: the same name bound at one sort does not
; affect a variable of the other sort.

(acl2::assert-equal
 (b* (((mv & denv) (extend-ispace-denv (list (ispace-var-dim "n"))
                                       (list (ispace-value-dim 7))
                                       *empty-denv*)))
   (list (dim-partial-eval-dims (dim-var "n") denv)
         (shape-partial-eval-dims (shape-var "n") denv)))
 (list (dim-const 7) (shape-var "n")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An ispace variable that is not bound is an error at a call site, and is
; left alone by substitution.

(acl2::assert-equal
 (mv-list 2 (eval-iargs (list (ispace-shape (shape-var "s"))) *empty-denv*))
 (list t nil))

(acl2::assert-equal
 (shape-partial-eval-dims (shape-var "s") *empty-denv*)
 (shape-var "s"))
