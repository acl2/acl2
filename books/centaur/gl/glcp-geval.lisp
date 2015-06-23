

(in-package "GL")
(include-book "generic-geval")
(include-book "symbolic-arithmetic")
(include-book "shape-spec-defs")
(include-book "gl-mbe")


(defun gl-cp-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable gl-cp-hint (:type-prescription gl-cp-hint) (gl-cp-hint)))

(def-eval-g glcp-generic-geval
  (
   ;; used in shape specs
   logapp int-set-sign maybe-integer
          cons car cdr consp if not equal nth len iff
          shape-spec-slice-to-env
          ss-append-envs
          shape-spec-obj-in-range-iff
          shape-spec-obj-in-range
          shape-spec-env-slice
          shape-spec-iff-env-slice
          acl2::logcons$inline

          if gl-cp-hint shape-spec-obj-in-range return-last use-by-hint equal
      acl2::typespec-check implies iff not cons gl-aside gl-ignore gl-error gl-hide
      BINARY-*
      BINARY-+
      PKG-WITNESS
;   UNARY-/
      UNARY--
      COMPLEX-RATIONALP
;   BAD-ATOM<=
      ACL2-NUMBERP
      SYMBOL-PACKAGE-NAME
      INTERN-IN-PACKAGE-OF-SYMBOL
      CODE-CHAR
;   DENOMINATOR
      CDR
;   COMPLEX
      CAR
      CONSP
      SYMBOL-NAME
      CHAR-CODE
      IMAGPART
      SYMBOLP
      REALPART
;   NUMERATOR
      EQUAL
      STRINGP
      RATIONALP
      CONS
      INTEGERP
      CHARACTERP
      <
      COERCE
      booleanp
      logbitp
      binary-logand
      binary-logior
      acl2::binary-logxor
      acl2::binary-logeqv
      lognot
      ash
      integer-length
      floor
      mod
      truncate
      rem
      acl2::bool-fix$inline

      ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
      NOT IMPLIES
      EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
      PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
      ;; FORCE CASE-SPLIT
      ;; DOUBLE-REWRITE

      ;; used for shape specs
      acl2::logapp int-set-sign maybe-integer

      ;; force checks
      gl-force-check-fn
      binary-minus-for-gl))

(in-theory (disable glcp-generic-geval))




(defund glcp-generic-geval-alist (al env)
  (declare (xargs :guard (consp env)))
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al)
                    (glcp-generic-geval (cdar al)
                                        env))
              (glcp-generic-geval-alist (cdr al) env))
      (glcp-generic-geval-alist (cdr al) env))))
