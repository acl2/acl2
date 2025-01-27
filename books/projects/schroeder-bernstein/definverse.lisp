; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SBT")

(include-book "std/system/pseudo-event-formp" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "kestrel/utilities/er-soft-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definverse-process-inputs
  (function
   domain
   codomain)
  :returns (mv er-msg
               (function$ symbolp)
               (domain$ symbolp)
               (codomain$ symbolp))
  ;; TODO: check function is a function with one argument
  ;; TODO: check domain is a function with one argument
  ;; TODO: check codomain is a function with one argument
  (b* (((reterr) nil nil nil)
       ((unless (symbolp function))
        (reterr (msg "~x0 must be a symbol" function)))
       ((unless (symbolp domain))
        (reterr (msg "~x0 must be a symbol" domain)))
       ((unless (symbolp codomain))
        (reterr (msg "~x0 must be a symbol" codomain))))
    (retok function
           domain
           codomain)))

(define packn-pos-no-cl
  ((lst atom-listp)
   (witness symbolp))
  (acl2::packn-pos
   lst
   (if (equal (symbol-package-name witness) "COMMON-LISP")
       (pkg-witness "ACL2")
     witness)))

;; TODO: handle nil domain and codomain
(define definverse-gen
  ((function symbolp)
   (domain symbolp)
   (codomain symbolp))
  :returns (event acl2::pseudo-event-formp)
  (b* ((is-inverse
         (packn-pos-no-cl (list 'is- function '-inverse) function))
       (inverse
         (packn-pos-no-cl (list function '-inverse) function))
       (in-imagep
         (packn-pos-no-cl (list 'in- function '-imagep) function))
       (domain-of-inverse-when-in-imagep
         (packn-pos-no-cl (list domain '-of- inverse '-when- in-imagep)
                          function))
       (function-of-inverse-when-in-imagep
         (packn-pos-no-cl (list function '-of- inverse '-when- in-imagep)
                          function))
       (inverse-of-function-when-domain
         (packn-pos-no-cl (list inverse '-of- function '-when- domain)
                          function))
       (in-imagep-of-function-when-domain
         (packn-pos-no-cl (list in-imagep '-of- function '-when- domain)
                          function)))
    `(progn
       ;; Prep
       (defrule equal-of-f-and-f
         (implies (and (p x)
                       (p y))
                  (equal (equal (f x) (f y))
                         (equal x y)))
         :use injectivity-of-f)

       (defun ,is-inverse (inv x)
         (declare (xargs :guard t
                         :type-prescription (booleanp (,is-inverse inv x))))
         (and (,domain inv)
              (,codomain x)
              (equal (,function inv) x)))
       (defchoose ,inverse (inv) (x)
         (,is-inverse inv x))
       (defun ,in-imagep (x)
         (declare (xargs :guard t))
         (,is-inverse (,inverse x) x))
       (defthm ,domain-of-inverse-when-in-imagep
         (implies (,in-imagep x)
                  (,domain (,inverse x)))
         :hints (("Goal" :in-theory '(,in-imagep ,is-inverse))))
       (defthm ,function-of-inverse-when-in-imagep
         (implies (,in-imagep x)
                  (equal (,function (,inverse x))
                         x))
         :hints (("Goal" :in-theory '(,in-imagep ,is-inverse))))
       (defthm ,inverse-of-function-when-domain
         (implies (,domain x)
                  (equal (,inverse (,function x))
                         x))
         :hints (("Goal" ;; :in-theory '(,is-inverse)
                         ;; Open-world because we need injectivity and
                         ;;   codomain-of-function-when-domain.
                         :in-theory (enable ,is-inverse)
                         :use ((:instance ,inverse (inv x) (x (,function x)))))))
       (defthm ,in-imagep-of-function-when-domain
         (implies (,domain x)
                  (,in-imagep (,function x)))
         :hints (("Goal" ;; :in-theory '(,in-imagep
                         ;;              ,is-inverse
                         ;;              ,inverse-of-function-when-domain)
                         ;; Open-world because we need codomain-of-function-when-domain.
                         :in-theory (enable ,in-imagep
                                            ,is-inverse
                                            ,inverse-of-function-when-domain)
                         )))
       ))
  :guard-hints (("Goal" :in-theory (enable atom-listp))))

(define definverse-macro
  (function
   domain
   codomain
   (ctx symbolp)
   state)
  :returns (mv erp
               (event acl2::pseudo-event-formp)
               state)
  (b* (((mv er-msg function domain codomain)
        (definverse-process-inputs function domain codomain))
       ((when er-msg)
        (acl2::er-soft+ ctx t '(_) "~@0" er-msg))
       (event (definverse-gen function domain codomain)))
    (value event)))

(defmacro definverse
  (function
   &key
   domain
   codomain)
  (declare (xargs :guard t))
  `(make-event
     (definverse-macro
       ',function
       ',domain
       ',codomain
       'definverse
       state)))
