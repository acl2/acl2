;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(defxdoc SMT-basics
  :parents (verified)
  :short "Basic functions and types in Smtlink.")

(define SMT-basics ()
  :parents (SMT-basics)
  :short "Basic ACL2 functions supported in Smtlink."
  (append
   '(rationalp booleanp integerp symbolp)
   '(binary-+ binary-* unary-/ unary-- equal < if not implies)))

(in-theory (disable (:executable-counterpart smt-basics)))

(defval *SMT-functions*
  :parents (SMT-functions)
  :short "ACL2 functions and their corresponding Z3 functions."
  ;;(ACL2 function     . (SMT function         Least # of arguments))
  `((binary-+          . ("_SMT_.plus"       . 1))
    (binary-*          . ("_SMT_.times"      . 1))
    (unary-/           . ("_SMT_.reciprocal" . 1))
    (unary--           . ("_SMT_.negate"     . 1))
    (equal             . ("_SMT_.equal"      . 2))
    (<                 . ("_SMT_.lt"         . 2))
    (if                . ("_SMT_.ifx"        . 3))
    (not               . ("_SMT_.notx"       . 1))
    (implies           . ("_SMT_.implies"    . 2))))

(define is-basic-function ((opr symbolp))
  (assoc-equal opr *SMT-functions*))

(defval *SMT-types*
  :parents (SMT-basics)
  :short "ACL2 type functions and their corresponding Z3 type declarations."
  ;;(ACL2 type      .  SMT type)
  `((rationalp      . "_SMT_.RealSort()")
    (integerp       . "_SMT_.IntSort()")
    (booleanp       . "_SMT_.BoolSort()")
    (symbolp        . "Symbol_z3.z3Sym")))

;; current tag . next computed-hint
(defval *SMT-architecture*
  '((process-hint              . add-hypo-cp)
    (add-hypo                  . expand-cp)
    (expand                    . reorder-hypotheses-cp)
    (reorder                   . type-judge-bottomup-cp)
    (type-judge-bottomup       . type-judge-topdown-cp)
    (type-judge-topdown        . term-replacement-cp)
    (term-replacement          . type-extract-cp)
    (type-extract              . smt-trusted-cp)
    (type-extract-custom       . smt-trusted-cp-custom)))

;;----------------------------------------------------------------

(encapsulate ()
  (local (defun falist-to-xdoc-aux (falist acc)
           ;; collects a reversed list of strings
           (b* (((when (atom falist)) acc)
                ((cons facl2 (cons fsmt nargs)) (car falist))
                (facl2-str (if (equal facl2 'hint-please)
                               (list (downcase-string (symbol-name facl2)))
                             `("@(see " ,(symbol-name facl2) ")")))
                (entry `("<tr><td>"
                         ,@facl2-str
                         "</td><td>"
                         ,fsmt
                         "</td><td>"
                         ,(natstr nargs)
                         "</td></tr> ")))
             (falist-to-xdoc-aux (cdr falist) (revappend entry acc)))))

  (local (defun falist-to-xdoc ()
           (declare (xargs :mode :program))
           (str::string-append-lst
            `("<p></p>
<table>
<tr><th>ACL2 function</th><th>Z3 function</th><th>Nargs</th></tr>
"
              ,@(reverse (falist-to-xdoc-aux *SMT-functions* nil))
              "</table>"))))

  (make-event
   `(defxdoc SMT-functions
      :parents (SMT-basics)
      :short "SMT functions"

      :long ,(falist-to-xdoc))))


(encapsulate ()
  (local (defun alist-to-xdoc-aux (alist acc)
           ;; collects a reversed list of strings
           (b* (((when (atom alist)) acc)
                ((cons facl2 fsmt) (car alist))
                (facl2-str (if (equal facl2 'realp)
                               (list (downcase-string (symbol-name facl2)))
                             `("@(see " ,(symbol-name facl2) ")")))
                (entry `("<tr><td>"
                         ,@facl2-str
                         "</td><td>"
                         ,fsmt
                         "</td></tr> ")))
             (alist-to-xdoc-aux (cdr alist) (revappend entry acc)))))

  (local (defun talist-to-xdoc ()
           (declare (xargs :mode :program))
           (str::string-append-lst
            `("<p></p>
<table>
<tr><th>ACL2 type functions</th><th>Z3 type declarations</th></tr>
"
              ,@(reverse (alist-to-xdoc-aux *SMT-types* nil))
              "</table>"))))

  (make-event
   `(defxdoc SMT-types
      :parents (SMT-basics)
      :short "SMT types"

      :long ,(talist-to-xdoc)))
  )
