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

(defxdoc SMT-basics
  :parents (verified)
  :short "Basic functions and types in Smtlink.")

(defval *SMT-basics*
  :parents (SMT-basics)
  :short "Basic ACL2 functions supported in Smtlink."
  (append
   '(magic-fix)
   '(rationalp realp booleanp integerp symbolp)
   '(binary-+ binary-* unary-/ unary--
              equal <
              implies if not
              lambda)))

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
    (lambda            . ("lambda"           . 2))
    (implies           . ("_SMT_.implies"    . 2))
    ;; (hint-please       . ("_SMT_.hint_okay"  . 0))
    ;; This doesn't work right now because Z3's definition is different from ACL2
    ;; when using types as hypotheses. If X is rationalp in Z3, then it can not
    ;; be an integerp. We need to first grab a definition in Z3 that can fully
    ;; capture its ACL2 meaning.
    ;; (integerp      . ("_SMT_.integerp"   . 1))
    ;; (rationalp     . ("_SMT_.rationalp"  . 1))
    ;; (booleanp      . ("_SMT_.booleanp"   . 1))
    ))

(defval *SMT-types*
  :parents (SMT-basics)
  :short "ACL2 type functions and their corresponding Z3 type declarations."
  ;;(ACL2 type      .  SMT type)
  `((realp          . "_SMT_.RealSort()")
    (rationalp      . "_SMT_.RealSort()")
    (integerp       . "_SMT_.IntSort()")
    (booleanp       . "_SMT_.BoolSort()")
    (symbolp        . "Symbol_z3.z3Sym")))

(defval *SMT-uninterpreted-types*
  :parents (SMT-basics)
  :short "ACL2 type functions and their corresponding Z3 uninterpreted function
    type declarations."
  `((realp          . "_SMT_.RealSort()")
    (rationalp      . "_SMT_.RealSort()")
    (real/rationalp . "_SMT_.RealSort()")
    (integerp       . "_SMT_.IntSort()")
    (booleanp       . "_SMT_.BoolSort()")
    (symbolp        . "Symbol_z3.z3Sym")))

;; current tag . next computed-hint
(defval *SMT-architecture*
  '((process-hint          . add-hypo-cp)
    (add-hypo              . expand-cp)
    (expand                . type-extract-cp)
    (type-extract          . uninterpreted-fn-cp)
    (uninterpreted         . smt-trusted-cp)
    (uninterpreted-custom  . smt-trusted-cp-custom)))


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
                         ,(nat-to-dec-string nargs)
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

  (local (defun ualist-to-xdoc ()
           (declare (xargs :mode :program))
           (str::string-append-lst
            `("<p></p>
<table>
<tr><th>ACL2 type functions</th><th>Z3 uninterpreted function type declarations</th></tr>
"
              ,@(reverse (alist-to-xdoc-aux *SMT-uninterpreted-types* nil))
              "</table>"))))

  (make-event
   `(defxdoc SMT-uninterpreted-types
      :parents (SMT-basics)
      :short "SMT uninterpreted function types"

      :long ,(ualist-to-xdoc)))
  )
