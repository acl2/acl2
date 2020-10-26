;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "translate-type")
(include-book "translate-constant")

(local (in-theory (enable paragraph-fix paragraph-p word-p)))

(define translate-uninterpreted-arguments ((args decl-list-p)
                                           (fixinfo smt-fixtype-info-p)
                                           (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  :measure (len args)
  (b* ((args (decl-list-fix args))
       ((unless (consp args)) nil)
       ((cons first rest) args)
       ((decl d) first)
       ((hint-pair h) d.type)
       ((unless (type-decl-p h.thm fixinfo))
        (er hard? 'translator=>translate-uninterpreted-arguments
            "Type theorem is not a type-decl-p: ~q0"
            h.thm))
       (translated-type (translate-type (car h.thm) (cadr h.thm)
                                        int-to-rat fixinfo)))
    (cons `(#\, #\Space ,translated-type)
          (translate-uninterpreted-arguments rest fixinfo int-to-rat))))

(define translate-uninterpreted-decl ((fn smt-function-p)
                                      (fixinfo smt-fixtype-info-p)
                                      (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  (b* ((fn (smt-function-fix fn))
       ((smt-function f) fn)
       (name f.name)
       (translated-formals
        (translate-uninterpreted-arguments f.formals fixinfo int-to-rat))
       ((if (> (len f.returns) 1))
        (er hard? 'SMT-translator=>translate-uninterpreted-decl "Multiple
              returns are not supported: ~q0" f.returns))
       (translated-returns
        (translate-uninterpreted-arguments f.returns fixinfo int-to-rat)))
    `(,(translate-symbol name) "= z3.Function("
      #\' ,name #\' ,translated-formals ,translated-returns
      ")" #\Newline)))

(define translate-uninterpreted-decl-lst ((fn-lst smt-function-list-p)
                                          (fixinfo smt-fixtype-info-p)
                                          (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  :measure (len fn-lst)
  (b* ((fn-lst (smt-function-list-fix fn-lst))
       ((unless (consp fn-lst)) nil)
       ((cons first rest) fn-lst)
       (first-decl
        (translate-uninterpreted-decl first fixinfo int-to-rat)))
    (cons first-decl
          (translate-uninterpreted-decl-lst rest fixinfo int-to-rat))))

