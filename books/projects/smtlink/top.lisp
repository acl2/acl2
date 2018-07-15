;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "config")

;; verified
(include-book "verified/basics")
(include-book "verified/computed-hints")
(include-book "verified/extractor")
(include-book "verified/Smtlink")
(include-book "verified/hint-interface")
(include-book "verified/hint-please")
(include-book "verified/type-hyp")
(include-book "verified/add-hypo-cp")
(include-book "verified/expand-cp")
(include-book "verified/type-extract-cp")
(include-book "verified/uninterpreted-fn-cp")

;; trusted
(include-book "trusted/prove")
(include-book "trusted/run")
(include-book "trusted/trusted-cp")
(include-book "trusted/write")

;; trusted/z3-py
(include-book "trusted/z3-py/header")
(include-book "trusted/z3-py/names")
(include-book "trusted/z3-py/translator")
(include-book "trusted/z3-py/magic-fix")

(in-theory (disable consp-when-member-equal-of-sym-nat-alistp
                    pseudo-term-list-of-cdar-of-ex-args->term-lst
                    pseudo-term-listp-of-cdr-of-ex-args->term-lst
                    symbolp-of-car-of-ex-args->term-lst
                    pseudo-termp-of-car-of-ex-args->term-lst
                    len-equal-of-formals-of-pseudo-lambdap-and-actuals-of-pseudo-termp
                    symbolp-of-caar-of-ex-args->term-lst
                    symbol-listp-of-formals-of-pseudo-lambdap
                    not-cddr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
                    consp-cdr-of-car-of-pseudo-term-list-fix-of-expand-args->term-lst
                    pseudo-term-listp-of-pseudo-lambdap-of-cdar-ex-args->term-lst
                    pseudo-termp-of-body-of-pseudo-lambdap
                    consp-of-cdr-of-pseudo-lambdap
                    consp-of-pseudo-lambdap
                    consp-of-cddr-of-pseudo-lambdap
                    not-stringp-of-cadr-of-pseudo-lambdap
                    integerp-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                    non-neg-of-cdr-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                    consp-of-assoc-equal-of-ex-args->fn-lvls-of-ex-args-p
                    not-symbolp-then-consp-of-car-of-fhg-args->term-lst
                    pseudo-term-listp-of-cdr-of-fhg-args->term-lst
                    pseudo-term-listp-of-cdar-of-fhg-args->term-lst
                    symbolp-of-caar-of-fhg-args->term-lst
                    len-equal-of-formals-of-pseudo-lambdap-and-actuals
                    lemma-8
                    lemma-10
                    symbol-string-alistp-is-true-listp))
