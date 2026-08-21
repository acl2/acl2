; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "struct-type-split-proofs0")

(include-book "variables-in-computation-states")

(include-book "kestrel/c/language/dynamic-semantics" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define c::compustate-has-static-var-with-type-p ((var c::identp)
                                                  (type c::typep)
                                                  (compst c::compustatep))
  :returns (yes/no booleanp)
  (and (c::compustate-has-var-with-type-p var type compst)
       (equal (c::objdesign-kind (c::objdesign-of-var var compst)) :static))
  :guard-hints (("Goal" :in-theory (enable c::compustate-has-var-with-type-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains work in progress towards
; some general approach to generate proofs for the STS transformation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; struct s {
;;   unsigned int a;
;;   unsigned int b;
;; };

;; struct s gso;

;; unsigned int f(unsigned int x) {
;;   return x + gso.a + gso.b;
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; struct s {
;;   unsigned int a;
;; };

;; struct s2 {
;;   unsigned int b;
;; };

;; struct s gso;

;; struct s2 gso_0;

;; unsigned int f(unsigned int x) {
;;   return x + gso.a + gso_0.b;
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; old and new struct values

(define struct-value-oldp ((sval c::valuep))
  :returns (yes/no booleanp)
  (b* (((unless (c::value-case sval :struct)) nil)
       ((unless (equal (c::value-struct->tag sval) (c::ident "s"))) nil)
       (memvals (c::value-struct->members sval))
       ((unless (equal (len memvals) 2)) nil)
       (amemval (nth 0 memvals))
       (bmemval (nth 1 memvals))
       ((unless (equal (c::member-value->name amemval) (c::ident "a"))) nil)
       ((unless (equal (c::member-value->name bmemval) (c::ident "b"))) nil)
       (aval (c::member-value->value amemval))
       (bval (c::member-value->value bmemval))
       ((unless (c::value-case aval :uint)) nil)
       ((unless (c::value-case bval :uint)) nil)
       ((unless (not (c::value-struct->flexiblep sval))) nil))
    t))

(define struct-value-newlp ((sval c::valuep))
  :returns (yes/no booleanp)
  (b* (((unless (c::value-case sval :struct)) nil)
       ((unless (equal (c::value-struct->tag sval) (c::ident "s"))) nil)
       (memvals (c::value-struct->members sval))
       ((unless (equal (len memvals) 1)) nil)
       (amemval (nth 0 memvals))
       ((unless (equal (c::member-value->name amemval) (c::ident "a"))) nil)
       (aval (c::member-value->value amemval))
       ((unless (c::value-case aval :uint)) nil)
       ((unless (not (c::value-struct->flexiblep sval))) nil))
    t))

(define struct-value-newrp ((sval c::valuep))
  :returns (yes/no booleanp)
  (b* (((unless (c::value-case sval :struct)) nil)
       ((unless (equal (c::value-struct->tag sval) (c::ident "s2"))) nil)
       (memvals (c::value-struct->members sval))
       ((unless (equal (len memvals) 1)) nil)
       (bmemval (nth 0 memvals))
       ((unless (equal (c::member-value->name bmemval) (c::ident "b"))) nil)
       (bval (c::member-value->value bmemval))
       ((unless (c::value-case bval :uint)) nil)
       ((unless (not (c::value-struct->flexiblep sval))) nil))
    t))

(define struct-value-old-a ((sval c::valuep))
  :guard (struct-value-oldp sval)
  :returns (aval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "a") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-oldp
                                           c::value-struct-read
                                           c::value-struct-read-aux)))
  ///
  (defret value-kind-of-struct-value-old-a
    (equal (c::value-kind aval) :uint)
    :hyp (struct-value-oldp sval)
    :hints (("Goal" :in-theory (enable struct-value-oldp
                                       c::value-struct-read
                                       c::value-struct-read-aux)))))

(define struct-value-old-b ((sval c::valuep))
  :guard (struct-value-oldp sval)
  :returns (bval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "b") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-oldp
                                           c::value-struct-read
                                           c::value-struct-read-aux
                                           nth)))
  ///
  (defret value-kind-of-struct-value-old-b
    (equal (c::value-kind bval) :uint)
    :hyp (struct-value-oldp sval)
    :hints (("Goal" :in-theory (enable struct-value-oldp
                                       c::value-struct-read
                                       c::value-struct-read-aux
                                       nth)))))

(define struct-value-newl-a ((sval c::valuep))
  :guard (struct-value-newlp sval)
  :returns (aval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "a") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-newlp
                                           c::value-struct-read
                                           c::value-struct-read-aux)))
  ///
  (defret value-kind-of-struct-value-newl-a
    (equal (c::value-kind aval) :uint)
    :hyp (struct-value-newlp sval)
    :hints (("Goal" :in-theory (enable struct-value-newlp
                                       c::value-struct-read
                                       c::value-struct-read-aux)))))

(define struct-value-newr-b ((sval c::valuep))
  :guard (struct-value-newrp sval)
  :returns (bval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "b") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-newrp
                                           c::value-struct-read
                                           c::value-struct-read-aux)))
  ///
  (defret value-kind-of-struct-value-newr-b
    (equal (c::value-kind bval) :uint)
    :hyp (struct-value-newrp sval)
    :hints (("Goal" :in-theory (enable struct-value-newrp
                                       c::value-struct-read
                                       c::value-struct-read-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; equivalence of computation states

(define struct-value-equivp ((old-val c::valuep)
                             (newl-val c::valuep)
                             (newr-val c::valuep))
  :returns (yes/no booleanp)
  (and (struct-value-oldp old-val)
       (struct-value-newlp newl-val)
       (struct-value-newrp newr-val)
       (equal (struct-value-old-a old-val)
              (struct-value-newl-a newl-val))
       (equal (struct-value-old-b old-val)
              (struct-value-newr-b newr-val))))

(define static-equivp ((old-static c::scopep)
                       (new-static c::scopep))
  :returns (yes/no booleanp)
  (b* (((when (omap::emptyp (c::scope-fix old-static)))
        (omap::emptyp (c::scope-fix new-static)))
       ((mv var old-val) (omap::head old-static)))
    (if (equal var (c::ident "gso"))
        (b* ((newl-var (c::ident "gso"))
             (newr-var (c::ident "gso_0"))
             (newl-var+val (omap::assoc newl-var (c::scope-fix new-static)))
             (newr-var+val (omap::assoc newr-var (c::scope-fix new-static)))
             ((unless (and newl-var+val newr-var+val)) nil)
             (newl-val (cdr newl-var+val))
             (newr-val (cdr newr-var+val))
             ((unless (struct-value-equivp old-val newl-val newr-val)) nil)
             (old-static (omap::tail old-static))
             (new-static (omap::delete newl-var (c::scope-fix new-static)))
             (new-static (omap::delete newr-val (c::scope-fix new-static))))
          (static-equivp old-static new-static))
      (b* ((new-var+val (omap::assoc var (c::scope-fix new-static)))
           ((unless new-var+val) nil)
           (new-val (cdr new-var+val))
           ((unless (equal old-val new-val)) nil)
           (old-static (omap::tail old-static))
           (new-static (omap::delete var (c::scope-fix new-static))))
        (static-equivp old-static new-static)))))

(define compustate-equivp ((old-compst c::compustatep)
                           (new-compst c::compustatep))
  :returns (yes/no booleanp)
  (and (static-equivp (c::compustate->static old-compst)
                      (c::compustate->static new-compst))
       (equal (c::compustate->frames old-compst)
              (c::compustate->frames new-compst))
       (equal (c::compustate->heap old-compst)
              (c::compustate->heap new-compst))
       (c::compustate-has-static-var-with-type-p (c::ident "gso")
                                                 (c::type-struct
                                                  (c::ident "s"))
                                                 old-compst)
       (c::compustate-has-static-var-with-type-p (c::ident "gso")
                                                 (c::type-struct
                                                  (c::ident "s"))
                                                 new-compst)
       (c::compustate-has-static-var-with-type-p (c::ident "gso_0")
                                                 (c::type-struct
                                                  (c::ident "s2"))
                                                 new-compst)))

; i.e. the computation states are the same except that
; there is a global struct object that is split into two

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
