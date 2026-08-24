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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; these should be just consequences of the values having those struct types,
; given the known definitions of the struct types

;;;;;;;;;;;;;;;;;;;;

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
    t)

  ///

  (defruled value-kind-when-struct-value-oldp
    (implies (struct-value-oldp sval)
             (equal (c::value-kind sval) :struct))))

;;;;;;;;;;;;;;;;;;;;

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
    t)

  ///

  (defruled value-kind-when-struct-value-newlp
    (implies (struct-value-newlp sval)
             (equal (c::value-kind sval) :struct))))

;;;;;;;;;;;;;;;;;;;;

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
    t)

  ///

  (defruled value-kind-when-struct-value-newrp
    (implies (struct-value-newrp sval)
             (equal (c::value-kind sval) :struct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; accessors with unconditional return types

;;;;;;;;;;;;;;;;;;;;

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
                                       c::value-struct-read-aux))))

  (defruled value-struct-read-a-when-struct-value-oldp
    (implies (and (struct-value-oldp sval)
                  (equal member (c::ident "a")))
             (equal (c::value-struct-read member sval)
                    (struct-value-old-a sval)))
    :enable (struct-value-oldp
             c::value-struct-read
             c::value-struct-read-aux)))

;;;;;;;;;;;;;;;;;;;;

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
                                       nth))))

  (defruled value-struct-read-b-when-struct-value-oldp
    (implies (and (struct-value-oldp sval)
                  (equal member (c::ident "b")))
             (equal (c::value-struct-read member sval)
                    (struct-value-old-b sval)))
    :enable (struct-value-oldp
             c::value-struct-read
             c::value-struct-read-aux
             nth)))

;;;;;;;;;;;;;;;;;;;;

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
                                       c::value-struct-read-aux))))

  (defruled value-struct-read-a-when-struct-value-newlp
    (implies (and (struct-value-newlp sval)
                  (equal member (c::ident "a")))
             (equal (c::value-struct-read member sval)
                    (struct-value-newl-a sval)))
    :enable (struct-value-newlp
             c::value-struct-read
             c::value-struct-read-aux)))

;;;;;;;;;;;;;;;;;;;;

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
                                       c::value-struct-read-aux))))

  (defruled value-struct-read-b-when-struct-value-newrp
    (implies (and (struct-value-newrp sval)
                  (equal member (c::ident "b")))
             (equal (c::value-struct-read member sval)
                    (struct-value-newr-b sval)))
    :enable (struct-value-newrp
             c::value-struct-read
             c::value-struct-read-aux)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; equivalence of computation states

; the computation states are the same except that
; there is a global struct object that is split into two

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
        (static-equivp old-static new-static))))

  ///

  (defruled struct-value-equivp-when-static-equivp
    (b* ((old-var+val (omap::assoc (c::ident "gso") old-static))
         (newl-var+val (omap::assoc (c::ident "gso") new-static))
         (newr-var+val (omap::assoc (c::ident "gso_0") new-static)))
      (implies (and (static-equivp old-static new-static)
                    (c::scopep old-static)
                    (c::scopep new-static)
                    old-var+val)
               (and newl-var+val
                    newr-var+val
                    (struct-value-equivp (cdr old-var+val)
                                         (cdr newl-var+val)
                                         (cdr newr-var+val)))))
    :induct (static-equivp old-static new-static)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                                                 new-compst))

  ///

  (defruled struct-value-equivp-when-compustate-equivp
    (b* ((old-val
          (c::read-object (c::objdesign-of-var (c::ident "gso") old-compst)
                          old-compst))
         (newl-val
          (c::read-object (c::objdesign-of-var (c::ident "gso") new-compst)
                          new-compst))
         (newr-val
          (c::read-object (c::objdesign-of-var (c::ident "gso_0") new-compst)
                          new-compst)))
      (implies (compustate-equivp old-compst new-compst)
               (struct-value-equivp old-val newl-val newr-val)))
    ;; TODO: try as rewrite rules
    :use ((:instance c::read-object-when-compustate-has-static-var-with-type-p
                     (var (c::ident "gso"))
                     (type (c::type-struct (c::ident "s")))
                     (compst old-compst))
          (:instance c::read-object-when-compustate-has-static-var-with-type-p
                     (var (c::ident "gso"))
                     (type (c::type-struct (c::ident "s")))
                     (compst new-compst))
          (:instance c::read-object-when-compustate-has-static-var-with-type-p
                     (var (c::ident "gso_0"))
                     (type (c::type-struct (c::ident "s2")))
                     (compst new-compst))
          (:instance struct-value-equivp-when-static-equivp
                     (old-static (c::compustate->static old-compst))
                     (new-static (c::compustate->static new-compst))))
    :enable c::assoc-static-when-compustate-has-static-var-with-type-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; equality of member accesses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-old-struct
  (implies (and (compustate-equivp old-compst new-compst)
                (equal expr (c::expr-ident (c::ident "gso")))
                (not (zp limit)))
           (equal (c::exec-expr expr old-compst old-fenv limit)
                  (mv (c::expr-value
                       (c::read-object (c::objdesign-of-var (c::ident "gso")
                                                            old-compst)
                                       old-compst)
                       (c::objdesign-of-var (c::ident "gso") old-compst))
                      (c::compustate-fix old-compst))))
  :enable (c::exec-expr
           c::exec-ident
           compustate-equivp
           c::objdesign-of-var-when-compustate-has-static-var-with-type-p))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-newl-struct
  (implies (and (compustate-equivp old-compst new-compst)
                (equal expr (c::expr-ident (c::ident "gso")))
                (not (zp limit)))
           (equal (c::exec-expr expr new-compst new-fenv limit)
                  (mv (c::expr-value
                       (c::read-object (c::objdesign-of-var (c::ident "gso")
                                                            new-compst)
                                       new-compst)
                       (c::objdesign-of-var (c::ident "gso") new-compst))
                      (c::compustate-fix new-compst))))
  :enable (c::exec-expr
           c::exec-ident
           compustate-equivp
           c::objdesign-of-var-when-compustate-has-static-var-with-type-p))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-newr-struct
  (implies (and (compustate-equivp old-compst new-compst)
                (equal expr (c::expr-ident (c::ident "gso_0")))
                (not (zp limit)))
           (equal (c::exec-expr expr new-compst new-fenv limit)
                  (mv (c::expr-value
                       (c::read-object (c::objdesign-of-var (c::ident "gso_0")
                                                            new-compst)
                                       new-compst)
                       (c::objdesign-of-var (c::ident "gso_0") new-compst))
                      (c::compustate-fix new-compst))))
  :enable (c::exec-expr
           c::exec-ident
           compustate-equivp
           c::objdesign-of-var-when-compustate-has-static-var-with-type-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-member-a
  (b* ((old-expr (c::expr-member (c::expr-ident (c::ident "gso"))
                                 (c::ident "a")))
       (new-expr (c::expr-member (c::expr-ident (c::ident "gso"))
                                 (c::ident "a")))
       ((mv old-eval old-compst1)
        (c::exec-expr old-expr old-compst old-fenv limit))
       ((mv new-eval new-compst1)
        (c::exec-expr new-expr new-compst new-fenv limit))
       (old-val (c::expr-value->value old-eval))
       (new-val (c::expr-value->value new-eval)))
    (implies (and (compustate-equivp old-compst new-compst)
                  (integerp limit)
                  (>= limit 2))
             (and (not (c::errorp old-eval))
                  (not (c::errorp new-eval))
                  old-eval
                  new-eval
                  (equal old-val new-val)
                  (equal old-compst1 (c::compustate-fix old-compst))
                  (equal new-compst1 (c::compustate-fix new-compst)))))
  :use struct-value-equivp-when-compustate-equivp
  :expand ((c::exec-expr '(:member
                           (:ident (:ident (c::name . "gso")))
                           (:ident (c::name . "a")))
                         old-compst old-fenv limit)
           (c::exec-expr '(:member (:ident (:ident (c::name . "gso")))
                           (:ident (c::name . "a")))
                         new-compst new-fenv limit))
  :enable (exec-old-struct
           exec-newl-struct
           c::not-errorp-when-expr-valuep
           c::not-errorp-when-valuep
           c::exec-member
           c::apconvert-expr-value
           struct-value-equivp
           value-kind-when-struct-value-oldp
           value-kind-when-struct-value-newlp
           value-struct-read-a-when-struct-value-oldp
           value-struct-read-a-when-struct-value-newlp))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-member-b
  (b* ((old-expr (c::expr-member (c::expr-ident (c::ident "gso"))
                                 (c::ident "b")))
       (new-expr (c::expr-member (c::expr-ident (c::ident "gso_0"))
                                 (c::ident "b")))
       ((mv old-eval old-compst1)
        (c::exec-expr old-expr old-compst old-fenv limit))
       ((mv new-eval new-compst1)
        (c::exec-expr new-expr new-compst new-fenv limit))
       (old-val (c::expr-value->value old-eval))
       (new-val (c::expr-value->value new-eval)))
    (implies (and (compustate-equivp old-compst new-compst)
                  (integerp limit)
                  (>= limit 2))
             (and (not (c::errorp old-eval))
                  (not (c::errorp new-eval))
                  old-eval
                  new-eval
                  (equal old-val new-val)
                  (equal old-compst1 (c::compustate-fix old-compst))
                  (equal new-compst1 (c::compustate-fix new-compst)))))
  :use struct-value-equivp-when-compustate-equivp
  :expand ((c::exec-expr '(:member
                           (:ident (:ident (c::name . "gso")))
                           (:ident (c::name . "b")))
                         old-compst old-fenv limit)
           (c::exec-expr '(:member (:ident (:ident (c::name . "gso_0")))
                           (:ident (c::name . "b")))
                         new-compst new-fenv limit))
  :enable (exec-old-struct
           exec-newr-struct
           c::not-errorp-when-expr-valuep
           c::not-errorp-when-valuep
           c::exec-member
           c::apconvert-expr-value
           struct-value-equivp
           value-kind-when-struct-value-oldp
           value-kind-when-struct-value-newrp
           value-struct-read-b-when-struct-value-oldp
           value-struct-read-b-when-struct-value-newrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
