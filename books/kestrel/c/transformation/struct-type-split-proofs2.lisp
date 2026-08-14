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

(include-book "kestrel/c/language/dynamic-semantics" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains work in progress towards
; some general approach to generate proofs for the STS transformation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mapping between old and new struct values

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

(define struct-value-new1p ((sval c::valuep))
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

(define struct-value-new2p ((sval c::valuep))
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

(define struct-value-new1-a ((sval c::valuep))
  :guard (struct-value-new1p sval)
  :returns (aval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "a") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-new1p
                                           c::value-struct-read
                                           c::value-struct-read-aux)))
  ///
  (defret value-kind-of-struct-value-new1-a
    (equal (c::value-kind aval) :uint)
    :hyp (struct-value-new1p sval)
    :hints (("Goal" :in-theory (enable struct-value-new1p
                                       c::value-struct-read
                                       c::value-struct-read-aux)))))

(define struct-value-new2-b ((sval c::valuep))
  :guard (struct-value-new2p sval)
  :returns (bval c::valuep)
  (c::value-fix (c::value-struct-read (c::ident "b") sval))
  :guard-hints (("Goal" :in-theory (enable struct-value-new2p
                                           c::value-struct-read
                                           c::value-struct-read-aux)))
  ///
  (defret value-kind-of-struct-value-new2-b
    (equal (c::value-kind bval) :uint)
    :hyp (struct-value-new2p sval)
    :hints (("Goal" :in-theory (enable struct-value-new2p
                                       c::value-struct-read
                                       c::value-struct-read-aux)))))

(define struct-value-old-to-new ((sval c::valuep))
  :guard (struct-value-oldp sval)
  :returns (mv (sval1 c::valuep) (sval2 c::valuep))
  (b* ((aval (struct-value-old-a sval))
       (bval (struct-value-old-b sval)))
    (mv (c::make-value-struct
         :tag (c::ident "s")
         :members (list (c::make-member-value :name (c::ident "a")
                                              :value aval))
         :flexiblep nil)
        (c::make-value-struct
         :tag (c::ident "s2")
         :members (list (c::make-member-value :name (c::ident "b")
                                              :value bval))
         :flexiblep nil)))
  ///
  (defret struct-value-new1p-of-struct-value-old-to-new
    (struct-value-new1p sval1)
    :hyp (struct-value-oldp sval)
    :hints (("Goal" :in-theory (enable struct-value-new1p))))
  (defret struct-value-new2p-of-struct-value-old-to-new
    (struct-value-new2p sval2)
    :hyp (struct-value-oldp sval)
    :hints (("Goal" :in-theory (enable struct-value-new2p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mapping between old and new computation states

(define compustate-oldp ((compst c::compustatep))
  :returns (yes/no booleanp)
  (b* (;; old struct value at gso:
       (objdes (c::objdesign-of-var (c::ident "gso") compst))
       ((unless objdes) nil)
       ((unless (c::objdesign-case objdes :static)) nil)
       (sval (c::read-object objdes compst))
       ((unless (struct-value-oldp sval)) nil)
       ;; no gso_0 (i.e. fresh name):
       ((when (c::objdesign-of-var (c::ident "gso_0") compst)) nil))
    t)
  :guard-hints
  (("Goal" :in-theory (enable c::valuep-of-read-object-of-objdesign-of-var))))

(define compustate-newp ((compst c::compustatep))
  :returns (yes/no booleanp)
  (b* (;; new left struct at gso:
       (objdes (c::objdesign-of-var (c::ident "gso") compst))
       ((unless objdes) nil)
       ((unless (c::objdesign-case objdes :static)) nil)
       (sval (c::read-object objdes compst))
       ((unless (struct-value-new1p sval)) nil)
       ;; new right struct at gso_0:
       (objdes (c::objdesign-of-var (c::ident "gso_0") compst))
       ((unless objdes) nil)
       ((unless (c::objdesign-case objdes :static)) nil)
       (sval (c::read-object objdes compst))
       ((unless (struct-value-new2p sval)) nil))
    t)
  :guard-hints
  (("Goal" :in-theory (enable c::valuep-of-read-object-of-objdesign-of-var))))

(define compustate-old-to-new ((compst c::compustatep))
  :guard (compustate-oldp compst)
  :returns (compst1 c::compustatep)
  (b* ((static (c::compustate->static compst))
       (sval (omap::lookup (c::ident "gso") static))
       ((mv sval1 sval2) (struct-value-old-to-new sval))
       (static (omap::delete (c::ident "gso") static))
       (static (omap::update (c::ident "gso") sval1 static))
       (static (omap::update (c::ident "gso_0") sval2 static)))
    (c::change-compustate compst :static static))
  :guard-hints (("Goal" :in-theory (enable compustate-oldp
                                           c::objdesign-of-var
                                           c::read-object
                                           omap::lookup)))
  ///
  (defret compustate-newp-of-compustate-old-to-new
    (compustate-newp compst1)
    :hyp (compustate-oldp compst)
    :hints (("Goal" :in-theory (enable compustate-oldp
                                       compustate-newp
                                       c::objdesign-of-var
                                       c::top-frame
                                       c::read-object
                                       omap::lookup)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
