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
(include-book "kestrel/c/representation/integers" :dir :system)
(include-book "kestrel/c/atc/symbolic-execution-rules/top" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of equivalence of
; the code transformed in struct-type-split-proofs0.lisp.
; It is preliminary; we are still working out the best formulation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The part of a computation state that f observes consists of two unsigned
; integer members.  In the old program they are both in the static object gso.
; In the new program, a remains in gso and b is in the new static object gso_0.
; The rest of each computation state is deliberately unconstrained.

(define f-compustate-equiv ((old-compst c::compustatep)
                            (new-compst c::compustatep))
  :returns (yes/no booleanp)
  (b* ((old-gso
        (c::read-static-var (c::ident "gso") old-compst))
       ((unless (c::valuep old-gso)) nil)
       ((unless (c::value-case old-gso :struct)) nil)
       ((unless (equal (c::value-struct->tag old-gso) (c::ident "s"))) nil)
       (new-gso
        (c::read-static-var (c::ident "gso") new-compst))
       ((unless (c::valuep new-gso)) nil)
       ((unless (c::value-case new-gso :struct)) nil)
       ((unless (equal (c::value-struct->tag new-gso) (c::ident "s"))) nil)
       (new-gso-0
        (c::read-static-var (c::ident "gso_0") new-compst))
       ((unless (c::valuep new-gso-0)) nil)
       ((unless (c::value-case new-gso-0 :struct)) nil)
       ((unless (equal (c::value-struct->tag new-gso-0)
                       (c::ident "s2")))
        nil)
       (old-a (c::value-struct-read (c::ident "a") old-gso))
       (old-b (c::value-struct-read (c::ident "b") old-gso))
       (new-a (c::value-struct-read (c::ident "a") new-gso))
       (new-b (c::value-struct-read (c::ident "b") new-gso-0)))
    (and (c::uintp old-a)
         (c::uintp old-b)
         (c::uintp new-a)
         (c::uintp new-b)
         (equal old-a new-a)
         (equal old-b new-b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete descriptions of f in the two function environments.  These let the
; dynamic semantics symbolically execute the two parsed function bodies.

(make-event
 `(defruled lookup-of-old-f
    (equal (c::fun-env-lookup (c::ident "f")
                              (c::init-fun-env
                               (c::preprocess *oldf*)))
           ',(c::fun-env-lookup (c::ident "f")
                                (c::init-fun-env
                                 (c::preprocess *oldf*))))))

(make-event
 `(defruled lookup-of-new-f
    (equal (c::fun-env-lookup (c::ident "f")
                              (c::init-fun-env
                               (c::preprocess *newf*)))
           ',(c::fun-env-lookup (c::ident "f")
                                (c::init-fun-env
                                 (c::preprocess *newf*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The generic symbolic execution rules know how to reduce arithmetic and
; member access.  These two rules package that reduction for the concrete
; return expressions, including the fact that global identifiers denote
; static objects below f's stack frame.

(make-event
 `(defruled exec-gso-ident-in-f
    (implies
     (c::valuep (c::read-static-var (c::ident "gso") compst))
     (equal
      (c::exec-expr-pure
       ',(c::expr-ident (c::ident "gso"))
       (c::add-var ',(c::ident "x")
                   x
                   (c::add-frame (c::ident "f") compst)))
      (c::expr-value
       (c::read-static-var (c::ident "gso") compst)
       (c::objdesign-static ',(c::ident "gso")))))
    :in-theory (theory 'c::atc-all-rules)))

(make-event
 `(defruled exec-gso-a-in-f
    (implies
     (and (c::valuep (c::read-static-var (c::ident "gso") compst))
          (c::value-case
           (c::read-static-var (c::ident "gso") compst)
           :struct)
          (c::uintp
           (c::value-struct-read
            (c::ident "a")
            (c::read-static-var (c::ident "gso") compst))))
     (equal
      (c::exec-expr-pure
       ',(c::expr-member (c::expr-ident (c::ident "gso"))
                         (c::ident "a"))
       (c::add-var ',(c::ident "x")
                   x
                   (c::add-frame (c::ident "f") compst)))
      (c::expr-value
       (c::value-struct-read
        (c::ident "a")
        (c::read-static-var (c::ident "gso") compst))
       (and (c::objdesign-static ',(c::ident "gso"))
            (c::objdesign-member
             (c::objdesign-static ',(c::ident "gso"))
             (c::ident "a"))))))
    :in-theory
    (union-theories (theory 'c::atc-all-rules)
                    '(exec-gso-ident-in-f
                      c::exec-member
                      c::expr-value->object-of-expr-value
                      c::objdesign-option-fix-when-objdesign-optionp
                      c::objdesign-optionp-when-objdesignp
                      c::not-nil-when-objdesignp
                      c::not-errorp-when-expr-valuep))))

(make-event
 (b* ((info (c::fun-env-lookup
             (c::ident "f")
             (c::init-fun-env (c::preprocess *oldf*))))
      (item (car (c::fun-info->body info)))
      (stmt (c::block-item-stmt->get item))
      (expr (c::stmt-return->value stmt)))
   `(defruled exec-old-f-expression
      (implies
       (and (c::compustatep compst)
            (c::uintp x)
            (c::valuep
             (c::read-static-var (c::ident "gso") compst))
            (c::value-case
             (c::read-static-var (c::ident "gso") compst)
             :struct)
            (c::uintp
             (c::value-struct-read
              (c::ident "a")
              (c::read-static-var (c::ident "gso") compst)))
            (c::uintp
             (c::value-struct-read
              (c::ident "b")
              (c::read-static-var (c::ident "gso") compst))))
       (equal
        (c::exec-expr-pure
         ',expr
         (c::add-var ',(c::ident "x")
                     x
                     (c::add-frame (c::ident "f") compst)))
        (c::expr-value
         (c::add-uint-uint
          (c::add-uint-uint
           x
           (c::value-struct-read
            (c::ident "a")
            (c::read-static-var (c::ident "gso") compst)))
          (c::value-struct-read
           (c::ident "b")
           (c::read-static-var (c::ident "gso") compst)))
         nil)))
      :in-theory
      (union-theories
       (theory 'c::atc-all-rules)
       '(exec-gso-ident-in-f
         exec-gso-a-in-f
         c::exec-member
         c::expr-value->object-of-expr-value
         c::objdesign-option-fix-when-objdesign-optionp
         c::objdesign-optionp-when-objdesignp
         c::not-nil-when-objdesignp
         c::not-errorp-when-expr-valuep
         c::objdesign-of-var-of-add-var-iff
         c::read-object-of-objdesign-of-var-of-add-var
         c::objdesign-of-var-of-add-frame-when-read-object-static)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((info (c::fun-env-lookup
             (c::ident "f")
             (c::init-fun-env (c::preprocess *oldf*))))
      (body (c::fun-info->body info))
      (item (car body))
      (stmt (c::block-item-stmt->get item)))
   `(progn
      (defruled exec-old-f-stmt
        (implies
         (and (c::compustatep compst)
              (c::uintp x)
              (integerp limit)
              (>= limit 5)
              (c::valuep
               (c::read-static-var (c::ident "gso") compst))
              (c::value-case
               (c::read-static-var (c::ident "gso") compst)
               :struct)
              (c::uintp
               (c::value-struct-read
                (c::ident "a")
                (c::read-static-var (c::ident "gso") compst)))
              (c::uintp
               (c::value-struct-read
                (c::ident "b")
                (c::read-static-var (c::ident "gso") compst))))
         (equal
          (c::exec-stmt
           ',stmt
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst))
           fenv
           limit)
          (mv
           (c::stmt-value-return
            (c::add-uint-uint
             (c::add-uint-uint
              x
              (c::value-struct-read
               (c::ident "a")
               (c::read-static-var (c::ident "gso") compst)))
             (c::value-struct-read
              (c::ident "b")
              (c::read-static-var (c::ident "gso") compst))))
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst)))))
        :in-theory
        (union-theories
         (theory 'c::atc-all-rules)
         '(exec-old-f-expression
           c::stmt-fix-when-stmtp
           (:e c::stmtp)))
        :hints
        (("Goal"
          :expand
          ((c::exec-stmt
            ',stmt
            (c::add-var ',(c::ident "x")
                        x
                        (c::add-frame (c::ident "f") compst))
            fenv
            limit)))))

      (defruled exec-old-f-item
        (implies
         (and (c::compustatep compst)
              (c::uintp x)
              (integerp limit)
              (>= limit 6)
              (c::valuep
               (c::read-static-var (c::ident "gso") compst))
              (c::value-case
               (c::read-static-var (c::ident "gso") compst)
               :struct)
              (c::uintp
               (c::value-struct-read
                (c::ident "a")
                (c::read-static-var (c::ident "gso") compst)))
              (c::uintp
               (c::value-struct-read
                (c::ident "b")
                (c::read-static-var (c::ident "gso") compst))))
         (equal
          (c::exec-block-item
           ',item
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst))
           fenv
           limit)
          (mv
           (c::stmt-value-return
            (c::add-uint-uint
             (c::add-uint-uint
              x
              (c::value-struct-read
               (c::ident "a")
               (c::read-static-var (c::ident "gso") compst)))
             (c::value-struct-read
              (c::ident "b")
              (c::read-static-var (c::ident "gso") compst))))
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst)))))
        :in-theory
        '(c::exec-block-item-when-stmt
          (:e c::block-item-kind)
          c::not-zp-of-limit-variable
          (:e c::block-item-stmt->get)
          exec-old-f-stmt))

      (defruled exec-old-f-body
        (implies
         (and (c::compustatep compst)
              (c::uintp x)
              (integerp limit)
              (>= limit 7)
              (c::valuep
               (c::read-static-var (c::ident "gso") compst))
              (c::value-case
               (c::read-static-var (c::ident "gso") compst)
               :struct)
              (c::uintp
               (c::value-struct-read
                (c::ident "a")
                (c::read-static-var (c::ident "gso") compst)))
              (c::uintp
               (c::value-struct-read
                (c::ident "b")
                (c::read-static-var (c::ident "gso") compst))))
         (equal
          (c::exec-block-item-list
           ',body
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst))
           fenv
           limit)
          (mv
           (c::stmt-value-return
            (c::add-uint-uint
             (c::add-uint-uint
              x
              (c::value-struct-read
               (c::ident "a")
               (c::read-static-var (c::ident "gso") compst)))
             (c::value-struct-read
              (c::ident "b")
              (c::read-static-var (c::ident "gso") compst))))
           (c::add-var ',(c::ident "x")
                       x
                       (c::add-frame (c::ident "f") compst)))))
        :in-theory
        '(c::exec-block-item-list-when-consp
          c::not-zp-of-limit-variable
          acl2::mv-nth-of-cons
          (:e zp)
          c::value-optionp-when-valuep
          (:e c::value-optionp)
          (:e c::valuep)
          c::valuep-when-uintp
          exec-old-f-item
          c::exec-block-item-list-of-nil
          c::return-type-of-stmt-value-return
          c::stmt-value-return->value?-of-stmt-value-return
          c::stmt-value-return-of-value-option-fix-value?
          c::value-option-fix-when-value-optionp
          c::not-zp-of-limit-minus-const)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-old-f
  (implies
   (and (c::compustatep compst)
        (c::uintp x)
        (integerp limit)
        (>= limit 8)
        (c::valuep (c::read-static-var (c::ident "gso") compst))
        (c::value-case
         (c::read-static-var (c::ident "gso") compst)
         :struct)
        (c::uintp
         (c::value-struct-read
          (c::ident "a")
          (c::read-static-var (c::ident "gso") compst)))
        (c::uintp
         (c::value-struct-read
          (c::ident "b")
          (c::read-static-var (c::ident "gso") compst))))
   (equal
    (c::exec-fun (c::ident "f")
                 (list x)
                 compst
                 (c::init-fun-env (c::preprocess *oldf*))
                 limit)
    (mv
     (c::add-uint-uint
      (c::add-uint-uint
       x
       (c::value-struct-read
        (c::ident "a")
        (c::read-static-var (c::ident "gso") compst)))
      (c::value-struct-read
       (c::ident "b")
       (c::read-static-var (c::ident "gso") compst)))
     compst)))
  :in-theory
  (union-theories (theory 'c::atc-all-rules)
                  '(lookup-of-old-f
                    exec-old-f-body
                    exec-old-f-expression
                    c::return-type-of-stmt-value-return
                    c::not-errorp-when-stmt-valuep
                    c::stmt-value-return->value?-of-stmt-value-return
                    c::value-option-fix-when-value-optionp
                    c::value-optionp-when-valuep
                    c::type-of-value-option-when-valuep))
  :hints
  (("Goal"
    :expand
    ((c::exec-fun (c::ident "f")
                  (list x)
                  compst
                  (c::init-fun-env (c::preprocess *oldf*))
                  limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defruled exec-gso-0-ident-in-f
    (implies
     (c::valuep (c::read-static-var (c::ident "gso_0") compst))
     (equal
      (c::exec-expr-pure
       ',(c::expr-ident (c::ident "gso_0"))
       (c::add-var ',(c::ident "x")
                   x
                   (c::add-frame (c::ident "f") compst)))
      (c::expr-value
       (c::read-static-var (c::ident "gso_0") compst)
       (c::objdesign-static ',(c::ident "gso_0")))))
    :in-theory (theory 'c::atc-all-rules)))

(make-event
 `(defruled exec-gso-0-b-in-f
    (implies
     (and (c::valuep (c::read-static-var (c::ident "gso_0") compst))
          (c::value-case
           (c::read-static-var (c::ident "gso_0") compst)
           :struct)
          (c::uintp
           (c::value-struct-read
            (c::ident "b")
            (c::read-static-var (c::ident "gso_0") compst))))
     (equal
      (c::exec-expr-pure
       ',(c::expr-member (c::expr-ident (c::ident "gso_0"))
                         (c::ident "b"))
       (c::add-var ',(c::ident "x")
                   x
                   (c::add-frame (c::ident "f") compst)))
      (c::expr-value
       (c::value-struct-read
        (c::ident "b")
        (c::read-static-var (c::ident "gso_0") compst))
       (and (c::objdesign-static ',(c::ident "gso_0"))
            (c::objdesign-member
             (c::objdesign-static ',(c::ident "gso_0"))
             (c::ident "b"))))))
    :in-theory
    (union-theories (theory 'c::atc-all-rules)
                    '(exec-gso-0-ident-in-f
                      c::exec-member
                      c::expr-value->object-of-expr-value
                      c::objdesign-option-fix-when-objdesign-optionp
                      c::objdesign-optionp-when-objdesignp
                      c::not-nil-when-objdesignp
                      c::not-errorp-when-expr-valuep))))

(make-event
 (b* ((info (c::fun-env-lookup
             (c::ident "f")
             (c::init-fun-env (c::preprocess *newf*))))
      (item (car (c::fun-info->body info)))
      (stmt (c::block-item-stmt->get item))
      (expr (c::stmt-return->value stmt)))
   `(defruled exec-new-f-expression
      (implies
       (and (c::compustatep compst)
            (c::uintp x)
            (c::valuep
             (c::read-static-var (c::ident "gso") compst))
            (c::value-case
             (c::read-static-var (c::ident "gso") compst)
             :struct)
            (c::uintp
             (c::value-struct-read
              (c::ident "a")
              (c::read-static-var (c::ident "gso") compst)))
            (c::valuep
             (c::read-static-var (c::ident "gso_0") compst))
            (c::value-case
             (c::read-static-var (c::ident "gso_0") compst)
             :struct)
            (c::uintp
             (c::value-struct-read
              (c::ident "b")
              (c::read-static-var (c::ident "gso_0") compst))))
       (equal
        (c::exec-expr-pure
         ',expr
         (c::add-var ',(c::ident "x")
                     x
                     (c::add-frame (c::ident "f") compst)))
        (c::expr-value
         (c::add-uint-uint
          (c::add-uint-uint
           x
           (c::value-struct-read
            (c::ident "a")
            (c::read-static-var (c::ident "gso") compst)))
          (c::value-struct-read
           (c::ident "b")
           (c::read-static-var (c::ident "gso_0") compst)))
         nil)))
      :in-theory
      (union-theories
       (theory 'c::atc-all-rules)
       '(exec-gso-ident-in-f
         exec-gso-a-in-f
         exec-gso-0-ident-in-f
         exec-gso-0-b-in-f
         c::exec-member
         c::expr-value->object-of-expr-value
         c::objdesign-option-fix-when-objdesign-optionp
         c::objdesign-optionp-when-objdesignp
         c::not-nil-when-objdesignp
         c::not-errorp-when-expr-valuep
         c::objdesign-of-var-of-add-var-iff
         c::read-object-of-objdesign-of-var-of-add-var
         c::objdesign-of-var-of-add-frame-when-read-object-static)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((info (c::fun-env-lookup
             (c::ident "f")
             (c::init-fun-env (c::preprocess *newf*))))
      (body (c::fun-info->body info))
      (item (car body))
      (stmt (c::block-item-stmt->get item))
      (fun-compst `(c::add-var ',(c::ident "x")
                               x
                               (c::add-frame (c::ident "f") compst)))
      (result `(c::add-uint-uint
                (c::add-uint-uint
                 x
                 (c::value-struct-read
                  (c::ident "a")
                  (c::read-static-var (c::ident "gso") compst)))
                (c::value-struct-read
                 (c::ident "b")
                 (c::read-static-var (c::ident "gso_0") compst))))
      (hyps `((c::compustatep compst)
              (c::uintp x)
              (integerp limit)
              (c::valuep
               (c::read-static-var (c::ident "gso") compst))
              (c::value-case
               (c::read-static-var (c::ident "gso") compst)
               :struct)
              (c::uintp
               (c::value-struct-read
                (c::ident "a")
                (c::read-static-var (c::ident "gso") compst)))
              (c::valuep
               (c::read-static-var (c::ident "gso_0") compst))
              (c::value-case
               (c::read-static-var (c::ident "gso_0") compst)
               :struct)
              (c::uintp
               (c::value-struct-read
                (c::ident "b")
                (c::read-static-var (c::ident "gso_0") compst))))))
   `(progn
      (defruled exec-new-f-stmt
        (implies
         (and ,@hyps (>= limit 5))
         (equal (c::exec-stmt ',stmt ,fun-compst fenv limit)
                (mv (c::stmt-value-return ,result) ,fun-compst)))
        :in-theory
        (union-theories
         (theory 'c::atc-all-rules)
         '(exec-new-f-expression
           c::stmt-fix-when-stmtp
           (:e c::stmtp)))
        :hints
        (("Goal"
          :expand ((c::exec-stmt ',stmt ,fun-compst fenv limit)))))

      (defruled exec-new-f-item
        (implies
         (and ,@hyps (>= limit 6))
         (equal (c::exec-block-item ',item ,fun-compst fenv limit)
                (mv (c::stmt-value-return ,result) ,fun-compst)))
        :in-theory
        '(c::exec-block-item-when-stmt
          (:e c::block-item-kind)
          c::not-zp-of-limit-variable
          (:e c::block-item-stmt->get)
          exec-new-f-stmt))

      (defruled exec-new-f-body
        (implies
         (and ,@hyps (>= limit 7))
         (equal (c::exec-block-item-list ',body ,fun-compst fenv limit)
                (mv (c::stmt-value-return ,result) ,fun-compst)))
        :in-theory
        '(c::exec-block-item-list-when-consp
          c::not-zp-of-limit-variable
          acl2::mv-nth-of-cons
          (:e zp)
          c::value-optionp-when-valuep
          (:e c::value-optionp)
          (:e c::valuep)
          c::valuep-when-uintp
          exec-new-f-item
          c::exec-block-item-list-of-nil
          c::return-type-of-stmt-value-return
          c::stmt-value-return->value?-of-stmt-value-return
          c::stmt-value-return-of-value-option-fix-value?
          c::value-option-fix-when-value-optionp
          c::not-zp-of-limit-minus-const))

      (defruled exec-new-f
        (implies
         (and ,@hyps (>= limit 8))
         (equal
          (c::exec-fun (c::ident "f")
                       (list x)
                       compst
                       (c::init-fun-env (c::preprocess *newf*))
                       limit)
          (mv ,result compst)))
        :in-theory
        (union-theories
         (theory 'c::atc-all-rules)
         '(lookup-of-new-f
           exec-new-f-body
           c::return-type-of-stmt-value-return
           c::not-errorp-when-stmt-valuep
           c::stmt-value-return->value?-of-stmt-value-return
           c::value-option-fix-when-value-optionp
           c::value-optionp-when-valuep
           c::type-of-value-option-when-valuep))
        :hints
        (("Goal"
          :expand
          ((c::exec-fun (c::ident "f")
                        (list x)
                        compst
                        (c::init-fun-env (c::preprocess *newf*))
                        limit))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Calls of f return the same value whenever their initial computation states
; satisfy the correspondence above.  Since f only reads its parameter and the
; two global members, both calls also leave their respective states unchanged.

(defrule f-calls-equivalent-lemma
  (implies
   (and (f-compustate-equiv old-compst new-compst)
        (c::compustatep old-compst)
        (c::compustatep new-compst)
        (c::uintp x)
        (integerp limit)
        (>= limit 8)
        (equal old-result+compst
               (c::exec-fun (c::ident "f")
                            (list x)
                            old-compst
                            (c::init-fun-env (c::preprocess *oldf*))
                            limit))
        (equal old-result (mv-nth 0 old-result+compst))
        (equal old-final-compst (mv-nth 1 old-result+compst))
        (equal new-result+compst
               (c::exec-fun (c::ident "f")
                            (list x)
                            new-compst
                            (c::init-fun-env (c::preprocess *newf*))
                            limit))
        (equal new-result (mv-nth 0 new-result+compst))
        (equal new-final-compst (mv-nth 1 new-result+compst)))
   (and (c::uintp old-result)
        (c::uintp new-result)
        (equal old-result new-result)
        (equal old-final-compst old-compst)
        (equal new-final-compst new-compst)))
  :in-theory
  (union-theories (theory 'c::atc-all-rules)
                  '(f-compustate-equiv
                   lookup-of-old-f
                   lookup-of-new-f
                   exec-old-f
                   exec-new-f
                   exec-old-f-expression
                   c::exec-member
                   c::objdesign-of-var-of-add-var-iff
                   c::read-object-of-objdesign-of-var-of-add-var
                   c::objdesign-of-var-of-add-frame-when-read-object-static))
  :rule-classes nil)

(defrule f-calls-equivalent
  (implies
   (and (f-compustate-equiv old-compst new-compst)
        (c::compustatep old-compst)
        (c::compustatep new-compst)
        (c::uintp x)
        (integerp limit)
        (>= limit 8))
   (b* (((mv old-result old-final-compst)
         (c::exec-fun (c::ident "f")
                      (list x)
                      old-compst
                      (c::init-fun-env (c::preprocess *oldf*))
                      limit))
        ((mv new-result new-final-compst)
         (c::exec-fun (c::ident "f")
                      (list x)
                      new-compst
                      (c::init-fun-env (c::preprocess *newf*))
                      limit)))
     (and (c::uintp old-result)
          (c::uintp new-result)
          (equal old-result new-result)
          (equal old-final-compst old-compst)
          (equal new-final-compst new-compst))))
  :use
  (:instance f-calls-equivalent-lemma
   (old-result+compst
    (c::exec-fun (c::ident "f")
                 (list x)
                 old-compst
                 (c::init-fun-env (c::preprocess *oldf*))
                 limit))
   (old-result
    (mv-nth 0
            (c::exec-fun (c::ident "f")
                         (list x)
                         old-compst
                         (c::init-fun-env (c::preprocess *oldf*))
                         limit)))
   (old-final-compst
    (mv-nth 1
            (c::exec-fun (c::ident "f")
                         (list x)
                         old-compst
                         (c::init-fun-env (c::preprocess *oldf*))
                         limit)))
   (new-result+compst
    (c::exec-fun (c::ident "f")
                 (list x)
                 new-compst
                 (c::init-fun-env (c::preprocess *newf*))
                 limit))
   (new-result
    (mv-nth 0
            (c::exec-fun (c::ident "f")
                         (list x)
                         new-compst
                         (c::init-fun-env (c::preprocess *newf*))
                         limit)))
   (new-final-compst
    (mv-nth 1
            (c::exec-fun (c::ident "f")
                         (list x)
                         new-compst
                         (c::init-fun-env (c::preprocess *newf*))
                         limit))))
  :in-theory nil
  :rule-classes nil)
