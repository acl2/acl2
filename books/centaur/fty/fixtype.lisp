; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/da-base" :dir :system)

(program)
(set-state-ok t)

(defxdoc fty
  :parents (acl2::macro-libraries)

  :short "A library of utilities supporting a type discipline that minimizes
the need for type hypotheses in theorems."

  :long "<p>FTY is short for <i>fixtype</i>, a systematic way of using types in
ACL2 that is intended to be easy to use and easy on prover and execution
performance.</p>

<p>Fixtype is one of several paradigms for \"type-safe\" programming in ACL2.
In this discipline,</p>
<ul>

<li>Every type (predicate) @('q-p') has an associated fixing function
@('q-fix') and equivalence relation @('q-equiv'), such that (for all @('x'), @('y'))
@({
    (q-p (q-fix x)),
    (implies (q-p x) (equal (q-fix x) x)),
    (equal (q-equiv x y) (equal (q-fix x) (q-fix y))).
 })</li>


<li>If a function @('foo') takes an argument of the @('q') type, then it has an
equality congruence with @('q-equiv') on that argument, i.e.:
@({
 (implies (q-equiv x y) (equal (foo x) (foo y)))
 })</li>

<li>If @('foo') is supposed to return a value of type @('q'), then it does so unconditionally:
@({
 (q-p (foo x)).
 })</li>
</ul>

<p>Given types that have associated fixing functions and equivalence relations,
the latter two requirements are easy to engineer: you can either build on
existing functions that already satisfy these requirements, or you can fix each
of the inputs to a function to appropriate types for free, using MBE:</p>
@({
 (defun nat-add-5 (n)
   (declare (xargs :guard (natp n)))
   (let ((n (mbe :logic (nfix n) :exec n)))
     (+ n 5)))
 })

<p>Having unconditional return types and congruences are both beneficial in
themselves.  But the main benefit of using the fixtype discipline is that
reasoning about such functions does not require hypotheses constraining their
inputs to the expected types, because they are fixed to that type (in a
consistent manner) before being used.</p>

<p>The @('FTY') library contains various utilities to support this typing discipline, notably:</p>
<ul>
<li>@(see deffixtype), associates a fixing function and equivalence relation
with a type predicate (optionally defining the equivalence relation for
you);</li>
<li>@(see deffixequiv) and @(see deffixequiv-mutual) automate the (otherwise
tedious) congruence proofs required for each function that follows the fixtype
discipline;</li>
<li>@(see deftypes) provides a set of type generating utilities that can be
used with the fixtype discipline, supporting (recursive and mutually recursive)
sum, product, list, and alist types;</li>
<li>@(see basetypes) includes fixing function associations for many of the
common ACL2 base types (numbers, symbols, strings).</li>
</ul>")

(defxdoc deffixtype
  :parents (fty)
  :short "Define a named type, associating a unary predicate, fixing function,
and equivalence relation."
  :long "<p>Part of an attempt to automate the proof discipline described at
@(see fixtype).</p>

<p>@('DEFFIXTYPE') simply associates a type name with an existing predicate,
fixing function, and equivalence relation.  It stores this association in a
table for later use by @(see deffixequiv) and @(see deffixequiv-mutual).</p>

<p>Usage:</p>
@({
  (deffixtype widget
              :pred widget-p
              :fix  widget-fix
              :equiv widget-equiv
              ;; optional:
              :executablep nil  ;; t by default
              :define t  ;; nil by default: define the equivalence as equal of fix
})

<p>The optional arguments:</p>

<ul>

<li>@(':define') is NIL by default; if set to T, then the equivalence relation
is assumed not to exist yet, and is defined as equality of fix, with
appropriate rules to rewrite the fix away under the equivalence and to
propagate the congruence into the fix.</li>

<li>@(':executablep') should be set to NIL if either the fixing function or
predicate are non-executable or especially expensive.  This mainly affects, in
@('deffixequiv') and @('deffixequiv-mutual'), whether a theorem is introduced
that normalizes constants by applying the fixing function to them.</li>

</ul>

<p>We assume that the fixing function returns an object that satisfies the
predicate, and if given an object satisfying the predicate, it returns the same
object.  We also assume that equiv is an equivalence relation (see @(see
defequiv)).</p>")


(def-primitive-aggregate fixtype
  (name               ;; foo  (not necessarily a function)
   pred               ;; foo-p
   fix                ;; foo-fix
   equiv              ;; foo-equiv
   executablep        ;; affects whether constants are normalized, set to NIL if predicate and fix aren't both executable
   ;; theorem names:
   ;; pred-of-fix         ;; (foo-p (foo-fix x))
   ;; fix-idempotent       ;; (implies (foo-p x) (equal (foo-fix x) x))
   equiv-means-fixes-equal ;; (implies (foo-equiv x y) (equal (foo-fix x) (foo-fix y)))  (or iff/equal)
   
   ))

(table fixtypes)

(defun get-fixtypes-alist (world)
  (cdr (assoc 'fixtype-alist (table-alist 'fixtypes world))))

(defun deffixtype-fn (name predicate fix equiv execp definep verbosep hints)
  (if definep
      `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
         (encapsulate nil
           (logic)
           (local (make-event
                   '(:or (with-output :stack :pop
                           (defthm tmp-deffixtype-idempotent
                             (equal (,fix (,fix x)) (,fix x))))
                     (value-triple
                      (er hard? 'deffixtype
                          "Failed to prove that ~x0 is idempotent.~%" ',fix)))))
           (defund ,equiv (x y)
             (declare (xargs :verify-guards nil))
             (equal (,fix x) (,fix y)))
           (local (in-theory '(,equiv tmp-deffixtype-idempotent
                                      booleanp-compound-recognizer)))
           (defequiv ,equiv)
           (defcong ,equiv equal (,fix x) 1)
           (defthm ,(intern-in-package-of-symbol
                     (concatenate 'string
                                  (symbol-name fix) "-UNDER-" (symbol-name equiv))
                     equiv)
             (,equiv (,fix x) x))
           (table fixtypes 'fixtype-alist
                  (cons (cons ',name ',(fixtype name predicate fix equiv execp equiv))
                        (get-fixtypes-alist world)))))
    (b* ((thmname (intern-in-package-of-symbol
                   (concatenate
                    'string "__DEFFIXTYPE-" (symbol-name equiv) "-MEANS-EQUAL-OF-"
                    (symbol-name fix))
                   'fty)))
      `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
         (progn (make-event
                 '(:or (encapsulate nil
                         (logic)
                         (with-output :stack :pop
                           (defthm ,thmname
                             (implies (,equiv x y)
                                      (equal (,fix x) (,fix y)))
                             :hints ,hints
                             :rule-classes nil)))
                   (with-output :on (error)
                     (value-triple
                      (er hard? 'deffixtype
                          "Failed to prove that ~x0 implies equality of ~x1.  ~
                           You may provide :hints to help."
                          ',equiv ',fix)))))
                (table fixtypes 'fixtype-alist
                       (cons (cons ',name ',(fixtype name predicate fix equiv execp thmname))
                             (get-fixtypes-alist world))))))))


(defmacro deffixtype (name &key pred fix equiv (execp 't)
                           ;; optional 
                           define
                           verbosep
                           hints)
  (deffixtype-fn name pred fix equiv execp define verbosep hints))

(defun find-fixtype-for-pred (pred alist)
  (if (atom alist)
      nil
    (let* ((fixtype (cdar alist)))
      (if (eq (fixtype->pred fixtype) pred)
          fixtype
        (find-fixtype-for-pred pred (cdr alist))))))

(defun find-fixtype-for-equiv (equiv alist)
  (if (atom alist)
      nil
    (let* ((fixtype (cdar alist)))
      (if (eq (fixtype->equiv fixtype) equiv)
          fixtype
        (find-fixtype-for-equiv equiv (cdr alist))))))

(defun find-fixtype-for-typename (name alist)
  (cdr (assoc name alist)))


(defconst *deffixequiv-basic-keywords*
  '(:hints
    :skip-const-thm
    :skip-ok
    :verbosep
    :out-equiv
    :other-var
    :basename))


(def-primitive-aggregate fixequiv
  (form
   arg
   type
   kwd-alist
   fix-body
   fix-thm
   const-thm
   cong-thm))


(defun deffixequiv-basic-parse (form arg type keys state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((__function__ 'deffixequiv-basic-parse)
       (world (w state))
       ((mv kwd-alist rest)
        (extract-keywords 'deffixequiv-basic
                          *deffixequiv-basic-keywords*
                          keys nil))
       ((when rest) (raise "Bad args: ~x0~%" rest))
       (fixtype-al (get-fixtypes-alist world))
       (fixtype (or (find-fixtype-for-typename type fixtype-al)
                    (find-fixtype-for-pred type fixtype-al)))
       (skip-ok (cdr (assoc :skip-ok kwd-alist)))
       ((unless fixtype)
        (if skip-ok
            (prog2$ (cw "Note: skipping ~x0 since its type ~x1 was not a ~
                         fixtype name or predicate~%" arg type)
                    nil)
          (raise "Not a fixtype name or predicate: ~x0" type)))
       (fix (fixtype->fix fixtype))
       (equiv (fixtype->equiv fixtype))
       (pred (fixtype->pred fixtype))
       (hints (getarg :hints nil kwd-alist))
       (skip-const-thm (or (getarg :skip-const-thm nil kwd-alist)
                           (not (fixtype->executablep fixtype))))
       (out-equiv (getarg :out-equiv 'equal kwd-alist))
       ((unless (and (consp form) (symbolp (car form))))
        (raise "Form should be a function call term, but it's ~x0" form))
       (basename (getarg :basename (car form) kwd-alist))
       (pkg (if (equal (symbol-package-name basename) "COMMON-LISP")
                'acl2::foo
              basename))
       (under-out-equiv (if (eq out-equiv 'equal) ""
                          (concatenate 'string "-UNDER-" (symbol-name out-equiv))))
       (fix-thmname
        (intern-in-package-of-symbol
         (concatenate
          'string (symbol-name basename) "-OF-" (symbol-name fix) "-" (symbol-name arg)
          under-out-equiv)
         pkg))
       (const-thmname
        (intern-in-package-of-symbol
         (concatenate
          'string (symbol-name basename) "-OF-" (symbol-name fix) "-" (symbol-name arg) "-NORMALIZE-CONST" under-out-equiv)
         pkg))
       (congruence-thmname
        (intern-in-package-of-symbol
         (concatenate
          'string (symbol-name basename) "-" (symbol-name equiv) "-CONGRUENCE-ON-" (symbol-name arg) under-out-equiv)
         pkg))
       (argequiv (or (getarg :other-var nil kwd-alist)
                     (intern-in-package-of-symbol
                      (concatenate
                       'string (symbol-name arg) "-EQUIV")
                      pkg)))
       ((mv err tr-form) (acl2::translate-cmp form t t nil 'deffixequiv-basic-parse
                                              (w state) (acl2::default-state-vars t)))
       ((when err)
        (raise "Error translating form: ~@0" tr-form))
       (vars (all-vars tr-form))
       ((unless (and (symbolp arg)
                     (member arg vars)))
        (raise "Expected ~x0 to be among variables of ~x1" arg form))

       (fix-body `(,out-equiv ,(subst `(,fix ,arg) arg form)
                              ,form))
       (fix-thm `(defthm ,fix-thmname
                   ,fix-body
                   :hints ,hints))
       (const-thm (and (not skip-const-thm)
                       `(defthm ,const-thmname
                          (implies (syntaxp (and (quotep ,arg)
                                                 (not (,pred (cadr ,arg)))))
                                   (,out-equiv ,form
                                               ,(subst `(,fix ,arg) arg form))))))
       (cong-thm `(defthm ,congruence-thmname
                    (implies (,equiv ,arg ,argequiv)
                             (,out-equiv ,form
                                         ,(subst argequiv arg form)))
                    :hints (("Goal" :in-theory nil
                             :do-not '(preprocess)
                             :use ((:instance ,fix-thmname)
                                   (:instance ,fix-thmname (,arg ,argequiv))
                                   (:instance ,(fixtype->equiv-means-fixes-equal fixtype)
                                    (x ,arg) (y ,argequiv)))))
                    :rule-classes :congruence)))
    (make-fixequiv
     :form form
     :arg arg
     :type type
     :kwd-alist kwd-alist
     :fix-body fix-body
     :fix-thm fix-thm
     :const-thm const-thm
     :cong-thm cong-thm)))

(defun fixequiv-events (fixequiv)
  (b* (((unless fixequiv) '(value-triple :skipped))
       ((fixequiv x) fixequiv))
    `(progn

       (with-output :stack :pop
         ,x.fix-thm)
       
       ,@(and x.const-thm
              `((with-output :on (error)
                  ,x.const-thm)))

       (make-event
        '(:or (with-output :on (error) ,x.cong-thm)
          (with-output :on (error)
            (value-triple
             (er hard? 'fixequiv
                 "The congruence theorem failed: this is unexpected because ~
                  this should be automatic once the fixing theorem succeeds.  ~
                  Please try again with :verbosep t to diagnose the problem."))))))))

(defmacro deffixequiv-basic (fn arg type &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (let ((formals (fgetprop ',fn 'acl2::formals :none (w state))))
          (fixequiv-events
           (deffixequiv-basic-parse
             (cons ',fn formals)
             ',arg ',type ',keys state)))))))


#||

(deffixtype nat :pred natp :fix nfix :equiv nat-equiv :define t)

(logic)

(deffixequiv-basic nth acl2::n nat :verbosep t)

(program)
||#

(defun deffixcong-parse (in-equiv out-equiv form var keys state)
  (b* ((fixtypes (get-fixtypes-alist (w state)))
       (in-fixtype (find-fixtype-for-equiv in-equiv fixtypes)))
    (deffixequiv-basic-parse form var (fixtype->name in-fixtype)
      (list* :out-equiv out-equiv keys) state)))

(defmacro deffixcong (in-equiv out-equiv form var &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cdr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (fixequiv-events
         (deffixcong-parse ',in-equiv ',out-equiv ',form ',var ',keys state))))))

#||

(logic)

(defun inc (x) (+ 1 (nfix x)))

(deffixcong nat-equiv nat-equiv (inc x) x :hints(("Goal" :in-theory (enable nat-equiv))))


||#
    
