; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/da-base" :dir :system)

(program)
(set-state-ok t)

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
   inline
   equal
   topic    ;; preferred xdoc topic to link to this
   ))

(table fixtypes)

(defun get-fixtypes-alist (world)
  (cdr (assoc 'fixtype-alist (table-alist 'fixtypes world))))

(defun deffixtype-fn (name predicate fix equiv executablep definep inline equal no-rewrite-quoted-constant
                           topic verbosep hints forward)
  (if definep
      `(with-output ,@(and (not verbosep) '(:off :all :on acl2::error)) :stack :push
         (encapsulate nil
           (logic)
           (local (make-event
                   '(:or (with-output :stack :pop
                           (defthm tmp-deffixtype-idempotent
                             (equal (,fix (,fix x)) (,fix x))))
                     (value-triple
                      (er hard? 'deffixtype
                          "Failed to prove that ~x0 is idempotent.~%" ',fix)))))
           (,(cond ((not executablep) 'defun-nx)
                   ((not inline) 'defun)
                   (t            'defun-inline))
            ,equiv (x y)
            (declare (xargs :normalize nil
                            ,@(and executablep `(:guard (and (,predicate x) (,predicate y))))
                            :verify-guards ,executablep))
            (,equal (,fix x) (,fix y)))
           (local (in-theory '(,equiv tmp-deffixtype-idempotent
                                      booleanp-compound-recognizer)))
           (defequiv ,equiv :package :legacy)
           (defcong ,equiv equal (,fix x) 1 :package :legacy)
           (defthm ,(intern-in-package-of-symbol
                     (concatenate 'string
                                  (symbol-name fix) "-UNDER-" (symbol-name equiv))
                     equiv)
             (,equiv (,fix x) x)
             :rule-classes (:rewrite
                            . ,(and (not no-rewrite-quoted-constant)
                                    '(:rewrite-quoted-constant))))
           ,@(and forward
                  `((defthm ,(intern-in-package-of-symbol
                              (concatenate 'string "EQUAL-OF-" (symbol-name fix) "-1-FORWARD-TO-" (symbol-name equiv))
                              equiv)
                      (implies (equal (,fix x) y)
                               (,equiv x y))
                      :rule-classes :forward-chaining)
                    (defthm ,(intern-in-package-of-symbol
                              (concatenate 'string "EQUAL-OF-" (symbol-name fix) "-2-FORWARD-TO-" (symbol-name equiv))
                              equiv)
                      (implies (equal x (,fix y))
                               (,equiv x y))
                      :rule-classes :forward-chaining)
                    (defthm ,(intern-in-package-of-symbol
                              (concatenate 'string (symbol-name equiv) "-OF-" (symbol-name fix) "-1-FORWARD")
                              equiv)
                      (implies (,equiv (,fix x) y)
                               (,equiv x y))
                      :rule-classes :forward-chaining)
                    (defthm ,(intern-in-package-of-symbol
                              (concatenate 'string (symbol-name equiv) "-OF-" (symbol-name fix) "-2-FORWARD")
                              equiv)
                      (implies (,equiv x (,fix y))
                               (,equiv x y))
                      :rule-classes :forward-chaining)))
           (table fixtypes 'fixtype-alist
                  (cons (cons ',name ',(make-fixtype :name name
                                                     :pred predicate
                                                     :fix fix
                                                     :equiv equiv
                                                     :executablep executablep
                                                     :equiv-means-fixes-equal
                                                     ;; BOZO stupid ACL2 is so awful...
                                                     (if (and executablep inline)
                                                         (intern-in-package-of-symbol
                                                          (concatenate 'string (symbol-name equiv) "$INLINE")
                                                          equiv)
                                                       equiv)
                                                     :inline inline
                                                     :equal equal
                                                     :topic topic
                                                     ))
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
                       (cons (cons ',name
                                   ',(make-fixtype :name name
                                                   :pred predicate
                                                   :fix fix
                                                   :equiv equiv
                                                   :executablep executablep
                                                   :equiv-means-fixes-equal thmname
                                                   :inline inline
                                                   :equal equal
                                                   :topic topic
                                                   ))
                             (get-fixtypes-alist world))))))))


(defmacro deffixtype (name &key
                           pred
                           fix
                           equiv
                           (executablep 't)
                           define
                           verbosep
                           hints
                           forward
                           (no-rewrite-quoted-constant 'nil)
                           (inline 't)
                           (equal 'equal)
                           (topic 'nil topic-p))
; We contemplated making "equal" the default equivalence relation but decided
; against it.  See Github Issue 240 for relevant discussion.
  (declare (xargs :guard (and pred fix equiv)))
  (deffixtype-fn name pred fix equiv executablep define inline equal no-rewrite-quoted-constant
    (if topic-p topic name)
    verbosep hints forward))

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

(defun find-fixtype (typename alist)
  (or (find-fixtype-for-typename typename alist)
      (find-fixtype-for-pred typename alist)))

(defconst *deffixequiv-basic-keywords*
  '(:hints
    :skip-const-thm
    :skip-cong-thm
    :skip-ok
    :verbosep
    :out-equiv
    :other-var
    :thm-suffix
    :basename
    :pkg))


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
       (stobjname (and (fgetprop arg 'acl2::stobj nil world)
                       (acl2::congruent-stobj-rep arg world)))
       (fixtype (or (find-fixtype-for-typename type fixtype-al)
                    (find-fixtype-for-pred type fixtype-al)
                    (find-fixtype-for-typename stobjname fixtype-al)))
       (skip-ok (cdr (assoc :skip-ok kwd-alist)))
       ((unless fixtype)
        (if skip-ok
            (prog2$ (cw "Note: skipping ~x0 since its type ~x1 was not a ~
                         fixtype name or predicate~%" arg type)
                    nil)
          (raise "Not a fixtype name or predicate: ~x0" type)))
       (fix (fixtype->fix fixtype))
       (equiv (fixtype->equiv fixtype))
       (hints (getarg :hints nil kwd-alist))
       (skip-cong-thm (getarg :skip-cong-thm nil kwd-alist))
       ((unless (and (consp form) (symbolp (car form))))
        (raise "Form should be a function call term, but it's ~x0" form))
       (basename (getarg :basename (car form) kwd-alist))
       (pkg (or (getarg :pkg nil kwd-alist)
                basename))
       (pkg (if (equal (symbol-package-name pkg) "COMMON-LISP")
                'acl2::foo
              pkg))
       (out-equiv (getarg :out-equiv 'equal kwd-alist))
       (out-equiv-equiv-rune (acl2::equivalence-rune
                              (acl2::deref-macro-name out-equiv (macro-aliases world))
                              world))
       ((unless out-equiv-equiv-rune)
        (raise "Expected ~s0 to be a known equivalence relation" out-equiv))
       (under-out-equiv (if (eq out-equiv 'equal) ""
                          (concatenate 'string "-UNDER-" (symbol-name out-equiv))))
       (suffix (getarg :thm-suffix "" kwd-alist))
       (fix-thmname
        (intern-in-package-of-symbol
         (concatenate
          'string (symbol-name basename) "-OF-" (symbol-name fix) "-" (symbol-name arg)
          under-out-equiv suffix)
         pkg))
       (congruence-thmname
        (intern-in-package-of-symbol
         (concatenate
          'string (symbol-name basename) "-" (symbol-name equiv) "-CONGRUENCE-ON-" (symbol-name arg) under-out-equiv suffix)
         pkg))
       (argequiv (or (getarg :other-var nil kwd-alist)
                     (intern-in-package-of-symbol
                      (concatenate
                       'string (symbol-name arg) "-EQUIV")
                      pkg)))
       ((mv err tr-form) (acl2::translate-cmp form t nil nil 'deffixequiv-basic-parse
                                              world (acl2::default-state-vars t)))
       ((when err)
        (raise "Error translating form: ~@0" tr-form))
       (vars (all-vars tr-form))
       ((unless (and (symbolp arg)
                     (member arg vars)))
        (raise "Expected ~x0 to be among variables of ~x1" arg form))

       (subst-alist `((,arg . (,fix ,arg))))
       (fix-body `(,out-equiv ,(acl2::sublis-var subst-alist form)
                              ,form))
       (fix-thm `(defthm ,fix-thmname
                   ,fix-body
                   :hints ,hints))
       (cong-thm (and (not skip-cong-thm)
                      `(defthm ,congruence-thmname
                         (implies (,equiv ,arg ,argequiv)
                                  (,out-equiv ,form
                                              ,(acl2::sublis-var `((,arg . ,argequiv)) form)))
                         :hints (("Goal" :in-theory nil
                                  :do-not '(preprocess)
                                  :use ((:instance ,fix-thmname)
                                        (:instance ,fix-thmname (,arg ,argequiv))
                                        (:instance ,(fixtype->equiv-means-fixes-equal fixtype)
                                         (x ,arg) (y ,argequiv)))))
                         :rule-classes :congruence))))
    (make-fixequiv
     :form form
     :arg arg
     :type type
     :kwd-alist kwd-alist
     :fix-body fix-body
     :fix-thm fix-thm
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

       ,@(and x.cong-thm
              `((make-event
                 '(:or (with-output :on (error) ,x.cong-thm)
                   (with-output :on (error)
                     (value-triple
                      (er hard? 'fixequiv
                          "The congruence theorem failed: this is unexpected because ~
                  this should be automatic once the fixing theorem succeeds.  ~
                  Please try again with :verbosep t to diagnose the problem."))))))))))

(defmacro deffixequiv-basic (fn arg type &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (let ((formals (fgetprop ',fn 'acl2::formals :none (w state))))
          (fixequiv-events
           (deffixequiv-basic-parse
             (cons ',fn formals)
             ',arg ',type (cons (cons :pkg ',fn) ',keys) state)))))))


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
