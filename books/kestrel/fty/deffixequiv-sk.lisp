; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/defun-sk-queries" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination fixtype-p)
(verify-termination fixtype->fix$inline)
(verify-termination get-fixtypes-alist)
(verify-termination fixtype->pred$inline)
(verify-termination find-fixtype-for-pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 deffixequiv

 :item-wrld t

 :items

 ("@('fn') and @('args') are
   the homonymous inputs of @(tsee deffixequiv-sk)."

  "@('fn-witness') is the witness function associated to @('fn').
   See the option @(':skolem-name') of @(tsee defun-sk)."

  "@('fn-rule') is the rewrite rule associated to @('fn').
   See the option @(':thm-name') of @(tsee defun-sk)."

  "@('bvars') are the bound (i.e. quantified) variables of @('fn')."

  "@('args-names') is the list of argument names (without predicates)
   from the @('args') input."

  "@('args-alist') is an alist
   from the names of the arguments
   to their corresponding predicates.
   In other words, it is @('args') in alist form."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffixequiv-sk-lemma-inst-subst ((bvars symbol-listp)
                                         (index natp)
                                         (call pseudo-termp))
  :returns (instantiations true-list-listp)
  :short "Generate instantiations for the bound variables."
  :long
  (xdoc::topstring-p
   "If @('bvars') consists of the variables @('b1'), ... , @('bn'),
    we generate the list of doublets
    @('((b1 (mv-nth index call)) ... (bn (mv-nth index+n-1 call)))'),
    which is then used to create some lemma instances.
    The index is initially 0.")
  (cond ((endp bvars) nil)
        (t (cons `(,(car bvars) (mv-nth ,index ,call))
                 (deffixequiv-sk-lemma-inst-subst
                   (cdr bvars) (1+ index) call)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffixequiv-sk-lemma-insts-arg ((fn-rule symbolp)
                                        (fn-witness symbolp)
                                        (bvars symbol-listp)
                                        (args-names symbol-listp)
                                        (arg-name symbolp)
                                        (arg-fix symbolp))
  :guard (not (eq fn-witness 'quote))
  :returns (lemma-instances true-list-listp)
  :short "Generate lemma instances to prove the fixing of an argument."
  :long
  (xdoc::topstring-p
   "Each argument of the function has some associated lemma instances,
    which are then used in the hints to prove the fixing of the argument.
    This code generates the lemma instances for the argument
    whose name is @('arg-name') and whose fixer is @('arg-fix')
    (meaning the fixer for the type for the predicate
    paired to the argument in the @(':args') input.")
  (b* ((call1 (acl2::fcons-term fn-witness args-names))
       (call2 (acl2::fcons-term fn-witness
                                (subst (list arg-fix arg-name)
                                       arg-name
                                       args-names)))
       (instance1 `(:instance ,fn-rule
                    (,arg-name (,arg-fix ,arg-name))
                    ,@(if (= (len bvars) 1)
                          (list (list (car bvars) call1))
                        (deffixequiv-sk-lemma-inst-subst bvars 0 call1))))
       (instance2 `(:instance ,fn-rule
                    ,@(if (= (len bvars) 1)
                          (list (list (car bvars) call2))
                        (deffixequiv-sk-lemma-inst-subst bvars 0 call2)))))
    (list instance1 instance2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffixequiv-sk-lemma-insts-args ((fn-rule symbolp)
                                         (fn-witness symbolp)
                                         (bvars symbol-listp)
                                         (args-names symbol-listp)
                                         (args-alist acl2::symbol-symbol-alistp)
                                         (wrld plist-worldp))
  :guard (not (eq fn-witness 'quote))
  :returns (lemma-instances true-list-listp)
  :verify-guards nil
  :short "Generate lemma instances to prove the fixing of all the arguments."
  :long
  (xdoc::topstring-p
   "This loops through the alist of arguments
    and collects the lemma instances.")
  (b* (((when (endp args-alist)) nil)
       (arg (car args-alist))
       (arg-name (car arg))
       (arg-pred (cdr arg))
       (arg-fty-info (find-fixtype-for-pred arg-pred (get-fixtypes-alist wrld)))
       (arg-fix (fixtype->fix arg-fty-info))
       (arg-lemma-instances (deffixequiv-sk-lemma-insts-arg
                              fn-rule fn-witness bvars args-names
                              arg-name arg-fix))
       (rest-lemma-instances (deffixequiv-sk-lemma-insts-args
                               fn-rule fn-witness bvars args-names
                               (cdr args-alist) wrld)))
    (append arg-lemma-instances rest-lemma-instances)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffixequiv-sk-hints ((fn symbolp)
                              (fn-rule symbolp)
                              (fn-witness symbolp)
                              (bvars symbol-listp)
                              (args-alist acl2::symbol-symbol-alistp)
                              (wrld plist-worldp))
  :guard (not (eq fn-witness 'quote))
  :returns (hints true-listp)
  :verify-guards nil
  :short "Generate the hints for @(tsee deffixequiv)."
  :long
  (xdoc::topstring-p
   "The hints consist of
    a @(':use') hints with the lemma instances for all the arguments
    and an @(':in-theory') hints to enable @('fn') and disable @('fn-rule').")
  (b* ((args-names (strip-cars args-alist)))
    `(("Goal"
       :in-theory (e/d (,fn) (,fn-rule))
       :use ,(deffixequiv-sk-lemma-insts-args
               fn-rule fn-witness bvars args-names args-alist wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deffixequiv-sk-fn (fn args (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Process the inputs and generate the @(tsee deffixequiv)."
  (b* (((unless (acl2::defun-sk-namep fn wrld))
        (raise "The first input, ~x0, must be a DEFUN-SK function symbol." fn))
       (fn-rule (acl2::defun-sk-rewrite-name fn wrld))
       (fn-witness (acl2::defun-sk-witness fn wrld))
       (bvars (acl2::defun-sk-bound-vars fn wrld))
       ((unless (acl2::doublet-listp args))
        (raise "The :ARGS input, ~x0, must be a true list of doublets." args))
       (args-alist (acl2::doublets-to-alist args))
       ((unless (acl2::symbol-symbol-alistp args-alist))
        (raise "The :ARGS input, ~x0, ~
                must be a true list of doublets of symbols." args))
       (hints (deffixequiv-sk-hints
                fn fn-rule fn-witness bvars args-alist wrld)))
    `(fty::deffixequiv ,fn :args ,args :hints ,hints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deffixequiv-sk-macro-definition
  :short "Definition of the @('deffixequiv-sk') macro."
  :long (xdoc::topstring-@def "deffixequiv-sk")
  (defmacro deffixequiv-sk (fn &key args)
    `(make-event (deffixequiv-sk-fn ',fn ',args (w state)))))
