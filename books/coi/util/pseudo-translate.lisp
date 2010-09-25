(in-package "ACL2")

;; Here we copy the translate function from ACL2 and remove the check
;; for function existence.  This is really useful when you want to do
;; macro expansion but don't really care (yet) about the underlying
;; functions.

;; The changes were quite minor and are marked by "CHANGE".  We
;; renamed all of the functions, of course, but the only substantial
;; changes were to remove the call to "(ev ..)" and to replace the
;; undefined function call check with a recursive call to translate.

;; Modified 9/24/10 by Matt Kaufmann to reflect changes in the definitions of
;; translate11 etc.

(set-state-ok t)

(program)

(mutual-recursion

(defun translate11x-flet-alist (form fives stobjs-out bindings known-stobjs
                                    flet-alist ctx w state)
  (cond ((endp fives)
         (trans-value flet-alist))
        (t
         (trans-er-let*
          ((flet-entry
            (translate11x-flet-alist1 form (car fives) stobjs-out bindings
                                     known-stobjs flet-alist ctx w state))
           (flet-entries
            (translate11x-flet-alist  form (cdr fives) stobjs-out bindings
                                     known-stobjs flet-alist ctx w state)))
          (trans-value (cons flet-entry flet-entries))))))

(defun translate11x-flet-alist1 (form five stobjs-out bindings known-stobjs
                                     flet-alist ctx w state)
  (let* ((name (car five))
         (bound-vars (cadr five))
         (edcls (fourth five))
         (body (fifth five))
         (new-stobjs-out
          (if (eq stobjs-out t)
              t
            (genvar name (symbol-name name) nil (strip-cars bindings)))))
    (cond
     ((member-eq name '(flet with-local-stobj throw-raw-ev-fncall
                         untrace$-fn-general))

; This check may not be necessary, because of our other checks.  But the
; symbols above are not covered by our check for the 'predefined property.

      (trans-er+ form ctx
                 "An FLET form has attempted to bind ~x0.  However, this ~
                  symbol must not be FLET-bound."
                 name))
     ((getprop name 'predefined nil 'current-acl2-world w)
      (trans-er+ form ctx
                 "An FLET form has attempted to bind ~x0, which is predefined ~
                  in ACL2 hence may not be FLET-bound."
                 name))
#||
     #-acl2-loop-only
     ((or (special-form-or-op-p name)
          (and (or (macro-function name)
                   (fboundp name))
               (not (getprop name 'macro-body nil 'current-acl2-world w))
               (eq (getprop name 'formals t 'current-acl2-world w) t)))
      (prog2$ (er hard ctx
                  "It is illegal to FLET-bind ~x0, because it is defined as a ~
                   ~s1 in raw Lisp~#2~[~/ but not in the ACL2 loop~]."
                  name
                  (cond ((special-form-or-op-p name) "special operator")
                        ((macro-function name) "macro")
                        (t "function"))
                  (if (special-form-or-op-p name) 0 1))
              (mv t
                  nil ; empty "message": see the Essay on Context-message Pairs
                  nil)))
||#
     (t
      (trans-er-let*
       ((tdcls (translate11x-lst (translate-dcl-lst edcls w)
                                nil           ;;; '(nil ... nil)
                                bindings
                                nil ; inclp
                                known-stobjs
                                "in a DECLARE form in an FLET binding"
                                flet-alist form ctx w state))
        (tbody (translate11x body new-stobjs-out
                            (if (eq stobjs-out t)
                                bindings
                              (translate-bind new-stobjs-out new-stobjs-out
                                              bindings))
                            nil known-stobjs
                            flet-alist form ctx w state)))
       (let ((stobjs-bound
              (collect-non-x nil (compute-stobj-flags bound-vars
                                                      known-stobjs
                                                      w)))
             (used-vars (union-eq (all-vars tbody)
                                  (all-vars1-lst tdcls nil)))
             (ignore-vars (ignore-vars edcls))
             (ignorable-vars (ignorable-vars edcls))
             (stobjs-out (translate-deref new-stobjs-out bindings)))
         (cond

; We skip the following case, where stobjs-out is not yet bound to a consp and
; some formal is a stobj, in favor of the next, which removes the stobj
; criterion.  But we leave this case here as a comment in case we ultimately
; find a way to eliminate the more sweeping case after it.

;         ((and (not (eq stobjs-out t))
;               stobjs-bound
;               (not (consp stobjs-out)))
;          (trans-er ctx
;                    "~@0"
;                    (unknown-binding-msg
;                     stobjs-bound
;                     (msg "the formals of an FLET binding for function ~x0"
;                          name)
;                     "the body of this FLET binding"
;                     "that body")))

          ((and (not (eq stobjs-out t))
                (not (consp stobjs-out)))

; Warning: Before changing this case, see the comment above about the
; commented-out preceding case.

           (trans-er+ form ctx
                      "We are unable to determine the output signature for an ~
                       FLET-binding of ~x0.  You may be able to remedy the ~
                       situation by rearranging the order of the branches of ~
                       an IF and/or rearranging the order of the presentation ~
                       of a clique of mutually recursive functions.  If you ~
                       believe you have found an example on which you believe ~
                       ACL2 should be able to complete this translation, ~
                       please send such an example to the ACL2 implementors."
                     name))
          ((and (not (eq stobjs-out t))
                stobjs-bound
                (not (subsetp-eq stobjs-bound
                                 (collect-non-x nil stobjs-out))))
           (let ((stobjs-returned (collect-non-x nil stobjs-out)))
             (trans-er+ form ctx
                        "The single-threaded object~#0~[ ~&0 is a formal~/s ~
                         ~&0 are formals~] of an FLET-binding of ~x3.  It is ~
                         a requirement that ~#0~[this object~/these objects~] ~
                         be among the outputs of the body of that binding, ~
                         but ~#0~[it is~/they are~] not.  That body returns ~
                         ~#1~[no single-threaded objects~/the single-threaded ~
                         object ~&2~/the single-threaded objects ~&2~]."
                       (set-difference-eq stobjs-bound stobjs-returned)
                       (zero-one-or-more stobjs-returned)
                       stobjs-returned
                       name)))
          ((intersectp-eq used-vars ignore-vars)
           (trans-er+ form ctx
                      "Contrary to the declaration that ~#0~[it is~/they ~
                       are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 are~] ~
                       used in the body of an FLET-binding of ~x1, whose ~
                       formal parameter list includes ~&2."
                     (intersection-eq used-vars ignore-vars)
                     name
                     bound-vars))
          (t
           (let* ((diff (set-difference-eq
                         bound-vars
                         (union-eq used-vars
                                   (union-eq ignorable-vars
                                             ignore-vars))))
                  (ignore-ok
                   (if (null diff)
                       t
                     (cdr (assoc-eq
                           :ignore-ok
                           (table-alist 'acl2-defaults-table w))))))
             (cond
              ((null ignore-ok)
               (trans-er+ form ctx
                          "The variable~#0~[ ~&0 is~/s ~&0 are~] not used in ~
                           the body of the LET expression that binds ~&1.  ~
                           But ~&0 ~#0~[is~/are~] not declared IGNOREd or ~
                           IGNORABLE.  See :DOC set-ignore-ok."
                         diff
                         bound-vars))
              (t
               (prog2$
                (cond
                 ((eq ignore-ok :warn)
                  (warning$-cmp ctx "Ignored-variables"
                                "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                 used in the body of an FLET-binding of ~x1 ~
                                 that binds ~&2.  But ~&0 ~#0~[is~/are~] not ~
                                 declared IGNOREd or IGNORABLE.  See :DOC ~
                                 set-ignore-ok."
                                diff
                                name
                                bound-vars))
                 (t nil))
                (let* ((tbody
                        (cond
                         (tdcls
                          (let ((guardian (dcl-guardian tdcls)))
                            (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                   tbody)
                                  (t
                                   (fcons-term* 'prog2$
                                                guardian
                                                tbody)))))
                         (t tbody)))
                       (body-vars (all-vars tbody))
                       (extra-body-vars (set-difference-eq
                                         body-vars
                                         bound-vars)))
                  (cond
                   (extra-body-vars
  
; Warning: Do not eliminate this error without thinking about the possible role
; of variables that are declared special in Common Lisp.  There might not be
; such an issue, but we haven't thought about it.

                    (trans-er+ form ctx
                               "The variable~#0~[ ~&0 is~/s ~&0 are~] used in ~
                                the body of an FLET-binding of ~x1 that only ~
                                binds ~&2.  In ACL2, every variable occurring ~
                                in the body of an FLET-binding, (fn vars ~
                                body), must be in vars, i.e., a formal ~
                                parameter of that binding.  The ACL2 ~
                                implementors may be able to remove this ~
                                restriction, with some effort, if you ask."
                              extra-body-vars
                              name
                              bound-vars))
                   (t
                    (trans-value
                     (list* name
                            (make-lambda bound-vars tbody)
                            stobjs-out)
                     (if (eq new-stobjs-out t)
                         bindings
                       (delete-assoc-eq new-stobjs-out
                                        bindings))))))))))))))))))

(defun translate11x-flet (x stobjs-out bindings inclp known-stobjs flet-alist
                           ctx w state)
  (cond
   ((not (eql (length x) 3))
    (trans-er ctx
              "An FLET form must have the form (flet bindings body), where ~
               bindings is a list of local function definitions, but ~x0 does ~
               not have this form.  See :DOC flet."
              x))
   (t
    (mv-let
     (erp fives)
     (chk-defuns-tuples-cmp (cadr x) t ctx w state)
     (mv-let
      (erp ignored-val)
      (if erp ; erp is a ctx and fives is a msg
          (mv erp fives)

; Note that we do not need to call chk-xargs-keywords, since
; acceptable-dcls-alist guarantees that xargs is illegal.

        (chk-no-duplicate-defuns-cmp (strip-cars fives) ctx))
      (declare (ignore ignored-val))
      (cond
       (erp (trans-er ctx
                      "The above error indicates a problem with the form ~p0."
                      x))
       (t
        (trans-er-let*
         ((flet-alist (translate11x-flet-alist x fives stobjs-out bindings
                                              known-stobjs flet-alist ctx w
                                              state)))
         (translate11x (car (last x)) ; (nth 2 x) as of this writing
                      stobjs-out bindings inclp known-stobjs flet-alist x
                      ctx w state)))))))))

(defun translate11x-mv-let (x stobjs-out bindings inclp known-stobjs
                             local-stobj local-stobj-creator flet-alist
                             ctx w state)

; X is a cons whose car is 'MV-LET.  This function is nothing more than the
; restriction of function translate11x to that case, except that if local-stobj
; is not nil, then we are in the process of translating
; (with-local-stobj local-stobj x local-stobj-creator), where we know that
; local-stobj-creator is the creator function for the stobj local-stobj.

; Warning:  If the final form of a translated mv-let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

  (cond
   ((not (and (true-listp (cadr x))
              (> (length (cadr x)) 1)))
    (trans-er ctx
              "The first form in an MV-LET expression must be a true list of ~
               length 2 or more.  ~x0 does not meet these conditions."
              (cadr x)))
   ((not (arglistp (cadr x)))
    (mv-let (culprit explan)
            (find-first-bad-arg (cadr x))
            (trans-er ctx
                      "The first form in an MV-LET expression must be a list ~
                       of distinct variables of length 2 or more, but ~x0 ~
                       does not meet these conditions.  The element ~x1 ~@2."
                      x culprit explan)))
   ((not (>= (length x) 4))
    (trans-er ctx
              "An MV-LET expression has the form (mv-let (var var var*) form ~
               dcl* form) but ~x0 does not have sufficient length to meet ~
               this condition."
              x))
   (t
    (let* ((bound-vars (cadr x))
           (producer-known-stobjs
            (if (and local-stobj (not (eq known-stobjs t)))
                (add-to-set-eq local-stobj known-stobjs)
              known-stobjs))
           (bound-stobjs-out (if (and (eq stobjs-out t)

; If local-stobj is true (hence we are being called by translate in the case of
; a with-local-stobj term), then we want to do syntax-checking that we wouldn't
; normally do with stobjs-out = t, because we don't have a spec for
; with-local-stobj in the case that this syntax-checking is turned off.

                                      (not local-stobj))
                                 t
                               (compute-stobj-flags bound-vars
                                                    producer-known-stobjs
                                                    w)))
           (stobjs-bound0 (if (eq bound-stobjs-out t)
                              nil
                            (collect-non-x nil bound-stobjs-out)))
           (stobjs-bound

; Stobjs-bound is perhaps an odd name for this variable, since if there is a
; local stobj, then literally speaking it is bound -- though we do not consider
; it so here.  Really, stobjs-bound is the list of stobj names that we require
; to come out of the mv-let.

            (if local-stobj
                (remove1-eq local-stobj stobjs-bound0)
              stobjs-bound0))
           (body (car (last x))))
      (mv-let
       (erp edcls)
       (collect-declarations-cmp (butlast (cdddr x) 1)
                                 (cadr x) 'mv-let state ctx)
       (cond
        (erp (trans-er erp edcls))
        (t
         (trans-er-let*
          ((tcall (translate11x (caddr x)
                               bound-stobjs-out
                               bindings inclp
                               producer-known-stobjs
                               flet-alist x ctx w state))
           (tdcls (translate11x-lst (translate-dcl-lst edcls w)
                                   (if (eq stobjs-out t)
                                       t
                                     nil)          ;;; '(nil ... nil)
                                   bindings
                                   inclp known-stobjs
                                   "in a DECLARE form in an MV-LET"
                                   flet-alist x ctx w state))
           (tbody (translate11x body stobjs-out bindings inclp
                               known-stobjs flet-alist x ctx w state)))
          (let ((used-vars (union-eq (all-vars tbody)
                                     (all-vars1-lst tdcls nil)))
                (ignore-vars (if local-stobj
                                 (cons local-stobj (ignore-vars edcls))
                               (ignore-vars edcls)))
                (ignorable-vars (ignorable-vars edcls))
                (stobjs-out (translate-deref stobjs-out bindings)))
            (cond
             ((and local-stobj
                   (not (member-eq local-stobj ignore-vars)))
              (trans-er+ x ctx
                         "A local-stobj must be declared ignored, but ~x0 is ~
                          not.  See :DOC with-local-stobj."
                         local-stobj))
             ((and stobjs-bound
                   (not (consp stobjs-out)))
              (trans-er+ x ctx
                         "~@0"
                         (unknown-binding-msg
                          stobjs-bound "an MV-LET" "the MV-LET" "the MV-LET")))
             ((and stobjs-bound
                   (not (subsetp stobjs-bound
                                 (collect-non-x nil stobjs-out))))
              (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                (trans-er+ x ctx
                           "The single-threaded object~#0~[ ~&0 has~/s ~&0 ~
                            have~] been bound in an MV-LET.  It is a ~
                            requirement that ~#0~[this object~/these ~
                            objects~] be among the outputs of the MV-LET, but ~
                            ~#0~[it is~/they are~] not.  The MV-LET returns ~
                            ~#1~[no single-threaded objects~/the ~
                            single-threaded object ~&2~/the single-threaded ~
                            objects ~&2~]."
                           (set-difference-eq stobjs-bound stobjs-returned)
                           (zero-one-or-more stobjs-returned)
                           stobjs-returned)))
             ((intersectp-eq used-vars ignore-vars)
              (trans-er+ x ctx
                         "Contrary to the declaration that ~#0~[it is~/they ~
                          are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 ~
                          are~] used in the MV-LET expression that binds ~&1."
                         (intersection-eq used-vars ignore-vars)
                         bound-vars))
             (t
              (let* ((diff (set-difference-eq
                            bound-vars
                            (union-eq used-vars
                                      (union-eq ignorable-vars
                                                ignore-vars))))
                     (ignore-ok
                      (if (null diff)
                          t
                        (cdr (assoc-eq
                              :ignore-ok
                              (table-alist 'acl2-defaults-table w))))))
                (cond
                 ((null ignore-ok)
                  (trans-er+ x ctx
                             "The variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                              in the body of the MV-LET expression that binds ~
                              ~&1.  But ~&0 ~#0~[is~/are~] not declared ~
                              IGNOREd or IGNORABLE.  See :DOC set-ignore-ok."
                             diff
                             bound-vars))
                 (t
                  (prog2$
                   (cond
                    ((eq ignore-ok :warn)
                     (warning$-cmp ctx "Ignored-variables"
                                   "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                    used in the body of the MV-LET expression ~
                                    that binds ~&1. But ~&0 ~#0~[is~/are~] ~
                                    not declared IGNOREd or IGNORABLE.  See ~
                                    :DOC set-ignore-ok."
                                   diff
                                   bound-vars))
                    (t nil))
                   (let* ((tbody
                           (cond
                            (tdcls
                             (let ((guardian (dcl-guardian tdcls)))
                               (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                      tbody)
                                     (t
                                      (fcons-term* 'prog2$ guardian tbody)))))
                            (t tbody)))
                          (body-vars (all-vars tbody))
                          (extra-body-vars
                           (set-difference-eq body-vars (cadr x)))
                          (vars (all-vars1 tcall extra-body-vars))
                          (mv-var (genvar 'genvar "MV" nil vars)))
                     (trans-value
                      (list* (make-lambda
                              (cons mv-var extra-body-vars)
                              (cons (make-lambda
                                     (append (cadr x)
                                             extra-body-vars)
                                     tbody)

; When the rewriter encounters ((lambda (... xi ...) body) ... actuali
; ...), where xi is ignored and actuali is in the corresponding
; position, we'd like to tell the rewriter not to bother rewriting
; actuali.  We do this by wrapping a hide around it.  This typically
; only happens with MV-LET expressions, though we do it for LET
; expressions as well.

                                    (append (hide-ignored-actuals
                                             ignore-vars
                                             (cadr x)
                                             (mv-nth-list
                                              mv-var 0
                                              (length (cadr x))))
                                            extra-body-vars)))
                             (if local-stobj
                                 (let ((tcall-vars
                                        (remove1-eq local-stobj
                                                    (all-vars tcall))))
                                   (cons (make-lambda
                                          (cons local-stobj tcall-vars)
                                          tcall)
                                         (cons (list local-stobj-creator)
                                               tcall-vars)))
                               tcall)
                             extra-body-vars))))))))))))))))))

(defun translate11x-wormhole-eval (x y z bindings inclp flet-alist ctx w state)

; The three arguments of wormhole-eval are x y and z.  Here, z has been
; translated but x and y have not been.  We want to insure that x and y are
; well-formed quoted forms of a certain shape.  We don't actually care about z
; and ignore it!  We translated it just for sanity's sake: no point in allowing
; the user ever to write an ill-formed term in a well-formed term.

  (declare (ignore z))
  (cond
   ((not (and (true-listp x)
              (equal (length x) 2)
              (equal (car x) 'quote)))
    (trans-er ctx
              "The first argument to wormhole-eval must be a QUOTE expression ~
               containing the name of the wormhole in question and ~x0 is not ~
               quoted."
              x))
   ((not (and (true-listp y)
              (equal (length y) 2)
              (equal (car y) 'quote)))
    (trans-er ctx
              "The second argument to wormhole-eval must be a QUOTE ~
               expression containing a LAMBDA expression and ~x0 is not ~
               quoted."
              y))
   ((not (and (true-listp (cadr y))
              (equal (length (cadr y)) 3)
              (equal (car (cadr y)) 'lambda)
              (true-listp (cadr (cadr y)))
              (<= (length (cadr (cadr y))) 1)))
    (trans-er ctx
              "The second argument to wormhole-eval must be a QUOTE ~
               expression containing a LAMBDA expression with at most one ~
               formal, e.g., the second argument must be either of the form ~
               '(LAMBDA () body) or of the form (LAMBDA (v) body).  But ~x0 ~
               is of neither form."
              y))
   (t (let ((lambda-formals (cadr (cadr y)))
            (lambda-body (caddr (cadr y))))
        (cond
         ((not (arglistp lambda-formals))
          (mv-let (culprit explan)
                  (find-first-bad-arg lambda-formals)
                  (trans-er ctx
                            "The quoted lambda expression, ~x0, supplied to ~
                             wormhole-eval is improper because it binds ~x1, ~
                             which ~@2."
                            y culprit explan)))
         (t
          (let ((whs (car lambda-formals)))

; Whs is either nil or the legal variable name bound by the lambda.

            (mv-let
               (body-erp tlambda-body body-bindings)
               (translate11x lambda-body
                            '(nil)           ; stobjs-out
                            nil              ; bindings
                            inclp
                            '(state) ; known-stobjs
                            flet-alist
                            x ctx w state)
               (declare (ignore body-bindings))
               (cond
                (body-erp (mv body-erp tlambda-body bindings))
                ((and whs
                      (not (member-eq whs (all-vars tlambda-body))))
                 (trans-er ctx
                           "The form ~x0 is an improper quoted lambda ~
                            expression for wormhole-eval because it binds but ~
                            does not use ~x1, which is understood to be the ~
                            name you're giving to the current value of the ~
                            wormhole status for the wormhole in question."
                           y whs))
                (t

; We replace the second argument of wormhole-eval by a possibly different
; quoted object.  But that is ok because wormhole-eval returns nil no matter
; what objects we pass it.  We also compute a form with the same free vars as
; the lambda expression and stuff it in as the third argument, throwing away whatever
; the user supplied.

                 (trans-value
                  (fcons-term* 'wormhole-eval
                               x
                               (list 'quote
                                     (if whs
                                         `(lambda (,whs) ,tlambda-body)
                                         `(lambda () ,tlambda-body)))
                               (name-dropper
                                (if whs
                                    (remove1-eq whs (all-vars tlambda-body))
                                    (all-vars tlambda-body)))))))))))))))

(defun translate11x-call (form fn args stobjs-out stobjs-out2 bindings inclp
                              known-stobjs msg flet-alist ctx w state)
  (let ((stobjs-in
         (if (consp fn)
             (compute-stobj-flags (lambda-formals fn)
                                  known-stobjs
                                  w)
           (stobjs-in fn w))))
    (cond
     ((consp stobjs-out)
      (cond
       ((consp stobjs-out2)
        (cond
         ((not (equal stobjs-out stobjs-out2))
          (trans-er+ form ctx
                     "It is illegal to invoke ~@0 here because of a signature ~
                      mismatch.  This function returns a result of shape ~x1 ~
                      where a result of shape ~x2 is required."
                     (if (consp fn) msg (msg "~x0" fn))
                     (prettyify-stobjs-out stobjs-out2)
                     (prettyify-stobjs-out stobjs-out)))
         (t (trans-er-let*

; We handle the special translation of wormhole-eval both here, when stobjs-out
; is known, and below, where it is not.  Of course, stobjs-out2 (for
; wormhole-eval) is fixed: (nil).  Keep this code in sync with that below.

; The odd treatment of wormhole-eval's first two arguments below is due to the fact
; that we actually don't want to translate them.  We will insist that they actually
; be quoted forms, not macro calls that expand to quoted forms.  So we put bogus nils
; in here and then swap back the untranslated args below.

             ((targs (translate11x-lst (if (eq fn 'wormhole-eval)
                                          (list *nil* *nil* (nth 2 args))
                                          args)
                                      stobjs-in
                                      bindings
                                      (compute-inclp-lst
                                       stobjs-in
                                       stobjs-out)
                                      known-stobjs
                                      msg flet-alist form ctx w state)))
             (cond ((eq fn 'wormhole-eval)
                    (translate11x-wormhole-eval (car args)
                                               (cadr args)
                                               (caddr targs)
                                               bindings inclp flet-alist ctx w state))
                   (t (trans-value (fcons-term fn targs))))))))
       (t
        (let ((bindings
               (translate-bind stobjs-out2 stobjs-out bindings)))
          (trans-er-let*
           ((args (translate11x-lst args
                                   stobjs-in
                                   bindings inclp known-stobjs
                                   msg flet-alist form ctx w state)))
           (trans-value (fcons-term fn args)))))))
     ((consp stobjs-out2)
      (let ((bindings
             (translate-bind stobjs-out stobjs-out2 bindings)))
        (trans-er-let*
         ((targs (translate11x-lst (if (eq fn 'wormhole-eval)
                                      (list *nil* *nil* (nth 2 args))
                                      args)
                                  stobjs-in
                                  bindings inclp known-stobjs
                                  msg flet-alist form ctx w state)))
         (cond ((eq fn 'wormhole-eval)
                (translate11x-wormhole-eval (car args)
                                           (cadr args)
                                           (caddr targs)
                                           bindings inclp flet-alist ctx w state))
               (t (trans-value (fcons-term fn targs)))))))
     (t (let ((bindings
               (translate-bind stobjs-out2 stobjs-out bindings)))
          (trans-er-let*
           ((args (translate11x-lst args
                                   stobjs-in
                                   bindings inclp known-stobjs
                                   msg flet-alist form ctx w state)))
           (trans-value (fcons-term fn args))))))))

(defun translate11x (x stobjs-out bindings inclp known-stobjs flet-alist
                      cform ctx w state)

; Bindings is an alist binding symbols either to their corresponding
; STOBJS-OUT or to symbols.  The only symbols used are (about-to-be
; introduced) function symbols or the keyword :STOBJS-OUT.  When fn is
; bound to gn it means we have determined that the STOBJS-OUT of fn is
; that of gn.  We allow fn to be bound to itself -- indeed, it is
; required initially!  (This allows bindings to double as a recording
; of all the names currently being introduced.)

; Stobjs-out is one of:

; t              - meaning we do not care about multiple-value or stobj 
;                  restrictions (as when translating proposed theorems).
; (s1 s2 ... sk) - a list of 1 or more stobj flags indicating where stobjs
;                  are returned in the translation of x
; fn             - a function name, indicating that we are trying to deduce 
;                  the stobjs-out setting for fn from some output branch, x,
;                  of its body, as we translate.  We also enforce prohibitions
;                  against the use of DEFUN, IN-PACKAGE, etc inside bodies.
; :stobjs-out    - like a function name, except we know we are NOT in a defun
;                  body and allow DEFUN, IN-PACKAGE, etc.

; See the essay on STOBJS-IN and STOBJS-OUT, above.

; When stobjs-out is a symbol, it must be dereferenced through bindings
; before using it.  [One might think that we follow the convention of keeping
; it dereferenced, e.g., by using the new value whenever we bind it.
; But that is hard since the binding may come deep in some recursive
; call of translate.]

; T always deferences to t and nothing else dereferences to t.  So you
; can check (eq stobjs-out t) without dereferencing to know whether we
; care about the stobjs-out conditions.

; Inclp is t or nil and changes the precise meaning of a non-nil stobj
; flag, $s.  If inclp is nil, then $s means that the given stobj MUST
; appear in the corresponding slot.  If inclp is t, then $s means that
; the given stobj MAY appear in the corresponding slot.  At the
; moment, inclp is always set to nil initially and is set to t only
; when this function, in some recursive call, has determined that it
; is safe to allow non-live stobjs into stobj positions.

; Known-stobjs is a subset of the list of all stobjs known in world w,
; or else known-stobjs is T and denotes all the stobjs in w.  A name
; is considered a stobj iff it is in known-stobjs.  This allows us to
; implement the :STOBJS declaration in defuns, by which the user can
; declare the stobjs in a function.

; The cform argument is a form that provides context -- it is the one to be
; printed by trans-er+ when there isn't another obvious contextual form to
; print.  (Often x carries enough context.)

; Keep this in sync with oneify.

  (cond
   ((f-big-clock-negative-p state)
    (trans-er+ x ctx
               "Translate ran out of time!  This is almost certainly caused ~
                by a loop in macro expansion."))

; We handle both the (quote x) and atom case together because both
; have the same effects on calculating the stobjs-out.

   ((or (atom x) (eq (car x) 'quote))
    (let* ((stobjs-out (translate-deref stobjs-out bindings))
           (vc (legal-variable-or-constant-namep x))
           (const (and (eq vc 'constant)
                       (defined-constant x w))))
      (cond
       ((and (symbolp x)
             (not (keywordp x))
             (not vc))
        (trans-er+? cform x
                    ctx
                    "The symbol ~x0 is being used as a variable or constant ~
                     symbol but does not have the proper syntax.  Such names ~
                     must ~@1.  See :DOC name."
                    x
                    (tilde-@-illegal-variable-or-constant-name-phrase x)))
       ((and (eq vc 'constant)
             (not const))
        (trans-er+? cform x
                    ctx
                    "The symbol ~x0 (in package ~x1) has the syntax of a ~
                     constant, but has not been defined."
                    x
                    (symbol-package-name x)))

       ((and (not (atom x)) (not (termp x w)))
        (trans-er+? cform x
                    ctx
                    "The proper form of a quoted constant is (quote x), but ~
                     ~x0 is not of this form."
                    x))

; We now know that x denotes a term.  Let transx be that term.

       (t (let ((transx (cond ((keywordp x) (kwote x))
                              ((symbolp x)
                               (cond ((eq vc 'constant) const)
                                     (t x)))
                              ((atom x) (kwote x))
                              (t x))))

; Now consider the specified stobjs-out.  It is fully dereferenced.
; So there are three cases: (1) we don't care about stobjs-out, (2)
; stobjs-out tells us exactly what kind of output is legal here and we
; must check, or (3) stobjs-out is an unknown but we now know its
; value and can bind it.

            (cond
             ((eq stobjs-out t)              ;;; (1)
              (trans-value transx))
             ((consp stobjs-out)             ;;; (2)
              (cond
               ((cdr stobjs-out)
                (trans-er+? cform x
                            ctx
                            "One value, ~x0, is being returned where ~x1 ~
                             values were expected."
                            x (length stobjs-out)))
               ((and (null (car stobjs-out))
                     (stobjp transx known-stobjs w))

; Warning: We ignore the inclp flag in this case.  Even if inclp = t,
; which permits non-stobjs into stobj slots, we still prohibit stobjs
; from going into non-stobj slots.  Why?  Because the stobj in
; question might be a live one and might be treated ``surprisingly''
; by non-stobj functions, e.g., we might take the car of
; *the-live-state*.

                (trans-er+? cform x
                            ctx
                            "A single-threaded object, namely ~x0, is being ~
                             used where an ordinary object is expected."
                            transx))
               ((and (car stobjs-out)
                     (not (or inclp
                              (eq (car stobjs-out) transx))))
                (cond
                 ((stobjp transx known-stobjs w)
                  (trans-er+? cform x
                              ctx
                              "The single-threaded object ~x0 is being used ~
                               where the single-threaded object ~x1 was ~
                               expected."
                              transx (car stobjs-out)))
                 (t
                  (trans-er+? cform x
                              ctx
                              "The ordinary object ~x0 is being used where ~
                               the single-threaded object ~x1 was expected."
                              transx (car stobjs-out)))))
               (t (trans-value transx))))
             (t                              ;;; (3)
              (trans-value transx
                           (translate-bind
                            stobjs-out
                            (list (if (stobjp transx known-stobjs w) transx nil))
                            bindings)))))))))
   ((not (true-listp (cdr x)))
    (trans-er ctx
              "Function applications in ACL2 must end in NIL.  ~x0 is ~
               not of this form."
              x))
   ((not (symbolp (car x)))
    (cond ((or (not (consp (car x)))
               (not (eq (caar x) 'lambda)))
           (trans-er ctx
                     "Function applications in ACL2 must begin with a ~
                      symbol or LAMBDA expression.  ~x0 is not of ~
                      this form."
                     x))
          ((or (not (true-listp (car x)))
               (not (>= (length (car x)) 3))
               (not (true-listp (cadr (car x)))))
           (trans-er ctx
                     "Illegal LAMBDA expression: ~x0."
                     x))
          ((not (= (length (cadr (car x))) (length (cdr x))))
           (trans-er+ x ctx
                      "The LAMBDA expression ~x0 takes ~#1~[no arguments~/1 ~
                       argument~/~x2 arguments~] and is being passed ~#3~[no ~
                       arguments~/1 argument~/~x4 arguments~]."
                      (car x)
                      (zero-one-or-more (length (cadr (car x))))
                      (length (cadr (car x)))
                      (zero-one-or-more (length (cdr x)))
                      (length (cdr x))))
          (t (translate11x
              (list* 'let
                     (listlis (cadr (car x)) (cdr x))
                     (cddr (car x)))
              stobjs-out bindings inclp known-stobjs flet-alist x ctx w
              state))))
   ((and (not (eq stobjs-out t)) (eq (car x) 'mv))

; If stobjs-out is t we let normal macroexpansion handle mv.

    (let ((stobjs-out (translate-deref stobjs-out bindings)))
      (cond
       ((let ((len (length (cdr x))))
          (or (< len 2)
              (> len

; Keep the number below (which also occurs in the string) equal to the value of
; raw Lisp constant *number-of-return-values*.

                 32)))
        (cond ((< (length (cdr x)) 2)
               (trans-er ctx
                         "MV must be given at least two arguments, but ~x0 has ~
                          fewer than two arguments."
                         x))
              (t
               (trans-er ctx
                         "MV must be given no more than 32 arguments; thus ~x0 ~
                          has too many arguments."
                         x))))
       ((consp stobjs-out)
        (cond
         ((not (int= (length stobjs-out) (length (cdr x))))
          (trans-er+? cform x
                      ctx
                      "The expected number of return values for ~x0 is ~x1 ~
                       but the actual number of return values is ~x2."
                      x
                      (length stobjs-out)
                      (length (cdr x))))
         (t
          (trans-er-let*
           ((args (translate11x-lst (cdr x) stobjs-out bindings
                                   inclp known-stobjs 'mv flet-alist x ctx w
                                   state)))
           (trans-value (listify args))))))
       (t (let* ((new-stobjs-out (compute-stobj-flags (cdr x)
                                                      known-stobjs
                                                      w))
                 (bindings
                  (translate-bind stobjs-out new-stobjs-out bindings)))

; When we compute new-stobjs-out, above, we do with untranslated
; terms.  The stobj slots of an mv must be occupied by stobj variable
; names!  If a slot is occupied by anything else, the occupant must be
; a single non-stobj.

            (cond
             ((not (no-duplicatesp (collect-non-x nil new-stobjs-out)))
              (trans-er ctx
                        "It is illegal to return more than one ~
                         reference to a given single-threaded object ~
                         in an MV form.  The form ~x0 is thus illegal."
                        x))
             (t
              (trans-er-let*
               ((args
                 (translate11x-lst (cdr x) new-stobjs-out
                                  bindings inclp known-stobjs
                                  'mv flet-alist x ctx w state)))
               (trans-value (listify args))))))))))
   ((eq (car x) 'mv-let)
    (translate11x-mv-let x stobjs-out bindings inclp known-stobjs
                        nil nil ; stobj info
                        flet-alist ctx w state))
   ((assoc-eq (car x) flet-alist)

; The lambda-bodies in flet-alist are already translated.  Our approach is to
; consider a call of an flet-bound function symbol to be a call of the lambda
; to which it is bound in flet-alist.

    (let* ((entry (assoc-eq (car x) flet-alist))
           (lambda-fn (cadr entry))
           (formals (lambda-formals lambda-fn))
           (stobjs-out (translate-deref stobjs-out bindings))
           (stobjs-out2 (translate-deref (cddr entry) bindings)))
      (cond ((not (eql (length formals) (length (cdr x))))
             (trans-er ctx
                       "FLET-bound local function ~x0 takes ~#1~[no ~
                        arguments~/1 argument~/~x2 arguments~] but in the ~
                        call ~x3 it is given ~#4~[no arguments~/1 ~
                        argument~/~x5 arguments~].   The formal parameters ~
                        list for the applicable FLET-binding of ~x0 is ~X67."
                       (car x)
                       (zero-one-or-more (length formals))
                       (length formals)
                       x
                       (zero-one-or-more (length (cdr x)))
                       (length (cdr x))
                       formals
                       nil))
            (t
             (translate11x-call x lambda-fn (cdr x) stobjs-out stobjs-out2
                               bindings inclp known-stobjs
                               (msg "a call of FLET-bound function ~x0"
                                    (car x))
                               flet-alist ctx w state)))))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x) '(defun defmacro in-package progn)))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp meaning differs from ~
                its ACL2 meaning."
               (car x)))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x)
                    '(defpkg defconst defstobj defthm defaxiom
                       deflabel defdoc deftheory
                       verify-guards
                       in-theory in-arithmetic-theory
                       push-untouchable remove-untouchable reset-prehistory
                       set-body table theory-invariant
                       include-book certify-book value-triple
                       local make-event with-output progn!)))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp runtime value and ~
                effect differs from its ACL2 meaning."
               (car x)))
   ((and (eq (car x) 'pargs)
         (true-listp x)
         (member (length x) '(2 3))
         
; Notice that we are restricting this error case to a pargs that is
; syntactically well-formed, in the sense that if this pargs has one or two
; arguments, then the form argument is a function call.  The rest of the
; well-formedness checking will be done during macro expansion of pargs; by
; making the above restriction, we avoid the possibility that the error message
; below is confusing.

         (let ((form (car (last x)))) ; should be a function call
           (or flet-alist
               (not (and (consp form)
                         (symbolp (car form))
                         (function-symbolp (car form) w))))))
    (cond
     (flet-alist

; It may be fine to have flet-bound functions as in:

; (defun g ()
;   (flet ((foo (x) (+ x x)))
;     (pargs (h (foo 3)))))

; But we haven't thought through whether closures really respect superior FLET
; bindings, so for now we simply punt.

      (trans-er+ x ctx
                 "~x0 may not be called in the scope of ~x1.  If you want ~
                  support for that capability, please contact the ACL2 ~
                  implementors."
                 'pargs
                 'flet))
     (t
      (let ((form (car (last x))))
        (trans-er+ x ctx
                   "~x0 may only be used when its form argument is a function ~
                    call, unlike the argument ~x1.~@2  See :DOC pargs."
                   'pargs
                   form
                   (if (and (consp form)
                            (symbolp (car form))
                            (getprop (car form) 'macro-body nil 'current-acl2-world
                                     w))
                       (list "  Note that ~x0 is a macro, not a function symbol."
                             (cons #\0 (car form)))
                     ""))))))
   ((eq (car x) 'translate-and-test)
    (cond ((not (equal (length x) 3))
           (trans-er+ x ctx
                      "TRANSLATE-AND-TEST requires exactly two arguments."))
          (t (trans-er-let*
              ((ans (translate11x (caddr x) stobjs-out bindings inclp
                                 known-stobjs flet-alist x ctx w state)))

; The next mv-let is spiritually just a continuation of the trans-er-let*
; above, as though to say "and let  test-term be (translate11x (list ...)...)"
; except that we do not want to touch the current setting of bindings nor
; do we wish to permit the current bindings to play a role in the translation
; of the test.

              (mv-let
               (test-erp test-term test-bindings)
               (translate11x (list (cadr x) 'form)
                           '(nil) nil inclp known-stobjs flet-alist x ctx w
                           state)
               (declare (ignore test-bindings))
               (cond
                (test-erp (mv test-erp test-term bindings))
                (t
                 (mv-let (erp msg)
                         ;; CHANGE: Just stub this (ev ..) call right out ..
#||
                         (ev-w test-term
                               (list (cons 'form ans))
                               w
                               (f-get-global 'safe-mode state)
                               (gc-off state)
                               nil

; We are conservative here, using nil for the following AOK argument in case
; the intended test-term is to be considered in the current theory, without
; attachments.

                               nil)
||#
                         (mv nil nil)
                         (cond
                          (erp
                           (trans-er+ x ctx
                                      "The attempt to evaluate the ~
                                       TRANSLATE-AND-TEST test, ~x0, when ~
                                       FORM is ~x1, failed with the ~
                                       evaluation error:~%~%``~@2''"
                                      (cadr x) ans msg))
                          ((or (consp msg)
                               (stringp msg))
                           (trans-er+ x ctx "~@0" msg))
                          (t (trans-value ans)))))))))))
   ((eq (car x) 'with-local-stobj)

; Even if stobjs-out is t, we do not let normal macroexpansion handle
; with-local-stobj, because we want to make sure that we are dealing with a
; stobj.  Otherwise, the raw lisp code will bind a bogus live stobj variable;
; although not particularly harmful, that will give rise to an inappropriate
; compiler warning about not declaring the variable unused.

    (mv-let (erp st mv-let-form creator)
            (parse-with-local-stobj (cdr x))
            (cond
             (erp
              (trans-er ctx
                        "Ill-formed with-local-stobj form, ~x0.  ~
                         See :DOC with-local-stobj."
                        x))
             ((not (and st
                        (eq st (stobj-creatorp creator w))))
              (trans-er ctx
                        "Illegal with-local-stobj form, ~x0.  The first ~
                         argument must be the name of a stobj other than ~
                         STATE and the third, if supplied, must be its ~
                         creator function.  See :DOC with-local-stobj."
                        x))
             ((eq stobjs-out :stobjs-out)
              (trans-er ctx
                        "Calls of with-local-stobj, such as ~x0, cannot be ~
                         evaluated directly in the top-level loop.  ~
                         See :DOC with-local-stobj."
                        x))
             (t
              (translate11x-mv-let mv-let-form stobjs-out bindings inclp
                                  known-stobjs st creator flet-alist ctx w
                                  state)))))
   ((and (assoc-eq (car x) *ttag-fns-and-macros*)
         (not (ttag w)))
    (trans-er+ x ctx
               "The ~x0 ~s1 cannot be called unless a trust tag is in effect. ~
                ~ See :DOC defttag.~@2"
               (car x)
               (if (getprop (car x) 'macro-body nil 'current-acl2-world w)
                   "macro"
                 "function")
               (or (cdr (assoc-eq (car x) *ttag-fns-and-macros*))
                   "")))
   ((getprop (car x) 'macro-body nil 'current-acl2-world w)
    (cond
     ((and (eq stobjs-out :stobjs-out)
           (member-eq (car x) '(pand por pargs plet))
           (eq (f-get-global 'parallel-evaluation-enabled state) t))
      (trans-er ctx
                "Parallel evaluation is enabled, but is not implemented for ~
                 calls of parallelism primitives (~&0) made directly in the ~
                 ACL2 top-level loop, as opposed to being made inside a ~
                 function definition.  The call ~P12 is thus illegal.  To ~
                 allow such calls to be evaluated (but without parallelism), ~
                 evaluate ~x3.  See :DOC parallelism-at-the-top-level and ~
                 :DOC set-parallel-evaluation."
                '(pand por pargs plet)
                x
                (term-evisc-tuple t state)
                '(set-parallel-evaluation :bogus-parallelism-ok)))
     ((and (member-eq (car x) (global-val 'untouchable-fns w))
           (not (eq (f-get-global 'temp-touchable-fns state) t))
           (not (member-eq (car x) (f-get-global 'temp-touchable-fns state))))

; If this error burns you during system maintenance, you can subvert our security
; by setting untouchables to nil in raw Lisp:

; (setf (cadr (assoc 'global-value (get 'untouchable-fns *current-acl2-world-key*)))
;       nil)
      
      (trans-er+ x ctx
                 "It is illegal to call ~x0 because it has been placed on ~
                  untouchable-fns."
                 (car x)))
     (t
      (mv-let (erp expansion)
              (macroexpand1-cmp x ctx state)
              (cond (erp (mv erp expansion bindings))
                    (t (translate11x expansion stobjs-out bindings inclp
                                    known-stobjs flet-alist x ctx w
                                    (f-decrement-big-clock state))))))))
   ((eq (car x) 'let)

; Warning:  If the final form of a translated let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

; In translating LET and MV-LET we generate "open lambdas" as function
; symbols.  The main reason we did this was to prevent translate from
; exploding in our faces when presented with typical DEFUNs (e.g., our
; own code).  Note that such LAMBDAs can be expanded away.  However,
; expansion affects the guards.  Consider (let ((x (car 3))) t), which
; expands to ((lambda (x) t) (car 3)).

    (cond
     ((not (and (>= (length x) 3)
                (doubleton-list-p (cadr x))))
      (trans-er ctx
                "The proper form of a let is (let bindings dcl ... ~
                 dcl body), where bindings has the form ((v1 term) ~
                 ... (vn term)) and the vi are distinct variables, ~
                 not constants, and do not begin with an asterisk, ~
                 but ~x0 does not have this form."
                x))
     ((not (arglistp (strip-cars (cadr x))))
      (mv-let (culprit explan)
              (find-first-bad-arg (strip-cars (cadr x)))
              (trans-er ctx
                        "The form ~x0 is an improper let expression ~
                         because it attempts to bind ~x1, which ~@2."
                        x culprit explan)))
     ((and (not (eq stobjs-out t))
           (not (equal 1 (length (cadr x))))
           (not (all-nils (compute-stobj-flags (strip-cars (cadr x))
                                               known-stobjs
                                               w))))
      (trans-er ctx
                "A single-threaded object name, such as ~x0, may be ~
                 LET-bound only when it is the only binding in the ~
                 LET, but ~x1 binds more than one variable."
                (car
                 (collect-non-x nil
                  (compute-stobj-flags (strip-cars (cadr x))
                                       known-stobjs
                                       w)))
                x))
     (t (let* ((bound-vars (strip-cars (cadr x)))
               (stobjs-bound
                (collect-non-x nil (compute-stobj-flags bound-vars
                                                        known-stobjs
                                                        w)))
               (body (car (last x))))
          (mv-let
           (erp edcls)
           (collect-declarations-cmp (butlast (cddr x) 1)
                                     bound-vars 'let state ctx)
           (cond
            (erp (mv erp edcls bindings))
            (t
             (trans-er-let*
              ((value-forms
                (cond ((and (not (eq stobjs-out t))
                            stobjs-bound)

; In this case, we know that the only variable of the LET is a stobj name.
; Note that (list (car bound-vars)) is thus a stobjs-out specifying
; a single result consisting of that stobj.

                       (trans-er-let*
                        ((val (translate11x (cadr (car (cadr x)))
                                           (list (car bound-vars))
                                           bindings

; One might be tempted to allow the stobj name to be bound to anything
; (i.e., inclp = t) if no stobjs come out.  But we have a rule that
; says if a stobj name is bound it must come out.  (See the big error
; messages below, for example.)  So I don't implement the inclusive
; treatment of LET bindings.

                                           inclp known-stobjs flet-alist
                                           x ctx w state)))
                        (trans-value (list val))))
                      (t (translate11x-lst (strip-cadrs (cadr x))
                                          (if (eq stobjs-out t)
                                              t
                                            nil)       ;;; '(nil ... nil)
                                          bindings inclp known-stobjs
                                          "in a LET binding (or ~
                                           LAMBDA application)"
                                          flet-alist x ctx w state))))
               (tbody
                (translate11x body stobjs-out bindings inclp known-stobjs
                             flet-alist x ctx w state))
               (tdcls (translate11x-lst
                       (translate-dcl-lst edcls w)
                       (if (eq stobjs-out t)
                           t
                         nil)         ;;; '(nil ... nil)
                       bindings inclp known-stobjs
                       "in a DECLARE form in a LET (or LAMBDA)"
                       flet-alist x ctx w state)))
              (let ((used-vars (union-eq (all-vars tbody)
                                         (all-vars1-lst tdcls nil)))
                    (ignore-vars (ignore-vars edcls))
                    (ignorable-vars (ignorable-vars edcls))
                    (stobjs-out (translate-deref stobjs-out bindings)))
                (cond 
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (consp stobjs-out)))
                  (trans-er+ x ctx
                             "~@0"
                             (unknown-binding-msg
                              stobjs-bound "a LET" "the LET" "the LET")))
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (subsetp-eq stobjs-bound
                                        (collect-non-x nil stobjs-out))))
                  (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                    (trans-er+ x ctx
                               "The single-threaded object~#0~[ ~&0 has~/s ~
                                ~&0 have~] been bound in a LET.  It is a ~
                                requirement that ~#0~[this object~/these ~
                                objects~] be among the outputs of the LET, ~
                                but ~#0~[it is~/they are~] not.  The LET ~
                                returns ~#1~[no single-threaded objects~/the ~
                                single-threaded object ~&2~/the ~
                                single-threaded objects ~&2~]."
                               (set-difference-eq stobjs-bound stobjs-returned)
                               (zero-one-or-more stobjs-returned)
                               stobjs-returned)))
                 ((intersectp-eq used-vars ignore-vars)
                  (trans-er+ x ctx
                             "Contrary to the declaration that ~#0~[it ~
                              is~/they are~] IGNOREd, the variable~#0~[ ~&0 ~
                              is~/s ~&0 are~] used in the body of the LET ~
                              expression that binds ~&1."
                             (intersection-eq used-vars ignore-vars)
                             bound-vars))
                 (t
                  (let* ((ignore-vars (augment-ignore-vars bound-vars
                                                           value-forms
                                                           ignore-vars))
                         (diff (set-difference-eq
                                bound-vars
                                (union-eq used-vars
                                          (union-eq ignorable-vars
                                                    ignore-vars))))
                         (ignore-ok
                          (if (null diff)
                              t
                            (cdr (assoc-eq
                                  :ignore-ok
                                  (table-alist 'acl2-defaults-table w))))))
                    (cond
                     ((null ignore-ok)
                      (trans-er+ x ctx
                                 "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                  used in the body of the LET expression that ~
                                  binds ~&1.  But ~&0 ~#0~[is~/are~] not ~
                                  declared IGNOREd or IGNORABLE.  See :DOC ~
                                  set-ignore-ok."
                                 diff
                                 bound-vars))
                     (t
                      (prog2$
                       (cond
                        ((eq ignore-ok :warn)
                         (warning$-cmp ctx "Ignored-variables"
                                       "The variable~#0~[ ~&0 is~/s ~&0 are~] ~
                                        not used in the body of the LET ~
                                        expression that binds ~&1.  But ~&0 ~
                                        ~#0~[is~/are~] not declared IGNOREd ~
                                        or IGNORABLE.  See :DOC set-ignore-ok."
                                       diff
                                       bound-vars))
                        (t nil))
                       (let* ((tbody
                               (cond
                                (tdcls
                                 (let ((guardian (dcl-guardian tdcls)))
                                   (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                          tbody)
                                         (t
                                          (fcons-term* 'prog2$
                                                       guardian
                                                       tbody)))))
                                (t tbody)))
                              (body-vars (all-vars tbody))
                              (extra-body-vars (set-difference-eq
                                                body-vars
                                                bound-vars)))
                         (trans-value
                          (cons (make-lambda
                                 (append bound-vars extra-body-vars)
                                 tbody)

; See the analogous line in the handling of MV-LET for an explanation
; of hide-ignored-actuals.

                                (append
                                 (hide-ignored-actuals
                                  ignore-vars bound-vars value-forms)
                                 extra-body-vars)))))))))))))))))))
   ((eq (car x) 'flet) ; (flet bindings form)
    (translate11x-flet x stobjs-out bindings inclp known-stobjs flet-alist ctx w
                      state))
   ((and (not (eq stobjs-out t))
         (null (cdr x)) ; optimization
         (stobj-creatorp (car x) w))
    (trans-er+ x ctx
               "It is illegal to call ~x0 in this context because it is a ~
                stobj creator.  Stobj creators cannot be called directly ~
                except in theorems.  If you did not explicitly call a stobj ~
                creator, then this error is probably due to an attempt to ~
                evaluate a with-local-stobj form directly in the top-level ~
                loop.  Such forms are only allowed in the bodies of functions ~
                and in theorems.  Also see :DOC with-local-stobj."
               (car x)))
   ((equal (arity (car x) w) (length (cdr x)))
    (cond ((and (member-eq (car x) (global-val 'untouchable-fns w))
                (not (eq (f-get-global 'temp-touchable-fns state) t))
                (not (member-eq (car x) (f-get-global 'temp-touchable-fns state))))
           (trans-er+ x ctx
                      "It is illegal to call ~x0 because it has been placed ~
                       on untouchable-fns."
                      (car x)))
          ((eq (car x) 'if)
           (cond ((stobjp (cadr x) known-stobjs w)
                  (trans-er+ x ctx
                             "It is illegal to test on a single-threaded ~
                              object such as ~x0."
                             (cadr x)))

; Because (cadr x) has not yet been translated, we do not really know
; it is not a stobj!  It could be a macro call that expands to a
; stobj.'  The error message above is just to be helpful.  An accurate
; check is made below.

                 (t (trans-er-let*
                     ((arg1 (translate11x (cadr x)
                                         (if (eq stobjs-out t)
                                             t
                                           '(nil))
                                         bindings inclp known-stobjs
                                         flet-alist x ctx w state))
                      (arg2 (translate11x (caddr x)
                                         stobjs-out bindings inclp known-stobjs
                                         flet-alist x ctx w state))
                      (arg3 (translate11x (cadddr x)
                                         stobjs-out bindings inclp known-stobjs
                                         flet-alist x ctx w state)))
                     (trans-value (fcons-term* 'if arg1 arg2 arg3))))))
          ((eq (car x) 'synp)

; Synp is a bit odd.  We store the quotation of the term to be evaluated in the
; third arg of the synp form.  We store the quotation so that ACL2 will not see
; the term as a potential induction candidate.  (Eric Smith first pointed out
; this issue.)  This, however forces us to treat synp specially here in order
; to translate the term to be evaluated and thereby get a proper ACL2 term.
; Without this special treatment (cadr x), for instance, would be left alone
; whereas it needs to be translated into (car (cdr x)).

; This mangling of the third arg of synp is sound because synp always returns
; t.

; Robert Krug has mentioned the possibility that the known-stobjs below could
; perhaps be t.  This would allow a function called by synp to use, although
; not change, stobjs.  If this is changed, change the referances to stobjs in
; the documentation for syntaxp and bind-free as appropriate.  But before
; making such a change, consider this: no live user-defined stobj will ever
; appear in the unifying substitution that binds variables in the evg of
; (cadddr x).  So it seems that such a relaxation would not be of much value.

           (cond ((not (eq stobjs-out t))
                  (trans-er ctx
                            "A call to synp is not allowed here.  This ~
                             call may have come from the use of syntaxp ~
                             or bind-free within a function definition ~
                             since these two macros expand into calls to ~
                             synp.  The form we were translating when we ~
                             encountered this problem is ~x0.  If you ~
                             believe this error message is itself in error ~
                             or that we have been too restrictive, please ~
                             contact the maintainers of ACL2."
                            x))
                 ((eql (length x) 4)
                  (trans-er-let*
                   ((quoted-vars (translate11x (cadr x)
                                              '(nil) ; stobjs-out
                                              bindings
                                              inclp
                                              '(state) ; known-stobjs
                                              flet-alist x ctx w state))
                    (quoted-user-form (translate11x (caddr x)
                                                   '(nil) ; stobjs-out
                                                   bindings
                                                   inclp
                                                   '(state) ; known-stobjs
                                                   flet-alist x ctx w state))
                    (quoted-term (translate11x (cadddr x)
                                              '(nil) ; stobjs-out
                                              bindings
                                              inclp
                                              '(state) ; known-stobjs
                                              flet-alist x ctx w state)))
                   (let ((quoted-term (if (quotep quoted-term)
                                          quoted-term
                                        (sublis-var nil quoted-term))))
                     (cond ((quotep quoted-term)
                            (trans-er-let*
                             ((term-to-be-evaluated
                               (translate11x (cadr quoted-term)
                                            '(nil) ; stobjs-out
                                            bindings
                                            inclp
                                            '(state) ; known-stobjs
                                            flet-alist x ctx w state)))
                             (let ((quoted-vars (if (quotep quoted-vars)
                                                    quoted-vars
                                                  (sublis-var nil quoted-vars)))
                                   (quoted-user-form (if (quotep quoted-user-form)
                                                         quoted-user-form
                                                       (sublis-var nil
                                                                   quoted-user-form))))
                               (cond ((and (quotep quoted-vars)
                                           (quotep quoted-user-form))
                                      (trans-value 
                                       (fcons-term* 'synp quoted-vars quoted-user-form
                                                    (kwote term-to-be-evaluated))))
                                     (t (trans-er ctx
                                                  *synp-trans-err-string*
                                                  x))))))
                           (t
                            (trans-er ctx
                                      *synp-trans-err-string*
                                      x))))))
                 (t
                  (trans-er ctx
                            *synp-trans-err-string*
                            x))))
          ((eq (car x) 'prog2$)
           (trans-er-let*
            ((arg1 (translate11x (cadr x)
                                (if (eq stobjs-out t)
                                    t
                                  '(nil))
                                bindings inclp known-stobjs flet-alist x
                                ctx w state))
             (arg2 (translate11x (caddr x)
                                stobjs-out bindings inclp known-stobjs
                                flet-alist x ctx w state)))
            (trans-value (fcons-term* 'prog2$ arg1 arg2))))
          ((eq (car x) 'time$-logic)
           (trans-er-let*
            ((aux-args (translate11x-lst
                        (butlast (cdr x) 1)
                        (if (eq stobjs-out t)
                            t
                          '(nil))
                        bindings inclp known-stobjs nil flet-alist x ctx w
                        state))
             (timing-arg (translate11x (car (last (cdr x)))
                                      stobjs-out bindings inclp known-stobjs
                                      flet-alist x ctx w state)))
            (trans-value (fcons-term (car x)
                                     (append aux-args (list timing-arg))))))
          ((eq (car x) 'must-be-equal)
           (cond
            ((and (not (eq (f-get-global 'ld-skip-proofsp state)
                           'include-book))
                  (not (eq stobjs-out t))
                  (non-trivial-encapsulate-ee-entries
                   (global-val 'embedded-event-lst w)))

; See the example in the comment near the top of (deflabel note-3-4 ...).  We
; don't complain when in include-book or the second pass of an encapsulate
; since we have already checked legality on an earlier pass.  We also don't
; complain if stobjs-out is t, for example because we are processing a defun
; with xargs declaration :non-executable t.

             (trans-er+ x ctx
                        "It is illegal to call ~x0 (~x1) under an encapsulate ~
                         event with a non-empty signature."
                        'must-be-equal 'mbe))
            (t

; We need to know that the first argument of must-be-equal has the same
; signature as the second argument.  If for example we have (mv-let (x y)
; (must-be-equal <logic-form> <exec-form>)), but <exec-form> had signature *,
; then Common Lisp would get confused during evaluation.

             (trans-er-let*
              ((arg1 (translate11x (cadr x)
                                  stobjs-out bindings inclp known-stobjs
                                  flet-alist x ctx w state)) 
               (arg2 (translate11x (caddr x)
                                  stobjs-out bindings inclp known-stobjs
                                  flet-alist x ctx w state)))
              (trans-value (fcons-term* 'must-be-equal arg1 arg2))))))
          ((eq (car x) 'ec-call)
           (cond
            ((not (and (consp (cdr x))
                       (consp (cadr x))
                       (let ((fn (car (cadr x))))
                         (and (symbolp fn)
                              (not (member-eq fn *ec-call-bad-ops*))
                              (function-symbolp fn w)))))
             (trans-er ctx
                       "A call of ~x0 must only be made on an argument of the ~
                        form (FN ARG1 ... ARGK), where FN is a known function ~
                        in the current ACL2 world other than ~v1.  The call ~
                        ~x2 is thus illegal."
                       'ec-call *ec-call-bad-ops* x))
            ((assoc-eq (car (cadr x)) flet-alist)
             (trans-er ctx
                       "A call of ~x0 is illegal when made on a call of a ~
                        function bound by ~x1.  The call ~x2 is thus illegal."
                       'ec-call 'flet x))
            (t
             (trans-er-let*
              ((arg1 (translate11x (cadr x)
                                  stobjs-out bindings inclp known-stobjs
                                  flet-alist x ctx w state)))
              (trans-value (fcons-term* (car x) arg1))))))
          ((and (eq (car x) 'mv-list)
                (not (eq stobjs-out t)))
           (trans-er-let*
            ((arg1 (translate11x (cadr x)
                                stobjs-out bindings inclp known-stobjs
                                flet-alist x ctx w state)))
            (cond ((not (and (quotep arg1)
                             (integerp (unquote arg1))
                             (<= 2 (unquote arg1))))
                   (trans-er ctx
                             "A call of ~x0 can only be made when the first ~
                              argument is explicitly a natural number.  The ~
                              call ~x1 is thus illegal."
                             'mv-list x))
                  (t
                   (trans-er-let*
                    ((arg2 (translate11x (caddr x)
                                        (make-list (unquote arg1)
                                                   :initial-element nil)
                                        bindings inclp known-stobjs
                                        flet-alist x ctx w state)))
                    (trans-value (fcons-term* 'mv-list arg1 arg2)))))))
          ((member-eq (car x) '(memoize-on memoize-off ; relevant for #+hons
                                with-prover-time-limit
                                with-guard-checking))
           (trans-er-let*
            ((arg1 (translate11x (cadr x)
                                (if (eq stobjs-out t)
                                    t
                                  '(nil))
                                bindings inclp known-stobjs
                                flet-alist x ctx w state))
             (arg2 (translate11x (caddr x)
                                stobjs-out bindings inclp known-stobjs
                                flet-alist x ctx w state)))
            (trans-value (fcons-term* (car x) arg1 arg2))))
          ((eq stobjs-out t)
           (trans-er-let*
            ((args (translate11x-lst (cdr x) t bindings inclp known-stobjs
                                    nil flet-alist x ctx w state)))
            (trans-value (fcons-term (car x) args))))
          ((and (member-eq (car x) '(makunbound-global put-global))
                (not (eq (f-get-global 'temp-touchable-vars state) t))
                (or ; Keep this case in sync with the cond cases below
                 (not (and (consp (cadr x))
                           (eq (car (cadr x)) 'quote)
                           (null (cddr (cadr x)))
                           (symbolp (cadr (cadr x)))))
                 (and (member-eq (cadr (cadr x))
                                 (global-val 'untouchable-vars w))
                      (not (member-eq (cadr (cadr x))
                                      (f-get-global 'temp-touchable-vars
                                                    state))))
                 (and (eq (car x) 'makunbound-global)
                      (always-boundp-global (cadr (cadr x))))))
           (cond ( ; Keep this case the same as its twin above
                  (not (and (consp (cadr x))
                            (eq (car (cadr x)) 'quote)
                            (null (cddr (cadr x)))
                            (symbolp (cadr (cadr x)))))
                  (trans-er+ x ctx
                             "The first arg of ~x0 must be a quoted symbol, ~
                              unlike ~x1.  We make this requirement in ~
                              support of untouchable-vars."
                             (car x) (cadr x)))
                 ( ; Keep this case the same as its twin above
                  (and (member-eq (cadr (cadr x))
                                  (global-val 'untouchable-vars w))
                       (not (member-eq (cadr (cadr x))
                                       (f-get-global 'temp-touchable-vars
                                                     state))))
                  (trans-er ctx
                            "State global variable ~x0 has been rendered ~
                             untouchable and thus may not be directly ~
                             altered, as in ~x1.~@2"
                            (cadr (cadr x))
                            x
                            (let ((set-fn (intern-in-package-of-symbol
                                           (concatenate 'string
                                                        "SET-"
                                                        (symbol-name (cadr (cadr x))))
                                           (cadr (cadr x)))))
                              (cond ((function-symbolp set-fn w)
                                     (msg "~|There is a function ~x0, which ~
                                           (from the name) may provide the ~
                                           functionality you desire."
                                          set-fn))
                                    (t "")))))
                 (t
                  (trans-er ctx
                            "Built-in state global variables may not be made ~
                             unbound, as in ~x1."
                            (cadr (cadr x))
                            x))))
          (t
           (let ((stobjs-out (translate-deref stobjs-out bindings))
                 (stobjs-out2 (let ((temp (translate-deref (car x) bindings)))
                                (cond (temp temp)
                                      (t (stobjs-out (car x) w))))))
             (translate11x-call x (car x) (cdr x) stobjs-out stobjs-out2
                               bindings inclp known-stobjs (car x) flet-alist
                               ctx w state)))))
   ((arity (car x) w)
    (trans-er ctx
              "~x0 takes ~#1~[no arguments~/1 argument~/~x2 ~
               arguments~] but in the call ~x3 it is given ~#4~[no ~
               arguments~/1 argument~/~x5 arguments~].   The formal ~
               parameters list for ~x0 is ~X67."
              (car x)
              (zero-one-or-more (arity (car x) w))
              (arity (car x) w)
              x
              (zero-one-or-more (length (cdr x)))
              (length (cdr x))
              (formals (car x) w)
              nil))
   ((eq (car x) 'declare)
    (trans-er ctx
              "It is illegal to use DECLARE as a function symbol, as ~
               in ~x0.  DECLARE forms are permitted only in very ~
               special places, e.g., before the bodies of function ~
               definitions, LETs, and MV-LETs.  DECLARE forms are ~
               never permitted in places in which their ``values'' ~
               are relevant.  If you already knew this, it is likely ~
               you have made a typographical mistake, e.g., including ~
               the body in the DECLARE form or closing the superior ~
               form before typing the body."
              x))
   (t ;; CHANGE : Replace the non-existing function failure with this code
#||
    (trans-er+ x ctx
                 "The symbol ~x0 (in package ~x1) has neither a function nor ~
                  macro definition in ACL2.  ~#2~[Please define ~
                  it.~/Moreover, this symbol is in the main Lisp package; ~
                  hence, you cannot define it in ACL2.~]"
                 (car x)
                 (symbol-package-name (car x))
                 (if (equal (symbol-package-name (car x))
                            *main-lisp-package-name*)
                     1
                   0))
||#
    (trans-er-let*
     ((args (translate11x-lst (cdr x) 
                              nil bindings inclp known-stobjs
                              "Unknown Function" flet-alist x ctx w state)))
     (trans-value (fcons-term (car x) args))))))

(defun translate11x-lst (lst stobjs-out bindings inclp-lst known-stobjs
                            msg flet-alist cform ctx w state)

; WARNING: This function's treatment of stobjs-out is unusual:
; (1) stobjs-out must be either t, nil, or list of stobjs flags.
;     It CANNOT be a function name (``an unknown'').
; (2) If stobjs-out is nil, it is treated as though it were a list of
;     nils as long as lst.

; If stobjs-out is t, we translate each element of lst (with stobjs-out t)
; and return the resulting list.

; If stobjs-out is not t, it is a list of stobj flags as long as lst.
; We consider each element, x, of list in correspondence with each
; flag, flg.  If flg is nil, we insist that the translation of x
; return one non-stobj result.  If flg is a stobj, we insist that x BE
; flg -- except that x ``is'' a stobj, flg, only if x is flg and x is
; among known-stobjs (with proper treatment of known-stobjs = t).

; Inclp-lst is thought of as being a list in 1:1 correspondence with
; lst which supplies the inclp flag for each element of lst.  However,
; if inclp-lst is t it is treated as (t t ... t) and if inclp-lst is
; nil it is treated as (nil nil ... nil).  We exploit the fact that
; (car nil) = (cdr nil) = nil and so have to take special care only
; for t.

; Msg is used to describe the form that contains the list, lst, of
; forms being translated.  It is only used if an error is caused when
; some element of lst violates the stobj restrictions of stobjs-out.
; If msg is nil, no allusion to the containing form is made.  If msg
; is a symbol, we describe the containing form as though it were a
; call of that function symbol.  Otherwise, we print msg with ~@ in
; ``the form x is being used, @msg, where a stobj...''.

; The cform argument is a form that provides context -- it is the one to be
; printed by trans-er+ when there isn't another obvious contextual form to
; print.  (Often x carries enough context.)

  (cond ((atom lst) (trans-value nil))
        ((eq stobjs-out t)
         (trans-er-let*
          ((x (translate11x (car lst) t bindings
                           (if (eq inclp-lst t)
                               t
                             (car inclp-lst))
                           known-stobjs flet-alist (car lst) ctx w state))
           (y (translate11x-lst (cdr lst) t bindings
                               (if (eq inclp-lst t)
                                   t
                                 (cdr inclp-lst))
                               known-stobjs msg flet-alist cform ctx w state)))
          (trans-value (cons x y))))
        ((car stobjs-out)
         (trans-er-let*
          ((x (cond
               ((eq (if (or (eq known-stobjs t)
                            (member-eq (car lst) known-stobjs))
                        (car lst)
                      nil)
                    (car stobjs-out))
                (trans-value (car lst)))

; The following case is checked to allow our use of big-clock-entry to control
; recursion, a violation of our normal rule that state-producing forms are not
; allowed where STATE is expected (except when binding STATE).  We have to look
; for the unexpanded form of the macro f-decrement-big-clock as well.

               ((and (eq (car stobjs-out) 'state)
                     (or (equal (car lst)
                                '(decrement-big-clock state))
                         (equal (car lst)
                                '(f-decrement-big-clock state))))
                (trans-value '(decrement-big-clock state)))
               ((eq (car lst) (car stobjs-out))

; In this case, we failed because (car lst) is not considered a stobj even
; though it has the right name.

                (let ((known-stobjs (collect-non-x nil known-stobjs)))
                  (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object of that name is ~
                              required.  But in the current context, ~
                              ~#3~[there are no declared stobj names~/the ~
                              only declared stobj name is ~&4~/the only ~
                              declared stobj names are ~&4~]."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (cond ((null known-stobjs) 0)
                                   ((null (cdr known-stobjs)) 1)
                                   (t 2))
                             known-stobjs)))
               (t (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object ~x3 is required.  Note ~
                              that the variable ~x3 is required, not merely a ~
                              term that returns such a single-threaded ~
                              object, so you may need to bind ~x3 with LET; ~
                              see :DOC stobj."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (car stobjs-out)))))
           (y (translate11x-lst (cdr lst) (cdr stobjs-out)
                               bindings
                               (if (eq inclp-lst t)
                                   t
                                 (cdr inclp-lst))
                               known-stobjs msg flet-alist cform ctx w state)))
          (trans-value (cons x y))))
        (t (trans-er-let*
            ((x (translate11x (car lst) '(nil) bindings
                             (if (eq inclp-lst t)
                                 t
                               (car inclp-lst))
                             known-stobjs flet-alist (car lst) ctx w state))
             (y (translate11x-lst (cdr lst) (cdr stobjs-out)
                                 bindings
                                 (if (eq inclp-lst t)
                                     t
                                   (cdr inclp-lst))
                                 known-stobjs msg flet-alist cform
                                 ctx w state)))
            (trans-value (cons x y))))))

)

(defun translate1x-cmp (x stobjs-out bindings known-stobjs ctx w state)
  (translate11x x stobjs-out bindings nil known-stobjs nil x ctx w state))

(defun translate1x (x stobjs-out bindings known-stobjs ctx w state)
  (mv-let (erp msg-or-val bindings)
          (translate1x-cmp x stobjs-out bindings known-stobjs ctx w state)
          (cond (erp ; erp is a ctx and val is a msg
                 (mv-let (erp0 val state)
                         (er soft erp
                             "~@0"
                             msg-or-val)
                         (declare (ignore erp0 val))
                         (mv t nil bindings state)))
                (t (mv nil msg-or-val bindings state)))))

(DEFUN pseudo-translate (FORM STATE)
  (LET
   ((WRLD (W STATE)))
   (MV-LET
    (FLG VAL BINDINGS STATE)
    (TRANSLATE1x FORM :STOBJS-OUT
		 '((:STOBJS-OUT . :STOBJS-OUT))
		 T 'TOP-LEVEL
		 WRLD STATE)
    (declare (ignore bindings))
    (mv flg val state))))
