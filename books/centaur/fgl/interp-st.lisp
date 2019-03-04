; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "pathcond")
(include-book "bvar-db")
(include-book "constraint-db")
(include-book "glcp-config")
(include-book "contexts")
(include-book "stack")
(include-book "centaur/fty/bitstruct" :dir :system)
(include-book "prof")

(fty::defbitstruct interp-flags
  ((intro-bvars booleanp :default t)
   (intro-synvars booleanp :default t)
   (simplify-logic booleanp :default t)))

(acl2::defstobj-clone constraint-pathcond pathcond :prefix "CONSTRAINT-")

(make-event
 `(defconst *interp-st-fields*
    '((stack :type stack)
      (logicman :type logicman)
      (bvar-db :type bvar-db)
      (pathcond :type pathcond)
      (constraint :type pathcond)
      (constraint-db :type (satisfies constraint-db-p))
      (prof :type interp-profiler)
      (backchain-limit :type integer :initially -1)
      (bvar-mode :type t)
      (equiv-contexts :type (satisfies equiv-contextsp))
      (reclimit :type (integer 0 *) :initially 0)
      (config :type (satisfies glcp-config-p) :initially ,(make-glcp-config))
      (flags :type (and (unsigned-byte 60)
                        (satisfies interp-flags-p))
             :initially ,(make-interp-flags)))))


(local (defun member-eq-tree (x tree)
         (declare (xargs :guard (symbolp x)))
         (if (atom tree)
             (eq x tree)
           (or (member-eq-tree x (car tree))
               (member-eq-tree x (cdr tree))))))

(local (defun interp-st-fields-to-templates (fields)
         (declare (xargs :mode :program))
         (if (atom fields)
             nil
           (cons (b* ((name (caar fields))
                      (type (cadr (assoc-keyword :type (cdar fields))))
                      (type-pred (acl2::translate-declaration-to-guard type name nil))
                      (typep (and type-pred (not (member-eq-tree 'satisfies type))))
                      (pred (or type-pred
                                (and (symbolp type)
                                     `(,(intern-in-package-of-symbol (concatenate 'string (symbol-name type) "P")
                                                                     type)
                                       ,name))))
                      (- (and (not pred)
                              (er hard? 'interp-st-fields-to-templates
                                  "couldn't figure out the predicate for the type of ~x0~%" (car fields)))))
                   (acl2::make-tmplsubst :atoms `((<field> . ,(caar fields))
                                                  (:<field> . ,(intern$ (symbol-name (caar fields)) "KEYWORD"))
                                                  (<fieldcase> . ,(if (atom (cdr fields))
                                                                      t
                                                                    (intern$ (symbol-name (caar fields)) "KEYWORD")))
                                                  (<type> . ,(third (car fields)))
                                                  (<rest> . ,(cdddr (car fields)))
                                                  (<pred> . ,pred))
                                         :features (cond ((eq pred t) '(:no-pred))
                                                         (typep '(:type-pred))
                                                         (t nil))
                                         :strs `(("<FIELD>" . ,(symbol-name (caar fields))))
                                         :pkg-sym 'fgl::foo))
                 (interp-st-fields-to-templates (cdr fields))))))

(make-event
 `(defconst *interp-st-field-templates*
    ',(interp-st-fields-to-templates *interp-st-fields*)))
  

(make-event
 (acl2::template-subst
  '(defstobj interp-st
     (:@proj fields (interp-st-><field> :type <type> . <rest>)))
  :subsubsts `((fields . ,*interp-st-field-templates*))))


(make-event
 (acl2::template-subst
  '(std::defenum interp-st-field-p ((:@proj fields :<field>)))
  :subsubsts `((fields . ,*interp-st-field-templates*))))

(make-event
 (acl2::template-subst
  '(define interp-st-get ((key interp-st-field-p) &optional (interp-st 'interp-st))
     ;; bozo define doesn't correctly support :non-executable t with macro args
     (declare (xargs :non-executable t))
     :no-function t
     :prepwork ((local (in-theory (enable interp-st-field-fix))))
     (prog2$ (acl2::throw-nonexec-error 'interp-st-get-fn (list key interp-st))
             (case key
               (:@proj fields (<fieldcase> (interp-st-><field> interp-st))))))
  :subsubsts `((fields . ,*interp-st-field-templates*))))

(make-event
 (acl2::template-subst
  '(defsection interp-st-field-basics
     (local (in-theory (enable interp-st-get
                               interp-st-field-fix
                               interp-stp)))
     (:@append fields
      (def-updater-independence-thm interp-st-><field>-updater-independence
        (implies (equal (interp-st-get :<field> new)
                        (interp-st-get :<field> old))
                 (equal (interp-st-><field> new)
                        (interp-st-><field> old))))

      (defthm update-interp-st-><field>-preserves-others
        (implies (not (equal (interp-st-field-fix i) :<field>))
                 (equal (interp-st-get i (update-interp-st-><field> x interp-st))
                        (interp-st-get i interp-st))))

      (defthm update-interp-st-><field>-self-preserves-interp-st
        (implies (interp-stp interp-st)
                 (equal (update-interp-st-><field>
                         (interp-st-><field> interp-st)
                         interp-st)
                        interp-st))
        :hints(("Goal" :in-theory (enable interp-stp
                                          aignet::redundant-update-nth))))

      (defthm interp-st-><field>-of-update-interp-st-><field>
        (equal (interp-st-><field> (update-interp-st-><field> x interp-st))
               x))

      (:@ :type-pred
       (defthm interp-st-implies-<field>-type
         (implies (interp-stp interp-st)
                  (let ((<field> (interp-st-><field> interp-st)))
                    <pred>))
         :hints(("Goal" :in-theory (enable interp-st-><field>)))
         :rule-classes :type-prescription))

      (:@ (and (not :type-pred) (not :no-pred))
       (defthm interp-st-implies-<field>-type
         (implies (interp-stp interp-st)
                  (let ((<field> (interp-st-><field> interp-st)))
                    <pred>))
         :hints(("Goal" :in-theory (enable interp-st-><field>))))))

     (:@proj fields
      (in-theory (disable interp-st-><field>
                          update-interp-st-><field>)))

     (local (in-theory (disable interp-st-get
                                interp-st-field-fix)))

     ;; test:
     (local 
      (defthm interp-st-test-updater-independence
        (b* ((interp-st1 (update-interp-st->bvar-mode bvar-mode interp-st))
             (interp-st2 (update-interp-st->logicman logicman interp-st)))
          (and (equal (interp-st->constraint interp-st2) (interp-st->constraint interp-st))
               (equal (interp-st->constraint interp-st1) (interp-st->constraint interp-st)))))))
  
  :subsubsts `((fields . ,*interp-st-field-templates*))))


(defthm interp-st-implies-natp-flags
  (implies (interp-stp interp-st)
           (natp (interp-st->flags interp-st)))
  :hints(("Goal" :in-theory (enable interp-st->flags)))
  :rule-classes :type-prescription)

(in-theory (disable interp-stp))






(define interp-st-prof-push (name interp-st)       
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-push name interp-profiler)
   interp-st))

(define interp-st-prof-pop-increment (successp interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-pop-increment successp interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-def (name interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-def name interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-exec (name interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-exec name interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-g (name interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-g name interp-profiler)
   interp-st))

(define interp-st-prof-unwind-stack (interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-unwind-stack interp-profiler)
   interp-st))

(define interp-st-prof-print-report (interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (res)
   (prof-print-report interp-profiler)
   res))

(define interp-st-prof-report (interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-report interp-profiler)
   interp-st))

(define interp-st-prof-reset (interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-reset interp-profiler)
   interp-st))

(define interp-st-prof-enable (interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp t interp-profiler)
   interp-st))

(define interp-st-prof-disable (interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp nil interp-profiler)
   interp-st))

(define interp-st-prof-enabledp (interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (enabledp)
   (prof-enabledp interp-profiler)
   enabledp))

(define update-interp-st-prof-enabledp ((val booleanp) interp-st)
  :returns (new-interp-st)
  :enabled t
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp val interp-profiler)
   interp-st))




(define interp-st-bindings (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-bindings stack)
             bindings))

(define interp-st-minor-bindings (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-minor-bindings stack)
             bindings))

(define interp-st-stack-frames (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-frames stack)
             frames))

(define interp-st-stack-minor-frames (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-minor-frames stack)
             frames))

(define interp-st-pop-frame (interp-st)
  :enabled t
  :inline t
  :guard (and (< 1 (interp-st-stack-frames interp-st))
              (eql 1 (interp-st-stack-minor-frames interp-st)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-frame stack)
             interp-st))

(define interp-st-pop-minor-frame (interp-st)
  :enabled t
  :inline t
  :guard (< 1 (interp-st-stack-minor-frames interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-minor-frame stack)
             interp-st))

(define interp-st-push-scratch ((x gl-object-p)
                                interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-push-scratch x stack)
             interp-st))

(define interp-st-scratch-len (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-scratch-len stack)
             len))

(define interp-st-pop-scratch ((n natp)
                                interp-st)
  :enabled t
  :inline t
  :guard (<= n (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-scratch n stack)
             interp-st))

(define interp-st-peek-scratch ((n natp)
                                interp-st)
  :enabled t
  :inline t
  :guard (<= n (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (args)
             (stack-peek-scratch n stack)
             args))

(define interp-st-add-binding ((var pseudo-var-p)
                               (val gl-object-p)
                               interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-binding var val stack)
             interp-st))

(define interp-st-set-bindings ((bindings gl-object-alist-p)
                                interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-bindings bindings stack)
             interp-st))

(define interp-st-add-minor-bindings ((bindings gl-object-alist-p)
                                      interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-minor-bindings bindings stack)
             interp-st))

(define interp-st-set-minor-bindings ((bindings gl-object-alist-p)
                                      interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-minor-bindings bindings stack)
             interp-st))

(define interp-st-push-frame ((bindings gl-object-alist-p)
                              interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((stack (stack-push-frame stack)))
               (stack-set-bindings bindings stack))
             interp-st))

(define interp-st-push-minor-frame (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((bindings (stack-minor-bindings stack))
                  (stack (stack-push-minor-frame stack)))
               (stack-set-minor-bindings bindings stack))
             interp-st))

(define interp-st-set-debug (debug interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-debug debug stack)
             interp-st))

(define interp-st-set-minor-debug (debug interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-minor-debug debug stack)
             interp-st))


(define interp-st-decrement-reclimit (interp-st)
  :guard (posp (interp-st->reclimit interp-st))
  (update-interp-st->reclimit (1- (interp-st->reclimit interp-st)) interp-st))

(define interp-st-increment-reclimit (interp-st)
  (update-interp-st->reclimit (1+ (lnfix (interp-st->reclimit interp-st))) interp-st))




;; Interp-st-bind:
;;
;; This works differently from a regular LET* or something.  Instead of
;; containing an expression whose value is returned, this splices some bindings
;; in between bindings that set some interp-st slots to new values and restore
;; them to their old values.  E.g.:
;;   (b* (...
;;        ((interp-st-bind
;;          (flags new-flag-expr flag-backup-var)
;;          (equiv-contexts new-equiv-contexts-expr))
;;         ((gl-interp-recursive-call err successp-interp-st state)
;;          (gl-rewrite-relieve-hyps rule.hyps interp-st state)))
;;        ...)
;;     ...)
;; Note: The bindings are of the form
;;        (slot-name new-value-expr &optional backup-varname)
;; If backup-varname is specified, it should be already bound to the current value of that slot.
;; Slot is accessed with interp-st->[slotname] and updated with update-interp-st->[slotname].



(define interp-st-bind-default-backup-name (slotname)
  :mode :program
  (intern-in-package-of-symbol
   (concatenate 'string "CURRENT-INTERP-ST-" (symbol-name slotname))
   'fgl::gl-package-symbol))

(define interp-st-accessor (slotname)
  :mode :program
  (acl2::tmpl-sym-sublis `(("<FIELD>" . ,(symbol-name slotname)))
                         'interp-st-><field>
                         'fgl::gl-package))

(define interp-st-updater (slotname)
  :mode :program
  (acl2::tmpl-sym-sublis `(("<FIELD>" . ,(symbol-name slotname)))
                         'update-interp-st-><field>
                         'fgl::gl-package))

(define interp-st-bind-backup-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((when (eql (len arg) 3))
        (interp-st-bind-backup-vals (cdr args) interp-st-name))
       ((list slotname ?expr) arg)
       (backup-name (interp-st-bind-default-backup-name slotname)))
    (cons `(,backup-name (,(interp-st-accessor slotname) ,interp-st-name))
          (interp-st-bind-backup-vals (cdr args) interp-st-name))))

(define interp-st-bind-new-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((list slotname expr) arg))
    (cons `(,interp-st-name (,(interp-st-updater slotname) ,expr ,interp-st-name))
          (interp-st-bind-new-vals (cdr args) interp-st-name))))

(define interp-st-unbind-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((list slotname ?expr backup-name) arg)
       (backup-name (or backup-name (interp-st-bind-default-backup-name slotname))))
    (cons `(,interp-st-name (,(interp-st-updater slotname) ,backup-name ,interp-st-name))
          (interp-st-unbind-vals (cdr args) interp-st-name))))

(def-b*-binder interp-st-bind
  :body
  `(b* (,@(interp-st-bind-backup-vals args 'interp-st)
        ,@(interp-st-bind-new-vals args 'interp-st)
        ,@forms
        ,@(interp-st-unbind-vals args 'interp-st))
     ,rest-expr))



(define interp-st-bfr-p (x &key (interp-st 'interp-st))
  :enabled t
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok)
             (lbfr-p x)
             ok))

(define interp-st-bfr-mode (&key (interp-st 'interp-st))
  :enabled t
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (mode)
             (logicman->mode logicman)
             mode))

(define interp-st-bfr-state (&key (interp-st 'interp-st))
  :enabled t
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (bfrstate)
             (logicman->bfrstate logicman)
             bfrstate))

(define interp-st-bfr-not (x &key (interp-st 'interp-st))
  :enabled t
  :inline t
  :guard (interp-st-bfr-p x)
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (not)
             (bfr-not x)
             not))
