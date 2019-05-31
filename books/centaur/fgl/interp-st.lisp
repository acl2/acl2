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
(include-book "bvar-db-equivs")
(include-book "constraint-db")
(include-book "glcp-config")
(include-book "contexts")
(include-book "stack")
(include-book "centaur/fty/bitstruct" :dir :system)
(include-book "prof")
(include-book "array-alist")
(include-book "cgraph")
(local (include-book "std/lists/resize-list" :dir :System))
(local (in-theory (disable nth update-nth resize-list
                           acl2::resize-list-when-atom)))
(local (in-theory (disable unsigned-byte-p)))

(local (std::add-default-post-define-hook :fix))

(fty::defbitstruct interp-flags
  ((intro-bvars booleanp :default t)
   (intro-synvars booleanp :default t)
   (simplify-logic booleanp :default t)
   (trace-rewrites booleanp :default nil)))

(local (defthm unsigned-byte-p-of-flags
         (implies (interp-flags-p flags)
                  (unsigned-byte-p 60 flags))
         :hints(("Goal" :in-theory (enable interp-flags-p unsigned-byte-p)))))

(acl2::defstobj-clone constraint-pathcond pathcond :prefix "CONSTRAINT-")


(acl2::defstobj-clone bitarr acl2::bitarr :pkg fgl-pkg)

(stobjs::defnicestobj env$
  (alist :initially nil)
  (bitarr :type bitarr)
  (obj-alist :type (satisfies obj-alist-p) :fix obj-alist-fix))







(make-event
 `(stobjs::defnicestobj interp-st
    (stack :type stack)
    (logicman :type logicman)
    (bvar-db :type bvar-db)
    (pathcond :type pathcond)
    (constraint :type pathcond)
    (constraint-db :type (satisfies constraint-db-p) :fix constraint-db-fix :pred constraint-db-p)
    (prof :type interp-profiler)
    (backchain-limit :type integer :initially -1 :fix ifix)
    ;; (bvar-mode :type t)
    (equiv-contexts :type (satisfies equiv-contextsp) :fix equiv-contexts-fix :pred equiv-contextsp)
    (reclimit :type (integer 0 *) :initially 0 :fix lnfix :pred natp)
    (config :type (satisfies glcp-config-p) :initially ,(make-glcp-config) :fix glcp-config-fix :pred glcp-config-p)
    (flags :type (and (unsigned-byte 60)
                      (satisfies interp-flags-p))
           :initially ,(make-interp-flags)
           :fix interp-flags-fix :pred interp-flags-p)

    ;; backing arrays for fgarray primitives -- see fgarrays.lisp
    (fgarrays :type (array fgarray (0)) :resizable t :pred fgarray-alistp)
    (next-fgarray :type (integer 0 *) :initially 0 :fix lnfix :pred natp)

    ;; no logical significance
    (cgraph :type (satisfies cgraph-p) :initially nil :fix cgraph-fix)
    (cgraph-memo :type (satisfies cgraph-alist-p) :initially nil :fix cgraph-alist-fix)
    (cgraph-index :type (integer 0 *) :initially 0 :fix lnfix :pred natp)
    (ctrex-env :type env$)
    (sat-ctrex :type bitarr)

    (user-scratch :type (satisfies obj-alist-p) :initially nil :fix obj-alist-fix)

    (errmsg :type t)
    (debug-info :type t)))

;; (make-event
;;  `(defconst *interp-st-fields*
;;     ;; note: predfn is required if fix is provided
;;     '((stack :type stack)
;;       (logicman :type logicman)
;;       (bvar-db :type bvar-db)
;;       (pathcond :type pathcond)
;;       (constraint :type pathcond)
;;       (constraint-db :type (satisfies constraint-db-p) :fix constraint-db-fix :predfn constraint-db-p)
;;       (prof :type interp-profiler)
;;       (backchain-limit :type integer :initially -1 :fix lifix :predfn integerp)
;;       ;; (bvar-mode :type t)
;;       (equiv-contexts :type (satisfies equiv-contextsp) :fix equiv-contexts-fix :predfn equiv-contextsp)
;;       (reclimit :type (integer 0 *) :initially 0 :fix lnfix :predfn natp)
;;       (config :type (satisfies glcp-config-p) :initially ,(make-glcp-config) :fix glcp-config-fix :predfn glcp-config-p)
;;       (flags :type (and (unsigned-byte 60)
;;                         (satisfies interp-flags-p))
;;              :initially ,(make-interp-flags)
;;              :fix interp-flags-fix :predfn interp-flags-p)
;;       (errmsg :type t)
;;       (debug-info :type t))))


;; (local (defun member-eq-tree (x tree)
;;          (declare (xargs :guard (symbolp x)))
;;          (if (atom tree)
;;              (eq x tree)
;;            (or (member-eq-tree x (car tree))
;;                (member-eq-tree x (cdr tree))))))

;; (local (defun interp-st-fields-to-templates (fields)
;;          (declare (xargs :mode :program))
;;          (if (atom fields)
;;              nil
;;            (cons (b* ((name (caar fields))
;;                       (type (cadr (assoc-keyword :type (cdar fields))))
;;                       (initially (cadr (assoc-keyword :initially (cdar fields))))
;;                       (fix (cadr (assoc-keyword :fix (cdar fields))))
;;                       (predfn (cadr (assoc-keyword :predfn (cdar fields))))
;;                       (type-pred (acl2::translate-declaration-to-guard type name nil))
;;                       (typep (and type-pred (not (member-eq-tree 'satisfies type))))
;;                       (pred (or type-pred
;;                                 (and (symbolp type)
;;                                      `(,(intern-in-package-of-symbol (concatenate 'string (symbol-name type) "P")
;;                                                                      type)
;;                                        ,name))))
;;                       (- (and (not pred)
;;                               (er hard? 'interp-st-fields-to-templates
;;                                   "couldn't figure out the predicate for the type of ~x0~%" (car fields)))))
;;                    (acl2::make-tmplsubst :atoms `((<field> . ,name)
;;                                                   (:<field> . ,(intern$ (symbol-name (caar fields)) "KEYWORD"))
;;                                                   (<fieldcase> . ,(if (atom (cdr fields))
;;                                                                       t
;;                                                                     (intern$ (symbol-name (caar fields)) "KEYWORD")))
;;                                                   (<type> . ,type)
;;                                                   (<initially> . ,(and initially
;;                                                                        `(:initially ,initially)))
;;                                                   (<pred> . ,pred)
;;                                                   (<predfn> . ,predfn)
;;                                                   (<fix> . ,fix))
;;                                          :features (append (cond ((eq pred t) '(:no-pred))
;;                                                                  (typep '(:type-pred)) 
;;                                                                  (t nil))
;;                                                            (if fix
;;                                                                '(:fix)
;;                                                              '(:no-fix)))
;;                                          :strs `(("<FIELD>" . ,(symbol-name (caar fields))))
;;                                          :pkg-sym 'fgl::foo))
;;                  (interp-st-fields-to-templates (cdr fields))))))

;; (make-event
;;  `(defconst *interp-st-field-templates*
;;     ',(interp-st-fields-to-templates *interp-st-fields*)))
  

;; (make-event
;;  (acl2::template-subst
;;   '(defstobj interp-st
;;      (:@proj fields (interp-st-><field> :type <type> . <initially>))
;;      :renaming ((:@append fields
;;                  (:@ :fix
;;                   (interp-st-><field> interp-st-><field>1)
;;                   (update-interp-st-><field> update-interp-st-><field>1)))))
;;   :subsubsts `((fields . ,*interp-st-field-templates*))))


;; (local (defthm unsigned-byte-60-when-interp-flags
;;          (implies (interp-flags-p x)
;;                   (unsigned-byte-p 60 x))
;;          :hints(("Goal" :in-theory (enable interp-flags-p)))))

;; (local (in-theory (disable unsigned-byte-p)))

;; (make-event
;;  (cons
;;   'progn
;;   (acl2::template-append
;;    '((:@ :fix
;;       (define interp-st-><field> (interp-st)
;;         :inline t
;;         :returns (<field> <predfn> (:@ :type-pred
;;                                     :rule-classes (:rewrite (:type-prescription :typed-term <field>))))
;;         (mbe :logic (<fix> (interp-st-><field>1 interp-st))
;;              :exec (interp-st-><field>1 interp-st)))

;;       (define update-interp-st-><field> ((x <predfn> :type <type>)
;;                                          interp-st)
;;         :split-types t
;;         :inline t
;;         (mbe :logic (update-interp-st-><field>1 (<fix> x) interp-st)
;;              :exec (update-interp-st-><field>1 x interp-st)))))
;;      *interp-st-field-templates*)))

;; (make-event
;;  (acl2::template-subst
;;   '(std::defenum interp-st-field-p ((:@proj fields :<field>)))
;;   :subsubsts `((fields . ,*interp-st-field-templates*))))

;; (make-event
;;  (acl2::template-subst
;;   '(define interp-st-get ((key interp-st-field-p) &optional (interp-st 'interp-st))
;;      ;; bozo define doesn't correctly support :non-executable t with macro args
;;      (declare (xargs :non-executable t))
;;      :no-function t
;;      :prepwork ((local (in-theory (enable interp-st-field-fix))))
;;      (prog2$ (acl2::throw-nonexec-error 'interp-st-get-fn (list key interp-st))
;;              (case key
;;                (:@proj fields (<fieldcase> (interp-st-><field> interp-st))))))
;;   :subsubsts `((fields . ,*interp-st-field-templates*))))

;; (make-event
;;  (acl2::template-subst
;;   '(defsection interp-st-field-basics
;;      (local (in-theory (enable interp-st-get
;;                                interp-st-field-fix
;;                                interp-stp)))
;;      (local (in-theory (enable (:@append fields
;;                                 (:@ :fix
;;                                  interp-st-><field>
;;                                  update-interp-st-><field>)))))

;;      (:@append fields
;;       (def-updater-independence-thm interp-st-><field>-updater-independence
;;         (implies (equal (interp-st-get :<field> new)
;;                         (interp-st-get :<field> old))
;;                  (equal (interp-st-><field> new)
;;                         (interp-st-><field> old))))

;;       (defthm update-interp-st-><field>-preserves-others
;;         (implies (not (equal (interp-st-field-fix i) :<field>))
;;                  (equal (interp-st-get i (update-interp-st-><field> x interp-st))
;;                         (interp-st-get i interp-st))))

;;       (defthm update-interp-st-><field>-self-preserves-interp-st
;;         (implies (interp-stp interp-st)
;;                  (equal (update-interp-st-><field>
;;                          (interp-st-><field> interp-st)
;;                          interp-st)
;;                         interp-st))
;;         :hints(("Goal" :in-theory (enable interp-stp
;;                                           aignet::redundant-update-nth))))

;;       (defthm interp-st-><field>-of-update-interp-st-><field>
;;         (equal (interp-st-><field> (update-interp-st-><field> x interp-st))
;;                (:@ :fix (<fix> x))
;;                (:@ :no-fix x)))

;;       (:@ :type-pred
;;        (defthm interp-st-implies-<field>-type
;;          (implies (interp-stp interp-st)
;;                   (let ((<field> (interp-st-><field> interp-st)))
;;                     <pred>))
;;          :hints(("Goal" :in-theory (enable interp-st-><field>)))
;;          :rule-classes :type-prescription))

;;       (:@ (and (not :type-pred) (not :no-pred))
;;        (defthm interp-st-implies-<field>-type
;;          (implies (interp-stp interp-st)
;;                   (let ((<field> (interp-st-><field> interp-st)))
;;                     <pred>))
;;          :hints(("Goal" :in-theory (enable interp-st-><field>))))))

;;      (:@proj fields
;;       (in-theory (disable interp-st-><field>
;;                           update-interp-st-><field>)))

;;      (local (in-theory (disable interp-st-get
;;                                 interp-st-field-fix)))

;;      ;; test:
;;      (local 
;;       (defthm interp-st-test-updater-independence
;;         (b* ((interp-st1 (update-interp-st->reclimit reclimit interp-st))
;;              (interp-st2 (update-interp-st->logicman logicman interp-st)))
;;           (and (equal (interp-st->constraint interp-st2) (interp-st->constraint interp-st))
;;                (equal (interp-st->constraint interp-st1) (interp-st->constraint interp-st)))))))
  
;;   :subsubsts `((fields . ,*interp-st-field-templates*))))

(define interp-st-put-user-scratch (key val interp-st)
  :returns (new-interp-st)
  (update-interp-st->user-scratch
   (hons-acons key val (interp-st->user-scratch interp-st))
   interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :user-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))



(defthm interp-st-implies-natp-flags
  (natp (interp-st->flags interp-st))
  :hints(("Goal" :in-theory (enable interp-st->flags)))
  :rule-classes :type-prescription)

(in-theory (disable interp-stp))






(define interp-st-prof-push (name interp-st)       
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-push name interp-profiler)
   interp-st))

(define interp-st-prof-pop-increment (successp interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-pop-increment successp interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-def (name interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-def name interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-exec (name interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-exec name interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-g (name interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-g name interp-profiler)
   interp-st))

(define interp-st-prof-unwind-stack (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-unwind-stack interp-profiler)
   interp-st))

(define interp-st-prof-print-report (interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (res)
   (prof-print-report interp-profiler)
   res))

(define interp-st-prof-report (interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-report interp-profiler)
   interp-st))

(define interp-st-prof-reset (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-reset interp-profiler)
   interp-st))

(define interp-st-prof-enable (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp t interp-profiler)
   interp-st))

(define interp-st-prof-disable (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp nil interp-profiler)
   interp-st))

(define interp-st-prof-enabledp (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (enabledp)
   (prof-enabledp interp-profiler)
   enabledp))

(define update-interp-st-prof-enabledp ((val booleanp) interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp val interp-profiler)
   interp-st))




(define interp-st-bindings (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-bindings stack)
             bindings))

(define interp-st-minor-bindings (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-minor-bindings stack)
             bindings))

(define interp-st-stack-frames (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-frames stack)
             frames))

(define interp-st-stack-minor-frames (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-minor-frames stack)
             frames))

(define interp-st-scratch-len (interp-st)
  :enabled t :hooks nil
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-scratch-len stack)
             len))

(define interp-st-pop-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (and (< 1 (interp-st-stack-frames interp-st))
              (eql 1 (interp-st-stack-minor-frames interp-st))
              (eql 0 (interp-st-scratch-len interp-st)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-frame stack)
             interp-st))

(define interp-st-pop-minor-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (and (< 1 (interp-st-stack-minor-frames interp-st))
              (eql 0 (interp-st-scratch-len interp-st)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-minor-frame stack)
             interp-st))



(define interp-st-pop-scratch (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< 0 (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-scratch stack)
             interp-st))

(define interp-st-top-scratch (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< 0 (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (obj)
             (stack-top-scratch stack)
             obj))

(define interp-st-nth-scratch ((n natp) interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< n (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (obj)
             (stack-nth-scratch n stack)
             obj))


(defsection interp-st-push/pop-scratch-kinds
  (local (include-book "scratchobj"))
  ;; (local (include-book "tools/templates" :dir :system))
  (make-event
   `(progn
      .
      ,(acl2::template-append
        '((define interp-st-push-scratch-<kind> ((x <pred>)
                                                 interp-st)
            :enabled t :hooks nil
            :inline t
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (stack)
                       (stack-push-scratch-<kind> x stack)
                       interp-st))
          (define interp-st-top-scratch-<kind> (interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< 0 (interp-st-scratch-len interp-st))
                        (scratchobj-case (interp-st-top-scratch interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj)
                       (stack-top-scratch-<kind> stack)
                       obj))

          (define interp-st-nth-scratch-<kind> ((n natp) interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< n (interp-st-scratch-len interp-st))
                        (scratchobj-case (interp-st-nth-scratch n interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj)
                       (stack-nth-scratch-<kind> n stack)
                       obj))

          (define interp-st-update-scratch-<kind> ((n natp) (obj <pred>) interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (< n (interp-st-scratch-len interp-st))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (stack)
                       (stack-update-scratch-<kind> n obj stack)
                       interp-st))

          (define interp-st-pop-scratch-<kind> (interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< 0 (interp-st-scratch-len interp-st))
                        (scratchobj-case (interp-st-top-scratch interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj stack)
                       (stack-pop-scratch-<kind> stack)
                       (mv obj interp-st))))
        *scratchobj-tmplsubsts*))))

(define interp-st-add-binding ((var pseudo-var-p)
                               (val gl-object-p)
                               interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-binding var val stack)
             interp-st))

(define interp-st-set-bindings ((bindings gl-object-bindings-p)
                                interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-bindings bindings stack)
             interp-st))

(define interp-st-add-minor-bindings ((bindings gl-object-bindings-p)
                                      interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-minor-bindings bindings stack)
             interp-st))

(define interp-st-set-minor-bindings ((bindings gl-object-bindings-p)
                                      interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-minor-bindings bindings stack)
             interp-st))

(define interp-st-push-frame ((bindings gl-object-bindings-p)
                              interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((stack (stack-push-frame stack)))
               (stack-set-bindings bindings stack))
             interp-st))

(define interp-st-push-minor-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((bindings (stack-minor-bindings stack))
                  (stack (stack-push-minor-frame stack)))
               (stack-set-minor-bindings bindings stack))
             interp-st))

(define interp-st-set-debug (debug interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-debug debug stack)
             interp-st))

(define interp-st-set-minor-debug (debug interp-st)
  :enabled t :hooks nil
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



(define interp-st-bfr-p (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok)
             (lbfr-p x)
             ok))

(define interp-st-bfr-fix (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  :guard (interp-st-bfr-p x)
  (mbe :logic (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (new-x)
                         (lbfr-fix x)
                         new-x)
       :exec x))

(define interp-st-bfr-listp (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok)
             (lbfr-listp x)
             ok))


(define interp-st-bfr-mode (&optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (mode)
             (logicman->mode logicman)
             mode))

(define interp-st-bfr-state (&optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (bfrstate)
             (logicman->bfrstate logicman)
             bfrstate))

(define interp-st-bfr-not (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  :inline t
  :guard (interp-st-bfr-p x)
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (not)
             (bfr-not x)
             not))


(define interp-st-nvars-ok (interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (ok)
             (equal (next-bvar bvar-db) (bfr-nvars))
             ok))


(local
 (defthm subsetp-of-bvar-db-bfrlist-when-get-term->bvar$a
   (implies (get-term->bvar$a x bvar-db)
            (subsetp (gl-object-bfrlist x) (bvar-db-bfrlist bvar-db)))
   :hints (("goal" :use ((:instance subsetp-bfrlist-of-bvar-db-bfrlist
                          (m (get-term->bvar$a x bvar-db))))
            :in-theory (disable subsetp-bfrlist-of-bvar-db-bfrlist)))))

(define interp-st-add-term-bvar ((x gl-object-p) interp-st state)
  :returns (mv bfr new-interp-st)
  :guard (interp-st-nvars-ok interp-st)
  :prepwork ((local (in-theory (enable interp-st-nvars-ok))))
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (bfr bvar-db logicman)
             (b* ((nextvar (next-bvar bvar-db))
                  (bvar-db (add-term-bvar (gl-object-fix x) bvar-db))
                  (bvar-db (maybe-add-equiv-term (gl-object-fix x) nextvar bvar-db state))
                  (logicman (logicman-add-var logicman))
                  (bfr (bfr-var nextvar logicman)))
               (mv bfr bvar-db logicman))
             (mv bfr interp-st))
  ///
  (defret interp-st-nvars-ok-of-interp-st-add-term-bvar
    (implies (interp-st-nvars-ok interp-st)
             (interp-st-nvars-ok new-interp-st)))

  (defret bfr-p-of-interp-st-add-term-bvar
    (implies (interp-st-nvars-ok interp-st)
             (lbfr-p bfr (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-bfr-p))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$a (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bvar-db-bfrlist-of-<fn>
    (acl2::set-equiv (bvar-db-bfrlist (interp-st->bvar-db new-interp-st))
                     (append (gl-object-bfrlist x)
                             (bvar-db-bfrlist (interp-st->bvar-db interp-st)))))

  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key (interp-st->logicman new-interp-st))
                    (logicman-get key (interp-st->logicman interp-st))))))

(define interp-st-add-term-bvar-unique ((x gl-object-p) interp-st state)
  :returns (mv bfr new-interp-st)
  :guard (interp-st-nvars-ok interp-st)
  :prepwork ((local (in-theory (enable interp-st-nvars-ok
                                       bfr-varname-p))))
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (bfr bvar-db logicman)
             (b* ((var (get-term->bvar x bvar-db))
                  ((when var)
                   (mv (bfr-var var logicman) bvar-db logicman))
                  (nextvar (next-bvar bvar-db))
                  (bvar-db (add-term-bvar (gl-object-fix x) bvar-db))
                  (bvar-db (maybe-add-equiv-term (gl-object-fix x) nextvar bvar-db state))
                  (logicman (logicman-add-var logicman))
                  (bfr (bfr-var nextvar logicman)))
               (mv bfr bvar-db logicman))
             (mv bfr interp-st))
  ///
  (defret interp-st-nvars-ok-of-interp-st-add-term-bvar-unique
    (implies (interp-st-nvars-ok interp-st)
             (interp-st-nvars-ok new-interp-st)))

  (defret bfr-p-of-interp-st-add-term-bvar-unique
    (implies (interp-st-nvars-ok interp-st)
             (lbfr-p bfr (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-bfr-p))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$a (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bvar-db-bfrlist-of-<fn>
    (acl2::set-equiv (bvar-db-bfrlist (interp-st->bvar-db new-interp-st))
                     (append (gl-object-bfrlist x)
                             (bvar-db-bfrlist (interp-st->bvar-db interp-st)))))

  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key (interp-st->logicman new-interp-st))
                    (logicman-get key (interp-st->logicman interp-st))))))


(def-updater-independence-thm logicman->aignet-of-interp-st->logicman
  (implies (equal (logicman-get :aignet (interp-st->logicman new))
                  (logicman-get :aignet (interp-st->logicman old)))
           (equal (logicman->aignet (interp-st->logicman new))
                  (logicman->aignet (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->aignet-of-update)))))

(def-updater-independence-thm logicman->strash-of-interp-st->logicman
  (implies (equal (logicman-get :strash (interp-st->logicman new))
                  (logicman-get :strash (interp-st->logicman old)))
           (equal (logicman->strash (interp-st->logicman new))
                  (logicman->strash (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->strash-of-update)))))

(def-updater-independence-thm logicman->ipasir-of-interp-st->logicman
  (implies (equal (logicman-get :ipasir (interp-st->logicman new))
                  (logicman-get :ipasir (interp-st->logicman old)))
           (equal (logicman->ipasir (interp-st->logicman new))
                  (logicman->ipasir (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->ipasir-of-update)))))

(def-updater-independence-thm logicman->sat-lits-of-interp-st->logicman
  (implies (equal (logicman-get :sat-lits (interp-st->logicman new))
                  (logicman-get :sat-lits (interp-st->logicman old)))
           (equal (logicman->sat-lits (interp-st->logicman new))
                  (logicman->sat-lits (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->sat-lits-of-update)))))

(def-updater-independence-thm logicman->mode-of-interp-st->logicman
  (implies (equal (logicman-get :mode (interp-st->logicman new))
                  (logicman-get :mode (interp-st->logicman old)))
           (equal (logicman->mode (interp-st->logicman new))
                  (logicman->mode (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->mode-of-update)))))

(def-updater-independence-thm logicman->aignet-refcounts-of-interp-st->logicman
  (implies (equal (logicman-get :aignet-refcounts (interp-st->logicman new))
                  (logicman-get :aignet-refcounts (interp-st->logicman old)))
           (equal (logicman->aignet-refcounts (interp-st->logicman new))
                  (logicman->aignet-refcounts (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->aignet-refcounts-of-update)))))

(def-updater-independence-thm logicman->refcounts-index-of-interp-st->logicman
  (implies (equal (logicman-get :refcounts-index (interp-st->logicman new))
                  (logicman-get :refcounts-index (interp-st->logicman old)))
           (equal (logicman->refcounts-index (interp-st->logicman new))
                  (logicman->refcounts-index (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->refcounts-index-of-update)))))


(def-updater-independence-thm logicman-invar-of-interp-st-logicman-extension
  (implies (and (equal new-logicman (interp-st->logicman new))
                (equal old-logicman (interp-st->logicman old))
                (logicman-extension-p new-logicman old-logicman)
                (logicman-invar old-logicman)
                (equal (logicman->ipasir new-logicman)
                       (logicman->ipasir old-logicman))
                (equal (logicman->sat-lits new-logicman)
                       (logicman->sat-lits old-logicman))
                (equal (logicman->refcounts-index new-logicman)
                       (logicman->refcounts-index old-logicman))
                (equal (logicman->aignet-refcounts new-logicman)
                       (logicman->aignet-refcounts old-logicman)))
           (logicman-invar (interp-st->logicman new))))






;; Trace this!
(define glcp-interp-error-message ((str stringp)
                                   (arglist))
  :returns (error-message (or (consp error-message)
                              (stringp error-message))
                          :rule-classes :type-prescription)
  (if arglist
      (cons (str-fix str) arglist)
    (str-fix str)))

(defmacro gl-msg (str &rest args)
  `(glcp-interp-error-message ,str ,(make-fmt-bindings acl2::*base-10-chars* args)))


(define gl-interp-store-debug-info (msg obj interp-st)
  :returns new-interp-st
  (b* (((when (interp-st->errmsg interp-st))
        interp-st)
       (interp-st (update-interp-st->errmsg msg interp-st))
       (stack-obj (stobj-let ((stack (interp-st->stack interp-st)))
                             (obj)
                             (stack-extract stack)
                             obj))
       (interp-st (update-interp-st->debug-info (list obj stack-obj) interp-st)))
    interp-st)
  ///

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-of-<fn>
    (implies msg
             (interp-st->errmsg new-interp-st)))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (and (not (equal msg x))
                  (not (equal (interp-st->errmsg interp-st) x)))
             (not (equal (interp-st->errmsg new-interp-st) x)))))

(defmacro gl-interp-error (&key msg debug-obj (nvals '1))
  `(b* ((msg ,msg)
        (debug-obj ,debug-obj)
        (interp-st (gl-interp-store-debug-info msg debug-obj interp-st)))
     ,(if (eql nvals 0)
          'interp-st
        `(mv ,@(acl2::repeat nvals nil) interp-st))))
