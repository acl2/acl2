; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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


(in-package "ACL2")

(include-book "bddify-correct")

(include-book "../gl/g-if")
(include-book "../gl/gify")
(include-book "../gl/gify-thms")
(include-book "../gl/eval-f-i-cp")
(include-book "../gl/bvecs")
(include-book "../gl/gify-clause-proc")
(local (include-book "../gl/general-object-thms"))
(local (include-book "eval-restrict"))

(local (in-theory (disable gl::generic-geval gl::generic-geval-alt-def
                           gl::geval-for-meta-gtests-nonnil-correct)))

(defun atom-key-gobj-val-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (not (gl::g-keyword-symbolp x))
      (and (consp (car x))
           (atom (caar x))
           (not (gl::g-keyword-symbolp (caar x)))
           (gl::gobjectp (cdar x))
           (atom-key-gobj-val-alistp (cdr x)))))

(local
 (progn
   #!GL (defthmd not-keyword-symbolp-car-impl
          (implies (not (g-keyword-symbolp (car x)))
                   (and (not (g-concrete-p x))
                        (not (g-boolean-p x))
                        (not (g-number-p x))
                        (not (g-ite-p x))
                        (not (g-apply-p x))
                        (not (g-var-p x))))
          :hints(("Goal" :in-theory
                  (enable* g-concrete-p g-boolean-p g-number-p
                           g-ite-p g-apply-p g-var-p
                           g-keyword-symbolp-def)))
          :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthmd atom-key-gobj-val-alistp-gobjectp
     (implies (atom-key-gobj-val-alistp x)
              (gl::gobjectp x))
     :hints (("goal" :expand ((gl::gobjectp x)
                              (gl::gobjectp (car x))
                              (gl::gobjectp (caar x)))
              :induct (atom-key-gobj-val-alistp x)
              :in-theory (enable
                          gl::not-keyword-symbolp-car-impl)))
     :rule-classes ((:rewrite :backchain-limit-lst 1)
                    :forward-chaining))

   (defthm atom-key-gobj-val-alistp-assoc-eval
     (implies (atom-key-gobj-val-alistp x)
              (equal (gl::generic-geval (hons-assoc-equal key x) env)
                     (hons-assoc-equal key (gl::generic-geval x env))))
     :hints (("goal" :in-theory (e/d (hons-assoc-equal
                                      atom-key-gobj-val-alistp-gobjectp)
                                     (suffixp
                                      ;; gl::concrete-key-alistp
                                      member-eq
                                      gl::gobjectp-cons-case
                                      ;; gl::gobjectp-car-cdr-when-cons
; gl::generic-geval-when-g-var-tag
                                      gl::general-number-components-ev))
              :induct (hons-assoc-equal key x))))))

(defun gobj-alist-to-bfr-alist (x hyp)
  (declare (xargs :guard (and (atom-key-gobj-val-alistp x)
                              (gl::bfr-p hyp))))
  (if (atom x)
      (mv nil nil)
    (b* ((test (gl::gtests (cdar x) hyp))
         ((mv rst rst-unknown)
          (gobj-alist-to-bfr-alist (cdr x) hyp)))
      (mv (hons-acons! (caar x) (gl::gtests-nonnil test) rst)
          (gl::bfr-or (let ((unk (gl::gtests-unknown test)))
                        (and unk
                             (prog2$ (cw "Unknown: ~x0~%" (caar x))
                                     unk)))
                      rst-unknown)))))

(local
 (defthm hons-assoc-equal-gobj-alist-to-bfr-alist-iff
   (implies (atom-key-gobj-val-alistp x)
            (iff (hons-assoc-equal key (mv-nth 0 (gobj-alist-to-bfr-alist
                                                  x hyp)))
                 (hons-assoc-equal key x)))))










(local
 (progn

   (defthm bfr-alistp-gobj-alist-to-bfr-alist
     (implies (atom-key-gobj-val-alistp x)
              (gl::bfr-alistp (mv-nth 0 (gobj-alist-to-bfr-alist x hyp)))))
   
   (defthm bfr-p-gobj-alist-to-bfr-alist
     (implies (and (gl::bfr-p hyp)
                   (atom-key-gobj-val-alistp x))
              (gl::bfr-p (mv-nth 1 (gobj-alist-to-bfr-alist x hyp)))))


   ;; (local (in-theory
   ;;         (disable GL-THM::GTESTS-NONNIL-CORRECT-FOR-GL-BASIS-EV
   ;;                  gl-thm::general-concrete-obj-correct-gobj-fix-for-glcp-geval
   ;;                  GL-THM::GTESTS-NONNIL-CORRECT-FOR-GLCP-GEVAL
   ;;                  GL-THM::NON-CONSP-EVAL-CORRECT-FOR-GLCP-GEVAL)))

   (defthmd non-keyword-atom-gobjectp
     (implies (and (not (gl::g-keyword-symbolp x))
                   (not (consp x)))
              (gobjectp x))
     :hints(("Goal" :in-theory (enable gl::gobjectp-def))))

   (defthmd gobjectp-cons-case-inverse
     (implies (and (consp x)
                   (not (gl::g-keyword-symbolp (car x)))
                   (not (consp (car x)))
                   (gobjectp (cdr x)))
              (gobjectp x))
     :hints(("Goal" :in-theory (enable gl::gobjectp-def))))

   (defthm bfr-eval-alist-hons-assoc-equal-iff
     (iff (hons-assoc-equal x (gl::bfr-eval-alist al env))
          (hons-assoc-equal x al)))



 (defthm hons-assoc-equal-generic-geval-atom-key-gobj-val-alistp-iff
   (implies (atom-key-gobj-val-alistp x)
            (iff (hons-assoc-equal key (gl::generic-geval x env))
                 (hons-assoc-equal key x)))
   :hints (("goal" :induct (atom-key-gobj-val-alistp x)
            :in-theory (e/d
               (hons-assoc-equal
                atom-key-gobj-val-alistp-gobjectp
                gl::not-keyword-symbolp-car-impl
                non-keyword-atom-gobjectp
                gobjectp-cons-case-inverse)
               (member-eq hons-assoc-equal
                          gl::gobjectp-cons-case
                          gl::general-number-components-ev
                          (:definition atom-key-gobj-val-alistp)
                          gl::generic-geval-non-gobjectp
                          gl::general-concrete-obj-correct
                          ;; gl::general-consp-car-correct
                          ;;                gl::general-consp-cdr-correct
; gl::generic-geval-when-g-var-tag
                          gl::gobj-fix-when-not-gobjectp)))
           (and stable-under-simplificationp
                '(:expand ((:with gl::generic-geval (gl::generic-geval (car x) env))
                           (:with gl::generic-geval (gl::generic-geval x env))
                           (:free (a b) (hons-assoc-equal key (cons a b)))
                           (:free (a b) (hons-assoc-equal (caar x) (cons a b)))
                           (hons-assoc-equal key x)
                           (hons-assoc-equal key nil)
                           (hons-assoc-equal (caar x) x)
                           (atom-key-gobj-val-alistp x))))))

   (defthm eval-gobj-alist
     (implies (and (atom-key-gobj-val-alistp x)
                   (gl::bfr-eval hyp (car env))
                   (gl::bfr-p hyp)
                   (not (gl::bfr-eval (mv-nth 1 (gobj-alist-to-bfr-alist x hyp))
                                      (car env))))
              (iff (cdr (hons-assoc-equal
                         key
                         (gl::bfr-eval-alist
                          (mv-nth 0
                                  (gobj-alist-to-bfr-alist
                                   x hyp))
                          (car env))))
                   (cdr (hons-assoc-equal key (gl::generic-geval x env)))))
     :hints (("goal" :in-theory
              (e/d
               (hons-assoc-equal
                atom-key-gobj-val-alistp-gobjectp
                gl::not-keyword-symbolp-car-impl
                non-keyword-atom-gobjectp
                gobjectp-cons-case-inverse)
               (member-eq hons-assoc-equal
                          gl::gobjectp-cons-case
                          gl::general-number-components-ev
                          atom-key-gobj-val-alistp
                          gl::generic-geval-non-gobjectp
                          gl::general-concrete-obj-correct
                          ;; gl::general-consp-car-correct
                          ;;                gl::general-consp-cdr-correct
; gl::generic-geval-when-g-var-tag
                          gl::gobj-fix-when-not-gobjectp))
              :do-not-induct t
              :expand ((:with gl::generic-geval (gl::generic-geval (car x) env))
                       (:with gl::generic-geval (gl::generic-geval x env))
                       (:free (a b) (hons-assoc-equal key (cons a b)))
                       (:free (a b) (hons-assoc-equal (caar x) (cons a b)))
;(gl::general-concrete-obj x)
;(gl::concrete-gobjectp x)
                       (hons-assoc-equal key x)
                       (hons-assoc-equal key nil)
                       (hons-assoc-equal (caar x) x)
                       (atom-key-gobj-val-alistp x))
              :induct (gobj-alist-to-bfr-alist x hyp))))

   (defun aig-eval-ind (x)
     (cond ((atom x) x)
           ((equal (cdr x) nil) (aig-eval-ind (car x)))
           (t (list (aig-eval-ind (car x))
                    (aig-eval-ind (cdr x))))))

   (defthm aig-eval-eval-gobj-alist
     (implies (and (atom-key-gobj-val-alistp x)
                   (gl::bfr-eval hyp (car env))
                   (gl::bfr-p hyp)
                   (not (gl::bfr-eval 
                         (mv-nth 1 (gobj-alist-to-bfr-alist x hyp))
                         (car env))))
              (equal (aig-eval aig (gl::bfr-eval-alist
                                    (mv-nth 0 (gobj-alist-to-bfr-alist
                                               x hyp))
                                    (car env)))
                     (aig-eval aig (gl::generic-geval x env))))
     :hints (("goal" :induct (aig-eval-ind aig)
              :in-theory (enable aig-env-lookup))))

   (defthm aig-eval-list-eval-gobj-alist
     (implies (and (atom-key-gobj-val-alistp x)
                   (gl::bfr-eval hyp (car env))
                   (gl::bfr-p hyp)
                   (not (gl::bfr-eval 
                         (mv-nth 1 (gobj-alist-to-bfr-alist x hyp))
                         (car env))))
              (equal (aig-eval-list aig (gl::bfr-eval-alist
                                         (mv-nth 0 (gobj-alist-to-bfr-alist
                                                    x hyp))
                                         (car env)))
                     (aig-eval-list aig (gl::generic-geval x env))))
     :hints (("goal" :induct (aig-eval-list aig (gl::generic-geval x env)))))

   (defthm gobjectp-g-apply
     (implies (symbolp fn)
              (equal (gl::gobjectp (gl::g-apply fn args))
                     (gl::gobjectp args)))
     :hints (("goal" :in-theory (e/d (gl::gobjectp-def
                                      gl::g-apply gl::tag
                                      gl::g-apply-p
                                      gl::g-apply->fn
                                      gl::g-apply->args)
                                     ((force)))
              :expand ((gl::gobjectp (list* :g-apply fn args))))))
             

 
   (local (in-theory (disable atom-key-gobj-val-alistp
                              suffixp ; car-member-when-suffix
                              faig-bddify-pat
; gl::g-var-p-implies-gobjectp
; gl::g-concrete-p-gobjectp1
                              gobjectp)))))





(defun g-boolean-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (gl::g-boolean (car x))
          (g-boolean-list (cdr x)))))


(local
 (progn
   
(defthm gobjectp-g-boolean-list
  (implies (gl::bfr-listp x)
           (gl::gobjectp (g-boolean-list x)))
  :hints(("Goal" :in-theory (enable gl::tag))))

(defthm eval-of-g-boolean-list
  (implies (gl::bfr-listp x)
           (equal (gl::generic-geval (g-boolean-list x) env)
                  (gl::bfr-eval-list x (car env))))
  :hints(("Subgoal *1/2"
          :expand ((:free (x) (:with gl::generic-geval
                                     (gl::generic-geval (gl::g-boolean x)
                                                        env)))))))))


(defthmd gl::bfr-eval-alist-bfr-cases
  (equal (gl::bfr-eval-alist x vals)
         (gl::bfr-case
          :bdd (acl2::bdd-eval-alst x vals)
          :aig (acl2::aig-eval-alist x vals)))
  :hints(("Goal" :in-theory (enable bfr-eval))))

(defthmd bfr-eval-list-bfr-cases
  (equal (bfr-eval-list x env)
         (gl::bfr-case
          :bdd (acl2::eval-bdd-list x env)
          :aig (acl2::aig-eval-list x env)))
  :hints(("Goal" :in-theory (enable bfr-eval-list bfr-eval))))



(defthmd bfr-alistp-bfr-cases
  (equal (gl::bfr-alistp x)
         (gl::bfr-case
          :bdd (acl2::ubddp-val-alistp x)
          :aig t))
  :hints(("Goal" :in-theory (enable bfr-p)
          :induct (gl::bfr-alistp x))))


(defthmd bfr-listp-bfr-cases
  (equal (gl::bfr-listp x)
         (gl::bfr-case
          :bdd (and (acl2::ubdd-listp x) (true-listp x))
          :aig (true-listp x)))
  :hints(("Goal" :in-theory (enable gl::bfr-listp gl::bfr-p)
          :induct (len x))))

(defun aig-bfr-compose (x al)
  (gl::bfr-case
   :bdd (aig-q-compose x al)
   :aig (aig-compose x al)))

(defun aig-bfr-compose-list (x al)
  (if (atom x)
      nil
    (cons (aig-bfr-compose (car x) al)
          (aig-bfr-compose-list (cdr x) al))))



(defthm bfr-eval-of-aig-bfr-compose
  (equal (bfr-eval (aig-bfr-compose x al) env)
         (aig-eval x (gl::bfr-eval-alist al env)))
  :hints(("Goal" :in-theory (enable bfr-eval gl::bfr-eval-alist-bfr-cases
                                    aig-q-compose-correct))))

(defun aig-bfrify-list (tries aigs bfr-al maybe-wash-args)
  (declare (Xargs :guard t))
  (gl::bfr-case
   :bdd (b* (((mv bdds & exact)
              (ec-call (aig-bddify-list
                        tries aigs bfr-al maybe-wash-args))))
          (mv bdds exact))
   :aig (mv (aig-compose-list aigs bfr-al) t)))



(defthm eval-bdd-list-aig-q-compose-list
  (equal (eval-bdd-list (aig-q-compose-list aigs bdd-al) env)
         (aig-eval-list aigs (bdd-eval-alst bdd-al env)))
  :hints(("Goal" :in-theory (enable aig-q-compose-correct))))

(defthm aig-bfrify-list-ok
  (implies
   (gl::bfr-alistp bfr-al)
   (mv-let (res exact)
     (aig-bfrify-list tries aigs bfr-al maybe-wash-args)
     (implies exact
              (equal (bfr-eval-list res env)
                     (aig-eval-list aigs
                                    (gl::bfr-eval-alist bfr-al env))))))
  :hints(("Goal" :in-theory (enable bfr-eval-list-bfr-cases
                                    gl::bfr-eval-alist-bfr-cases
                                    bfr-alistp-bfr-cases
                                    aig-q-compose-correct)
          :induct (len aigs))))




(defthm aig-bfrify-list-bfr-listp
  (implies (gl::bfr-alistp bfr-al)
           (gl::bfr-listp (mv-nth 0 (aig-bfrify-list tries aigs bfr-al maybe-wash-args))))
  :hints (("goal" :in-theory (enable bfr-listp-bfr-cases bfr-alistp-bfr-cases))))

(in-theory (disable aig-bfrify-list))

(defun aig-eval-list-symbolic
  (x al tries maybe-wash-args hyp clk)
  (declare (xargs :guard (and (gl::gobjectp x)
                              (gl::gobjectp al)
                              (gl::gobjectp tries)
                              (gl::bfr-p hyp))
                  :guard-hints (("goal" :in-theory
                                 (e/d (gl::tag) ((force)
                                                 aig-bddify-list)))))
           (ignore clk))
  (let ((x (mbe :logic (gl::gobj-fix x) :exec x))
        (al (mbe :logic (gl::gobj-fix al) :exec al))
        (hyp (mbe :logic (gl::bfr-fix hyp) :exec hyp))
        (tries (if (gl::general-concretep tries)
                   (gl::general-concrete-obj tries)
                 (er hard? 'aig-eval-list-symbolic "Expected tries to be concrete~%"))))
    (if (and (atom-key-gobj-val-alistp al)
             (gl::general-concretep x))
        (b* (((mv bfr-al badp) (gobj-alist-to-bfr-alist al hyp))
             (- (and badp
                     (cw "The alist is not well-formed for aig-eval-list-symbolic~%")
                     ))
             (ans
              (if (eq badp t)
                  (gl::g-apply 'aig-eval-list (gl::gl-list x al))
                (if badp
                    (gl::gobj-ite-merge
                     badp
                     (gl::g-apply 'aig-eval-list (gl::gl-list x al))
                     (b* ((x-obj (gl::general-concrete-obj x))
                          ((mv bdd exact)
                           (aig-bfrify-list tries x-obj bfr-al
                                            maybe-wash-args)))
                       (if exact
                           (g-boolean-list bdd)
                         (prog2$ (cw "BDDification failed to produce an exact result~%")
                                 (gl::g-apply 'aig-eval-list (gl::gl-list x al)))))
                     hyp)
                  (b* ((x-obj (gl::general-concrete-obj x))
                       ((mv bdd exact)
                        (aig-bfrify-list tries x-obj bfr-al maybe-wash-args)))
                    (if exact
                        (g-boolean-list bdd)
                      (prog2$ (cw "BDDification failed to produce an exact result~%")
                              (gl::g-apply 'aig-eval-list (gl::gl-list x al))))))))
             (- (flush-hons-get-hash-table-link bfr-al)))
          ans)
      (prog2$ (cw "AL is not an atom-key-gobj-val-alistp. cars: ~x0~%"
                  (ec-call (strip-cars al)))
              (gl::g-apply 'aig-eval-list (gl::gl-list x al))))))







(local
 (defthm gobjectp-aig-eval-list-symbolic
   (gl::gobjectp (aig-eval-list-symbolic x al tries maybe-wash-args
                                         hyp clk))
     :hints(("Goal" :in-theory (disable member-eq
                                        atom-key-gobj-val-alistp
                                        member-equal-of-cons
                                        gl::gobjectp-cons-case
                                        aig-bddify-list)))))


(make-event
 `(defun ,(gl-fnsym 'aig-eval-list-with-bddify)
    (x al tries maybe-wash-args hyp clk)
    (declare (xargs :guard (and (gl::gobjectp x)
                                (gl::gobjectp al)
                                (gl::gobjectp tries)
                                (gl::bfr-p hyp))))
    (aig-eval-list-symbolic x al tries maybe-wash-args hyp clk)))


(defthm gobjectp-g-aig-eval-list
  (gl::gobjectp (glr aig-eval-list-with-bddify
                     x al tries maybe-wash-args hyp clk))
  :hints(("Goal" :in-theory (disable aig-eval-list-symbolic))))

(add-to-ruleset! gl::g-gobjectp-lemmas '(gobjectp-g-aig-eval-list))


(encapsulate nil
  (make-event 
   `(gl::defapply aig-eval-ap
                  ,(list* 'aig-eval-list
                          (cdar (table-alist 'gl::g-apply-table (w state)))))))

(encapsulate nil
  (gl::def-eval-g aig-eval-ev aig-eval-ap))

(local
 (progn
   (gl::correctness-lemmas aig-eval-ev)

   (gl::eval-g-prove-f-i aig-eval-ev-f-i-generic-geval aig-eval-ev
                         gl::generic-geval)

   (gl::eval-g-functional-instance
    gl::generic-geval-g-boolean
    aig-eval-ev gl::generic-geval)

   (gl::eval-g-functional-instance
    gl::general-concrete-obj-correct
    aig-eval-ev gl::generic-geval)

   (gl::eval-g-functional-instance
    aig-eval-list-eval-gobj-alist
    aig-eval-ev gl::generic-geval)

   (gl::eval-g-functional-instance
    eval-of-g-boolean-list
    aig-eval-ev gl::generic-geval)))

(in-theory (disable aig-bddify-list aig-eval-list))

(defun def-g-correctness-thm-fn (thmname fn eval hints world)
  (declare (xargs :mode :program))
  (b* ((formals (fgetprop fn 'formals t world)))
    `(progn (defthm ,thmname
              (implies ,'(bfr-eval gl::hyp (car gl::env))
                       (equal (,eval (glr ,fn ,@formals gl::hyp gl::clk)
                                     gl::env)
                              (,fn . ,(gl::eval-list-env eval formals))))
              :hints ,hints)
            (table gl::gl-function-info ',fn `(,(gl-fnsym ',fn)
                                               (,',thmname . ,',eval))))))

(defmacro def-g-correctness-thm (thmname fn eval &key hints)
  `(make-event (def-g-correctness-thm-fn
                 ',thmname ',fn ',eval ',hints (w state))))

;; (local
;;  (defthm eval-bdd-list-aig-q-compose-list
;;    (equal (eval-bdd-list (aig-q-compose-list x al) vals)
;;           (aig-eval-list x (bdd-eval-alst al vals)))
;;    :hints(("Goal" :in-theory (enable aig-eval-list
;;                                      aig-q-compose-correct)))))


(local
 (defthm g-aig-eval-list-correct1
   (implies (bfr-eval hyp (car env))
            (equal (aig-eval-ev (aig-eval-list-symbolic
                                 x al tries maybe-wash-args hyp clk)
                                env)
                   (aig-eval-list (aig-eval-ev x env)
                                  (aig-eval-ev al env))))
   :hints (("goal" :in-theory (e/d (eval-bdd-list-aig-q-compose-list
                                    gl::bfr-eval-of-bfr-fix gl::gobj-fix)
                                   (member-eq atom-key-gobj-val-alistp
                                              member-equal eval-bdd-list
                                              gl::gobj-fix-when-gobjectp
                                              gl::gobj-fix-when-not-gobjectp
                                              gl-thm::generic-geval-g-boolean-for-aig-eval-ev
                                              aig-bddify-list
                                              gl::gobj-fix))
            :do-not-induct t))))


(def-g-correctness-thm g-aig-eval-list-with-bddify-correct
  aig-eval-list-with-bddify aig-eval-ev
  :hints (("goal" :in-theory (e/d (aig-eval-list-with-bddify)
                                  (aig-eval-list-symbolic)))))

;; The theorems that we'll set as the preferred defs for the following
;; functions express each of these functions in terms of aig-eval-list.
;; Therefore, we only need to do the above proof about aig-eval-list.


(gl::set-preferred-def aig-eval-with-bddify
       aig-eval-in-terms-of-aig-eval-list)
(gl::set-preferred-def aig-eval-pat-with-bddify
       aig-eval-pat-in-terms-of-aig-eval-list)
(gl::set-preferred-def aig-eval-alist-with-bddify
       aig-eval-alist-in-terms-of-aig-eval-list)

(gl::set-preferred-def faig-eval-with-bddify
                       faig-eval-in-terms-of-faig-eval-list)
(gl::set-preferred-def faig-eval-list-with-bddify
       faig-eval-list-in-terms-of-aig-eval-list)
(gl::set-preferred-def faig-eval-pat-with-bddify
       faig-eval-pat-in-terms-of-faig-eval-list)
(gl::set-preferred-def faig-eval-alist-with-bddify
       faig-eval-alist-in-terms-of-faig-eval-list)

(gl::set-preferred-def aig-eval aig-eval-in-terms-of-with-bddify)
(table gl::override-props 'aig-eval '((recursivep . nil)))

(gl::set-preferred-def aig-eval-list aig-eval-list-in-terms-of-with-bddify)
(table gl::override-props 'aig-eval-list '((recursivep . nil)))

(gl::set-preferred-def aig-eval-pat aig-eval-pat-in-terms-of-with-bddify)
(table gl::override-props 'aig-eval-pat '((recursivep . nil)))

(gl::set-preferred-def faig-eval faig-eval-in-terms-of-with-bddify)

(gl::set-preferred-def faig-eval-list faig-eval-list-in-terms-of-with-bddify)
(table gl::override-props 'faig-eval-list '((recursivep . nil)))

(gl::set-preferred-def faig-eval-pat faig-eval-pat-in-terms-of-with-bddify)
(table gl::override-props 'faig-eval-pat '((recursivep . nil)))

(gl::set-preferred-def aig-eval-alist aig-eval-alist-in-terms-of-with-bddify)
(table gl::override-props 'aig-eval-alist '((recursivep . nil)))

(gl::set-preferred-def faig-eval-alist faig-eval-alist-in-terms-of-with-bddify)
(table gl::override-props 'faig-eval-alist '((recursivep . nil)))


