; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "design-fsm")
(include-book "cycle-compile")
(include-book "assign")

(include-book "std/stobjs/nicestobj" :dir :system)

(local (include-book "std/lists/resize-list" :dir :System))
(local (in-theory (disable nth update-nth resize-list
                           acl2::resize-list-when-atom)))


(local (in-theory (enable stobjs::redundant-update-nth)))
;; (local (defthm redundant-update-nth-free
;;          (implies (and (equal v (nth n x))
;;                        (< (nfix n) (len x)))
;;                   (equal (update-nth n v x)
;;                          x))))

(local (defthm member-equal-is-booleanp
         (iff (member-equal k '(t nil))
              (booleanp k))))



(local (in-theory (disable member-equal)))

(defconst *svtv-data-nonstobj-fields*
  `((design :type (satisfies design-p)
            :pred design-p :fix design-fix :initially ,(make-design :top ""))

    (user-names :type (satisfies svtv-namemap-p)
                :pred svtv-namemap-p :fix svtv-namemap-fix)
    (namemap :type (satisfies svtv-name-lhs-map-p)
                :pred svtv-name-lhs-map-p :fix svtv-name-lhs-map-fix)
    (namemap-validp :type (member t nil) :pred booleanp :fix bool-fix)
;;     (moddb-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)

    (base-values :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (base-nextstate :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (base-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)

    (cycle-phases :type (satisfies svtv-cyclephaselist-p) :pred svtv-cyclephaselist-p :fix svtv-cyclephaselist-fix :initially nil)
    (cycle-values :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (cycle-nextstate :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (cycle-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)))

(make-event
 `(stobjs::defnicestobj svtv-data$c
    ,@*svtv-data-nonstobj-fields*

    (moddb :type moddb)
    (aliases :type aliases)))


(defsection svtv-data-field-defs
  (local (defun make-svtv-data-field-defs (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (cons
              (b* ((name (caar fields)))
                (acl2::template-subst
                '(define svtv-data$a-><fieldname> (x)
                   :enabled t
                   (non-exec (svtv-data$c-><fieldname> x)))
                :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                :pkg-sym 'sv-package))
              (make-svtv-data-field-defs (cdr fields))))))
  (make-event
   (cons 'progn (make-svtv-data-field-defs *svtv-data-nonstobj-fields*))))


(define svtv-data$c-invalidate-base-fsm (svtv-data$c)
  :enabled t
  (update-svtv-data$c->base-fsm-validp nil svtv-data$c))

(define svtv-data$a-invalidate-base-fsm (x)
  :enabled t
  (non-exec (update-svtv-data$c->base-fsm-validp nil x)))

(define svtv-data$c-invalidate-cycle-fsm (svtv-data$c)
  :enabled t
  (update-svtv-data$c->cycle-fsm-validp nil svtv-data$c))

(define svtv-data$a-invalidate-cycle-fsm (x)
  :enabled t
  (non-exec (update-svtv-data$c->cycle-fsm-validp nil x)))

(define svtv-data$c-invalidate-namemap (svtv-data$c)
  :enabled t
  (update-svtv-data$c->namemap-validp nil svtv-data$c))

(define svtv-data$a-invalidate-namemap (x)
  :enabled t
  (non-exec (update-svtv-data$c->namemap-validp nil x)))


(define update-svtv-data$a->design ((design design-p) x)
  :guard (and (not (svtv-data$a->base-fsm-validp x))
              (modalist-addr-p (design->modalist design)))
  :enabled t
  (non-exec (update-svtv-data$c->design design x)))

(define svtv-data$c-compute-base-fsm (svtv-data$c)
  :guard (and (not (svtv-data$c->namemap-validp svtv-data$c))
              (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
              (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c))))
  :returns (mv errmsg new-svtv-data$c)
  (b* ((design (svtv-data$c->design svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (err fsm moddb aliases)
               (svtv-design-to-fsm design)
               (b* (((when err) (mv err svtv-data$c))
                    ((svtv-fsm fsm))
                    (svtv-data$c (update-svtv-data$c->base-values fsm.values svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-nextstate fsm.nextstate svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-fsm-validp t svtv-data$c)))
                 (mv nil svtv-data$c)))))

(define svtv-data$c->base-fsm (svtv-data$c)
  :returns (fsm svtv-fsm-p)
  (make-svtv-fsm
   :values (svtv-data$c->base-values svtv-data$c)
   :nextstate (svtv-data$c->base-nextstate svtv-data$c)
   :design (svtv-data$c->design svtv-data$c)
   :user-names (svtv-data$c->user-names svtv-data$c)
   :namemap (svtv-data$c->namemap svtv-data$c)))

(define svtv-data$a->base-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->base-fsm x)))


(define svtv-data$c->cycle-fsm (svtv-data$c)
  :returns (fsm svtv-fsm-p)
  (make-svtv-fsm
   :values (svtv-data$c->cycle-values svtv-data$c)
   :nextstate (svtv-data$c->cycle-nextstate svtv-data$c)
   :design (svtv-data$c->design svtv-data$c)
   :user-names (svtv-data$c->user-names svtv-data$c)
   :namemap (svtv-data$c->namemap svtv-data$c)))

(define svtv-data$a->cycle-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->cycle-fsm x)))

(define svtv-data$ap (x)
  (non-exec
   (and ;; (svtv-data$cp x)
        (modalist-addr-p (design->modalist (svtv-data$c->design x)))
        (implies (svtv-data$c->base-fsm-validp x)
                 (b* (((mv err (svtv-fsm fsm) moddb aliases)
                       (svtv-design-to-fsm (svtv-data$c->design x)
                                           :moddb nil :aliases nil)))
                   (and (not err)
                        (equal (svtv-data$c->base-values x) fsm.values)
                        (equal (svtv-data$c->base-nextstate x) fsm.nextstate)
                        (equal (svtv-data$c->moddb x) moddb)
                        (equal (svtv-data$c->aliases x) aliases)

                        (implies (svtv-data$c->namemap-validp x)
                                 (b* (((mv errs lhsmap)
                                       (svtv-namemap->lhsmap
                                        (svtv-data$c->user-names x)
                                        (moddb-modname-get-index
                                         (design->top (svtv-data$c->design x))
                                         (svtv-data$c->moddb x))
                                        (svtv-data$c->moddb x)
                                        (svtv-data$c->aliases x))))
                                   (and (not errs)
                                        (equal (svtv-data$c->namemap x)
                                               lhsmap))))
                        
                        (implies (svtv-data$c->cycle-fsm-validp x)
                                 (b* (((svtv-fsm cycle-fsm)
                                       (svtv-fsm-to-cycle (svtv-data$c->cycle-phases x)
                                                          (svtv-data$c->base-fsm x))))
                                   (and (equal (svtv-data$c->cycle-values x) cycle-fsm.values)
                                        (equal (svtv-data$c->cycle-nextstate x) cycle-fsm.nextstate))))))))))

(define svtv-data$a-compute-base-fsm ((x svtv-data$ap))
  :guard (and (not (svtv-data$a->namemap-validp x))
              (not (svtv-data$a->cycle-fsm-validp x)))
  :enabled t
  (b* (((mv a b) (non-exec (svtv-data$c-compute-base-fsm x))))
    (mv a b)))


(define update-svtv-data$a->cycle-phases ((phases svtv-cyclephaselist-p) x)
  :guard (not (svtv-data$a->cycle-fsm-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->cycle-phases phases x)))

(local (in-theory (disable hons-dups-p)))

(define svtv-data$c-compute-cycle (svtv-data$c)
  :guard (and (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
              (no-duplicatesp-equal (svex-alist-keys (svtv-fsm->nextstate (svtv-data$c->base-fsm svtv-data$c)))))
  (b* ((fsm (svtv-data$c->base-fsm svtv-data$c))
       (phases (svtv-data$c->cycle-phases svtv-data$c))
       ((svtv-fsm cycle-fsm) (svtv-fsm-to-cycle phases fsm))
       (svtv-data$c (update-svtv-data$c->cycle-values cycle-fsm.values svtv-data$c))
       (svtv-data$c (update-svtv-data$c->cycle-nextstate cycle-fsm.nextstate svtv-data$c)))
    (update-svtv-data$c->cycle-fsm-validp t svtv-data$c)))


(define svtv-data$a-compute-cycle ((x svtv-data$ap))
  :guard (and (not (svtv-data$a->cycle-fsm-validp x))
              (svtv-data$a->base-fsm-validp x))
  :enabled t
  (non-exec (svtv-data$c-compute-cycle x)))

(define update-svtv-data$a->user-names ((names svtv-namemap-p) x)
  :guard (not (svtv-data$a->namemap-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->user-names names x)))

(define svtv-data$c-compute-namemap (svtv-data$c)
  :returns (mv err new-svtv-data$c)
  :guard (b* ((design (svtv-data$c->design svtv-data$c)))
           (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                       (aliases (svtv-data$c->aliases svtv-data$c)))
                      (ok)
                      (and (moddb-ok moddb)
                           (b* ((index (moddb-modname-get-index
                             (design->top design) moddb)))
                             (and index
                                  (svtv-mod-alias-guard
                                   index
                                   moddb aliases))))
                      ok))
  (b* ((user-names (svtv-data$c->user-names svtv-data$c))
       (design (svtv-data$c->design svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (errs lhsmap)
               (svtv-namemap->lhsmap user-names
                                     (moddb-modname-get-index (design->top design) moddb)
                                     moddb aliases)
               (b* (((when errs)
                     (mv (msg-list errs) svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->namemap lhsmap svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->namemap-validp t svtv-data$c)))
                 (mv nil svtv-data$c)))))

(define svtv-data$a-compute-namemap ((x svtv-data$ap))
  :guard (svtv-data$a->base-fsm-validp x)
  :enabled t
  (b* (((mv a b) (non-exec (svtv-data$c-compute-namemap x))))
    (mv a b)))
                    


 ;; BOZO allow names

(define create-svtv-data$a ()
  :enabled t
  (non-exec (create-svtv-data$c)))




;; (defun svtv-data-corr (c a)
;;   (equal c a))

(local (in-theory (set-difference-theories
                   (current-theory :here)
                   (executable-counterpart-theory :here))));; (create-svtv-data$a)
                           ;; (svtv-data$ap)
                           ;; (svtv-data$c->design))))

(local (in-theory (enable svtv-data$ap
                          svtv-data$c-compute-base-fsm
                          svtv-data$c-compute-cycle
                          svtv-data$c-compute-namemap
                          svtv-data$c->base-fsm
                          (design-p)
                          (svtv-fsm-p)
                          (svarlist-addr-p)
                          (design->modalist)
                          (modalist-vars)
                          (svarlist-addr-p)
                          (svtv-data$c-Field-fix))))

(defsection svtv-data
  (local (set-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable svtv-data$c-compute-base-fsm svtv-data$c-compute-cycle)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-data$cp
                                      svtv-data$c->design
                                      svtv-data$c->design^
                                      svtv-data$c->base-fsm-validp
                                      svtv-data$c->base-fsm-validp^
                                      svtv-data$c->cycle-fsm-validp
                                      svtv-data$c->cycle-fsm-validp^
                                      svtv-data$c->namemap-validp
                                      svtv-data$c->namemap-validp^))))))
  (local (defun make-svtv-data-accessor-defs (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (cons
              (b* ((name (caar fields)))
                (acl2::template-subst
                 '(svtv-data-><fieldname> :logic svtv-data$a-><fieldname> :exec svtv-data$c-><fieldname>$inline)
                 :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                 :pkg-sym 'sv-package))
              (make-svtv-data-accessor-defs (cdr fields))))))

  (local (defthm values-of-svtv-fsm-to-cycle-of-svtv-fsm-normalize
           (implies (syntaxp (not (and (equal user-names ''nil)
                                       (equal namemap ''nil))))
                    (equal (svtv-fsm->values
                            (svtv-fsm-to-cycle phases
                                               (svtv-fsm values nextstate design user-names namemap)))
                           (svtv-fsm->values
                            (svtv-fsm-to-cycle phases
                                               (svtv-fsm values nextstate design nil nil)))))
           :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle svtv-cycle-compile)))))
                           

  (make-event
   `(acl2::defabsstobj-events svtv-data
      :concrete svtv-data$c
      :corr-fn equal
      :recognizer (svtv-datap :logic svtv-data$ap :exec svtv-data$cp)
      :creator (create-svtv-data :logic create-svtv-data$a :exec create-svtv-data$c)
      :exports (,@(make-svtv-data-accessor-defs *svtv-data-nonstobj-fields*)
                 
                  (svtv-data-invalidate-base-fsm :logic svtv-data$a-invalidate-base-fsm :exec svtv-data$c-invalidate-base-fsm)
                  (svtv-data-invalidate-cycle-fsm :logic svtv-data$a-invalidate-cycle-fsm :exec svtv-data$c-invalidate-cycle-fsm)
                  (svtv-data-invalidate-namemap :logic svtv-data$a-invalidate-namemap :exec svtv-data$c-invalidate-namemap)
                  (update-svtv-data->design :logic update-svtv-data$a->design :exec update-svtv-data$c->design$inline)
                  (svtv-data-compute-base-fsm :logic svtv-data$a-compute-base-fsm :exec svtv-data$c-compute-base-fsm :protect t)
                  (update-svtv-data->cycle-phases :logic update-svtv-data$a->cycle-phases :exec update-svtv-data$c->cycle-phases$inline)
                  (svtv-data-compute-cycle :logic svtv-data$a-compute-cycle :exec svtv-data$c-compute-cycle :protect t)
                  (update-svtv-data->user-names :logic update-svtv-data$a->user-names :exec update-svtv-data$c->user-names$inline)
                  (svtv-data-compute-namemap :logic svtv-data$a-compute-namemap :exec svtv-data$c-compute-namemap :protect t)
                  (svtv-data->base-fsm :logic svtv-data$a->base-fsm :exec svtv-data$c->base-fsm)
                  (svtv-data->cycle-fsm :logic svtv-data$a->cycle-fsm :exec svtv-data$c->cycle-fsm)))))

  


       
