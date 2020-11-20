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

(make-event
 `(stobjs::defnicestobj svtv-data$c
    (design :type (satisfies design-p)
            :pred design-p :fix design-fix :initially ,(make-design :top ""))
    (moddb :type moddb)
    (aliases :type aliases)
;;     (moddb-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)
    (base-fsm :type (satisfies svtv-fsm-p) :pred svtv-fsm-p :fix svtv-fsm-fix :initially ,(make-svtv-fsm :design (make-design :top "")))
    (base-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)
    (cycle-phases :type (satisfies svtv-cyclephaselist-p) :pred svtv-cyclephaselist-p :fix svtv-cyclephaselist-fix :initially nil)
    (cycle-fsm :type (satisfies svtv-fsm-p) :pred svtv-fsm-p :fix svtv-fsm-fix :initially ,(make-svtv-fsm :design (make-design :top "")))
    (cycle-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix :initially nil)))


(define svtv-data$a->design (x)
  :enabled t
  (non-exec (svtv-data$c->design x)))

;; (define svtv-data$a->moddb-validp (x)
;;   (non-exec (svtv-data$c->moddb-validp x)))

(define svtv-data$a->base-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->base-fsm x)))

(define svtv-data$a->base-fsm-validp (x)
  :enabled t
  (non-exec (svtv-data$c->base-fsm-validp x)))

(define svtv-data$a->cycle-phases (x)
  :enabled t
  (non-exec (svtv-data$c->cycle-phases x)))

(define svtv-data$a->cycle-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->cycle-fsm x)))

(define svtv-data$a->cycle-fsm-validp (x)
  :enabled t
  (non-exec (svtv-data$c->cycle-fsm-validp x)))


;; (define svtv-data$c-invalidate-moddb (svtv-data$c)
;;   (update-svtv-data$c->moddb-validp nil svtv-data$c))

;; (define svtv-data$a-invalidate-moddb (x)
;;   (non-exec (update-svtv-data$a->moddb-validp nil x)))


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


(define update-svtv-data$a->design ((design design-p) x)
  :guard (and (not (svtv-data$a->base-fsm-validp x))
              (modalist-addr-p (design->modalist design)))
  :enabled t
  (non-exec (update-svtv-data$c->design design x)))

(define svtv-data$c-compute-base-fsm (svtv-data$c)
  :guard (and (not (svtv-data$c->base-fsm-validp svtv-data$c))
              (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
              (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c))))
  :returns (mv errmsg new-svtv-data$c)
  (b* ((design (svtv-data$c->design svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (err fsm moddb aliases)
               (svtv-design-to-fsm design)
               (b* (((when err) (mv err svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-fsm fsm svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-fsm-validp t svtv-data$c)))
                 (mv nil svtv-data$c)))))


(define svtv-data$ap (x)
  (non-exec
   (and ;; (svtv-data$cp x)
        (modalist-addr-p (design->modalist (svtv-data$c->design x)))
        (implies (svtv-data$c->base-fsm-validp x)
                 (b* (((mv err fsm moddb aliases)
                       (svtv-design-to-fsm (svtv-data$c->design x)
                                           :moddb nil :aliases nil)))
                   (and (not err)
                        (equal (svtv-data$c->base-fsm x) fsm) ;; BOZO allow names
                        (equal (svtv-data$c->moddb x) moddb)
                        (equal (svtv-data$c->aliases x) aliases))))
        (implies (svtv-data$c->cycle-fsm-validp x)
                 (b* ((cycle-fsm
                       (svtv-fsm-to-cycle (svtv-data$c->cycle-phases x)
                                          (svtv-data$c->base-fsm x))))
                   (equal (svtv-data$c->cycle-fsm x) cycle-fsm))))))

(define svtv-data$a-compute-base-fsm ((x svtv-data$ap))
  :guard (and (not (svtv-data$a->base-fsm-validp x))
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
       (cycle-fsm (svtv-fsm-to-cycle phases fsm))
       (svtv-data$c (update-svtv-data$c->cycle-fsm cycle-fsm svtv-data$c)))
    (update-svtv-data$c->cycle-fsm-validp t svtv-data$c)))


(define svtv-data$a-compute-cycle ((x svtv-data$ap))
  :guard (and (not (svtv-data$a->cycle-fsm-validp x))
              (svtv-data$a->base-fsm-validp x))
  :enabled t
  (non-exec (svtv-data$c-compute-cycle x)))

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
                                      svtv-data$c->cycle-fsm-validp^))))))

  (acl2::defabsstobj-events svtv-data
    :concrete svtv-data$c
    :corr-fn equal
    :recognizer (svtv-datap :logic svtv-data$ap :exec svtv-data$cp)
    :creator (create-svtv-data :logic create-svtv-data$a :exec create-svtv-data$c)
    :exports ((svtv-data->design :logic svtv-data$a->design :exec svtv-data$c->design$inline)
              (svtv-data->base-fsm :logic svtv-data$a->base-fsm :exec svtv-data$c->base-fsm$inline)
              (svtv-data->base-fsm-validp :logic svtv-data$a->base-fsm-validp :exec svtv-data$c->base-fsm-validp$inline)
              (svtv-data->cycle-phases :logic svtv-data$a->cycle-phases :exec svtv-data$c->cycle-phases$inline)
              (svtv-data->cycle-fsm :logic svtv-data$a->cycle-fsm :exec svtv-data$c->cycle-fsm$inline)
              (svtv-data->cycle-fsm-validp :logic svtv-data$a->cycle-fsm-validp :exec svtv-data$c->cycle-fsm-validp$inline)
              (svtv-data-invalidate-base-fsm :logic svtv-data$a-invalidate-base-fsm :exec svtv-data$c-invalidate-base-fsm)
              (svtv-data-invalidate-cycle-fsm :logic svtv-data$a-invalidate-cycle-fsm :exec svtv-data$c-invalidate-cycle-fsm)
              (update-svtv-data->design :logic update-svtv-data$a->design :exec update-svtv-data$c->design$inline)
              (svtv-data-compute-base-fsm :logic svtv-data$a-compute-base-fsm :exec svtv-data$c-compute-base-fsm :protect t)
              (update-svtv-data->cycle-phases :logic update-svtv-data$a->cycle-phases :exec update-svtv-data$c->cycle-phases$inline)
              (svtv-data-Compute-cycle :logic svtv-data$a-Compute-cycle :exec svtv-data$c-Compute-cycle :protect t)
              )))

  


       
