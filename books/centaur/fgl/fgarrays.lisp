 ; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(include-book "fast-alists")
(local (include-book "primitive-lemmas"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable w)))

(def-formula-checks fgarray-formula-checks
  (create-fgarray$a
   fgarray-get$a
   fgarray-set$a
   fgarray-compress$a
   fgarray->alist$a
   fgarray-init$a))

(set-ignore-ok t)


(def-fgl-primitive create-fgarray$a ()
  (b* ((next (interp-st->next-fgarray interp-st))
       (interp-st (if (<= (interp-st->fgarrays-length interp-st) next)
                      (resize-interp-st->fgarrays (max 16 (* 2 next)) interp-st)
                    interp-st))
       (interp-st (update-interp-st->next-fgarray (+ 1 next) interp-st)))
    (stobj-let ((fgarray (interp-st->fgarraysi next interp-st)))
               (obj fgarray)
               (b* ((fgarray (fgarray-init 16 fgarray))
                    (alist (fgarray->alist fgarray)))
                 (mv (g-map (g-map-tag next) alist) fgarray))
               (mv t obj interp-st)))
  :formula-check fgarray-formula-checks)

(defstub bad-fgarray-access-warning () nil)
(defattach bad-fgarray-access-warning acl2::constant-t-function-arity-0)

(define warn-about-bad-fgarray-access (fn msg)
  (and (bad-fgarray-access-warning)
       (cw "Bad ~x0 fgarray access: ~s1~%" fn msg)))
    
  

(def-fgl-primitive fgarray-get$a (n x)
  (fgl-object-case n
    :g-concrete
    (let ((key (nfix n.val)))
      (fgl-object-case x
        :g-concrete
        (if (atom x.val)
            (mv t nil interp-st)
          (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "nonempty constant alist")
                  (mv t (g-concrete (hons-assoc-equal key x.val)) interp-st)))
        :g-map
        (b* ((index (g-map-tag->index x.tag))
             ((unless index)
              (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "no index")
                      (mv t (fgl-keyval-pair-to-object (hons-assoc-equal key x.alist)) interp-st)))
             ((unless (< index (interp-st->fgarrays-length interp-st)))
              (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "index out of bounds")
                      (mv t (fgl-keyval-pair-to-object (hons-assoc-equal key x.alist)) interp-st))))
          (stobj-let ((fgarray (interp-st->fgarraysi index interp-st)))
                     (res)
                     (b* ((fg-alist (fgarray->alist fgarray))
                          ;; BOZO it would be really nice to make this an EQ check!
                          ((unless (equal x.alist fg-alist))
                           (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "alists mismatched")
                                   (fgl-keyval-pair-to-object (hons-assoc-equal key x.alist)))))
                       (fgl-keyval-pair-to-object (fgarray-get key fgarray)))
                     (mv t res interp-st)))
        :otherwise
        (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "bad alist object")
                (mv nil nil interp-st))))
    :otherwise
    (prog2$ (warn-about-bad-fgarray-access 'fgarray-get "nonconstant key object")
            (mv nil nil interp-st)))
  :formula-check fgarray-formula-checks)


(local (in-theory (disable boolean-listp member integer-listp)))

(def-fgl-primitive fgarray-set$a (n v x)
  (fgl-object-case n
    :g-concrete
    (let ((key (nfix n.val)))
      (fgl-object-case x
        :g-concrete
        (if (eq x.val nil)
            (b* ((next (interp-st->next-fgarray interp-st))
                 (interp-st (if (<= (interp-st->fgarrays-length interp-st) next)
                                (resize-interp-st->fgarrays (max 16 (* 2 next)) interp-st)
                              interp-st))
                 (interp-st (update-interp-st->next-fgarray (+ 1 next) interp-st)))
              (stobj-let ((fgarray (interp-st->fgarraysi next interp-st)))
                         (obj fgarray)
                         (b* ((fgarray (fgarray-init 16 fgarray))
                              (fgarray (fgarray-set key v fgarray))
                              (alist (fgarray->alist fgarray)))
                           (mv (g-map (g-map-tag next) alist) fgarray))
                         (mv t obj interp-st)))
          (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "nonnil constant alist")
                  (mv t (g-cons (g-cons (g-concrete key) v) x) interp-st)))
        :g-map
        (b* ((index (g-map-tag->index x.tag))
             ((unless index)
              ;; maybe we should avoid warning about no index?
              (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "no index")
                      (mv t (g-map '(:g-map) (cons (cons key v) x.alist)) interp-st)))
             ((unless (< index (interp-st->fgarrays-length interp-st)))
              (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "index out of bounds")
                      (mv t (change-g-map x :alist (cons (cons key v) x.alist)) interp-st))))
          (stobj-let ((fgarray (interp-st->fgarraysi index interp-st)))
                     (res fgarray)
                     (b* ((fg-alist (fgarray->alist fgarray))
                          ;; BOZO it would be really nice to make this an EQ check!
                          ((unless (equal x.alist fg-alist))
                           (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "alists mismatched")
                                   (mv (g-map '(:g-map) (cons (cons key v) x.alist)) fgarray)))
                          (fgarray (fgarray-set key v fgarray))
                          (alist (fgarray->alist fgarray)))
                       (mv (change-g-map x :alist alist) fgarray))
                     (mv t res interp-st)))
        :otherwise
        (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "bad alist object")
                (mv nil nil interp-st))))
    :otherwise
    (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "nonconstant key object")
            (mv nil nil interp-st)))
  :formula-check fgarray-formula-checks)

(defthm fgl-object-alist-p-of-fgarray-compress$a-aux
  (implies (fgl-object-alist-p x)
           (fgl-object-alist-p (fgarray-compress$a-aux i max x)))
  :hints(("Goal" :in-theory (enable fgarray-compress$a-aux))))

(defthm member-fgl-object-bfrlist-of-lookup
  (implies (not (member v (fgl-object-alist-bfrlist x)))
           (not (member v (fgl-object-bfrlist (cdr (hons-assoc-equal k x))))))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm fgl-object-alist-bfrlist-of-fgarray-compress$a-aux
  (implies (not (member v (fgl-object-alist-bfrlist x)))
           (not (member v (fgl-object-alist-bfrlist (fgarray-compress$a-aux i max x)))))
  :hints(("Goal" :in-theory (enable fgarray-compress$a-aux))))

(defthm fgarray-compress$a-aux-when-atom
  (implies (not (consp x))
           (equal (fgarray-compress$a-aux i max x) nil))
  :hints(("Goal" :in-theory (enable fgarray-compress$a-aux))))

(defthm fgl-object-alist-eval-of-compress$a-aux-when-atom
  (equal (fgl-object-alist-eval (fgarray-compress$a-aux i max x) env)
         (fgarray-compress$a-aux i max (fgl-object-alist-eval x env)))
  :hints(("Goal" :in-theory (enable fgarray-compress$a-aux fgl-object-alist-eval
                                    fgl-keyval-pair-eval))))

(defthm fgarray-max-key-of-fgl-object-alist-eval
  (equal (fgarray-max-key (fgl-object-alist-eval x env))
         (fgarray-max-key x))
  :hints(("Goal" :in-theory (enable fgarray-max-key fgl-object-alist-eval
                                    fgl-keyval-pair-eval))))

(local (in-theory (disable fgarray-compress$a-aux-of-greater-than-max-key)))

(def-fgl-primitive fgarray-compress$a (x)
  (fgl-object-case x
    :g-concrete
    (if (atom x.val)
        (b* ((next (interp-st->next-fgarray interp-st))
             (interp-st (if (<= (interp-st->fgarrays-length interp-st) next)
                            (resize-interp-st->fgarrays (max 16 (* 2 next)) interp-st)
                          interp-st))
             (interp-st (update-interp-st->next-fgarray (+ 1 next) interp-st)))
          (stobj-let ((fgarray (interp-st->fgarraysi next interp-st)))
                     (obj fgarray)
                     (b* ((fgarray (fgarray-init 16 fgarray))
                          (alist (fgarray->alist fgarray)))
                       (mv (g-map (g-map-tag next) alist) fgarray))
                     (mv t obj interp-st)))
      (prog2$ (warn-about-bad-fgarray-access 'fgarray-compress "nonatom constant alist")
              (mv t (g-concrete (ec-call (fgarray-compress$a x.val))) interp-st)))
    :g-map
    (b* ((index (g-map-tag->index x.tag))
         ((unless index)
          ;; maybe we should avoid warning about no index?
          (prog2$ (warn-about-bad-fgarray-access 'fgarray-compress "no index")
                  (mv t (g-map '(:g-map) (ec-call (fgarray-compress$a x.alist))) interp-st)))
         ((unless (< index (interp-st->fgarrays-length interp-st)))
          (prog2$ (warn-about-bad-fgarray-access 'fgarray-compress "index out of bounds")
                  (mv t (change-g-map x :alist (ec-call (fgarray-compress$a x.alist))) interp-st))))
      (stobj-let ((fgarray (interp-st->fgarraysi index interp-st)))
                 (res fgarray)
                 (b* ((fg-alist (fgarray->alist fgarray))
                      ;; BOZO it would be really nice to make this an EQ check!
                      ((unless (equal x.alist fg-alist))
                       (prog2$ (warn-about-bad-fgarray-access 'fgarray-compress "alists mismatched")
                               (mv (g-map '(:g-map) (ec-call (fgarray-compress$a x.alist))) fgarray)))
                      (fgarray (fgarray-compress fgarray))
                      (alist (fgarray->alist fgarray)))
                   (mv (change-g-map x :alist alist) fgarray))
                 (mv t res interp-st)))
    :otherwise
    (prog2$ (warn-about-bad-fgarray-access 'fgarray-compress "bad alist object")
            (mv nil nil interp-st)))
  :formula-check fgarray-formula-checks)


(make-event
 `(define fgarray-init-new ((size natp) interp-st)
    :returns (mv successp ans new-interp-st)
    (b* ((next (interp-st->next-fgarray interp-st))
         (interp-st (if (<= (interp-st->fgarrays-length interp-st) next)
                        (resize-interp-st->fgarrays (max 16 (* 2 next)) interp-st)
                      interp-st))
         (interp-st (update-interp-st->next-fgarray (+ 1 next) interp-st)))
      (stobj-let ((fgarray (interp-st->fgarraysi next interp-st)))
                 (obj fgarray)
                 (b* ((fgarray (fgarray-init size fgarray))
                      (alist (fgarray->alist fgarray)))
                   (mv (g-map (g-map-tag next) alist) fgarray))
                 (mv t obj interp-st)))
    ///
    (defret fgl-object-p-ans-of-<fn>
      (fgl-object-p ans))
    
    (defret interp-st-bfrs-ok-of-<fn>
      (implies (and (interp-st-bfrs-ok interp-st))
               (interp-st-bfrs-ok new-interp-st)))

    (defret bfr-listp-of-<fn>
      (implies (and
                (interp-st-bfrs-ok interp-st))
               (lbfr-listp (fgl-object-bfrlist ans)
                           (interp-st->logicman new-interp-st))))

    (defret interp-st-get-of-<fn>
      (implies (and (not (equal (interp-st-field-fix key) :logicman))
                    (not (equal (interp-st-field-fix key) :stack))
                    (not (equal (interp-st-field-fix key) :pathcond))
                    (not (equal (interp-st-field-fix key) :constraint))
                    (not (equal (interp-st-field-fix key) :bvar-db))
                    (not (equal (interp-st-field-fix key) :fgarrays))
                    (not (equal (interp-st-field-fix key) :next-fgarray)))
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st))))

    (defret scratch-isomorphic-of-<fn>
      (interp-st-scratch-isomorphic new-interp-st (double-rewrite interp-st)))

    (defret logicman->mode-of-<fn>
      (equal (logicman->mode (interp-st->logicman new-interp-st))
             (logicman->mode (interp-st->logicman interp-st))))

    (defret bfr-nvars-of-<fn>
      (equal (bfr-nvars (interp-st->logicman new-interp-st))
             (bfr-nvars (interp-st->logicman interp-st))))

    (defret pathcond-enabledp-of-<fn>
      (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
           (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

    (defret pathcond-rewind-stack-len-of-<fn>
      (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
               (equal (pathcond-rewind-stack-len mode (interp-st->pathcond new-interp-st))
                      (pathcond-rewind-stack-len mode (interp-st->pathcond interp-st)))))

    (defret pathcond-rewind-ok-of-<fn>
      (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
               (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
                    (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

    (defret pathcond-eval-checkpoints-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval-checkpoints!
                       env
                       (interp-st->pathcond new-interp-st)
                       (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval-checkpoints!
                       env
                       (interp-st->pathcond interp-st)
                       (interp-st->logicman interp-st)))))

    (defret constraint-eval-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval
                       env
                       (interp-st->constraint new-interp-st)
                       (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval
                       env
                       (interp-st->constraint interp-st)
                       (interp-st->logicman interp-st)))))

    (defret next-bvar-of-<fn>
      (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
             (next-bvar$a (interp-st->bvar-db interp-st))))

    (defret base-bvar-of-<fn>
      (equal (base-bvar$a (interp-st->bvar-db new-interp-st))
             (base-bvar$a (interp-st->bvar-db interp-st))))

    (defret get-bvar->term-eval-of-<fn>
      (b* ((bvar-db (interp-st->bvar-db interp-st)))
        (implies (and (interp-st-bfrs-ok interp-st)
                      (<= (base-bvar$a bvar-db) (nfix n))
                      (< (nfix n) (next-bvar$a bvar-db)))
                 (iff (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                                       env
                                       (interp-st->logicman new-interp-st))
                      (fgl-object-eval (get-bvar->term$a n bvar-db)
                                       env
                                       (interp-st->logicman interp-st))))))

    (defret major-stack-concretize-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
                      (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))))

    (defret eval-of-<fn>
      (implies (and successp
                    (fgl-ev-meta-extract-global-facts :state st)
                    (equal (w st) (w state))
                    (interp-st-bfrs-ok interp-st))
               (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                      nil)))))

(local (in-theory (enable fgarray-init$a)))

(local (in-theory (disable w acl2::member-equal-append)))

(def-fgl-primitive fgarray-init$a (size x)
  (b* ((size
        (fgl-object-case size
          :g-concrete
          (b* (((unless (natp size.val))
                (prog2$ (warn-about-bad-fgarray-access 'fgarray-init "non-natp size")
                        0)))
            size.val)
          :otherwise
          (prog2$ (warn-about-bad-fgarray-access 'fgarray-init "non-concrete size")
                  0))))
    (fgl-object-case x
      :g-concrete
      (prog2$ (and (consp x.val)
                   (warn-about-bad-fgarray-access 'fgarray-init "non-atom constant alist"))
              (fgarray-init-new size interp-st))
      :g-map
      (b* ((index (g-map-tag->index x.tag))
           ((unless index)
            (prog2$ (warn-about-bad-fgarray-access 'fgarray-init "no index")
                    (fgarray-init-new size interp-st)))
           ((unless (< index (interp-st->fgarrays-length interp-st)))
            (prog2$ (warn-about-bad-fgarray-access 'fgarray-init "index out of bounds")
                    (fgarray-init-new size interp-st))))
        (stobj-let ((fgarray (interp-st->fgarraysi index interp-st)))
                   (res fgarray)
                   (b* ((fg-alist (fgarray->alist fgarray))
                        ;; BOZO it would be really nice to make this an EQ check!
                        ((unless (equal x.alist fg-alist))
                         (prog2$ (warn-about-bad-fgarray-access 'fgarray-init "alists mismatched")
                                 (mv (g-map '(:g-map) nil) fgarray)))
                        (fgarray (fgarray-init size fgarray))
                        (alist (fgarray->alist fgarray)))
                     (mv (change-g-map x :alist alist) fgarray))
                   (mv t res interp-st)))
      :otherwise
      (prog2$ (warn-about-bad-fgarray-access 'fgarray-set "bad alist object")
              (fgarray-init-new size interp-st))))
  :formula-check fgarray-formula-checks)


(local (install-fgl-metafns fgarrayprims))


(defxdoc fgl-array-support
  :parents (fgl)
  :short "Support for fast array lookups in FGL"
  :long "<p> FGL supports a form of fast array lookup based on the @(see
fgarray) abstract stobj.  The accessors and updaters for the fgarray abstract
stobj have corresponding primitive implementations in FGL that operate on real
fgarray objects stored in the FGL interpreter state.  As with FGL's support for
fast alists (see @(see fgl-fast-alist-support)), some care must be taken to use
these array objects in a single-threaded manner.</p>")
