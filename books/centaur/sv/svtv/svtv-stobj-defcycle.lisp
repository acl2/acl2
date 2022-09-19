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
(include-book "svtv-stobj-cycle")
(include-book "svtv-stobj-rewrite")
(include-book "svtv-stobj-phase")
(include-book "svtv-stobj-util")
(include-book "centaur/sv/svex/derived-clocks" :dir :System)
(include-book "process")
(include-book "centaur/misc/hons-remove-dups" :dir :System)
(local (include-book "std/lists/sets" :dir :System))
(local (include-book "std/osets/under-set-equiv" :dir :System))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (in-theory (disable acl2::hons-union)))

(local (std::deflist svarlist-p (x)
         (svar-p x)
         :true-listp t
         :elementp-of-nil nil))



(local (defthm true-listp-of-hons-union2
         (implies (true-listp acc)
                  (true-listp (acl2::hons-union2 x y acc)))
         :hints(("Goal" :in-theory (enable acl2::hons-union2)))))

(local (defthm true-listp-of-hons-union1
         (implies (true-listp acc)
                  (true-listp (acl2::hons-union1 x y acc)))
         :hints(("Goal" :in-theory (enable acl2::hons-union1)))))

(local (defthm true-listp-of-hons-union
         (implies (and (true-listp x) (true-listp y))
                  (true-listp (acl2::hons-union x y)))
         :hints(("Goal" :in-theory (enable acl2::hons-union)))))
         

(local (defthm svarlist-p-of-hons-union
         (implies (and (svarlist-p x)
                       (svarlist-p y))
                  (svarlist-p (acl2::hons-union x y)))
         :hints (("Goal" :use ((:instance svarlist-p-of-mergesort
                                (x (acl2::hons-union x y)))
                               (:instance svarlist-p-of-mergesort
                                (x (append x y))))
                  :in-theory (disable svarlist-p-of-mergesort)))))

(local (defthm svar-key-alist-p-of-pairlis
         (implies (svarlist-p keys)
                  (svar-key-alist-p (pairlis$ keys vals)))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(define svtv-defcycle-overrides-omit-derived-clocks ((assigns svex-alist-p)
                                                     (config phase-fsm-config-p)
                                                     (clocks svarlist-p))
  :Returns (new-config phase-fsm-config-p)
  (b* (((unless clocks)
        (phase-fsm-config-fix config))
       ((acl2::with-fast assigns))
       (initial-clk-alist (make-fast-alist (pairlis$ (svarlist-fix clocks)
                                                     (make-list (len clocks) :initial-element t))))
       ((mv derived-clocks clock-alist seen)
        (svex-assigns-find-clock-signals-varlist
         (svex-alist-keys assigns) initial-clk-alist nil assigns))
       (- (fast-alist-free clock-alist)
          (fast-alist-free seen))
       ((unless derived-clocks)
        (phase-fsm-config-fix config))
       ((phase-fsm-config config)))
    (svtv-assigns-override-config-case config.override-config
      :omit (change-phase-fsm-config
             config
             :override-config
             (change-svtv-assigns-override-config-omit
              config.override-config
              :vars (acl2::hons-union derived-clocks config.override-config.vars)))
      :include (change-phase-fsm-config
                config
                :override-config
                (change-svtv-assigns-override-config-omit
                 config.override-config
                 :vars (acl2::hons-set-diff config.override-config.vars derived-clocks))))))
      

(define svtv-data-defcycle-core ((design design-p)
                                 (phases svtv-cyclephaselist-p)
                                 svtv-data
                                 &key
                                 ((phase-config phase-fsm-config-p)
                                  '(make-phase-fsm-config
                                    :override-config (make-svtv-assigns-override-config-omit)))
                                 ((phase-scc-limit maybe-natp) 'nil)
                                 ((clocks-avoid-overrides svarlist-p) 'nil)
                                 ((monotonify booleanp) 't)
                                 (rewrite-assigns '2)
                                 (rewrite-phases '1)
                                 (rewrite-cycle '1)
                                 ((skip-cycle booleanp) 'nil)
                                 ((cycle-simp svex-simpconfig-p) 't))
  :guard (modalist-addr-p (design->modalist design))
  :returns (mv err new-svtv-data)
  (b* ((svtv-data (svtv-data-set-design design svtv-data))
       ((mv err svtv-data) (svtv-data-maybe-compute-flatten svtv-data))
       ((when err)
        (mv err svtv-data))
       ((mv updatedp svtv-data) (svtv-data-maybe-compute-flatnorm svtv-data (make-flatnorm-setup :monotonify monotonify)))
       (svtv-data (svtv-data-maybe-rewrite-flatnorm (and updatedp rewrite-assigns) svtv-data :verbosep t))
       (svtv-data (svtv-data-maybe-concatnorm-flatnorm (and updatedp rewrite-assigns) svtv-data :verbosep t))
       (phase-config (svtv-defcycle-overrides-omit-derived-clocks
                      (flatnorm-res->assigns (svtv-data->flatnorm svtv-data))
                      phase-config clocks-avoid-overrides))
       ((mv updatedp svtv-data) (svtv-data-maybe-compute-phase-fsm
                                 svtv-data phase-config
                                 (make-phase-fsm-params
                                  :rewrite t
                                  :scc-selfcompose-limit phase-scc-limit)))
       (svtv-data (svtv-data-maybe-rewrite-phase-fsm (and updatedp rewrite-phases) svtv-data :verbosep t))
       ((mv updatedp svtv-data) (svtv-data-maybe-compute-cycle-fsm phases svtv-data cycle-simp :skip skip-cycle))
       ((when skip-cycle)
        (mv nil svtv-data))
       (svtv-data (svtv-data-maybe-rewrite-cycle-fsm (and updatedp rewrite-cycle) svtv-data :verbosep t)))
    (mv nil svtv-data))
  ///
  (defret <fn>-correct
    (implies (not err)
             (and (equal (svtv-data$c->design new-svtv-data) (design-fix design))
                  (equal (svtv-data$c->flatten-validp new-svtv-data) t)
                  (equal (svtv-data$c->flatnorm-validp new-svtv-data) t)
                  (equal (svtv-data$c->phase-fsm-validp new-svtv-data) t)
                  (equal (svtv-data$c->cycle-phases new-svtv-data) (svtv-cyclephaselist-fix phases))
                  (implies (not skip-cycle)
                           (equal (svtv-data$c->cycle-fsm-validp new-svtv-data) t))))))

(defun defcycle-fn (name design phases names names-p monotonify phase-config phase-scc-limit clocks-avoid-overrides rewrite-assigns rewrite-phases rewrite-cycle cycle-simp skip-cycle stobj)
  `(make-event
    (b* (((mv err ,stobj)
          (svtv-data-defcycle-core ,design ,phases
                                   ,stobj
                                   :phase-config ,phase-config
                                   :phase-scc-limit ,phase-scc-limit
                                   :clocks-avoid-overrides ,clocks-avoid-overrides
                                   :rewrite-assigns ,rewrite-assigns
                                   :rewrite-phases ,rewrite-phases
                                   :rewrite-cycle ,rewrite-cycle
                                   :cycle-simp ,cycle-simp
                                   :skip-cycle ,skip-cycle
                                   :monotonify ,monotonify))
         ((when err)
          (mv err nil state ,stobj))
         ((mv err ,stobj)
          (if ,names-p
              (svtv-data-maybe-compute-namemap ,names ,stobj)
            (mv nil ,stobj)))
         ((when err)
          (mv err nil state ,stobj))
         (fsm (make-svtv-fsm :base-fsm (svtv-data->cycle-fsm svtv-data)
                             :namemap (svtv-data->namemap svtv-data))))
      (mv nil
          `(with-output :off (event)
             (progn (defconst ,',(intern-in-package-of-symbol
                                (concatenate 'string "*" (symbol-name name) "*")
                                name)
                      ',fsm)
                    (defund ,',name ()
                      (declare (xargs :guard t))
                      ',fsm)
                    (in-theory (disable (,',name)))))
          state ,stobj))))


(defmacro defcycle (name &key
                         design
                         phases
                         (names 'nil names-p)
                         (monotonify 't)
                         (phase-config
                          '(make-phase-fsm-config
                            :override-config (make-svtv-assigns-override-config-omit)))
                         (phase-scc-limit 'nil)
                         (clocks-avoid-overrides 'nil)
                         (rewrite-assigns '2)
                         (rewrite-phases '1)
                         (rewrite-cycle '1)
                         (cycle-simp 't)
                         (skip-cycle 'nil)
                         (stobj 'svtv-data))
  (defcycle-fn name design phases names names-p monotonify phase-config
    phase-scc-limit clocks-avoid-overrides
    rewrite-assigns rewrite-phases rewrite-cycle cycle-simp skip-cycle stobj))

;; Doc in new-svtv-doc.lisp
