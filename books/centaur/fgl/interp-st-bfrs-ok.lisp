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

(include-book "interp-st")

(local (std::add-default-post-define-hook :fix))


(def-updater-independence-thm bfr-listp$-of-interp-st->logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new)
                                      (interp-st->logicman old))
                (lbfr-listp x (interp-st->logicman old)))
           (lbfr-listp x (interp-st->logicman new))))

(def-updater-independence-thm logicman-pathcond-p-of-interp-st->logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new)
                                      (interp-st->logicman old))
                (logicman-pathcond-p x (interp-st->logicman old)))
           (logicman-pathcond-p x (interp-st->logicman new))))

;; (def-updater-independence-thm logicman-extension-p-transitive-interp-st
;;   (implies (and (logicman-extension-p (interp-st->logicman new)
;;                                       (interp-st->logicman old))
;;                 (equal (interp-st->logicman )
;;            (logicman-extension-p (interp-st->logicman new) prev)))



(define interp-st-bfrs-ok (interp-st)
  (b* ((constraint-db (interp-st->constraint-db interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (bvar-db (interp-st->bvar-db interp-st))
                (stack (interp-st->stack interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (ok)
               (b* ((bfrstate (logicman->bfrstate)))
                 (and (bfr-listp (major-stack-bfrlist (stack-extract stack)))
                      (bfr-listp (constraint-db-bfrlist constraint-db))
                      (ec-call (logicman-pathcond-p-fn pathcond logicman))
                      (ec-call (logicman-pathcond-p-fn constraint-pathcond logicman))
                      (not (consp (bvar-db-bfrlist bvar-db)))
                      (equal (next-bvar bvar-db) (bfr-nvars logicman))))
               ok))
  ///
  (defthm interp-st-bfrs-ok-implies
    (implies (interp-st-bfrs-ok interp-st)
             (let* ((logicman (interp-st->logicman interp-st))
                    (bfrstate (logicman->bfrstate)))
               (and (bfr-listp (major-stack-bfrlist (interp-st->stack interp-st)))
                    (bfr-listp (constraint-db-bfrlist (interp-st->constraint-db interp-st)))
                    (logicman-pathcond-p (interp-st->pathcond interp-st))
                    (logicman-pathcond-p (interp-st->constraint interp-st))
                    (not (bvar-db-bfrlist (interp-st->bvar-db interp-st)))
                    (interp-st-nvars-ok interp-st)
                    (equal (next-bvar$a (interp-st->bvar-db interp-st))
                           (bfr-nvars (interp-st->logicman interp-st))))))
    :hints(("Goal" :in-theory (enable interp-st-nvars-ok))))

  (acl2::def-updater-independence-thm interp-st-bfrs-ok-updater-independence
    (implies (and (equal (interp-st-get :logicman new)
                         (interp-st-get :logicman old))
                  (equal (interp-st-get :stack new)
                         (interp-st-get :stack old))
                  (equal (interp-st-get :constraint-db new)
                         (interp-st-get :constraint-db old))
                  (equal (interp-st-get :pathcond new)
                         (interp-st-get :pathcond old))
                  (equal (interp-st-get :constraint new)
                         (interp-st-get :constraint old))
                  (equal (interp-st-get :bvar-db new)
                         (interp-st-get :bvar-db old)))
             (equal (interp-st-bfrs-ok new)
                    (interp-st-bfrs-ok old))))


  (defthm interp-st-bfrs-ok-of-logicman-extension
    (implies (and (interp-st-bfrs-ok interp-st)
                  (logicman-extension-p new-logicman (interp-st->logicman interp-st))
                  (equal (bfr-nvars new-logicman) (bfr-nvars (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->logicman new-logicman interp-st))))

  (defthm interp-st-bfrs-ok-of-update-stack
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (major-stack-bfrlist new-stack) (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->stack new-stack interp-st))))

  (defthm interp-st-bfrs-ok-of-update-constraint-db
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (constraint-db-bfrlist new-constraint-db) (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->constraint-db new-constraint-db interp-st))))

  (defthm interp-st-bfrs-ok-of-update-pathcond
    (implies (And (interp-st-bfrs-ok interp-st)
                  (logicman-pathcond-p-fn new-pathcond (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok (update-interp-st->pathcond new-pathcond interp-st))))

  (defthm interp-st-bfrs-ok-of-update-constraint
    (implies (And (interp-st-bfrs-ok interp-st)
                  (logicman-pathcond-p-fn new-constraint (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok (update-interp-st->constraint new-constraint interp-st))))

  (defthm interp-st-bfrs-ok-of-update-bvar-db
    (implies (And (interp-st-bfrs-ok interp-st)
                  (not (bvar-db-bfrlist new-bvar-db))
                  (equal (next-bvar new-bvar-db) (bfr-nvars (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->bvar-db new-bvar-db interp-st))))

  (defthm interp-st-bfrs-ok-of-interp-st-add-term-bvar
    (implies (and (interp-st-bfrs-ok interp-st)
                  (not (consp (gl-object-bfrlist x))))
             (interp-st-bfrs-ok (mv-nth 1 (interp-st-add-term-bvar x interp-st state))))
    ;; :hints (("goal" :use ((:instance logicman-extension-p-of-interp-st-add-term-bvar))
    ;;          :in-theory (disable logicman-extension-p-of-interp-st-add-term-bvar)))
    )

  (defthm interp-st-bfrs-ok-of-interp-st-add-term-bvar-unique
    (implies (and (interp-st-bfrs-ok interp-st)
                  (not (consp (gl-object-bfrlist x))))
             (interp-st-bfrs-ok (mv-nth 1 (interp-st-add-term-bvar-unique x interp-st state))))
    ;; :hints (("goal" :use ((:instance logicman-extension-p-of-interp-st-add-term-bvar-unique))
    ;;          :in-theory (disable logicman-extension-p-of-interp-st-add-term-bvar-unique)))
    ))

