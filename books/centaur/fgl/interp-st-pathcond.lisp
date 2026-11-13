; FGL - A Symbolic Simulation Framework for ACL2
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

; Interpreter-state path-condition operations.

(in-package "FGL")

(include-book "interp-st-bfrs-ok")

(local (std::add-default-post-define-hook :fix))
(std::make-returnspec-config :hints-sub-returnnames t)

(define interp-st-pathcond-assume ((test interp-st-bfr-p)
                                   interp-st)

  :returns (mv contra
               (new-interp-st))
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-ok)))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st))
              (constraint-pathcond (interp-st->constraint interp-st)))
             (contra pathcond constraint-pathcond)
             ;; this is a bit weak... would be better to check against
             ;; both constraint and pathcond at once somehow
             (b* ((constraint-pathcond (pathcond-fix constraint-pathcond))
                  ((unless test)
                   (mv t pathcond constraint-pathcond))
                  ;; ((mv constraint-implies constraint-pathcond)
                  ;;  (logicman-pathcond-implies test constraint-pathcond))
                  ;; ((when (eql constraint-implies 0))
                  ;;  (mv t pathcond constraint-pathcond))
                  ((mv contra constraint-pathcond)
                   (logicman-pathcond-assume test constraint-pathcond))
                  ((when contra)
                   (mv t pathcond constraint-pathcond))
                  (constraint-pathcond (pathcond-rewind (logicman->mode logicman) constraint-pathcond))
                  ((mv contra pathcond) (logicman-pathcond-assume test pathcond)))
               (mv contra pathcond constraint-pathcond))
             (mv contra interp-st))
  ///
  (defret interp-st-get-of-interp-st-pathcond-assume
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
                  (not (equal (interp-st-field-fix key) :constraint)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st->constraint-of-interp-st-pathcond-assume
    (equal (interp-st->constraint new-interp-st)
           (pathcond-fix (interp-st->constraint interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret pathcond-rewind-of-<fn>
    (implies (and (not contra)
                  (equal mode (logicman->mode (interp-st->logicman interp-st))))
             (equal (pathcond-rewind mode (interp-st->pathcond new-interp-st))
                    (pathcond-fix (interp-st->pathcond interp-st)))))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
          (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-pathcond-when-contra
    (implies contra
             (pathcond-equiv (interp-st->pathcond new-interp-st)
                             (interp-st->pathcond interp-st))))

  (defret logicman-pathcond-eval-of-<fn>
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (bfr-eval test env (interp-st->logicman interp-st))
                  (equal logicman (interp-st->logicman new-interp-st)))
             (logicman-pathcond-eval env (interp-st->pathcond new-interp-st) logicman)))

  (defret interp-st-pathcond-assume-not-contradictionp
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (bfr-eval test env (interp-st->logicman interp-st)))
             (not contra))))

(define interp-st-pathcond-implies ((test interp-st-bfr-p)
                                    interp-st)

  :returns (mv (ans acl2::maybe-bitp)
               (new-interp-st))
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-ok)))
  (b* (((when (booleanp test)) (mv (bool->bit test) interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (ans pathcond constraint-pathcond)
               ;; this is a bit weak... would be better to check against
               ;; both constraint and pathcond at once somehow
               (b* ((constraint-pathcond (pathcond-fix constraint-pathcond))
                    ;; ((mv constraint-implies constraint-pathcond)
                    ;;  (logicman-pathcond-implies test constraint-pathcond))
                    ;; ((when (eql constraint-implies 0))
                    ;;  (mv t pathcond constraint-pathcond))
                    ((mv ans1 constraint-pathcond)
                     (logicman-pathcond-implies test constraint-pathcond))
                    ((when ans1)
                     (mv ans1 pathcond constraint-pathcond))
                    ((mv ans2 pathcond) (logicman-pathcond-implies test pathcond)))
                 (mv ans2 pathcond constraint-pathcond))
               (mv ans interp-st)))
  ///
  (defretd eval-when-interp-st-pathcond-implies
    (implies (and ans
                  (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st)))
             (equal (bfr-eval test env (interp-st->logicman interp-st))
                    (bit->bool ans))))

  (defret interp-st-get-of-interp-st-pathcond-implies
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
                  (not (equal (interp-st-field-fix key) :constraint)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st->pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
                    (interp-st->pathcond interp-st)))

  (defret interp-st->constraint-of-<fn>
    (pathcond-equiv (interp-st->constraint new-interp-st)
                    (interp-st->constraint interp-st)))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
          (nth *pathcond-enabledp* (interp-st->pathcond interp-st)))))

(define interp-st-pathcond-fix-bfr ((test interp-st-bfr-p)
                                    interp-st)

  :returns (mv (ans)
               (new-interp-st))
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-ok)))
  (b* (((when (booleanp test)) (mv test interp-st))
       ((mv bit? interp-st) (interp-st-pathcond-implies test interp-st)))
    (mv (if bit? (bit->bool bit?) test) interp-st))
  ///
  (local (defthm bfr-p-of-equal
           (bfr-p (equal x y))
           :hints (("goal" :cases ((equal x y))))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
                  (not (equal (interp-st-field-fix key) :constraint)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st->pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
                    (interp-st->pathcond interp-st)))

  (defret interp-st->constraint-of-<fn>
    (pathcond-equiv (interp-st->constraint new-interp-st)
                    (interp-st->constraint interp-st)))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret bfr-p-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (logicman-extension-p logicman (interp-st->logicman interp-st)))
             (lbfr-p ans logicman)))

  (defret bfr-eval-of-<fn>
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st)))
             (equal (bfr-eval ans env (interp-st->logicman interp-st))
                    (bfr-eval test env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable eval-when-interp-st-pathcond-implies))))

  (defret bfr-eval-of-<fn>-free
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (interp-st-bfr-p test)
                  (logicman-extension-p logicman (interp-st->logicman interp-st)))
             (equal (bfr-eval ans env logicman)
                    (bfr-eval test env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (disable <fn>
                                       bfr-eval-of-<fn>)
            :use bfr-eval-of-<fn>)))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
          (nth *pathcond-enabledp* (interp-st->pathcond interp-st)))))

(define interp-st-pathcond-fix-bfr-list ((x interp-st-bfr-listp)
                                         interp-st)

  :returns (mv (ans true-listp)
               (new-interp-st))
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-ok)))
  (if (atom x)
      (mv nil interp-st)
    (b* (((mv first interp-st) (interp-st-pathcond-fix-bfr (car x) interp-st))
         ((mv rest interp-st) (interp-st-pathcond-fix-bfr-list (cdr x) interp-st)))
      (mv (cons first rest) interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
                  (not (equal (interp-st-field-fix key) :constraint)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st->pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
                    (interp-st->pathcond interp-st)))

  (defret interp-st->constraint-of-<fn>
    (pathcond-equiv (interp-st->constraint new-interp-st)
                    (interp-st->constraint interp-st)))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-listp x)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret bfr-p-of-<fn>
    (implies (and (interp-st-bfr-listp x)
                  (logicman-extension-p logicman (interp-st->logicman interp-st)))
             (lbfr-listp ans logicman)))

  (defret bfr-list-eval-of-<fn>
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st)))
             (equal (bfr-list-eval ans env (interp-st->logicman interp-st))
                    (bfr-list-eval x env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable eval-when-interp-st-pathcond-implies
                                      bfr-list-eval))))

  (defret bfr-list-eval-of-<fn>-free
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (interp-st-bfr-listp x)
                  (logicman-extension-p logicman (interp-st->logicman interp-st)))
             (equal (bfr-list-eval ans env logicman)
                    (bfr-list-eval x env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (disable <fn>
                                       bfr-list-eval-of-<fn>)
            :use bfr-list-eval-of-<fn>)))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
          (nth *pathcond-enabledp* (interp-st->pathcond interp-st)))))

(define interp-st-pathcond-rewind (interp-st)
  :guard (stobj-let ((pathcond (interp-st->pathcond interp-st))
                     (logicman (interp-st->logicman interp-st)))
                    (ok)
                    (pathcond-rewind-ok (lbfr-mode) pathcond)
                    ok)
  :returns new-interp-st
  :enabled t
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st)))
             (pathcond)
             (pathcond-rewind (logicman->mode logicman) pathcond)
             interp-st))
