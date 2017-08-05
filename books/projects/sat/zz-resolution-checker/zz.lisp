; ACL2 interface to the ZZ system
; Copyright (C) 2011-2017 Centaur Technology
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

(in-package "ACL2")

;; This is an ACL2 interface to the ZZ system.  At the moment it just
;; includes a simple interface for calling SAT on an AIG.

(include-book "centaur/aig/misc" :dir :system)
(include-book "centaur/aig/induction" :dir :system)
(include-book "centaur/aig/aig-vars-fast" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

;; The :zz ttag isn't needed, because we are not including the SAT
;; solver backend.
; (defttag zz)

(defun set-zz-differentiate-verbose (verbosep)
  ;; Has an under-the-hood definition
  (declare (xargs :guard t)
           (ignore verbosep))
  nil)


(defun set-zz-mc-verbose (verbosep)
  ;; Has an under-the-hood definition
  (declare (xargs :guard t)
           (ignore verbosep))
  nil)

(defun zzsat-useless-clauseproc (clause)
  (list clause))

(defchoose satisfying-assign (env) (aig)
  (aig-eval aig env))

;; The AIG evaluates to T for some env in the list.
(defun aig-eval-exists (aig envs)
  (if (atom envs)
      nil
    (or (aig-eval aig (car envs))
        (aig-eval-exists aig (cdr envs)))))

;; The following form was originally part of the definition of a trusted
;; clause-processor, which we omit here since we are not including the SAT
;; solver backend.
(encapsulate
  (((zz-sat-fn * * * *) => *)
   ((zz-abc-sat-fn * * * * *) => *)
   ((zz-batch-sat-fn * * * *) => *)
   ((zz-abc-batch-sat-fn * * * * *) => *)
   ((zz-differentiate-fn *) => (mv * * *))
   ((zz-modelcheck-fn * * * * * * * *) => *)
   ((zz-abc-modelcheck-fn * * * * * * * * *) => *)
   ((zz-abc-fn * * *) => (mv * * *))
   ((zz-reset-stats-fn) => *)
   ((zz-show-stats-fn) => *))
    
  (local (defun zz-sat-fn (aig mk-model mk-proof timeout)
           (declare (ignore aig mk-model mk-proof timeout))
           '(failed)))

  (local (defun zz-abc-sat-fn (aig mk-model mk-proof timeout abc-cmds)
           (declare (ignore aig mk-model mk-proof timeout abc-cmds))
           '(failed)))

  (local (defun zz-differentiate-fn (aigs)
           (mv nil (list aigs) nil)))

  (local (defun zz-batch-sat-fn (aigs mk-model mk-proof timeout)
           (if (atom aigs)
               nil
             (cons (zz-sat-fn (car aigs) mk-model mk-proof timeout)
                   (zz-batch-sat-fn (cdr aigs) mk-model mk-proof timeout)))))

  (local (defun zz-abc-batch-sat-fn (aigs mk-model mk-proof timeout abc-cmds)
           (if (atom aigs)
               nil
             (cons (zz-abc-sat-fn (car aigs) mk-model mk-proof timeout abc-cmds)
                   (zz-abc-batch-sat-fn (cdr aigs) mk-model mk-proof timeout abc-cmds)))))

  (local (defun zz-modelcheck-fn (stepfns prop initsts timeout max-depth mk-invar check-invar engine)
           (declare (ignorable stepfns prop initsts timeout max-depth mk-invar check-invar engine))
           '(aborted)))

  (local (defun zz-abc-modelcheck-fn (stepfns prop initsts timeout max-depth
                                              mk-invar check-invar abc-cmds engine)
           (declare (ignorable stepfns prop initsts timeout max-depth
                               mk-invar check-invar abc-cmds engine))
           '(aborted)))

  (local (defun zz-abc-fn (stepfns outfns cmds)
           (declare (ignorable stepfns outfns cmds))
           (mv 'undef stepfns outfns)))

  (local (defun zz-reset-stats-fn () nil))

  (local (defun zz-show-stats-fn () nil))

  (defthm zz-sat-fn-consp
    (consp (zz-sat-fn aig mk-model mk-proof timeout))
    :rule-classes :type-prescription)

  (defthm zz-sat-fn-sat
    (implies (equal (car (zz-sat-fn aig mk-model mk-proof timeout)) 'sat)
             (aig-eval aig (satisfying-assign aig))))

  (defthm zz-sat-fn-sat-model
    (implies (and (equal (car (zz-sat-fn aig mk-model mk-proof timeout)) 'sat)
                  mk-model)
             (aig-eval aig (cdr (zz-sat-fn aig mk-model mk-proof timeout)))))

  (defthm zz-sat-fn-unsat
    (implies (equal (car (zz-sat-fn aig mk-model mk-proof timeout)) 'unsat)
             (not (aig-eval aig env))))

  (defthm zz-batch-sat-len
    (equal (len (zz-batch-sat-fn aigs mk-model mk-proof timeout))
           (len aigs)))

  (defthm zz-batch-sat-fn-entries-consp
    (implies (member-equal entry (zz-batch-sat-fn aigs mk-model mk-proof timeout))
             (consp entry)))

  (defthm zz-batch-sat-fn-entry-sat
    (implies (equal (car (nth n (zz-batch-sat-fn aigs mk-model mk-proof timeout))) 'sat)
             (aig-eval (nth n aigs)
                       (satisfying-assign (nth n aigs)))))

  (defthm zz-batch-sat-fn-entry-sat-model
    (implies (and (equal (car (nth n (zz-batch-sat-fn aigs mk-model mk-proof
                                                      timeout))) 'sat)
                  mk-model)
             (aig-eval (nth n aigs)
                       (cdr (nth n (zz-batch-sat-fn aigs mk-model mk-proof
                                                    timeout))))))

  (defthm zz-batch-sat-fn-entry-unsat
    (implies (equal (car (nth n (zz-batch-sat-fn aigs mk-model mk-proof timeout))) 'unsat)
             (not (aig-eval (nth n aigs) env))))

  (defthmd zz-differentiate-fn-subsets
    (implies (or (member-equal list (mv-nth 0 (zz-differentiate-fn aigs)))
                 (member-equal list (mv-nth 1 (zz-differentiate-fn aigs))))
             (subsetp-equal list aigs)))

  (defthm zz-differentiate-fn-distinct
    (and (no-duplicatesp-equal (mv-nth 0 (zz-differentiate-fn aigs)))
         (no-duplicatesp-equal (mv-nth 1 (zz-differentiate-fn aigs)))
         (not (intersectp-equal (mv-nth 0 (zz-differentiate-fn aigs))
                                (mv-nth 1 (zz-differentiate-fn aigs)))))
    :hints(("Goal" :in-theory (enable intersectp-equal))))

  (defthm zz-differentiate-fn-no-overlaps
    (implies (and (or (member-equal list1 (mv-nth 0 (zz-differentiate-fn aigs)))
                      (member-equal list1 (mv-nth 1 (zz-differentiate-fn
                                                     aigs))))
                  (or (member-equal list2 (mv-nth 0 (zz-differentiate-fn aigs)))
                      (member-equal list2 (mv-nth 1 (zz-differentiate-fn
                                                     aigs))))
                  (not (equal list1 list2)))
             (not (intersectp-equal list1 list2))))

  (defthm zz-differentiate-fn-equiv-classes
    (implies (and (member-equal list (mv-nth 0 (zz-differentiate-fn aigs)))
                  (member-equal a list)
                  (member-equal b list))
             (equal (aig-eval a env) (aig-eval b env))))

  (defthm zz-differentiate-fn-partitions
    (implies (and (or (member-equal list1 (mv-nth 0 (zz-differentiate-fn aigs)))
                      (member-equal list1 (mv-nth 1 (zz-differentiate-fn
                                                     aigs))))
                  (or (member-equal list2 (mv-nth 0 (zz-differentiate-fn aigs)))
                      (member-equal list2 (mv-nth 1 (zz-differentiate-fn
                                                     aigs))))
                  (not (equal list1 list2))
                  (member-equal a list1)
                  (member-equal b list2))
             (aig-eval-exists (aig-xor a b) (mv-nth 2 (zz-differentiate-fn
                                                       aigs)))))

  (defthm consp-zz-modelcheck-fn
    (consp (zz-modelcheck-fn stepfns prop initsts timeout max-depth mk-invar check-invar engine)))

  (defthm consp-zz-modelcheck-fn-trace-when-refuted
    (let ((res (zz-modelcheck-fn stepfns prop initsts timeout max-depth mk-invar check-invar engine)))
      (implies (equal (car res) 'refuted)
               (and (consp (cdr res))
                    (consp (cddr res))))))

  (defthm zz-modelcheck-fn-when-refuted
    (let ((res (zz-modelcheck-fn stepfns prop initsts timeout max-depth mk-invar check-invar engine)))
      (implies (equal (car res) 'refuted)
               (and (equal (check-property stepfns prop (cadr res) (cddr res))
                           nil)
                    (alists-agree (alist-keys initsts) initsts (cadr res))))))

  (defthm zz-modelcheck-fn-when-proved
    (implies
     (and (equal (car (zz-modelcheck-fn stepfns prop initsts timeout max-depth mk-invar check-invar engine))
                 'proved)
          (alists-agree (alist-keys initsts) initsts ctrex-initst))
     (check-property stepfns prop ctrex-initst ctrex-frames))))


(defun zz-sat-exec (aig mk-model mk-proof timeout)
  ;; Has an under-the-hood redefinition
  (declare (xargs :guard (or (not timeout) (natp timeout))))
  (zz-sat-fn aig mk-model mk-proof timeout))

(defun zz-abc-sat-exec (aig mk-model mk-proof timeout abc-cmds)
  ;; Has an under-the-hood redefinition
  (declare (xargs :guard (or (not timeout) (natp timeout))))
  (zz-abc-sat-fn aig mk-model mk-proof timeout abc-cmds))

(defmacro zz-sat (aig &key (mk-model 't) (mk-proof 'nil)
                      (timeout 'nil) (abc-cmds 'nil))
  (if abc-cmds
      `(zz-abc-sat-exec ,aig ,mk-model ,mk-proof ,timeout ,abc-cmds)
    `(zz-sat-exec ,aig ,mk-model ,mk-proof ,timeout)))

(defun zz-differentiate-exec (aigs)
  ;; Has an under-the-hood redefinition
  (declare (xargs :guard t))
  (zz-differentiate-fn aigs))

(defmacro zz-differentiate (aigs)
  `(zz-differentiate-exec ,aigs))

(defun zz-batch-sat-exec (aigs mk-model mk-proof timeout)
  ;; Has an under-the-hood redefinition
  (declare (xargs :guard (or (not timeout) (natp timeout))))
  (zz-batch-sat-fn aigs mk-model mk-proof timeout))

(defun zz-abc-batch-sat-exec (aigs mk-model mk-proof timeout abc-cmds)
  ;; Has an under-the-hood redefinition
  (declare (xargs :guard (or (not timeout) (natp timeout))))
  (zz-abc-batch-sat-fn aigs mk-model mk-proof timeout abc-cmds))

(defmacro zz-batch-sat (aigs &key (mk-model 't) (mk-proof 'nil)
                             (timeout 'nil) (abc-cmds 'nil))
  (if abc-cmds
      `(zz-abc-batch-sat-exec ,aigs ,mk-model ,mk-proof ,timeout ,abc-cmds)
    `(zz-batch-sat-exec ,aigs ,mk-model ,mk-proof ,timeout)))

(defun zz-modelcheck-exec (stepfns prop initsts timeout max-depth mk-invar check-invar engine)
  (declare (xargs :guard t))
  (zz-modelcheck-fn stepfns prop initsts timeout max-depth mk-invar check-invar
                    engine))

(defun zz-abc-modelcheck-exec
  (stepfns prop initsts timeout max-depth mk-invar check-invar abc-cmds engine)
  (declare (xargs :guard t))
  (zz-abc-modelcheck-fn
   stepfns prop initsts timeout max-depth mk-invar check-invar abc-cmds engine))

(defmacro zz-modelcheck (stepfns prop initsts timeout max-depth mk-invar check-invar engine)
  `(zz-modelcheck-exec ,stepfns ,prop ,initsts ,timeout ,max-depth ,mk-invar
                       ,check-invar ,engine))

(defmacro zz-abc-modelcheck (stepfns prop initsts timeout max-depth mk-invar
                                     check-invar abc-cmds engine)
  `(zz-abc-modelcheck-exec ,stepfns ,prop ,initsts ,timeout ,max-depth ,mk-invar
                           ,check-invar ,abc-cmds ,engine))

(defun zz-bmc (stepfns props initsts timeout max-depth)
  (declare (xargs :Guard t))
  (zz-modelcheck stepfns props initsts timeout max-depth nil nil 'bmc))

(defun zz-imc (stepfns props initsts timeout mk-invar check-invar)
  (declare (xargs :Guard t))
  (zz-modelcheck stepfns props initsts timeout nil mk-invar check-invar 'imc))

(defun zz-pdr (stepfns props initsts timeout mk-invar check-invar)
  (declare (xargs :Guard t))
  (zz-modelcheck stepfns props initsts timeout nil mk-invar check-invar 'pdr))


(defun zz-reset-stats-exec ()
  (declare (Xargs :guard t))
  (zz-reset-stats-fn))

(defmacro zz-reset-stats ()
  '(zz-reset-stats-exec))

(defun zz-show-stats-exec ()
  (declare (Xargs :guard t))
  (zz-reset-stats-fn))

(defmacro zz-show-stats ()
  '(zz-show-stats-exec))

; There was originally additional code here to connect to the SAT
; solver backend.
