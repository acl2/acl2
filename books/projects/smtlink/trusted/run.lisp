;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")

(include-book "std/util/bstar" :dir :system)
(include-book "std/io/read-string" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
;; Proves f-put-global is returning state-p1
(include-book "system/f-put-global" :dir :system)

(include-book "../verified/hint-interface")

(defttag :tshell)
(value-triple (tshell-ensure))
(defttag :read-string)
(set-state-ok t)

(defsection SMT-run
  :parents (trusted)
  :short "SMT-run runs the configured SMT solver then interprets the result and feed it back to ACL2."

  (define SMT-run ((fname stringp) (smt-conf smtlink-config-p))
    :returns (mv (exit-status natp)
                 (lines string-listp))
    (b* ((cmd (concatenate 'string
                           (smtlink-config->smt-cmd smt-conf)
                           " " fname)))
      (time$ (tshell-call cmd
                          :print nil
                          :save t)
             :msg "; SMT solver: `~s0`: ~st sec, ~sa bytes~%"
             :args (list cmd))))

  ;; Changes included to bind counter example to global variable "cex" - Carl
(define SMT-interpret ((fname stringp) (rm-file booleanp) (smt-conf smtlink-config-p) (state))
  (declare (xargs :stobjs state))
    :returns (mv (proved? booleanp)
                 (state))
    :verify-guards nil
    (b* (((mv exit-status lines) (SMT-run fname smt-conf))
         ((unless (equal exit-status 0))
          (mv (er hard? 'SMT-run=>SMT-interpret "Z3 failure: ~q0" lines) state))
         ((if (equal lines nil))
          (mv (er hard? 'SMT-run=>SMT-interpret "Nothing returned from SMT solver.") state))
         ((if (equal (car lines) "proved"))
          (b* (((unless (equal rm-file nil)) (mv t state))
               (cmd (concatenate 'string "rm -f " fname))
               ((mv exit-status-rm lines-rm) (time$ (tshell-call cmd
                                                                 :print nil
                                                                 :save t)
                                                    ;; :msg "; rm -f: `~s0`: ~st sec, ~sa bytes~%"
                                                    :msg ""
                                                    :args (list cmd))))
            (if (equal exit-status-rm 0)
                (mv t state)
              (mv (er hard? 'SMT-run=>SMT-interpret "Remove file error.~% ~p0~%" lines-rm)
                  state))))
         ((mv err str state) (read-string (car lines) :state state))
         ((unless (equal err nil))
          (prog2$ (er hard? 'SMT-run=>SMT-interpret "Read-string error.~%~p0~%" err)
                  (mv nil state)))
         ((unless (and (true-listp str)
                       ;; These are guards for unquote
                       (listp (car str)) (equal (caar str) 'quote)
                       (consp (cdar str))))
          (prog2$
           (er hard? 'SMT-run=>SMT-interpret "We can't prove anything about the ~
thing returned by read-string. So we add a check for it. It's surprising that ~
the check for (true-listp str) and (consp (car str)) failed: ~q0" str)
           (mv nil state)))
         (- (cw "Possible counter-example found: ~p0~%One can access it ~
                 through global variable SMT-cex by doing (@ SMT-cex).~%"
                (unquote (car str))))
         (state (f-put-global 'SMT-cex nil state))
         (state (f-put-global 'SMT-cex (car str) state)))
      (mv nil state)))

  (encapsulate ()
    (local
     (defthm endp-of-not-consp-of-string-listp
       (implies (and (string-listp x) (not (consp x)))
                (not x))
       :rule-classes nil)
     )

    (local
     (defthm stringp-of-consp-of-string-listp
       (implies (and (string-listp x) (consp x))
                (stringp (car x)))
       :rule-classes nil)
     )

    (verify-guards SMT-interpret
      :hints (("goal"
               :in-theory (disable f-put-global)
               :use ((:instance
                      endp-of-not-consp-of-string-listp
                      (x (mv-nth 1 (smt-run fname smt-conf))))
                     (:instance
                      stringp-of-consp-of-string-listp
                      (x (mv-nth 1 (smt-run fname smt-conf))))))))
    )
)

