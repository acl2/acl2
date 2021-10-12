;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)

(include-book "../verified/hint-interface")
(include-book "../verified/expand-cp")
(include-book "../config")
(include-book "./run")
(include-book "./write")
(include-book "./z3-py/names")
(include-book "./z3-py/translate")
(include-book "./z3-py/header")

(defttag :tshell)
(value-triple (tshell-ensure))

(defsection SMT-prove
  :parents (trusted)
  :short "SMT-prove is the main functions for transliteration into SMT languages and calling the external SMT solver."

  (encapsulate ()

    (local (defthm lemma-1
             (implies (and (string-listp x) x) (consp x))))

    (local (defthm lemma-2
             (b* (((mv ?exit-status ?lines)
                   (tshell-call cmd :print print :save save)))
               (implies lines (consp lines)))))

    (local (defthm lemma-3
             (implies (and (string-listp x) x) (stringp (car x)))))

    (local (defthm lemma-4
             (b* (((mv ?exit-status ?lines)
                   (tshell-call cmd :print print :save save)))
               (implies lines (stringp (car lines))))))

    (local (in-theory (enable string-or-symbol-p)))
    (define make-fname ((dir stringp) (fname stringp))
      :returns (full-fname stringp)
      (b* ((dir (str-fix dir))
           (fname (str-fix fname))
           (dir (if (equal dir "") "/tmp/py_file" dir))
           ((unless (equal fname ""))
            (concatenate 'string dir "/" fname))
           (cmd (concatenate 'string "mkdir -p " dir " && "
                             "mktemp " dir "/smtlink.XXXXX")))
        (mv-let (exit-status lines)
          (time$ (tshell-call cmd
                              :print nil
                              :save t)
                 ;; :msg "; mktemp: `~s0`: ~st sec, ~sa bytes~%"
                 :msg ""
                 :args (list cmd))
          (if (and (equal exit-status 0) (not (equal lines nil)))
              (car lines)
            (prog2$ (er hard? 'SMT-prove=>make-fname "Error: Generate file error.")
                    "")))))
    )

  (define SMT-prove ((term pseudo-termp) (smtlink-hint smtlink-hint-p) (state))
    ;; :returns (mv (proved? booleanp)
    ;;              (precond pseudo-termp)
    ;;              (state))
    :mode :program
    (b* ((term (pseudo-term-fix term))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ((smt-config c) h.configurations)
         (smt-file (make-fname c.smt-dir c.smt-fname))
         ((mv smt-term precond)
          (SMT-translation term h state))
         (sc (smt-config->smt-cnf c))
         ((mv head import) (SMT-head sc))
         (state (SMT-write-file smt-file head import smt-term state))
         ((mv result state) (SMT-interpret smt-file c.rm-file sc state)))
      (mv result precond state)))
  )
