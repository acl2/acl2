;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 4th 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(value-triple (tshell-ensure))

(defsection SMT-config
  :parents (verified)
  :short "Define default Smtlink config and custom Smtlink config"

  (defprod smtlink-config
    :parents (SMT-config)
    ((interface-dir stringp :default "" "The directory to the customized Python file")
     (smt-module    stringp :default "" "The file/Module name")
     (smt-class     stringp :default "" "The Python class name")
     (smt-cmd       stringp :default "" "The Python command")
     (pythonpath    stringp :default "" "The PYTHONPATH to libraries")))

(local
 (defthm all-boundp-of-initial-glb
   (implies (state-p x)
            (all-boundp acl2::*initial-global-table*
                        (global-table x)))))

(local
 (defthm boundp-of-system-books-dir
   (implies (state-p state)
            (acl2::f-boundp-global 'acl2::system-books-dir state))
   :hints (("Goal"
            :in-theory (disable all-boundp-of-initial-glb)
            :use ((:instance all-boundp-of-initial-glb (x state)))))))

(defconsts *default-smtlink-config*
  (b* ((sys-dir (f-get-global 'acl2::system-books-dir state))
       ((unless (stringp sys-dir))
        (er hard? 'SMT-config=>*default-smtlink-config* "Failed to find ~
where the system books are."))
       (relative-smtlink-dir "projects/smtlink/z3_interface")
       (interface-dir
        (concatenate 'string sys-dir relative-smtlink-dir)))
    (make-smtlink-config :interface-dir interface-dir
                         :smt-module "ACL2_to_Z3"
                         :smt-class "ACL22SMT"
                         :smt-cmd "python"
                         :pythonpath "")))

;; -----------------------------------------------------------------
;; Define custom config using a defstub
(encapsulate
  (((custom-smt-cnf) => *))
  (local (define custom-smt-cnf () (make-smtlink-config)))
  (defthm smtlink-config-p-of-custom-smt-cnf
    (smtlink-config-p (custom-smt-cnf)))
  )

(define default-smtlink-config ()
  (change-smtlink-config *default-smtlink-config*))


(defattach custom-smt-cnf default-smtlink-config)

;; -----------------------------------------------------------------
;; Define baked-in default config

(defalist string-string-alist
  :key-type string
  :val-type string
  :pred string-string-alistp
  :true-listp t)

;; TODO: This check can check a lot of things.
;; Currently only checking if option is one of the valid ones.
(define check-valid-option ((option stringp) (value stringp))
  :returns (valid? booleanp)
  :ignore-ok t
  (b* (((unless (or (equal option "interface-dir")
                    (equal option "smt-module")
                    (equal option "smt-class")
                    (equal option "smt-cmd")
                    (equal option "pythonpath"))) nil))
    t))

(define extract-=-left-and-right ((lines string-listp))
  :returns (config-alist string-string-alistp)
  :measure (len lines)
  :hints (("Goal" :in-theory (enable str::string-list-fix)))
  (b* ((lines (str::string-list-fix lines))
       ((unless (consp lines)) nil)
       ((cons first rest) lines)
       (extracted-line (str::strtok first (list #\=)))
       ((unless (and (consp extracted-line) (endp (cddr extracted-line))
                     (stringp (car extracted-line))
                     (stringp (cadr extracted-line))))
        (er hard? 'SMT-config=>extract-=-left-and-right "Smtlink-config wrong ~
  format!~%~q0" first))
       ((list option value &) extracted-line)
       ((unless (check-valid-option option value))
        (er hard? 'SMT-config=>extract-=-left-and-right "There's something
  wrong with the configuration setup in smtlink-config.")))
    (cons `(,(car extracted-line) . ,(cadr extracted-line))
          (extract-=-left-and-right rest))))

(define process-config ((config-str stringp))
  :returns (config-alist string-string-alistp)
  (b* ((lines (str::strtok config-str (list #\Newline)))
       (config-alist (extract-=-left-and-right lines)))
    config-alist))

(define change-smt-cnf ((config-alist string-string-alistp) (default-cnf smtlink-config-p))
  :returns (smt-cnf smtlink-config-p)
  :measure (len config-alist)
  :hints (("Goal" :in-theory (enable string-string-alist-fix)))
  (b* ((config-alist (string-string-alist-fix config-alist))
       (default-cnf (smtlink-config-fix default-cnf))
       ((unless (consp config-alist)) default-cnf)
       ((cons first rest) config-alist)
       ((cons option value) first)
       (new-cnf (cond
                 ;; ;; if value is "", use the default-cnf
                 ;; ;; default-cnf is $ACL2_SYSTEM_BOOKS/projects/smtlink/z3_interface
                 ;; ((and (equal option "interface-dir") (not (equal value "default")))
                 ;;  (change-smtlink-config default-cnf :interface-dir value))
                 ;; ((equal option "smt-module")
                 ;;  (change-smtlink-config default-cnf :SMT-module value))
                 ;; ((equal option "smt-class")
                 ;;  (change-smtlink-config default-cnf :SMT-class value))
                 ((equal option "smt-cmd")
                  (change-smtlink-config default-cnf :SMT-cmd value))
                 ;; (t (change-smtlink-config default-cnf :PYTHONPATH value))
                 (t default-cnf)
                 )))
    (change-smt-cnf rest new-cnf)))

(define file-exists ((smtconfig stringp) (dir stringp))
  :returns (exist? booleanp)
  (b* ((cmd (concatenate 'string "test -f " dir "/" smtconfig))
       ((mv exit-status &)
        (time$ (tshell-call cmd
                            :print t
                            :save t)
               :msg "; test -f: `~s0`: ~st sec, ~sa bytes~%"
               :args (list cmd))))
    (if (equal exit-status 0) t nil)))

(define find-smtlink-config ((smtconfig stringp) (state t))
  :returns (mv (dir stringp)
               state)
  (b* (((mv & SMT_HOME state) (getenv$ "SMT_HOME" state))
       ((if (and (stringp SMT_HOME)
                 (file-exists smtconfig SMT_HOME)))
        (prog2$ (cw "Reading smtlink-config from $SMT_HOME...~%")
                (mv SMT_HOME state)))
       ((mv & HOME state) (getenv$ "HOME" state))
       ((if (and (stringp HOME)
                 (file-exists smtconfig HOME)))
        (prog2$ (cw "Reading smtlink-config from $HOME...~%")
                (mv HOME state)))
       ((mv & SMTLINK-PWD state) (getenv$ "PWD" state))
       ((if (and (stringp SMTLINK-PWD)
                 (file-exists smtconfig SMTLINK-PWD)))
        (prog2$ (cw "Reading smtlink-config from Smtlink directory...~%")
                (mv SMTLINK-PWD state))))
    (mv (prog2$
         (er hard? 'SMT-config=>find-smtlink-config "Failed to find smtlink-config.~%")
         "")
        state)))

;;
;; Where does Smtlink find the configuration file smtlink-config?
;; 1. It first search in $SMT_HOME if smtlink-config file exists.
;; 2. If $SMT_HOME is not set, or smtlink-config is not in there,
;;      look in $HOME to see if such a file exists.
;; 3. If smtlink-config is not in $HOME, it takes a look in current smtlink
;;      directory for such a file.
;; 4. Else, an error is produced asking for smtlink-config file
;;

(defconsts (*smt-cnf* state)
  (b* ((smtconfig "smtlink-config")
       ((mv dir state) (find-smtlink-config smtconfig state))
       (res (read-file-into-string (concatenate 'string dir "/" smtconfig)))
       ((unless res) (mv (default-smtlink-config) state))
       (config-alist (process-config res)))
    (mv (change-smt-cnf config-alist (default-smtlink-config)) state)))


(define default-smt-cnf () *smt-cnf*)
)
