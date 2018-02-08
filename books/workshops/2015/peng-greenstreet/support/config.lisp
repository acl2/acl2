;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "ACL2")
(include-book "std/util/defaggregate" :dir :system)

(std::defaggregate smtlink-config
  (dir-interface
   dir-files
   SMT-module
   SMT-class
   smt-cmd
   dir-expanded)
  :tag :smtlink-config)

(defconst *default-smtlink-config*
  (make-smtlink-config :dir-interface nil
                       :dir-files nil
                       :SMT-module "ACL2_to_Z3"
                       :SMT-class "ACL22SMT"
                       :smt-cmd "/usr/bin/env python"
                       :dir-expanded nil))

(encapsulate
  (((smt-cnf) => *))
  (local (defun smt-cnf ()
	   *default-smtlink-config*)))

(defun default-smtlink-config ()
  (declare (xargs :guard t))
  (change-smtlink-config *default-smtlink-config*))

(defattach smt-cnf default-smtlink-config)
