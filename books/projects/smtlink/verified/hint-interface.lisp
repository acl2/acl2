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

(include-book "../config")
(include-book "../utils/basics")
(include-book "../utils/pseudo-term")

;; (defsection SMT-hint-interface
;;   :parents (verified)
;;   :short "Define default Smtlink hint interface"

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defprod smt-function
  :parents (smtlink-hint)
  ((name symbolp :default nil)
   (formals symbol-listp :default nil)
   (returns symbol-listp :default nil)
   (uninterpreted-hints true-listp :default nil)
   (replace-thm symbolp :default nil)
   (depth natp :default 0)))

(defoption maybe-smt-function smt-function-p)

(deflist smt-function-list
  :parents (smt-function)
  :elt-type smt-function-p
  :true-listp t)

(defprod smt-config
  ((smt-cnf smtlink-config-p :default (make-smtlink-config))
   (rm-file booleanp :default t)
   (smt-dir stringp :default "")
   (smt-fname stringp :default "")))

(deftagsum int-to-rat
  (:switch ((okp booleanp :default nil)))
  (:symbol-list ((lst symbol-listp :default nil))))

(defprod smt-hypo
  ((thm symbolp)
   (subst symbol-pseudo-term-alistp)))

(deflist smt-hypo-list
  :elt-type smt-hypo-p
  :true-listp t)

(defprod smt-sub/supertype
  ((type symbolp)
   (formals symbol-listp)
   (thm symbolp)))

(deflist smt-sub/supertype-list
  :elt-type smt-sub/supertype-p
  :true-listp t)

(defprod smt-type
  ((recognizer symbolp)
   (functions smt-function-list-p)
   (subtypes smt-sub/supertype-list-p)
   (supertypes smt-sub/supertype-list-p)))

(deflist smt-type-list
  :elt-type smt-type-p
  :true-listp t)

(local (in-theory (disable symbol-listp)))

(defprod smtlink-hint
  :parents (SMT-hint-interface)
  ((functions smt-function-list-p :default nil)
   (types smt-type-list-p :default nil)
   (hypotheses smt-hypo-list-p :default nil)
   (configurations smt-config-p :default (make-smt-config))
   (int-to-ratp int-to-rat-p :default (make-int-to-rat-switch :okp nil))
   (under-inductionp symbolp :default nil)
   (global-hint symbolp :default nil)
   (wrld-fn-len natp :default 0)
   (customp booleanp :default nil)))

(defalist smtlink-hint-alist
  :key-type symbolp
  :val-type smtlink-hint-p
  :true-listp t)

(defthm assoc-equal-of-smtlink-hint-alist
  (implies (and (smtlink-hint-alist-p alst)
                (assoc-equal x alst))
           (smtlink-hint-p (cdr (assoc-equal x alst)))))
