;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 3rd 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "basic-hints")

;; initializing the smt-hint-table table
(table smt-hint-table)
;; get the smt-hint-table table
(define get-smt-hint-table ((world plist-worldp))
  :returns (tb smtlink-hint-alist-p)
  (b* ((tb (table-alist 'smt-hint-table world))
       ((unless (smtlink-hint-alist-p tb))
        (er hard? 'smt-hint-table=>get-smt-hint-table
            "smt-hint-table should be of type smtlink-hint-alistp, but
             unfortunately it's not. Do not panic, please take a look at
             (table-alist 'smt-hint-table world).~%")))
    tb))

;; add a smtlink-hint to the smt-hint-table table
(defmacro add-smtlink-hint (name hint)
  (declare (xargs :guard (symbolp name)))
  `(table smt-hint-table ',name ,hint))

;; When certifying this book, a default hint is put into the smt-hint-table
;; table
(add-smtlink-hint :default (make-basic-hints))

;; ------------------------------------------------------
;; Functions for updating the smt-hint-table table

(define get-smtlink-hint ((hintname symbolp)
                          (world plist-worldp))
  :returns (hint smtlink-hint-p)
  (b* ((tb (get-smt-hint-table world))
       (the-hint-cons (assoc-equal hintname tb))
       ((unless (consp the-hint-cons))
        (prog2$ (er hard? 'hint-interface=>get-smtlink-hint
                    "Can't find the hint from smt-hint-table: ~p0. See the
                     table using (get-smt-hint-table world)~%" hintname)
                (make-smtlink-hint))))
    (cdr the-hint-cons)))

(defmacro add-type (name type world)
  (declare (xargs :guard `(and (plist-worldp ,world)
                               (smt-fixtype-p ,type)
                               (symbolp name))))
  `(make-event
    (b* ((default-hint (get-smtlink-hint ',name ,world))
         (new-hint
          (change-smtlink-hint
           default-hint
           :types (cons ,type (smtlink-hint->types default-hint)))))
      (value `(table smt-hint-table ',,name ',new-hint)))))

(define clear-type ((hintname symbolp)
                    (world plist-worldp))
  :returns (hint smtlink-hint-p)
  (b* ((tb (get-smt-hint-table world))
       (the-hint-cons (assoc-equal hintname tb))
       ((unless (consp the-hint-cons))
        (prog2$ (er hard? 'hint-interface=>get-smtlink-hint
                    "Can't find the hint from smt-hint-table: ~p0. See the
                     table using (get-smt-hint-table world)~%" hintname)
                (make-smtlink-hint))))
    (change-smtlink-hint (cdr the-hint-cons) :types nil)))

(defmacro set-uninterpreted (uninterpreted hintname w)
  `(make-event
    (b* ((new-hint (change-smtlink-hint
                    (get-smtlink-hint ',hintname ,w)
                    :uninterpreted ,uninterpreted))
         (- (cw "~q0" new-hint)))
      (value `(table smt-hint-table ',,hintname ',new-hint)))))
