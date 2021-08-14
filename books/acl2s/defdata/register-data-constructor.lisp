#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
API to register a data constructor
author: harshrc
file name: register-data-constructor.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "defdata-util")


; DATA CONSTRUCTOR TABLE
(table data-constructor-table nil nil :clear)

(def-const *register-data-constructor-keywords*
  '(:verbose :hints :proper :rule-classes :local-events
             :export-defthms :theory-name :recordp))

(defmacro register-data-constructor (recog-constr-pair pred-dex-lst &rest keys)
  (declare (xargs :guard (and (consp recog-constr-pair)
                              (proper-symbolp (car recog-constr-pair))
                              (proper-symbolp (cadr recog-constr-pair))
                              (symbol-doublet-listp pred-dex-lst))))
  (let* ((verbosep (let ((lst (member :verbose keys)))
                     (and lst (cadr lst))))
         (ctx 'register-data-constructor))
    `(with-output ,@(and (not verbosep) '(:off :all :on comment)) :stack :push
       (make-event
        (register-data-constructor-fn
         ',recog-constr-pair
         ',pred-dex-lst
         ',keys
         ',ctx
         (current-package state)
         (w state))))))



;;--eg:(get-proper-dex-theorems 'cons '(car cdr))
;;--         ==>
;;--((EQUAL (CAR (CONS CAR CDR)) CAR)
;;-- (EQUAL (CDR (CONS CAR CDR)) CDR))
(defun get-proper-dex-theorems1 (conx-name dex-names rem-dex-names)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (symbol-listp rem-dex-names))))
  (if (endp rem-dex-names)
    nil
    ;; (if recordp
    ;;   (let ((d-keyword-name (intern (symbol-name (car rem-dex-names)) "KEYWORD")))
    ;;     (cons `(equal (mget ,d-keyword-name (,conx-name . ,dex-names))
    ;;                   ,(car rem-dex-names))
    ;;           (get-proper-dex-theorems1 conx-name dex-names
    ;;                                   (cdr rem-dex-names) recordp)))
      (cons `(equal (,(car rem-dex-names) (,conx-name . ,dex-names))
                    ,(car rem-dex-names))
            (get-proper-dex-theorems1 conx-name dex-names
                                      (cdr rem-dex-names)))))

(defun get-proper-dex-theorems (conx-name dex-names)
  (declare (xargs :guard (and (symbolp conx-name) (symbol-listp dex-names))))
  (get-proper-dex-theorems1 conx-name dex-names dex-names))


(defun apply-to-x-lst (fns pkg)
;  (declare (xargs :guard (true-listp fns)))
  (b* ((x (acl2s::fix-intern$ "X" pkg)))
    (list-up-lists fns (make-list (len fns) :initial-element x))))

(defun register-data-constructor-fn
    (recog-constr-pair pred-dex-lst keys ctx pkg wrld)
  (declare (ignorable wrld))
  (b* (((mv kwd-alist rest)
        (extract-keywords ctx *register-data-constructor-keywords* keys nil nil))
       ((when rest) (er hard? ctx "~| Error: Extra args: ~x0~%" rest))
       ((list recog conx-name) recog-constr-pair)
       (dex-names (strip-cadrs pred-dex-lst))
       (dpreds (strip-cars pred-dex-lst))
       (hyps (build-one-param-calls dpreds dex-names))
       (hyp (if (and (consp hyps) (consp (cdr hyps))) ;at least 2
                (cons 'AND hyps)
              (if (consp hyps)
                  (car hyps)
                t)))
       (rule-classes (if (member :rule-classes keys)
                         (get1 :rule-classes kwd-alist)
                       (list :rewrite)))
       (hints (get1 :hints kwd-alist))
       (proper (if (assoc :proper kwd-alist) (get1 :proper kwd-alist) t))
       (recordp (get1 :recordp kwd-alist))
       (dest-pred-alist (pairlis$ dex-names dpreds))
       (x (acl2s::fix-intern$ "X" pkg))
       (kwd-alist
        (acons :arity (len dex-names)
               (acons :recog recog
                      (acons :dest-pred-alist dest-pred-alist kwd-alist)))))

    `(ENCAPSULATE
      nil
      (LOGIC)
      (WITH-OUTPUT
       :SUMMARY-OFF (:OTHER-THAN ACL2::FORM) :ON (ERROR)
       (PROGN
        (defthm ,(s+ conx-name '-CONSTRUCTOR-PRED :pkg pkg)
          (implies ,hyp
                   (,recog (,conx-name . ,dex-names)))
          :hints ,hints
          :rule-classes ,rule-classes)

        (defthm ,(s+ conx-name '-CONSTRUCTOR-DESTRUCTORS :pkg pkg)
          (implies (,recog ,x)
                   (and . ,(list-up-lists
                            dpreds
                            (apply-to-x-lst dex-names pkg))))
          :hints ,hints
          :rule-classes ,(if recordp (cons ':generalize rule-classes) rule-classes))


        ,@(and proper
               `((defthm ,(s+ conx-name '-ELIM-RULE :pkg pkg)
                   (implies (,recog ,x)
                            (equal (,conx-name
                                    . ,(apply-to-x-lst dex-names pkg))
                                   ,x))
                   :hints ,hints
                   :rule-classes ,(if (or recordp rule-classes) '(:elim) rule-classes))


                 (defthm ,(s+ conx-name '-CONSTRUCTOR-DESTRUCTORS-PROPER :pkg pkg)
                   (implies ,hyp
                            (and . ,(get-proper-dex-theorems conx-name dex-names)))
                   :hints ,hints
                   :rule-classes ,rule-classes)))
;local
;export-defthms TODO
        (TABLE DATA-CONSTRUCTOR-TABLE ',conx-name ',kwd-alist)
        (VALUE-TRIPLE :REGISTERED)
        )))))

