; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-induction-schemas
  :parents (abstract-syntax)
  :short "Some induction schemas based on the Yul abstract syntax."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expressions-induction2
  :short "Induction on two expressions simultaneously."

  (define expression-induct2 ((old expressionp) (new expressionp))
    (expression-case
     old
     :path (expression-case new
                            :path nil
                            :literal nil
                            :funcall nil)
     :literal (expression-case new
                               :path nil
                               :literal nil
                               :funcall nil)
     :funcall (expression-case new
                               :path nil
                               :literal nil
                               :funcall (funcall-induct2 old.get new.get)))
    :measure (+ (expression-count old) (expression-count new)))

  (define expression-list-induct2 ((old expression-listp)
                                   (new expression-listp))
    (cond ((endp old) nil)
          ((endp new) nil)
          (t (list (expression-induct2 (car old) (car new))
                   (expression-list-induct2 (cdr old) (cdr new)))))
    :measure (+ (expression-list-count old) (expression-list-count new)))

  (define funcall-induct2 ((old funcallp) (new funcallp))
    (expression-list-induct2 (funcall->args old) (funcall->args new))
    :measure (+ (funcall-count old) (funcall-count new)))

  :flag-local nil)
