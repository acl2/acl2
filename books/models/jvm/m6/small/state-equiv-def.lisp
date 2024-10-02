(in-package "ACL2")
(include-book "jvm-model")
(include-book "djvm-model")


(defun method-equiv (jvm-method djvm-method)
  (and (equal (g 'method-name jvm-method)
              (g 'method-name djvm-method))
       (equal (g 'max-stack jvm-method)
              (g 'max-stack djvm-method))
       (equal (g 'nargs jvm-method)
              (g 'nargs djvm-method))
       (equal (g 'code jvm-method)
              (g 'code djvm-method))))
              


(defun class-table-equiv (jvm-method-table djvm-method-table)
  (if (endp djvm-method-table) t
      (and (method-equiv (binding (caar djvm-method-table)
                                  jvm-method-table)
                         (cdar djvm-method-table))
           (class-table-equiv jvm-method-table (cdr djvm-method-table)))))


;;r (defun class-table-equiv2 (jvm-method-table djvm-method-table)
;;   (if (endp jvm-method-table) t
;;       (and (method-equiv  (cdar jvm-method-table)
;;                           (binding (caar jvm-method-table)
;;                                    djvm-method-table))
;;            (class-table-equiv2 (cdr jvm-method-table) djvm-method-table))))
;;
;;
;; (defun class-table-equiv (jvm-method-table djvm-method-table)
;;   (and (class-table-equiv1  



(defun opstack-equiv (jvm-opstack djvm-opstack)
  (equal jvm-opstack 
         djvm-opstack))

(defun local-equiv (jvm-local djvm-local)
  (equal jvm-local djvm-local))


(defun call-frame-equiv (jvm-call-frame djvm-call-frame)
  (and (equal (g 'pc jvm-call-frame)
              (g 'pc djvm-call-frame))
       (equal (g 'method-name jvm-call-frame)
              (g 'method-name djvm-call-frame))
       (opstack-equiv (g 'op-stack jvm-call-frame)
                      (g 'op-stack djvm-call-frame))
       (local-equiv (g 'locals jvm-call-frame)
                    (g 'locals djvm-call-frame))))


(defun call-stack-equiv (jvm-call-stack djvm-call-stack)
  (if (endp jvm-call-stack)
      (endp djvm-call-stack)
    (if (endp djvm-call-stack) nil
      (and (call-frame-equiv (topx jvm-call-stack) (topx djvm-call-stack))
           (call-stack-equiv (popx jvm-call-stack) (popx djvm-call-stack))))))



(defun state-equiv (jvm-s djvm-s)
  (and (class-table-equiv (g 'method-table jvm-s)
                          (g 'method-table djvm-s))
       (call-stack-equiv (g 'call-stack jvm-s)
                         (g 'call-stack djvm-s))))

