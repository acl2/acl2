(in-package "BCV")
(include-book "../BCV/typechecker")

(acl2::set-verify-guards-eagerness 0)


;; Wed Jul 13 14:25:51 2005

(defun make-static-class-decl (cn super cp fs ms is as)
  (LIST 'CLASS cn super
        (CONS 'CONSTANT_POOL CP)
        (CONS 'FIELDS fs)
        (CONS 'METHODS ms)
        (CONS 'INTERFACES is)
        (CONS 'ACCESSFLAGS as)))



;; (defun make-static-class-decl (cn super cp fs ms is as ats)
;;   (LIST 'CLASS cn super
;;         (CONS 'CONSTANT_POOL CP)
;;         (CONS 'FIELDS fs)
;;         (CONS 'METHODS ms)
;;         (CONS 'INTERFACES is)
;;         (CONS 'ACCESSFLAGS as)
;;         (CONS 'ATTRIBUTES ats)))



(defun wff-scl-decl-guard-weak (scl-decl)
  (and (true-listp scl-decl)
       (equal (len scl-decl) 8)
       (consp (nth 4 scl-decl))
       (consp (nth 5 scl-decl))
       (consp (nth 6 scl-decl))
       (consp (nth 7 scl-decl))))


;; (defun wff-scl-decl-guard-weak (scl-decl)
;;   (and (true-listp scl-decl)
;;        (equal (len scl-decl) 9)
;;        (consp (nth 4 scl-decl))
;;        (consp (nth 5 scl-decl))
;;        (consp (nth 6 scl-decl))
;;        (consp (nth 7 scl-decl))
;;        (consp (nth 8 scl-decl))))


(defun scl-decl-bcv2jvm (scl-decl)
  (declare (xargs :guard (wff-scl-decl-guard-weak scl-decl)))
  (make-static-class-decl 
    (classClassName scl-decl)
    (classSuperClassName scl-decl)
    (classConstantPool scl-decl)
    (classFields scl-decl)
    (classMethods scl-decl)
    (classInterfaces scl-decl)
    (classAccessFlags scl-decl)))

;; (defun scl-decl-bcv2jvm (scl-decl)
;;   (declare (xargs :guard (wff-scl-decl-guard-weak scl-decl)))
;;   (make-static-class-decl 
;;     (classClassName scl-decl)
;;     (classSuperClassName scl-decl)
;;     (classConstantPool scl-decl)
;;     (classFields scl-decl)
;;     (classMethods scl-decl)
;;     (classInterfaces scl-decl)
;;     (classAccessFlags scl-decl)
;;     (classAttributes scl-decl)))


(defun scl-bcv2jvm (scl)
  (if (endp scl) nil
    (cons (scl-decl-bcv2jvm (car scl))
          (scl-bcv2jvm (cdr scl)))))

(defun scl-jvm2bcv (raw-scl)
  (if (endp raw-scl) nil
    (cons (make-class-def (car raw-scl))
          (scl-jvm2bcv (cdr raw-scl)))))


(defun good-scl (scl)
  (and (not (isClassTerm 
             (class-by-name 
              (classSuperClassName 
               (class-by-name "java.lang.Object" scl))
              scl)))
       (not (isClassTerm (class-by-name nil scl)))
       (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl)))



;;Fri Jul 15 18:17:33 2005
