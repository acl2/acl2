#|
This file contains code to generate "list of" enumerators that generate lists of a wide variety of lengths. 
|#

(in-package "ACL2S")
(include-book "utils")

(defconst *python-listof-enumerator-lengths*
  ;; min and max are inclusive
  '((:min 0 :max 0 :weight 1)
    (:min 1 :max 16 :weight 70)
    (:min 17 :max 128 :weight 25)
    (:min 129 :max 1024 :weight 3)
    (:min 1025 :max 10000 :weight 1)))

(defun generate-pylistof-enumerator-helper (name element-type-enum/acc)
  `(defun ,name (len seed acc)
     (if (or (not (integerp len)) (<= len 0))
         (mv acc seed)
       (b* (((mv el seed) (,element-type-enum/acc 0 seed)))
         (,name (1- len) seed (cons el acc))))))

(defmacro generate-attach-pylistof-enumerators (name element-type)
  `(make-event (b* ((name ,name)
                    (element-type ,element-type)
                    (pkg (current-package state))
                    (M (type-metadata-table (w state)))
                    (A (type-alias-table (w state)))
                    (element-type-enum/acc (defdata::enum/acc-name element-type A M))
                    (enum-helper-name (defdata::s+ "PYLISTOF-" name "-HELPER" :pkg pkg))
                    (enum-name (defdata::s+ "PYLISTOF-" name "-ENUM" :pkg pkg))
                    (enum/acc-name (defdata::s+ "PYLISTOF-" name "-ENUM/ACC" :pkg pkg)))
                 `(encapsulate
                   ()
                   ,(generate-pylistof-enumerator-helper enum-helper-name element-type-enum/acc)
                   (defun ,enum/acc-name (n seed)
                     (declare (ignorable n))
                     (declare
                      (xargs :mode :program
                             :guard (unsigned-byte-p 31 seed)))
                     (b* (((mv len seed)
                           (select-from-ranges ,*python-listof-enumerator-lengths* seed)))
                       (,enum-helper-name len seed nil)))
                   (defun ,enum-name (n)
                     (declare (xargs :mode :program))
                     (b* (((mv x &) (,enum/acc-name 0 n))) x))
                   (defdata::defdata-attach ,name :enumerator ,enum-name)
                   (defdata::defdata-attach ,name :enum/acc ,enum/acc-name)))))

;; name and element type should be symbols
(defun attach-pylistof-wrap (name element-type)
  `(generate-attach-pylistof-enumerators ',name ',element-type))

