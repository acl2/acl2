
(in-package "ACL2")

;; Note: This book should be included in conjunction with
;; memory-mgmt-raw.lisp; otherwise, these functions won't do
;; much of anything interesting.

(defun hons-analyze-memory (slowp)
  (declare (xargs :guard t)
           (ignore slowp))
  (er hard? 'hons-analyze-memory "Raw lisp definition not installed?"))

(defun maybe-wash-memory-fn (n clear)
  (declare (xargs :guard t)
           (ignore n clear))
  (cw "maybe-wash-memory is defined under the hood~%"))

(defmacro maybe-wash-memory (n &optional clear)
  `(maybe-wash-memory-fn ,n ,clear))

(add-macro-alias maybe-wash-memory maybe-wash-memory-fn)


(defun set-max-mem (n)
  (declare (xargs :guard t)
           (ignore n))
  (cw "set-max-mem is defined under the hood~%"))


(defun print-rwx-size ()
  (declare (xargs :guard t))
  (cw "print-rwx-size is defined under the hood~%"))


(defun last-chance-wash-memory-fn ()
  (declare (xargs :guard t))
  ;; Sol: I removed this printing because in certain places I use BDD functions
  ;; without loading the -raw book, and if it prints this line each time it's
  ;; messy.
  ;; (cw "last-chance-wash-memory is defined under the hood~%")
  nil)

(defmacro last-chance-wash-memory ()
  `(last-chance-wash-memory-fn))

(add-macro-alias last-chance-wash-memory last-chance-wash-memory-fn)


(in-theory (disable maybe-wash-memory
                    (maybe-wash-memory)
                    (:type-prescription maybe-wash-memory-fn)
                    last-chance-wash-memory
                    (last-chance-wash-memory)
                    (:type-prescription last-chance-wash-memory-fn)
                    set-max-mem
                    (set-max-mem)
                    (:type-prescription set-max-mem)))

