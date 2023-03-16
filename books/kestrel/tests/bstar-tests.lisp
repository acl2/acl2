(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; normal case
(defun test-hyphen-binder (x)
  (b* ((- (cw "hi")))
    x))

;; more than one form after the binder (implicit progn)
(defun test-hyphen-binder2 (x)
  (b* ((- (cw "hi") (cw "there") ))
    x))

;; no forms after the binder.  apparently, this is legal!
(defun test-hyphen-binder0 (x)
  (b* ((- ))
    x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; normal case
(defun test-var-binder (x)
  (b* ((y x))
    y))

;; illegal: more than one form given to bind Y
(must-fail
 (defun test-var-binder2 (x)
  (b* ((y 3 x))
    y)))

;; illegal: no forms given to bind Y
(must-fail
 (defun test-var-binder0 (x)
   (b* ((y))
     y)))
