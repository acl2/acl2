; Making a nest of lambda applications

; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Makes a nest of lambda applications, one for each of the BINDINGS, around BODY.
;; Could optimize by having this also return the free vars.
(defund make-lambda-nest (bindings ; to be applied in sequence, outer bindings listed first
                         body)
  (declare (xargs :guard (and (symbol-alistp bindings)
                              (pseudo-term-listp (strip-cdrs bindings))
                              (pseudo-termp body))))
  (if (endp bindings)
      body
    (let* ((binding (first bindings))
           (var (car binding))
           (val (cdr binding))
           (body (make-lambda-nest (rest bindings) body))
           (body-vars (free-vars-in-term body)))
      (if (not (member-eq var body-vars))
          ;; This var would be ignored, so just don't bind it:
          body
        (let ((other-body-vars (remove1-eq var body-vars)))
          `((lambda (,var ,@other-body-vars) ,body) ,val ,@other-body-vars))))))

(defthm pseudo-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (pseudo-termp body))
           (pseudo-termp (make-lambda-nest bindings body)))
  :hints (("Goal" :in-theory (enable make-lambda-nest))))
