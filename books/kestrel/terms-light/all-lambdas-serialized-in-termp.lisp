; Checking whether lambdas are serialized
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-trivial-formals")

(mutual-recursion
 ;; Checks whether every lambda in TERM has at most 1 non-trivial formal.
 (defun all-lambdas-serialized-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (or (variablep term)
           (quotep term))
       t
     ;; TERM is a function call (perhaps a lambda application)
     (let ((args (fargs term)))
       (and (all-lambdas-serialized-in-termsp args)
            (let ((fn (ffn-symb term)))
              (if (not (flambdap fn))
                  t
                ;; more than one non-trivial formal would mean the lambda has not been serialized
                (and (<= (len (non-trivial-formals (lambda-formals fn) args)) 1)
                     (all-lambdas-serialized-in-termp (lambda-body fn)))))))))

 (defun all-lambdas-serialized-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
       (and (all-lambdas-serialized-in-termp (first terms))
            (all-lambdas-serialized-in-termsp (rest terms))))))

;; todo: the induction-depth limit here prevents me from seeing all the checkpoints, even though I used :otf-flg
;; (thm
;;  (implies (and (symbol-alistp bindings)
;;                (pseudo-term-listp (strip-cdrs bindings))
;;                (all-lambdas-serialized-in-termsp (strip-cdrs bindings))
;;                (pseudo-termp body))
;;           (all-lambdas-serialized-in-termp (make-lambda-nest bindings body)))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable make-lambda-nest))))

(defthm all-lambdas-serialized-in-termsp-of-remove1-equal
  (implies (all-lambdas-serialized-in-termsp terms)
           (all-lambdas-serialized-in-termsp (remove1-equal term terms))))

(defthm all-lambdas-serialized-in-termsp-of-take
  (implies (all-lambdas-serialized-in-termsp terms)
           (all-lambdas-serialized-in-termsp (take n terms))))

(defthm all-lambdas-serialized-in-termsp-of-append
  (equal (all-lambdas-serialized-in-termsp (append terms1 terms2))
         (and (all-lambdas-serialized-in-termsp terms1)
              (all-lambdas-serialized-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable append))))

(defthm all-lambdas-serialized-in-termsp-of-revappend
  (implies (and (all-lambdas-serialized-in-termsp terms1)
                (all-lambdas-serialized-in-termsp terms2))
           (all-lambdas-serialized-in-termsp (revappend terms1 terms2))))

(defthm all-lambdas-serialized-in-termsp-of-set-difference-equal
  (implies (all-lambdas-serialized-in-termsp terms1)
           (all-lambdas-serialized-in-termsp (set-difference-equal terms1 terms2))))

(defthm all-lambdas-serialized-in-termsp-when-symbol-listp
  (implies (symbol-listp terms)
           (all-lambdas-serialized-in-termsp terms)))
