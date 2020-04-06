;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abstract-separate" :skip-proofs-okp t)

;; Let's try to do this intuitively first...

;; (defund abs-mkdir
;;   (frame pathname)
;;   (b*
;;       ((frame (partial-collapse frame (butlast 1 pathname)))
;;        (mv (parent-dir error-code) (abs-find-file-helper (frame->root frame)
;;                                                          pathname))
;;        ((mv new-root &) (abs-remove-file (frame->root frame) pathname))
;;        ((unless (equal error-code 0))
;;         (mv frame -1 error-code))
;;        ((mv new-parent-dir error-code)
;;         (abs-place-file parent-dir pathname (make-abs-file :contents nil)))
;;        (frame (frame-with-root
;;                new-root
;;                (put-assoc-equal
;;                 (find-new-index
;;                  ;; Using this, not (strip-cars (frame->frame frame)), to make
;;                  ;; sure we don't get a zero.
;;                  (strip-cars frame))
;;                 new-parent-dir))))
;;     (mv frame -1 error-code)))
