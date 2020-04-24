;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abstract-separate" :skip-proofs-okp t)

;; Let's try to do this intuitively first...

;; (defund
;;   abs-place-file (frame pathname file)
;;   (declare
;;    (xargs :guard (and (frame-p frame)
;;                       (fat32-filename-list-p pathname))
;;           :guard-debug t
;;           :guard-hints (("Goal" :do-not-induct t) )))
;;   (b*
;;       (((when (atom frame))
;;         (mv frame *enoent*))
;;        (pathname (mbe :exec pathname
;;                       :logic (fat32-filename-list-fix pathname)))
;;        ((mv tail tail-error-code)
;;         (abs-place-file (cdr frame) pathname file))
;;        ((unless (and (equal tail-error-code *ENOENT*)
;;                      (prefixp (frame-val->path (cdar frame))
;;                               pathname)))
;;         (mv (list* (car frame) tail) tail-error-code))
;;        ;; Look up the parent directory - it has to be in one of the variables,
;;        ;; or else we must return ENOENT.
;;        ((mv & error-code)
;;         (abs-find-file-helper
;;          (frame-val->dir (cdar frame))
;;          (nthcdr (len (frame-val->path (cdar frame)))
;;                  (butlast 1 pathname))))
;;        ((when (or (equal error-code *enoent*)
;;                   (not (abs-complete (frame-val->dir (cdar frame))))))
;;         (mv (list* (car frame) tail) tail-error-code))
;;        ((mv head head-error-code)
;;         (hifat-place-file (frame-val->dir (cdar frame)) pathname file)))
;;     (mv
;;      (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
;;             (cdr frame))
;;      head-error-code)))

;; (defthm
;;   frame-p-of-abs-place-file
;;   (implies (frame-p frame)
;;            (frame-p (mv-nth 0 (abs-place-file
;;                                frame
;;                                pathname
;;                                file))))
;;   :hints (("Goal" :in-theory (enable abs-place-file)) ))

;; (defund abs-mkdir
;;   (frame pathname)
;;   (b*
;;       ((frame (partial-collapse frame (butlast 1 pathname)))
;;        ;; After partial-collapse, either the parent directory is there in one
;;        ;; variable, or it isn't there at all.
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
