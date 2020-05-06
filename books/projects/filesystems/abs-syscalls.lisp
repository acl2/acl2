;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abs-find-file")
(include-book "hifat-syscalls")

;; Let's try to do this intuitively first...

(defund
  abs-place-file (frame pathname file)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))
          :guard-debug t
          :guard-hints (("Goal" :do-not-induct t) )
          :verify-guards nil))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((mv tail tail-error-code)
        (abs-place-file (cdr frame) pathname file))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              pathname)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast 1 pathname))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-place-file (frame-val->dir (cdar frame)) pathname file)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

(defthm
  frame-p-of-abs-place-file
  (implies (frame-p frame)
           (frame-p (mv-nth 0 (abs-place-file
                               frame
                               pathname
                               file))))
  :hints (("Goal" :in-theory (enable abs-place-file))))

(defund
  abs-remove-file (frame pathname)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))
          :guard-debug t
          :guard-hints (("Goal" :do-not-induct t) )
          :verify-guards nil))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((mv tail tail-error-code)
        (abs-remove-file (cdr frame) pathname))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              pathname)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast 1 pathname))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-remove-file (frame-val->dir (cdar frame)) pathname)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

(defund abs-mkdir
  (frame pathname)
  (b*
      ((frame (partial-collapse frame (butlast 1 pathname)))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file-helper (frame->root frame)
                                                         pathname))
       ((mv new-root &) (abs-remove-file (frame->root frame) pathname))
       ((unless (equal error-code 0))
        (mv frame -1 error-code))
       ((mv new-parent-dir error-code)
        (abs-place-file parent-dir pathname (make-abs-file :contents nil)))
       (frame (frame-with-root
               new-root
               (put-assoc-equal
                (find-new-index
                 ;; Using this, not (strip-cars (frame->frame frame)), to make
                 ;; sure we don't get a zero.
                 (strip-cars frame))
                new-parent-dir
                (frame->frame frame)))))
    (mv frame -1 error-code)))

(defthm abs-mkdir-correctness-lemma-1
  (implies (atom pathname)
           (equal (1st-complete-under-pathname frame pathname)
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname
                                     1st-complete prefixp))))

;; Move later.
(defthm true-listp-of-frame-with-root
  (equal (true-listp (frame-with-root root frame))
         (true-listp frame))
  :hints (("goal" :in-theory (enable frame-with-root))))
(defthm true-listp-of-put-assoc
  (implies (not (null name))
           (iff (true-listp (put-assoc-equal name val alist))
                (or (true-listp alist)
                    (atom (assoc-equal name alist))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (mv-nth 1 (collapse frame))
                   (atom pathname)
                   (equal frame
                          (frame-with-root (frame->root frame)
                                           (frame->frame frame))))
              (equal (partial-collapse frame pathname)
                     (frame-with-root (mv-nth 0 (collapse frame))
                                      nil)))
     :hints (("goal" :in-theory (enable partial-collapse collapse collapse-this)
              :induct (collapse frame)
              :expand (partial-collapse frame pathname)))))

  (defthm
    abs-mkdir-correctness-lemma-2
    (implies
     (and (mv-nth 1
                  (collapse (frame-with-root root frame)))
          (atom pathname)
          (atom (assoc-equal 0 frame))
          (frame-p frame))
     (equal (partial-collapse (frame-with-root root frame)
                              pathname)
            (frame-with-root (mv-nth 0
                                     (collapse (frame-with-root root frame)))
                             nil)))
    :hints (("goal" :use (:instance lemma
                                    (frame (frame-with-root root frame)))))))

;; (thm
;;  (b*
;;      (((mv fs result) (collapse (frame-with-root root frame))))
;;    (implies
;;     (and
;;      result
;;      (atom (assoc-equal 0 frame))
;;      (frame-p frame))
;;     (and (mv-nth 1 (collapse (mv-nth 0 (abs-mkdir (frame-with-root root frame)
;;                                                   pathname))))
;;          (absfat-equiv (mv-nth 0 (collapse (mv-nth 0 (abs-mkdir
;;                                                       (frame-with-root root
;;                                                                        frame)
;;                                                       pathname))))
;;                        (mv-nth 0 (hifat-mkdir fs pathname))))))
;;  :hints (("Goal" :in-theory (enable hifat-mkdir abs-mkdir collapse)
;;           :do-not-induct t)) :otf-flg t)
