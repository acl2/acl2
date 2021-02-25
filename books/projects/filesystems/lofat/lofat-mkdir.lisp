(in-package "ACL2")

;  lofat-pwrite.lisp                                   Mihir Mehta

(include-book "../lofat")
(include-book "../hifat-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac)))

(defund lofat-mkdir (fat32$c path)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path))))
  (b* ((dirname (dirname path))
       ;; Never pass relative paths to syscalls - make them always begin
       ;; with "/".
       ((mv root-d-e-list &) (root-d-e-list fat32$c))
       ((mv parent-dir errno)
        (lofat-find-file fat32$c root-d-e-list dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (lofat-directory-file-p parent-dir))))
        (mv fat32$c -1 *enoent*))
       ((mv & errno)
        (lofat-find-file fat32$c root-d-e-list path))
       ((when (equal errno 0))
        (mv fat32$c -1 *eexist*))
       (basename (basename path))
       ((unless (equal (length basename) 11))
        (mv fat32$c -1 *enametoolong*))
       (d-e
        (d-e-install-directory-bit
         (d-e-fix nil)
         t))
       (file (make-lofat-file :d-e d-e
                              :contents nil))
       ((mv fat32$c error-code)
        (lofat-place-file fat32$c
                          (pseudo-root-d-e fat32$c)
                          path file))
       ((unless (equal error-code 0))
        (mv fat32$c -1 error-code)))
    (mv fat32$c 0 0)))

(defthm integerp-of-lofat-mkdir
  (integerp (mv-nth 1 (lofat-mkdir fat32$c path)))
  :hints (("Goal" :in-theory (enable lofat-mkdir)) ))

(defthm lofat-fs-p-of-lofat-mkdir
  (implies (lofat-fs-p fat32$c)
           (lofat-fs-p (mv-nth 0 (lofat-mkdir fat32$c path))))
  :hints (("goal" :in-theory (e/d (lofat-mkdir)
                                  (nth)))))

(defthm lofat-mkdir-correctness-1
  (and
   (integerp (mv-nth 1 (lofat-mkdir fat32$c path)))
   (natp (mv-nth 2
                 (lofat-mkdir fat32$c path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-mkdir)))
  :rule-classes ((:type-prescription
                  :corollary
                  (integerp (mv-nth 1 (lofat-mkdir fat32$c path))))
                 (:type-prescription
                  :corollary
                  (natp (mv-nth 2 (lofat-mkdir fat32$c path))))))

(defthm
  lofat-mkdir-refinement
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    ;; Let's discuss this hypothesis.
    ;;
    ;; This is something that we actually should
    ;; be able to derive from the structure of lofat-to-hifat-helper. That is,
    ;; we should be able to say that if we're able to do lofat-to-hifat-helper
    ;; with the max-entry-count parameter after the lofat-place-file operation,
    ;; then obviously we must have the capacity for that number of entries. And
    ;; if we don't have the capacity for that number of entries, then we must
    ;; be contradicting the hypothesis about the error code of lofat-place-file
    ;; being other than EIO. That is, this hypothesis should be implied by
    ;; that one, because in the case where that one holds, we must have gotten
    ;; away without an error while creating the new entry, and that means we
    ;; couldn't have exceeded the max entry count!
    ;;
    ;; That kind of reasoning, however, is exactly the kind of thing we gave up
    ;; on a while earlier. Now is not a great time to start either.
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not
     (equal
      (mv-nth 2 (lofat-mkdir fat32$c path))
      *enospc*)))
   (and (equal (mv-nth 1
                       (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
               0)
        (hifat-equiv
         (mv-nth 0
                 (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
         (mv-nth 0
                 (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                              path)))
        (equal (mv-nth 1 (lofat-mkdir fat32$c path))
               (mv-nth 1
                       (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                    path)))
        (equal (mv-nth 2 (lofat-mkdir fat32$c path))
               (mv-nth 2
                       (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                    path)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))
