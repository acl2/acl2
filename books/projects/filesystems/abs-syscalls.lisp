;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abs-find-file")
(include-book "hifat-syscalls")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersectp" :dir :system))

(local (in-theory (e/d (abs-file-p-when-m1-regular-file-p
                        nat-listp-of-strip-cars-when-frame-p
                        no-duplicatesp-of-strip-cars-of-frame->frame)
                       nil)))

(defthm
  abs-addrs-when-absfat-equiv
  (implies (absfat-equiv x y)
           (set-equiv (abs-addrs (abs-fs-fix x))
                      (abs-addrs (abs-fs-fix y))))
  :hints (("goal" :in-theory (e/d (absfat-equiv set-equiv abs-fs-p)
                                  (absfat-equiv-of-ctx-app-lemma-4))
           :use ((:instance absfat-equiv-of-ctx-app-lemma-4
                            (abs-file-alist1 (abs-fs-fix x))
                            (abs-file-alist2 (abs-fs-fix y)))
                 (:instance absfat-equiv-of-ctx-app-lemma-4
                            (abs-file-alist2 (abs-fs-fix x))
                            (abs-file-alist1 (abs-fs-fix y))))))
  :rule-classes :congruence)

(encapsulate
  ()

  (local (defun foo-equiv (fs1 fs2)
           (b* ((good1 (and (m1-file-alist-p fs1) (hifat-no-dups-p fs1)))
                (good2 (and (m1-file-alist-p fs2) (hifat-no-dups-p fs2))))
             (or (not (or good1 good2))
                 (and good1 good2
                      (hifat-subsetp fs1 fs2)
                      (hifat-subsetp fs2 fs1))))))

  (local (defequiv foo-equiv))

  (local (defun bar-equiv (fs1 fs2)
           (b* ((good1 (abs-fs-p fs1))
                (good2 (abs-fs-p fs2)))
             (or (not (or good1 good2))
                 (and good1 good2
                      (absfat-subsetp fs1 fs2)
                      (absfat-subsetp fs2 fs1))))))

  (local (defequiv bar-equiv))

  (local
   (defrefinement bar-equiv foo-equiv
     :hints
     (("goal"
       :in-theory (e/d (absfat-subsetp-correctness-1 abs-fs-p
                                                     absfat-equiv)
                       (abs-addrs-when-m1-file-alist-p abs-addrs-when-absfat-equiv))
       :use
       (abs-addrs-when-m1-file-alist-p
        (:instance
         abs-addrs-when-m1-file-alist-p (x y))
        abs-addrs-when-absfat-equiv))))))

;; Let's try to do this intuitively first...

(defund
  abs-place-file-helper (fs pathname file)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p pathname)
                              (abs-file-p file))
                  :guard-debug t
                  :measure (acl2-count pathname)))
  (b*
      (((unless (consp pathname))
        (mv fs *enoent*))
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem))
        (if (atom (cdr pathname))
            (mv (abs-put-assoc name file fs) 0)
            (mv fs *enotdir*)))
       ((when (and (not (abs-directory-file-p (cdr alist-elem)))
                   (or (consp (cdr pathname))
                       (abs-directory-file-p file))))
        (mv fs *enotdir*))
       ((when
         (not (or (abs-directory-file-p (cdr alist-elem))
                  (consp (cdr pathname))
                  (abs-directory-file-p file)
                  (and (atom alist-elem)
                       (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (abs-put-assoc name file fs) 0))
       ((when (and (atom alist-elem)
                   (>= (len fs) *ms-max-dir-ent-count*)))
        (mv fs *enospc*))
       ((mv new-contents error-code)
        (abs-place-file-helper
         (abs-file->contents (cdr alist-elem))
         (cdr pathname)
         file)))
    (mv (abs-put-assoc
         name
         (make-abs-file
          :dir-ent (abs-file->dir-ent (cdr alist-elem))
          :contents new-contents)
         fs)
        error-code)))

(defthm
  abs-file-alist-p-of-abs-place-file-helper
  (implies
   (and (abs-file-alist-p fs)
        (abs-file-p file))
   (abs-file-alist-p (mv-nth 0
                             (abs-place-file-helper fs pathname file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defund
  abs-place-file (frame pathname file)
  (declare
   (xargs :guard (and (frame-p frame)
                      (abs-file-p file)
                      (fat32-filename-list-p pathname))
          :guard-hints (("Goal" :do-not-induct t) )))
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
                 (butlast pathname 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (abs-place-file-helper (frame-val->dir (cdar frame)) pathname file)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame)
                                                 :dir (abs-fs-fix head)))
            (cdr frame))
     head-error-code)))

(defund
  pathname-clear (pathname frame)
  (declare (xargs :guard (and (fat32-filename-list-p pathname)
                              (frame-p frame))
                  :guard-debug t))
  (b*
      (((when (atom frame)) t)
       ((unless
            (pathname-clear pathname (cdr frame)))
        nil)
       (pathname (mbe :exec pathname :logic (fat32-filename-list-fix
                                             pathname))))
    (and
     (or
      (not (prefixp
            pathname
            (frame-val->path (cdar frame))))
      (equal
       (frame-val->path (cdar frame))
       pathname))
     (or
      (not (prefixp
            (frame-val->path (cdar frame))
            pathname))
      (atom
       (names-at (frame-val->dir (cdar frame))
                 (nthcdr
                  (len (frame-val->path (cdar frame)))
                  pathname)))))))

(defthm
  dist-names-when-pathname-clear
  (implies (pathname-clear pathname frame)
           (dist-names dir pathname frame))
  :hints (("goal" :in-theory (enable dist-names
                                     pathname-clear prefixp intersectp-equal)
           :induct (pathname-clear pathname frame)
           :expand (dist-names dir pathname frame))))

(defthm
  absfat-place-file-correctness-lemma-1
  (implies (and (consp (assoc-equal x frame))
                (abs-complete (frame-val->dir (cdr (assoc-equal x frame))))
                (abs-complete (frame-val->dir val)))
           (equal (1st-complete (put-assoc-equal x val frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  hifat-subsetp-of-put-assoc-1
  (implies
   (and (m1-file-alist-p x)
        (hifat-no-dups-p x)
        (stringp name))
   (equal
    (hifat-subsetp (put-assoc-equal name val x)
                   y)
    (and
     (hifat-subsetp (remove-assoc-equal name x)
                    y)
     (consp (assoc-equal name y))
     (or
      (and (not (m1-directory-file-p (cdr (assoc-equal name y))))
           (not (m1-directory-file-p val))
           (equal (m1-file->contents val)
                  (m1-file->contents (cdr (assoc-equal name y)))))
      (and (m1-directory-file-p (cdr (assoc-equal name y)))
           (m1-directory-file-p val)
           (hifat-subsetp (m1-file->contents val)
                          (m1-file->contents (cdr (assoc-equal name y)))))))))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (put-assoc-equal name val x)
                       (remove-assoc-equal name x)))))

(defthm hifat-subsetp-of-put-assoc-2
  (implies (and (m1-file-alist-p x)
                (hifat-subsetp x (remove-assoc-equal name y)))
           (hifat-subsetp x (put-assoc-equal name val y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-1
  (implies (and (m1-file-alist-p x)
                (atom (assoc-equal name x))
                (hifat-subsetp x y))
           (hifat-subsetp x (remove-assoc-equal name y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-2
  (implies (hifat-subsetp x y)
           (hifat-subsetp (remove-assoc-equal name x)
                          y))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthmd
  hifat-place-file-correctness-lemma-1
  (implies (and (m1-file-alist-p x)
                (m1-file-alist-p y)
                (hifat-no-dups-p x)
                (hifat-no-dups-p y)
                (hifat-subsetp x y)
                (hifat-subsetp y x)
                (or (hifat-no-dups-p (m1-file->contents file))
                    (m1-regular-file-p file)))
           (and
            (hifat-subsetp (mv-nth 0 (hifat-place-file y pathname file))
                           (mv-nth 0 (hifat-place-file x pathname file)))
            (equal (mv-nth 1 (hifat-place-file y pathname file))
                   (mv-nth 1 (hifat-place-file x pathname file)))))
  :hints (("goal" :in-theory (enable hifat-place-file hifat-subsetp))))

;; This isn't a congruence rule, so it may have to be left disabled...
(defthmd
  hifat-place-file-correctness-4
  (implies
   (and (hifat-equiv m1-file-alist2 m1-file-alist1)
        (or (hifat-no-dups-p (m1-file->contents file))
            (m1-regular-file-p file)))
   (and
    (equal (mv-nth 1
                   (hifat-place-file m1-file-alist2 pathname file))
           (mv-nth 1
                   (hifat-place-file m1-file-alist1 pathname file)))
    (hifat-equiv (mv-nth 0
                         (hifat-place-file m1-file-alist2 pathname file))
                 (mv-nth 0
                         (hifat-place-file m1-file-alist1 pathname file)))))
  :hints
  (("goal" :in-theory (enable hifat-place-file hifat-equiv)
    :use ((:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist2))
                     (file file)
                     (pathname pathname)
                     (y (hifat-file-alist-fix m1-file-alist1)))
          (:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist1))
                     (file file)
                     (pathname pathname)
                     (y (hifat-file-alist-fix m1-file-alist2))))
    :do-not-induct t)))

;; Probably tricky to get a refinement relationship (in the defrefinement
;; sense) between literally absfat-equiv and hifat-equiv. But we can still have
;; some kind of substitute...
(encapsulate
  ()

  (local
   (defthmd lemma
     (implies (and (m1-file-alist-p abs-file-alist1)
                   (m1-file-alist-p abs-file-alist2)
                   (hifat-no-dups-p abs-file-alist1)
                   (hifat-no-dups-p abs-file-alist2))
              (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                     (hifat-equiv abs-file-alist1 abs-file-alist2)))
     :hints (("goal" :in-theory (enable absfat-equiv hifat-equiv abs-fs-p
                                        absfat-subsetp-correctness-1)))))

  (defthm
    hifat-equiv-when-absfat-equiv
    (implies (and (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                  (m1-file-alist-p (abs-fs-fix abs-file-alist2)))
             (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                    (hifat-equiv (abs-fs-fix abs-file-alist1)
                                 (abs-fs-fix abs-file-alist2))))
    :hints
    (("goal" :use (:instance lemma
                             (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                             (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))))

(defthm abs-fs-p-when-hifat-no-dups-p
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (abs-fs-p fs))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-fs-p))))

;; Move later.
(defthm
  hifat-place-file-correctness-5
  (implies (hifat-no-dups-p (m1-file->contents file))
           (hifat-no-dups-p (mv-nth 0 (hifat-place-file fs pathname file))))
  :hints
  (("goal"
    :in-theory (enable hifat-place-file)
    :induct (hifat-place-file fs pathname file)
    :expand
    (:with
     (:rewrite hifat-no-dups-p-of-put-assoc)
     (hifat-no-dups-p
      (put-assoc-equal
       (fat32-filename-fix (car pathname))
       (m1-file
        (m1-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car pathname))
                           (hifat-file-alist-fix fs))))
        (mv-nth
         0
         (hifat-place-file
          (m1-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car pathname))
                             (hifat-file-alist-fix fs))))
          (cdr pathname)
          file)))
       (hifat-file-alist-fix fs)))))))

(defthm
  absfat-place-file-correctness-lemma-3
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (abs-fs-p dir)
    (not (consp (abs-addrs dir)))
    (pathname-clear nil frame)
    (not (consp (names-at root nil)))
    (abs-fs-p root)
    (not (zp x))
    (not (consp (assoc-equal 0 frame)))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (subsetp-equal
     (abs-addrs root)
     (frame-addrs-root
      (cons (cons x
                  (frame-val nil
                             (put-assoc-equal (car (last pathname))
                                              file dir)
                             src))
            frame)))
    (mv-nth 1
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
    (absfat-equiv
     (mv-nth 0
             (collapse (frame-with-root root
                                        (cons (cons x (frame-val nil dir src))
                                              frame))))
     fs)
    (no-duplicatesp-equal (abs-addrs root))
    (not (intersectp-equal nil (names-at dir nil)))
    (abs-separate frame))
   (hifat-equiv
    fs
    (mv-nth 0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))))
  :hints (("goal" :in-theory (enable abs-separate
                                     dist-names hifat-equiv-when-absfat-equiv
                                     frame-addrs-root))))

(defthm
  absfat-place-file-correctness-lemma-4
  (implies
   (subsetp-equal
    (abs-addrs root)
    (frame-addrs-root
     (cons (cons x
                 (frame-val nil
                            (put-assoc-equal (car (last pathname))
                                             file dir)
                            src))
           frame)))
   (subsetp-equal (abs-addrs root)
                  (frame-addrs-root (cons (cons x (frame-val 'nil dir src))
                                          frame))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (hifat-equiv-when-absfat-equiv dist-names
                                        abs-separate frame-addrs-root)
         nil)))
  :otf-flg t)

(defthm
  absfat-place-file-correctness-lemma-5
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (cons (cons x
                    (frame-val nil
                               (put-assoc-equal (car (last pathname))
                                                file dir)
                               src))
              frame))))
     (mv-nth
      0
      (hifat-place-file
       fs nil
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth
            0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
           nil)))
        (put-assoc-equal (car (last pathname))
                         file dir)))))
    (equal (mv-nth 1
                   (hifat-place-file fs nil
                                     (put-assoc-equal (car (last pathname))
                                                      file dir)))
           0))
   (hifat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (mv-nth 0 (hifat-place-file fs pathname file))))
  :instructions
  (:promote
   (:=
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last pathname))
                                               file dir)
                              src))
             frame))))
    (mv-nth
     0
     (hifat-place-file
      fs nil
      (m1-file
       (m1-file->dir-ent
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (frame-with-root root
                                      (cons (cons x (frame-val nil dir src))
                                            frame))))
          nil)))
       (put-assoc-equal (car (last pathname))
                        file dir))))
    :equiv hifat-equiv)
   (:bash ("goal" :in-theory (enable hifat-place-file)))))

(defthm absfat-place-file-correctness-lemma-6
  (implies (and (abs-fs-p dir)
                (not (member-equal (car (last pathname))
                                   (names-at dir nil))))
           (not (consp (assoc-equal (car (last pathname))
                                    dir))))
  :hints (("goal" :in-theory (enable names-at))))

(defthm abs-file-p-when-m1-file-p
  (implies (m1-file-p file)
           (abs-file-p file))
  :hints (("goal" :cases ((abs-directory-file-p file)))))

(defthm
  m1-file-p-of-abs-file
  (equal (m1-file-p (abs-file dir-ent contents))
         (or (stringp (abs-file-contents-fix contents))
             (m1-file-alist-p contents)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-p abs-file abs-file-contents-fix
                              abs-file-contents-p
                              m1-file-contents-p))))

(defthm
  m1-file-alist-p-of-abs-place-file-helper
  (implies
   (and (m1-file-alist-p fs)
        (m1-file-p file))
   (m1-file-alist-p (mv-nth 0
                            (abs-place-file-helper fs pathname file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm
  abs-place-file-helper-correctness-1
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (m1-file-p file))
           (equal (abs-place-file-helper fs pathname file)
                  (hifat-place-file fs pathname file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper
                                     hifat-place-file abs-file m1-file
                                     abs-file->dir-ent m1-file->dir-ent)
           :induct (abs-place-file-helper fs pathname file))))

(defthm
  abs-top-addrs-of-abs-place-file-helper
  (equal (abs-top-addrs (mv-nth 0
                                (abs-place-file-helper fs pathname file)))
         (abs-top-addrs fs))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-place-file-helper))))

(defthm
  addrs-at-when-abs-complete
  (implies (abs-complete (abs-fs-fix fs))
           (equal (addrs-at fs relpath) nil))
  :hints
  (("goal" :in-theory (enable addrs-at)
    :induct (addrs-at fs relpath))
   ("subgoal *1/1''" :in-theory (disable ctx-app-ok-when-abs-complete-lemma-3)
    :use ctx-app-ok-when-abs-complete-lemma-3)))

(defthm
  addrs-at-of-abs-place-file-helper-lemma-1
  (implies (and (m1-file-p file)
                (or (m1-regular-file-p file)
                    (hifat-no-dups-p (m1-file->contents file))))
           (not (addrs-at (m1-file->contents file)
                          (cdr relpath))))
  :hints
  (("goal" :in-theory
    (e/d (m1-file-contents-p addrs-at m1-regular-file-p
                             m1-file-p m1-file->contents abs-fs-fix)
         (m1-file-contents-p-of-m1-file->contents))
    :use (:instance m1-file-contents-p-of-m1-file->contents
                    (x file))
    :do-not-induct t))
  :otf-flg t)

(defthm
  addrs-at-of-abs-place-file-helper-1
  (implies (and (abs-fs-p fs)
                (m1-file-p file)
                (or (m1-regular-file-p file)
                    (hifat-no-dups-p (m1-file->contents file))))
           (equal (addrs-at (mv-nth 0
                                    (abs-place-file-helper fs pathname file))
                            relpath)
                  (addrs-at fs relpath)))
  :hints
  (("goal"
    :in-theory (enable abs-place-file-helper addrs-at)
    :induct (mv (fat32-filename-list-prefixp relpath pathname)
                (addrs-at fs relpath))
    :expand
    ((abs-place-file-helper fs pathname file)
     (addrs-at
      (put-assoc-equal
       (fat32-filename-fix (car pathname))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car pathname))
                           fs)))
        (mv-nth
         0
         (abs-place-file-helper
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car pathname))
                             fs)))
          (cdr pathname)
          file)))
       fs)
      relpath)))))

(defthm
  ctx-app-ok-of-abs-place-file-helper-1
  (implies
   (and (abs-fs-p fs)
        (m1-file-p file)
        (or (m1-regular-file-p file)
            (hifat-no-dups-p (m1-file->contents file))))
   (equal (ctx-app-ok (mv-nth 0
                              (abs-place-file-helper fs pathname file))
                      x x-path)
          (ctx-app-ok fs x x-path)))
  :hints (("goal" :in-theory (enable ctx-app-ok))))

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs pathname file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm
  collapse-hifat-place-file-lemma-9
  (implies
   (and (equal (frame->root frame1)
               (mv-nth 0
                       (abs-place-file-helper (frame->root frame2)
                                              pathname file)))
        (m1-file-p file)
        (or (m1-regular-file-p file)
            (hifat-no-dups-p (m1-file->contents file))))
   (equal
    (ctx-app-ok
     (frame->root frame1)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite ctx-app-ok-of-abs-place-file-helper-1))
    :use
    (:instance
     (:rewrite ctx-app-ok-of-abs-place-file-helper-1)
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (file file)
     (pathname pathname)
     (fs (frame->root frame2))))))

(defthm
  collapse-hifat-place-file-lemma-10
  (implies
   (and
    (< 0 (1st-complete (frame->frame frame1)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                          (frame->frame frame1))))
        (frame->frame frame1))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                          (frame->frame frame1))))
        (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                 (frame->frame frame1))))
              (frame->frame frame1)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1))))))
    (equal (frame->frame frame1)
           (frame->frame frame2))
    (dist-names (frame->root frame2)
                nil (frame->frame frame1))
    (abs-separate (frame->frame frame1))
    (no-duplicatesp-equal (strip-cars (frame->frame frame1))))
   (dist-names
    (frame->root frame2)
    nil
    (frame->frame (collapse-this frame1
                                 (1st-complete (frame->frame frame1))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-separate-correctness-1-lemma-32))
    :use (:instance (:rewrite abs-separate-correctness-1-lemma-32)
                    (x (1st-complete (frame->frame frame2)))
                    (frame frame2)))))

(defthm
  collapse-hifat-place-file-lemma-11
  (implies
   (and
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     0)
    (equal (frame->frame frame1)
           (frame->frame frame2))
    (dist-names (frame->root frame2)
                nil (frame->frame frame1))
    (abs-separate (frame->frame frame1)))
   (dist-names
    (ctx-app
     (frame->root frame2)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    nil
    (frame->frame (collapse-this frame1
                                 (1st-complete (frame->frame frame1))))))
  :hints
  (("goal" :in-theory (disable (:rewrite abs-separate-correctness-1-lemma-37))
    :use (:instance (:rewrite abs-separate-correctness-1-lemma-37)
                    (x (1st-complete (frame->frame frame2)))
                    (frame frame2)))))

(defthm abs-place-file-helper-correctness-2
  (implies (not (zp (mv-nth 1
                            (abs-place-file-helper fs pathname file))))
           (equal (mv-nth 0
                          (abs-place-file-helper fs pathname file))
                  fs))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs pathname file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm names-at-of-abs-place-file-helper-lemma-1
  (implies (and (abs-file-p file)
                (not (abs-directory-file-p file)))
           (not (names-at (abs-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at abs-directory-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm
  names-at-of-abs-place-file-helper-lemma-2
  (implies (m1-regular-file-p file)
           (not (names-at (m1-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-directory-file-p m1-regular-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm names-at-of-abs-place-file-helper-lemma-3
  (implies (and (abs-no-dups-p (abs-file->contents file))
                (abs-directory-file-p file))
           (abs-fs-p (abs-file->contents file)))
  :hints (("goal" :in-theory (enable abs-directory-file-p)
           :do-not-induct t)))

(defthm names-at-of-abs-place-file-helper-lemma-4
  (implies (and (abs-file-p file)
                (not (abs-directory-file-p file)))
           (equal (strip-cars (abs-fs-fix (abs-file->contents file)))
                  nil))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-directory-file-p
                              abs-file-p abs-file->contents
                              abs-fs-fix abs-file-contents-p))))

(defthm names-at-of-abs-place-file-helper-lemma-5
  (implies (m1-regular-file-p file)
           (equal (strip-cars (abs-fs-fix (m1-file->contents file)))
                  nil))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-regular-file-p
                              abs-file-p abs-file->contents
                              abs-fs-fix abs-file-contents-p))))

;; (b* ((fs (list (cons (coerce (name-to-fat32-name (coerce "var" 'list)) 'string)
;;                      (make-abs-file))
;;                (cons (coerce (name-to-fat32-name (coerce
;;                                                   "tmp"
;;                                                   'list))
;;                              'string)
;;                      (make-abs-file
;;                       :contents (list
;;                                  (cons
;;                                   (coerce
;;                                    (name-to-fat32-name
;;                                     (coerce
;;                                      "pipe"
;;                                      'list))
;;                                    'string)
;;                                   (make-abs-file)))))))
;;      ((mv val &) (abs-place-file-helper fs (pathname-to-fat32-pathname
;;                                             (coerce "/tmp/hspid" 'list))
;;                                         (make-abs-file))))
;;   (list (names-at val
;;                   (pathname-to-fat32-pathname
;;                    (coerce
;;                     "/tmp"
;;                     'list)))
;;         (names-at fs
;;                   (pathname-to-fat32-pathname
;;                    (coerce
;;                     "/tmp"
;;                     'list)))))

(defthm
  names-at-of-abs-place-file-helper-1
  (implies (and (abs-fs-p fs)
                (abs-file-p file))
           (equal (names-at (mv-nth 0
                                    (abs-place-file-helper fs pathname file))
                            relpath)
                  (cond ((not
                          (zp (mv-nth 1
                                      (abs-place-file-helper fs pathname file))))
                         (names-at fs relpath))
                        ((fat32-filename-list-prefixp pathname relpath)
                         (names-at (abs-file->contents file)
                                   (nthcdr (len pathname) relpath)))
                        ((and (fat32-filename-list-equiv relpath (butlast
                                                                  pathname 1))
                              (not
                               (member-equal (fat32-filename-fix (car (last pathname)))
                                             (names-at fs relpath))))
                         (append (names-at fs relpath)
                                 (list (fat32-filename-fix (car (last pathname))))))
                        (t (names-at fs relpath)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper names-at fat32-filename-list-fix)
                    ((:definition member-equal)
                     (:definition put-assoc-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-3)
                     (:definition abs-complete)
                     (:rewrite hifat-find-file-correctness-1-lemma-1)
                     (:type-prescription assoc-equal-when-frame-p)
                     (:definition assoc-equal)
                     (:definition no-duplicatesp-equal)
                     (:type-prescription len-when-consp)
                     (:rewrite m1-file-alist-p-when-subsetp-equal)
                     (:rewrite subsetp-when-prefixp)))
    :induct (mv (fat32-filename-list-prefixp relpath pathname)
                (names-at fs relpath))
    :expand (abs-place-file-helper fs pathname file))))

(ENCAPSULATE
  ()

  (local
   (defun
     induction-scheme (frame1 frame2)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame1))))
     (cond
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete (frame->frame frame1))
                          (frame->frame frame1))))
           (1st-complete (frame->frame frame1)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (1st-complete (frame->frame frame1))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame1))
               (frame->frame frame1))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1)))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame->root frame1)
         (1st-complete (frame->frame frame1))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      (t (mv frame1 frame2)))))

  (skip-proofs
   (defthmd
     collapse-hifat-place-file-lemma-8
     (implies
      (and
       (equal (frame->frame frame1)
              (frame->frame frame2))
       (equal (frame->root frame1)
              (mv-nth 0
                      (abs-place-file-helper (frame->root frame2)
                                             pathname file)))
       (m1-file-p file)
       (or (m1-regular-file-p file)
           (hifat-no-dups-p (m1-file->contents file)))
       (dist-names (frame->root frame2)
                   nil (frame->frame frame2))
       (abs-separate (frame->frame frame2))
       (frame-p (frame->frame frame2))
       (no-duplicatesp-equal (strip-cars (frame->frame frame2))))
      (and
       (equal
        (mv-nth 0 (collapse frame1))
        (mv-nth
         0
         (abs-place-file-helper (mv-nth 0 (collapse frame2))
                                pathname file)))
       (equal (mv-nth 1 (collapse frame1))
              (mv-nth 1 (collapse frame2)))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (collapse)
        ((:definition no-duplicatesp-equal)
         (:rewrite partial-collapse-correctness-lemma-24)
         (:definition assoc-equal)
         (:rewrite subsetp-when-prefixp)
         (:definition member-equal)
         (:rewrite
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          . 2)
         (:linear count-free-clusters-correctness-1)
         (:rewrite partial-collapse-correctness-lemma-28)
         (:rewrite nthcdr-when->=-n-len-l)
         (:rewrite strip-cars-of-frame->frame-of-collapse-this)
         (:definition len)
         (:definition integer-listp)
         (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
         (:definition remove-equal)
         (:rewrite remove-when-absent)))
       :induct (induction-scheme frame1 frame2)
       :expand (collapse frame2))))))

;; This theorem asserts some things about applying abs-place-file-helper to
;; filesystem instances with holes...
(defthm
  collapse-hifat-place-file-1
  (implies
   (and
    (equal
     (frame->root (frame-with-root (mv-nth 0
                                           (hifat-place-file (abs-fs-fix root)
                                                             pathname file))
                                   frame))
     (mv-nth 0
             (abs-place-file-helper (frame->root (frame-with-root root frame))
                                    pathname file)))
    (m1-file-p file)
    (or (m1-regular-file-p file)
        (hifat-no-dups-p (m1-file->contents file)))
    (dist-names (frame->root (frame-with-root root frame))
                nil
                (frame->frame (frame-with-root root frame)))
    (abs-separate (frame->frame (frame-with-root root frame)))
    (frame-p (frame->frame (frame-with-root root frame)))
    (no-duplicatesp-equal
     (strip-cars (frame->frame (frame-with-root root frame)))))
   (and
    (equal
     (mv-nth
      0
      (collapse (frame-with-root (mv-nth 0
                                         (hifat-place-file (abs-fs-fix root)
                                                           pathname file))
                                 frame)))
     (mv-nth
      0
      (abs-place-file-helper (mv-nth 0
                                     (collapse (frame-with-root root frame)))
                             pathname file)))
    (equal
     (mv-nth
      1
      (collapse (frame-with-root (mv-nth 0
                                         (hifat-place-file (abs-fs-fix root)
                                                           pathname file))
                                 frame)))
     (mv-nth 1
             (collapse (frame-with-root root frame))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite collapse-hifat-place-file-lemma-8)
     (frame1 (frame-with-root (mv-nth 0
                                      (hifat-place-file (abs-fs-fix root)
                                                        pathname file))
                              frame))
     (frame2 (frame-with-root root frame))))))

;; This is based on collapse-hifat-place-file-2, which relies on the lemma
;; collapse-hifat-place-file-lemma-6. That lemma would probably have to be tweaked to
;; deal with all the pathname appending stuff, which I'm skipping over for now.
(skip-proofs
 (defthm
   collapse-hifat-place-file-2
   (implies
    (and
     (m1-file-p file)
     (or (m1-regular-file-p file)
         (hifat-no-dups-p (m1-file->contents file)))
     (dist-names (frame->root (frame-with-root root frame))
                 nil
                 (frame->frame (frame-with-root root frame)))
     (abs-separate (frame->frame (frame-with-root root frame)))
     (frame-p (frame->frame (frame-with-root root frame)))
     (no-duplicatesp-equal
      (strip-cars (frame->frame (frame-with-root root frame)))))
    (and
     (equal
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             pathname file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       0
       (abs-place-file-helper
        (mv-nth 0
                (collapse (frame-with-root root frame)))
        (append (frame-val->path (cdr (assoc-equal x frame)))
                pathname)
        file)))
     (equal
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             pathname file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth 1
              (collapse (frame-with-root root frame))))))))

;; I guess I should say that this function can only really do so much, and if
;; we try to use this in our proofs we'll kinda be back to representing
;; filesystem trees as... filesystem trees. When I say it can only do so much,
;; I mean that it can only help us do some refinement proofs, which will tie
;; lofat to hifat and hifat to absfat. Ultimately, I guess we'll want theorems
;; that use the collapse-equiv relation defined previously...
(defun frame-reps-fs
    (frame fs)
  (b*
      (((mv fs-equiv result) (collapse frame)))
    (and result
         (absfat-equiv fs-equiv fs)
         (abs-separate frame)
         (subsetp-equal
          (abs-addrs (frame->root frame))
          (frame-addrs-root (frame->frame frame))))))

(defcong absfat-equiv equal (frame-reps-fs frame fs) 2)

;; I'm not even sure what the definition of abs-place-file above should be. But
;; I'm pretty sure it should support a theorem like the following.
;;
;; In the hypotheses here, there has to be a stipulation that not only is dir
;; complete, but also that it's the only one which has any names at that
;; particular relpath, i.e. (butlast pathname 1). It's codified under
;; pathname-clear.
;;
;; Also, the use hints in this theorem are awkward but necessary - restrict
;; hints do not work because there's never a real chance for them to be
;; applied, or so :brr tells us.
;;
;; OK, so how do we develop a specification for abs-mkdir which we can actually
;; USE? Like, we would want to say that (abs-mkdir frame) is going to return a
;; new frame and an error code, and that error code will tell us whether to
;; expect an unchanged frame (modulo absfat-equiv) or a new frame with an
;; element right at the front representing the parent directory of the new
;; directory with the new directory inside it.
(defthm
  absfat-place-file-correctness-lemma-2
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname)
    (m1-regular-file-p file)
    (abs-fs-p dir)
    (abs-complete dir)
    (pathname-clear (butlast pathname 1)
                    frame)
    (atom (names-at root (butlast pathname 1)))
    (abs-fs-p root)
    (not (zp x))
    (atom (assoc-equal 0 frame))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (frame-reps-fs
     (frame-with-root root
                      (cons (cons x
                                  (frame-val (butlast pathname 1)
                                             dir src))
                            frame))
     fs)
    (not (member-equal (car (last pathname))
                       (names-at dir nil)))
    (consp pathname))
   (b* ((dir (put-assoc-equal (car (last pathname))
                              file dir))
        (frame (frame-with-root root
                                (cons (cons x
                                            (frame-val (butlast pathname 1)
                                                       dir src))
                                      frame)))
        ((mv fs &)
         (hifat-place-file fs pathname file)))
     (frame-reps-fs frame fs)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (hifat-place-file dist-names
                           abs-separate frame-addrs-root)
         (collapse-hifat-place-file-2
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:definition member-equal)
          (:rewrite len-of-remove-assoc-when-no-duplicatesp-strip-cars)
          (:linear len-of-remove-assoc-1)
          (:definition remove-assoc-equal)
          (:rewrite subsetp-trans)
          (:rewrite abs-addrs-of-put-assoc-lemma-2)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:rewrite collapse-congruence-lemma-4)
          (:definition integer-listp)
          len-when-hifat-bounded-file-alist-p
          member-of-abs-addrs-when-natp
          (:linear position-equal-ac-when-member)
          (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition hifat-file-alist-fix)
          (:rewrite hifat-find-file-correctness-1-lemma-1)
          (:type-prescription ctx-app-list-when-set-equiv-lemma-4)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite abs-no-dups-p-of-put-assoc-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-3)
          (:type-prescription assoc-when-zp-len)
          (:definition take)
          (:rewrite take-of-len-free)
          (:rewrite take-of-too-many)
          (:definition true-listp)
          (:rewrite true-listp-when-string-list)
          (:definition string-listp)))
    :use
    ((:instance collapse-hifat-place-file-2
                (frame (cons (cons x
                                   (frame-val (butlast pathname 1)
                                              dir src))
                             frame))
                (pathname (last pathname)))
     (:instance
      (:rewrite hifat-place-file-correctness-4)
      (file file)
      (pathname pathname)
      (m1-file-alist2
       (mv-nth
        0
        (collapse
         (frame-with-root
          root
          (cons (cons x
                      (frame-val (take (+ -1 (len pathname)) pathname)
                                 dir src))
                frame)))))
      (m1-file-alist1 fs))))))

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
          :guard-hints (("Goal" :do-not-induct t) )))
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
                 (butlast pathname 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-remove-file (frame-val->dir (cdar frame)) pathname)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

;; Move later.
(defthm frame-p-of-partial-collapse
  (implies (frame-p frame)
           (frame-p (partial-collapse frame pathname)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defund abs-disassoc (fs pathname new-index)
  (declare (xargs :guard
                  (and (fat32-filename-list-p pathname)
                       (abs-file-alist-p fs)
                       (natp new-index))
                  :verify-guards nil))
  (b*
      ((new-index
        (mbe :exec new-index :logic (nfix new-index)))
       (pathname
        (mbe :exec pathname :logic (fat32-filename-list-fix pathname)))
       ((when (atom pathname))
        (mv fs (list new-index)))
       (alist-elem (abs-assoc (car pathname) fs))
       ((when (or (atom alist-elem)
                  (not (abs-directory-file-p (cdr alist-elem)))))
        (mv nil fs))
       ((mv x y)
        (abs-disassoc
         (abs-file->contents (cdr alist-elem))
         (cdr pathname)
         new-index)))
    (mv x
        (abs-put-assoc
         (car pathname)
         (change-abs-file
          (cdr alist-elem)
          :contents
          y)
         fs))))

(defthm
  abs-file-alist-p-of-abs-disassoc-1
  (implies
   (abs-file-alist-p fs)
   (abs-file-alist-p (mv-nth 1 (abs-disassoc fs pathname new-index))))
  :hints (("Goal" :in-theory (enable abs-disassoc abs-file-alist-p)
           :induct (abs-disassoc fs pathname new-index))))

(defthm
  abs-file-alist-p-of-abs-disassoc-2
  (implies (abs-file-alist-p fs)
           (abs-file-alist-p (mv-nth 0
                                     (abs-disassoc fs pathname new-index))))
  :hints (("goal" :in-theory (enable abs-disassoc)
           :induct (abs-disassoc fs pathname new-index))))

(defthm
  abs-no-dups-p-of-abs-disassoc-1
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs))
           (abs-no-dups-p (mv-nth 0
                                  (abs-disassoc fs pathname new-index))))
  :hints (("goal" :in-theory (enable abs-disassoc)
           :induct (abs-disassoc fs pathname new-index))))

(defthm
  abs-no-dups-p-of-abs-disassoc-2
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs))
           (abs-no-dups-p (mv-nth 1
                                  (abs-disassoc fs pathname new-index))))
  :hints (("goal" :in-theory (enable abs-disassoc abs-no-dups-p)
           :induct (abs-disassoc fs pathname new-index))))

(defthm
  abs-no-dups-p-of-abs-disassoc-2
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs))
           (abs-no-dups-p (mv-nth 1
                                  (abs-disassoc fs pathname new-index))))
  :hints (("goal" :in-theory (enable abs-disassoc abs-no-dups-p)
           :induct (abs-disassoc fs pathname new-index))))

(verify-guards abs-disassoc)

(defthm abs-mkdir-guard-lemma-1
  (implies (consp (assoc-equal 0 frame))
           (consp (assoc-equal 0 (partial-collapse frame pathname))))
  :hints (("goal" :in-theory (enable partial-collapse))))

;; This deliberately follows an almost-identical induction scheme to
;; abs-find-file. It was going to be a part of that function, but that just led
;; to too many failures.
(defund
  abs-find-file-src (frame pathname)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))))
  (b*
      (((when (atom frame)) 0)
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         pathname))
        (abs-find-file-src (cdr frame) pathname))
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 pathname)))
       ((when (not (equal error-code *enoent*)))
        (mbe :exec (caar frame) :logic (nfix (caar frame)))))
    (abs-find-file-src (cdr frame) pathname)))

(defthm
  abs-find-file-src-correctness-1
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (not (equal (mv-nth 1 (abs-find-file frame pathname))
                    *enoent*)))
   (and
    (consp (assoc-equal (abs-find-file-src frame pathname)
                        frame))
    (prefixp
     (frame-val->path (cdr (assoc-equal (abs-find-file-src frame pathname)
                                        frame)))
     (fat32-filename-list-fix pathname))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame pathname)
                                          frame)))
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal (abs-find-file-src frame pathname)
                                        frame))))
                pathname)))
      *enoent*))))
  :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src))))

(defthm abs-mkdir-guard-lemma-2
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
(defthm alistp-of-frame-with-root
  (implies (frame-p frame)
           (alistp (frame-with-root root frame)))
  :hints (("goal" :in-theory (disable alistp-when-frame-p)
           :use (:instance alistp-when-frame-p
                           (x (frame-with-root root frame))))))
(defthm strip-cars-of-frame-with-root
  (equal (strip-cars (frame-with-root root frame))
         (cons 0 (strip-cars frame)))
  :hints (("goal" :in-theory (enable frame-with-root))))
(defthm
  assoc-after-remove1-assoc-when-no-duplicatesp
  (implies (and (not (null name))
                (no-duplicatesp-equal (remove-equal nil (strip-cars alist))))
           (not (consp (assoc-equal name
                                    (remove1-assoc-equal name alist))))))

(defthm
  abs-mkdir-guard-lemma-3
  (implies (and (mv-nth 1 (collapse frame))
                (atom pathname)
                (equal frame
                       (frame-with-root (frame->root frame)
                                        (frame->frame frame))))
           (equal (partial-collapse frame pathname)
                  (frame-with-root (mv-nth 0 (collapse frame))
                                   nil)))
  :hints (("goal" :in-theory
           (e/d
            (partial-collapse collapse collapse-this)
            ((:definition no-duplicatesp-equal)
             (:rewrite
              partial-collapse-correctness-lemma-24)
             (:definition assoc-equal)
             (:rewrite subsetp-when-prefixp)
             (:definition member-equal)
             (:definition true-listp)
             (:rewrite put-assoc-equal-without-change . 2)
             abs-separate-of-frame->frame-of-collapse-this-lemma-8
             (:rewrite true-list-fix-when-true-listp)
             (:rewrite true-listp-when-string-list)
             (:definition string-listp)
             (:definition put-assoc-equal)
             (:rewrite remove-assoc-of-put-assoc)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:definition remove-assoc-equal)
             (:definition remove-equal)
             (:rewrite fat32-filename-p-correctness-1)))
           :induct (collapse frame)
           :expand (partial-collapse frame pathname))))

(defthm
  abs-mkdir-guard-lemma-4
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
  :hints (("goal"
           :in-theory (disable abs-mkdir-guard-lemma-3)
           :use (:instance abs-mkdir-guard-lemma-3
                           (frame (frame-with-root root frame))))))

(defthm abs-mkdir-guard-lemma-5
  (implies (abs-no-dups-p fs)
           (no-duplicatesp-equal (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-mkdir-guard-lemma-6
  (implies
   (no-duplicatesp-equal (strip-cars frame))
   (no-duplicatesp-equal (strip-cars (partial-collapse frame pathname))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this))))

(defthm
  abs-mkdir-guard-lemma-7
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file-helper fs pathname)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-mkdir-guard-lemma-8
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file frame pathname)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file frame pathname)))))
  :hints (("goal" :in-theory (enable abs-find-file))))

;; OK, here's the plan for defining abs-mkdir. We can proooobably get rid of
;; abs-place-file and abs-remove-file, since those tasks are going to be
;; accomplished by first bringing the parent directory to the front and then
;; doing a put-assoc or a remove-assoc respectively.
(defund abs-mkdir (frame pathname)
  (declare (xargs
            :guard (and (frame-p frame)
                        (consp (assoc-equal 0 frame))
                        (fat32-filename-list-p pathname)
                        (no-duplicatesp-equal (strip-cars frame)))
            :guard-hints
            (("goal"
              :in-theory (enable abs-find-file-helper abs-fs-p)))))
  (b*
      ((pathname (mbe :exec pathname :logic (fat32-filename-list-fix pathname)))
       ((unless (consp pathname)) (mv frame -1 *enoent*))
       (frame (partial-collapse frame (butlast pathname 1)))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file frame (butlast pathname 1)))
       ((unless (zp error-code)) (mv frame -1 error-code))
       ((unless (abs-directory-file-p parent-dir)) (mv frame -1 *enotdir*))
       (src (abs-find-file-src frame (butlast pathname 1)))
       (new-index (find-new-index
                   ;; Using this, not (strip-cars (frame->frame frame)), to make
                   ;; sure we don't get a zero.
                   (strip-cars frame)))
       ;; It's not even a matter of removing that thing - we need to leave a
       ;; body address in its place...
       ((mv var new-src-dir) (abs-disassoc
                              (frame-val->dir (cdr (assoc-equal src frame)))
                              (butlast pathname 1) new-index))
       (frame (put-assoc-equal src
                               (change-frame-val (cdr (assoc-equal src frame))
                                                 :dir new-src-dir)
                               frame))
       ;; Check somewhere that (car (last pathname)) is not already present...
       (new-var (abs-put-assoc (car (last pathname))
                               (make-abs-file :contents nil)
                               var))
       (frame (frame-with-root (frame->root frame)
                               (cons (cons new-index
                                           (frame-val (butlast pathname 1)
                                                      new-var src))
                                     (frame->frame frame)))))
    (mv frame -1 error-code)))

;; (thm
;;  (implies
;;   (and
;;    (frame-reps-fs frame fs))
;;   (frame-reps-fs
;;    (mv-nth 0 (abs-mkdir frame pathname))
;;    (mv-nth 0 (hifat-mkdir frame pathname))))
;;  :hints (("Goal" :in-theory (enable abs-mkdir hifat-mkdir))))
