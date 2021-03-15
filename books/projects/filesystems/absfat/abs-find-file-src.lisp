;  abs-find-file-src.lisp                               Mihir Mehta

; abs-find-file-src finds the variable, if any, that has a non-enoent value for
; finding the file.

(in-package "ACL2")

(include-book "abs-find-file")
(local (include-book "std/lists/prefixp" :dir :system))

(local
 (in-theory
  (e/d
   (abs-file-p-when-m1-regular-file-p len-when-consp)
   ((:definition member-equal)
    (:definition intersection-equal)
    (:definition integer-listp)
    (:rewrite true-listp-when-string-list)
    (:linear position-equal-ac-when-member)
    (:linear position-when-member)
    (:rewrite nth-when->=-n-len-l)
    (:linear len-of-remove-assoc-1)
    (:definition position-equal-ac)
    (:definition remove1-assoc-equal)
    (:rewrite m1-directory-file-p-correctness-1)
    (:rewrite assoc-of-car-when-member)
    (:rewrite integerp-of-car-when-integer-listp)
    (:linear len-when-hifat-bounded-file-alist-p . 1)
    (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
    (:rewrite natp-of-car-when-nat-listp)
    (:rewrite
     collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
    (:rewrite when-zp-src-of-1st-collapse-1)
    (:rewrite ctx-app-ok-of-abs-fs-fix-1)
    (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)
    (:rewrite hifat-file-alist-fix-guard-lemma-1)
    (:rewrite abs-file-alist-p-of-abs-file->contents)
    (:rewrite member-of-abs-fs-fix-when-natp)
    (:rewrite abs-find-file-helper-of-collapse-lemma-2)
    (:rewrite m1-file-alist-p-of-intersection-equal-2)
    (:rewrite absfat-subsetp-transitivity-lemma-5)
    (:rewrite
     abs-separate-of-frame->frame-of-collapse-this-lemma-7)
    (:linear 1st-complete-correctness-2)
    different-from-own-src-1
    (:rewrite m1-file-alist-p-when-subsetp-equal)
    (:rewrite stringp-when-nonempty-stringp)
    m1-file-alist-p-of-nthcdr
    take-of-len-free take-of-too-many
    len-of-remove-assoc-2 nth-of-take
    no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-3
    hifat-no-dups-p-of-m1-file-contents-of-cdar
    abs-find-file-correctness-1-lemma-18
    (:rewrite abs-complete-when-stringp)
    (:rewrite hifat-place-file-correctness-3)
    (:rewrite
     fat32-filename-list-p-of-cdr-when-fat32-filename-list-p)
    (:rewrite
     collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-9)))))

;; This deliberately follows an almost-identical induction scheme to
;; abs-find-file. It was going to be a part of that function, but that just led
;; to too many failures.
(defund
  abs-find-file-src (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))))
  (b*
      (((when (atom frame)) 0)
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         path))
        (abs-find-file-src (cdr frame) path))
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 path)))
       ((when (not (equal error-code *enoent*)))
        (mbe :exec (caar frame) :logic (nfix (caar frame)))))
    (abs-find-file-src (cdr frame) path)))

(defthmd
  abs-find-file-src-correctness-2
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (not (equal (mv-nth 1 (abs-find-file frame path))
                    *enoent*)))
   (and
    (consp (assoc-equal (abs-find-file-src frame path)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame)))
             (fat32-filename-list-fix path))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
      (nthcdr
       (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                               frame))))
       path))
     (abs-find-file frame path))))
  :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (not (equal (mv-nth 1 (abs-find-file frame path))
                      *enoent*)))
     (and
      (prefixp
       (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
       (fat32-filename-list-fix path))
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                             frame))))
         path))
       (abs-find-file frame path)))))
   (:linear
    :corollary
    (implies
     (and (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (not (equal (mv-nth 1 (abs-find-file frame path))
                      *enoent*)))
     (< (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame))))
        (len path)))
    :hints (("goal" :in-theory (enable abs-find-file-helper)
             :do-not-induct t)))))

(encapsulate ()

  (local
   (defthm
     lemma
     (implies (not (zp (abs-find-file-src frame path)))
              (consp (assoc-equal (abs-find-file-src frame path)
                                  frame)))
     :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))))

  (defthm
    abs-find-file-src-correctness-1
    (implies (consp (assoc-equal 0 frame))
             (consp (assoc-equal (abs-find-file-src frame path)
                                 frame)))
    :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (or (not (zp (abs-find-file-src frame path)))
                   (consp (assoc-equal 0 frame))
                   (and (frame-p frame)
                        (no-duplicatesp-equal (strip-cars frame))
                        (not (equal (mv-nth 1 (abs-find-file frame path))
                                    *enoent*))))
               (consp (assoc-equal (abs-find-file-src frame path)
                                   frame)))
      :hints
      (("goal"
        :use
        abs-find-file-src-correctness-2))))))

(defthmd
  abs-find-file-src-of-fat32-filename-list-fix
  (equal
   (abs-find-file-src frame (fat32-filename-list-fix path))
   (abs-find-file-src frame path))
  :hints (("Goal" :in-theory (enable abs-find-file-src))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-src frame path)
  2
  :hints
  (("goal"
    :use
    ((:instance abs-find-file-src-of-fat32-filename-list-fix
                (path path-equiv))
     abs-find-file-src-of-fat32-filename-list-fix))))

(defthm
  abs-find-file-src-of-frame-with-root
  (equal (abs-find-file-src (frame-with-root root frame)
                            path)
         (if (equal (mv-nth 1 (abs-find-file-helper root path))
                    2)
             (abs-find-file-src frame path)
             0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-find-file-src frame-with-root))))
