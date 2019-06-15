(include-book "../test-stuff")

;; See theorem compare-disks-correctness-1 in test-stuff.lisp for a proof of
;; correctness of this procedure.
(b*
    (((mv & image-path1 state)
      (getenv$ "REF_INPUT" state))
     ((mv & image-path2 state)
      (getenv$ "INPUT" state))
     ((mv equiv fat32-in-memory)
      (compare-disks image-path1 image-path2 fat32-in-memory state)))
  (mv (good-bye (if equiv 0 1)) fat32-in-memory state))
