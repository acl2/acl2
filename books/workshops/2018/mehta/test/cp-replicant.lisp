(include-book "../file-system-m2")

(defun
    get-dir-ent-contents
    (fat32-in-memory dir-ent)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (b*
      ((first-cluster (dir-ent-first-cluster dir-ent))
       (file-size (dir-ent-file-size dir-ent)))
    (get-clusterchain-contents
     fat32-in-memory (fat32-entry-mask first-cluster) file-size)))

(defun get-dir-ent-matching-name
    (dir-contents str)
  (declare (xargs :verify-guards nil
                  :measure (len dir-contents)))
  (if
      (atom dir-contents)
      nil
    (let*
        ((dir-ent (take *ms-dir-ent-length* dir-contents)))
      (if
          (and
           (not (equal (nth 0 dir-ent) #xe5))
           (equal str (nats=>string (subseq dir-ent 0 11))))
          dir-ent
        (get-dir-ent-matching-name
         (nthcdr *ms-dir-ent-length* dir-contents)
         str)))))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (slurp-disk-image
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "CP_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "CP_INPUT" state))
     ((mv dir-clusterchain error-code)
      (get-clusterchain
       fat32-in-memory 2 2097152))
     ((unless (equal error-code 0))
       (mv fat32-in-memory state))
     (dir-contents
      (get-contents-from-clusterchain
       fat32-in-memory dir-clusterchain 2097152))
     ((mv contents error-code)
      (get-dir-ent-contents
       fat32-in-memory
       (get-dir-ent-matching-name
        dir-contents val)))
     (state
      (if
          (not (equal error-code 0))
          state
        (princ$
         (nats=>string
          contents)
         channel state)))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
