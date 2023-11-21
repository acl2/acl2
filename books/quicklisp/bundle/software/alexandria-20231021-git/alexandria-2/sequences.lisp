(in-package :alexandria-2)


(defun subseq* (sequence start &optional end)
  "Like SUBSEQ, but limits END to the length."
  (subseq sequence start
          (if end
              (min end (length sequence)))))

