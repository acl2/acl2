(defun do-thing1 (n m x86)
  (declare (xargs :stobjs (x86)
                  :mode :program))
  (b* (((when (or (equal n m)
                  (ms x86)
                  (fault x86))) (mv m x86))
       (x86 (x86-fetch-decode-execute x86)))
      (do-thing1 n (1+ m) x86)))

(defun do-thing (n x86)
  (declare (xargs :stobjs (x86)
                  :mode :program))
  (do-thing1 n 0 x86))

(restore-x86 "x86-state.bak" x86)

(do-thing 8165050 x86)
