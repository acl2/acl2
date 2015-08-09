(in-package "ACL2")

(include-book "seqs")

;; To find whether the character is parsimony informative:
;; Iterate through the sequences.  Keep a hash table containing states we've
;; seen.  If we come across a state we've seen before, set first-big-state to
;; that state (originally should be nil.)  If we come across a different state
;; we've seen before, return t.  If we get through all the sequences and
;; there's at most one "big state", return nil.

(defun parsimony-informative-helper
  (seqs i state-hash missingGapChars first-big-state)
  (declare (xargs :guard (and (natp i)
                              (if (consp seqs)
                                  (and (valid-sequences-same-length seqs)
                                       (< i (- (len (car seqs)) 1)))
                                t))))
  (if (atom seqs)
      nil
    (let* ((curr-state (nth-gen i (cdar seqs)))
           (seen (het curr-state state-hash)))
      (if (and seen
               (not (member-gen curr-state missingGapChars)))
          (if (and first-big-state
                   (not (equal first-big-state curr-state)))
              t
            (parsimony-informative-helper (cdr seqs) i
                                          state-hash missingGapChars
                                          curr-state))
        (parsimony-informative-helper (cdr seqs) i
                                      (hut curr-state t state-hash)
                                      missingGapChars
                                      first-big-state)))))

(defun parsimony-informative? (i seqs missingGapChars)
  (declare (xargs :guard (and (natp i)
                              (valid-sequences-same-length seqs)
                              (if (consp seqs)
                                  (< i (- (len (car seqs)) 1))
                                t))))
  (parsimony-informative-helper seqs i 'parsimony-informative-hash
                                missingGapChars nil ))

(defun number-pis-helper (seqs curPos curNum missingGapChars)
  (declare (xargs :guard (and (valid-sequences-same-length seqs)
                              (natp curPos)
                              (if (consp seqs)
                                  (< curPos (len (cdar seqs)))
                                t)
                              (natp curNum))))
  (if (zp curPos)
      (if (equal curPos 0)
          (if (parsimony-informative? curPos seqs missingGapChars)
              (+ 1 curNum)
            curNum)
        curNum)
    (if (parsimony-informative? curPos seqs missingGapChars)
        (number-pis-helper seqs (- curPos 1) (+ 1 curNum) missingGapChars)
      (number-pis-helper seqs (- curPos 1) curNum missingGapChars))))

(defun number-of-p-informative-sites (seqs missingGapChars)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the number of sites that are parsimony informative~/
;  ~/
;  Arguments:
;    (1) seqs - a set of sequences
;    (2) missingGapChars - a list of characters indicating gaps or
;                          missing characters

;  Details: Checks that sequences are valid before counting number
;           of parsimony informative sites."
  (declare (xargs :guard t))
  (if (valid-sequences-same-length seqs)
      (if (and (consp seqs)
               (consp (cdar seqs)))
          (number-pis-helper seqs (- (len (cdar seqs)) 1) 0 missingGapChars)
        0)
    "Error: Need valid sequences in number-of-p-informative-sites"))

#||
EXAMPLES:

(number-of-p-informative-sites
 (build-fast-alist-from-alist
  '((1 a c t g - a)  ; Taxon . Sequence
    (2 g g - g g g)
    (3 t - c t g g)
    (4 g g g - a a)
    (5 c c t - a t)))
 '(- ?))

||#
