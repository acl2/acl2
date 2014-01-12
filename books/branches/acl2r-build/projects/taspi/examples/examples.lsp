;; Renamed from .lisp to .lsp by Jared, to follow Makefile convention of only
;; using .lisp for certifiable books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In addition to the examples given here, many files have
; examples given in comments at the end of the file. These
; examples are given here for ease of reference in doing
; i/o and computing consensus.  These operations are most 
; likely to be of general interest given the first papers
; describing TASPI.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../code/brlens/brlens")
(include-book "../sets-input/consensus")
(ld "../read-write/newick.lisp")
(ld "../read-write/write-trees.lisp")

;; An example of reading newick trees, and writing/reading compacted trees
;; Note that we know that the file indicated is simply a listing of trees with branch lengths
(let ((trees (remove-brlens-list (strip-cars (newick-read-file "tr64-ta500-brlns.nwk")))))
  (progn (compact-print-file trees "tr64-ta500.bhz")
	 (let ((bhz-trees (compact-read-file "tr64-ta500.bhz")))
	   (equal bhz-trees trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; An example of reading trees from a file, computing consensus, and writing newick result
(defun consensus-from-newick-file-no-brlens (file-name percentage)
  (let ((trees (strip-cars (newick-read-file file-name))))
    (compute-consensus trees
                       (mytips (car trees))
                       percentage)))

(defun consensus-from-to-newick-file-no-brlens (infile percentage outfile)
  (let ((trees (strip-cars (newick-read-file infile))))
    (with-open-file (str outfile :direction :output
                         :if-exists :supersede)
                    (print-newick 
                     str (compute-consensus 
                          trees
                          (mytips (car trees))
                          percentage)))))
 
(consensus-from-to-newick-file-no-brlens "tr30-ta328.nwk" 50 "tr30-ta328.50.nwk")
