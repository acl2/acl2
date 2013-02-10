(in-package "ACL2")

(set-raw-mode-on!)

; NEWICK PARSING

; Here's a Common Lisp parser for Newick expressions conforming to
; http://evolution.genetics.washington.edu/phylip/newicktree.html and
; the last pages of: "NEXUS: An Extensible File Format for Systematic
; Information," David R. Maddison; David L. Swofford; Wayne
; P. Maddison Systematic Biology, Vol. 46, No. 4. (Dec., 1997),
; pp. 590-621.

; Onto *NEWICK-INTERIOR-NODE-ALIST* we accumulate conses that pair
; names to interior nodes of the Newick expression currently being
; read.
(defg *newick-interior-node-alist* nil)

; *NEWICK-IGNORE-BRANCH-LENGTHS* determines whether a branch length is
; to be attached to Newick expression (by consing the expression onto
; the branch length), or simply ignored.
(defg *newick-ignore-branch-lengths* nil)

; *NEWICK-STR* an adjustable one-dimensional array of characters into
; which we accumulate the characters of a token as it is read.
(defg *newick-str*
  (make-array 60 :element-type 'character :adjustable t
              :fill-pointer 0))
(declaim (type (array character (*)) *newick-str*))

(defun newick-digit (c)

; NEWICK-DIGIT returns, for a character, the value of the character as
; a decimal digit, if it is a decimal digit, and otherwise returns
; NIL.

  (declare (character c))
  (case c (#\0 0) (#\1 1) (#\2 2)
        (#\3 3) (#\4 4) (#\5 5) (#\6 6)
        (#\7 7) (#\8 8) (#\9 9)))

(defmacro newick-ordinary-mac ()
  `(case c
     ,@(loop for c in (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'list)
             collect (list (list c (char-downcase c)) c))
     ,@(loop for c in (coerce "0123456789.<>~!@#$%^&|?" 'list)
             collect (list c c))
     (#\_ #\Space)))

(defun newick-ordinary (c)

; NEWICK-ORDINARY returns a non-NIL value on the characters that may
; occur in tokens outside of single quotes.  For a lowercase
; character, the corresponding uppercase character is returned.  For
; the underscore character, the space character is returned.
; Otherwise, the character itself is returned.

  (declare (character c))
  (newick-ordinary-mac))

(defmacro newick-white-mac ()
  `(case c
     ((#\Space #\Newline #\Tab
       ,(code-char 0) ,(code-char 1) ,(code-char 2)
       ,(code-char 3) ,(code-char 4) ,(code-char 5)
       ,(code-char 6)
       ,(code-char 12) ; CNTL-L
       ,(code-char 13) ; CNTL-M
       )
     t)))

(defun newick-white-p (c)

; NEWICK-WHITE-P returns non-NIL on characters that are white.

  (declare (character c))
  (newick-white-mac))

(defun newick-special-p (c)

; NEWICK-SPECIAL-P returns non-NIL on the five punctuation characters
; for Newick expressions.

  (case c ((#\, #\( #\) #\: #\;) t)))

(defun newick-illegal (x) (ofe "Illegal:  ~s" x))

(defun newick-consume-comment ()

; When NEWICK-CONSUME-COMMENT is called, an open square bracket must
; have just been read.  NEWICK-CONSUME-COMMENT reads forward up to and
; including the balancing close square bracket.

  (let ((n 1))
    (declare (fixnum n))
    (loop (let ((ch (read-char nil t nil t)))
            (declare (character ch))
            (cond ((eql ch #\[) (safe-incf n 1 newick-consume-comment))
                  ((eql ch #\])
                   (when (eql n 1) (return))
                   (setq n (the fixnum (1- n)))))))))

(defun newick-read-token ()

; If the next not-commented-out, non-white character is "special", we
; return it.  Otherwise, we return a symbol, which represents a token.

  (let ((p (read-char nil t nil t)) x)
    (declare (character p))
    (cond ((newick-white-p p) (newick-read-token))
          ((newick-special-p p) p)
          ((setq x (newick-ordinary p))
           (let ((s *newick-str*) (a *acl2-package*))
             (setf (fill-pointer s) 0)
             (vector-push (the character x) s)
             (loop
              (setq p (read-char nil t nil t))
              (cond ((setq x (newick-ordinary p))
                     (vector-push-extend (the character x) s))
                    ((eql p #\[) (newick-consume-comment))
                    (t (unread-char p) (return))))
             (or (find-symbol s a) (values (intern (copy-seq s) a)))))
          ((eql p #\[) (newick-consume-comment) (newick-read-token))
          ((eql p #\')
           (let ((c (read-char nil t nil t))
                 (flg nil) (s *newick-str*) (a *acl2-package*))
             (setf (fill-pointer s) 0)
             (loop
              (when (eql c #\')
                (cond ((eql #\' (peek-char nil nil t nil t))
                       (read-char nil t nil t))
                      (t (return))))
              (when (newick-ordinary c) (setq flg t))
              (vector-push-extend (char-upcase c) s)
              (setq c (read-char nil t nil t)))
             (unless flg
               (ofe "Newick-read-token: A Newick name ~
                     may not consist entirely of whitespace and ~
                     punctuation, ~%as does: ~s." s))
             (or (find-symbol s a) (values (intern (copy-seq s) a)))))
          (t (newick-illegal p)))))

(defun newick-read-branch-length ()
; P is the most recently read character.
; X is the digit value of P, if P is a digit; otherwise X is NIL.
; PAST-DOT, when non-NIL, is the number of digits we have read after a
;    decimal point and before any e or E.
; POS is T iff we have read an initial plus sign.
; NEG is T iff we have read an initial minus sign.
; ANS is the accumulated, nonnegative coefficient value.
; PAST-E is T iff we have read an e or E.
; ENEG is T iff we have read an e or E followed by a minus sign.
; EANS is the accumulated, nonnegative. exponent value.

; branch-lengths are represented in the following somewhat strange
; way.  An integer represents itself.  A Common Lisp complex number
; #c(i j) represents (* i (expt 10 j)).

  (let* ((ans 0) (eans 0) p x past-dot past-e pos neg eneg
         (ig *newick-ignore-branch-lengths*))
    (flet ((gp ()
               (loop (setq p (read-char nil t nil t))
                     (unless (eql p #\[) (return))
                     (newick-consume-comment))
               (setq x (newick-digit p))))
      ;; 1. Get past leading spaces, comments
      (gp)
      (loop (if (or x (not (newick-white-p p)))
                (return)
              (gp)))
      ;; 1.5 Get past .+-.
      (loop (cond (x (return))
                  ((eql p #\-)
                   (when (or pos neg past-dot) (newick-illegal p))
                   (setq neg t))
                  ((eql p #\.)
                   (when past-dot (newick-illegal p))
                   (setq past-dot 0))
                  ((eql p #\+)
                   (when (or pos neg past-dot) (newick-illegal p))
                   (setq pos t))
                  (t (newick-illegal p)))
            (gp))
      ;; 2. consume all remaining characters.
      (loop
       (cond (x (cond (ig)
                      (past-e (setq eans (+ (* eans 10) x)))
                      (t (setq ans (+ (* ans 10) x)))))
             ((or (eql p #\e) (eql p #\E))
              (if past-e (newick-illegal p))
              (setq past-e t)
              (let ((c (peek-char nil nil t nil t)))
                (cond ((eql c #\+)
                       (read-char nil t nil t)
                       (setq c (peek-char nil nil t nil t)))
                      ((eql c #\-)
                       (setq eneg t)
                       (read-char nil t nil t)
                       (setq c (peek-char nil nil t nil t))))
                (cond ((newick-digit c))
                      (t (newick-illegal c)))))
             ((eql p #\.)
              (if (or past-dot past-e) (newick-illegal p))
              (setq past-dot -1))
             (t (unread-char p)
                (if (or ig (eql ans 0))
                    (return-from newick-read-branch-length 0))
                (if neg (setq ans (- ans)))
                (if eneg (setq eans (- eans)))
                (if past-dot (decf eans past-dot))
                (loop
                 (if (eql eans 0)
                     (return-from newick-read-branch-length ans))
                 (multiple-value-bind (q r) (floor ans 10)
                   (cond ((eql r 0)
                          (incf eans)
                          (setq ans q))
                         (t (return-from newick-read-branch-length
                              ;; next form could be replaced with
                              ;; (* ans (expt 10 eans))
                              (complex ans eans))))))))
       (if (and past-dot (not past-e) (not ig))
           (incf past-dot))
       (gp)))))

(defun newick-cleanup-help (p x)
  (cond ((eql p #\:)
         (let ((r (newick-read-branch-length)))
           (cond (*newick-ignore-branch-lengths* x)
                 (t (hl-hspace-hons-normed x r nil *default-hs*)))))
        ((eql p #\() (newick-illegal p))
        ((characterp p)
         (unread-char p)
         x)
        (t (newick-illegal p))))

(defun newick-cleanup (x)

; NEWICK-CLEANUP returns the interior node (subtree), X, possibly
; consed to the node's branch length.  Before reading a colon,
; followed by branch length, a name for X may be read; if so, a pair
; will be added to *NEWICK-INTERIOR-NODE-ALIST* associating the name
; with X.  The final comma, semicolon, or close paren is left unread.

  (let ((p (newick-read-token)))
    (cond
     ((and (consp x) (symbolp p))
      (when (assoc p *newick-interior-node-alist*)
        (ofe "Newick-cleanup:  An interior node ~
              name, such as ~s, may not be twice given a value." p))
      (push (cons p x) *newick-interior-node-alist*)
      (newick-cleanup-help (newick-read-token) x))
     (t (newick-cleanup-help p x)))))

(defun newick-read-list (flg)

; When NEWICK-READ-LIST is called, the open paren of a list has
; already been read.  We expect a comma, a close paren, or an element
; of the list.

; If FLG is NIL, an immediately encountered comma or close paren is to
; be read as a NIL, then as itself, helping us handle such Newick
; expressions such as (,(),(,),,).  If FLG is T, then an immediately
; encountered comma or close paren is simply to be skipped over.

; NOTE:  After calling NEWICK-READ-LIST, a call to NEWICK-CLEANUP
;        must be made.
  (let ((p (newick-read-token)))
    (cond
     ((null flg)
      (cond ((eql p #\)) (hl-hspace-hons-normed nil nil nil *default-hs*))
            ((eql p #\,) (hl-hspace-hons-normed nil (newick-read-list nil) nil *default-hs*))
            ((symbolp p) (hl-hspace-hons-normed (newick-cleanup p)
                                      (newick-read-list t) nil *default-hs*))
            ((eql p #\()
             (hl-hspace-hons-normed (newick-cleanup (newick-read-list nil))
                          (newick-read-list t) nil *default-hs*))
            (t (newick-illegal p))))
     ((eql p #\)) nil)
     ((eql p #\,)
      (setq p (newick-read-token))
      (cond ((symbolp p) (hl-hspace-hons-normed (newick-cleanup p)
                                      (newick-read-list t) nil *default-hs*))
            ((eql p #\()
             (hl-hspace-hons-normed (newick-cleanup (newick-read-list nil))
                          (newick-read-list t) nil *default-hs*))
            ((eql p #\,)
             (hl-hspace-hons-normed nil (newick-read-list nil) nil *default-hs*))
            ((eql p #\)) (hl-hspace-hons-normed nil nil nil *default-hs*))
            (t (newick-illegal p))))
      (t (newick-illegal p)))))

(defun newick-read-file-error-report (osi ch)

; When NEWICK-READ-FILE causes an error, we print its location, if
; feasible.

  (rotatef *standard-input* osi)
  (setq *newick-interior-node-alist* nil)
  (our-syntax
   (let* ((fp (file-position osi))
          (fl (and fp (file-length osi)))
          (p (and fp (max 0 (- fp 30))))
          (d (and fp (max 0 (- fp p))))
          (e *error-output*))
     (cond ((and fp (eql fp fl))
            (format e "~%; At end of file."))
           (fp (format e "~%; File position: ~s" fp)))
     (when (and fp (file-position osi p))
       (format e "~%; Last ~d chars read:" d)
       (loop for i below d do
             (write-char (read-char osi t nil t) e)))
     (if (characterp ch)
         (ofe "Newick-read-file.")
       (ofe "Newick-read-file:  Missing semicolon.")))))

; NEWICK-READ-FILE reads a file of Newick expressions.  Unless an
; error occurs, a proper list is returned each of whose elements is a
; cons or a string.  A string represents the contents of one line of
; the file encountered outside a Newick expression.  A cons has as its
; CAR a honsp+consp representing a Newick expression and as its CDR an
; alist pairing symbols with interior nodes of the expression.  If the
; first non-white, not-commented-out character on a line not within a
; Newick expression is not an open paren, the entire line is read as a
; string.

; The accumulation of strings depends upon the implementation of
; FILE-POSITION; if FILE-POSITION always returns NIL, strings are not
; accumulated at all.

(defun newick-read-file (file-name)
  (let ((osi *standard-input*)
        (ch nil))
    (with-open-file (*standard-input* file-name)
      (let ((si *standard-input*) st ans)
        (loop (setq st (file-position si))

; Set CH to next non-white, not-commented-out character.

              (loop
               (setq ch (read-char nil nil nil t))
               (cond ((null ch) ;; EOF.
                      (setq *newick-interior-node-alist* nil)
                      (return-from newick-read-file (nreverse ans)))
                     ((newick-white-p ch))
                     ((eql ch #\[) (newick-consume-comment))
                     (t (return))))

; If CH is an open paren, accumulate onto ANS one Newick expression;

              (cond
               ((eql #\( ch)
                (setq *newick-interior-node-alist* nil)
                (ignore-errors
                  (setq ch (newick-cleanup (newick-read-list nil))))
                (when (or (characterp ch)
                          (not (eql #\; (read-char nil nil nil t))))
                  (newick-read-file-error-report osi ch))
                (push (cons ch *newick-interior-node-alist*) ans))

; otherwise accumulate as strings the lines since ST was last set.

               (t (let ((e (and st (file-position si))))
                    (when (and e st (file-position si st))
                      (loop (push (read-line nil t nil t) ans)
                            (if (< e (file-position si))
                                (return))))))))))))
