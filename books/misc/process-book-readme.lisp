; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (dates back to Feb., 2006 or earlier)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(set-state-ok t)

(defun next-newline (str pos len)

; Return the position of the next newline character in str starting with pos,
; if any; else return len.

  (cond ((int= pos len)
         len)
        ((eql (char str pos) #\Newline)
         pos)
        (t (next-newline str (1+ pos) len))))

(defun break-string-into-lines-rec (str pos len acc)

; Break str into lines, discarding empty lines.

  (cond ((int= pos len)
         (reverse acc))
        ((eql (char str pos) #\Newline)
         (break-string-into-lines-rec str (1+ pos) len acc))
        (t (let ((new-pos (next-newline str pos len)))
             (break-string-into-lines-rec str new-pos len
                                          (cons (subseq str pos new-pos)
                                                acc))))))

(defun find-whitespace-string (string-list)
  (cond ((endp string-list)
         nil)
        ((let* ((str (car string-list))
                (len (length str)))
           (or (member-char-stringp #\Space str (1- len))
               (member-char-stringp #\Tab str (1- len))))
         (car string-list))
        (t (find-whitespace-string (cdr string-list)))))

(defun break-string-into-lines (str msg ctx state)
  (let* ((lines (break-string-into-lines-rec str 0 (length str) nil))
         (bad-line (find-whitespace-string lines)))
    (cond (bad-line (er soft ctx
                        "Found ~@0 line with whitespace:~%~x1~|"
                        msg
                        bad-line))
          (t (value lines)))))

(defun process-book-readme-fn (readme-filename state)
  (declare (xargs :guard (stringp readme-filename)))
  (let ((ctx 'process-book-readme))
    (mv-let
     (channel state)
     (open-input-channel readme-filename :object state)
     (cond
      ((null channel)
       (er soft ctx
           "Unable to open file ~x0 for input."
           readme-filename))
      (t (mv-let
          (eofp alist state)
          (read-object channel state)
          (pprogn
           (close-input-channel channel state)
           (cond (eofp (er soft ctx
                           "No form could be read from input file ~x0."
                           readme-filename))
                 ((not (and (true-list-listp alist)
                            (alistp (strip-cdrs alist))))
                  (er soft ctx
                      "The form read from a book's Readme.lsp file should be ~
                       an list of true lists each with at least two elements, ~
                       but ~X01 is not."
                      alist (abbrev-evisc-tuple state)))
                 (t (let* ((files-entry    (assoc-eq :FILES alist))
                           (title-entry    (assoc-eq :TITLE alist))
                           (author/s-entry (assoc-eq :AUTHOR/S alist))
                           (keywords-entry (assoc-eq :KEYWORDS alist))
                           (abstract-entry (assoc-eq :ABSTRACT alist))
                           (perm-entry     (assoc-eq :PERMISSION alist))
                           (files    (and (true-listp files-entry)
                                          (eql (length files-entry) 2)
                                          (stringp (cadr files-entry))
                                          (cadr files-entry)))
                           (title    (and (true-listp title-entry)
                                          (eql (length title-entry) 2)
                                          (stringp (cadr title-entry))
                                          (cadr title-entry)))
                           (author/s (and (string-listp (cdr author/s-entry))
                                          (cdr author/s-entry)))
                           (keywords (and (string-listp (cdr keywords-entry))
                                          (cdr keywords-entry)))
                           (abstract (and (true-listp abstract-entry)
                                          (eql (length abstract-entry) 2)
                                          (stringp (cadr abstract-entry))
                                          (cadr abstract-entry)))
                           (perm     (and (true-listp perm-entry)
                                          (eql (length perm-entry) 2)
                                          (stringp (cadr perm-entry))
                                          (cadr perm-entry))))
                      (cond
                       ((not (and files title author/s keywords abstract perm))
                        (er soft ctx
                            "No valid field for ~x0 in Readme.lsp alist."
                            (cond
                             ((not files) :FILES)
                             ((not title) :TITLE)
                             ((not author/s) :AUTHOR/S)
                             ((not keywords) :KEYWORDS)
                             ((not abstract) :ABSTRACT)
                             (t :PERMISSION))))
                       (t
                        (pprogn (fms "File ~s0 PASSES the check.~|"
                                     (list (cons #\0 readme-filename))
                                     (standard-co state) state nil)
                                (value :invisible))))))))))))))

(defmacro process-book-readme (&key dir)
  (declare (xargs :guard (or (null dir)
                             (stringp dir))))
  `(process-book-readme-fn
    (concatenate
     'string
     (let ((dir ,dir))
       (cond (dir
              (cond ((eql (char dir (1- (length dir)))
                          *directory-separator*)
                     dir)
                    (t (concatenate 'string dir
                                    *directory-separator-string*))))
             (t (cbd))))
     "Readme.lsp")
    state))

; Last updated: Fri Feb 24 11:36:55 2006

