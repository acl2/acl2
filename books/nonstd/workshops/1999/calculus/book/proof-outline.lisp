;;; Outline tool
;;; Matt Kaufmann
;;; June, 2000 (adapted from 1999 version, which was not a certifable book).
;;; Example usage:
;;; (display-proof-outline-all "outline/outline" "fundamental-theorem-of-calculus")
;;; Send email to kaufmann@cs.utexas.edu to request further documentation.
;;; This tool is described in "Computer-Aided Reasoning:  ACL2 Case Studies",
;;; Kluwer Academic Publishers, June, 2000.

(in-package "ACL2")

(program)

(set-state-ok t)

; Next we include a book to define constant *dep-tree*.
(include-book
; This linebreak eliminates a generated dependency on tree.lisp, which is a
; generated file.  Instead, we add that dependency explicitly where needed.
 "tree")

(defconst *top-lemma* "main")
(defconst *separator* "==============================")

; In the following, acc is always closed downward.
(defun deps-aux (filename deps all-deps acc)
  (if (endp deps)
      acc
    (deps-aux filename
              (cdr deps)
              all-deps
              (if (and (equal (caar deps) filename)
                       (not (member-equal (cdar deps) acc)))
                  (cons (cdar deps)
                        (deps-aux (cdar deps) all-deps all-deps acc))
                acc))))

(defmacro deps (filename &optional (deps 'nil deps-supplied-p))
  (if deps-supplied-p
      `(deps-aux ,filename ,deps ,deps nil)
    `(deps-aux ,filename *dep-tree* *dep-tree* nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Print summary of proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun last-form-in-file-aux (obj channel state)
  (mv-let (eofp obj2 state)
	  (read-object channel state)
	  (if eofp
	      (mv obj state)
	    (last-form-in-file-aux obj2 channel state))))

(defun last-form-in-file (fname state)
  (mv-let (channel state)
	  (open-input-channel (string-append fname ".lisp") :object state)
          (if channel
              (mv-let (result state)
                      (last-form-in-file-aux nil channel state)
                      (let ((state (close-input-channel channel state)))
                        (value result)))
            (er soft 'top-level
                "Unable to open file ~s0 for :object input."
                (string-append fname ".lisp")))))

; Return form if it is a defthm, else if form is an encapsulate apply the same
; routine to the last form in the encapsulate.  Return nil if no reasonable
; result can be computed.
(defun last-atomic-event-in-form (form)
  (cond
   ((or (atom form) (atom (cdr form)))
    nil)
   ((eq (car form) 'encapsulate)
    (last-atomic-event-in-form (car (last form))))
   ((member (car form) '(defthm defthm-std
                          ;; defun defun-std
                          ))
    form)))

; The following routine returns a defthm form if the last form in the file is a
; defthm (or an encapsulate whose last form is the desired defthm, etc.; see
; last-atomic-event-in-form).
(defun last-atomic-event-in-file (filename state)
  (er-let*
   ((last-form (last-form-in-file filename state)))
   (let ((form (last-atomic-event-in-form last-form)))
     (value (and form
                 (string-equal (symbol-name (cadr form)) filename)
                 (if (member (car form) '(defthm defthm-std))
                     (caddr form)
                   form))))))

(defun proof-alist-aux (files state)
  (if (endp files)
      (value nil)
    (let* ((file (car files)))
      (er-let*
       ((theorem (last-atomic-event-in-file file state))
        (alist (proof-alist-aux (cdr files) state)))
       (if theorem
           (value (cons (cons file theorem) alist))
         (value alist))))))

; The following returns an alist associating lemma books (without .lisp
; extensions) with their corresponding defthm or defthm-std events, for all
; lemma books in support of top-file (including top-file).
(defun proof-alist (top-file dep-tree state)
  (proof-alist-aux (cons top-file (deps top-file dep-tree)) state))

(defun get-lemmas (name dep-tree)
  (cond
   ((endp dep-tree)
    nil)
   ((equal (caar dep-tree) name)
    (cons (cdar dep-tree)
          (get-lemmas name (cdr dep-tree))))
   (t
    (get-lemmas name (cdr dep-tree)))))

(defun dec (n)
  (and n (1- n)))

(defun valid-keys (keys alist)
  (cond
   ((endp keys)
    nil)
   ((assoc-equal (car keys) alist)
    (cons (car keys)
          (valid-keys (cdr keys) alist)))
   (t
    (valid-keys (cdr keys) alist))))

; Just like fms, but without initial newline or evisc-tuple:
(defun my-fms (str alist chan state)
  (mv-let
   (col state)
   (fmt1 str alist 0 chan state nil)
   (declare (ignore col))
   state))

; Returns the immediate sublemmas.
(defun display-proof-step (triple prefix proof-alist truncatedp channel state)
  (let* ((name (car triple))
         (theorem (cadr triple))
         (lemmas (caddr triple))
         (lemma-books (valid-keys lemmas proof-alist))
         (library-books
          ;; The call of reverse below is only there to make the result line up
          ;; with what is reported in "Computer-Aided Reasoning:  ACL2 Case
          ;; Studies."
          (reverse (set-difference-equal lemmas lemma-books)))
         (trunc-string
          (if (and lemma-books truncatedp)
              " (NOT shown just below:  depth limit reached)"
            "")))
    (pprogn
     (my-fms "~s0.  ~s1.~% ~q2"
             (list (cons #\0 prefix) (cons #\1 name) (cons #\2 theorem))
             channel state)
     (if lemma-books
         (my-fms "using lemmas~s0:~%  ~q1"
                 (list (cons #\0 trunc-string) (cons #\1 lemma-books))
                 channel state)
       state)
     (if library-books
         (my-fms "~s0 library books:~%  ~q1"
                 (list (cons #\0 (if lemma-books "and" "using"))
                       (cons #\1 library-books))
                 channel state)
       state)
     (princ$ *separator* channel state)
     (newline channel state)
     (value lemma-books))))

(defun display-proof-step-short (name old-prefix prefix channel state)
  (pprogn
   (my-fms "~s0.  ~s1.~%" (list (cons #\0 prefix) (cons #\1 name)) channel state)
   (my-fms " <See ~s0 for details.>~%" (list (cons #\0 old-prefix)) channel state)
   (princ$ *separator* channel state)
   (newline channel state)))

(mutual-recursion

; Here acc is an alist associating lemmas already printed with their
; names.  This function returns the new alist associating lemmas
; printed with their names.
(defun display-proof-outline-rec (depth lemma prefix proof-alist channel acc state)
  (let* ((pair (assoc-equal lemma proof-alist))
         (triple (list (car pair)
                       (cdr pair)
                       (get-lemmas (car pair) *dep-tree*))))
    (er-let*
     ((sublemmas
       (display-proof-step triple prefix proof-alist (eql depth 1) channel state)))
     (cond
      ((int= depth 1)
       (value (cons (cons lemma prefix) acc)))
      (t
       (display-proof-outline-rec-list (dec depth) sublemmas prefix 1 proof-alist channel
                                       (cons (cons lemma prefix) acc)
                                       state))))))

(defun display-proof-outline-rec-list (depth lemmas prefix counter proof-alist
                                             channel acc state)
  (let ((local-prefix (concatenate 'string prefix "."
                                   (coerce (explode-atom counter 10) 'string))))
    (if (endp lemmas)
        (value acc)
      (let ((temp (assoc-equal (car lemmas) acc)))
        (if temp
            (pprogn
             (display-proof-step-short (car lemmas) (cdr temp) local-prefix
                                       channel state)
             (display-proof-outline-rec-list depth (cdr lemmas) prefix
                                             (1+ counter) proof-alist channel
                                             acc state))
          (er-let* ((new-acc (display-proof-outline-rec depth (car lemmas) local-prefix
                                                        proof-alist channel acc state)))
                   (display-proof-outline-rec-list
                    depth (cdr lemmas) prefix (1+ counter) proof-alist channel
                    new-acc state)))))))

)


(defun display-proof-outline (filename depth top-file dep-tree proof-alist state)
  (pprogn
   (fms "Printing depth ~x0..." (list (cons #\0 depth))
        *standard-co* state nil)
   (er-let*
    ((proof-alist (if proof-alist
                      (value proof-alist)
                    (proof-alist top-file dep-tree state))))
    (let ((filename
           (if (and filename depth)
               (symbol-name (packn (list filename "." depth)))
             filename)))
      (mv-let (channel state)
              (open-output-channel filename :character state)
              (if channel
                  (er-let*
                   ((new-lemmas-alist
                     (display-proof-outline-rec depth top-file "Main" proof-alist
                                                channel nil state)))
                   (pprogn (close-output-channel channel state)
                           (princ$ " done." *standard-co* state)
                           (value new-lemmas-alist)))
                (er soft 'display-proof-outline
                    "Unable to open file ~s0 for output."
                    filename)))))))

; Run display-proof-outline for all depths of at least 2.
(defun display-proof-outline-all-aux (filename n top-lemma dep-tree
                                               lemmas-alist proof-alist state)
  (er-let* ((proof-alist
             (if proof-alist
                 (value proof-alist)
               (proof-alist top-lemma dep-tree state)))
            (new-lemmas-alist
             (display-proof-outline filename n top-lemma dep-tree proof-alist state)))
           (if (int= (length lemmas-alist) (length new-lemmas-alist))
               (pprogn
                (newline *standard-co* state)
                (value :invisible))
             (display-proof-outline-all-aux filename (1+ n) top-lemma dep-tree
                                            new-lemmas-alist proof-alist state))))

(defmacro display-proof-outline-all (filename &optional
                                              (top-lemma 'nil top-lemma-p)
                                              (dep-tree 'nil dep-tree-p))
  `(display-proof-outline-all-aux
    ,filename 1
    ',(if top-lemma-p top-lemma *top-lemma*)
    ',(if dep-tree-p dep-tree *dep-tree*)
    nil
    nil
    state))
