; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date February, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Description:

; This file formerly connected xdoc with David Russinoff's online rtl manual.
; That manual has been replaced by a book, "Formal Verification of
; Floating-Point Hardware Design: A Mathematical Approach" by
; David M. Russinoff, at:
; https://www.springer.com/us/book/9783319955124

(in-package "RTL")

(defconst *rtl-node-tree*

; Nodes from mousing over topics at (the now defunct)
; http://russinoff.com/libman/top.html, with spaces replaced by underscores and
; commas deleted.  These are organized to match the hierarchy on that page.

; We use "/" rather than ":" as a separator so that ACL2-Doc can include the
; node, since ACL2-Doc ignores names that ACL2 prints using vertical bars.
; Also, Jared Davis points out that the std libraries use "/" as a separator,
; so we follow that convention.

  '((|Register-Transfer Logic|
     (|Basic Arithmetic Functions| ; basic.lisp
      |Floor and Ceiling|
      |Modulus|
      |Chop|)
     (|Bit Vectors| ; bits.lisp
      |Recognizing Bit Vectors|
      |Bit Slices|
      |Bit Extraction|
      |Concatenation|
      |Signed Integer Formats|)
     (|Logical Operations| ; log.lisp
      |Binary Operations|
      |Complementation|
      |Algebraic Properties|))
    (|Floating-Point Arithmetic|
     (|Floating-Point Numbers| ; float.lisp
      |Floating-Point Decomposition|
      |Exactness|)
     (|Floating-Point Formats| ; reps.lisp
       |Classification of Formats|
       |Normal Encodings|
       |Denormals and Zeroes|
       |Infinities and NaNs|
       |Rebiasing Exponents|)
     (|Rounding| ; round.lisp
      |Truncation|
      |Rounding Away from Zero|
      |Unbiased Rounding|
      |Odd Rounding|
      |IEEE Rounding|
      |Denormal Rounding|))
    (|Floating-Point Exceptions and Specification of Elementary Arithmetic Instructions| ; exps.lisp
     (|IEEE-Compliant Square Root| ; sqrt.lisp
      |Truncated Square Root|
      |Odd-Rounded Square Root|
      |IEEE-Rounded Square Root|)
      |SSE Floating-Point Instructions|
      |x87 Instructions|
      |ARM AArch32 Floating-Point Instructions|
      ;; |ARM AArch64 Floating-Point Instructions|
     )
   (|Implementation of Elementary Operations|
    (|Addition| ; add.lisp
     |Bit Vector Addition|
     |Leading One Prediction|
     |Trailing One Prediction|)
    (|Multiplication| ; mult.lisp
     |Radix-4 Booth Encoding|
     |Statically Encoded Multiplier Arrays|
     |Encoding Redundant Representations|
     |Radix-8 Booth Encoding|)
    (|FMA-Based Division| ; div.lisp
     |Quotient Refinement|
     |Reciprocal Refinement|
     |Examples|)
    (|SRT Division and Square Root| ; srt.lisp
     |SRT Division and Quotient Digit Selection|
     |SRT Square Root Extraction|))
   |Modeling Algorithms in C++ and ACL2| ; rac.lisp
   |Bibliography|))

(defun rtl-node-name-basic (sym)
  sym)

(defun rtl-node-alist1 (sym global-index)
  (list sym
        (rtl-node-name-basic sym)
        (concatenate 'string
                     "http://russinoff.com/libman/text/node"
                     (coerce (explode-nonnegative-integer
                              global-index 10 nil)
                             'string)
                     ".html")))

(defun rtl-node-alist (flg tree global-index)

; Return a list of entries (original-name doc-topic-name url).  Flg is nil for
; a single tree, t for a list of trees.

  (declare (xargs :mode :program))
  (cond (flg ; list of child trees
         (assert$
          (true-listp tree)
          (cond ((atom tree) nil)
                (t (let* ((alist (rtl-node-alist nil (car tree) global-index))
                          (len-alist (length alist)))
                     (append alist
                             (rtl-node-alist t
                                             (cdr tree)
                                             (+ global-index len-alist))))))))
        ((atom tree)
         (assert$
          (symbolp tree)
          (list (rtl-node-alist1 tree global-index))))
        (t (assert$
            (and (true-listp tree)
                 tree
                 (symbolp (car tree)))
            (cons (rtl-node-alist1 (car tree) global-index)
                  (rtl-node-alist t
                                  (cdr tree)
                                  (1+ global-index)))))))

(defconst *rtl-node-alist*
  (rtl-node-alist t *rtl-node-tree* 4))

(defun defsection-rtl-defs1 (events acc)
  (declare (xargs :mode :program))
  (cond ((endp events) (reverse acc))
        (t (defsection-rtl-defs1
             (cdr events)
             (let ((ev (car events)))
               (case-match ev
                 ((& name . &)

; Based on the definition of formula-info-to-defs1 from xdoc/top.lisp.

                  (cond ((symbolp name)
                         (cons (concatenate 'string
                                            "@(def "
                                            (xdoc::full-escape-symbol name)
                                            ")")
                               acc))
                        (t acc)))
                 (& acc)))))))

(defun defsection-rtl-defs (events)
  (declare (xargs :mode :program))
  (cond ((endp events) "")
        (t (concatenate
            'string

; Based on formula-info-to-defs in xdoc/top.lisp:

            "<h3>Definitions and Theorems</h3>"
            (string-append-lst (defsection-rtl-defs1 events nil))))))

(defun rtl-node-entry (name)
  (or (assoc-eq name *rtl-node-alist*)
      (er hard 'defsection-rtl
          "Unknown rtl node name, ~x0"
          name)))

(defmacro defsection-rtl (name parent &rest events)
  (let* ((entry (rtl-node-entry name))
         (section-name (cadr entry))
         ;; (url (caddr entry)) ; no longer used
         )
    `(defsection ,section-name
       :parents (,(if (eq parent 'rtl) 'rtl (cadr (rtl-node-entry parent))))
       :short ,(symbol-name name)
       :long ,(defsection-rtl-defs events)
       (deflabel ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "$SECTION")
                   name))
       ,@events)))

(defun rtl-node-name (name)
  (cond ((eq name 'rtl) name)
        ((consp name)
         (rtl-node-name (car name)))
        (t (cadr (rtl-node-entry name)))))

(defun rtl-node-name-lst (trees)
  (cond ((endp trees) nil)
        (t (cons (rtl-node-name (car trees))
                 (rtl-node-name-lst (cdr trees))))))

(defmacro rtl-order-subtopics (parent children)
  `(xdoc::order-subtopics ,(rtl-node-name parent)
                          ,(rtl-node-name-lst children)))

(defxdoc rtl
  :parents (acl2::bit-vectors acl2::hardware-verification)
  :short "A library of register-transfer logic and computer arithmetic"
  :long "<p>This @(see documentation) is based on the directory @('rtl') of the
  ACL2 @(see community-books).  For a more thorough treatment, see <a
  href='https://www.springer.com/us/book/9783319955124'>\"Formal Verification
  of Floating-Point Hardware Design: A Mathematical Approach\"</a> by David
  M. Russinoff.  See file @('rtl/README') for additional information about this
  library and its connection to this book.</p>")

(rtl-order-subtopics rtl (|Register-Transfer Logic|
                          |Floating-Point Arithmetic|
                          |Floating-Point Exceptions and Specification of Elementary Arithmetic Instructions|
                          |Implementation of Elementary Operations|
                          |Modeling Algorithms in C++ and ACL2|
                          |Bibliography|))

(defun defsection-rtl-list-for-tree (parent trees)

; Trees is a tail of the children of parent in *rtl-node-tree*.

  (declare (xargs :mode :program))
  (cond ((endp trees) nil)
        ((atom (car trees))

; Then defsection-rtl will be given explicitly for each tree in trees.

         nil)
        (t ; (car trees) is (topic . children)
         (list* `(defsection-rtl ,(caar trees) ,parent)
                `(rtl-order-subtopics ,(caar trees) ,(cdar trees))
                (append (defsection-rtl-list-for-tree (caar trees) (cdar trees))
                        (defsection-rtl-list-for-tree parent (cdr trees)))))))

(defmacro defsection-rtl-list ()
  (cons 'progn (defsection-rtl-list-for-tree 'rtl *rtl-node-tree*)))

(defsection-rtl-list)

; Handle top-level leaves:

(defsection-rtl |Bibliography| rtl)
(defsection-rtl |Modeling Algorithms in C++ and ACL2| rtl)
