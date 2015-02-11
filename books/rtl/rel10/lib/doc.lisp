; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date February, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Description:

; This file connects xdoc with David Russinoff's online rtl manual,
; http://russinoff.com/libman/index.html.

(in-package "ACL2")

(defconst *rtl-node-tree*

; Nodes from mousing over topics at http://russinoff.com/libman/top.html, with
; spaces replaced by underscores and commas deleted.  These are organized to
; match the hierarchy on that page.

; We use "/" rather than ":" as a separator so that ACL2-Doc can include the
; node, since ACL2-Doc ignores names that ACL2 prints using vertical bars.
; Also, Jared Davis points out that the std libraries use "/" as a separator,
; so we follow that convention.

  '((|Register-Transfer Logic|
     (|Basic Arithmetic Functions| ; basic.lisp
      |Floor and Ceiling|
      |Modulus|)
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
      |Representations with Explicit Leading One|
      |Representations with Implicit Leading One|
      |Denormal Representations|
      |Rebiasing Exponents|)
     (|Rounding| ; round.lisp
      |Truncation|
      |Rounding Away from Zero|
      |Unbiased Rounding|
      |Odd Rounding|
      |IEEE Rounding|
      |Denormal Rounding|))
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
      |SRT Square Root Extraction|
      |Square Root Seed Tables|)
     (|IEEE-Compliant Square Root| ; sqrt.lisp
      |Truncation {Square Root}|
      |Odd Rounding {Square Root}|
      |IEEE Rounding {Square Root}|))
    |Bibliography|))

; We use "/" rather than ":" as a separator so that ACL2-Doc can include the
; node, since ACL2-Doc ignores names that ACL2 prints using vertical bars.
; Also, Jared Davis points out that the std libraries use "/" as a separator,
; so we follow that convention.
(defun rtl-node-name-basic (sym)
  (intern$ (concatenate 'string "RTL/" (symbol-name sym))
           "ACL2"))

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
         (url (caddr entry)))
    `(defsection ,section-name
       :parents (,(if (eq parent 'rtl) 'rtl (cadr (rtl-node-entry parent))))
       :short ,(symbol-name name)
       :long ,(concatenate 'string
                           "<p>See also <a href='" url "'>"
                           "the corresponding section in David Russinoff's "
                           "online rtl manual</a>.</p>"
                           (defsection-rtl-defs events))
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
  :parents (arithmetic hardware-verification)
  :short "A library of register-transfer logic and computer arithmetic"
  :long "<p>This @(see documentation) for @(see community-books) residing under
  @('rtl/rel10') contains links to David Russinoff's online rtl manual, <i><a
  href='http://russinoff.com/libman/index.html'>A Formal Theory of
  Register-Transfer Logic and Computer Arithmetic</a></i>.  The organization of
  that manual is essentially isomorphic to the organization of the tree of
  documentation topics under this RTL topic.  Each leaf topic of that tree
  corresponds to a section of a book in the directory @('rtl/rel10/lib/').  The
  (leaf) topic for a section has two parts: (1) a link near the top of the page
  points to the corresponding page in the online rtl manual, which contains
  discussion and proofs written in mathematical English; and (2) the rest of
  the page displays definitions and theorems from that section.  Note that the
  books in @('rtl/rel10/lib/') contain additional definitions and theorems not
  documented here or in the rtl online manual.</p>

  <p>See file @('rtl/rel10/README') for additional information about this
  library.</p>")

(rtl-order-subtopics rtl (|Register-Transfer Logic|
                          |Floating-Point Arithmetic|
                          |Implementation of Elementary Operations|
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

; Handle top-level leaf:
(defsection-rtl |Bibliography| rtl)
