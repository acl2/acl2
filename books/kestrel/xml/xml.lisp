; A formalization of XML datatypes
;
; Copyright (C) 2014-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book describes a quick-and-dirty ACL2 encoding of XML as S-expressions.

;; TODO: Handle Unicode (in strings, in tags?)
;; TODO: Handle character entities like &lt; and &gt;.

;recognizes a binding from an attribute name to a value.  Example: (= "package" "edu.kestrel.examples.app2")
;; TODO: Consider not storing the equal sign.
(defun xml-attributep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal 3 (len x))
       (eq '= (first x))
       (stringp (second x))
       (stringp (third x))))

(defun xml-attribute-listp (atts)
  (declare (xargs :guard t))
  (if (not (consp atts))
      (null atts)
    (and (xml-attributep (first atts))
         (xml-attribute-listp (rest atts)))))

;Skip over a prefix of well-formed attribute bindings (these come first in the list of arguments of a parent element, before its child elements):
(defund skip-xml-attributes (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      items
    (if (xml-attributep (first items))
        (skip-xml-attributes (rest items))
      items)))

(defthm true-listp-of-skip-xml-attributes
  (implies (true-listp items)
           (true-listp (skip-xml-attributes items)))
  :hints (("Goal" :in-theory (enable skip-xml-attributes))))

(defthm acl2-count-of-skip-xml-attributes
  (<= (acl2-count (skip-xml-attributes items))
      (acl2-count items))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (enable skip-xml-attributes))))

; In XML, an element can have attributes (name/value pairs stored in
; the element's start tag), followed by child elements (nested elements listed
; between the parent element's start and end tags)
(mutual-recursion
  ;; An XML 'item' is an XML element or a string
  (defund xml-item-listp (items)
    (declare (xargs :guard t
                    :measure (acl2-count items)))
    (if (not (consp items))
        (null items)
      (let ((item (first items)))
        (and (or ;(xml-attributep item)
               (stringp item)
               (xml-elementp item))
             (xml-item-listp (rest items))))))

  ;; Recognizes a well-formed XML element, representing a pair of matched start
  ;; and end tags, possibly with attributes in the start tag and possibly
  ;; containing nested xml items (strings and XML elements) between the tags.
  (defund xml-elementp (x)
    (declare (xargs :guard t
                    :measure (acl2-count x)))
    (and (consp x)
         (let ((tag (first x))
               (args (rest x)))
           (and (stringp tag)
                (true-listp args)
                ;;first we skip over any XML attributes (these must come first), then we check that everything else consists of well-formed child elements:
                (xml-item-listp (skip-xml-attributes args)))))))

(defthm xml-item-listp-forward-to-true-listp
  (implies (xml-item-listp items)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable xml-item-listp))))

;Recognizes a list of attributes followed by a list of child elements
;; TODO: Change xml-elementp to store the attributes and the nested items separately.
(defund xml-element-argsp (items)
  (declare (xargs :guard (true-listp items)))
  (xml-item-listp (skip-xml-attributes items)))

(defthm skip-xml-attributes-does-nothing
  (implies (xml-item-listp args)
           (equal (skip-xml-attributes args)
                  args))
  :hints (("Goal" :in-theory (enable xml-item-listp skip-xml-attributes xml-elementp))))

(defthm xml-element-argsp-of-cdr
  (implies (xml-element-argsp args)
           (xml-element-argsp (cdr args)))
  :hints (("Goal" :in-theory (enable xml-element-argsp xml-item-listp skip-xml-attributes))))

(defthm xml-element-argsp-of-append
  (implies (and (xml-attribute-listp attributes)
                (xml-item-listp child-items))
           (xml-element-argsp (append attributes child-items)))
  :hints (("Goal" :in-theory (enable xml-element-argsp skip-xml-attributes xml-attribute-listp))))

;re-characterize to have xml-element-argsp closed up:
(defthm xml-elementp-rewrite
  (equal (xml-elementp x)
         (and (consp x)
              (let ((tag (first x))
                    (args (rest x)))
                (and (stringp tag)
                     (true-listp args)
                     ;;first we skip over any XML attrbutes (these must come first), then we check that everything else consists of well-formed child elements:
                     (xml-element-argsp args)))))
  :rule-classes ((:definition))
  :hints (("Goal" :in-theory (enable XML-ELEMENT-ARGSP)
           :expand ((XML-ELEMENTP X)))))

(defthm xml-item-listp-of-cdr
  (implies (xml-item-listp items)
           (xml-item-listp (cdr items)))
  :hints (("Goal" :in-theory (enable xml-item-listp))))

(defthm xml-item-listp-of-cons
  (equal (xml-item-listp (cons item items))
         (and (or (stringp item) (xml-elementp item))
              (xml-item-listp items)))
  :hints (("Goal" :in-theory (enable xml-item-listp))))

;expensive since hung off of car
(defthmd car-type-when-xml-item-listp
  (implies (and (xml-item-listp items)
                (consp items))
           (or (stringp (car items))
               (consp (car items))))
  :rule-classes (:type-prescription
                 (:rewrite :backchain-limit-lst (0 1)))
  :hints (("Goal" :expand (XML-ITEM-LISTP ITEMS)
           :in-theory (enable xml-item-listp))))

;; (defthmd xml-item-listp-of-skip-xml-attributes
;;   (implies (xml-item-listp args)
;;            (xml-item-listp (skip-xml-attributes args)))
;;   :hints (("Goal" :in-theory (enable skip-xml-attributes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-xml-element (tag attributes child-items)
  (declare (xargs :guard (and (stringp tag)
                              (xml-attribute-listp attributes)
                              (xml-item-listp child-items))))
  (cons tag (append attributes child-items)))


(defthm xml-elementp-of-make-xml-element
  (implies (and (stringp tag)
                (xml-attribute-listp attributes)
                (xml-item-listp child-items))
           (xml-elementp (make-xml-element tag attributes child-items)))
  :hints (("Goal" :in-theory (enable make-xml-element))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Getters for the tag, attributes, and child-elements:

;; Returns the tag of an XML element.
(defund xml-element-tag (elem)
  (declare (xargs :guard (xml-elementp elem)))
  (car elem))

;; Also used by the xml-parser
(defund get-xml-attributes (items)
  (declare (xargs :guard (true-listp items))) ; todo
  (if (endp items)
      nil
    (if (xml-attributep (first items))
        (cons (first items) (get-xml-attributes (rest items)))
      ;; we've reached the end of the attributes
      nil)))

(defthm xml-attribute-listp-of-get-xml-attributes
  (xml-attribute-listp (get-xml-attributes elem))
  :hints (("Goal" :in-theory (enable xml-attribute-listp
                                     get-xml-attributes))))

;; Returns the attributes of an XML element.
(defund xml-element-attributes (elem)
  (declare (xargs :guard (xml-elementp elem)))
  (get-xml-attributes (cdr elem)))

(defthm xml-attribute-listp-of-xml-element-attributes
  (implies (xml-elementp elem)
           (xml-attribute-listp (xml-element-attributes elem)))
  :hints (("Goal" :in-theory (enable xml-elementp xml-element-attributes
                                     xml-element-argsp))))

;; Returns the child items (strings and XML elements) of an XML element:
(defund xml-element-sub-items (elem)
  (declare (xargs :guard (xml-elementp elem)))
  (skip-xml-attributes (cdr elem)))

(defthm <-of-acl2-count-of-xml-element-sub-items-linear
  (implies (xml-elementp elem)
           (< (acl2-count (xml-element-sub-items elem))
              (acl2-count elem)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable xml-element-sub-items))))

(defthm xml-item-listp-of-xml-element-sub-items
  (implies (xml-elementp elem)
           (xml-item-listp (xml-element-sub-items elem)))
  :hints (("Goal" :in-theory (enable xml-element-sub-items xml-element-argsp))))

(defthm true-listp-of-xml-element-sub-items-type
  (implies (xml-elementp elem)
           (true-listp (xml-element-sub-items elem)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable xml-element-sub-items xml-element-argsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;keep the members of ITEMS that are XML elements, not strings
(defun filter-xml-elements (items)
  (declare (xargs :guard (xml-item-listp items)))
  (if (not (consp items))
      nil
    (let ((item (first items)))
      (if (not (stringp item))
          (cons item (filter-xml-elements (rest items)))
        (filter-xml-elements (rest items))))))

;returns all of the child elements (not the strings)
(defun child-elements (elem)
  (declare (xargs :guard (xml-elementp elem)
                  :guard-hints (("Goal" :in-theory (enable xml-element-argsp)))))
  (filter-xml-elements (xml-element-sub-items elem)))

;; From the ITEMS (elements and strings) keep the ones that are elements whose tag is NAME.
(defun filter-elements-with-tag (name items)
  (declare (xargs :guard (xml-item-listp items)))
  (if (not (consp items))
      nil
    (let ((item (first items)))
      (if (and (not (stringp item))
               (equal name (xml-element-tag item)))
          (cons item (filter-elements-with-tag name (rest items)))
        (filter-elements-with-tag name (rest items))))))

;; (defthm use-xml-element-argsp-limited
;;   (implies (xml-element-argsp item)
;;            (xml-item-listp (skip-xml-attributes item)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable xml-element-argsp))))

(defund child-elements-with-tag (tag elem)
  (declare (xargs :guard (xml-elementp elem)))
  (let ((child-items (xml-element-sub-items elem)))
    (filter-elements-with-tag tag child-items)))

;; Returns the first  child element with the given tag.
;; Returns nil if there aren't any.
(defund first-child-element-with-tag (tag elem)
  (declare (xargs :guard (xml-elementp elem)))
  (first (child-elements-with-tag tag elem)))

;use a generic? something like get-the (for "get the unique item in this list that satisfies this predicate" -- obligation that only one does?)
(defun get-xml-attribute-aux (name args)
  (declare (xargs :guard (and (stringp name)
                              (true-listp args)
                              (xml-element-argsp args))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors) :in-theory (disable len)))))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (if (not (xml-attributep arg))
          nil ;since the attributes come first, all that's left is child elements
        (if (and (eq '= (first arg)) ; drop?
                 (equal name (second arg)))
            (third arg)
          (get-xml-attribute-aux name (rest args)))))))

;returns nil or a string
;get the string value equated to the string name in something like (= "foo" "bar")
(defund get-xml-attribute (name elem)
  (declare (xargs :guard (and (stringp name)
                              (xml-elementp elem))))
  (let ((args (rest elem)))
    (get-xml-attribute-aux name args)))

(defun xml-attribute-presentp (name elem)
  (declare (xargs :guard (and (stringp name)
                              (xml-elementp elem))))
  ;;todo: weaken to bool-fix?
  (stringp (get-xml-attribute name elem)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get the first thing in the XML-ELEMENT's contents (a string or child element)
(defun xml-element-first-contents (elem)
  (declare (xargs :guard (xml-elementp elem)
                  :guard-hints (("Goal" :in-theory (disable xml-elementp-rewrite)))
                  ))
  (first (xml-element-sub-items elem)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Gather all element names (i.e., tag names):
(mutual-recursion
  (defun gather-element-names-from-items (items)
    (declare (xargs :guard (xml-item-listp items)
                    :measure (acl2-count items)
                    :verify-guards nil ; done below
                    ))
    (if (endp items)
        nil
      (let ((item (first items)))
        ;; todo: maybe union?
        (append (if (stringp item) nil (gather-element-names item))
                (gather-element-names-from-items (rest items))))))

  (defun gather-element-names (elem)
    (declare (xargs :guard (xml-elementp elem)
                    :measure (acl2-count elem)))
    (if (mbt (xml-elementp elem)) ; for termination
        (cons (xml-element-tag elem)
              (gather-element-names-from-items (xml-element-sub-items elem)))
      nil)))

(verify-guards gather-element-names-from-items)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *whitespace-chars*
  '(#\Space #\Tab #\Return #\Newline))

(defund whitespace-char-p (char)
  (declare (xargs :guard t))
  (member char *whitespace-chars*))

(defun all-whitespace-char-p (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      t
    (and (whitespace-char-p (first chars))
         (all-whitespace-char-p (rest chars)))))

(defun whitespace-string-p (str)
  (declare (xargs :guard (stringp str)))
  (all-whitespace-char-p (coerce str 'list)))

(mutual-recursion
  (defun drop-whitespace-strings-from-parsed-xml-element (elem)
    (declare (xargs :guard (xml-elementp elem)
                    :measure (acl2-count elem)))
    (if (not (mbt (xml-elementp elem)))
        nil
      (let* ((tag (xml-element-tag elem))
             (attribs (xml-element-attributes elem))
             (sub-items (xml-element-sub-items elem)))
        `(,tag ,@attribs ,@(drop-whitespace-strings-from-parsed-xml-items sub-items)))))

 (defun drop-whitespace-strings-from-parsed-xml-items (items)
   (declare (xargs :guard (xml-item-listp items)
                   :measure (acl2-count items)))
   (if (endp items)
       nil
     (let ((item (first items)))
       (if (stringp item)
           (if (whitespace-string-p item)
               (drop-whitespace-strings-from-parsed-xml-items (rest items))
             (cons item (drop-whitespace-strings-from-parsed-xml-items (rest items))))
         (cons (drop-whitespace-strings-from-parsed-xml-element item)
               (drop-whitespace-strings-from-parsed-xml-items (rest items))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a true-listp of xml-elements.
(defun xml-element-listp (elems)
  (declare (xargs :guard t))
  (if (not (consp elems))
      (null elems)
    (and (xml-elementp (first elems))
         (xml-element-listp (rest elems)))))

(defun filter-elements-with-attribute (elements attribute-name attribute-value)
  (declare (xargs :guard (and (xml-element-listp elements)
                              (stringp attribute-name)
                              (stringp attribute-value))))
  (if (not (consp elements))
      nil
    (let* ((element (first elements)))
      (if (equal (get-xml-attribute  attribute-name element)
                 attribute-value)
          (cons element ;keep it
                (filter-elements-with-attribute (rest elements) attribute-name attribute-value))
        ;;drop it
        (filter-elements-with-attribute (rest elements) attribute-name attribute-value)))))

;gets the first such element, or nil
(defun get-element-with-attribute (elements attribute-name attribute-value)
  (declare (xargs :guard (and (xml-element-listp elements)
                              (stringp attribute-name)
                              (stringp attribute-value))))
  (first (filter-elements-with-attribute elements attribute-name attribute-value)))
