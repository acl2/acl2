; A formalization of XML datatypes
;
; Copyright (C) 2014-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book describes a quick-and-dirty ACL2 encoding of XML as S-expressions.

;TODO: Handle Unicode...

;recognizes a binding from an attribute name to a value.  Example: (= "package" "edu.kestrel.examples.app2")
(defun xml-attributep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal 3 (len x))
       (eq '= (first x))
       (stringp (second x))
       (stringp (third x))))

;; Used by the xml-parser
(defun get-xml-attributes (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (if (xml-attributep (first items))
        (cons (first items) (get-xml-attributes (rest items)))
      nil)))

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

; xml-elementp recognizes a valid XML element (possibly containing attributes and nested elements)

;an XML 'item' is an XML element or a string

; In XML, an element can have attributes (name/value pairs stored in
; the element's start tag), followed by child elements (nested elements listed
; between the parent element's start and end tags)
(mutual-recursion
 (defund xml-item-listp (items)
   (declare (xargs :guard (true-listp items)
                   :measure (acl2-count items)))
   (if (endp items)
       t
     (let ((item (first items)))
       (and (or ;(xml-attributep item)
             (stringp item)
             (xml-elementp item))
            (xml-item-listp (rest items))))))

 ;;Recognizes a well-formed XML element:
 (defund xml-elementp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (and (consp x)
        (let ((tag (first x))
              (args (rest x)))
          (and (stringp tag) ;fixme can unicode appear here?
               (true-listp args)
               ;;first we skip over any XML attrbutes (these must come first), then we check that everything else consists of well-formed child elements:
               (xml-item-listp (skip-xml-attributes args)))))))

;looks for attributes followed by child elements
(defund xml-element-argsp (items)
  (declare (xargs :guard (true-listp items)))
  (xml-item-listp (skip-xml-attributes items)))

;re-characterize to have xml-element-argsp closed up:
(defthm xml-elementp-rewrite
  (equal (xml-elementp x)
         (and (consp x)
              (let ((tag (first x))
                    (args (rest x)))
                (and (stringp tag) ;fixme can unicode appear here?
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

(defthm xml-item-listp-of-skip-xml-attributes
  (implies (xml-item-listp args)
           (xml-item-listp (skip-xml-attributes args)))
  :hints (("Goal" :in-theory (enable skip-xml-attributes))))

;fixme use deffilter
;can the items include attrbutes as well as child elements?
(defun filter-elements-with-name (name items)
  (declare (xargs :guard (and (true-listp items)
                              (xml-item-listp items))))
  (if (not (consp items))
      nil
    (let ((item (first items)))
      (if (and (not (stringp item))
               (equal name (car item)))
          (cons item (filter-elements-with-name name (rest items)))
        (filter-elements-with-name name (rest items))))))

;keep the members of ITEMS that are XML elemenet, not strings
(defun filter-xml-elements (items)
  (declare (xargs :guard (and (true-listp items)
                              (xml-item-listp items))))
  (if (not (consp items))
      nil
    (let ((item (first items)))
      (if (not (stringp item))
          (cons item (filter-xml-elements (rest items)))
        (filter-xml-elements (rest items))))))

(defthm use-XML-ELEMENT-ARGSP-limited
  (IMPLIES (XML-ELEMENT-ARGSP ITEM)
           (XML-ITEM-LISTP (SKIP-XML-ATTRIBUTES ITEM)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable XML-ELEMENT-ARGSP))))

;fixme what if there are several child elements with the same name?
(defun get-child-element (name xml-element)
  (declare (xargs :guard (xml-elementp xml-element)))
  (let ((child-elements (skip-xml-attributes (rest xml-element))))
    (first (filter-elements-with-name name child-elements))))

(defun get-child-elements (name xml-element)
  (declare (xargs :guard (xml-elementp xml-element)))
  (let ((child-elements (skip-xml-attributes (rest xml-element))))
    (filter-elements-with-name name child-elements)))

;returns all child elements
(defun child-elements (xml-element)
   (declare (xargs :guard (xml-elementp xml-element)))
   (let ((args (rest xml-element)))
    (filter-xml-elements (skip-xml-attributes args))))

(defthm SKIP-XML-ATTRIBUTES-does-nothing
  (implies (xml-item-listp args)
           (equal (skip-xml-attributes args)
                  args))
  :hints (("Goal" :in-theory (enable xml-item-listp skip-xml-attributes))))

(defthm xml-element-argsp-of-cdr
  (implies (xml-element-argsp args)
           (xml-element-argsp (cdr args)))
  :hints (("Goal" :in-theory (enable xml-element-argsp xml-item-listp skip-xml-attributes))))

;use a generic? something like get-the (for "get the unique item in this list that satisfies this predicate -- obligation that only one does?)
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
        (if (and (eq '= (first arg))
                 (equal name (second arg)))
            (third arg)
          (get-xml-attribute-aux name (rest args)))))))

;returns nil or a string
;get the string value equated to the string name in something like (= "foo" "bar")
(defund get-xml-attribute (name xml-element)
  (declare (xargs :guard (and (stringp name)
                              (xml-elementp xml-element))))
  (let ((args (rest xml-element)))
    (get-xml-attribute-aux name args)))

;Gather all element names (i.e., tag names):
(mutual-recursion
 (defun gather-element-names-list (items)
   (declare (xargs :guard (and (true-listp items)
                               (xml-item-listp items))
                   :measure (acl2-count items)
                   :guard-hints (("Goal" :in-theory (enable XML-ITEM-LISTP)))))
   (if (endp items)
       nil
     (append (if (stringp (first items)) nil (gather-element-names (first items)))
             (gather-element-names-list (rest items)))))

 (defun gather-element-names (item)
   (declare (xargs :guard (xml-elementp item)
                   :measure (acl2-count item)))
   (if (consp item)       ;for termination
       (cons (first item) ;the tag
             ;;first we skip over any XML attrbutes (these must come first), then we check that everything else consists of well-formed child elements:
             (gather-element-names-list (skip-xml-attributes (rest item))))
     nil)))

;todo: rename get-xml-tag
(defund get-tag (xml-element)
  (declare (xargs :guard (xml-elementp xml-element)))
  (car xml-element))

(defun xml-attribute-presentp (name xml-element)
  (declare (xargs :guard (and (stringp name)
                              (xml-elementp xml-element))))
  ;;todo: weaken to non-nil?
  (stringp (get-xml-attribute name xml-element)))

(defun xml-element-contents (xml-element)
  (declare (xargs :guard (xml-elementp xml-element)))
  (cdr xml-element))

;; Get the first thing in the XML-ELEMENT's contents (a string or child element)
(defun xml-element-first-contents (xml-element)
  (declare (xargs :guard (xml-elementp xml-element)))
  (first (xml-element-contents xml-element)))

(defun all-xml-elementp (elems)
  (declare (xargs :guard t))
  (if (atom elems)
      t
    (and (xml-elementp (first elems))
         (all-xml-elementp (rest elems)))))

(defthm all-xml-elementp-of-cdr
  (implies (all-xml-elementp elems)
           (all-xml-elementp (cdr elems)))
  :hints (("Goal" :in-theory (enable all-xml-elementp))))

(defun filter-elements-with-attribute (elements attribute-name attribute-value)
  (declare (xargs :guard (and (true-listp elements)
                              (all-xml-elementp elements)
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
  (first (filter-elements-with-attribute elements attribute-name attribute-value)))
