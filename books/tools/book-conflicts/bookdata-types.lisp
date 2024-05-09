;;
;; Copyright (C) 2014, David Greve
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2.
;;
(in-package "ACL2")

;;
;; Here we define the types of the various entries we expect
;; to find in a bookdata file.
;;

;; ------------------------------------------------------------------
;;
;; Bookdata pkg-symbol-name-listp
;;
;; ------------------------------------------------------------------

(defund pkg-symbol-name-list-entry (entry)
  (declare (type t entry))
  (and (consp entry)
       (stringp (car entry))
       (string-listp (cdr entry))))

(defthm pkg-symbol-name-list-entry-implies
  (implies
   (pkg-symbol-name-list-entry entry)
   (and (consp entry)
	(stringp (car entry))
	(string-listp (cdr entry))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pkg-symbol-name-list-entry))))

(defthm implies-pkg-symbol-name-list-entry
  (implies
   (and (consp entry)
	(stringp (car entry))
	(string-listp (cdr entry)))
   (pkg-symbol-name-list-entry entry))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable pkg-symbol-name-list-entry))))

(defun pkg-symbol-name-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (pkg-symbol-name-list-entry (car list))
	 (pkg-symbol-name-listp (cdr list)))))

(defthm consp-pkg-symbol-name-listp-implies
  (implies
   (and
    (pkg-symbol-name-listp list)
    (consp list))
   (and (pkg-symbol-name-list-entry (car list))
	(pkg-symbol-name-listp (cdr list))))
  :rule-classes :forward-chaining)

(defthm pkg-symbol-name-listp-implies-alistp
  (implies
   (pkg-symbol-name-listp list)
   (alistp list))
  :rule-classes :forward-chaining)

;; ------------------------------------------------------------------
;;
;; Bookdata :pkgs entry
;;
;; ------------------------------------------------------------------

(defund bookdata-pkgs-type (key value)
  (declare (type t key value))
  (and (equal key :pkgs)
       (string-listp value)))

(defthm bookdata-pkgs-type-implies
  (implies
   (bookdata-pkgs-type key value)
   (and (equal key :pkgs)
	(string-listp value)))
  :hints (("Goal" :in-theory (enable bookdata-pkgs-type)))
  :rule-classes (:forward-chaining))

(defthm not-bookdata-pkgs-type-from-not-pkgs
  (implies
   (not (equal key :pkgs))
   (not (bookdata-pkgs-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-pkgs-type)))
  :rule-classes (:type-prescription
		 (:forward-chaining :trigger-terms ((bookdata-pkgs-type key value)))))

;; ------------------------------------------------------------------
;;
;; Bookdata :books entry
;;
;; ------------------------------------------------------------------

(defund bookdata-books-type (key value)
  (declare (type t key value))
  (and (or (equal key :books)
	   (equal key :port-books))
       (string-listp value)))

(defthm bookdata-books-type-implies
  (implies
   (bookdata-books-type key value)
   (and (or (equal key :books)
	    (equal key :port-books))
	(string-listp value)))
  :hints (("Goal" :in-theory (enable bookdata-books-type)))
  :rule-classes (:forward-chaining))

(defthm not-bookdata-books-type
  (implies
   (and (not (equal key :books))
	(not (equal key :port-books)))
   (not (bookdata-books-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-books-type)))
  :rule-classes (:type-prescription
		 (:forward-chaining :trigger-terms ((bookdata-books-type key value)))))

;; ------------------------------------------------------------------
;;
;; Bookdata symbols entries
;;
;; ------------------------------------------------------------------

(defund bookdata-symbols-type (key value)
  (declare (type t key value))
  (and (not (equal key :books))
       (not (equal key :port-books))
       (not (equal key :pkgs))
       (pkg-symbol-name-listp value)))

(defthm bookdata-symbols-type-implies
  (implies
   (bookdata-symbols-type key value)
   (and (not (equal key :books))
	(not (equal key :port-books))
	(not (equal key :pkgs))
	(pkg-symbol-name-listp value)))
  :hints (("Goal" :in-theory (enable bookdata-symbols-type)))
  :rule-classes (:forward-chaining))

(defthm books-not-bookdata-symbols-type
  (implies
   (equal key :books)
   (not (bookdata-symbols-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-symbols-type)))
  :rule-classes (:type-prescription
		 (:forward-chaining :trigger-terms ((bookdata-symbols-type key value)))))

(defthm port-books-not-bookdata-symbols-type
  (implies
   (equal key :port-books)
   (not (bookdata-symbols-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-symbols-type)))
  :rule-classes (:type-prescription
		 (:forward-chaining :trigger-terms ((bookdata-symbols-type key value)))))

(defthm pkgs-not-bookdata-symbols-type
  (implies
   (equal key :pkgs)
   (not (bookdata-symbols-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-symbols-type)))
  :rule-classes (:type-prescription
		 (:forward-chaining :trigger-terms ((bookdata-symbols-type key value)))))

;; ------------------------------------------------------------------
;;
;; Bookdata key types
;;
;; ------------------------------------------------------------------

(defund bookdata-key-type (key value)
  (declare (type t key value))
  (or (bookdata-books-type key value)
      (bookdata-pkgs-type key value)
      (bookdata-symbols-type key value)))

(defthm bookdata-key-type-implies
  (implies
   (bookdata-key-type key value)
   (or (bookdata-books-type key value)
       (bookdata-pkgs-type key value)
       (bookdata-symbols-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-key-type)))
  :rule-classes (:forward-chaining))

(defthm open-bookdata-key-type
  (equal (bookdata-key-type key value)
	 (if (equal key :pkgs) (bookdata-pkgs-type key value)
	   (if (equal key :books) (bookdata-books-type key value)
	     (if (equal key :port-books) (bookdata-books-type key value)
	       (bookdata-symbols-type key value)))))
  :hints (("Goal" :in-theory (enable bookdata-key-type))))

;; ------------------------------------------------------------------
;;
;; Bookdata key map
;;
;; ------------------------------------------------------------------

(defund bookdata-key-map (key value)
  (declare (type t key value))
  (and (symbolp key)
       (equal (symbol-package-name key) "KEYWORD")
       (bookdata-key-type key value)))

(defthm bookdata-key-map-implies
  (implies
   (bookdata-key-map key value)
   (and (symbolp key)
	(equal (symbol-package-name key) "KEYWORD")
	(bookdata-key-type key value)))
  :hints (("Goal" :in-theory (enable bookdata-key-map)))
  :rule-classes (:forward-chaining))

;; ------------------------------------------------------------------
;;
;; Bookdata key maps
;;
;; ------------------------------------------------------------------

(defun bookdata-key-maps (list)
  (declare (type t list))
  (if (consp list)
      (and (consp (cdr list))
	   (bookdata-key-map (car list) (cadr list))
	   (bookdata-key-maps (cddr list)))
    (null list)))

(defthm bookdata-key-maps-implies-true-listp
  (implies
   (bookdata-key-maps list)
   (true-listp list))
  :rule-classes (:forward-chaining))

;; ------------------------------------------------------------------
;;
;; wf-bookdata
;;
;; ------------------------------------------------------------------

(defund wf-bookdata (entry)
  (declare (type t entry))
  (and (consp entry)
       (stringp (car entry))
       (consp (cdr entry))
       (bookdata-key-maps (cdr entry))))

(defthm wf-bookdata-implies
  (implies
   (wf-bookdata entry)
   (and (consp entry)
	(stringp (car entry))
	(consp (cdr entry))
	(bookdata-key-maps (cdr entry))))
  :hints (("Goal" :in-theory (enable wf-bookdata)))
  :rule-classes (:forward-chaining))

;; ------------------------------------------------------------------
;;
;; wf-bookdata-listp
;;
;; ------------------------------------------------------------------

(defun wf-bookdata-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (wf-bookdata (car list))
	 (wf-bookdata-listp (cdr list)))))

