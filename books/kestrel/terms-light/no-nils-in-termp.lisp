; Checking that NIL never appears as a variable in a term or list of terms
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

;; This is needed due to a deficiency in how defevaluator evaluates NIL, which
;; is syntactically a variable although not a legal one:

(mutual-recursion
 ;; Checks that NIL never appears as a variable in TERM, including in lambda
  ;; bodies.
  ;; todo: disable these functions
 (defun no-nils-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       (not (equal term nil))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (no-nils-in-termsp (fargs term))
              (if (consp fn)
                  (no-nils-in-termp (lambda-body fn))
                t))))))
 (defun no-nils-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (no-nils-in-termp (first terms))
          (no-nils-in-termsp (rest terms))))))

(defthm no-nils-in-termsp-of-cdr
  (implies (no-nils-in-termsp terms)
           (no-nils-in-termsp (cdr terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp))))

(defthm no-nils-in-termp-of-cons
  (equal (no-nils-in-termp (cons fn args))
         (if (equal 'quote fn)
             t
           (and (no-nils-in-termsp args)
                (if (consp fn)
                    (no-nils-in-termp (lambda-body fn))
                  t))))
  :hints (("Goal" :expand (no-nils-in-termp (cons fn args))
           :in-theory (enable no-nils-in-termp))))

(defthm-flag-free-vars-in-term
  (defthm not-member-equal-of-nil-and-free-vars-in-term
    (implies (and ;(pseudo-termp term)
                  (no-nils-in-termp term))
             ;; This is weaker than (no-nils-in-termp term) because it doesn't
             ;; check lambda bodies:
             (not (member-equal nil (free-vars-in-term term))))
    :flag free-vars-in-term)
  (defthm not-member-equal-of-nil-and-free-vars-in-terms
    (implies (and ;(pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (not (member-equal nil (free-vars-in-terms terms))))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand ((FREE-VARS-IN-TERM TERM))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable free-vars-in-terms
                              no-nils-in-termp
                              no-nils-in-termsp))))

(defthm no-nils-in-termp-when-symbolp
  (implies (symbolp term)
           (equal (no-nils-in-termp term)
                  (not (equal term nil))))
  :hints (("Goal" :in-theory (enable no-nils-in-termp))))

(defthm no-nils-in-termsp-when-symbol-listp
  (implies (symbol-listp terms)
           (equal (no-nils-in-termsp terms)
                  (not (member-equal nil terms))))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp))))

(defthmd not-member-equal-of-nil-when-no-nils-in-termsp
  (implies (no-nils-in-termsp terms)
           (not (member-equal nil terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp))))

(defthm no-nils-in-termp-of-car
  (implies (no-nils-in-termsp terms)
           (equal (no-nils-in-termp (car terms))
                  (consp terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp))))

(defthm no-nils-in-termsp-of-cons
  (equal (no-nils-in-termsp (cons term terms))
         (and (no-nils-in-termp term)
              (no-nils-in-termsp terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp))))


(defthm no-nils-in-termsp-of-remove-equal
  (implies (no-nils-in-termsp terms)
           (no-nils-in-termsp (remove-equal term terms)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     remove-equal))))

(defthm no-nils-in-termsp-of-take
  (implies (no-nils-in-termsp terms)
           (equal (no-nils-in-termsp (take n terms))
                  (<= (nfix n) (len terms))))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     take))))

(defthm no-nils-in-termsp-of-union-equal
  (equal (no-nils-in-termsp (union-equal terms1 terms2))
         (and (no-nils-in-termsp terms1)
              (no-nils-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     union-equal))))

(defthm no-nils-in-termsp-of-intersection-equal
  (implies (or (no-nils-in-termsp terms1)
               (no-nils-in-termsp terms2))
           (no-nils-in-termsp (intersection-equal terms1 terms2)))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp
                                     intersection-equal))))

(defthm no-nils-in-termsp-of-set-difference-equal
  (implies (no-nils-in-termsp terms)
           (no-nils-in-termsp (set-difference-equal terms terms2)))
  :hints (("Goal" :in-theory (enable set-difference-equal no-nils-in-termsp))))

(defthm no-nils-in-termsp-of-append
  (equal (no-nils-in-termsp (append terms1 terms2))
         (and (no-nils-in-termsp terms1)
              (no-nils-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable append no-nils-in-termsp))))

(local (make-flag no-nils-in-termp))

;; Just use no-nils-in-termsp-when-symbol-listp
;; (defthm-flag-no-nils-in-termp
;;   (defthm no-nils-in-termsp-of-free-vars-in-term
;;     (implies (no-nils-in-termp term)
;;              (no-nils-in-termsp (free-vars-in-term term)))
;;     :flag no-nils-in-termp)
;;   (defthm no-nils-in-termsp-of-free-vars-in-terms
;;     (implies (no-nils-in-termsp terms)
;;              (no-nils-in-termsp (free-vars-in-terms terms)))
;;     :flag no-nils-in-termsp)
;;   :hints (("Goal" :expand (free-vars-in-terms terms)
;;            :in-theory (enable free-vars-in-term no-nils-in-termsp))))

(local
 (defthm-flag-no-nils-in-termp
   (defthm no-nils-in-termp-when-termp
     (implies (termp term w)
              (no-nils-in-termp term))
     :flag no-nils-in-termp)
   (defthm no-nils-in-termsp-when-term-listp
     (implies (term-listp terms w)
              (no-nils-in-termsp terms))
     :flag no-nils-in-termsp)
   :hints (("Goal" :expand (free-vars-in-terms terms)
            :in-theory (enable free-vars-in-term no-nils-in-termp no-nils-in-termsp)))))

;; Sanity check: termp implies no-nils-in-termp
;; redundant and non-local
(defthm no-nils-in-termp-when-termp
  (implies (termp term w)
           (no-nils-in-termp term)))

;; redundant and non-local
(defthm no-nils-in-termsp-when-term-listp
  (implies (term-listp terms w)
           (no-nils-in-termsp terms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sanity check: logic-termp implies no-nils-in-termp
(defthm no-nils-in-termp-when-logic-termp
  (implies (logic-termp term w)
           (no-nils-in-termp term)))

(defthm no-nils-in-termsp-when-logic-term-listp
  (implies (logic-term-listp terms w)
           (no-nils-in-termsp terms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm no-nils-in-termp-of-cdr-of-assoc-equal
  (implies (and (no-nils-in-termsp (strip-cdrs alist))
                (assoc-equal term alist))
           (no-nils-in-termp (cdr (assoc-equal term alist))))
  :hints (("Goal" :in-theory (enable no-nils-in-termsp assoc-equal strip-cdrs))))
