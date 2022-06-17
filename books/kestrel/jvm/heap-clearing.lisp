; Material on clearing parts of a heap
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "heap0")
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;;
;; clear-field
;;

(defund clear-field (ref pair heap)
  (set-field ref pair nil heap))

(defthm clear-field-of-nil
  (equal (clear-field ad pair nil)
         nil)
  :hints (("goal" :in-theory (enable clear-field))))

(defthm equal-set-field-destruct
  (equal (equal (set-field ref pair value1 heap1)
		(set-field ref pair value2 heap2))
	 (and (equal value1 value2)
	      (equal (clear-field ref pair heap1)
		     (clear-field ref pair heap2))))
  :hints (("Goal" :in-theory (enable clear-field set-field))))

(defthm clear-field-of-set-field-both
  (equal (clear-field ref1 pair1 (set-field ref2 pair2 value heap))
	 (if (and (equal ref1 ref2)
                  (equal pair1 pair2))
	     (clear-field ref1 pair1 heap)
	   (set-field ref2 pair2 value (clear-field ref1 pair1 heap))))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

(defthm clear-field-of-set-field-diff
  (implies (not (and (equal ref1 ref2)
		     (equal pair1 pair2))) ;distribute?
	   (equal (clear-field ref1 pair1
				      (set-field ref2 pair2 value heap))
		  (set-field ref2 pair2 value (clear-field ref1 pair1 heap))))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

(defthm clear-field-of-set-field-same
  (equal (clear-field ref pair (set-field ref pair value heap))
	 (clear-field ref pair heap))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

;more theorems needed about clr?

;;
;; clear-binding
;;

;remove all the bindings from BINDINGS whose keys match PAIR
(defund clear-binding (pair bindings)
  (if (endp bindings)
      nil
    (let ((binding (car bindings)))
      (if (equal (car binding) pair)
          (clear-binding pair (cdr bindings))
        (cons binding (clear-binding pair (cdr bindings)))))))

(defthm clear-binding-nil
  (equal (clear-binding pair nil)
         nil)
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm clear-binding-of-not-consp
  (implies (not (consp x))
           (equal (clear-binding pair x)
                  nil))
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm clear-binding-does-nothing
  (implies (and (not (memberp a (strip-cars b)))
;                (true-listp b)
                )
           (equal (CLEAR-BINDING a b)
                  (true-list-fix b)))
  :hints (("Goal" :expand ((CLEAR-BINDING A B)))))

(defthm clear-binding-of-cons
  (equal (clear-binding pair (cons binding bindings))
         (if (equal pair (car binding))
             (clear-binding pair bindings)
           (cons binding (clear-binding pair bindings))))
  :hints (("Goal" :in-theory (enable clear-binding))))

(defthm clear-binding-of-clear-binding
  (equal (clear-binding pair (clear-binding pair bindings))
         (clear-binding pair bindings))
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm acl2-count-clear-binding-decreases
  (implies (and (consp bindings) (true-listp bindings))
           (<= (acl2-count (clear-binding pair bindings))
               (acl2-count bindings)))
  :rule-classes :linear
  :hints (("goal" :do-not '(eliminate-destructors generalize)
           :in-theory (enable clear-binding acl2-count))))

(defthm set-to-nil-equal-clear-field
  (equal (set-field ad pair nil heap)
         (clear-field ad pair heap)
         )
  :hints (("goal" :in-theory (enable set-field clear-field))))

(theory-invariant (incompatible (:rewrite SET-TO-NIL-EQUAL-CLEAR-FIELD)
                                (:definition clear-field)))

(defthm clear-field-of-clear-field
  (equal (clear-field ad pair (clear-field ad2 pair2 heap))
         (clear-field ad2 pair2 (clear-field ad pair heap)))
  :rule-classes ((:rewrite :loop-stopper ((ad ad2)
                                          (pair pair2))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (set-difference-theories
                       (enable clear-field)
                       '( SET-TO-NIL-EQUAL-CLEAR-FIELD)))))

;what if the ads differ?
(defthm clear-field-of-set-fields
  (equal (clear-field ad pair (set-fields ad bindings heap))
         (set-fields ad (clear-binding pair bindings)
                     (clear-field ad pair heap)))
  :hints (("goal"
           :in-theory (set-difference-theories
                       (enable set-fields clear-binding)
                       '(set-fields-collect-2))
           :do-not '(eliminate-destructors generalize))))

;rename
(defthm set-fields-of-clear-binding
  (implies (consp bindings)
           (equal (set-fields ad (cons (car bindings)
                                       (clear-binding (caar bindings) (cdr bindings)))
                              heap)
                  (set-fields ad bindings heap)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable set-fields)
                              '(SET-FIELDS-COLLECT-2))
           :do-not '(eliminate-destructors))))


;other cases?
(defthm clear-field-of-set-fields-diff
  (implies (not (equal ad ad2))
           (equal (CLEAR-FIELD ad pair (SET-FIELDS ad2 bindings heap))
                  (SET-FIELDS ad2 bindings (CLEAR-FIELD ad pair heap))))
  :hints (("Goal" :in-theory (e/d (set-fields)
                                  (set-fields-collect-2)))))

(defthm get-field-of-clear-field-both
  (equal (get-field ad1 pair1 (clear-field ad2 pair2 heap))
         (if (and (equal ad1 ad2)
                  (equal pair1 pair2))
             nil
           (get-field ad1 pair1 heap)))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

(defthm clr-of-set-field
  (equal (clr ad (set-field ad pair value heap))
         (clr ad heap))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm clr-of-clear-field
  (equal (clr ad (clear-field ad value heap))
         (clr ad heap))
  :hints (("Goal" :in-theory (e/d (clear-field) (SET-TO-NIL-EQUAL-CLEAR-FIELD)))))

(defthm clr-of-set-fields
  (equal (clr ad (set-fields ad bindings heap))
         (clr ad heap))
  :hints (("Goal" :expand (SET-FIELDS AD BINDINGS HEAP)
           :in-theory (enable set-fields))))

(defthm clear-field-does-nothing
  (implies (not (get-field ad pair heap))
           (equal (clear-field ad pair heap)
                  heap))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

;why does this arise (as opposed to clear-field of set-field)?
(defthm clr-of-set-field-diff
  (implies (not (equal ad1 ad2))
           (equal (CLR ad1 (SET-FIELD AD2 CLASS-FIELD-PAIR VALUE HEAP))
                  (SET-FIELD AD2 CLASS-FIELD-PAIR VALUE (clr ad1 HEAP))))
  :hints (("Goal" :in-theory (enable set-field))))
