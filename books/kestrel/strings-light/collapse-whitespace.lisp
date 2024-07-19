; Collapsing/removing whitespace in strings
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund skip-leading-members (elems target-elems)
  (declare (xargs :guard (and (true-listp target-elems)
                              (true-listp elems))))
  (if (endp elems)
      nil
    (if (member-equal (first elems) target-elems)
        (skip-leading-members (rest elems) target-elems)
      elems)))

(local
  (defthm character-listp-of-skip-leading-members
    (implies (character-listp elems)
             (character-listp (skip-leading-members elems target-elems)))
    :hints (("Goal" :in-theory (enable skip-leading-members)))))

(local
  (defthm true-listp-of-skip-leading-members
    (implies (true-listp elems)
             (true-listp (skip-leading-members elems target-elems)))
    :hints (("Goal" :in-theory (enable skip-leading-members)))))

(local
  (defthm <=-of-len-of-skip-leading-members
    (<= (len (skip-leading-members elems target-elems))
        (len elems))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable skip-leading-members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund replace-runs-aux (elems target-elems rev-replacement-elems acc)
  (declare (xargs :guard (and (true-listp elems)
                              (true-listp target-elems)
                              (true-listp rev-replacement-elems)
                              (true-listp acc))
                  :measure (len elems)))
  (if (endp elems)
      (reverse acc)
    (let ((elem (first elems)))
      (if (member-equal elem target-elems)
          (replace-runs-aux (skip-leading-members (rest elems) target-elems)
                            target-elems
                            rev-replacement-elems
                            (append rev-replacement-elems acc))
        (replace-runs-aux (rest elems) target-elems rev-replacement-elems (cons elem acc))))))

(local
  (defthm character-listp-of-replace-runs-aux
    (implies (and (character-listp elems)
                  (character-listp rev-replacement-elems)
                  (character-listp acc))
             (character-listp (replace-runs-aux elems target-elems rev-replacement-elems acc)))
    :hints (("Goal" :in-theory (enable replace-runs-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Replace each maximal run in ELEMS of consecutive elements from the
;; TARGET-ELEMS with a single copy of the REPLACEMENT-ELEMS.
(defun replace-runs (elems target-elems replacement-elems)
  (declare (xargs :guard (and (true-listp elems)
                              (true-listp target-elems)
                              (true-listp replacement-elems))))
  (replace-runs-aux elems target-elems (reverse replacement-elems) nil))

;; (equal (replace-runs '(a b c 1 d e 1 2 3 f g 3 h i) '(1 2 3) '(small numbers here)) '(a b c small numbers here d e small numbers here f g small numbers here h i))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Collapses all whitespace down to a single space.
(defund collapse-whitespace-in-char-list (chars)
  (declare (xargs :guard (character-listp chars)))
  (replace-runs chars '(#\Space #\Tab #\Newline #\Return) '(#\Space)))

(local
  (defthm character-listp-of-collapse-whitespace-in-char-list
    (implies (character-listp chars)
             (character-listp (collapse-whitespace-in-char-list chars)))
    :hints (("Goal" :in-theory (enable collapse-whitespace-in-char-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Collapses all whitespace down to a single space.
(defund collapse-whitespace-in-string (string)
  (declare (xargs :guard (stringp string)
                  :type-prescription (stringp (collapse-whitespace-in-string string))))
  (coerce (collapse-whitespace-in-char-list (coerce string 'list)) 'string))

;; (equal (collapse-whitespace-in-string "a     b c


;;                                        d")
;;        "a b c d")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removes all whitespace.
(defund remove-whitespace-in-char-list (chars)
  (declare (xargs :guard (character-listp chars)))
  (replace-runs chars '(#\Space #\Tab #\Newline #\Return) nil))

(local
  (defthm character-listp-of-remove-whitespace-in-char-list
    (implies (character-listp chars)
             (character-listp (remove-whitespace-in-char-list chars)))
    :hints (("Goal" :in-theory (enable remove-whitespace-in-char-list)))))

;; Removes all whitespace.
(defund remove-whitespace-in-string (string)
  (declare (xargs :guard (stringp string)
                  :type-prescription (stringp (remove-whitespace-in-string string))))
  (coerce (remove-whitespace-in-char-list (coerce string 'list)) 'string))
