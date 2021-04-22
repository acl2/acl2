; An xdoc constructor for a list of paragraphs
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable mv-nth)))

(defund skip-newlines (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (if (eql #\Newline (first chars))
        (skip-newlines (rest chars))
      chars)))

(defthm character-listp-of-skip-newlines
  (implies (character-listp chars)
           (character-listp (skip-newlines chars)))
  :hints (("Goal" :in-theory (enable skip-newlines))))

(local
 (defthm <=-of-len-of-skip-newlines
  (<= (len (skip-newlines chars))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable skip-newlines)))))

;; Returns (mv chars-before-double-newline chars-after-double-newline
(defund split-chars-at-double-newline (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))))
  (if (endp chars)
      (mv (reverse acc)
          nil)
    (if (eql #\Newline (first chars))
        (if (endp (rest chars))
            ;; drop final newline
            (mv (reverse acc)
                nil)
          (if (eql #\Newline (first (rest chars)))
              (mv (reverse acc)
                  (rest (rest chars))) ;skip both newlines
            (split-chars-at-double-newline (rest chars) (cons (first chars) acc))))
      (split-chars-at-double-newline (rest chars) (cons (first chars) acc)))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-split-chars-at-double-newline
  (<= (len (mv-nth 1 (split-chars-at-double-newline chars acc)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable split-chars-at-double-newline)))))

(local
 (defthm <-of-len-of-mv-nth-1-of-split-chars-at-double-newline
   (implies (consp chars)
            (< (len (mv-nth 1 (split-chars-at-double-newline chars acc)))
               (len chars)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable split-chars-at-double-newline)))))

(local
 (defthm character-listp-of--mv-nth-0-of-split-chars-at-double-newline
   (implies (and (character-listp chars)
                 (character-listp acc))
            (character-listp (mv-nth 0 (split-chars-at-double-newline chars acc))))
   :hints (("Goal" :in-theory (enable split-chars-at-double-newline)))))

(local
 (defthm character-listp-of--mv-nth-1-of-split-chars-at-double-newline
   (implies (and (character-listp chars)
                 (character-listp acc))
            (character-listp (mv-nth 1 (split-chars-at-double-newline chars acc))))
   :hints (("Goal" :in-theory (enable split-chars-at-double-newline)))))

(defund xdoc::paras-aux (chars)
  (declare (xargs :guard (character-listp chars)
                  :measure (len chars)))
  (let ((chars (skip-newlines chars)))
    (if (endp chars)
        nil
      (mv-let (chars-before-double-newline chars-after-double-newline)
        (split-chars-at-double-newline chars nil)
        (cons `(xdoc::p ,(coerce chars-before-double-newline 'string))
              (xdoc::paras-aux chars-after-double-newline))))))

;; Returns a list of calls to xdoc::p, one for each paragraph (separated by newlines) in STR.
(defund xdoc::paras (str)
  (declare (xargs :guard (stringp str)))
  (xdoc::paras-aux (coerce str 'list)))

;; Splits STR into paragraphs at blank lines.
;; Returns a "top-level" xdoc string suitable for use as a :short or :long string.
(defmacro xdoc::topparas (str)
  (declare (xargs :guard (stringp str)))
  `(xdoc::topstring (xdoc::&& ,@(xdoc::paras str))))

;; Make an ordered list, given a string, interpreting blank lines as separators between list items
(defmacro xdoc::ol-from-string (str)
  (declare (xargs :guard (stringp str)))
  `(xdoc::ol (xdoc::topparas ,str)))
