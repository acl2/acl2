; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "cat")
(local (include-book "misc/take" :dir :system))
(local (include-book "arithmetic"))

(defsection pad-trim
  :parents (str)
  :short "Functions for trimming whitespace and padding with spaces.")

(defsection rpadchars
  :parents (pad-trim)
  :short "Pad a character-list with spaces on the right."

  :long "<p>@(call rpadchars) extends the character list @('x') to length
@('len') by adding spaces on the right.  For instance,</p>

@({
  (rpadchars '(#\\f #\\o #\\o) 5)
     --&gt;
  '(#\\f #\\o #\\o #\\Space #\\Space)
})

<p>This is completely dumb: we don't try to account for newlines, tabs, or
anything like that, and just add @('#\\Space') characters until reaching the
desired width.</p>

<p>If no new spaces are needed, @('x') is returned unchanged and no consing is
performed.</p>"

  (defund rpadchars (x len)
    (declare (xargs :guard (and (character-listp x)
                                (natp len))
                    :guard-hints (("Goal" :in-theory (enable acl2::repeat))))
             (type integer len))
    (mbe :logic
         (append x (make-list (nfix (- (nfix len) (len x)))
                              :initial-element #\Space))
         :exec
         (let* ((x-len (length (the list x)))
                (diff  (- len x-len)))
           (if (> diff 0)
               (append x (make-list diff :initial-element #\Space))
             x))))

  (local (in-theory (enable rpadchars)))

  (defthm character-listp-of-rpadchars
    (implies (force (character-listp x))
             (character-listp (rpadchars x len))))

  (defthm len-of-rpadchars
    (equal (len (rpadchars x len))
           (max (len x) (nfix len)))))


(defsection rpadstr
  :parents (pad-trim)
  :short "Pad a string with spaces on the right."

  :long "<p>@(call rpadstr) extends the string @('x') to length @('len') by
adding spaces on the right.  For instance,</p>

@({
  (rpadchars \"foo\" 5)
     --&gt;
  \"foo  \"
})

<p>This is completely dumb: we don't try to account for newlines, tabs, or
anything like that, and just add @('#\\Space') characters until reaching the
desired width.</p>

<p>If no new spaces are needed, @('x') is returned unchanged and no consing or
coercion is performed.</p>"

  (local (in-theory (enable rpadchars append-chars)))

  (defund rpadstr (x len)
    (declare (xargs :guard (and (stringp x)
                                (natp len))
                    :guard-debug t)
             (type string x)
             (type integer len))
    (mbe :logic
         (coerce (rpadchars (coerce x 'list) len) 'string)
         :exec
         (let* ((x-len (length (the string x)))
                (diff  (- len x-len)))
           (if (> diff 0)
               (let ((spaces (make-list diff :initial-element #\Space)))
                 (coerce (mbe :logic (append-chars x spaces)
                              :exec (if (zp x-len)
                                        spaces
                                      (append-chars-aux x (- x-len 1) spaces)))
                         'string))
             x))))

  (local (in-theory (enable rpadstr)))

  (defthm stringp-of-rpadstr
    (stringp (rpadstr x len))
    :rule-classes :type-prescription)

  (defthm len-of-coerce-of-rpadstr
    (implies (force (stringp x))
             (equal (len (coerce (rpadstr x len) 'list))
                    (max (length x)
                         (nfix len))))))


(defsection lpadchars
  :parents (pad-trim)
  :short "Pad a character-list with spaces on the left."

  :long "<p>@(call lpadchars) extends the character list @('x') to length
@('len') by adding spaces on the left.  For instance,</p>

@({
  (lpadchars '(#\\f #\\o #\\o) 5)
     --&gt;
  '(#\\Space #\\Space #\\f #\\o #\\o)
})

<p>This is completely dumb: we don't try to account for newlines, tabs, or
anything like that, and just add @('#\\Space') characters until reaching the
desired width.</p>

<p>If no new spaces are needed, @('x') is returned unchanged and no consing is
performed.</p>"

  (defund lpadchars (x len)
    (declare (xargs :guard (and (character-listp x)
                                (natp len)))
             (type integer len))
    (mbe :logic
         (append (make-list (nfix (- (nfix len) (len x)))
                            :initial-element #\Space)
                 x)
         :exec
         (let* ((x-len (length x))
                (diff  (- len x-len)))
           (if (< 0 diff)
               (make-list-ac diff #\Space x)
             x))))

  (local (in-theory (enable lpadchars)))

  (defthm character-listp-of-lpadchars
    (implies (force (character-listp x))
             (character-listp (lpadchars x len))))

  (defthm len-of-lpadchars
    (equal (len (lpadchars x len))
           (max (len x) (nfix len)))))


(defsection lpadstr
  :parents (pad-trim)
  :short "Pad a string with spaces on the left."

  :long "<p>@(call lpadstr) extends the string @('x') to length @('len') by
adding spaces on the left.  For instance,</p>

@({
  (lpadstr \"foo\" 5)
     --&gt;
  \"  foo\"
})

<p>This is completely dumb: we don't try to account for newlines, tabs, or
anything like that, and just add @('#\\Space') characters until reaching the
desired width.</p>

<p>If no new spaces are needed, @('x') is returned unchanged and no consing is
performed.</p>"

  (local (in-theory (enable lpadchars)))

  (defund lpadstr (x len)
    (declare (xargs :guard (and (stringp x)
                                (natp len)))
             (type string x)
             (type integer len))
    (mbe :logic
         (coerce (lpadchars (coerce x 'list) len) 'string)
         :exec
         (let* ((x-len (length x))
                (diff  (- len x-len)))
           (if (< 0 diff)
               (coerce (make-list-ac diff #\Space (coerce x 'list)) 'string)
             x))))

  (local (in-theory (enable lpadstr)))

  (defthm stringp-of-lpadstr
    (stringp (lpadstr x len))
    :rule-classes :type-prescription)

  (defthm len-of-coerce-of-lpadstr
    (implies (force (stringp x))
             (equal (len (coerce (lpadstr x len) 'list))
                    (max (length x)
                         (nfix len))))))


(defsection trim
  :parents (pad-trim)
  :short "Remove whitespace from the front and end of a string."

  :long "<p>@(call trim) removes whitespace characters from the front and end
of the string @('x').</p>

<p>BOZO eventually make this efficient.</p>"

  (defund trim-aux (x)
    (declare (xargs :guard (character-listp x)))
    ;; Remove all whitespace characters from the front of a list.
    (if (consp x)
        (if (or (eql (car x) #\Space)
                (eql (car x) #\Tab)
                (eql (car x) #\Newline)
                (eql (car x) #\Page)
                (eql (car x) (code-char 13)) ;; Carriage Return
                (eql (car x) (code-char 11)) ;; Vertical Tab
                )
            (trim-aux (cdr x))
          x)
      nil))

  (local (in-theory (enable trim-aux)))

  (defthm character-listp-of-trim-aux
    (implies (force (character-listp x))
             (character-listp (trim-aux x))))

  (local (defthm true-listp-when-character-listp
           (implies (character-listp x)
                    (true-listp x))))

  (defund trim (x)
    (declare (xargs :guard (stringp x)))
    (let* ((chars (coerce x 'list))
           (chars (trim-aux chars)) ;; eat spaces at the front
           (chars (reverse chars))  ;; flip so we can get to the back
           (chars (trim-aux chars)) ;; eat spaces at the back
           (chars (reverse chars))) ;; flip again so it's back to normal
      (coerce chars 'string)))

  (local (in-theory (enable trim)))

  (defthm stringp-of-trim
    (stringp (trim x))
    :rule-classes :type-prescription))
