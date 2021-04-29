; Documentation for lists-light library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)
;(include-book "all-true-listp")

(defxdoc lists-light
  :short "A lightweight library for lists."
  :parents (kestrel-books lists)
  :long
   (xdoc::topstring
    (xdoc::&&
     (xdoc::topparas
      "This library covers many built-in list operations as well as many additional list functions defined in the library itself.  Specifically, it covers the built-in functions:")

     (xdoc::ul-from-string
      "cons
car

cdr

nthcdr

take

len

true-list-fix

reverse

first-n-ac

member-equal

subsetp-equal

last

nth

update-nth

no-duplicatesp-equal

butlast

append

revappend

remove-duplicates-equal

remove-equal

remove1-equal

union-equal

intersection-equal

add-to-set-equal

set-difference-equal

subsequencep")

     (xdoc::topparas "It also defines these functions and includes rules about them:")

     (xdoc::ul-from-string
      "find-index

firstn

repeat

reverse-list

memberp

perm

repeat-tail

subrange

subsequencep-equal

update-nth2

last-elem

finalcdr

all-equal$

all-eql$

all-same

all-same-eql

update-subrange

add-to-end

first-non-member

count-occs

prefixp

len-at-least

group

ungroup

append-with-key

list-equiv")

     (xdoc::topparas "The library is located in <tt>[books]/kestrel/lists-light/</tt>.  It is being developed in a lightweight style that minimizes dependencies.  See the individual files for details."))))

;; (gen-xdoc-for-file "all-true-listp.lisp"
;;                    ((all-true-listp "Recognize a list of true-lists"))
;;                    (typed-lists-light))

;; TODO: Add documentation for other files.
