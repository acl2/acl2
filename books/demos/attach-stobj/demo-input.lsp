; Copyright (C) 2024, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.txt for an overview of this example.

(in-package "ACL2")

; First we redefine comment-window-co so that cw will print to the standard-co
; of state.

(defttag :attach-stobj-demo)
(progn!
 (set-raw-mode t)
 (defun comment-window-co ()
   (standard-co *the-live-state*)))
(defttag nil)

; Set a starting point to undo back through.

(deflabel start)

; Include the book that introduces the mem stobj, and note the rules proved in
; that book (checking that they are redundant).

(include-book "mem")

(set-enforce-redundancy t)
(defthm lookup-update
  (implies (and (mem-indexp i)
                (mem-indexp j))
           (equal (lookup i (update j v mem))
                  (if (equal i j)
                      v
                    (lookup i mem)))))
(defthm update-update-same
  (implies (equal i1 i2)
           (equal (update i2 v2 (update i1 v1 mem))
                  (update i2 v2 mem))))
(defthm update-update-different
  (implies (and (mem-indexp i1)
                (mem-indexp i2)
                (not (equal i1 i2)))
           (equal (update i2 v2 (update i1 v1 mem))
                  (update i1 v1 (update i2 v2 mem)))))
(set-enforce-redundancy nil)

; Now do some evaluation, which should produce output showing the use of array
; operations (see the definitions of lookup$c and update$c in mem.lisp).

; Returns nil,   with output: @@ Calling: (MEM$C-ARI 2 MEM$C)
(lookup 2 mem)

; Returns <mem>, with output: @@ Calling: (UPDATE-MEM$C-ARI 2 TWO MEM$C)
(update 2 'two mem)

; Returns TWO,   with output: @@ Calling: (MEM$C-ARI 2 MEM$C)
(lookup 2 mem)

; Next we do similar testing with mem nested as a field of another stobj, st.

(include-book "nested")

; Returns NIL,   with output: @@ Calling: (MEM$C-ARI 2 MEM$C)
(st-lookup 2 st)

; Returns <st>, with output: @@ Calling: (UPDATE-MEM$C-ARI 2 TWO MEM$C)
(st-update 2 'two st)

; Returns TWO,   with output: @@ Calling: (MEM$C-ARI 2 MEM$C)
(st-lookup 2 st)

; Start over:
(ubt 'start)

; This time include the book in which mem has mem{ht} as an attachment, so that
; exported operations will be hash-table operations rather than array
; operations.

(include-book "mem-as-ht")

; Check that the rules proved for mem are still present (with having to prove
; them again) when including mem-as-ht.lisp.

(set-enforce-redundancy t)
(defthm lookup-update
  (implies (and (mem-indexp i)
                (mem-indexp j))
           (equal (lookup i (update j v mem))
                  (if (equal i j)
                      v
                    (lookup i mem)))))
(defthm update-update-same
  (implies (equal i1 i2)
           (equal (update i2 v2 (update i1 v1 mem))
                  (update i2 v2 mem))))
(defthm update-update-different
  (implies (and (mem-indexp i1)
                (mem-indexp i2)
                (not (equal i1 i2)))
           (equal (update i2 v2 (update i1 v1 mem))
                  (update i1 v1 (update i2 v2 mem)))))
(set-enforce-redundancy nil)

; Now do the evaluation we did before, where this time, they should produce
; output showing the use of hash-table operations (see the definitions of
; lookup{ht}$c and update{ht}$c in mem{ht}.lisp -- those are from the :EXEC
; fields of the stobj mem{ht} that was attached to mem in mem-as-ht.lisp).

; Returns NIL,   with output: @@ Calling: (MEM{HT}$C-HT-GET 2 MEM{HT}$C)
(lookup 2 mem)

; Returns <mem>, with output: @@ Calling: (MEM{HT}$C-HT-PUT 2 TWO MEM{HT}$C)
(update 2 'two mem)

; Returns TWO,   with output: @@ Calling: (MEM{HT}$C-HT-GET 2 MEM{HT}$C)
(lookup 2 mem)

; Next we do similar testing with mem nested as a field of another stobj, st.
; We expect to see that the attachment to mem, mem{ht}, is being used for
; execution, since the stobj mem was introduced in mem-as-ht.lisp after the
; attach-stobj event in that book.

(include-book "nested")

; Returns NIL,   with output: @@ Calling: (MEM{HT}$C-HT-GET 2 MEM{HT}$C)
(st-lookup 2 st)

; Returns <st>, with output: @@ Calling: (MEM{HT}$C-HT-PUT 2 TWO MEM{HT}$C)
(st-update 2 'two st)

; Returns TWO,   with output: @@ Calling: (MEM{HT}$C-HT-GET 2 MEM{HT}$C)
(st-lookup 2 st)

