; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Attachable stobjs and the :congruent-to keyword

(in-package "ACL2")

(include-book "gen-support")

(include-book "impl") ; includes book defining must-fail

(encapsulate
  ()

  (local (attach-stobj st nil)) ; This undoes the attach-stobj in impl.lisp.

; As expected, st is not congruent to st{impl} when st has no attachment.

  (must-fail (defabsstobj st
               :exports ((lookup :exec mem$ci)
                         (update :exec update-mem$ci)
                         (misc :exec misc$c+)
                         update-misc)
               :congruent-to st{impl}
               :attachable t)))

; Here we modify what is provided in gen.lisp, by adding :congruent-to.
(defabsstobj st
  :exports ((lookup :exec mem$ci)
            (update :exec update-mem$ci)
            (misc :exec misc$c+)
            update-misc)
  :congruent-to st{impl}
  :attachable t)

(attach-stobj st3 st{impl})

; The :congruent-to keyword avoids the need to prove the usual lemmas, because
; the event is justified by the lemmas already proved for the congruent stobj,
; because congruence implies the same foundation as well as correspondence of
; the various :logic and :exec fields of the primitives.  By contrast, an
; attachment need not agree on the foundation or :exec fields, so attachment
; does not remove the need to prove such lemmas.

(must-fail
 (defabsstobj st3
   :foundation st$c
   :recognizer (st3p :logic st$ap :exec st$cp)
   :creator (create-st3 :logic create-st$a :exec create-st$c)
   :corr-fn st$corr
   :exports ((lookup3 :logic lookup$a :exec mem$ci)
             (update3 :logic update$a :exec update-mem$ci)
             (misc3 :logic misc$a :exec misc$c+)
             (update-misc3 :logic update-misc$a :exec update-misc$c))
; Need this to avoid failure due to missing lemmas (commented out here):
;  :congruent-to st{impl}
   :attachable t))

(defabsstobj st3
  :foundation st$c
  :recognizer (st3p :logic st$ap :exec st$cp)
  :creator (create-st3 :logic create-st$a :exec create-st$c)
; The :corr-fn keyword can be omitted when :congruent-to supplies a congruent
; stobj.
; :corr-fn st$corr
  :exports ((lookup3 :logic lookup$a :exec mem$ci)
            (update3 :logic update$a :exec update-mem$ci)
            (misc3 :logic misc$a :exec misc$c+)
            (update-misc3 :logic update-misc$a :exec update-misc$c))
; Need this to avoid failure due to missing lemmas:
  :congruent-to st{impl}
  :attachable t)
