; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>
;                  Jared Davis <jared@centtech.com>

(in-package "FTY")
(include-book "../deftypes")
(include-book "../basetypes")
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "std/osets/top" :dir :system)
(table xdoc::xdoc 'xdoc::doc nil)

(defun topiclist->names (all-topics)
  (if (atom all-topics)
      nil
    (cons (cdr (assoc :name (car all-topics)))
          (topiclist->names (cdr all-topics)))))

(defun collect-all-topics-with-name (name all-topics)
  (if (atom all-topics)
      nil
    (if (equal (cdr (assoc :name (car all-topics))) name)
        (cons (car all-topics)
              (collect-all-topics-with-name name (cdr all-topics)))
      (collect-all-topics-with-name name (cdr all-topics)))))



; Basic tests of deftypes doc generation

(defmacro grab (topic)
  `(xdoc::find-topic ,topic (xdoc::get-xdoc-table (w state))))

(defmacro assert-parents (topic expect)
  "Ensure that TOPIC exists and has :parents EXPECT"
  (declare (xargs :guard (and (symbolp topic)
                              (symbol-listp expect))))
  `(assert!
    (let ((topic (grab ',topic)))
      (and (or topic
               (cw "Topic ~x0 not found.~%" ',topic))
           (or (equal (cdr (assoc :parents topic)) ',expect)
               (cw "Topic parents for ~x0 are ~x1 instead of ~x2.~%"
                   ',topic
                   (cdr (assoc :parents topic))
                   ',expect))))))

(defmacro assert-short (topic expect)
  "Ensure that TOPIC exists and has EXPECT somewhere in its :short (case insensitive)"
  (declare (xargs :guard (and (symbolp topic)
                              (stringp expect))))
  `(assert!
    (let ((topic (grab ',topic)))
      (and (or topic
               (cw "Topic ~x0 not found.~%" ',topic))
           (or (and (stringp (cdr (assoc :short topic)))
                    (str::isubstrp ',expect (cdr (assoc :short topic))))
               (cw "Topic short for ~x0 is ~x1 instead of ~x2.~%"
                   ',topic
                   (cdr (assoc :short topic))
                   ',expect))))))

(defmacro assert-long (topic expect)
  "Ensure that TOPIC exists and has EXPECT somewhere in its :long (case insensitive)"
  (declare (xargs :guard (and (symbolp topic)
                              (stringp expect))))
  `(assert!
    (let ((topic (grab ',topic)))
      (and (or topic
               (cw "Topic ~x0 not found.~%" ',topic))
           (or (and (stringp (cdr (assoc :long topic)))
                    (str::isubstrp ',expect (cdr (assoc :long topic))))
               (cw "Topic long for ~x0 is ~x1 instead of ~x2.~%"
                   ',topic
                   (cdr (assoc :long topic))
                   ',expect))))))

(defmacro assert-dupefree ()
  `(assert! (let ((dupes (acl2::duplicated-members
                          (topiclist->names
                           (set::mergesort (xdoc::get-xdoc-table (w state)))))))
              (or (not dupes)
                  (cw "Found duplicated topics for ~x0~%" dupes)))))




(defxdoc game
  :parents (top)
  :short "Pretend game that will be used for deftypes doc testing.")

(assert-dupefree)


(defprod monster
  :parents (game)
  :short "A monster to fight."
  :tag :monster
  ((name   stringp  "Name of the monster.")
   (health natp     "How much health the monster has.")
   (magicp booleanp "Does the monster have magic powers?")
   (extra  posp     ;; Some extra field that we forgot to document
           ))
  :long "<p>Monsters are scary.</p>")

(assert-parents monster (game))
(assert-short monster "A monster to fight")
(assert-long monster "Name of the monster")
(assert-long monster "How much health the monster has")
(assert-long monster "Does the monster have magic powers")
(assert-long monster "extra")
(assert-long monster "Monsters are scary")

(assert-parents monster-fix (monster))
(assert-short monster-fix "")
(assert-long monster-fix "@(def")

(assert-parents make-monster (monster))
(assert-short make-monster "")
(assert-long make-monster "")

(assert-parents change-monster (monster))
(assert-short change-monster "")
(assert-long change-monster "")

(assert-parents monster->name (monster))
(assert-short monster->name "")
(assert-long monster->name "")

(assert-parents monster->extra (monster))
(assert-short monster->extra "")
(assert-long monster->extra "")

(assert-dupefree)


(defprod monsterpair
  :parents (game)
  :short "Two monsters, side by side."
  :tag :monsterpair
  ((left   monster "Monster on the left.")
   (right  monster "Monster on the right.")))

(assert-parents monsterpair (game))
(assert-short monsterpair "Two monsters")
(assert-long monsterpair "Monster on the left")
(assert-long monsterpair "Monster on the right")


(deflist monsterlist
  :parents (monster)
  :short "A list of monsters."
  :elt-type monster)

(assert-parents monsterlist (monster))
(assert-short monsterlist "A list of monsters")

(assert-parents monsterlist-p (monsterlist))
(assert-short monsterlist-p "")
(assert-long monsterlist-p "")

(assert-parents monsterlist-fix (monsterlist))
(assert-short monsterlist-fix "")
(assert-long monsterlist-fix "")


(deflist monsterlist2
  :parents (monster)
  :elt-type monster)

(assert-parents monsterlist2 (monster))
(assert-short monsterlist2 "")

(assert-parents monsterlist2-p (monsterlist2))
(assert-short monsterlist2-p "")
(assert-long monsterlist2-p "")

(assert-parents monsterlist2-fix (monsterlist2))
(assert-short monsterlist2-fix "")
(assert-long monsterlist2-fix "")


(deflist monsterlist3
  :elt-type monster)

(assert-parents monsterlist3 (acl2::undocumented))
(assert-short monsterlist3 "")

(assert-parents monsterlist3-p (monsterlist3))
(assert-short monsterlist3-p "")
(assert-long monsterlist3-p "")

(assert-parents monsterlist3-fix (monsterlist3))
(assert-short monsterlist3-fix "")
(assert-long monsterlist3-fix "")



(defoption maybe-monster
  monster
  :parents (game)
  :short "The kind of monster under my kids' beds."
  :long "<p>It might be there.  Honest.</p>")

(assert-parents maybe-monster (game))
(assert-short maybe-monster "kind of monster under")
(assert-long maybe-monster "might be there")

(assert-parents maybe-monster-p (maybe-monster))
(assert-short maybe-monster-p "")
(assert-long maybe-monster-p "")

(assert-parents maybe-monster-fix (maybe-monster))
(assert-short maybe-monster-fix "")
(assert-long maybe-monster-fix "")

(assert-parents maybe-monster-equiv (maybe-monster))
(assert-short maybe-monster-equiv "")
(assert-long maybe-monster-equiv "")


(defoption maybe-monster2
  monster)

(assert-parents maybe-monster2 (undocumented))
(assert-short maybe-monster2 "")
(assert-long maybe-monster2 "")

(assert-parents maybe-monster2-p (maybe-monster2))
(assert-short maybe-monster2-p "")
(assert-long maybe-monster2-p "")

(assert-parents maybe-monster2-fix (maybe-monster2))
(assert-short maybe-monster2-fix "")
(assert-long maybe-monster2-fix "")

(assert-parents maybe-monster2-equiv (maybe-monster2))
(assert-short maybe-monster2-equiv "")
(assert-long maybe-monster2-equiv "")


(defoption maybe-monster3
  monster
  :parents (game))

(assert-parents maybe-monster3 (game))
(assert-short maybe-monster3 "")
(assert-long maybe-monster3 "")

(assert-parents maybe-monster3-p (maybe-monster3))
(assert-short maybe-monster3-p "")
(assert-long maybe-monster3-p "")

(assert-parents maybe-monster3-fix (maybe-monster3))
(assert-short maybe-monster3-fix "")
(assert-long maybe-monster3-fix "")

(assert-parents maybe-monster3-equiv (maybe-monster3))
(assert-short maybe-monster3-equiv "")
(assert-long maybe-monster3-equiv "")




(defalist monster-scoreboard
  :key-type monster
  :val-type natp
  :parents (game)
  :short "How many points each monster has."
  :long "<p>Wait, why are <i>monsters</i> getting points?  What kind of a game
is this?</p>")

(assert-parents monster-scoreboard (game))
(assert-short monster-scoreboard "points each monster has")
(assert-long monster-scoreboard "Wait, why are <i>monsters</i>")

(assert-parents monster-scoreboard-p (monster-scoreboard))
(assert-short monster-scoreboard-p "")
(assert-long monster-scoreboard-p "")

(assert-parents monster-scoreboard-fix (monster-scoreboard))
(assert-short monster-scoreboard-fix "")
(assert-long monster-scoreboard-fix "")

(assert-parents monster-scoreboard-equiv (monster-scoreboard))
(assert-short monster-scoreboard-equiv "")
(assert-long monster-scoreboard-equiv "")


(defalist monster-scoreboard2
  :key-type monster
  :val-type natp)

(assert-parents monster-scoreboard2 (undocumented))
(assert-short monster-scoreboard2 "")
(assert-long monster-scoreboard2 "")

(assert-parents monster-scoreboard2-p (monster-scoreboard2))
(assert-short monster-scoreboard2-p "")
(assert-long monster-scoreboard2-p "")

(assert-parents monster-scoreboard2-fix (monster-scoreboard2))
(assert-short monster-scoreboard2-fix "")
(assert-long monster-scoreboard2-fix "")

(assert-parents monster-scoreboard2-equiv (monster-scoreboard2))
(assert-short monster-scoreboard2-equiv "")
(assert-long monster-scoreboard2-equiv "")


(encapsulate
  ()
  (local (xdoc::set-default-parents game))
  (defalist monster-scoreboard3
    :key-type monster
    :val-type natp))

(assert-parents monster-scoreboard3 (game))
(assert-parents monster-scoreboard3-p (monster-scoreboard3))
(assert-parents monster-scoreboard3-fix (monster-scoreboard3))
(assert-parents monster-scoreboard3-equiv (monster-scoreboard3))



(defprod player
  :parents (game)
  :short "Someone who is playing the game."
  :tag :player
  ((name   stringp  "Name of the player.")
   (health natp     "How much health the monster has."))
  :long "<p>Most players won't last long.</p>")

(assert-parents player (game))


(deftranssum drawable
  :parents (game)
  :short "Things that can be visible on the screen and need to be drawn."
  :long "<p>It's not clear this is a good idea.</p>"
  (monster
   player))

(assert-parents drawable (game))
(assert-short drawable "visible on the screen")
(assert-long drawable "this is a good idea")

(assert-parents drawable-fix (drawable))
(assert-short drawable-fix "")
(assert-long drawable-fix "")

(assert-parents drawable-equiv (drawable))
(assert-short drawable-equiv "")
(assert-long drawable-equiv "")

;; (assert-parents drawable-kind (drawable))
;; (assert-short drawable-kind "")
;; (assert-long drawable-kind "")



(defmap prison
  :key-type player
  :val-type natp
  :parents (game)
  :short "The prison where monsters try to take the players."
  :long "<p>Maps players to how long they have been in jail (picoseconds).</p>")

(assert-parents prison (game))
(assert-short prison "where monsters try to take the players")
(assert-long prison "how long they have been in jail")

(assert-parents prison-fix (prison))
(assert-short prison-fix "")
(assert-long prison-fix "")

(assert-parents prison-equiv (prison))
(assert-short prison-equiv "")
(assert-long prison-equiv "")



(deftagsum castle
  :parents (game)
  :short "Maybe players and monsters can fight over castles."
  :long "<p>Either way, the alligators get lunch.</p>"
  (:bricks
   :short "A castle made of bricks."
   :long "<p>Bricks are a pretty good choice.</p>"
   ((height natp "How tall is the castle?")
    (alligators natp "How many alligators in the water?")))
  (:straw
   :short "A castle made of straw."
   :long "<p>Preferred by certain little pigs.</p>"
   ((npigs natp "Number of pigs inside."))))

(assert-parents castle (game))
(assert-short castle "players and monsters can fight over castles")
(assert-long castle "alligators get lunch")

(assert-parents castle-p (castle))
(assert-short castle-p "")
(assert-long castle-p "")

(assert-parents castle-fix (castle))
(assert-short castle-fix "")
(assert-long castle-fix "")

(assert-parents castle-equiv (castle))
(assert-short castle-equiv "")
(assert-long castle-equiv "")

(assert-parents castle-kind (castle))
(assert-short castle-kind "")
(assert-long castle-kind "")

(assert-parents castle-bricks (castle))
(assert-short castle-bricks "A castle made of bricks")
(assert-long castle-bricks "good choice")

(assert-parents make-castle-bricks (castle-bricks))
(assert-parents change-castle-bricks (castle-bricks))
(assert-parents castle-bricks->alligators (castle-bricks))
(assert-parents castle-bricks->height (castle-bricks))

(assert-parents castle-straw (castle))
(assert-short castle-straw "A castle made of straw")
(assert-long castle-straw "little pigs")
(assert-parents make-castle-straw (castle-straw))
(assert-parents change-castle-straw (castle-straw))
(assert-parents castle-straw->npigs (castle-straw))

(assert-parents castle-case (castle))
(assert-short castle-case "")
(assert-long castle-case "")

(assert-dupefree)



(defprod monster->arrow
  :parents (game)
  :short "A test of arrows."
  :tag :monster
  ((cow->moo stringp  "An arrow in a field."))
  :long "<p>Arrows cause escaping problems.</p>")

(assert-parents monster->arrow (game))

(assert-dupefree)


(deftranssum monstermash
  :parents (game)
  :short "It caught on in a flash."
  :long "<p>It was a graveyard smash.</p>"
  (monster
   monsterpair))


(assert-parents monstermash (game))
(assert-parents monstermash-p (monstermash))
(assert-parents monstermash-fix (monstermash))
(assert-parents monstermash-equiv (monstermash))
;; (assert-parents monstermash-case (monstermash))
;; (assert-parents monstermash-kind (monstermash))

(assert-dupefree)


;; (include-book "xdoc/save" :dir :system)
;; (xdoc::save "./my-manual")
