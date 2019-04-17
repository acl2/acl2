(in-package "ACL2")

;  block-listp.lisp                                  Mihir Mehta

; Here we define the size of a block to be 8 characters, and define functions
; for making blocks from text and retrieving text from blocks, with proofs of
; their correctness and their one-way inverse relationship.

(local (include-book "file-system-lemmas"))

;; I don't think blocks are 8 characters long in any system; I simply set this
;; in order to actually get fragmentation without having to make unreasonably
;; large examples.
(defconst *blocksize* 8)

;; This fragments a character-list into blocks that are *blocksize*-character
;; long. If the character-list is not exactly aligned to a block boundary, we
;; fill the space with null characters.
;; It will be used in wrchs.
(defund make-blocks (text)
  (declare (xargs :guard (character-listp text)
                  :measure (len text)))
  (if (atom text)
      nil
    (cons (make-character-list (take *blocksize* text))
          (make-blocks (nthcdr *blocksize* text)))))

(defthm
  make-blocks-correctness-5
  (iff (consp (make-blocks text))
       (consp text))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (iff (equal (len (make-blocks text)) 0)
                    (atom text))
    :hints (("goal''" :expand (len (make-blocks text))))))
  :hints (("goal" :in-theory (enable make-blocks))))

;; Characterisation of a disk, which is a list of blocks as described before.
(defun block-listp (block-list)
  (declare (xargs :guard t))
  (if (atom block-list)
      (eq block-list nil)
    (and (character-listp (car block-list))
         (equal (len (car block-list)) *blocksize*)
         (block-listp (cdr block-list)))))

;; Proving that we get a proper block-list out of make-blocks.
(defthm make-blocks-correctness-2
        (implies (character-listp text)
                 (block-listp (make-blocks text)))
        :hints (("Goal" :in-theory (enable make-blocks))))

(defthm block-listp-correctness-1
  (implies (block-listp block-list)
           (true-listp block-list))
  :rule-classes (:forward-chaining))

(defthm block-listp-correctness-2
  (implies (true-listp block-list1)
           (equal (block-listp (binary-append block-list1 block-list2))
                  (and (block-listp block-list1)
                       (block-listp block-list2)))))

;; This function spells out how many characters can be in a file given the
;; number of blocks associated with it. It is kept disabled in order to avoid
;; huge arithmetic-heavy subgoals where they're not wanted.
(defund feasible-file-length-p (index-list-length file-length)
  (declare (xargs :guard (and (natp file-length) (natp index-list-length))))
  (and (> file-length
          (* *blocksize* (- index-list-length 1)))
       (<= file-length
           (* *blocksize* index-list-length))))

;; This is the counterpart of make-blocks that collapses blocks into a
;; character-list of the appropriate length.
;; It will be used in stat and, by extension, in rdchs.
(defun
  unmake-blocks (blocks n)
  (declare
   (xargs
    :guard (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
    :guard-hints
    (("goal" :in-theory (enable feasible-file-length-p)))))
  (if (atom blocks)
      nil
      (if (atom (cdr blocks))
          (take n (car blocks))
          (binary-append (car blocks)
                         (unmake-blocks (cdr blocks)
                                        (- n *blocksize*))))))

;; Proving that we get a proper character-list out provided we don't ask for
;; more characters than we have.
(defthm unmake-blocks-correctness-1
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (character-listp (unmake-blocks blocks n)))
  :hints (("Goal" :in-theory (enable feasible-file-length-p)) ))

(defthm
  unmake-blocks-correctness-2
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (equal (len (unmake-blocks blocks n))
                  n))
  :rule-classes
  ((:rewrite :corollary (implies (and (block-listp blocks)
                                      (natp n)
                                      (feasible-file-length-p (len blocks) n))
                                 (iff (consp (unmake-blocks blocks n))
                                      (not (zp n))))))
  :hints (("goal" :in-theory (enable feasible-file-length-p))
          ("subgoal *1/5'''" :expand (len (cdr blocks)))))

(defthm unmake-make-blocks-lemma-1
        (implies (natp n)
                 (iff (consp (nthcdr n l)) (> (len l) n)))
        :hints (("Goal" :induct (nthcdr n l))))

(encapsulate ()
  (local (include-book "std/lists/repeat" :dir :system))

  ;; Proving that make and unmake are, in a sense, inverse functions of each
  ;; other.
  (defthm
    unmake-make-blocks
    (implies (and (character-listp text))
             (equal (unmake-blocks (make-blocks text)
                                   (len text))
                    text))
    :hints
    (("goal" :in-theory (enable make-blocks))
     ("subgoal *1/3.3"
      :in-theory (disable take-of-make-character-list
                          take-of-too-many)
      :use ((:instance take-of-make-character-list
                       (i (len text))
                       (l (first-n-ac 8 text nil)))
            (:instance take-of-too-many (x text)
                       (n *blocksize*)))))))

;; This is a constant that might be needed later.
;; This is to be returned when a block is not found. It's full of null
;; characters and is *blocksize* long.
(defconst *nullblock* (make-character-list (take *blocksize* nil)))

(defthm
  make-blocks-correctness-1
  (implies (character-listp text)
           (and (< (- (* *blocksize* (len (make-blocks text)))
                      *blocksize*)
                   (len text))
                (not (< (* *blocksize* (len (make-blocks text)))
                        (len text)))))
  :hints (("goal" :in-theory (enable make-blocks)
           :induct t)))

(defthm
  make-blocks-correctness-3
  (implies (and (character-listp cl))
           (feasible-file-length-p (len (make-blocks cl))
                                   (len cl)))
  :hints
  (("goal"
    :in-theory (e/d (feasible-file-length-p)
                    (make-blocks-correctness-1))
    :use (:instance make-blocks-correctness-1 (text cl)))))

(encapsulate ()
  (local (include-book "std/lists/nthcdr" :dir :system))

  (local (defun nthcdr-*blocksize*-induction-2 (text1 text2)
           (cond ((or (atom text1) (atom text2))
                  (list text1 text2))
                 (t (nthcdr-*blocksize*-induction-2 (nthcdr *blocksize* text1)
                                                    (nthcdr *blocksize* text2))))))

  (defthm
    make-blocks-correctness-4
    (implies (equal (len text1) (len text2))
             (equal (len (make-blocks text1))
                    (len (make-blocks text2))))
    :hints (("goal" :in-theory (enable make-blocks)
             :induct (nthcdr-*blocksize*-induction-2 text1 text2)))))

(defthm
  len-of-make-unmake
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (equal (len (make-blocks (unmake-blocks blocks n)))
                  (len blocks)))
  :hints
  (("goal" :in-theory (enable make-blocks feasible-file-length-p))
   ("subgoal *1/8"
    :expand (append (car blocks)
                    (unmake-blocks (cdr blocks) (+ -8 n))))
   ("subgoal *1/5.2" :cases ((atom (cdr blocks))) :expand (len (cdr blocks)))
   ("subgoal *1/5.1'"
    :expand (append (car blocks)
                    (unmake-blocks (cdr blocks) (+ -8 n))))
   ("subgoal *1/2" :expand (make-blocks (first-n-ac n (car blocks) nil)))))
