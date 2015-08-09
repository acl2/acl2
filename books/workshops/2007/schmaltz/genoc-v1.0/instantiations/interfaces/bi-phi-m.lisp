;; Julien Schmaltz
;; definition of the send side of the biphase mark protocol
;; definition taken from Moore's paper


(in-package "ACL2")


(defun listn (n x)
  ;; makes a list of n copies of x
  (if (zp n)
      nil
    (cons x (listn (1- n) x))))


;; Sending
;; -------

;; Moore wrote:
;; "A cell encodes one bit, b, of the message, but the encoding depends
;; upon the signal, x, output immediately before the cell.
;; Let csig be x if b is t and not(x) otherwise.
;; Then a cell is defined as the concatenation of a "mark" subcell containing n
;; repetitions of not(x), followed by a "code" subcell containing k repetitions
;; of csig."

(defun csig (x b)
  (if b x (not x)))

(defun cell (x n k bit)
  ;; encodes bit in a cell of size n+k
  (append (listn n (not x))
          (listn k (csig x bit))))

;; "To encode a bit vector, msg, with cell size n+k, assuming
;; that the previously otput signal is x we merely concatenate
;; successive cells, being careful to pass the correct value
;; for the "previous signal"."
(defun cells (x n k msg)
  (if (endp msg)
      nil
    (append (cell x n k (car msg))
            (cells (csig x (car msg)) n k (cdr msg)))))

;; "We adopt the convention that the sender holds the line high
;; before and after the message is sent. Thus, on either side
;; of the encoded cells we include "pads" of t, of arbitrary
;; lengths p1 and p2.
;(defun send (msg p1 n k p2)
;  (append (listn p1 t)
;          (append (cells t n k msg) (listn p2 t))))

(defun send (msg p1 n k flg)
  ;; I consider a more general function, that takes the initial
  ;; signal as a parameter
  (append (listn p1 flg)
          (cells flg n k msg)))


;; Receiving
;; ---------

;; "Scan takes a signal x, and a list of signals, lst, and
;; scans lst until it finds the first signal different from x.
;; If lst happens to begin with a string of xs, scan finds the
;; first edge."
(defun scan (x lst)
  (if (endp lst)
      nil
    (if (xor x (car lst))
        lst
      (scan x (cdr lst)))))

;; "Recv-bit is the function that recovers the bit encoded in a
;; cell. It takes two arguments. The first is the 0-based sampling
;; distance, j, at which it is supposed to sample [...].
;; The second argument is the list of signals, starting with the
;; first signal in the mark subcell of the cell."
(defun recv-bit (k lst)
  ;; "The bit received is t if the first signal of the mark is
  ;; different from the signal sampled in the code subcell;
  ;; otherwise the bit received is f."
  (if (xor (car lst) (nth k lst))
      t
    nil))

;; The receive function receives i bits.
;; "The list of signals on which recv operates should be thought
;; of as starting with the signal, x, sampled in the code subcell
;; of previous cell. If i is 0, the empty message is recovered.
;; Otherwise, recv scans to the next edge (i.e., it scans past the
;; initial xs to get past the code subcell of the previous cell
;; and to the mark of the next cell). Recv then used recv-bit
;; to recover the bit in that cell and conses it to the result
;; of recursively recovering i - 1 more bits."

(defun recv (i x k lst)
  (if (zp i)
      nil
    (cons (recv-bit k (scan x lst))
          (recv (1- i) (nth k (scan x lst))
                k (nthcdr k (scan x lst))))))
;; Correctness
;; -----------

(defun bvp (x)
  (if (endp x)
      t
    (and (booleanp (car x))
         (bvp (cdr x)))))


;; I remove the end of the line .... does not seem to be necessary

;; I load books on lists
(include-book "data-structures/list-defuns" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)

;; I load the book for arithmetic
(include-book "arithmetic-3/bind-free/top" :dir :system)

;; we want to prove that the composition of send and recv
;; is an identity.

(defthm car-cells
  ;; if the size of the cells is properly set up and
  ;; if there is at least one bit in the message
  ;; the first bit of the cell is the opposite of the previous
  ;; signal on the line.
  (implies (and (booleanp flg) (integerp n) (integerp k)
                (< 0 n) (< 0 k) (consp msg))
           (xor flg (car (cells flg n k msg)))))

(defthm scan-cells-cancel
  ;; if scan works properly then if applied to a list of cells
  ;; it returns this list of cells
  (implies (and (booleanp flg) (integerp n) (integerp k)
                (< 0 n) (< 0 k) (consp msg))
           (equal (scan flg (cells flg n k msg))
                  (cells flg n k msg))))

;; using this rule we could prove theorems on cells only

(defthm true-listp-cells
  ;; cells returns a true-listp
  (true-listp (cells flg n k msg))
  :rule-classes :type-prescription)

(defthm bvp-cells
  ;; if flg is a Boolean and lst a list of Booleans, then
  ;; cells is still a list of Booleans.
  (implies (and (bvp msg) (booleanp flg))
           (bvp (cells flg n k msg))))

(defthm consp-cells
  (implies (and (consp msg) (integerp n) (integerp k)
                (< 0 n) (<= 0 k))
           (consp (cells flg n k msg))))

(defthm len-listn
  (implies (and (integerp n) (<= 0 n))
           (equal (len (listn n x)) n)))

(defun induct-i-k (i k)
  (if (or (zp i) (zp k))
      0
    (induct-i-k (1- i) (1- k))))

(defthm car-listn
  (implies (and (integerp k) (< 0 k))
           (equal (car (listn k x)) x))
  :hints (("Subgoal *1/3"
           :expand (listn 1 x))))

(defthm consp-listn
  (implies (and (integerp k) (< 0 k))
           (consp (listn k x)))
  :hints (("GOAL"
           :expand (listn 1 x))))

(defthm nth-listn
  (implies (and (integerp i) (<= 0 i) (< i k) (integerp k))
           (equal (nth i (listn k x)) x))
  :hints (("GOAL"
           :do-not-induct t
           :induct (induct-i-k i k))))

(defthm scan-cells-nth
  ;; if rclock is in the code cell (n <= rclock < k) then
  ;; the rclock'th bit of scan is the first coded bit
  (implies (and (integerp rclock) (<= n rclock)
                (< rclock (+ n k))
                (integerp n) (< 0 n) (integerp k) (< 0 k)
                (booleanp flg) (bvp msg) (consp msg))
           (equal (nth rclock (cells flg n k msg))
                  (csig flg (car msg))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable REMOVE-WEAK-INEQUALITIES-ONE)
           :induct (cells flg n k msg))))

(defthm car-append
  (implies (consp a)
           (equal (car (append a b))
                  (car a))))

(defthm recv-bit-first-cell
  (implies (and (integerp rclock) (<= n rclock)
                (< rclock (+ n k))
                (integerp n) (< 0 n) (integerp k) (< 0 k)
                (booleanp flg) (bvp msg) (consp msg))
           (equal (recv-bit rclock (cells flg n k msg))
                  (car msg)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t)))

(in-theory (disable recv-bit))

(defthm nthcdr-listn
  (implies (and (integerp i) (integerp k) (< 0 k) (<= 0 i)
                (<= i k))
           (equal (nthcdr i (listn k bit))
                  (listn (- k i) bit))))

(defthm scan-cells-nthcdr
  ;; if rclock is in the code cell (n <= rclock < k) then
  ;; the msg after rclock is an append of n+k-rclock coded
  ;; signals and the next cell.
  (implies (and (integerp rclock) (<= n rclock)
                (< rclock (+ n k))
                (integerp n) (< 0 n) (integerp k) (< 0 k)
                (booleanp flg) (bvp msg) (consp msg))
           (equal (nthcdr rclock (cells flg n k msg))
                  (append (listn (- (+ n k) rclock)
                                 (csig flg (car msg)))
                          (cells (csig flg (car msg)) n k
                                 (cdr msg)))))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t
           :induct (cells flg n k msg))))


(defthm recv-cells-base-case-1
  (implies (and (not (consp msg)) (true-listp msg))
           (equal (recv (len msg) flg rclock (cells flg n k msg))
                  msg)))

(defthm true-listp-scan
  (implies (true-listp msg)
           (true-listp (scan flg msg)))
  :rule-classes :type-prescription)

(defthm bvp-scan
  (implies (bvp msg)
           (bvp (scan flg msg))))

(defthm bvp-nthcdr
  (implies (bvp msg)
           (bvp (nthcdr n msg)))
  :hints (("GOAL"
           :in-theory (disable prefer-positive-addends-<))))


(defthm scan-append
  (equal (scan flg (append (listn n flg) lst))
         (scan flg lst)))

(defthm recv-append
  (equal (recv i flg rclock (append (listn n flg) msg))
         (recv i flg rclock msg)))

(defthm recv-cells
  (implies (and (integerp rclock) (<= n rclock)
                (< rclock (+ n k))
                (true-listp msg)
                (integerp n) (< 0 n) (integerp k) (< 0 k)
                (booleanp flg) (bvp msg) (consp msg))
           (equal (recv (len msg) flg rclock (cells flg n k msg))
                  msg))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :expand (recv 1 flg rclock (cells flg n k msg))
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable (:definition cells))
           :induct (cells flg n k msg))))

(defthm recv-send-is-id
  (implies (and (integerp rclock) (<= n rclock)
                (< rclock (+ n k))
                (true-listp msg) (natp p1)
                (integerp n) (< 0 n) (integerp k) (< 0 k)
                (booleanp flg) (bvp msg) (consp msg))
           (equal (recv (len msg) flg rclock
                        (send msg p1 n k flg))
                  msg))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize fertilize)
           :cases ((and (consp msg) (consp (cdr msg))))
           :expand (recv 1 flg rclock (cells flg n k msg))
           :in-theory (disable recv len)
           :do-not-induct t)
          ("Subgoal 2"
           :in-theory (enable len))))
