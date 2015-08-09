(in-package "ACL2")

;;;; we will need a book on record ops and theorems

(include-book "records")
(include-book "../../../../ordinals/e0-ordinal")

#|----------------------------------------------------------------------------|#

;;;; BEGIN auxiliary definitions ;;;;

(defun add-set (e x)
  (if (member e x) x (cons e x)))

(defun add-in-range (lo hi x)
  (declare (xargs :measure (nfix (1+ (- hi lo)))))
  (if (and (integerp hi)
           (integerp lo)
           (<= lo hi))
      (add-in-range lo (1- hi) (add-set hi x))
    x))

(defun add-nums-in (case x)
  (cond ((endp (cdr case)) x)
        ((consp (car case))
         (add-in-range (caar case)
                       (cadar case)
                       (add-nums-in (cdr case) x)))
        (t (add-set (car case)
                    (add-nums-in (cdr case) x)))))

(defun locase-nums (cases)
  (if (endp cases) ()
    (add-nums-in (car cases)
                 (locase-nums (cdr cases)))))

(defun loc-in-range (loc range)
  (and (consp range)
       (>= loc (first range))
       (<= loc (second range))))

(defun loc-in-when (loc case)
  (and (consp (rest case))
       (or (equal loc (first case))
           (loc-in-range loc (first case))
           (loc-in-when loc (rest case)))))

(defun gen-locase (loc cases)
  (cond ((endp cases) ())
        ((loc-in-when loc (first cases))
         (cons (first (last (first cases)))
               (gen-locase loc (rest cases))))
        (t (gen-locase loc (rest cases)))))

(defun gen-locases (locs cases)
  (if (endp locs) '((t t))
    (cons (list (first locs)
                (cons 'and (gen-locase (first locs) cases)))
          (gen-locases (rest locs) cases))))

;;;; a useful macro for defining large case splits on program locations
;;;; in predicates. This is used extensively in the invariant definitions

(defmacro locase (loc &rest cases)
  (list* 'case loc (gen-locases (locase-nums cases) cases)))

(defthm nil-update-absorbed
  (implies (not (g a r))
           (equal (s a nil r) r))
  :hints (("Goal"
           :use (:instance s-same-g)
           :in-theory (disable s-same-g))))


;; some initial defintions

(defmacro in-range (x lo hi)
  `(and (integerp ,x)
        (>= ,x ,lo)
        (<= ,x ,hi)))

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm natp-compound-recognizer
;  (iff (natp x)
;       (and (integerp x) (>= x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable natp))

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm posp-compound-recognizer
;  (iff (posp x)
;       (and (integerp x) (> x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable posp))


(encapsulate
 (((maxf) => *))
 (local (defun maxf () 1))
 (defthm maxf-is-positive-natural
   (posp (maxf))
   :rule-classes :type-prescription))

(defun thf (ndx)
  (if (and (posp ndx) (<= ndx (maxf))) ndx 1))

(defthm thf-is-<=-maxf (<= (thf ndx) (maxf)))

(in-theory (disable thf))

(defun indexp (i N)
  (and (posp i) (<= i N) (posp N)))

(defthm indexp-thf-ndx-maxf
  (indexp (thf ndx) (maxf)))

(in-theory (disable indexp))


(defmacro top (a) `(car ,a))
(defmacro tag (a) `(cdr ,a))

(defmacro top+1 (a)
  `(cons (1+ (top ,a)) (tag ,a)))

(defmacro top=0 (a)
  `(cons 0 (tag ,a)))

(defmacro tag+1 (a)
  `(cons (top ,a) (1+ (tag ,a))))

(defmacro agep (a)
  `(and (natp (top ,a)) (natp (tag ,a))))

(defun age<< (x y)
  (or (< (tag x) (tag y))
      (and (equal (tag x) (tag y))
           (< (top x) (top y)))))


(defun mend (bot top mem)
  (declare (xargs :measure (nfix (- bot top))))
  (and (integerp bot)
       (integerp top)
       (> bot top)
       (cons (<- mem (1- bot))
             (mend (1- bot) top mem))))


(defun val (x) (if (natp x) x 0))

(defthm val-type-prescription
  (natp (val x))
  :rule-classes :type-prescription)

(in-theory (disable val))

(defun one-eltp (x)
  (and (consp x) (atom (rest x))))

(defun get-top (d)
  (if (endp (rest d))
      (and (consp d) (val (first d)))
    (get-top (rest d))))

(defun drop-top (d)
  (if (endp (rest d))
      ()
    (cons (first d) (drop-top (rest d)))))

(defmacro get-bot (d) `(and (consp ,d) (val (first ,d))))

(defmacro drop-bot (d) `(rest ,d))

(defmacro push-bot (x d) `(cons ,x ,d))


;; various auxiliary theorems about mending and ages ;;

(defthm mend-bounded-to-bot-top
  (implies (and (integerp bot)
                (integerp x)
                (>= x bot))
           (equal (mend bot top (-> mem x y))
                  (mend bot top mem))))

(defthm mend-atom-bot<=top
  (implies (and (integerp top)
                (integerp bot))
           (equal (consp (mend bot top mem))
                  (> bot top))))

(defthm get-top-of-mend-is-top
  (implies (and (integerp bot)
		(integerp top)
		(> bot top))
	   (equal (get-top (mend bot top mem))
		  (val (<- mem top)))))

(defthm drop-top-mend-is-mend-top1+
  (implies (and (integerp bot)
		(integerp top))
	   (equal (drop-top (mend bot top mem))
                  (mend bot (1+ top) mem))))

(defthm one-eltp-mend-iff-bot=top+1
  (implies (and (integerp bot)
                (integerp top))
           (equal (one-eltp (mend bot top mem))
                  (equal bot (1+ top)))))

(in-theory (disable one-eltp))

(defthm mend-<=-bot-top-equals-nil
  (implies (<= bot top)
           (not (mend bot top mem))))

(defthm additive-factoid1
  (implies (and (integerp x) (integerp y))
           (equal (+ (- x) x y) y)))

(defthm mend-top+1-unwind-hack
  (implies (and (equal x (1+ bot))
                (integerp bot)
                (integerp top)
                (<= top bot))
           (equal (mend x top mem)
                  (cons (<- mem bot)
                        (mend bot top mem)))))


(defthm agep-age<<-top+1
  (implies (agep a)
           (age<< a (top+1 a))))

(defthm agep-age<<-tag+1-top=0
  (implies (agep a)
           (age<< a (tag+1 (top=0 a)))))

(defthm age<<-transitive-top+1
  (implies (age<< a b)
           (age<< a (top+1 b))))

(defthm age<<-transitive-tag+1-top=0
  (implies (age<< a b)
           (age<< a (tag+1 (top=0 b)))))

(defthm age<<-irreflexive
  (not (age<< x x)))

(defthm age<<-trichotomy
  (implies (and (agep x) (agep y)
                (not (age<< y x)))
           (iff (age<< x y)
                (not (equal x y)))))

(defthm age<<-is-asymmetric
  (implies (age<< a b)
           (not (age<< b a))))

(in-theory (disable age<<))

(defthm agep-implies-top+1-not-equal
  (implies (agep x) (not (equal x (top+1 x)))))

(defthm agep-implies-tag+1-top=0-not-equal
  (implies (agep x) (not (equal x (cons 0 (1+ (cdr x)))))))

(defthm age<<-top+1-hack1
  (implies (and (agep a)
                (equal b (top+1 a)))
           (age<< a b)))

(defthm age<<-top+1-hack2
  (implies (and (age<< a b)
                (equal c (top+1 b)))
           (age<< a c)))

(defthm tag<-implies-age<<
  (implies (< (tag x) (tag y))
           (age<< x y))
  :hints (("Goal" :in-theory (enable age<<))))

(defthm age<<-implies-tag<=
  (implies (age<< x y)
           (<= (tag x) (tag y)))
  :hints (("Goal" :in-theory (enable age<<)))
  :rule-classes :forward-chaining)

(defthm forward-chain-unfortunate
  (implies (and (<= x y)
                (equal z (1+ y)))
           (< x z))
  :rule-classes :forward-chaining)

;;;; some macros for defining accessors from records

(defmacro new (x) `(<- ,x :new))
(defmacro old (x) `(<- ,x :old))
(defmacro itm (x) `(<- ,x :itm))
(defmacro loc (x) `(<- ,x :loc))
(defmacro emt (x) `(<- ,x :emt))
(defmacro dtm (x) `(<- ,x :dtm))

(defmacro bot (x) `(<- ,x :bot))
(defmacro mem (x) `(<- ,x :mem))
(defmacro age (x) `(<- ,x :age))
(defmacro ret (x) `(<- ,x :ret))
(defmacro deq (x) `(<- ,x :deq))
(defmacro ctr (x) `(<- ,x :ctr))
(defmacro one (x) `(<- ,x :one))
(defmacro clk (x) `(<- ,x :clk))

(defmacro xitm  (x) `(<- ,x :xitm))
(defmacro xctr  (x) `(<- ,x :xctr))
(defmacro xone  (x) `(<- ,x :xone))
(defmacro xzero (x) `(<- ,x :xzero))
(defmacro xsafe (x) `(<- ,x :xsafe))

(defmacro shr (x) `(<- ,x :shr))
(defmacro tvs (x) `(<- ,x :tvs))
(defmacro onr (x) `(<- ,x :onr))

(defmacro ndx (x) `(<- ,x :ndx))
(defmacro dtm (x) `(<- ,x :dtm))
(defmacro psh (x) `(<- ,x :psh))

(defmacro st8 (x) `(<- ,x :st8))
(defmacro stl (x) `(<- ,x :stl))
(defmacro xgo (x) `(<- ,x :xgo))

(defmacro >s  (&rest x) `(update s ,@x))
(defmacro >f  (&rest x) `(update f ,@x))
(defmacro >o  (&rest x) `(update o ,@x))
(defmacro >st (&rest x) `(update st ,@x))
(defmacro >in (&rest x) `(update in ,@x))
(defmacro >_  (&rest x) `(update () ,@x))

;;;; END auxiliary definitions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN cdeq step functions ;;;;

(defun c-thf-s (f s)
  (case (loc f)
        (8  (if (equal (age s) (old f))
                (>s :age (new f))
              s))
        (10 (>s :ret (itm f) :clk (1+ (clk s))))
        (t  s)))

(defun c-thf-f (f s)
  (case (loc f)
        (0  (>f :loc 1))
        (1  (>f :loc 2 :old (age s)))
        (2  (>f :loc 3 :bot (bot s)))
        (3  (>f :loc (if (> (bot f) (top (old f))) 5 4)))
        (4  (>f :loc 0 :ret nil))
        (5  (>f :loc 6 :itm (val (<- (mem s) (top (old f))))))
        (6  (>f :loc 7 :new (old f)))
        (7  (>f :loc 8 :new (top+1 (new f))))
        (8  (>f :loc 9 :new (if (equal (age s) (old f))
                                 (age s) (new f))))
        (9  (>f :loc (if (equal (old f) (new f)) 10 11)))
        (10 (>f :loc 0 :ret (itm f)))
        (11 (>f :loc 0 :ret nil))
        (t  (>f :loc 0))))

(defun c-onr-s (o s)
  (case (loc o)
        (5  (>s :bot (bot o)))
        (9  (>s :ret (itm o) :clk (1+ (clk s))))
        (10 (>s :bot 0))
        (14 (if (equal (age s) (old o))
                (>s :age (new o))
              s))
        (16 (>s :ret (itm o) :clk (1+ (clk s))))
        (17 (>s :age (new o)))
        (20 (>s :mem (-> (mem s) (bot o) (dtm o))))
        (22 (>s :bot (bot o)))
        (t  s)))

(defun c-onr-o (p d o s)
  (case (loc o)
        (0  (if p (>o :loc 19 :dtm d)
              (>o :loc 1)))
        (1  (>o :loc 2 :bot (bot s)))
        (2  (>o :loc (if (= (bot o) 0) 3 4)))
        (3  (>o :loc 0 :ret nil))
        (4  (>o :loc 5 :bot (1- (bot o))))
        (5  (>o :loc 6))
        (6  (>o :loc 7 :itm (val (<- (mem s) (bot o)))))
        (7  (>o :loc 8 :old (age s)))
        (8  (>o :loc (if (> (bot o) (top (old o))) 9 10)))
        (9  (>o :loc 0 :ret (itm o)))
        (10 (>o :loc 11))
        (11 (>o :loc 12 :new (top=0 (old o))))
        (12 (>o :loc 13 :new (tag+1 (new o))))
        (13 (>o :loc (if (= (bot o) (top (old o))) 14 17)))
        (14 (>o :loc 15 :new (if (equal (age s) (old o))
                                 (age s) (new o))))
        (15 (>o :loc (if (equal (old o) (new o)) 16 17)))
        (16 (>o :loc 0 :ret (itm o)))
        (17 (>o :loc 18))
        (18 (>o :loc 0 :ret nil))
        (19 (>o :loc 20 :bot (bot s)))
        (20 (>o :loc 21))
        (21 (>o :loc 22 :bot (1+ (bot o))))
        (t  (>o :loc 0))))

(DEFUN cdeq (st in)
  (let* ((ndx (thf (ndx in)))
         (dtm (dtm in))
         (psh (psh in))
         (tvs (tvs st))
         (shr (shr st))
         (onr (onr st))
         (thf (<- tvs ndx)))
    (if (ndx in)
        (>st :tvs (-> tvs ndx (c-thf-f thf shr))
             :shr (c-thf-s thf shr))
      (>st :onr (c-onr-o psh dtm onr shr)
           :shr (c-onr-s onr shr)))))

;;;; END cdeq step functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN cdeq+ step functions ;;;;

(defun i-thf-s (f s)
  (case (loc f)
        (8  (if (equal (age s) (old f))
                (>s :age (new f)
                    :xctr (1+ (xctr s)))
              s))
        (10 (>s :ret (itm f) :clk (1+ (clk s))))
        (t  s)))

(defun i-thf-f (f s)
  (case (loc f)
        (0  (>f :loc 1))
        (1  (>f :loc 2
                :old (age s)
                :xctr (xctr s)))
        (2  (>f :loc 3
                :bot (bot s)
                :xitm (and (> (bot s) (top (age s)))
                           (val (<- (mem s) (top (age s)))))))
        (3  (>f :loc (if (> (bot f) (top (old f))) 5 4)))
        (4  (>f :loc 0 :ret nil))
        (5  (>f :loc 6 :itm (val (<- (mem s) (top (old f))))))
        (6  (>f :loc 7 :new (old f)))
        (7  (>f :loc 8 :new (top+1 (new f))))
        (8  (>f :loc 9 :new (if (equal (age s) (old f))
                                (age s) (new f))))
        (9  (>f :loc (if (equal (old f) (new f)) 10 11)))
        (10 (>f :loc 0 :ret (itm f)))
        (11 (>f :loc 0 :ret nil))
        (t  (>f :loc 0))))

(defun i-onr-s (o s)
  (case (loc o)
        (5  (>s :bot (bot o)
                :xsafe (<= (bot o) (top (age s)))))
        (7  (>s :xsafe (<= (bot s) (top (age s)))))
        (9  (>s :ret (itm o) :clk (1+ (clk s))))
        (10 (>s :bot 0))
        (14 (if (equal (age s) (old o))
                (>s :age (new o)
                    :xctr (1+ (xctr s))
                    :xsafe nil)
              s))
        (16 (>s :ret (itm o) :clk (1+ (clk s))))
        (17 (>s :age (new o)
                :xctr (1+ (xctr s))
                :xsafe nil))
        (20 (>s :mem (-> (mem s) (bot o) (dtm o))))
        (22 (>s :bot (bot o)))
        (t  s)))

(defun i-onr-o (p d o s)
  (case (loc o)
        (0  (if p (>o :loc 19 :dtm d)
              (>o :loc 1)))
        (1  (let ((o (>o :loc 2 :bot (bot s))))
              (if (= (bot s) 0)
                  (>o :xitm nil)
                o)))
        (2  (>o :loc (if (= (bot o) 0) 3 4)))
        (3  (>o :loc 0 :ret nil :xzero t))
        (4  (>o :loc 5 :bot (1- (bot o))))
        (5  (>o :loc 6
                :xitm (and (>= (bot o) (top (age s)))
                           (val (<- (mem s) (bot o))))
                :xctr (and (= (bot o) (top (age s)))
                           (xctr s))))
        (6  (>o :loc 7 :itm (val (<- (mem s) (bot o)))))
        (7  (>o :loc 8
                :old (age s)
                :xitm (and (>= (bot o) (top (age s)))
                           (xitm o))
                :xctr (if (and (not (xctr o))
                               (= (bot o) (top (age s))))
                          (xctr s)
                        (xctr o))))
        (8  (if (> (bot o) (top (old o)))
                (>o :loc 9 :xctr nil :xzero nil)
              (>o :loc 10)))
        (9  (>o :loc 0 :ret (itm o)))
        (10 (>o :loc 11))
        (11 (>o :loc 12 :new (top=0 (old o))))
        (12 (>o :loc 13 :new (tag+1 (new o))))
        (13 (>o :loc (if (= (bot o) (top (old o))) 14 17)))
        (14 (let ((o (>o :loc 15)))
              (if (equal (age s) (old o))
                  (>o :new (age s)
                      :xctr nil
                      :xzero t)
                o)))
        (15 (>o :loc (if (equal (old o) (new o)) 16 17)))
        (16 (>o :loc 0 :ret (itm o)))
        (17 (>o :loc 18 :xctr nil :xzero t))
        (18 (>o :loc 0 :ret nil))
        (19 (>o :loc 20 :bot (bot s)))
        (20 (>o :loc 21))
        (21 (>o :loc 22 :bot (1+ (bot o))))
        (22 (>o :loc 0  :xzero nil))
        (t  (>o :loc 0))))

(DEFUN cdeq+ (st in)
  (let* ((ndx (thf (ndx in)))
         (dtm (dtm in))
         (psh (psh in))
         (tvs (tvs st))
         (shr (shr st))
         (onr (onr st))
         (thf (<- tvs ndx)))
    (if (ndx in)
        (>st :tvs (-> tvs ndx (i-thf-f thf shr))
             :shr (i-thf-s thf shr))
      (>st :onr (i-onr-o psh dtm onr shr)
           :shr (i-onr-s onr shr)))))

;;;; END cdeq+ step functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN intr step functions ;;;;

(defun m-thf-s (f s)
  (case (loc f)
        (2 (if (and (itm f)
                    (= (ctr f) (ctr s)))
               (>s :deq (drop-top (deq s))
                   :ctr (1+ (ctr s)))
             s))
        (3 (>s :ret (itm f) :clk (1+ (clk s))))
        (t s)))

(defun m-thf-f (f s)
  (case (loc f)
        ;; popTop
        (0 (>f :loc 1 :ctr (ctr s)))
        (1 (>f :loc 2 :itm (get-top (deq s))))
        (2 (>f :loc (if (and (itm f)
                             (= (ctr s) (ctr f)))
                        3 0)))
        (t (>f :loc 0))))

(defun m-onr-s (o s)
  (case (loc o)
        (1 (>s :deq (drop-bot (deq s))))
        (3 (if (or (= (ctr o) (ctr s))
                   (and (atom (deq s))
                        (implies (itm o) (ctr o))
                        (not (xzero o))))
               (>s :ctr (1+ (ctr s)))
             s))
        (4 (>s :ret (itm o) :clk (1+ (clk s))))
        (5 (>s :deq (push-bot (dtm o) (deq s))))
        (t s)))

(defun m-onr-o (p d o s)
  (case (loc o)
        (0 (if p (>o :loc 5 :dtm d)
             (>o :loc 1)))
        ;; popBottom
        (1 (>o :loc 2
               :itm (get-bot (deq s))
               :ctr (and (one-eltp (deq s))
                         (ctr s))))
        (2 (let ((o (>o :loc 3)))
             (cond ((or (not (itm o))
                        (consp (deq s))
                        (= (ctr o) (ctr s)))
                    o)
                   ((not (ctr o)) (>o :ctr (ctr s)))
                   (t (>o :itm nil)))))
        (3 (>o :loc (if (and (itm o)
                             (implies (ctr o)
                                      (= (ctr o) (ctr s))))
                        4 0)
               :xzero (implies (itm o) (ctr o))
               :ctr nil))
        (5 (>o :loc 0 :xzero nil))
        ;; pushBottom
        (t (>o :loc 0))))

(DEFUN intr (st in)
  (let* ((ndx (thf (ndx in)))
         (dtm (dtm in))
         (psh (psh in))
         (tvs (tvs st))
         (shr (shr st))
         (onr (onr st))
         (thf (<- tvs ndx)))
    (if (ndx in)
        (>st :tvs (-> tvs ndx (m-thf-f thf shr))
             :shr (m-thf-s thf shr))
      (>st :onr (m-onr-o psh dtm onr shr)
           :shr (m-onr-s onr shr)))))

;;;; END intr step functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN intr+ step functions ;;;;

(defun r-thf-s (f s)
  (case (loc f)
        (2 (if (and (itm f)
                    (= (ctr f) (ctr s)))
               (>s :deq (drop-top (deq s))
                   :ctr (1+ (ctr s)))
             s))
        (3 (>s :ret (itm f) :clk (1+ (clk s))))
        (t s)))

(defun r-thf-f (f s)
  (let ((f (>f :xgo
               (and (consp (deq s))
                    (or (= (loc f) 0)
                        (xgo f))))))
    (case (loc f)
          ;; popTop
          (0 (>f :loc 1 :ctr (ctr s)))
          (1 (>f :loc 2 :itm (get-top (deq s))))
          (2 (>f :loc (if (and (itm f)
                               (= (ctr s) (ctr f)))
                          3 0)))
          (t (>f :loc 0)))))

(defun r-onr-s (o s)
  (case (loc o)
        (1 (>s :deq (drop-bot (deq s))))
        (3 (if (or (= (ctr o) (ctr s))
                   (and (atom (deq s))
                        (implies (itm o) (ctr o))
                        (not (xzero o))))
               (>s :ctr (1+ (ctr s)))
             s))
        (4 (>s :ret (itm o) :clk (1+ (clk s))))
        (5 (>s :deq (push-bot (dtm o) (deq s))))
        (t s)))

(defun r-onr-o (p d o s)
  (case (loc o)
        (0 (if p (>o :loc 5 :dtm d)
             (>o :loc 1)))
        ;; popBottom
        (1 (>o :loc 2
               :itm (get-bot (deq s))
               :ctr (and (one-eltp (deq s))
                         (ctr s))))
        (2 (let ((o (>o :loc 3)))
             (cond ((or (not (itm o))
                        (consp (deq s))
                        (= (ctr o) (ctr s)))
                    o)
                   ((not (ctr o)) (>o :ctr (ctr s)))
                   (t (>o :itm nil)))))
        (3 (>o :loc (if (and (itm o)
                             (implies (ctr o)
                                      (= (ctr o) (ctr s))))
                        4 0)
               :xzero (implies (itm o) (ctr o))
               :ctr nil))
        (5 (>o :loc 0 :xzero nil))
        ;; pushBottom
        (t (>o :loc 0))))

(DEFUN intr+ (st in)
  (let* ((ndx (thf (ndx in)))
         (dtm (dtm in))
         (psh (psh in))
         (tvs (tvs st))
         (shr (shr st))
         (onr (onr st))
         (thf (<- tvs ndx)))
    (if (ndx in)
        (>st :tvs (-> tvs ndx (r-thf-f thf shr))
             :shr (r-thf-s thf shr))
      (>st :onr (r-onr-o psh dtm onr shr)
           :shr (r-onr-s onr shr)))))

;;;; END intr+ step functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN spec step function ;;;;

(DEFUN spec (st in)
  (let ((ndx (thf (ndx in)))
        (dtm (dtm in))
        (tvs (tvs st))
        (s (shr st))
        (o (onr st))
        (deq (deq (shr st))))
    (if (ndx in)
        (cond ((<- tvs ndx)
               (>st :tvs (-> tvs ndx nil)
                    :shr (>s :ret (<- tvs ndx)
                             :clk (1+ (clk s)))))
              ((and (itm o) (equal (st8 o) 'pop)
                    (atom deq) (stl in))
               (>st :tvs (-> tvs ndx (itm o))
                    :onr (>o :itm nil)))
              (t
               (>st :tvs (-> tvs ndx (get-top deq))
                    :shr (>s :deq (drop-top deq)))))
      (case (st8 o)
            (push (>st :onr (>o :st8 'idle)
                       :shr (>s :deq (push-bot (dtm o) deq))))
            (pop  (if (itm o)
                      (>st :onr (>o :st8 'idle :itm nil)
                           :shr (>s :ret (itm o)
                                    :clk (1+ (clk s))))
                    (>st :onr (>o :st8 'idle))))
            (idle (if (psh in)
                      (>st :onr (>o :st8 'push :dtm dtm))
                    (>st :onr (>o :st8 'pop :itm (get-bot deq))
                         :shr (>s :deq (drop-bot deq)))))))))

;;;; END spec step function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN label function ;;;;

(DEFUN label (st)
  (list (ret (shr st))
        (clk (shr st))
        (dtm (onr st))))

;;;; END label function ;;;;

#|----------------------------------------------------------------------------|#

