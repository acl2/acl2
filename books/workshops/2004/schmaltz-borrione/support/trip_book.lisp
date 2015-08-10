;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;;
;;
;; Functional Specification and Validation of the Octagon Network on
;;              Chip using the ACL2 Theorem Prover
;;
;;
;;                          Proof Script
;;
;;
;;                         Julien Schmaltz
;;                     Joseph Fourier University
;;               46, av. Felix Viallet 38031 Grenoble Cedex
;;                             FRANCE
;;                      Julien.Schmaltz@imag.fr
;;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------

;; File: trip_book.lisp
;; Definition of the functions that perform the steps of a trip

(in-package "ACL2")

;; we import the definition of the function Switch
(include-book "switch")

;; we import some definitions and predicates
(include-book "predicatesNCie")

;; we import a library on lists
(include-book  "../../../../data-structures/list-defuns")

(include-book  "../../../../data-structures/list-defthms")


(defun first_travel_step (msg route_pair N)
  ;; definition of the first and the last step of a travel
  ;; N stands for the number of nodes in a quarter
  (let ((where_i_am (nth 0 route_pair))
        (where_i_go (nth 1 route_pair)))
    ;; I have to split the computation in 3 cases
    ;; case 1: where-i-am is 0
    (cond ((equal where_i_am 0)
           (mv-let (node cw ccw acr)
                   (switch msg nil nil nil
                           0 ;; sw_nb = where_i_am = 0
                           ;; cwise, ccwise and across (from)
                           (+ -1 (* 4 N)) 1 (* 2 N)
                           ;; cwise, ccwise and across (to)
                           1 (+ -1 (* 4 N)) (* 2 N)
                           (list 0 where_i_go))
                   (declare (ignore node))
                   ;; I must know where is (nth 1 route_pair)
                   (if (equal where_i_go 1)
                       ;; then I go clockwise
                       cw
                     (if (equal where_i_go (+ -1 (* 4 N)))
                         ;; then I go counter-clockwise
                         ccw
                       ;; else I go across
                       acr))))
          ;; case 2 where_i_am = (* 4 N) - 1
          ((equal where_i_am (+ -1 (* 4 N)))
           (mv-let (node cw ccw acr)
                   (switch msg nil nil nil
                           (+ -1 (* 4 N))
                           (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                           0 (+ -1 where_i_am) (+ -1 (* 2 N))
                           (list (+ -1 (* 4 N)) where_i_go))
                   (declare (ignore node))
                   (if (equal where_i_go 0)
                       ;; cwise
                       cw
                     (if (equal where_i_go (+ -1 where_i_am))
                       ;; ccwise
                         ccw
                       ;; across
                       acr))))
          (t ;; case 3: 0 < (nth 0 route_pair) < N - 1
           (mv-let (node cw ccw acr)
                   (switch msg nil nil nil
                           where_i_am
                           (+ -1 where_i_am) (+ 1 where_i_am)
                           ;; the from_accross_nb is
                           (if (< where_i_am (* 2 N))
                               (+ where_i_am (* 2 N))
                             (+ where_i_am (* -2 N)))
                           (+ 1 where_i_am) (+ -1 where_i_am)
                           (if (< where_i_am (* 2 N))
                               (+ where_i_am (* 2 N))
                             (+ where_i_am (* -2 N)))
                           (list where_i_am where_i_go))
                   (declare (ignore node))
                   (if (equal where_i_go (+ 1 where_i_am))
                       ;; then I go cwise
                       cw
                     (if (equal where_i_go (+ -1 where_i_am))
                         ccw
                       ;; else across
                       acr)))))))



(defun nth_travel_step (msg route_triple N)
  ;; definition of the general step of a travel
  ;; N gives the number of nodes in a quarter
  (let ((where_i_come_from (nth 0 route_triple))
        (where_i_am (nth 1 route_triple))
        (where_i_go (nth 2 route_triple)))
    ;; I have to split the computation in 3 cases
    ;; case 1: where_i_am is 0
    (cond ((equal where_i_am 0)
           ;; I must know where is where_i_go
           (cond ((equal where_i_go 1)
                  ;; then I go clockwise
                  (cond ((equal where_i_come_from 1)
                         ;; I come from ccwise, so I go back to where i come from
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         0 ; sw_nb = where_i_am = 0
                                         (+ -1 (* 4 N)) 1 (* 2 N)
                                         1 (+ -1 (* 4 N)) (* 2 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))
                        ((equal where_i_come_from (+ -1 (* 4 N)))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         0 ; sw_nb = where_i_am = 0
                                         (+ -1 (* 4 N)) 1 (* 2 N)
                                         1 (+ -1 (* 4 N)) (* 2 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         0 ; sw_nb = where_i_am = 0
                                         (+ -1 (* 4 N)) 1 (* 2 N)
                                         1 (+ -1 (* 4 N)) (* 2 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))))
                  ((equal where_i_go (+ -1 (* 4 N)))
                   ;; then I go counter-clockwise
                   (cond ((equal where_i_come_from 1)
                          ;; I come from ccwise
                          (mv-let (node cw ccw acr)
                                  (switch nil nil msg nil
                                          0 ; sw_nb = where_i_am = 0
                                          (+ -1 (* 4 N)) 1 (* 2 N)
                                          1 (+ -1 (* 4 N)) (* 2 N)
                                          (list where_i_come_from
                                                where_i_go))
                                  (declare (ignore node cw acr))
                                  ccw))
                         ((equal where_i_come_from (+ -1 where_i_am))
                          ;; I come from cwise
                          (mv-let (node cw ccw acr)
                                  (switch nil msg nil nil
                                          0
                                          (+ -1 (* 4 N)) 1 (* 2 N)
                                          1 (+ -1 (* 4 N)) (* 2 N)
                                          (list where_i_come_from
                                                where_i_go))
                                  (declare (ignore node cw acr))
                                  ccw))
                         ;; I come from across
                         (t
                          (mv-let (node cw ccw acr)
                                  (switch nil nil nil msg
                                          0
                                          (+ -1 (* 4 N)) 1 (* 2 N)
                                          1 (+ -1 (* 4 N)) (* 2 N)
                                          (list where_i_come_from
                                                where_i_go))
                                  (declare (ignore node cw acr))
                                 ccw))))
                  ;; else I go across
                 (t
                  (cond ((equal where_i_come_from 1)
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         0
                                         (+ -1 (* 4 N)) 1 (* 2 N)
                                         1 (+ -1 (* 4 N)) (* 2 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ((equal where_i_come_from (+ -1 (* 4 N)))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         0
                                         (+ -1 (* 4 N)) 1 (* 2 N)
                                         1 (+ -1 (* 4 N)) (* 2 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         0
                                         (+ -1 (* 4 N)) 1 (* 4 N)
                                         1 (+ -1 (* 4 N)) (* 4 N)
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))))))
          ;; case 2 where_i_am = (* 4 N) - 1
          ((equal where_i_am (+ -1 (* 4 N)))
           (cond ((equal where_i_go 0)
                  ;; cwise
                  (cond ((equal where_i_come_from 0)
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))
                         ((equal where_i_come_from (+ -1 where_i_am))
                          ;; I come from cwise
                          (mv-let (node cw ccw acr)
                                  (switch nil msg nil nil
                                          where_i_am
                                          (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                          0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                          (list where_i_come_from
                                                where_i_go))
                                  (declare (ignore node ccw acr))
                                  cw))
                         ;; I come from across
                         (t
                          (mv-let (node cw ccw acr)
                                  (switch nil nil nil msg
                                          where_i_am
                                          (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                          0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                          (list where_i_come_from
                                                where_i_go))
                                  (declare (ignore node ccw acr))
                                  cw))))
                 ((equal where_i_go (+ -1 where_i_am))
                  ;; ccwise
                  (cond ((equal where_i_come_from 0)
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))
                        ((equal where_i_come_from (+ -1 where_i_am))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))))
                 ;; across
                 (t
                  (cond ((equal where_i_come_from 0)
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ((equal where_i_come_from (+ -1 where_i_am))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         where_i_am
                                         (+ -1 where_i_am) 0 (+ -1 (* 2 N))
                                         0 (+ -1 where_i_am) (+ -1 (* 2 N))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))))))
          (t ; case 3: 0 < where_i_am < (* 4 N) - 1
           (cond ((equal where_i_go (+ 1 where_i_am))
                  ;; then I go cwise
                  (cond ((equal where_i_come_from (+ 1 where_i_am))
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         ;; computation of the across nb
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))
                        ((equal where_i_come_from (+ -1 where_i_am))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node ccw acr))
                                 cw))))
                 ((equal where_i_go (+ -1 where_i_am))
                  ;; I go ccwise
                  (cond ((equal where_i_come_from (+ 1 where_i_am))
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))
                        ((equal where_i_come_from (+ -1 where_i_am))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw acr))
                                 ccw))))
                 ;; else across
                 (t
                  (cond ((equal where_i_come_from (+ 1 where_i_am))
                         ;; I come from ccwise
                         (mv-let (node cw ccw acr)
                                 (switch nil nil msg nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ((equal where_i_come_from (+ -1 where_i_am))
                         ;; I come from cwise
                         (mv-let (node cw ccw acr)
                                 (switch nil msg nil nil
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr))
                        ;; I come from across
                        (t
                         (mv-let (node cw ccw acr)
                                 (switch nil nil nil msg
                                         where_i_am
                                         (+ -1 where_i_am) (+ 1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (+ 1 where_i_am) (+ -1 where_i_am)
                                         (if (< where_i_am (* 2 N))
                                             (+ (* 2 N) where_i_am)
                                           (+ (* -2 N) where_i_am))
                                         (list where_i_come_from
                                               where_i_go))
                                 (declare (ignore node cw ccw))
                                 acr)))))))))

(defthm lemma_no_duplicatesp_len_2
  (implies (and (no-duplicatesp x)
                (equal (car x) y)
                (<= 2 (len x)))
           (not (equal (nth 1 x)
                       y))))

(defthm no_dupli_len_3_lemma
  (implies (and (no-duplicatesp x)
                (<= 3 (len x))
                (equal (nth 2 x) a))
           (not (equal (nth 1 x) a))))

(defthm no_dupli_len_3_lemma_bis
  (implies (and (no-duplicatesp x)
                (<= 3 (len x))
                (equal (car x) a))
           (not (equal (nth 2 x) a))))

