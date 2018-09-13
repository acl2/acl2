; Copyright (C) 2018, Regents of the University of Texas
; Written by Ebelechukwu Esimai
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; Modeling HexNet in ACL2

; This file depicts the current model of HexNet in ACL2.  This is an
; attempt to capture HexNet functionality using the ACL2 modeling
; system.  However, this model does not demonstrate asynchrony in
; packet movement; instead, it is the first step in modeling
; acceptable HexNet behaviours of the network as a whole.  We have
; represented the network as a graph spread on a Cartesian grid.  The
; nodes in the graph represent the junctions in the network.  Each
; junction is named by a pair indicating its X- and Y- coordinates.
; The edges of the graph are the links between the junctions.

; We start by defining the syntax of the network, its junctions, and
; links.  Then, we define the syntax of packets, which are the data
; items in the HexNet network.  Having defined this notion, we then
; define a state of the system, which we call a "Linktable".  The
; Linktable contains the location of all packets in the network after
; each ``step'' of the system.  Then, we define functions that update
; the state, "Linktable", and then conclude with the definition of the
; run function of the system.


; Outline -- These section headers appear in the code below, in this order
; 1) Introduction
; 2) HexNet Recognizers  :- network, junction and link recognizers
; 3) Source-Links accessor
; 4) Sources
; 5) Packets and Linktable :- packet recognizer and accessor
; 6) Link Accessors
; 7) Current inputs
; 8) Terminal recognizer
; 9) Routing Function
; 10) Arbiter
; 11) Update link function
; 12) Process junction function
; 13) Single step function
; 14) Inverse map
; 15) Adding new packets into the network
; 16) Removing delivered packets from the network
; 17) Resetting the processed bit of each packet
; 18) Multi-step Function
; 19) Trace Function
; 20) Construct linktable and inverse graph from a network example


; Terms and labels
; G :- Network , The HexNet network

; LT :- Link Table, the table of all the links present in the network
;       and the packets on any link

; AST :- Arbiter state, the map of previous arbitration decisions and
;        where they were made

; MS :- Model state, error property of the model


(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "helper-functions")

;(set-well-founded-relation o<)

; A drawing of HexNet                            Legend:
;                                                 # => Terminals
;                                               (+) => repeaters
;   8                            #              --- => ``east-west'' links
;                                |                | => ``north-south'' links
;   7                    #       |       #
;                        |       |       |
;   6    #------(+)-----(+)-----(+)-----(+)-----(+)------#
;                |                               |
;   5            |                               |
;                |                               |
;   4           (+)--#                          (+)--#
;                |                               |
;   3            |       #               #       |
;                |       |               |       |
;   2    #------(+)-----(+)-----(+)-----(+)-----(+)------#
;                                |
;   1                            |
;                                |
;   0                            #
;        0   1   2   3   4   5   6   7   8   9   A   B   C

; Note: Both terminals and repeaters are junctions.  Terminals are the
; entry and exit points of the network.  Also, there are two links
; between any connected pair of junctions.


;  1. Introduction

;; Collector functions to get all nodes and all edges in a graph
(defun all-juncts (g)
  (declare (xargs :guard (alistp g)))
  (strip-cars g))

(defund links (juncts g)
  (declare (xargs :guard (and (true-listp juncts)
			      (alistp g))))
  (if (endp juncts)
      nil
    (if (alistp (cdr (assoc-equal (car juncts) g)))
        (append (flatten-alist (strip-cdrs (cdr (assoc-equal (car juncts) g))))
                (links (cdr juncts) g))
      nil)))

(defthm symbol-listp-links
  (implies (and (true-listp juncts)
                (alistp g))
           (symbol-listp (links juncts g)))
  :hints (("Goal" :in-theory (enable links)))
  :rule-classes :type-prescription)
(defthm symbol-listp-remove-duplicates-links
  (implies (symbol-listp (links juncts g))
           (symbol-listp (remove-duplicates-equal (links juncts g))))
   :hints (("Goal" :in-theory (enable links))))


;; A junction is a pair of its x and y coordinates; e.g. (0 . 2).
(defun coordinatep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

;; A source-link alist is the list of other junctions connected to a
;; particular junction.  The keys are the junctions and the values are
;; the links connecting them.

;; For example,
;;   ((2 . 2)  ((0 . 2)  S2  S1)  source-links-list   (((0 . 2)  S2  S1)
;;             ((4 . 2)  S3  S4)  ------------------>  ((4 . 2)  S3  S4)
;;             ((2 . 4)  T1  T2))                      ((2 . 4)  T1  T2))

;; This means that (2 . 2) -----> (0 . 2) and (0 . 2) <------ (2 . 2)
;;                           S2                          S1

(defun source-linksp (srlnks juncts links)
  (declare (xargs :guard (and (alistp srlnks)
                              (true-listp juncts)
                              (no-duplicatesp-equal juncts)
                              (symbol-listp links))))
  (cond
   ((atom srlnks) (equal srlnks nil))
   (t (let* ((entry (car srlnks))
             (junct (car entry))
             (links-list (cdr entry)))
        (and (coordinatep junct)
             (member-equal junct juncts)
             (consp links-list)
             (consp (cdr links-list))
             (symbolp (car links-list))
             (member-equal (car links-list) links)
             (symbolp (cadr links-list))
             (member-equal (cadr links-list) links)
             (null (cddr links-list))
             (source-linksp (cdr srlnks) juncts links))))))


; 2. HexNet recognizer

;; Definition of the syntax of the HexNet
(defun graph1p (g juncts links)
  "Property of the whole network"
  (declare (xargs :guard (and (alistp g)
                              (true-listp juncts)
                              (no-duplicatesp-equal juncts)
                              (symbol-listp links))))
  (cond
   ((atom g) (equal g nil))
   (t (let* ((entry (car g))
	     (junct (car entry))
	     (source-links (cdr entry)))
	(and (coordinatep junct)
             (member-equal junct juncts)
             (consp source-links)
             (alistp source-links)
             (true-list-listp source-links)
	     (source-linksp source-links juncts links)
	     (graph1p (cdr g) juncts links))))))

;; Network recognizer
(defund graphp (g)
  (declare (xargs :guard t))
  (and (alistp g)
       (no-duplicatesp-equal (all-juncts g))
       (symbol-listp (remove-duplicates-equal (links (all-juncts g) g)))
       (graph1p g (all-juncts g)
                (remove-duplicates-equal (links (all-juncts g) g)))))

(defthm graphp-forward
  (implies
   (graphp g)
   (and (alistp g)
        (no-duplicatesp-equal (all-juncts g))
        (symbol-listp (remove-duplicates-equal (links (all-juncts g) g)))
        (graph1p g (all-juncts g)
                 (remove-duplicates-equal (links (all-juncts g) g)))))
  :hints (("Goal" :in-theory (enable graphp)))
  :rule-classes :forward-chaining)




;; Junction recognizer
(defun junctp (x g)
  (declare (xargs :guard (graphp g)))
  (member-equal x (all-juncts g)))

(defthm graphp-implies-consp-junct
  (implies (and (graph1p g keys values)
		(junctp junct g))
	   (consp junct)))
(defthm graphp-implies-rationalp-x
  (implies (and (graph1p g keys values)
		(junctp junct g))
	   (rationalp (car junct))))
(defthm graphp-implies-rationalp-y
  (implies (and (graph1p g keys values)
		(junctp junct g))
	   (rationalp (cdr junct))))
(in-theory (disable coordinatep))


;; Link recognizer
(defun linkp (lnk g)
  (declare (xargs :guard (graphp g)))
  (and (symbolp lnk)
       (member-equal lnk (remove-duplicates-equal
                          (links (all-juncts g) g)))))

; recognizer for a list of links
(defun link-listp (lst g)
  (declare (xargs :guard (graphp g)))
  (cond ((atom lst) (equal lst nil))
        (t (and (linkp (car lst) g)
                (link-listp (cdr lst) g)))))

(defthm link-listp-implies-symbol-listp
  (implies (and (graphp g)
                (link-listp lst g))
           (symbol-listp lst))
  :rule-classes :type-prescription)

(defthm link-listp-implies-subsetp-equal-links
  (implies (and (graphp g)
                (link-listp lst g))
           (subsetp-equal lst
                          (remove-duplicates-equal
                           (links (all-juncts g) g))))
  :rule-classes :type-prescription)

(defthm link-listp-remove-equal
  (implies (link-listp lst g)
           (link-listp (remove-equal x lst) g))
  :rule-classes :type-prescription)


; 3. Source-Links Accessor

;; Definition of accessor function to get the neighboring junctions
;; and associated links to a particular function
(defun get-source-link (junct g)
  (declare (xargs :guard (and (graphp g)
                              (junctp junct g))))
  (cdr (assoc-equal junct g)))

(defthm graphp-implies-alistp-get-source-links
  (implies
   (and (graph1p g keys values)
        (junctp junct g))
   (alistp (get-source-link junct g))))
(defthm graphp-implies-true-list-listp-get-source-link
  (implies
   (and (graph1p g keys values)
        (junctp junct g))
   (true-list-listp (get-source-link junct g)))
  :rule-classes :type-prescription)
(defthm graphp-implies-consp-get-source-links
  (implies
   (and (graph1p g keys values)
        (junctp junct g))
   (consp (get-source-link junct g))))
(defthm graphp-implies-source-linksp
  (implies
   (and (graph1p g keys values)
        (junctp junct g))
   (source-linksp (get-source-link junct g) keys values)))
(in-theory (disable get-source-link all-juncts))


; 4. Sources

;; The function "Sources" returns the list of junctions connected to a
;; specific junction
(defun sources (junct g)
  (declare (xargs :guard (and (graphp g)
			      (junctp junct g))))
  (strip-cars (get-source-link junct g)))

;; Lemma : Sources returns a list of junctions that is a subset of all
;; the junctions in thr network
(defthm  graphp-implies-subsetp-sources-all-juncts
  (implies
   (and (graph1p g keys values)
        (junctp junct g))
   (subsetp-equal (sources junct g) keys))
  :hints (("Goal" :in-theory (enable get-source-link all-juncts))))

(defthm  graphp-implies-subsetp-sources-remove-all-juncts
  (implies
   (and (graphp g)
        (junctp junct g)
        (junctp dest g)
        (subsetp-equal (sources junct g) (all-juncts g)))
   (subsetp-equal (remove-equal dest (sources junct g)) (all-juncts g))))


;  5. Packets and Linktable

;; A packet is a data item in the network. It is modeled as a list that
;; contains:
;;      i)   a packet id
;;      ii)  a turn signal :- the next direction the packet should take
;;     iii)  a processed bit :- this ensures that a packet moves at most
;;           once in each ``cycle'' of execution of the system
;;      iv)  a final terminal :- address of final destination for a packet
;;       v)  a source terminal :- the address of the origin of the packet
;;      vi)  the information to be passed along
;;
;; Example : '(pkt1 E 0 (8 . 7) (0 . 2) data)

;; Cardinal points check
(defund directionp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (or (equal x 'n)
           (equal x 'e)
           (equal x 'w)
           (equal x 's))))

;; Turn signal recognizer
(defund turn_signalp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (or (directionp x)
           (equal x 'done))))

;; Packet recognizer
(defun packetp (pkt g)
  "Valid packet property"
  (declare (xargs :guard (graphp g)))
  (cond ((atom pkt) nil)
	(t (and (symbolp (car pkt))                      ;; pkt_id
                (consp (cdr pkt))
                (turn_signalp (cadr pkt))                ;; turn_signal
                (consp (cddr pkt))
                (bitp (caddr pkt))                       ;; processed_bit
                (consp (cdddr pkt))
                (junctp (cadddr pkt) g)                  ;; final destination
                (consp (cddddr pkt))
                (junctp (car (cddddr pkt)) g)            ;; origin
                (consp (cdr (cddddr pkt)))
                (true-listp (cdr (cddddr pkt)))))))      ;; data

(defthm packetp-true-listp
  (implies
   (and (graphp g)
        (packetp pkt g))
   (true-listp pkt))
  :rule-classes :forward-chaining)

;; Packet detail accessors
(defund get-turn-signal (pkt g)
  (declare (xargs :guard (and (graphp g)
                              (packetp pkt g)))
           (ignore g))
  (cadr pkt))

(defund get-processed-bit (pkt g)
  (declare (xargs :guard (and (graphp g)
                              (packetp pkt g)))
           (ignore g))
  (caddr pkt))

(defund get-final-dest (pkt g)
  (declare (xargs :guard (and (graphp g)
                              (packetp pkt g)))
           (ignore g))
  (cadddr pkt))

(defund get-origin (pkt g)
  (declare (xargs :guard (and (graphp g)
                              (packetp pkt g)))
           (ignore g))
  (car (cddddr pkt)))

;  Link Table

;; Packets are stored on links.  A Link-table shows the state of all
;; the links in the network at a given time.  A link can either be
;; full or empty.

;; Linktable recognizer
(defun linktable-validp (x g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom x) (equal x nil))
   (t (let ((entry (car x)))
	(and (consp entry)
             (true-listp  entry)
	     (linkp (car entry) g)
             (if (endp (cdr entry))                  ;; Empty link
                 (linktable-validp (cdr x) g)
               (let ((pkt (cadr entry)))             ;; Full link
                 (and (true-listp pkt)
                      (packetp pkt g)
                      (linktable-validp (cdr x) g)))))))))

(defthm linktable-validp-implies-symbol-alistp
  (implies (linktable-validp lt g)
           (alistp lt)))
(defthm linktable-validp-implies-symbol-alistp-weaker
  (implies (and (bind-free '((g . g)))
                (linktable-validp lt g))
           (alistp lt)))
(defthm linktable-implies-alistp-update
  (implies (linktable-validp lt g)
           (alistp (update-alist key datum lt)))
  :hints (("Goal" :in-theory (disable packetp)))
  :rule-classes :type-prescription)
(defthm strip-cars-linktable-subsetp-linksg
  (implies (and (graphp g)
                (linktable-validp lt g))
           (link-listp (strip-cars lt)
                       g))
  :hints (("Goal" :in-theory (disable packetp))))


;  Packet accessor

;; Packet accessor function
(defun get-packet (lnk lt g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)))
           (ignore g))
  (if (consp (cdr (assoc-equal lnk lt)))
      (cadr (assoc-equal lnk lt))
    nil))


;; Lemmas for valid Packet Access
;; The 'get-packet' function returns a valid packet
(defthm get-packet-consp-asssoc
  (implies (and (graphp g)
                (linktable-validp lt g)
                (get-packet lnk lt g))
           (consp (cdr (assoc-equal lnk lt)))))
(defthm truelistp-get-packet
  (implies (and (graphp g)
                (linktable-validp lt g))
           (true-listp (get-packet x lt g))))
(defthm linktable-validp-implies-packetp
  (implies (and (graphp g)
		(linktable-validp lt g)
                (get-packet lnk lt g))
	   (packetp (get-packet lnk lt g)
		    g))
  :hints (("Goal" :in-theory (disable packetp))))
(defthm packetp-guards-1
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (consp (get-packet lnk lt g))))
(defthm packetp-guards-2
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (symbolp (car (get-packet lnk lt g)))))
(defthm packetp-guards-3
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (consp (cdr (get-packet lnk lt g)))))
(defthm packetp-guards-4
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (turn_signalp (get-turn-signal (get-packet lnk lt g) g)))
  :hints (("Goal" :in-theory (enable get-turn-signal))))
(defthm packetp-guards-5
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (consp (cddr (get-packet lnk lt g)))))
(defthm packetp-guards-6
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (bitp (get-processed-bit (get-packet lnk lt g) g)))
  :hints (("Goal" :in-theory (enable get-processed-bit))))
(defthm packetp-guards-7
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (consp (cdddr (get-packet lnk lt g)))))
(defthm packetp-guards-8
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (junctp (get-final-dest (get-packet lnk lt g) g) g))
  :hints (("Goal" :in-theory (enable get-final-dest))))
(defthm packetp-guards-9
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (consp (cddddr (get-packet lnk lt g)))))
(defthm packetp-guards-10
  (implies (and (graphp g)
                (linktable-validp lt g)
		(packetp (get-packet lnk lt g) g))
	   (junctp (get-origin (get-packet lnk lt g) g) g))
  :hints (("Goal" :in-theory (enable get-origin))))
(in-theory (disable get-packet packetp))



;  6. Link Accessors

;; Since packets are stored on the links, we need to be able to
;; identify a link, by looking at the two junctions it connects, and
;; further access the packet, if there is one, stored on the link.

;; Link lookup
;; Lemmas for inlink-access
(defthm graphp-implies-consp-get-source-link
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp dest g)
                (member-equal dest (strip-cars srlnks)))
           (consp (assoc-equal dest srlnks))))
(defthm graphp-implies-consp-links-list
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp dest g)
                (member-equal dest (strip-cars srlnks)))
           (consp (cdr (assoc-equal dest srlnks)))))
(defthm graphp-implies-symbolp-car-links-list
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp source g)
                (member-equal source (strip-cars srlnks)))
           (symbolp (cadr (assoc-equal source srlnks)))))
(defthm graphp-implies-member-equal-car-links-list-links
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp source g)
                (member-equal source (strip-cars srlnks)))
           (member-equal (cadr (assoc-equal source srlnks)) values)))

;; Lemmas for outlink-access
(defthm graphp-implies-consp-cdr-links-list
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp dest g)
                (member-equal dest (strip-cars srlnks)))
           (consp (cddr (assoc-equal dest srlnks)))))
(defthm graphp-implies-symbolp-cadr-links-list
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp dest g)
                (member-equal dest (strip-cars srlnks)))
           (symbolp (caddr (assoc-equal dest srlnks)))))
(defthm graphp-implies-member-equal-cadr-links-list-links
  (implies (and (graph1p g keys values)
                (source-linksp srlnks keys values)
                (junctp dest g)
                (member-equal dest (strip-cars srlnks)))
           (member-equal (caddr (assoc-equal dest srlnks)) values)))
(in-theory (disable source-linksp sources))


;; Output link accessor
(defund get-output-link (junct dest g)
  "Gets the output link from junct to dest"
  (declare (xargs :guard (and (graphp g)
			      (junctp junct g)
			      (junctp dest g)
                              (member-equal dest (sources junct g)))
                  :guard-hints (("Goal" :in-theory (enable sources)))))
  (caddr (assoc-equal dest (get-source-link junct g))))

;; Output link accessor
(defund get-input-link (junct source g)
  "Gets the input link from source to junct"
  (declare (xargs :guard (and (graphp g)
			      (junctp junct g)
			      (junctp source g)
                              (member-equal source (sources junct g)))
                   :guard-hints (("Goal" :in-theory (enable sources)))))
  (cadr (assoc-equal source (get-source-link junct g))))

;; Type prescription for outlinks and inlinks
(defthm linkp-get-output-link
  (implies (and (graphp g)
		(junctp junct g)
		(junctp dest g)
                (member-equal dest (sources junct g)))
	   (linkp (get-output-link junct dest g) g))
  :hints (("Goal" :in-theory (enable get-output-link sources))))
(defthm linkp-get-input-link
  (implies (and (graphp g)
		(junctp junct g)
		(junctp source g)
                (member-equal source (sources junct g)))
	   (linkp (get-input-link junct source g) g))
  :hints (("Goal" :in-theory (enable get-input-link sources))))



;   7. Current Inputs

; Matt K. addition for ACL2(r):
#+:non-standard-analysis
(local
 (defthm rationalp-implies-realp
   (implies (rationalp x)
            (realp x))))

;; Get-direction is a function that returns the position (north,
;; east, west or south) of a junction, junctA, in relation to another
;; connected junction, junctB. This is done by comparing either their
;; x- or y- coordinates.

(defund get-direction (junctA junctB g)
  (declare (xargs :guard (and (graphp g)
  			      (junctp junctA g)
  			      (junctp junctB g))))
  (if (member-equal junctB (sources junctA g))
      (let* ((junctA-x (car junctA))
	     (junctA-y (cdr junctA))
	     (junctB-x (car junctB))
	     (junctB-y (cdr junctB)))
	(cond
         ((< junctA-x junctB-x) 'E)
	 ((> junctA-x junctB-x) 'W)
	 ((< junctA-y junctB-y) 'N)
	 ((> junctA-y junctB-y) 'S)))
    nil))

(defthm directionp-get-direction
  (implies (and (graphp g)
                (junctp junctA g)
                (junctp junctB g)
                (get-direction junctA junctB g))
           (directionp (get-direction junctA junctB g)))
  :hints (("Goal" :in-theory (enable get-direction))))


;; In this system, we process packet movement from the perspective of
;; the output link; i.e., the link to which the packet is transferred.
;; This can be seen as a merge, where two links are merged into one.

;; Current-inputs checks the links feeding into an output link to know
;; if they have packets on them; it makes a list of these active
;; links.  In addition, it ensures that a packet moves at most once in
;; a cycle of the system by checking if it has been processed in the
;; current cycle.

(defun current-inputs (junct dest input-juncts lt g)
  (declare (xargs :guard (and (graphp g)
  			      (linktable-validp lt g)
  			      (junctp junct g)
  			      (junctp dest g)
  			      (true-listp input-juncts)
  			      (subsetp-equal input-juncts (sources junct g)))))
  (if (endp input-juncts)
      nil
    (let* ((lnk (get-input-link junct (car input-juncts) g)))
      (if (get-packet lnk lt g)
          (let* ((pkt (get-packet lnk lt g))
                 (turn-signal (get-turn-signal pkt g))
                 (isprocessed (get-processed-bit pkt g)))
	    (if (and (equal turn-signal (get-direction junct dest g))
                     (equal 0 isprocessed))
		(cons lnk
		      (current-inputs junct dest (cdr input-juncts) lt g))
	      (current-inputs junct dest (cdr input-juncts) lt g)))
	(current-inputs junct dest (cdr input-juncts) lt g)))))

;; Type prescription for current input
(defthm link-listp-current-inputs
  (implies (and (graphp g)
		(linktable-validp lt g)
		(junctp junct g)
		(junctp dest g)
		(true-listp input-juncts)
		(subsetp-equal input-juncts (sources junct g)))
	   (link-listp (current-inputs junct dest input-juncts lt g)
                       g)))


;  8. Terminal recognizer

;; A terminal is the entry or exit junction in the system.  A terminal
;; is characterized as having only one junction connected to it while
;; the other type of junctions (aka. repeaters) are connected to three
;; other nodes.

(defund isTerminal (junct g)
  (declare (xargs :guard (and (graphp g)
  			      (junctp junct g))))
  (let ((dests (sources junct g)))
    (atom (cdr dests))))

(defthm isTerminal-consp-sources
  (implies (and (graph1p g keys values)
                (junctp junct g)
                (isTerminal junct g))
           (consp (sources junct g)))
  :hints (("Goal" :in-theory (enable sources get-source-link isTerminal all-juncts))))




;   9. Routing Function

;                          PKT1   curr
;                 (2 . 2)------->(4 . 2)------->(6 . 2)  dest1
;                  past            |
;                                  |
;                                  v
;                               (4 . 0)  dest2

;; The routing function caluclates the next direction of a packet or
;; it returns if the packet has arrived at its destination.  This
;; function decides the packet direction by comparing the current
;; junction address with the final destination address and then picks
;; the possible next junction that is closest to the final address.

;; In the graph above, PKT1 is entering junction (4 . 2). The packet can
;; either go through junction (6 . 2) or (4 . 0) after leaving (4 . 2)
;; based on the final destination address in it.  For instance, if the
;; final destination address in the packet is (8 . 3), then the
;; function comapres (4 . 2), the current address and (8 . 3), the final
;; destination. Thereafter, the function makes a choice between the
;; possible next junctions, (6 . 2) and (4 . 0) based on which is closer
;; to (8 . 3).

;; Past - The junction from which the packet is leaving
;; Curr - The junction to which the packet is entering
;; Final - The final destination to which the packet is to be delivered
;; Dests - The list of possible next junctions that could be on the
;;         path to the final destination.

(defun routing-guard (past curr final g)
  (declare (xargs :guard t))
  (and (graphp g)
       (junctp past g)
       (junctp curr g)
       (junctp final g)))

(defun Routing (past curr final g)
  (declare (xargs :guard (routing-guard past curr final g)))
  (let ((dests (remove-equal past (sources curr g))))
    (cond

     ;; Case 1: If there is no junction in the list Dests, then the
     ;; packet is at its destination or there is an error
     ((atom dests) (if (equal curr final)
		       'Done
		     (cw "Bad route")))

    ;; Case 2: If there is only one junction in the list Dests, then
    ;; return the direction to the junction
     ((atom (cdr dests)) (get-direction curr (car dests) g))

    ;; Case 3: If there are two junctions, determine which junction
    ;; will take the packet closest to the final destination address
     ((atom (cddr dests))
      (let* ((dest1 (car dests))
             (dest2 (cadr dests))
             (dir1 (get-direction curr dest1 g))
             (dir2 (get-direction curr dest2 g)))
      (cond
       ((isTerminal dest1 g)  (if (equal dest1 final)
                                  dir1
                                (if (isTerminal dest2 g)
                                    (if (equal dest2 final)
                                        dir2
                                      (cw "Bad route"))
                                  dir2)))
       ((isTerminal dest2 g)  (if (equal dest2 final)
                                  dir2
                                dir1))
       (t
        (let ((curr-x (car curr))      (curr-y (cdr curr))
              (final-x (car final))    (final-y (cdr final))
              (dest1-x (car dest1))    (dest1-y (cdr dest1))
              (dest2-x (car dest2))    (dest2-y (cdr dest2)))
          (cond
           ((< curr-y final-y)   (cond
                                  ((< dest1-y dest2-y)
                                   (if (< final-y dest2-y)
                                       dir1
                                     (if (= final-y dest2-y)
                                         (if (< (abs (- dest1-x final-x))
                                                (abs (- dest2-x final-x)))
                                             dir1
                                           dir2)
                                       dir2)))
                                  ((= dest1-y dest2-y)
                                   (if (< (abs (- dest1-x final-x))
                                          (abs (- dest2-x final-x)))
                                       dir1
                                     dir2))
                                  (t (if (< final-y dest1-y)
                                         dir2
                                       (if (= final-y dest1-y)
                                           (if (< (abs (- dest1-x final-x))
                                                  (abs (- dest2-x final-x)))
                                               dir1
                                             dir2)
                                         dir1)))))
           ((> curr-y final-y) (cond
                                ((< dest1-y dest2-y)
                                 (if (= final-y dest1-y)
                                     (if (<= (abs (- dest1-x final-x))
                                             (abs (- dest2-x final-x)))
                                         dir1
                                       dir2)
                                   dir1))
                                ((= dest1-y dest2-y)
                                 (if (< (abs (- dest1-x final-x))
                                        (abs (- dest2-x final-x)))
                                     dir1
                                   dir2))
                                (t   (if (= final-y dest2-y)
                                         (if (<= (abs (- dest1-x final-x))
                                                 (abs (- dest2-x final-x)))
                                             dir1
                                           dir2)
                                       dir2))))
           ((< curr-x final-x) (if (< dest1-x dest2-x)
                                   dir2
                                 dir1))
           ((> curr-x final-x) (if (< dest1-x dest2-x)
                                   dir1
                                 dir2))))))))
     (t nil))))

;; The routing function produces a valid direction or a done tag


(defthm turn_signalp-routing
  (implies (and (graphp g)
                (junctp curr g)
                (junctp final g)
                (routing past curr final g))
           (turn_signalp (routing past curr final g)))
  :hints (("Goal" :in-theory (e/d (turn_signalp) (abs)))))


;  10. Arbiter

;; The Arbiter choosing between two inputs links vying for the same
;; output link when packets arrive on the input links at nearly the
;; same time.  Arbitration is based on the output link and to have
;; some mechanism of fairness in its decision making, it has a state
;; which records the decision from the provious cycle.

;; arbiter-state recognizer
(defun arbiter-statep (x g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom x) (equal x nil))
   (t (let ((entry (car x)))
	(and (consp entry)
             (linkp (car entry) g)
             (linkp (cdr entry) g)
             (arbiter-statep (cdr x) g))))))

(defthm arbiter-statep-implies-symbol-alistp
  (implies (arbiter-statep ast g)
           (symbol-alistp ast))
  :rule-classes :type-prescription)
(defthm strip-cars-arbiter-state-subsetp-linksg
  (implies (and (graphp g)
                (arbiter-statep ast g))
           (link-listp (strip-cars ast) g)))


(defun arbiter (outlink inputs ast g)
  (declare (xargs :guard (and (graphp g)
                              (link-listp inputs g)
  			      (linkp outlink g)
			      (arbiter-statep ast g)))
	   (ignore g))
  (let* ((entry (assoc-equal outlink ast)))
    (cond
     ((endp inputs)  (mv nil ast))
     ((endp (cdr inputs))  (mv (car inputs) ast))
     (t (if entry
            (let* ((last-choice (cdr entry))
                   (new-choice (car (remove1-equal last-choice inputs)))
                   (new-ast (update-alist outlink new-choice ast)))
              (mv new-choice new-ast))
          (let* ((choice (car inputs))
                 (new-ast (acons outlink choice ast)))
            (mv choice new-ast)))))))

;; The arbiter returns its choice of a link among the inputs given
(defthm linkp-arbiter
  (implies (and (graphp g)
		(arbiter-statep ast g)
                (link-listp inputs g)
                (consp inputs)
                (linkp outlink g))
	   (linkp (car (arbiter outlink inputs ast g))  g))
  :hints (("Goal" :in-theory (disable linkp update-alist arbiter-statep))))




;    11. Update link

;                          PKT1
;                 (2 . 2)------->(4 . 2)------->(6 . 2)
;                                  ||
;                                  VV
;                                        PKT1
;                 (2 . 2)------->(4 . 2)------->(6 . 2)


;; Since packets are stored on the links, the link table depicts the
;; state of the system by showing where the packets are located at a
;; given time.  Therefore, to model packet movement, we update the
;; linktable as long as some packet can move.

;; Algorithm:

;;  * Check if the receiving link (outlink) is empty.  If full, no
;;  * update is made.

;;  * Otherwise, the arbiter gives a chosen input link.  Check if the
;;    packet on the input link is valid

;;  * If the packet is valid, the routing function calculates and
;;    returns the packet's next ``turn_signal'' direction.

;;  * If the ``turn_signal'' is valid, repack the packet and update
;;    the linktable by adding it to output link.  Then, update the
;;    linktable to remove the old packet from the input link.

;;  * Otherwise, make no changes to the linktable.


(defun update-link (junct dest lt ast g MS)
  "Moves the packet on an input link to an output link"
  (declare (xargs :guard (and (graphp g)
  			      (linktable-validp lt g)
  			      (junctp junct g)
  			      (junctp dest g)
  			      (arbiter-statep ast g)
                              (member-equal dest (sources junct g)))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable routing arbiter junctp)))))
  (if MS
      (mv MS lt ast)
    (let* ((outlink (get-output-link junct dest g)))
      (if (get-packet outlink lt g)
          (mv MS lt ast)
        (let* ((stack (remove-equal dest (sources junct g)))
               (inputs (current-inputs junct dest stack lt g)))
          (if (endp inputs)
              (mv MS lt ast)
            (mv-let (input new-ast)
              (arbiter outlink inputs ast g)
              (if (null (get-packet input lt g))
                  (mv "Invalid input, problem from the Arbiter" lt ast)
                (let* ((pkt (get-packet input lt g))
                       (final (get-final-dest pkt g))
                       (turn_signal (routing junct dest final g)))
                  (if (turn_signalp turn_signal)
                      (let* ((new-pkt (list* (car pkt) turn_signal 1 (cdddr pkt)))
                             (new-link-state (update-alist outlink (list new-pkt) lt))
                             (new-lt (update-alist input nil new-link-state)))
                        (mv MS new-lt new-ast))
                    (mv turn_signal lt new-ast)))))))))))

; Preservation Lemma for Update-link

;; Update-Link produces a valid linktable
(defthm linktable-update-nil
  (implies (and (graphp g)
                (linktable-validp lt g))
           (linktable-validp (update-alist lnk nil lt)
                             g)))
(defthm linktable-update-newpkt
  (implies (and (graphp g)
                (linktable-validp lt g)
                (packetp newpkt g))
           (linktable-validp (update-alist lnk (list newpkt) lt)
                             g)))
(defthm packetp-make_new_packet
  (implies (and (graphp g)
                (linktable-validp lt g)
                (packetp pkt g)
                (turn_signalp turn_signal)
                (bitp num))
           (packetp (list* (car pkt) turn_signal num (cdddr pkt))
                    g))
   :hints (("goal" :in-theory (enable packetp))))
(defthm  update-link-linktable-validp
  (implies
   (and (graphp g)
        (linktable-validp lt g)
        (junctp junct g)
        (junctp dest g)
        (arbiter-statep ast g))
   (linktable-validp (mv-nth 1 (update-link junct dest lt ast g MS))
                     g))
  :hints (("Goal" :in-theory (disable routing arbiter)
                  :do-not-induct t)))

;; Update-Link produces a valid arbiter state
(defthm arbiter-statep-update-pref
           (implies (and (graphp g)
                         (arbiter-statep ast g)
                         (linkp outlink g)
                         (linkp choice g))
                    (arbiter-statep (update-alist outlink choice ast) g)))
(defthm arbiter-arbiter-statep
           (implies (and (graphp g)
                         (link-listp inputs g)
                         (linkp outlink g)
                         (arbiter-statep ast g))
                    (arbiter-statep (mv-nth 1 (arbiter outlink inputs ast g))
                                     g)))
(defthm update-link-arbiter-statep
    (implies (and (graphp g)
                  (linktable-validp lt g)
                  (junctp junct g)
                  (junctp dest g)
                  (arbiter-statep ast g)
                  (member-equal dest (sources junct g)))
             (arbiter-statep (mv-nth 2 (update-link junct dest lt ast g MS))
                              g))
    :hints (("Goal" :in-theory (disable routing arbiter)
                    :do-not-induct t)))




;    12. Process-Junction

;; When any of the input links to a junction are full, we process the
;; junction to move the packets to the output links when possible.
;; This means that, packet traffic is processed in all the directions
;; of the neighbors of the junction.  The argument 'neighbors' is the
;; list of nodes in each direction from the junction.

(defun process-junct (junct neighbors lt ast g MS)
  (declare (xargs :guard (and (graphp g)
  			      (linktable-validp lt g)
  			      (junctp junct g)
  			      (arbiter-statep ast g)
                              (true-listp neighbors)
  			      (subsetp-equal neighbors (sources junct g)))
                  :guard-hints (("Goal" :in-theory (disable update-link)
                                        :do-not-induct t))))
  (if MS
      (mv MS lt ast)
    (if (endp neighbors)
        (mv MS lt ast)
      (b* ((dest (car neighbors))
           ((mv new-MS new-lt new-ast) (update-link junct dest lt ast g MS)))
        (process-junct junct (cdr neighbors) new-lt new-ast g new-MS)))))

; Preservation Lemma for Process-junct

;; Process-junct produces a valid linktable
(defthm process-junct-linktable-validp
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (junctp junct g)
             (arbiter-statep ast g)
	     (true-listp neighbors)
  	     (subsetp-equal neighbors (sources junct g)))
        (linktable-validp (mv-nth 1 (process-junct junct neighbors lt ast g MS))
                          g))
   :hints (("Goal" :in-theory (disable update-link arbiter routing))))

;; Process-junct produces a valid arbiter-state
(defthm process-junct-arbiter-statep
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (junctp junct g)
             (arbiter-statep st g)
	     (true-listp neighbors)
  	     (subsetp-equal neighbors (sources junct g)))
        (arbiter-statep (mv-nth 2 (process-junct junct neighbors lt st g MS))
                          g))
  :hints (("Goal" :in-theory (disable update-link arbiter routing))))



;     13.  Single step

;; The 'Single-step' function is a single cycle of execution in the
;; system.  That is, all packets in the system take at most one step.
;; The 'Junct-list' argument is the list of junctions with packets on
;; its input links.

(defun Single-step (junct-list lt ast g MS)
  "Run the interpreter once"
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (arbiter-statep ast g)
                              (true-listp junct-list)
                              (subsetp-equal junct-list (all-juncts g)))
                  :guard-hints (("Goal" :in-theory (disable process-junct)))))
  (if MS
      (mv MS lt ast)
    (if (endp junct-list)
        (mv MS lt ast)
      (b* ((junct (car junct-list))
           (neighbors (sources junct g))
           ((mv new-MS new-lt new-ast)
            (process-junct junct neighbors lt ast g MS)))
        (Single-step (cdr junct-list) new-lt new-ast g new-MS)))))

; Preservation Lemma for Process-junct

;; Single-step produces a valid linktable
(defthm Single-step-linktable-validp
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (arbiter-statep ast g)
	     (true-listp junct-list)
  	     (subsetp-equal junct-list (all-juncts g)))
        (linktable-validp (mv-nth 1 (Single-step junct-list lt ast g MS))
                          g))
  :hints (("Goal" :in-theory (disable process-junct update-link arbiter
                                      routing))))
;; Single-step produces a valid arbiter-state
(defthm Single-step-arbiter-statep
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (arbiter-statep st g)
	     (true-listp junct-list)
  	     (subsetp-equal junct-list (all-juncts g)))
        (arbiter-statep (mv-nth 2 (Single-step junct-list lt st g MS))
                          g))
  :hints (("Goal" :in-theory (disable process-junct update-link arbiter routing))))



;    14. Inverse map

;; To reduce the amount of computation, we decide to process junctions
;; only when one (or more) of their their input links are full.
;; Therefore, before the system may take a step, we do a preprocessing
;; check to collect the list of junctions with current inputs.

;; To aid this process, we need a mechanism to get the junctions to
;; which a link connects.  Therefore, we calculate the ``inverse
;; map'', which is a map of each link to its input and output
;; junctions (joints); i.e., the junction at its head and at its tail.

;; An inverse-map is an alist of link names and their corresponding
;; connecting junctions.

;; For example, ((S2 (0 . 2) (2 . 2)) (S1 (2 . 2) (0 . 2)) ...)
;; For link S2, (0 . 2) is its input junction and (2 . 2) is its
;; output junction.

;; Inverse map recognizer
(defun inverse-map-p (x g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom x) (equal x nil))
   (t (let ((entry (car x)))
	(and (consp entry)
             (true-listp  entry)
	     (linkp (car entry) g)
             (consp (cdr entry))
             (alistp (cdr entry))
             (junctp (cadr entry) g)
             (junctp (caddr entry) g)
             (inverse-map-p (cdr x) g))))))

;; Output Junction accessor
(defund get-output-junct (lnk imap g)
  (declare (xargs :guard (and (graphp g)
                              (inverse-map-p imap g)
                              (linkp lnk g)))
           (ignore g))
  (if (member-equal lnk (strip-cars imap))
      (caddr (assoc-equal lnk imap))
    nil))

(defthm junctp-get-output-junct-inverse-map
  (implies (and (graphp g)
                (inverse-map-p imap g)
		(member-equal lnk (strip-cars imap)))
           (member-equal (get-output-junct lnk imap g) (all-juncts g)))
  :hints (("Goal" :in-theory (enable get-output-junct))))

;; Input Junction accessor
(defund get-input-junct (lnk imap g)
  (declare (xargs :guard (and (graphp g)
                              (inverse-map-p imap g)
                              (linkp lnk g)))
           (ignore g))
  (if (member-equal lnk (strip-cars imap))
      (cadr (assoc-equal lnk imap))
    nil))

(defthm junctp-get-input-junct-inverse-map
  (implies (and (graphp g)
                (inverse-map-p imap g)
		(member-equal lnk (strip-cars imap)))
           (member-equal (get-output-junct lnk imap g) (all-juncts g)))
  :hints (("Goal" :in-theory (enable get-output-junct))))

(defthm link-listp-strip-cars-inverse-map
  (implies (and (graphp g) (inverse-map-p imap g))
           (link-listp (strip-cars imap) g)))


;; Get-junct-list function collects the junctions with current inputs
;; before each cycle of the system.
(defun get-junct-list (lt imap g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (inverse-map-p imap g))
                  :guard-hints (("Goal" :in-theory (disable linkp)))))
  (if (endp lt)
      nil
    (let* ((entry (car lt))
           (linkname (car entry)))
      (if (consp (cdr entry))
          (if (member-equal linkname (strip-cars imap))
              (cons (get-output-junct linkname imap g)
                    (get-junct-list  (cdr lt) imap g))
            (get-junct-list (cdr lt) imap g))
        (get-junct-list (cdr lt) imap g)))))

(defthm subsetp-get-junct-list-all-juncts
  (implies (and (graphp g)
                (linktable-validp lt g)
                (inverse-map-p imap g))
           (subsetp-equal (get-junct-list lt imap g) (all-juncts g))))


;    15. Adding new packets into the network

;; Packets are added to the network through the terminals.  Such
;; externally-arriving packets are viewed as a stream of input that is
;; then split into valid packets.

;; In the packet-input stream, each input is a list that contains: a
;; packet id, a final destination address, and an origin address
;; (point of entry to the network).

;; Input recognizer
(defun valid-input (input g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom input) (equal input nil))
   (t (let ((entry (car input)))
        (and (consp entry)
             (true-listp entry)
             (symbolp (car entry))  ;pktid
             (consp (cdr entry))
             (junctp (cadr entry) g) ;final
             (consp (cddr entry))
             (junctp (caddr entry) g)  ; source
             (consp (cdddr entry))
             (true-listp (cdddr entry))
             (valid-input (cdr input) g))))))

(defun valid-input-stream (input-stream g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom input-stream) (equal input-stream nil))
   (t (and (valid-input (car input-stream) g)
           (valid-input-stream (cdr input-stream) g)))))

;; When packing the packets we make sure that they are assigned the
;; right advance turn-signal.
(defun add-new-packets (input lt g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (valid-input input g))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (e/d (packetp) (routing))))))
  (if (endp input)
      lt
    (let* ((entry (car input))
           (pktid (car entry))
           (final (cadr entry))
           (source (caddr entry))
           (data (cadddr entry)))
      (if (isTerminal source g)
          (let* ((junctB (car (sources source g)))
                 (turn_signal (routing source junctB final g)))
            (if (turn_signalp turn_signal)
                (let* ((pkt (list pktid turn_signal 1 final source data))
                       (outlink (get-output-link source junctB g))
                       (new-lt (update-alist outlink (list pkt) lt)))
                  (add-new-packets (cdr input) new-lt g))
              (add-new-packets (cdr input) lt g)))
        lt))))

;; Lemma showing that adding new packets to the link table still
;; preserves its validity.
(defthm add-new-packets-linktable-validp
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (valid-input input g))
        (linktable-validp (add-new-packets input lt g)
                          g))
   :hints (("Goal" :in-theory (e/d (packetp) (routing)))))


;    16. Removing delivered packets from the network

;; Packets that have reached their destination need to leave the
;; network.  We keep a global history of the delivered packets.  This
;; might help with later proofs.

;; Global history recognizer
(defun delivery-history-p (hist g)
  (declare (xargs :guard (graphp g)))
  (cond
   ((atom hist) (equal hist nil))
   (t (and (true-listp (car hist))
           (packetp (car hist) g)
           (delivery-history-p (cdr hist) g)))))

(defun remove-delivered-packets (hist lnk-lst lt g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (delivery-history-p hist g))))
  (if (atom lnk-lst)
      (mv lt hist)
      (if (get-packet (car lnk-lst) lt g)
          (let* ((pkt (get-packet (car lnk-lst) lt g))
                 (turn_signal (get-turn-signal pkt g))
                 (isprocessed (get-processed-bit pkt g)))
            (if (and (equal turn_signal 'Done)
                     (equal 0 isprocessed))
                (let ((new-hist (cons (get-packet (car lnk-lst) lt g)
                                               hist))
                      (new-lt (update-alist (car lnk-lst) nil lt)))
                  (remove-delivered-packets new-hist (cdr lnk-lst) new-lt g))
              (remove-delivered-packets hist (cdr lnk-lst) lt g)))
        (remove-delivered-packets hist (cdr lnk-lst) lt g))))

;; Lemma showing that removing packets from the linktable still
;; preserves its validity

(defthm still-valid-delivery-history
  (implies (and (graphp g)
                (packetp pkt g)
                (delivery-history-p hist g))
           (delivery-history-p (cons pkt hist) g)))

(defthm remove-delivered-packets-linktable-validp
   (implies
        (and (graphp g)
             (linktable-validp lt g)
             (delivery-history-p hist g))
        (linktable-validp (car (remove-delivered-packets hist lnk-lst lt g))
                          g)))
(defthm remove-delivered-packets-delivery-history-p
  (implies
        (and (graphp g)
             (linktable-validp lt g)
             (delivery-history-p hist g))
        (delivery-history-p (mv-nth 1 (remove-delivered-packets hist lnk-lst lt g))
                            g)))



;     17.  Resetting the processed bit of each packet


;; To ensure that a packet takes at most one step in a cycle of the
;; system, we added a bit to each packet. This bit indicates if the
;; packet has been processsed in the current single-step cycle or not.
;; Therefore, after each cycle, the bit has to be cleared. Note that
;; this is only necessary in this current implementation. It would not
;; be necessary when looking at packets moving at their own rates.

(defun reset_process_bit (lnk-lst lt g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g))))
  (if (atom lnk-lst)
      lt
    (if (get-packet (car lnk-lst) lt g)
          (let* ((pkt (get-packet (car lnk-lst) lt g))
                 (new-pkt (list* (car pkt) (get-turn-signal pkt g) 0 (cdddr pkt)))
                 (new-lt (update-alist (car lnk-lst) (list new-pkt) lt)))
            (reset_process_bit (cdr lnk-lst) new-lt g))
      (reset_process_bit (cdr lnk-lst) lt g))))

(defthm reset_process_bit-linktable-validp
   (implies
        (and (graphp g)
             (linktable-validp lt g))
        (linktable-validp (reset_process_bit lnk-lst lt g)
                          g)))



;     18. Multi-step

;; The "multi-step" function runs multiple iterations of the system.
;; This function runs as long as there is input to the system.

;; How multi-step works :
;;  * scan the link table for junctions with current inputs
;;  * add new packets
;;  * run the step junction on the list of junctions with current inputs before
;; the addition of new packets
;;  * removes any delivered packets
;;  * reset the processed_bits of the packets
;;  * repeat


(defun multi-step (input-stream hist lt imap ast g MS)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (arbiter-statep ast g)
                              (inverse-map-p imap g)
                              (valid-input-stream input-stream g)
                              (delivery-history-p hist g))
                  :guard-hints (("Goal"
                                 :in-theory (disable add-new-packets
                                                     remove-delivered-packets
                                                     Single-step)))))
  (if MS
      (mv MS nil)
    (if (endp input-stream)
        (mv lt hist)
      (b* ((junct-list (get-junct-list lt imap g))
           (trans-lt1 (add-new-packets (car input-stream) lt g))
           ((mv new-MS trans-lt2 new-ast)
            (Single-step junct-list trans-lt1 ast g MS))
           ((mv trans-lt3 new-hist)
            (remove-delivered-packets hist (strip-cars lt) trans-lt2 g))
           (new-lt (reset_process_bit (strip-cars trans-lt3) trans-lt3 g)))
        (multi-step (cdr input-stream) new-hist new-lt imap new-ast g new-MS)))))



;  19. Trace Function

;; To see the transition of the packet from one link to another, we
;; can project just the full links in the linktable at each iteration
;; of the system.  This works exactly like the multi-step function.
;; However, instead of returning the full linktable at the end of all
;; the iterations of the system, it returns a projection at each
;; iteration.


;; Helper function which prints out only the populated links in the linktable
(defun projection (lt g)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g))))
  (if (endp lt)
      nil
    (let ((entry (car lt)))
      (if (consp (cdr entry))
          (cons entry
                (projection (cdr lt) g))
        (projection (cdr lt) g)))))


(defun trace-pkts (input-stream hist lt imap ast g MS)
  (declare (xargs :guard (and (graphp g)
                              (linktable-validp lt g)
                              (arbiter-statep ast g)
                              (inverse-map-p imap g)
                              (valid-input-stream input-stream g)
                              (delivery-history-p hist g))
                  :guard-hints (("Goal"
                                 :in-theory (disable add-new-packets packetp
                                                     remove-delivered-packets
                                                     Single-step)))))
  (if MS
      MS
    (if (endp input-stream)
        nil
      (b* ((junct-list (get-junct-list lt imap g))
           (trans-lt1 (add-new-packets (car input-stream) lt g))
           ((mv new-MS trans-lt2 new-ast)
            (Single-step junct-list trans-lt1 ast g MS))
           ((mv trans-lt3 new-hist)
            (remove-delivered-packets hist (strip-cars lt) trans-lt2 g))
           (new-lt (reset_process_bit (strip-cars trans-lt3) trans-lt3 g)))
        (cons (list (projection new-lt g) new-hist)
              (trace-pkts (cdr input-stream) new-hist new-lt imap new-ast g new-MS))))))



;    20. Construct Linktable and Inverse graph from network example


;; Build an empty link table for the network
;; For example,
;; (DEFCONST *LT*
;;    '((S2) (S1) (S4) (S3) (S6) (S5) (S8) (S7) ...))

(defun construct-linktable (network)
  (declare (xargs :guard (graphp network)))
      (b* ((links (remove-duplicates-equal (links (strip-cars network) network)))
           (length (len links))
           (nil-list (repeat length nil))
           (linktable (pairlis$ links nil-list)))
        linktable))

(defmacro create-linktable (name network)
  `(defconst ,name (construct-linktable ,network)))



;; Build the inverse graph of the network.
;; Here, the network is represented as a collections of links and the junctions
;; at the head and tail of each link.
;; For example,
;; (DEFCONST *IMAP*
;;    '((S2 (0 . 2) (2 . 2))
;;      (S1 (2 . 2) (0 . 2))
;;      (S4 (2 . 2) (4 . 2))
;;      (S3 (4 . 2) (2 . 2)) ...)

(encapsulate
  ()
  (defun scan-inner (source neighbors inverse-graph network)
    (declare (xargs :guard (and (graphp network)
                                (junctp source network)
                                (true-listp neighbors)
                                (subsetp-equal neighbors (sources source network))
                                (symbol-alistp inverse-graph))))
    (if (endp neighbors)
        inverse-graph
      (let* ((target (car neighbors))
             (linkname (get-output-link source target network))
             (new-inverse-graph (update-alist linkname (list source target)
                                              inverse-graph)))
        (scan-inner source (cdr neighbors) new-inverse-graph
                    network))))
  (local (defthm symbol-alistp-scan-inner
           (implies
            (and (graphp network)
                 (junctp source network)
                 (true-listp neighbors)
                 (subsetp-equal neighbors (sources source network))
                 (symbol-alistp inverse-graph))
            (symbol-alistp (scan-inner source neighbors inverse-graph
                                       network)))))
  (defun scan-outer (junct-list inverse-graph network)
    (declare (xargs :guard (and (graphp network)
                                (symbol-alistp inverse-graph)
                                (true-listp junct-list)
                                (subsetp-equal junct-list (all-juncts
                                                           network)))))
    (if (endp junct-list)
        inverse-graph
      (let* ((source (car junct-list))
             (new-inverse-graph (scan-inner source (sources source network)
                                            inverse-graph network)))
        (scan-outer (cdr junct-list) new-inverse-graph network))))
  (local (defthm symbol-alistp-pairlis$
           (implies (symbol-listp x)
                    (symbol-alistp (pairlis$ x (repeat (len x) nil))))))

  (defun construct-inverse-graph (network)
    (declare (xargs :guard (graphp network)))
    (let* ((links (remove-duplicates-equal (links (strip-cars network) network)))
           (length (len links))
           (nil-list (repeat length nil))
           (links-alist (pairlis$ links nil-list))
           (inverse-graph (scan-outer (all-juncts network) links-alist network)))
      inverse-graph)))

(defmacro create-inverse-graph (name network)
  `(defconst ,name (construct-inverse-graph ,network)))
