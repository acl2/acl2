(FUNPOL::DEG)
(FUNPOL::NATP-DEG (76 38
                      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
                  (56 10
                      (:REWRITE FUTER::|a < b or b < a or a = b|))
                  (50 5 (:REWRITE FUTER::|a < b => ~(b < a)|))
                  (28 28 (:REWRITE DEFAULT-CAR))
                  (25 25 (:REWRITE DEFAULT-CDR))
                  (15 15 (:TYPE-PRESCRIPTION FUTER::<))
                  (14 12 (:REWRITE DEFAULT-<-1))
                  (12 12 (:REWRITE DEFAULT-<-2))
                  (10 10
                      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
                  (10 10
                      (:REWRITE FUTER::|a < b & b < c => a < c|))
                  (5 5 (:DEFINITION FUMON::NULOP))
                  (2 2
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FUNPOL::=-IMPLIES-EQUAL-DEG-A
     (92 92 (:REWRITE DEFAULT-CAR))
     (70 14
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (63 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (59 59 (:REWRITE DEFAULT-CDR))
     (55 14
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (55 14
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (28 28
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (21 21 (:TYPE-PRESCRIPTION FUTER::<))
     (14 14
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (12 6
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG)))
(FUNPOL::=-IMPLIES-EQUAL-DEG-B
     (92 92 (:REWRITE DEFAULT-CAR))
     (70 14
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (63 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (59 59 (:REWRITE DEFAULT-CDR))
     (55 14
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (55 14
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (28 28
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (21 21 (:TYPE-PRESCRIPTION FUTER::<))
     (14 14
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (12 6
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG)))
(FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|
 (364 1 (:DEFINITION FUPOL::FN))
 (331 67
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (294 1 (:DEFINITION FUPOL::+-MONOMIO))
 (267 27
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (251 224 (:REWRITE DEFAULT-CAR))
 (227 227 (:REWRITE DEFAULT-CDR))
 (170 14
      (:REWRITE
           FUPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (167 82
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (150 4 (:REWRITE FUPOL::FN-ORDENADO))
 (132 132
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (132 132
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (132
  7
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (85 67
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (72 2
     (:REWRITE FUPOL::|primero (p1 * p2) != 0|))
 (58 1
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (14 2
     (:REWRITE FUPOL::|p != 0 => m *M p != 0|))
 (9 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (7 7
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-*))
 (2 2 (:TYPE-PRESCRIPTION ATOM))
 (2 2 (:REWRITE FUPOL::POLINOMIOP-FN))
 (2 2 (:REWRITE FUPOL::POLINOMIOP-*))
 (1 1 (:DEFINITION FUMON::+)))
(FUNPOL::|FUMON::termino (* m1 m2) =e FUMON::termino m1 ACL2::+ FUMON::termino m2|)
(FUNPOL::|deg (p1 * p2) =e deg p1 ACL2::+ deg p2|
     (352 80
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (258 26
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (213 213 (:REWRITE DEFAULT-CDR))
     (204 204 (:REWRITE DEFAULT-CAR))
     (136 136
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (116 80
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (40 22 (:REWRITE DEFAULT-+-2))
     (40 22 (:REWRITE DEFAULT-+-1))
     (40 20
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (36 36
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (24 9 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (8 8 (:TYPE-PRESCRIPTION ATOM))
     (8 8 (:DEFINITION ATOM))
     (6 6 (:REWRITE FUTER::|~(a < a)|))
     (3 3
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*)))
(FUNPOL::|deg p1 <= deg (p1 * p2)|
     (48 48
         (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
     (30 6
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (26 4 (:DEFINITION FUPOL::POLINOMIOP))
     (20 20 (:REWRITE DEFAULT-CDR))
     (18 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (16 16 (:REWRITE DEFAULT-CAR))
     (12 12
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (12 12
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (6 6
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (3 1 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE DEFAULT-<-2))
     (2 1 (:REWRITE DEFAULT-+-2))
     (2 1 (:REWRITE DEFAULT-+-1)))
(FUNPOL::|deg p2 <= deg (p1 * p2)|
     (66 8 (:DEFINITION FUPOL::POLINOMIOP))
     (50 10
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (48 48
         (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
     (40 40 (:REWRITE DEFAULT-CDR))
     (32 32 (:REWRITE DEFAULT-CAR))
     (24 12
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (20 20
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (20 20
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (18 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (10 10
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 2 (:REWRITE DEFAULT-+-2))
     (4 2 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE DEFAULT-<-2)))
(FUNPOL::LC)
(FUNPOL::|FLD::fdp (lc p)| (30 6
                               (:REWRITE FUTER::|a < b or b < a or a = b|))
                           (27 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
                           (19 19 (:REWRITE DEFAULT-CAR))
                           (16 16 (:REWRITE DEFAULT-CDR))
                           (12 12
                               (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
                           (12 12
                               (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
                           (9 9 (:TYPE-PRESCRIPTION FUTER::<))
                           (6 6
                              (:REWRITE FUTER::|a < b & b < c => a < c|)))
(FUNPOL::|primero -p FUMON::= FUMON::- primero p|
     (82 18
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (80 8 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (58 48 (:REWRITE DEFAULT-CAR))
     (41 41 (:REWRITE DEFAULT-CDR))
     (32 32
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (24 18
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (13 7
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO)))
(FUNPOL::|resto -p = - resto p|
     (302 125 (:REWRITE DEFAULT-CDR))
     (161 161 (:REWRITE DEFAULT-CAR))
     (88 62
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (84 6 (:TYPE-PRESCRIPTION FLD::FDP-+))
     (36 3
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (16 14
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (15 3
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1)))
(FUNPOL::|nil + p = p|)
(FUNPOL::|FUMON::termino (- m) =e FUMON::termino m|)
(FUNPOL::|FUMON::monomiop (primero p)| (1 1 (:REWRITE DEFAULT-CAR)))
(FUNPOL::|not FUMON::nulop (primero p)|
     (7 1 (:DEFINITION FUPOL::POLINOMIOP))
     (4 1
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE DEFAULT-CDR)))
(FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|
     (43 4 (:DEFINITION FUPOL::POLINOMIOP))
     (25 5
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (21 21 (:REWRITE DEFAULT-CAR))
     (20 20 (:REWRITE DEFAULT-CDR))
     (12 6
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (10 10
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (10 10
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (5 5
        (:REWRITE FUTER::|a < b & b < c => a < c|)))
(FUNPOL::|FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|
     (21 21 (:REWRITE DEFAULT-CAR))
     (19 2 (:DEFINITION FUPOL::POLINOMIOP))
     (15 3
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (14 2 (:REWRITE FUMON::TERMINO-MONOMIO))
     (10 10 (:REWRITE DEFAULT-CDR))
     (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (6 6
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (6 6
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (6 6
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (6 2 (:TYPE-PRESCRIPTION FLD::FDP_-))
     (6 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (3 3
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|deg (- p) =e deg p|
     (27 3 (:DEFINITION FUPOL::POLINOMIOP))
     (25 25 (:REWRITE DEFAULT-CAR))
     (25 5
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (18 6 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (18 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (15 15 (:REWRITE DEFAULT-CDR))
     (14 2 (:REWRITE FUMON::TERMINO-MONOMIO))
     (11 3
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (10 10
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (10 10
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (6 6
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (6 2 (:TYPE-PRESCRIPTION FLD::FDP_-))
     (5 5
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (3 3
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|primero p FUPOL::+-monomio resto p =e p|
     (397 77
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (274 272 (:REWRITE DEFAULT-CDR))
     (212 212 (:REWRITE DEFAULT-CAR))
     (159 77
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (159 16
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (78 42
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (12 3
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (12 3
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1)))
(FUNPOL::|- nil =e nil|)
(FUNPOL::|- p =e FUPOL::- p|)
(FUNPOL::|- (m +Mo p) = (- m) +Mo (- p)|
     (422 10
          (:REWRITE FUPOL::|- p =e (- mp(p)) +M (- (resto(p)))|))
     (382 15
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (159 29
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (118 6 (:REWRITE FLD::|a + b = b + a|))
     (116 116 (:REWRITE DEFAULT-CAR))
     (102 7
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (96 96 (:REWRITE DEFAULT-CDR))
     (72 8 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (30 14
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (29 29
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (28 14
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (22 1
         (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
     (16 7
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (12 12 (:TYPE-PRESCRIPTION FUNPOL::NULO))
     (2 2 (:TYPE-PRESCRIPTION ATOM))
     (2 2
        (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO))
     (2 2 (:DEFINITION ATOM))
     (1 1 (:TYPE-PRESCRIPTION FUMON::NULOP)))
(FUNPOL::|p + q FUPOL::=P mp(p) +Mo (resto(p) + q)-lemma|
 (997 3 (:DEFINITION FUPOL::+-MONOMIO))
 (612 4 (:DEFINITION FUPOL::FN))
 (505
  15
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (392 15 (:DEFINITION FUPOL::POLINOMIOP))
 (287 16
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (248 31
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (168 32
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (147 147 (:REWRITE DEFAULT-CDR))
 (144 3
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (141 126 (:REWRITE DEFAULT-CAR))
 (101 3 (:DEFINITION FUMON::+))
 (98 2 (:REWRITE FLD::|a + b = b + a|))
 (84 84 (:TYPE-PRESCRIPTION FUPOL::+))
 (78 39
     (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
 (77 31
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (68 68
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (68 68
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (68 3
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (42 1
     (:REWRITE FUPOL::|q + p = mp(p) +M (q + resto(p))|))
 (36 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (32 32
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (19 19 (:REWRITE FUPOL::POLINOMIOP-+))
 (15 15
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
 (5 5 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (4 4
    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::=))
 (3 3 (:REWRITE FUPOL::POLINOMIOP-FN))
 (2 2
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)-lemma-a|
    (13105 12873 (:REWRITE DEFAULT-CDR))
    (9019 8758 (:REWRITE DEFAULT-CAR))
    (6597 30
          (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
    (5142 83
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
    (3129 2181
          (:REWRITE FUTER::|a < b & b < c => a < c|))
    (2262 83
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
    (2184 2184 (:TYPE-PRESCRIPTION FUPOL::+))
    (716 85
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
    (542 13
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
    (281 281
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
    (216 6
         (:REWRITE FUNPOL::|primero p FUPOL::+-monomio resto p =e p|))
    (42 42 (:TYPE-PRESCRIPTION ATOM))
    (4 4
       (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO)))
(FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|)
(FUNPOL::|=-implies-=-FUPOL::+-monomio-2a|
     (214 2 (:DEFINITION FUPOL::+-MONOMIO))
     (160 6 (:DEFINITION FUPOL::POLINOMIOP))
     (135 6
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (59 11
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (44 44 (:REWRITE DEFAULT-CAR))
     (40 40 (:REWRITE DEFAULT-CDR))
     (27 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (24 24
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (24 24
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (13 9 (:DEFINITION FUMON::NULOP))
     (12 2 (:DEFINITION FUMON::+))
     (11 11
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (10 2 (:REWRITE FLD::|a + b = b + a|))
     (4 4
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (4 4 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|=-implies-=-FUPOL::+-monomio-2b|
     (214 2 (:DEFINITION FUPOL::+-MONOMIO))
     (160 6 (:DEFINITION FUPOL::POLINOMIOP))
     (135 6
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (59 11
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (44 44 (:REWRITE DEFAULT-CAR))
     (40 40 (:REWRITE DEFAULT-CDR))
     (27 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (24 24
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (24 24
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (13 9 (:DEFINITION FUMON::NULOP))
     (12 2 (:DEFINITION FUMON::+))
     (11 11
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (10 2 (:REWRITE FLD::|a + b = b + a|))
     (4 4
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (4 4 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|q + p = mp(q) +Mo (resto(q) + p)|
     (1389 7 (:DEFINITION FUPOL::+-MONOMIO))
     (1018 46
           (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (401 75
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (384 61
          (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (295 295 (:REWRITE DEFAULT-CDR))
     (252 252 (:REWRITE DEFAULT-CAR))
     (163 163
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (163 163
          (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (134 6
          (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
     (127 75
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (121 13
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (37 19
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (20 7
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (20 7
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (12 7 (:DEFINITION FUMON::+))
     (7 7 (:REWRITE FUTER::|~(a < a)|))
     (5 1 (:REWRITE FLD::|a + b = b + a|))
     (2 2
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (1 1
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|
     (3081 623
           (:REWRITE FUTER::|a < b or b < a or a = b|))
     (2184 2184 (:REWRITE DEFAULT-CDR))
     (1893 1893 (:REWRITE DEFAULT-CAR))
     (1691 53
           (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
     (1229 1229
           (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (1070 117
           (:REWRITE FUTER::|a < b => ~(b < a)|))
     (820 623
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (464 232
          (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (75 28
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (75 28
         (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (15 3 (:REWRITE FLD::|a + b = b + a|))
     (3 3
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|
   (31318 343
          (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
   (22360 320
          (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
   (17115 3189
          (:REWRITE FUTER::|a < b or b < a or a = b|))
   (11784 11784 (:REWRITE DEFAULT-CDR))
   (10555 185 (:DEFINITION FUPOL::>-MONOMIO))
   (9796 9796 (:REWRITE DEFAULT-CAR))
   (6963 6963
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
   (6899 3189
         (:REWRITE FUTER::|a < b & b < c => a < c|))
   (5457 286
         (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
   (3262 349
         (:REWRITE FUTER::|a < b => ~(b < a)|))
   (1235 420
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
   (1060 1060
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
   (829 262
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
   (829 262
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
   (480 50
        (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
   (185 185 (:TYPE-PRESCRIPTION FUMON::NULOP))
   (132 25 (:REWRITE FLD::|a + b = b + a|))
   (71 71
       (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO))
   (28 28 (:REWRITE FUNPOL::|- nil =e nil|))
   (25 25
       (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|FUMON::coeficiente (- m) FLD::= FLD::- (FUMON::coeficiente m)|)
(FUNPOL::|coeficiente (- (primero p)) FLD::= FLD::- (coeficiente (primero p))|
     (19 2 (:DEFINITION FUPOL::POLINOMIOP))
     (15 15 (:REWRITE DEFAULT-CAR))
     (15 3
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (14 2 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (10 10 (:REWRITE DEFAULT-CDR))
     (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (6 6
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (6 6
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (6 6
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (6 2 (:TYPE-PRESCRIPTION FLD::FDP_-))
     (6 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (3 3
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|
     (146 30
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (130 14
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (82 14
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (71 71 (:REWRITE DEFAULT-CDR))
     (58 58
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (33 30
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (3 1 (:TYPE-PRESCRIPTION FLD::FDP_-))
     (2 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (2 2 (:REWRITE FLD::|- a = 0 <=> a = 0|))
     (1 1
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-1|
 (8464 57
       (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
 (7682 18 (:DEFINITION FUPOL::+-MONOMIO))
 (7149 67
       (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (3870 32 (:DEFINITION FUPOL::>-MONOMIO))
 (2911 221
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (2010 358
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1652 1652 (:REWRITE DEFAULT-CDR))
 (1392 1392 (:REWRITE DEFAULT-CAR))
 (1305 76
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (1198
   83
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (1092 18 (:DEFINITION FUMON::+))
 (897 4
      (:REWRITE FUPOL::|m >-monomio (n +-monomio p)|))
 (833 69
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (799 218
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (646 356
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (592 35 (:REWRITE FUNPOL::|nil + p = p|))
 (574 574
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (552 80 (:REWRITE FUMON::TERMINO-MONOMIO))
 (506 9 (:REWRITE FUNPOL::|p + q = q + p|))
 (466 358
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (419 43
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (412 60
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (256 7
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (242 54
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (242 18
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (184 184
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (108 69
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (92 18
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (90 26
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (65 8 (:REWRITE FLD::|a + b = b + a|))
 (32 32 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (23 1
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (18 6
     (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (12 12 (:REWRITE FUTER::|~(a < a)|))
 (6 6
    (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO))
 (5 1
    (:REWRITE FUPOL::|~(a + b) = 0 => a +Mo (b +Mo p) =P (a + b) +Mo p|))
 (4 4
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+-MONOMIO)))
(FUNPOL::LEMMA-A (19 2 (:DEFINITION FUPOL::POLINOMIOP))
                 (15 15 (:REWRITE DEFAULT-CAR))
                 (15 3
                     (:REWRITE FUTER::|a < b or b < a or a = b|))
                 (10 10 (:REWRITE DEFAULT-CDR))
                 (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
                 (7 1 (:REWRITE FUMON::TERMINO-MONOMIO))
                 (6 6
                    (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
                 (6 6
                    (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
                 (6 2
                    (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
                 (4 2
                    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
                 (3 3
                    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
                 (3 3
                    (:REWRITE FUTER::|a < b & b < c => a < c|))
                 (3 1 (:TYPE-PRESCRIPTION FLD::FDP_-))
                 (1 1
                    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::LEMMA-B (40 8
                     (:REWRITE FUTER::|a < b or b < a or a = b|))
                 (36 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
                 (32 32 (:REWRITE DEFAULT-CAR))
                 (30 4 (:DEFINITION FUPOL::POLINOMIOP))
                 (20 20 (:REWRITE DEFAULT-CDR))
                 (18 4
                     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
                 (16 16
                     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
                 (16 16
                     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
                 (14 2 (:REWRITE FUMON::TERMINO-MONOMIO))
                 (8 8
                    (:REWRITE FUTER::|a < b & b < c => a < c|))
                 (6 6
                    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
                 (6 2 (:TYPE-PRESCRIPTION FLD::FDP_-))
                 (4 1
                    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
                 (4 1
                    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
                 (2 2
                    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
                 (2 2 (:DEFINITION FUMON::NULOP)))
(FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-2|
 (128 4 (:DEFINITION FUPOL::POLINOMIOP))
 (86 86 (:REWRITE DEFAULT-CAR))
 (79 79 (:REWRITE DEFAULT-CDR))
 (74 14
     (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
 (66 22
     (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (44 8
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (38 38
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (36 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (31 5
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (31 5
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (30 30
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (28 10
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (28 10
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (28
   10
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (24 4 (:DEFINITION FUMON::NULOP))
 (20 4 (:REWRITE FUMON::TERMINO-MONOMIO))
 (20 4 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (18 18
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (18 18
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (16 4
     (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (8 8
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 4
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (4 1
    (:REWRITE FUNPOL::|p + r = q + r <=> p = q|)))
(FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|
 (454 2 (:DEFINITION FUPOL::+-MONOMIO))
 (322 7
      (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
 (165 10
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (110 5 (:DEFINITION FUPOL::>-MONOMIO))
 (75 75 (:REWRITE DEFAULT-CDR))
 (70 14
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (40 8
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (39 39 (:REWRITE DEFAULT-CAR))
 (32 1 (:DEFINITION FUPOL::POLINOMIOP))
 (30 30
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (29 8
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (29 8
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (29
   8
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (28 28
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (28 28
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (26 26 (:TYPE-PRESCRIPTION FUTER::<))
 (18 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (15 10
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (14 14
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (12 2
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (12 2
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (6 6
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (5 5 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (4 1
    (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (2 2 (:DEFINITION FUMON::+))
 (1 1
    (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO)))
(FUNPOL::|p + q = (resto p) + (resto q)|
     (83 1 (:DEFINITION FUPOL::+-MONOMIO))
     (34 2
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (32 1 (:DEFINITION FUPOL::POLINOMIOP))
     (26 26 (:REWRITE DEFAULT-CDR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (10 4
         (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
     (10 4
         (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
     (10 2
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (10 2
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (5 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (5 1
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (4 4
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (4 4
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (4 1
        (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
     (4 1
        (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
     (3 3 (:TYPE-PRESCRIPTION FUTER::<))
     (2 2
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (1 1
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
     (1 1 (:DEFINITION FUMON::+)))
(FUNPOL::|p + q = (resto p) + (resto q)-a| (4 4 (:REWRITE DEFAULT-CAR))
                                           (2 2 (:REWRITE DEFAULT-CDR)))
(FUNPOL::|deg(p + q) =_e deg(p)-lemma-1|
    (1068 81
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
    (847 19
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
    (679 147
         (:REWRITE FUTER::|a < b or b < a or a = b|))
    (481 443 (:REWRITE DEFAULT-CDR))
    (387 367 (:REWRITE DEFAULT-CAR))
    (331 31
         (:REWRITE FUTER::|a < b => ~(b < a)|))
    (272 260
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
    (239 147
         (:REWRITE FUTER::|a < b & b < c => a < c|))
    (166 68
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
    (159 159
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
    (159 159 (:TYPE-PRESCRIPTION BINARY-APPEND))
    (64 32
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-APPEND))
    (46 2 (:REWRITE FUPOL::POLINOMIOP-APPEND))
    (43 2
        (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
    (1 1 (:TYPE-PRESCRIPTION ATOM))
    (1 1 (:DEFINITION ATOM)))
(FUNPOL::|deg(p + q) =_e deg(p)-lemma-2|
     (4309 185
           (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (2097 203
           (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (1352 260
           (:REWRITE FUTER::|a < b or b < a or a = b|))
     (1188 11
           (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (1151 1148 (:REWRITE DEFAULT-CDR))
     (584 289
          (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (546 546
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (339 11
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (329 33
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (308 308 (:TYPE-PRESCRIPTION FUPOL::+))
     (284 260
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (261 1
          (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
     (36 36
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
     (11 11 (:DEFINITION FUMON::+)))
(FUNPOL::|deg(p + q) =_e deg(p)-lemma-3|
     (344 18
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (120 24
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (104 84 (:REWRITE DEFAULT-CAR))
     (91 91 (:REWRITE DEFAULT-CDR))
     (58 6 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (48 48
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (48 48
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (43 1
         (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
     (38 15
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (27 24
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (21 21 (:TYPE-PRESCRIPTION FUPOL::+))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO)))
(FUNPOL::|deg(p + q) =_e deg(p)-lema-4|
 (757 1 (:DEFINITION FUPOL::FN))
 (627 1 (:DEFINITION FUPOL::+-MONOMIO))
 (623 22 (:DEFINITION FUPOL::POLINOMIOP))
 (467
  7
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (455 23
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (319 17
      (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
 (171 4 (:REWRITE FUPOL::FN-ORDENADO))
 (146 30
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (132 132 (:REWRITE DEFAULT-CDR))
 (105 105 (:REWRITE DEFAULT-CAR))
 (102 45
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (91 24
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (58 58
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (58 58
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (48 1
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (40 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (33 30
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (19 19 (:TYPE-PRESCRIPTION FUPOL::+))
 (12 12
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
 (7 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (2 2 (:REWRITE FUPOL::POLINOMIOP-+))
 (1 1 (:REWRITE FUPOL::POLINOMIOP-FN))
 (1 1 (:DEFINITION FUMON::+)))
(FUNPOL::|deg(p + q) =_e deg(p)|
     (38 16
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (38 4 (:DEFINITION FUPOL::POLINOMIOP))
     (35 7
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (26 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (22 22 (:REWRITE DEFAULT-CAR))
     (20 20 (:REWRITE DEFAULT-CDR))
     (14 14
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (14 14
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (14 14
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 7 (:REWRITE DEFAULT-<-2))
     (14 7 (:REWRITE DEFAULT-<-1))
     (12 4
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (12 4
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (7 7
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (3 3
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+)))
(FUNPOL::|=-refines-FUPOL::=P|)
(FUNPOL::|FUPOL::=P-refines-=|)
(FUNPOL::|deg(p + q) =_e deg(q)|
 (14336 10 (:DEFINITION FUPOL::+-MONOMIO))
 (7884 24
       (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
 (6477 263 (:DEFINITION FUPOL::POLINOMIOP))
 (5640 30
       (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (3916 169
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (3534 288
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (2529 1265
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (2239 342
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (2193 2193 (:REWRITE DEFAULT-CDR))
 (1812 103
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (1812 103
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (1810 362
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1710 15 (:DEFINITION FUPOL::>-MONOMIO))
 (1357 1357 (:REWRITE DEFAULT-CAR))
 (1277 10 (:DEFINITION FUMON::+))
 (1216
      6
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (724 724
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (724 724
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (485 32
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (362 362
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (165 3
      (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (90 90
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (90 10
     (:REWRITE FUTER::|a < b => ~(b < a)|))
 (69 12
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (69 12
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (64 26
     (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (51 6 (:REWRITE FLD::|a + b = b + a|))
 (48 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (45 30
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (15 15 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (12 12
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (6 6
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (3 3
    (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO))
 (2 2 (:DEFINITION FUMON::-)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-1|
    (804 23
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
    (345 81
         (:REWRITE FUTER::|a < b or b < a or a = b|))
    (265 44
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
    (253 243 (:REWRITE DEFAULT-CDR))
    (217 211 (:REWRITE DEFAULT-CAR))
    (132 132
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
    (132 132
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
    (131 81
         (:REWRITE FUTER::|a < b & b < c => a < c|))
    (124 12
         (:REWRITE FUTER::|a < b => ~(b < a)|))
    (82 31
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
    (46 46
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
    (46 46 (:TYPE-PRESCRIPTION BINARY-APPEND))
    (24 12
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-APPEND))
    (20 8
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
    (20 8
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
    (16 16 (:REWRITE FUTER::|~(a < a)|))
    (15 1 (:REWRITE FUPOL::POLINOMIOP-APPEND))
    (12 4 (:DEFINITION BINARY-APPEND)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-2|
   (2617 59
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
   (2463 6 (:DEFINITION FUPOL::+-MONOMIO))
   (2380 400
         (:REWRITE FUTER::|a < b or b < a or a = b|))
   (1856 1822 (:REWRITE DEFAULT-CDR))
   (1220 1220 (:REWRITE DEFAULT-CAR))
   (1181 400
         (:REWRITE FUTER::|a < b & b < c => a < c|))
   (1034 16
         (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
   (673 58
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
   (612 49
        (:REWRITE FUTER::|a < b => ~(b < a)|))
   (397 163
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
   (274 78
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
   (274 78
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
   (82 18
       (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
   (69 69 (:REWRITE FUTER::|~(a < a)|))
   (42 14
       (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
   (35 1
       (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
   (32 6 (:DEFINITION FUMON::+))
   (26 4 (:REWRITE FLD::|a + b = b + a|))
   (18 18
       (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
   (14 14 (:TYPE-PRESCRIPTION FUPOL::+M))
   (10 10 (:TYPE-PRESCRIPTION FUMON::NULOP))
   (4 4
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
   (4 4
      (:REWRITE FUPOL::POLINOMIOP-+-MONOMIO))
   (3 1 (:DEFINITION BINARY-APPEND)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-3|
 (426 1 (:DEFINITION FUPOL::FN))
 (383 1 (:DEFINITION FUPOL::+-MONOMIO))
 (285 13 (:DEFINITION FUPOL::POLINOMIOP))
 (282
  7
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (260 20
      (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
 (141 68
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (133 133
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (113 14
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (100 100 (:REWRITE DEFAULT-CDR))
 (46 4 (:REWRITE FUPOL::FN-ORDENADO))
 (31 1
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (30 30 (:REWRITE DEFAULT-CAR))
 (25 2
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (16 2
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (12 2
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (9 3
    (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lemma-3|))
 (9 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (8 8 (:TYPE-PRESCRIPTION FUPOL::+))
 (5 5
    (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (5 5
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
 (5 5
    (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (4 1
    (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (4 1
    (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (4
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (4 1
    (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (3 3 (:TYPE-PRESCRIPTION FUTER::<))
 (2 2
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (2 2 (:REWRITE FUPOL::POLINOMIOP-FN))
 (1 1
    (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (1 1 (:REWRITE FUPOL::POLINOMIOP-+))
 (1 1 (:DEFINITION FUMON::NULOP))
 (1 1 (:DEFINITION FUMON::+)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-4|
 (1342 3 (:DEFINITION FUPOL::FN))
 (1213 3 (:DEFINITION FUPOL::+-MONOMIO))
 (875 40 (:DEFINITION FUPOL::POLINOMIOP))
 (848
  23
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (762 67
      (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
 (435 210
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (410 410
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (343 43
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (310 310 (:REWRITE DEFAULT-CDR))
 (151 18 (:REWRITE FUPOL::FN-ORDENADO))
 (93 3
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (79 79 (:REWRITE DEFAULT-CAR))
 (69 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (67 3 (:DEFINITION FUMON::+))
 (52 2
     (:REWRITE FUPOL::|q + p = mp(p) +M (q + resto(p))|))
 (42 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (42 2
     (:REWRITE
          FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (36 6
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (27 9
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lemma-3|))
 (27 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (24 24 (:TYPE-PRESCRIPTION FUPOL::+))
 (22 2 (:REWRITE FLD::|a + b = b + a|))
 (15 15
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (15 15
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
 (15 15
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (9 9 (:TYPE-PRESCRIPTION FUTER::<))
 (6 6
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (6 6 (:REWRITE FUPOL::POLINOMIOP-FN))
 (4 4
    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (4 1
    (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (4 1
    (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (4
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (3 3 (:REWRITE FUPOL::POLINOMIOP-+))
 (3 3 (:DEFINITION FUMON::NULOP))
 (2 2
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (2 2 (:REWRITE FUPOL::ORDENADOP-FN)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|
     (38 1
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (35 7
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (27 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (14 14
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (14 14
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (10 10 (:REWRITE DEFAULT-CDR))
     (7 7
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (6 6
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (6 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (6 2
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (3 2 (:DEFINITION FUMON::NULOP))
     (1 1
        (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (1 1 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-6|
 (17 17 (:REWRITE DEFAULT-CDR))
 (10 4
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (10 4
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (10
   4
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (8 8 (:REWRITE DEFAULT-CAR))
 (4 1
    (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (3 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (3 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-7|)
(FUNPOL::|deg(p + q) ACL2::< deg(p)|
    (2788 13 (:DEFINITION FUPOL::+-MONOMIO))
    (1313 37
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
    (1205 37
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
    (1146 62
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
    (705 13
         (:REWRITE FUTER::|a < b => ~(b < a)|))
    (556 109
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
    (543 17 (:DEFINITION FUPOL::>-MONOMIO))
    (493 493 (:REWRITE DEFAULT-CDR))
    (307 307 (:REWRITE DEFAULT-CAR))
    (266 62
         (:REWRITE FUTER::|a < b or b < a or a = b|))
    (254 13 (:DEFINITION FUPOL::POLINOMIOP))
    (159 60
         (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
    (159 60
         (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
    (150 24
         (:REWRITE FUMON::COEFICIENTE-MONOMIO))
    (126 42 (:TYPE-PRESCRIPTION FLD::FDP_-))
    (117 117
         (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
    (117 117 (:TYPE-PRESCRIPTION FUTER::<))
    (105 19
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
    (102 102
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
    (102 102
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
    (101 45
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
    (84 21
        (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
    (84 12 (:REWRITE FUMON::TERMINO-MONOMIO))
    (71 71
        (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
    (62 62
        (:REWRITE FUTER::|a < b & b < c => a < c|))
    (45 9
        (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
    (42 42
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
    (39 13
        (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
    (20 4
        (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
    (13 13 (:DEFINITION FUMON::+))
    (12 4
        (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
    (8 2
       (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
    (6 6 (:TYPE-PRESCRIPTION FUNPOL::NULO))
    (6 6 (:REWRITE FUTER::|~(a < a)|))
    (2 2
       (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO))
    (2 2
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
    (2 1 (:REWRITE DEFAULT-<-2))
    (2 1 (:REWRITE DEFAULT-<-1)))
(FUNPOL::|deg(p + q) ACL2::< deg(p)-a|
     (3771 27
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
     (3011 189
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (1490 102 (:DEFINITION FUPOL::POLINOMIOP))
     (1441 30 (:DEFINITION FUPOL::>-MONOMIO))
     (1104 48
           (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (889 189
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (571 571 (:REWRITE DEFAULT-CDR))
     (565 20
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (544 544 (:REWRITE DEFAULT-CAR))
     (384 192
          (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (350 350
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (350 350
          (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (284 102
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (189 189
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (167 167
          (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (96 58
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (80 26
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (35 5 (:REWRITE FUMON::TERMINO-MONOMIO))
     (23 23 (:REWRITE FUTER::|~(a < a)|))
     (15 15
         (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (15 5 (:TYPE-PRESCRIPTION FLD::FDP_-))
     (15 5
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (5 5
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 2 (:REWRITE DEFAULT-<-2))
     (4 2 (:REWRITE DEFAULT-<-1)))
(FUNPOL::|not FUMON::nulop m|
     (884 442
          (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (362 64
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (352 26
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (272 26
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (165 40
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (162 162 (:REWRITE DEFAULT-CAR))
     (150 150 (:REWRITE DEFAULT-CDR))
     (86 78 (:REWRITE DEFAULT-<-1))
     (82 64
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (80 78 (:REWRITE DEFAULT-<-2))
     (80 23
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (58 58
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (36 12 (:REWRITE FLD::|a * b = b * a|))
     (24 18 (:REWRITE DEFAULT-+-2))
     (22 22
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (22 18 (:REWRITE DEFAULT-+-1))
     (20 10
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (14 14
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (14 12 (:REWRITE DEFAULT-UNARY-MINUS)))
(FUNPOL::|m FUPOL::*-monomio p2 != 0|
     (4061 4061 (:REWRITE DEFAULT-CDR))
     (3949 3949 (:REWRITE DEFAULT-CAR))
     (3240 16 (:REWRITE FUMON::|a * b = b * a|))
     (2814 494
           (:REWRITE FUTER::|a < b or b < a or a = b|))
     (2134 2130 (:REWRITE DEFAULT-<-2))
     (2134 2130 (:REWRITE DEFAULT-<-1))
     (1675 171
           (:REWRITE FUTER::|a < b => ~(b < a)|))
     (812 303
          (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (566 494
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (392 308 (:REWRITE DEFAULT-+-1))
     (348 28 (:REWRITE COMMUTATIVITY-2-OF-+))
     (332 308 (:REWRITE DEFAULT-+-2))
     (300 60 (:REWRITE FLD::|a * b = b * a|))
     (252 252 (:TYPE-PRESCRIPTION FLD::FDP-0_F))
     (212 152 (:REWRITE DEFAULT-UNARY-MINUS))
     (188 188
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (172 108
          (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (80 16
         (:REWRITE FLD::|a * (b * c) = b * (a * c)|))
     (80 16
         (:REWRITE FLD::|a * (b * (/ a)) = b|))
     (72 72 (:REWRITE FOLD-CONSTS-IN-+))
     (60 24 (:REWRITE UNICITY-OF-0))
     (48 48
         (:TYPE-PRESCRIPTION FUTER::TERMINOP-UNO))
     (36 24 (:DEFINITION FIX)))
(FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|)
(FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|
     (6705 6140 (:REWRITE DEFAULT-CAR))
     (6361 6199 (:REWRITE DEFAULT-CDR))
     (5359 957
           (:REWRITE FUTER::|a < b or b < a or a = b|))
     (3586 3470 (:REWRITE DEFAULT-<-1))
     (3571 361
           (:REWRITE FUTER::|a < b => ~(b < a)|))
     (3471 3470 (:REWRITE DEFAULT-<-2))
     (1304 8 (:REWRITE FUMON::|a * b = b * a|))
     (1224 957
           (:REWRITE FUTER::|a < b & b < c => a < c|))
     (579 552 (:REWRITE DEFAULT-+-1))
     (564 552 (:REWRITE DEFAULT-+-2))
     (404 36 (:REWRITE COMMUTATIVITY-2-OF-+))
     (283 268 (:REWRITE DEFAULT-UNARY-MINUS))
     (141 8
          (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
     (136 136
          (:TYPE-PRESCRIPTION FUTER::TERMINOP-UNO))
     (124 124 (:REWRITE FOLD-CONSTS-IN-+))
     (123 69
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (105 73
          (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (62 28 (:REWRITE UNICITY-OF-0))
     (60 12
         (:REWRITE FLD::|(a * b) * c = a * (b * c)|))
     (34 28 (:DEFINITION FIX))
     (25 5
         (:REWRITE FLD::|a * (b * c) = b * (a * c)|))
     (20 10
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (9 9
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (7 7 (:TYPE-PRESCRIPTION FUMON::NULOP)))
(FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|
     (592 56
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (558 12
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (264 8 (:DEFINITION FUPOL::>-MONOMIO))
     (260 56
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (232 226 (:REWRITE DEFAULT-CAR))
     (180 180 (:REWRITE DEFAULT-CDR))
     (102 102
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (102 102
          (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (72 6
         (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
     (66 22 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (56 56
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (56 24
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (48 6 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (32 32
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (32 32
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (32 8
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (26 15 (:REWRITE DEFAULT-UNARY-MINUS))
     (26 15 (:REWRITE DEFAULT-+-1))
     (24 8
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (22 22
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (15 15 (:REWRITE DEFAULT-+-2))
     (12 12
         (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
     (10 5 (:REWRITE DEFAULT-<-2))
     (10 5 (:REWRITE DEFAULT-<-1))
     (6 6 (:TYPE-PRESCRIPTION FUMON::NULOP))
     (2 2
        (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::|FUMON::- (FUMON::- m) FUMON::= m|)
(FUNPOL::|FUMON::- (primero (- (m *-monomio p2))) = (primero (m *-monomio p2))|
     (2292 95
           (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (952 5
          (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
     (559 111
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (507 507 (:REWRITE DEFAULT-CDR))
     (428 101
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (414 138 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (319 19
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (224 224
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (151 151
          (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (142 120 (:REWRITE DEFAULT-+-2))
     (142 120 (:REWRITE DEFAULT-+-1))
     (131 98 (:REWRITE DEFAULT-UNARY-MINUS))
     (117 111
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (97 9
         (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
     (96 96
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (95 95
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (75 75
         (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
     (71 19 (:REWRITE FLD::|a * b = b * a|))
     (66 2 (:DEFINITION FUPOL::>-MONOMIO))
     (48 12
         (:TYPE-PRESCRIPTION FUPOL::|m +M p != 0|))
     (32 16
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (18 9 (:REWRITE DEFAULT-<-2))
     (18 9 (:REWRITE DEFAULT-<-1))
     (14 12
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (14 6
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (9 9
        (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
     (8 8 (:TYPE-PRESCRIPTION FUMON::NULOP))
     (8 8 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (8 2
        (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (6 2
        (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|)))
(FUNPOL::|FUMON::- (primero (- (m *-monomio p2))) FUMON::= primero p1|
 (492 8 (:DEFINITION FUPOL::*-MONOMIO))
 (428 22
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (346 18 (:DEFINITION FUPOL::POLINOMIOP))
 (270 2
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (248
  2
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (246 36
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (238 6 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (172 36
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (156 4 (:REWRITE FUMON::|a * b = b * a|))
 (146 140 (:REWRITE DEFAULT-CAR))
 (132 4 (:DEFINITION FUPOL::>-MONOMIO))
 (124 124 (:REWRITE DEFAULT-CDR))
 (68 68
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (68 68
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (54 20 (:DEFINITION FUMON::NULOP))
 (44 22
     (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (40 8
     (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (36 36
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (30 10 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (28 12
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (26 4
     (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (22 22
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (22 22
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (18 18 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (16 4
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (16 2 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (12 12
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 4
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (10 10
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (10 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 7 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE DEFAULT-+-2))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (2 2 (:TYPE-PRESCRIPTION FUMON::NULOP)))
(FUNPOL::|FUPOL::- p != 0|
     (728 44
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (305 56
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (282 56
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (243 49
          (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (189 189 (:REWRITE DEFAULT-CDR))
     (179 10
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (177 177 (:REWRITE DEFAULT-CAR))
     (160 56
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (37 21
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (7 7 (:REWRITE FUTER::|~(a < a)|))
     (1 1 (:TYPE-PRESCRIPTION ATOM)))
(FUNPOL::|- p != 0|
     (60 3 (:DEFINITION FUPOL::POLINOMIOP))
     (44 1
         (:REWRITE FUPOL::|- p =e (- mp(p)) +M (- (resto(p)))|))
     (37 3
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (20 4
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (16 16 (:REWRITE DEFAULT-CDR))
     (13 4
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (13 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (12 12 (:REWRITE DEFAULT-CAR))
     (8 8
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (8 8
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (8 3
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (4 4
        (:REWRITE FUTER::|a < b & b < c => a < c|)))
(FUNPOL::|- (m FUPOL::*-monomio p2) != 0|
     (303 6 (:DEFINITION FUPOL::*-MONOMIO))
     (301 28
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (292 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (260 20
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (193 15 (:DEFINITION FUPOL::POLINOMIOP))
     (132 4 (:DEFINITION FUPOL::>-MONOMIO))
     (130 28
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (129 5 (:REWRITE FUMON::|a * b = b * a|))
     (100 100 (:REWRITE DEFAULT-CAR))
     (84 84 (:REWRITE DEFAULT-CDR))
     (51 51
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (51 51
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (45 12 (:DEFINITION FUMON::NULOP))
     (36 3
         (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
     (30 6
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (28 28
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (28 12
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (27 9 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (24 3 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (21 21
         (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (16 16
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (16 16
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 4
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (12 4
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (11 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (11 6 (:REWRITE DEFAULT-+-1))
     (9 9
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (9 9
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (9 9 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 3 (:REWRITE DEFAULT-<-2))
     (6 3 (:REWRITE DEFAULT-<-1))
     (3 3
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (3 3 (:TYPE-PRESCRIPTION FUMON::NULOP))
     (3 3 (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
     (1 1
        (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::|deg (p1 + (- (m FUPOL::*-monomio p2))) ACL2::< deg p1|
 (4057 3 (:DEFINITION FUPOL::+-MONOMIO))
 (3281 157 (:DEFINITION FUPOL::*-MONOMIO))
 (1645 142 (:DEFINITION FUPOL::POLINOMIOP))
 (1520 12
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (942 157
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (891 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (882
  6
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (756 126 (:REWRITE FUMON::|a * b = b * a|))
 (534 3 (:DEFINITION FUPOL::>-MONOMIO))
 (437 410 (:REWRITE DEFAULT-CDR))
 (432
  6
  (:REWRITE
   FUNPOL::|FUMON::termino (FUMON::- (primero p) =e FUMON::termino (primero p)|))
 (408 6
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (374 356 (:REWRITE DEFAULT-CAR))
 (362 2
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (344 2
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (314 314
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (314 157 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (314 157 (:REWRITE DEFAULT-UNARY-MINUS))
 (314 157 (:REWRITE DEFAULT-+-2))
 (314 157 (:REWRITE DEFAULT-+-1))
 (284 4
      (:REWRITE FUNPOL::|deg (- p) =e deg p|))
 (183 3
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (183 3
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (111 3
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (90 90
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (82 8 (:REWRITE DEFAULT-<-1))
 (78 24
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (54 12
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (52 8 (:REWRITE DEFAULT-<-2))
 (51 9
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (48 6
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (42 15
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (42 15
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (39 3
     (:REWRITE FUPOL::|primero (m *M p) >-monomio resto (m *M p)|))
 (27 3
     (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (24 24 (:TYPE-PRESCRIPTION FUTER::<))
 (24 18
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (24 6
     (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (18 18
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (12 12
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (12 12
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (3 3 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (3 3 (:DEFINITION FUMON::+))
 (2 2
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO)))
(FUNPOL::QUOT
 (8156 324 (:DEFINITION FUPOL::*-MONOMIO))
 (7828 339 (:DEFINITION FUPOL::POLINOMIOP))
 (7688
   33
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (4222 202
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (2921 50
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2921 17
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2624
  28
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (2544 241 (:REWRITE FUMON::|a * b = b * a|))
 (2080 360
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (1853 84
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1821 27
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (1744 1681 (:REWRITE DEFAULT-CAR))
 (1638 1560 (:REWRITE DEFAULT-CDR))
 (1209 209
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1123 6
       (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (898 898
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (862 2
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (830 10
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (827 361 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (779 21 (:REWRITE FUMON::TERMINO-MONOMIO))
 (628 327 (:REWRITE DEFAULT-+-1))
 (625 324 (:REWRITE DEFAULT-UNARY-MINUS))
 (588 327 (:REWRITE DEFAULT-+-2))
 (574 8
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (572 428
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (570 8
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (530 282
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (452
  12
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (450
    45
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (444 37
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (428 428
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (387 5 (:DEFINITION FUPOL::>-MONOMIO))
 (296 37
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (273 7
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (250 50
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (250 50
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (209 209
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (195 57 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (188 164
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (165 33
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (112 2 (:REWRITE FLD::|a + b = b + a|))
 (109 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (97 5 (:REWRITE FUNPOL::|- p != 0|))
 (96 96
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (94 5
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (89 5
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (39 39 (:DEFINITION FUMON::-))
 (37 37 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (12 5 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-<-2))
 (2 2
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|
     (25 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (20 4
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (17 4
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (13 2 (:DEFINITION FUPOL::POLINOMIOP))
     (12 12 (:REWRITE DEFAULT-CDR))
     (8 8
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (8 8
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (8 8 (:REWRITE DEFAULT-CAR))
     (7 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (7 2
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (4 4
        (:REWRITE FUTER::|a < b & b < c => a < c|)))
(FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|
     (54 1
         (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (51 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (40 8
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (34 4 (:DEFINITION FUPOL::POLINOMIOP))
     (32 8
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (23 23 (:REWRITE DEFAULT-CDR))
     (16 16
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (16 16
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (16 16 (:REWRITE DEFAULT-CAR))
     (15 4
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (11 3
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (8 8
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (6 6
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (4 4 (:TYPE-PRESCRIPTION FUNPOL::=))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (1 1 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|
     (192 4 (:DEFINITION FUPOL::ORDENADOP))
     (54 1
         (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (54 1
         (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (52 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (42 4 (:DEFINITION FUPOL::POLINOMIOP))
     (40 8
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (30 8
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (22 22 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE DEFAULT-CAR))
     (20 10
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (16 16
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (16 16
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (16 4
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (14 14 (:TYPE-PRESCRIPTION FUTER::<))
     (12 12
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (8 8 (:TYPE-PRESCRIPTION FUNPOL::=))
     (8 8
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (8 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (6 4 (:DEFINITION FUMON::NULOP))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 2 (:REWRITE DEFAULT-<-2))
     (4 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|(p = 0) =e (p =e nil)|)
(FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|
     (89 1
         (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (86 1 (:DEFINITION FUPOL::ORDENADOP))
     (48 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (41 4
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (30 1 (:DEFINITION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (14 14
         (:TYPE-PRESCRIPTION FUNPOL::BOOLEANP-POLINOMIOP))
     (14 1 (:DEFINITION FUPOL::POLINOMIOP))
     (10 1
         (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
     (9 9 (:TYPE-PRESCRIPTION FUTER::<))
     (6 6
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (6 6
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (6 6
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-CAR))
     (6 3
        (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (4 4 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (4 4
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 2 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (4 1
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (3 1
        (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (2 1
        (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (2 1
        (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (2 1 (:REWRITE DEFAULT-<-2))
     (2 1 (:DEFINITION FUMON::NULOP))
     (2 1 (:DEFINITION FUNPOL::DEG))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|
     (89 1
         (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (86 1 (:DEFINITION FUPOL::ORDENADOP))
     (48 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (41 4
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (30 1 (:DEFINITION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (14 14
         (:TYPE-PRESCRIPTION FUNPOL::BOOLEANP-POLINOMIOP))
     (14 1 (:DEFINITION FUPOL::POLINOMIOP))
     (10 1
         (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
     (9 9 (:TYPE-PRESCRIPTION FUTER::<))
     (6 6
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (6 6
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (6 6
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-CAR))
     (6 3
        (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (4 4 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (4 4
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 2 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (4 1
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (3 1
        (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (3 1
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
     (2 1
        (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (2 1
        (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (2 1 (:REWRITE DEFAULT-<-1))
     (2 1 (:DEFINITION FUMON::NULOP))
     (2 1 (:DEFINITION FUNPOL::DEG))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::POLINOMIOP-QUOT
 (22574 15 (:DEFINITION FUPOL::+-MONOMIO))
 (12027 754
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (10742 72
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (10478 350
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (8036 362 (:DEFINITION FUPOL::*-MONOMIO))
 (6324 38
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (6296 15
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (5741 15 (:DEFINITION FUMON::+))
 (5666 12 (:REWRITE FLD::|a + b = b + a|))
 (4828 56
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (3258 44
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (3222 314 (:REWRITE FUMON::|a * b = b * a|))
 (2762 392
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2518 130
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (2246 38 (:REWRITE FUNPOL::|- p != 0|))
 (2154 397 (:REWRITE DEFAULT-UNARY-MINUS))
 (2154 397 (:REWRITE DEFAULT-+-1))
 (2065 2065 (:REWRITE DEFAULT-CDR))
 (1903 363
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1813 1813 (:REWRITE DEFAULT-CAR))
 (1768
  20
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1484 160
       (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (1372 65 (:REWRITE DEFAULT-<-1))
 (1292 16
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (1176 397 (:REWRITE DEFAULT-+-2))
 (998 130
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (878 111
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (798 798
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (778 162
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (770 770
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (770 770
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (680 72
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (680
   72
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (640 65 (:REWRITE DEFAULT-<-2))
 (622 80
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (610 42
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (610 42
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (610 42
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (610 42
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (590 295 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (585 311
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (538 38
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (430 430
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (363 363
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (356 15
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (328 12 (:REWRITE FUNPOL::|p + q = q + p|))
 (150 30 (:REWRITE FUMON::TERMINO-MONOMIO))
 (140 12 (:REWRITE FUNPOL::|nil + p = p|))
 (130 130 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (126 4 (:DEFINITION FUPOL::>-MONOMIO))
 (80
  16
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (76 76
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (30 6
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (26 12
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (14 4
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (12 12
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (10 4
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (4 4 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::QUOT-INDUCT-HINT
 (8156 324 (:DEFINITION FUPOL::*-MONOMIO))
 (7828 339 (:DEFINITION FUPOL::POLINOMIOP))
 (7688
   33
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (4222 202
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (2921 50
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2921 17
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2624
  28
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (2544 241 (:REWRITE FUMON::|a * b = b * a|))
 (2080 360
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (1853 84
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1821 27
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (1744 1681 (:REWRITE DEFAULT-CAR))
 (1638 1560 (:REWRITE DEFAULT-CDR))
 (1209 209
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1123 6
       (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (898 898
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (862 2
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (830 10
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (827 361 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (779 21 (:REWRITE FUMON::TERMINO-MONOMIO))
 (628 327 (:REWRITE DEFAULT-+-1))
 (625 324 (:REWRITE DEFAULT-UNARY-MINUS))
 (588 327 (:REWRITE DEFAULT-+-2))
 (574 8
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (572 428
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (570 8
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (530 282
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (452
  12
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (450
    45
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (444 37
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (428 428
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (387 5 (:DEFINITION FUPOL::>-MONOMIO))
 (296 37
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (273 7
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (250 50
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (250 50
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (209 209
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (195 57 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (188 164
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (165 33
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (112 2 (:REWRITE FLD::|a + b = b + a|))
 (109 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (97 5 (:REWRITE FUNPOL::|- p != 0|))
 (96 96
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (94 5
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (89 5
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (39 39 (:DEFINITION FUMON::-))
 (37 37 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (12 5 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-<-2))
 (2 2
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1
     (345 180
          (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (54 1
         (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (42 3 (:REWRITE DEFAULT-<-2))
     (39 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (38 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (36 3 (:REWRITE DEFAULT-<-1))
     (34 3 (:DEFINITION FUPOL::POLINOMIOP))
     (30 6
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (23 6
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (17 17 (:REWRITE DEFAULT-CDR))
     (12 12
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (12 12
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (12 12 (:REWRITE DEFAULT-CAR))
     (11 3
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (6 6
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (6 2
        (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
     (6 2
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
     (4 1
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-2
     (57796 3624
            (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (20944 612
            (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (18908 3796
            (:REWRITE FUTER::|a < b or b < a or a = b|))
     (14432 14432 (:REWRITE DEFAULT-CDR))
     (11560 952
            (:REWRITE FUTER::|a < b => ~(b < a)|))
     (9624 2986
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (5896 3008
           (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4608 1272 (:REWRITE FLD::|a * b = b * a|))
     (4276 3796
           (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4044 4044
           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3024 2054 (:REWRITE DEFAULT-+-1))
     (2872 1694 (:REWRITE DEFAULT-UNARY-MINUS))
     (2574 2054 (:REWRITE DEFAULT-+-2))
     (1376 688 (:REWRITE DEFAULT-<-2))
     (1376 688 (:REWRITE DEFAULT-<-1))
     (148 4 (:DEFINITION FUPOL::>-MONOMIO))
     (28 12
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (16 16
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (12 4
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-3
     (238 6 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (214 20
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (132 4 (:DEFINITION FUPOL::>-MONOMIO))
     (84 20
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (46 6 (:DEFINITION FUPOL::POLINOMIOP))
     (40 40 (:REWRITE DEFAULT-CDR))
     (32 32
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (32 32
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (28 28 (:REWRITE DEFAULT-CAR))
     (28 12
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (28 6
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (20 20
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (18 3 (:REWRITE DEFAULT-<-1))
     (16 16
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (14 4 (:REWRITE DEFAULT-+-1))
     (12 4
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4 (:REWRITE DEFAULT-+-2))
     (8 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 3 (:REWRITE DEFAULT-<-2))
     (2 2 (:DEFINITION FUMON::NULOP)))
(FUNPOL::|FUMON::=-implies-=-FUPOL::*-monomio-1|
     (504 13
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (473 16 (:DEFINITION FUPOL::ORDENADOP))
     (100 18
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (93 93
         (:TYPE-PRESCRIPTION FUNPOL::BOOLEANP-POLINOMIOP))
     (86 86 (:REWRITE DEFAULT-CDR))
     (73 73 (:REWRITE DEFAULT-CAR))
     (41 41
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (41 41
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (36 36 (:TYPE-PRESCRIPTION FUTER::<))
     (36 18
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (28 14
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (28 14 (:DEFINITION FUMON::NULOP))
     (18 18
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (18 18 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
     (8 5
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-4
 (992 35 (:DEFINITION FUPOL::*-MONOMIO))
 (787 43 (:DEFINITION FUPOL::POLINOMIOP))
 (627 9
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (598 69
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (548 2
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (548
   2
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (546 2
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (345
  3
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (339 29 (:REWRITE FUMON::|a * b = b * a|))
 (276 47
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (199 172 (:REWRITE DEFAULT-CDR))
 (191 33
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (161 152 (:REWRITE DEFAULT-CAR))
 (158 33
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (132 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (117 3 (:REWRITE FUMON::TERMINO-MONOMIO))
 (105
  3
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (103 103
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (98 37 (:REWRITE DEFAULT-+-1))
 (97 61
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (74 37 (:REWRITE DEFAULT-UNARY-MINUS))
 (74 37 (:REWRITE DEFAULT-+-2))
 (70 35 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (66 2 (:DEFINITION FUPOL::>-MONOMIO))
 (61 61
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (60 12
     (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (60 12
     (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (60
    6
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (51 15 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (42 42
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (33 33
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (25 15
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (21 15
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (14 6
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (14 2
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (8 2
    (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (6 6
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (6 6 (:DEFINITION FUMON::-))
 (6 2
    (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-5
     (294 2 (:DEFINITION FUPOL::+-MONOMIO))
     (175 8 (:DEFINITION FUPOL::POLINOMIOP))
     (140 8
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (102 11
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (71 13
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (48 48 (:REWRITE DEFAULT-CDR))
     (48 48 (:REWRITE DEFAULT-CAR))
     (31 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (29 29
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (29 29
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (24 8
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (13 13
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (12 2 (:DEFINITION FUMON::+))
     (10 2 (:REWRITE FLD::|a + b = b + a|))
     (6 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 4
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-6)
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-7
 (15524 3 (:DEFINITION FUPOL::+-MONOMIO))
 (11173 325 (:DEFINITION FUPOL::POLINOMIOP))
 (10231 10
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (9039 10
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (8994 584
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (8787 316 (:DEFINITION FUPOL::*-MONOMIO))
 (6776 80
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (6150 253
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (5442 10
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (4909 3
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (3876 279 (:REWRITE FUMON::|a * b = b * a|))
 (2572
   10
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (2557 10
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (2554
  29
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (2539 5
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (2539 5
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (2435 5
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (2435 5
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (2262 318 (:REWRITE DEFAULT-UNARY-MINUS))
 (2262 318 (:REWRITE DEFAULT-+-1))
 (2171 311
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1789 10
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (1642 1642 (:REWRITE DEFAULT-CDR))
 (1375 1375 (:REWRITE DEFAULT-CAR))
 (1342 254
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1340
  22
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (1012 143
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (981 109
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (954 318 (:REWRITE DEFAULT-+-2))
 (784 784
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (705 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (608 26
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (544 544
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (544 544
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (524 286
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (462 3 (:DEFINITION FUMON::+))
 (460 230 (:DEFINITION FUMON::NULOP))
 (426 6 (:DEFINITION FUPOL::>-MONOMIO))
 (317 2
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (296 296
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (264
    22
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (254 254
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (230 230 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (202 101 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (170 2
      (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (167 3
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (144 6 (:REWRITE DEFAULT-<-1))
 (142 2 (:REWRITE FLD::|a + b = b + a|))
 (132 44 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (114 18
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (101 10
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (96 6
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (90 6
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (55 55
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (47 6 (:REWRITE DEFAULT-<-2))
 (46 46
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (29 29
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (24 24
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (22 22 (:DEFINITION FUMON::-))
 (13 10
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (10 2 (:REWRITE FUMON::TERMINO-MONOMIO))
 (6 6
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (6 2
    (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (3 3 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (2 2 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-8
 (97161 2665 (:DEFINITION FUPOL::POLINOMIOP))
 (85304 66
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (79575 4854
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (79231 2637 (:DEFINITION FUPOL::*-MONOMIO))
 (75768 66
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (58178 661
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (50758 110
        (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (44090 2066
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (33502 2350 (:REWRITE FUMON::|a * b = b * a|))
 (29890 22
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (22206
  242
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (21964
   110
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (21856 110
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (21245 36
        (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (21245 36
        (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (20387 36
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (20387 36
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (20076 20 (:REWRITE FLD::|a + b = b + a|))
 (19637 66
        (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (18731 2655 (:REWRITE DEFAULT-+-1))
 (18692 2655 (:REWRITE DEFAULT-UNARY-MINUS))
 (17843 2549
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13804 13804 (:REWRITE DEFAULT-CDR))
 (11414 11414 (:REWRITE DEFAULT-CAR))
 (11052 2072
        (:REWRITE FUTER::|a < b or b < a or a = b|))
 (10954
  177
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (8127 903
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (7965 2655 (:REWRITE DEFAULT-+-2))
 (4992 240
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (4848 41
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (4564
      16
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (4514 2466
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (4490 4490
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (4490 4490
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (2912 1456 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (2907 33 (:DEFINITION FUPOL::>-MONOMIO))
 (2124
    177
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (2072 2072
       (:REWRITE FUTER::|a < b & b < c => a < c|))
 (1226 22
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (1062 354 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (1006 41 (:REWRITE DEFAULT-<-1))
 (815 99
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (716 33
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (683 33
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (612 66
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (410 410
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (374 374
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (316 41 (:REWRITE DEFAULT-<-2))
 (242 242
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (177 177 (:DEFINITION FUMON::-))
 (132 132
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (84 66
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (60 12 (:REWRITE FUMON::TERMINO-MONOMIO))
 (42 42
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (42 14
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (20 4 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (18 18 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (6 6 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-9
 (1555 6
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (1069
   20
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (739 10
      (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (560 4
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (386
  15
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (386 6
      (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (324 6
      (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (287 4
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (270 135 (:REWRITE DEFAULT-UNARY-MINUS))
 (270 135 (:REWRITE DEFAULT-+-2))
 (260 4
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (255 135 (:REWRITE DEFAULT-+-1))
 (240 4
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (194 7
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (164 14 (:REWRITE DEFAULT-<-1))
 (155 31
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (150
    15
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (146 6
      (:REWRITE FUNPOL::|deg (- p) =e deg p|))
 (103 16
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (84 14 (:REWRITE DEFAULT-<-2))
 (72 30 (:DEFINITION FUMON::-))
 (67 10
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (65 53 (:REWRITE DEFAULT-CDR))
 (65 13
     (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (65 13
     (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (59 59 (:REWRITE DEFAULT-CAR))
 (57 57
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (46 46
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (44 44
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (42 10
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (39 6 (:REWRITE FUNPOL::|- p != 0|))
 (36 6 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (27 27
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (27 3
     (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (21 3 (:REWRITE FUMON::TERMINO-MONOMIO))
 (21 3 (:DEFINITION FUMON::NULOP))
 (18 6 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (16 4
     (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (10 6
     (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (10 6
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (8 2
    (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (6 6
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (6 3 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (3 3 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (3 3 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (3 1
    (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO)))
(FUNPOL::=-IMPLIES-=-QUOT-1
     (124 4
          (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
     (90 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (83 7 (:DEFINITION FUPOL::POLINOMIOP))
     (70 14
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (52 5 (:REWRITE DEFAULT-<-1))
     (50 14
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (38 38 (:REWRITE DEFAULT-CDR))
     (36 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 28
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (28 28
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (28 28 (:REWRITE DEFAULT-CAR))
     (27 7
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (26 5 (:REWRITE DEFAULT-<-2))
     (20 10
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (14 14
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (8 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|)))
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1
     (345 180
          (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (42 3 (:REWRITE DEFAULT-<-1))
     (39 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (36 3 (:REWRITE DEFAULT-<-2))
     (25 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (20 4
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (20 2 (:DEFINITION FUPOL::POLINOMIOP))
     (17 4
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (12 12 (:REWRITE DEFAULT-CDR))
     (8 8
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (8 8
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (8 8 (:REWRITE DEFAULT-CAR))
     (7 2
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (6 2
        (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
     (6 2
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
     (4 4
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 2
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 1
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (2 2
        (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-2
     (39936 2674
            (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (14568 2896
            (:REWRITE FUTER::|a < b or b < a or a = b|))
     (13624 13624
            (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (13496 420
            (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (11052 11052 (:REWRITE DEFAULT-CDR))
     (9170 722
           (:REWRITE FUTER::|a < b => ~(b < a)|))
     (7814 2376
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (4456 2288
           (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (3256 2896
           (:REWRITE FUTER::|a < b & b < c => a < c|))
     (2558 2558
           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2038 1220 (:REWRITE DEFAULT-+-1))
     (2008 1190 (:REWRITE DEFAULT-UNARY-MINUS))
     (1246 1220 (:REWRITE DEFAULT-+-2))
     (926 246 (:REWRITE FLD::|a * b = b * a|))
     (896 448 (:REWRITE DEFAULT-<-2))
     (896 448 (:REWRITE DEFAULT-<-1))
     (148 4 (:DEFINITION FUPOL::>-MONOMIO))
     (28 12
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (16 16
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (12 4
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|)))
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-3
     (238 6 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (214 20
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (132 4 (:DEFINITION FUPOL::>-MONOMIO))
     (84 20
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (46 6 (:DEFINITION FUPOL::POLINOMIOP))
     (40 40 (:REWRITE DEFAULT-CDR))
     (32 32
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (32 32
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (28 28 (:REWRITE DEFAULT-CAR))
     (28 12
         (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
     (28 6
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (20 20
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (18 3 (:REWRITE DEFAULT-<-2))
     (16 16
         (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
     (16 4
         (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
     (14 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 4
         (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
     (9 4 (:REWRITE DEFAULT-+-2))
     (8 4 (:REWRITE DEFAULT-+-1))
     (8 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 3 (:REWRITE DEFAULT-<-1))
     (2 2 (:DEFINITION FUMON::NULOP)))
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-4)
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-5)
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-6)
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-7
     (294 2 (:DEFINITION FUPOL::+-MONOMIO))
     (175 8 (:DEFINITION FUPOL::POLINOMIOP))
     (140 8
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (102 11
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (71 13
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (48 48 (:REWRITE DEFAULT-CDR))
     (48 48 (:REWRITE DEFAULT-CAR))
     (31 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (29 29
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (29 29
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (24 8
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (13 13
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (12 2 (:DEFINITION FUMON::+))
     (10 2 (:REWRITE FLD::|a + b = b + a|))
     (6 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 4
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (4 2
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (2 2
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-8)
(FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-9
 (102098 3295 (:DEFINITION FUPOL::POLINOMIOP))
 (76697 5328
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (74023 2329 (:DEFINITION FUPOL::*-MONOMIO))
 (58188 92
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (54900 92
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (51623 2837
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (50416 514
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (41157 48
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (30406 2020 (:REWRITE FUMON::|a * b = b * a|))
 (26590 261
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (26561
   261
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (25668 92
        (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (18340 384
        (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (17796
  170
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (17297 17297 (:REWRITE DEFAULT-CDR))
 (16881 44 (:REWRITE FLD::|a + b = b + a|))
 (16562 388
        (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (16450 2944
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16006 2353 (:REWRITE DEFAULT-UNARY-MINUS))
 (15986 2353 (:REWRITE DEFAULT-+-1))
 (14819 2845
        (:REWRITE FUTER::|a < b or b < a or a = b|))
 (13987 13987 (:REWRITE DEFAULT-CAR))
 (13920 26
        (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (13920 26
        (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (13401 26
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (13401 26
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (12068 95
        (:REWRITE FUTER::|a < b => ~(b < a)|))
 (11835 596
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (10978
      40
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (9671 5079
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (7059 2353 (:REWRITE DEFAULT-+-2))
 (6992 64
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (6287 73 (:DEFINITION FUPOL::>-MONOMIO))
 (5987 5987
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (5987 5987
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (5092
  82
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (4629 428 (:REWRITE DEFAULT-<-1))
 (4122 60
       (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (3487 428 (:REWRITE DEFAULT-<-2))
 (3276 364
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (2862 1431 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (2845 2845
       (:REWRITE FUTER::|a < b & b < c => a < c|))
 (2497 48
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (1866 386
       (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (1811 92
       (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (1755 219
       (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (1536 73
       (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (1463 73
       (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (984
    82
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (750 250
      (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (629 629
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (492 164 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (372 372 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (334 4 (:REWRITE FUNPOL::|p + q = q + p|))
 (292 292
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (208 208
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (156 8 (:REWRITE FUNPOL::|nil + p = p|))
 (146 92
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (87 29
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (82 82 (:DEFINITION FUMON::-))
 (80 16 (:REWRITE FUMON::TERMINO-MONOMIO))
 (24 24 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (16 16 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::=-IMPLIES-=-QUOT-2
 (41576 4 (:DEFINITION FUNPOL::QUOT))
 (31484 4 (:DEFINITION FUPOL::+-MONOMIO))
 (20441 626 (:DEFINITION FUPOL::POLINOMIOP))
 (16208 78
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (16067 1094
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (13130 494 (:DEFINITION FUPOL::*-MONOMIO))
 (11375 576
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (10978 34
        (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (9196 112
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (7704 4
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (7704 4 (:DEFINITION FUMON::+))
 (7680 4 (:REWRITE FLD::|a + b = b + a|))
 (6084 468 (:REWRITE FUMON::|a * b = b * a|))
 (4614 48
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (4448 218
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (3522 504
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3388 502 (:REWRITE DEFAULT-UNARY-MINUS))
 (3388 502 (:REWRITE DEFAULT-+-1))
 (3376
  40
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (3304 3304 (:REWRITE DEFAULT-CDR))
 (3064 580
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (2746 2746 (:REWRITE DEFAULT-CAR))
 (2686 34 (:REWRITE FUNPOL::|- p != 0|))
 (2444 32
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (2122 226
       (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (1885 42
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1506 502 (:REWRITE DEFAULT-+-2))
 (1242 1242
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (1242 1242
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (1134 230
       (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (1042 78
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (1042
   78
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (1038 558
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1032 506
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (922 922
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (878 106
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (848 106
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (796 20
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (796 20
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (796 20
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (796 20
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (680 340 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (632 33 (:REWRITE DEFAULT-<-1))
 (580 580
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (552 66
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (418 14
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (412 8 (:REWRITE FUNPOL::|p + q = q + p|))
 (324 33 (:REWRITE DEFAULT-<-2))
 (232 8 (:REWRITE FUNPOL::|nil + p = p|))
 (218 218 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (216 4
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (212 212
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (110 22
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (80
  16
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (68 68
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (40 8 (:REWRITE FUMON::TERMINO-MONOMIO))
 (36 36
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (32 32
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (12 12 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (8 8
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (8 8 (:REWRITE FUNPOL::|- nil =e nil|))
 (4 4
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-1|
 (2885 112 (:DEFINITION FUPOL::*-MONOMIO))
 (2261 115 (:DEFINITION FUPOL::POLINOMIOP))
 (2090 30
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (1570 196
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (1150
  10
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (909 91 (:REWRITE FUMON::|a * b = b * a|))
 (892 152
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (547 1
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (547
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (547 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (547 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (547 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (545 1
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (545 1
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (501 411 (:REWRITE DEFAULT-CDR))
 (414 384 (:REWRITE DEFAULT-CAR))
 (399 61
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (390 10 (:REWRITE FUMON::TERMINO-MONOMIO))
 (350
  10
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (334 334
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (229 109
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (224 112 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (224 112 (:REWRITE DEFAULT-UNARY-MINUS))
 (224 112 (:REWRITE DEFAULT-+-2))
 (224 112 (:REWRITE DEFAULT-+-1))
 (204 61
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (200 40
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (200 40
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (200
    20
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (170 50 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (140 140
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (135 135
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (109 109
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (106 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (86 43 (:DEFINITION FUMON::NULOP))
 (70 50
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (66 2 (:DEFINITION FUPOL::>-MONOMIO))
 (61 61
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (51 31
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (43 43 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (20 20
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (20 20 (:DEFINITION FUMON::-))
 (14 6
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (8 8 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (8 2
    (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (6 2
    (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (6 2 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE DEFAULT-<-2)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-2|
     (222 15
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (214 21
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (146 26
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (116 8 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (80 16
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (77 77 (:REWRITE DEFAULT-CDR))
     (70 70
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (70 35 (:REWRITE DEFAULT-<-2))
     (70 35 (:REWRITE DEFAULT-<-1))
     (60 60
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (60 60
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (48 16 (:TYPE-PRESCRIPTION FLD::FDP-+))
     (32 32
         (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (32 13
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (26 26
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (16 16
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (9 7
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (8 4
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (8 4
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (7 7
        (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|
     (724 724 (:REWRITE DEFAULT-CDR))
     (711 711 (:REWRITE DEFAULT-CAR))
     (632 114
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (457 47
          (:REWRITE FUTER::|a < b => ~(b < a)|))
     (402 401 (:REWRITE DEFAULT-<-2))
     (402 401 (:REWRITE DEFAULT-<-1))
     (270 270 (:TYPE-PRESCRIPTION FLD::FDP-0_F))
     (154 47
          (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (132 114
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (75 15 (:REWRITE FLD::|a * b = b * a|))
     (40 20
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (35 35
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (34 19 (:REWRITE DEFAULT-+-1))
     (32 16
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (31 16 (:REWRITE DEFAULT-UNARY-MINUS))
     (22 19 (:REWRITE DEFAULT-+-2))
     (12 12
         (:TYPE-PRESCRIPTION FUTER::TERMINOP-UNO)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|
     (1264 157
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (1058 188
           (:REWRITE FUTER::|a < b or b < a or a = b|))
     (1022 75
           (:REWRITE FUTER::|a < b => ~(b < a)|))
     (835 835 (:REWRITE DEFAULT-CAR))
     (703 703 (:REWRITE DEFAULT-CDR))
     (480 448 (:REWRITE DEFAULT-<-1))
     (474 448 (:REWRITE DEFAULT-<-2))
     (276 82
          (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (224 188
          (:REWRITE FUTER::|a < b & b < c => a < c|))
     (176 176
          (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (126 126
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (70 38 (:REWRITE DEFAULT-+-1))
     (66 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (60 12 (:REWRITE FLD::|a * b = b * a|))
     (54 27
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (44 38 (:REWRITE DEFAULT-+-2))
     (20 16
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (20 10
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|
     (277 277 (:REWRITE DEFAULT-CDR))
     (262 262 (:REWRITE DEFAULT-CAR))
     (124 123 (:REWRITE DEFAULT-<-2))
     (124 123 (:REWRITE DEFAULT-<-1))
     (100 18
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (53 38 (:REWRITE DEFAULT-+-1))
     (47 32 (:REWRITE DEFAULT-UNARY-MINUS))
     (45 5 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (41 38 (:REWRITE DEFAULT-+-2))
     (36 13
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (35 35
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (32 16
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (32 16
         (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (18 18
         (:REWRITE FUTER::|a < b & b < c => a < c|)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-6|
     (12646 4 (:DEFINITION FUNPOL::QUOT))
     (9972 4 (:DEFINITION FUPOL::+-MONOMIO))
     (5179 5179 (:REWRITE DEFAULT-CAR))
     (5102 247
           (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
     (4618 8 (:DEFINITION FUPOL::POLINOMIOP))
     (4594 8
           (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (3568 320
           (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
     (2636 429
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
     (2289 247
           (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
     (2149 4
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (1957 4
           (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (1739 34
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
     (1731 34
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
     (1452 36
           (:REWRITE FUNPOL::|(p + q) + r = p + (q + r)|))
     (1144 1103 (:REWRITE DEFAULT-+-1))
     (1136 1099 (:REWRITE DEFAULT-UNARY-MINUS))
     (1113 1103 (:REWRITE DEFAULT-+-2))
     (824 247
          (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (448 112 (:REWRITE FLD::|a * b = b * a|))
     (448 10 (:REWRITE FUMON::TERMINO-MONOMIO))
     (440 8 (:DEFINITION FUMON::NULOP))
     (432 8 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (253 247
          (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (253 247
          (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
     (244 4
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (150 150
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (125 125
          (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
     (118 118
          (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (68 35 (:REWRITE DEFAULT-<-1))
     (66 22 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (64 35 (:REWRITE DEFAULT-<-2))
     (50 50
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (48 8
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (36 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (24 24
         (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
     (24 24
         (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
     (20 20
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (20 20
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (20 20 (:REWRITE DEFAULT-CDR))
     (20 4
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (16 4 (:REWRITE COMMUTATIVITY-OF-+))
     (12 12 (:TYPE-PRESCRIPTION FUTER::<))
     (12 12 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
     (8 8
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (4 4 (:DEFINITION FUMON::+)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-7|
     (2 1 (:TYPE-PRESCRIPTION FLD::FDP-*)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-8|
 (16218 12 (:DEFINITION FUNPOL::QUOT))
 (14250 6 (:DEFINITION FUPOL::+-MONOMIO))
 (8770 12 (:DEFINITION FUPOL::POLINOMIOP))
 (8734 12
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (6698 295
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (6581 6581 (:REWRITE DEFAULT-CAR))
 (4416 412
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (3472 509
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (2723 70
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (2685 295
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (2511 70
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (2149 4
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (1957 4
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (1780 44
       (:REWRITE FUNPOL::|(p + q) + r = p + (q + r)|))
 (1484 1415 (:REWRITE DEFAULT-+-1))
 (1464 295
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (1460 1403 (:REWRITE DEFAULT-UNARY-MINUS))
 (1433 1415 (:REWRITE DEFAULT-+-2))
 (516 132 (:REWRITE FLD::|a * b = b * a|))
 (480 14 (:REWRITE FUMON::TERMINO-MONOMIO))
 (476 12 (:DEFINITION FUMON::NULOP))
 (464 12
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (301 295
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (301 295
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (254 254
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (244 4
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (221 221
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (166 166
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (122 61 (:REWRITE DEFAULT-<-1))
 (114 38 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (110 61 (:REWRITE DEFAULT-<-2))
 (70 70
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (64 12
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (60 12
     (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (54 6 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (48 12 (:REWRITE COMMUTATIVITY-OF-+))
 (32 32
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (32 32
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (30 30 (:REWRITE DEFAULT-CDR))
 (28 28
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (26
    2
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-2|))
 (24 24
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (22 2
     (:REWRITE FUPOL::|m >-monomio p => primero (m +M p) =e m|))
 (18 18 (:TYPE-PRESCRIPTION FUTER::<))
 (16 16 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (12 12
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (6 6 (:DEFINITION FUMON::+))
 (6 3
    (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-9|
     (83 28 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (56 56 (:REWRITE DEFAULT-CAR))
     (27 27
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (23 1
         (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
     (18 18
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (16 11 (:REWRITE DEFAULT-+-1))
     (16 2 (:REWRITE FUMON::TERMINO-MONOMIO))
     (16 2 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (11 11 (:REWRITE DEFAULT-+-2))
     (8 4 (:REWRITE DEFAULT-<-2))
     (8 4 (:REWRITE DEFAULT-<-1))
     (6 3
        (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
     (4 1
        (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
     (1 1
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-10|
     (30 15
         (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-11|
     (154 52 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (128 106 (:REWRITE DEFAULT-CAR))
     (128 55
          (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
     (52 2
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
     (50 50
         (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (34 1
         (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
     (28 22 (:REWRITE DEFAULT-UNARY-MINUS))
     (28 22 (:REWRITE DEFAULT-+-1))
     (26 1
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
     (26 1
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
     (23 1
         (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
     (22 22
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (22 22 (:REWRITE DEFAULT-+-2))
     (16 2 (:REWRITE FUMON::TERMINO-MONOMIO))
     (16 2 (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (10 5 (:REWRITE DEFAULT-<-2))
     (10 5 (:REWRITE DEFAULT-<-1))
     (6 6
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
     (6 3
        (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
     (5 5
        (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
     (4 1
        (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|)))
(FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)|
 (32217 374 (:DEFINITION FUPOL::*-MONOMIO))
 (23918 797 (:DEFINITION FUPOL::POLINOMIOP))
 (20329 11 (:DEFINITION FUPOL::+-MONOMIO))
 (20216
    706
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|))
 (16290 1103
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (15990 326 (:REWRITE FUMON::|a * b = b * a|))
 (12730 91
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (12502 11
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (10365 11
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (5766
   21
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (5751 21
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (5458 873
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (5398 11
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (5000 4
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (5000 4
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (4740
  33
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (4543 885
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (4496 4496 (:REWRITE DEFAULT-CDR))
 (3828 3
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (3828 3
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (3622 3622 (:REWRITE DEFAULT-CAR))
 (2976 398 (:REWRITE DEFAULT-+-1))
 (2962 430
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2948 397 (:REWRITE DEFAULT-UNARY-MINUS))
 (2858 376
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (2571 43
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2448 11 (:DEFINITION FUMON::+))
 (2182 1152
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1835 1835
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (1823 1823
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (1725
  25
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (1710
      5
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (1536 69
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1470 27 (:DEFINITION FUPOL::>-MONOMIO))
 (1392
    12
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|))
 (1205 398 (:REWRITE DEFAULT-+-2))
 (1116 124
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (1020
    12
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (885 885
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (795 5
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (762 762
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (727 5 (:REWRITE FLD::|a + b = b + a|))
 (665 5
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (652 326 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (466 11
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (364 81
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (308 16 (:REWRITE DEFAULT-<-1))
 (300
    25
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (283 27
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (256 27
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (180 16 (:REWRITE DEFAULT-<-2))
 (150 50 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (120 50
      (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (108 108
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (55 55
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (26 11
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (25 25 (:DEFINITION FUMON::-))
 (12 4
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (6 6 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (4 4
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (4 4
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-1|
 (570 224
      (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (138 13 (:DEFINITION FUPOL::POLINOMIOP))
 (84 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (84 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (70 14
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (62 62 (:REWRITE DEFAULT-CDR))
 (61 61
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (49 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (48 48 (:REWRITE DEFAULT-CAR))
 (42 1
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (42
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (42 1
     (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (42 1
     (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (40 20
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (39 14
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (29 12
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (29 12
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (28 28
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (28 28
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (28 4
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (28 2 (:REWRITE DEFAULT-<-2))
 (28 2 (:REWRITE DEFAULT-<-1))
 (27 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (14 14
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-2|
     (365 19
          (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (145 109 (:REWRITE DEFAULT-CDR))
     (139 27
          (:REWRITE FUTER::|a < b or b < a or a = b|))
     (128 8 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (115 24
          (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (99 99 (:REWRITE DEFAULT-CAR))
     (72 72
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (72 36 (:REWRITE DEFAULT-<-2))
     (72 36 (:REWRITE DEFAULT-<-1))
     (56 56
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (46 17
         (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (27 27
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (21 7 (:TYPE-PRESCRIPTION FLD::FDP-+))
     (20 20 (:TYPE-PRESCRIPTION FUNPOL::=))
     (8 8 (:TYPE-PRESCRIPTION FUTER::<))
     (7 7
        (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
     (6 3
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (6 3
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (5 5
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-3|
 (56002 14 (:DEFINITION FUPOL::+-MONOMIO))
 (43917 2076
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (30516 315 (:DEFINITION FUPOL::*-MONOMIO))
 (24826 1476
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (22561
  138
  (:REWRITE
    FUPOL::|(primero p) >-monomio (resto p) => primero (fn p) =e primero p|))
 (15164 262 (:REWRITE FUPOL::FN-ORDENADO))
 (10574 24 (:DEFINITION FUPOL::>-MONOMIO))
 (9836 70
       (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (9318 12
       (:REWRITE FUPOL::|m >-monomio p => m >-monomio (fn p)|))
 (9191 168
       (:REWRITE FUPOL::|p + q =e mp(p) +M (resto(p) + q)|))
 (9163 9163 (:REWRITE DEFAULT-CDR))
 (8734 1332
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (8204 1454
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (7010 3496
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (6620 6593 (:REWRITE DEFAULT-CAR))
 (4754 14 (:DEFINITION FUMON::+))
 (4674 6
       (:REWRITE FUPOL::|q + p = mp(p) +M (q + resto(p))|))
 (4444
      182
      (:REWRITE
           FUPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (4002
      10
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (3925 14
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (3579 36
       (:REWRITE FUPOL::|p != 0 => m *M p != 0|))
 (3375 3375
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (3375 3375
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (3059 69
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lemma-3|))
 (2361 1454
       (:REWRITE FUTER::|a < b & b < c => a < c|))
 (1925 17
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1727 34
       (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (1691 44
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1428 14
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (1072 34
       (:REWRITE FUPOL::|nulop p1 * p2 <=> nulop p1 or nulop p2|))
 (855 87
      (:REWRITE FUPOL::|primero (p1 * p2) != 0|))
 (738 10 (:REWRITE FLD::|a + b = b + a|))
 (713 4
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lemma-1|))
 (642 642 (:TYPE-PRESCRIPTION FUPOL::*))
 (597 4
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lemma-2|))
 (466 466
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (346 346 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (332 6
      (:REWRITE FUPOL::|primero (* p1 p2) >-monomio resto (* p1 p2)|))
 (322 127 (:TYPE-PRESCRIPTION FUPOL::+))
 (212 212
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (132 132
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-*))
 (125 2
      (:REWRITE FUPOL::|p1 != 0 and p2 != 0 => fn(p1 * p2) != 0|))
 (125 2
      (:REWRITE FUPOL::|nulop fn(p1 * p2) <=> nulop p1 or nulop p2|))
 (122 122 (:TYPE-PRESCRIPTION ATOM))
 (122 2
      (:REWRITE FUPOL::|primero (m *M p) >-monomio resto (m *M p)|))
 (121 121 (:REWRITE FUPOL::POLINOMIOP-*))
 (116 70
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (100 100 (:REWRITE FUTER::|~(a < a)|))
 (72 72
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-+))
 (60 60 (:REWRITE FUPOL::ORDENADOP-FN))
 (59 59
     (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (49 49 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (36 36
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-*-MONOMIO))
 (30 30 (:REWRITE FUPOL::POLINOMIOP-FN))
 (27 12
     (:REWRITE FUPOL::|m = 0 => m *M p = 0|))
 (20 20
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (12 12
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-FN))
 (10 10
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (5 2
    (:REWRITE FUPOL::|m = 0 => fn(m *M p) =e 0|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-4|
 (1509 102
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (1342 10
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (1017
   10
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (988 23 (:DEFINITION FUPOL::*-MONOMIO))
 (850 162
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (666 131
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (638 638 (:REWRITE DEFAULT-CDR))
 (608 10
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (588 588 (:REWRITE DEFAULT-CAR))
 (330 330
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (323 16
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (294 14
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (256 28
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (252
     63
     (:REWRITE
          FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (240 114
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (162 162
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (159 87
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (156 4 (:REWRITE FUMON::|a * b = b * a|))
 (64 64
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (40 8 (:REWRITE FLD::|a + b = b + a|))
 (22 11
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (22 11
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (21 21
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (16 16
     (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (14 14
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 7 (:REWRITE DEFAULT-<-2))
 (14 7 (:REWRITE DEFAULT-<-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-5|
 (1243 58 (:DEFINITION FUPOL::POLINOMIOP))
 (913 18
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (746 44 (:DEFINITION FUPOL::*-MONOMIO))
 (710 58
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (605
   18
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (501 18
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (344 24
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (294 294 (:REWRITE DEFAULT-CDR))
 (263 51
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (256 256 (:REWRITE DEFAULT-CAR))
 (217 2 (:DEFINITION FUPOL::+-MONOMIO))
 (208 52
      (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (202 46
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (202 27
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (184 49
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (131 25
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (124
  8
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (106 106
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (106 106
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (96 8
     (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (88 12 (:REWRITE FUNPOL::|- p != 0|))
 (86 44
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (51 51
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (42 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (42 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (36 9
     (:REWRITE
          FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (31 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (26 26
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (16 16
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (12 3
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (8 2
    (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (7 2 (:DEFINITION FUMON::+))
 (5 5
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (5 1 (:REWRITE FLD::|a + b = b + a|))
 (4 2
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (4 2
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (2 2
    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-6|
 (65269 1 (:DEFINITION FUNPOL::QUOT))
 (47067 3 (:DEFINITION FUPOL::+-MONOMIO))
 (39294 1341 (:DEFINITION FUPOL::*-MONOMIO))
 (34746 1198 (:DEFINITION FUPOL::POLINOMIOP))
 (26766 1773
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (24227 374
        (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (20970 10
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (19409 10
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (18187 3
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (17957 65
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (16975 334 (:REWRITE FLD::|a * b = b * a|))
 (16328 770
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (13028 121
        (:REWRITE FUNPOL::|FLD::fdp (lc p)|))
 (9691
   374
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (8925 374
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (8829 573 (:REWRITE FUMON::|a * b = b * a|))
 (8341 1182
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (7068 10
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (6699
  23
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (5629 5629 (:REWRITE DEFAULT-CDR))
 (5471 3
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (5471 3
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (5273 234
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (5273 234
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (4821 4821 (:REWRITE DEFAULT-CAR))
 (4559 19
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (4518 117
       (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (4180 115
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (4103 771
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (4015 9 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (3637 1347 (:REWRITE DEFAULT-+-1))
 (3345
    1115
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|))
 (3287 747
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (3209 3209
       (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (3154 1347 (:REWRITE DEFAULT-+-2))
 (2690 1345 (:REWRITE DEFAULT-UNARY-MINUS))
 (2630 7 (:DEFINITION FUPOL::>-MONOMIO))
 (2602 1301 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (2576 222
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1745 3 (:DEFINITION FUMON::+))
 (1666 1666
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (1666 1666
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (1404 172
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1226
      2
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (1189 163
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1146 642
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1064 2 (:REWRITE FUMON::TERMINO-MONOMIO))
 (863 3
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (782 16 (:REWRITE FUNPOL::|- p != 0|))
 (771 771
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (717 21
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (689 7
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (516 2 (:REWRITE FLD::|a + b = b + a|))
 (386 7
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (242 121 (:TYPE-PRESCRIPTION FLD::FDP-/))
 (174 7 (:REWRITE DEFAULT-<-1))
 (115 115 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (97 10
     (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (90 30
     (:TYPE-PRESCRIPTION FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (28 28
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (23 23
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (14 7 (:REWRITE DEFAULT-<-2))
 (12 10
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (12 4
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (6 6
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (6 6
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (3 3 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (2 2
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (2 2 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-7|
     (76 2 (:DEFINITION FUPOL::ORDENADOP))
     (41 1
         (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
     (41 1
         (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
     (24 2 (:DEFINITION FUPOL::POLINOMIOP))
     (12 12
         (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 2
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (8 8 (:REWRITE DEFAULT-CAR))
     (8 4
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
     (4 4
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (4 4
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (4 4 (:TYPE-PRESCRIPTION FUTER::<))
     (4 2
        (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
     (4 2
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (4 2
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (4 2 (:DEFINITION FUMON::NULOP))
     (2 2
        (:REWRITE FUTER::|a < b & b < c => a < c|))
     (2 2 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-8|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-9|
     (18693 5 (:DEFINITION FUNPOL::QUOT))
     (15268 5 (:DEFINITION FUPOL::+-MONOMIO))
     (10255 50
            (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
     (7658 10 (:DEFINITION FUPOL::POLINOMIOP))
     (7628 10
           (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
     (5161 507
           (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
     (5112 26
           (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
     (4406 1867 (:REWRITE DEFAULT-+-2))
     (3878 1867 (:REWRITE DEFAULT-+-1))
     (3850 1862 (:REWRITE DEFAULT-UNARY-MINUS))
     (3564 5
           (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
     (3480 369
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
     (3230 369
           (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
     (2865 340 (:REWRITE FLD::|a * b = b * a|))
     (2329 5
           (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
     (1865 60 (:REWRITE FUNPOL::|FLD::fdp (lc p)|))
     (1482 50
           (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
     (1445 35
           (:REWRITE FUNPOL::|(p + q) + r = p + (q + r)|))
     (752 44 (:REWRITE DEFAULT-<-1))
     (641 15 (:REWRITE FUMON::TERMINO-MONOMIO))
     (630 10 (:DEFINITION FUMON::NULOP))
     (620 10
          (:REWRITE FUMON::COEFICIENTE-MONOMIO))
     (524 62
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (322 322
          (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
     (285 5
          (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
     (259 259
          (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
     (190 44 (:REWRITE DEFAULT-<-2))
     (120 60 (:TYPE-PRESCRIPTION FLD::FDP-/))
     (78 50
         (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
     (62 50
         (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
     (60 10
         (:REWRITE FUTER::|a < b or b < a or a = b|))
     (58 29 (:TYPE-PRESCRIPTION FLD::FDP-*))
     (45 45 (:REWRITE DEFAULT-CAR))
     (45 5 (:REWRITE FUTER::|a < b => ~(b < a)|))
     (42 5
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
     (37 5 (:REWRITE COMMUTATIVITY-OF-+))
     (30 30
         (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
     (30 30
         (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
     (25 25
         (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
     (25 25
         (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
     (25 25 (:REWRITE DEFAULT-CDR))
     (15 15 (:TYPE-PRESCRIPTION FUTER::<))
     (15 15 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
     (10 10
         (:REWRITE FUTER::|a < b & b < c => a < c|))
     (5 5 (:DEFINITION FUMON::+)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-10|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-11|
     (4 2 (:TYPE-PRESCRIPTION FLD::FDP-*)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-12|
     (10 5 (:TYPE-PRESCRIPTION FLD::FDP-*)))
(FUNPOL::|nil * p =e nil|)
(FUNPOL::|p * nil =e nil|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-13|
 (370 10 (:DEFINITION FUPOL::*-MONOMIO))
 (324 16
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (207 2
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (125 2
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (125
   2
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (91 91 (:REWRITE DEFAULT-CDR))
 (85 17
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (74 74 (:REWRITE DEFAULT-CAR))
 (39 17
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (34 34
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (34 34
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (34 16
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (20 10
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (17 17
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (13 1
     (:REWRITE FUTER::|a < b => ~(b < a)|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-14|
 (296 8 (:DEFINITION FUPOL::*-MONOMIO))
 (265 14
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (121 1
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (121
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (91 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (80 80 (:REWRITE DEFAULT-CDR))
 (80 16
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (64 64 (:REWRITE DEFAULT-CAR))
 (43 16
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (33 14
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (32 32
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (32 32
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (27 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (16 16
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (16 8
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-15|
 (830 54 (:DEFINITION FUPOL::*-MONOMIO))
 (581 49
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (413
   2
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (367 2
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (320 12
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (306 2
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (205 205 (:REWRITE DEFAULT-CDR))
 (178 178 (:REWRITE DEFAULT-CAR))
 (135 27
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (128
  4
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (65 27
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (64 4
     (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (55 25
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (54 54
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (54 54
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (48 2 (:REWRITE FUNPOL::|- p != 0|))
 (36 18
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (27 27
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (27 2
     (:REWRITE FUTER::|a < b => ~(b < a)|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-16|
 (1142 94 (:DEFINITION FUPOL::*-MONOMIO))
 (711 78
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (640 24
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (626
   4
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (534 4
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (472 4
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (326 42
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (294 294 (:REWRITE DEFAULT-CDR))
 (262 262 (:REWRITE DEFAULT-CAR))
 (256
  8
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (160 32
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (128 8
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (96 4 (:REWRITE FUNPOL::|- p != 0|))
 (75 32
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (65 30
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (64 64
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (64 64
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (56 28
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (32 32
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (27 2
     (:REWRITE FUTER::|a < b => ~(b < a)|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-17|
 (1407 113 (:DEFINITION FUPOL::*-MONOMIO))
 (923 98
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (720 27
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (680
   12
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (588 12
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (526 12
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (378 378 (:REWRITE DEFAULT-CDR))
 (356 47
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (334 334 (:REWRITE DEFAULT-CAR))
 (288
  9
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (215 43
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (208 52
      (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (144 9
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (132 41
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (111 43
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (96 4 (:REWRITE FUNPOL::|- p != 0|))
 (86 86
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (86 86
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (84 42
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (43 43
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (42 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (42 2
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (27 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (12 3
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (8 2
    (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-18|
 (11137 147
        (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (7530 163
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (6408 4
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (5929 1
       (:REWRITE FUNPOL::=-IMPLIES-EQUAL-DEG-B))
 (5207 1
       (:REWRITE FUNPOL::=-IMPLIES-EQUAL-DEG-A))
 (4759 278
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (4397 181
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (3562 122
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (3064 20 (:DEFINITION FUMON::+))
 (2732 4
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (2672
      4
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (2628 56 (:REWRITE FUNPOL::|0 + p = p|))
 (1838
   163
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (1825 1531 (:REWRITE DEFAULT-CDR))
 (1764 280
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1710 294
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1696
  36
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1544 772 (:REWRITE DEFAULT-UNARY-MINUS))
 (1544 772 (:REWRITE DEFAULT-+-2))
 (1544 772 (:REWRITE DEFAULT-+-1))
 (1348 12
       (:REWRITE FUNPOL::|p + (q + r) = q + (p + r)|))
 (1341 33
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1287 1203 (:REWRITE DEFAULT-CAR))
 (1175 23
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1100 552
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1092
  42
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (1016 10 (:REWRITE FUNPOL::|p + q = q + p|))
 (880 42
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (876 540
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (840 60 (:REWRITE FUMON::TERMINO-MONOMIO))
 (700
    70
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (656 200 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (630 126
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (630 126
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (609 5 (:DEFINITION FUPOL::>-MONOMIO))
 (540 540
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (476 22 (:REWRITE FUNPOL::|- p != 0|))
 (468 10 (:REWRITE FUNPOL::|p + 0 = p|))
 (434 434
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (294 294
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (276 220
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (260 20 (:REWRITE FLD::|a + b = b + a|))
 (240 8
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (236 20
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (236 20
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (183 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (170 170
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (168 5
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (163 5
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (128 128
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (112 16
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (102 6 (:REWRITE FUPOL::|resto(m +M p) = p|))
 (84 12
     (:TYPE-PRESCRIPTION FUPOL::|m +M p != 0|))
 (80 16
     (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (70 70 (:DEFINITION FUMON::-))
 (64 4 (:REWRITE FUPOL::|mp(m +M p) = m|))
 (48 48
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO))
 (42 42
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (34 17 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (24 8
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (12 12 (:TYPE-PRESCRIPTION FUPOL::+M))
 (9 5
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (4 2
    (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2b|))
 (4 2
    (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2a|))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-19|
 (11598 148
        (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (7407 164
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (5993 1
       (:REWRITE FUNPOL::=-IMPLIES-EQUAL-DEG-B))
 (5759 5
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (5271 1
       (:REWRITE FUNPOL::=-IMPLIES-EQUAL-DEG-A))
 (4867 294
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (4549 189
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (3910 134
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (3100 20 (:DEFINITION FUMON::+))
 (3063 5
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (2708
      4
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (2628 56 (:REWRITE FUNPOL::|0 + p = p|))
 (2195
   164
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (2181 5
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (1921 1591 (:REWRITE DEFAULT-CDR))
 (1904
  40
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1822 310
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1764 280
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1636 818 (:REWRITE DEFAULT-UNARY-MINUS))
 (1636 818 (:REWRITE DEFAULT-+-2))
 (1636 818 (:REWRITE DEFAULT-+-1))
 (1355 1259 (:REWRITE DEFAULT-CAR))
 (1348 12
       (:REWRITE FUNPOL::|p + (q + r) = q + (p + r)|))
 (1196
  46
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (1175 23
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1138 34
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1132 568
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (948 564
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (928 64 (:REWRITE FUMON::TERMINO-MONOMIO))
 (880 42
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (780
    78
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (724 220 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (710 142
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (710 142
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (609 5 (:DEFINITION FUPOL::>-MONOMIO))
 (564 564
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (508 10 (:REWRITE FUNPOL::|p + q = q + p|))
 (490 490
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (476 22 (:REWRITE FUNPOL::|- p != 0|))
 (468 10 (:REWRITE FUNPOL::|p + 0 = p|))
 (310 310
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (304 240
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (271 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (271 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (260 20 (:REWRITE FLD::|a + b = b + a|))
 (240 8
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (236 20
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (236 20
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (234 234
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (183 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (168 5
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (163 5
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (136 136
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (112 16
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (102 6 (:REWRITE FUPOL::|resto(m +M p) = p|))
 (84 12
     (:TYPE-PRESCRIPTION FUPOL::|m +M p != 0|))
 (80 16
     (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (78 78 (:DEFINITION FUMON::-))
 (72 72
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO))
 (64 4 (:REWRITE FUPOL::|mp(m +M p) = m|))
 (42 42
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (34 17 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (28 2 (:REWRITE DEFAULT-<-1))
 (24 8
     (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (13 1
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:TYPE-PRESCRIPTION FUPOL::+M))
 (9 5
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2
    (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2b|))
 (4 2
    (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2a|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-20|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-21|
 (42763 26 (:DEFINITION FUNPOL::QUOT))
 (26880 855
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (18732 52
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (15853 270 (:DEFINITION FUPOL::POLINOMIOP))
 (15758 6683
        (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (10847 97
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (10178 52
        (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (8123
   855
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (8084 52
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (6530 1707 (:REWRITE DEFAULT-+-2))
 (6375 1707 (:REWRITE DEFAULT-+-1))
 (6127 855
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (6033 789
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5653 270
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (5295 1681 (:REWRITE DEFAULT-UNARY-MINUS))
 (4276 313
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (4101 169 (:REWRITE FLD::|a * b = b * a|))
 (3712 267
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (3601 31
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (3601
  31
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (3337 85 (:REWRITE FUNPOL::|FLD::fdp (lc p)|))
 (3044 35
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (3044 35
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (2216 265
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (2166 265
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (2111 30
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2016 109 (:REWRITE FUNPOL::|- p != 0|))
 (1975 217
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1638 317
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1586 61 (:REWRITE DEFAULT-<-1))
 (1565 313
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1438 1438 (:REWRITE DEFAULT-CDR))
 (1119 1119 (:REWRITE DEFAULT-CAR))
 (1024 512
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (936 234
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (892 152
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (888 148
      (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (644 61 (:REWRITE DEFAULT-<-2))
 (626 626
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (626 626
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (531 52
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (511 86
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (468 26 (:REWRITE COMMUTATIVITY-OF-+))
 (444
    148
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (313 313
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (170 170
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (170 170
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (122 52
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (84
  21
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (69 8
     (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (52 52
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (23 23
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (23 23
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (13 13
     (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (8 8
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-22|
     (91 91
         (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-23|
 (993 47 (:DEFINITION FUPOL::POLINOMIOP))
 (832 7
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (612 33 (:DEFINITION FUPOL::*-MONOMIO))
 (560
   7
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (513 47
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (472 7
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (344 24
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (244 244 (:REWRITE DEFAULT-CDR))
 (219 43
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (209 209 (:REWRITE DEFAULT-CAR))
 (188 25
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (124
  8
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (123 42
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (123 23
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (111 1 (:DEFINITION FUPOL::+-MONOMIO))
 (96 8
     (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (88 88
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (88 88
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (82 40
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (77 39
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (46 6 (:REWRITE FUNPOL::|- p != 0|))
 (44 1
     (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-14|))
 (43 43
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (36 9
     (:REWRITE
          FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (24 24
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (22 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (8 8
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (6 1 (:DEFINITION FUMON::+))
 (5 5
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (5 1 (:REWRITE FLD::|a + b = b + a|))
 (2 2
    (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (2 1
    (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (1 1
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-24|
     (10 5 (:TYPE-PRESCRIPTION FLD::FDP-*)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-25|
 (4263 136
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (4127 274
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (3645
   136
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (3266 112
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2708
      4
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (2582 40 (:REWRITE FUNPOL::|0 + p = p|))
 (1844
  38
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1680 1398 (:REWRITE DEFAULT-CDR))
 (1654 142
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1610 274
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1597 14
       (:REWRITE FUNPOL::|p + (q + r) = q + (p + r)|))
 (1340 32
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1142 571 (:REWRITE DEFAULT-UNARY-MINUS))
 (1142 571 (:REWRITE DEFAULT-+-2))
 (1142 571 (:REWRITE DEFAULT-+-1))
 (1132 568
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1067 971 (:REWRITE DEFAULT-CAR))
 (1031 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (860 476
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (780
  30
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (760 32
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (704 32 (:REWRITE FUMON::TERMINO-MONOMIO))
 (630 126
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (630 126
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (620
    62
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (609 5 (:DEFINITION FUPOL::>-MONOMIO))
 (532 156 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (476 476
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (460 2 (:REWRITE FUNPOL::|p + 0 = p|))
 (442 442
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (410 4 (:REWRITE FUNPOL::|- p != 0|))
 (274 274
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (224 160
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (183 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (180 6
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (168 5
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (163 5
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (102 6 (:REWRITE FUPOL::|resto(m +M p) = p|))
 (100 1
      (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2a|))
 (84 12
     (:TYPE-PRESCRIPTION FUPOL::|m +M p != 0|))
 (64 4 (:REWRITE FUPOL::|mp(m +M p) = m|))
 (62 62 (:DEFINITION FUMON::-))
 (52 4 (:REWRITE FLD::|a + b = b + a|))
 (44 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (44 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (34 17 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (32 32
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (12 12
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO))
 (12 12 (:TYPE-PRESCRIPTION FUPOL::+M))
 (9 5
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (2 2
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (2 2
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-26|
 (4131 276
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (3996 137
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (3266 112
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2904
   137
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (2708
      4
      (:REWRITE
           FUNPOL::|coeficiente (primero p)) + coeficiente (primero q) = 0|))
 (2582 40 (:REWRITE FUNPOL::|0 + p = p|))
 (2179 3
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (1844
  38
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1690 1408 (:REWRITE DEFAULT-CDR))
 (1654 142
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (1620 276
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1597 14
       (:REWRITE FUNPOL::|p + (q + r) = q + (p + r)|))
 (1146 573 (:REWRITE DEFAULT-UNARY-MINUS))
 (1146 573 (:REWRITE DEFAULT-+-2))
 (1146 573 (:REWRITE DEFAULT-+-1))
 (1140 572
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1137 33
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (1075 979 (:REWRITE DEFAULT-CAR))
 (1031 7 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (864 480
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (780
  30
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (760 32
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (704 32 (:REWRITE FUMON::TERMINO-MONOMIO))
 (630 126
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (630 126
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (620
    62
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (609 5 (:DEFINITION FUPOL::>-MONOMIO))
 (532 156 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (480 480
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (460 2 (:REWRITE FUNPOL::|p + 0 = p|))
 (442 442
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (410 4 (:REWRITE FUNPOL::|- p != 0|))
 (276 276
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (271 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (271 1
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (271 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (271 1
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (224 160
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (183 15
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (180 6
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (168 5
      (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (163 5
      (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (102 6 (:REWRITE FUPOL::|resto(m +M p) = p|))
 (100 1
      (:REWRITE FUNPOL::|=-implies-=-FUPOL::+-monomio-2a|))
 (84 12
     (:TYPE-PRESCRIPTION FUPOL::|m +M p != 0|))
 (64 4 (:REWRITE FUPOL::|mp(m +M p) = m|))
 (62 62 (:DEFINITION FUMON::-))
 (52 4 (:REWRITE FLD::|a + b = b + a|))
 (44 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (44 4
     (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (34 17 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (32 32
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (28 2 (:REWRITE DEFAULT-<-1))
 (20 20
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (13 1
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-NULO))
 (12 12 (:TYPE-PRESCRIPTION FUPOL::+M))
 (7 3
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (4 2 (:REWRITE DEFAULT-<-2)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-27|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-28|
 (778 20
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (573 36 (:DEFINITION FUPOL::POLINOMIOP))
 (465
   20
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (423 20
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (195 39
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (194 43
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (183 183 (:REWRITE DEFAULT-CDR))
 (144 144 (:REWRITE DEFAULT-CAR))
 (132 66
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (120 39
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (102 12 (:REWRITE FUNPOL::|- p != 0|))
 (100 36
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (100 36
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (78 78
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (78 78
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (63 14
     (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (63
  14
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (61 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (39 39
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (24 6
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-29|
 (1463 18
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (741 37 (:DEFINITION FUPOL::POLINOMIOP))
 (399 63
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (290
   18
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (285 18
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (265 61 (:REWRITE FUNPOL::|- p != 0|))
 (190 38
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (182 182 (:REWRITE DEFAULT-CDR))
 (150 9
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (144 144 (:REWRITE DEFAULT-CAR))
 (136 68
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (133 21
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (133
  21
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (86 38
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (76 76
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (76 76
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (76 36
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (76 36
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (38 38
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (26 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (3 3
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-30|
 (9867 115
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (5123 309 (:DEFINITION FUPOL::POLINOMIOP))
 (3243
   115
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (2757 115
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (2735 20
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (2010 441
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (1660 332
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1564 1564 (:REWRITE DEFAULT-CDR))
 (1232 1232 (:REWRITE DEFAULT-CAR))
 (1136 568
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1038 149 (:REWRITE FUNPOL::|- p != 0|))
 (824 332
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (704 308
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (704 308
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (696 22 (:REWRITE FUNPOL::|- (- p) = p|))
 (670 147
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (670
  147
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (664 664
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (664 664
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (492 54
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (352 24
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (332 332
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-31|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-32|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-33|)
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-34|
 (759
   5
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (657 5
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (609 21
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (364
  7
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (333 57
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (287 218 (:REWRITE DEFAULT-CDR))
 (269 1
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (207 186 (:REWRITE DEFAULT-CAR))
 (206 57
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (192 96 (:REWRITE DEFAULT-UNARY-MINUS))
 (192 96 (:REWRITE DEFAULT-+-2))
 (192 96 (:REWRITE DEFAULT-+-1))
 (182
  7
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (180 96
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (154 28
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (154 7 (:REWRITE FUMON::TERMINO-MONOMIO))
 (132 4 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (124 62
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (119 35 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (104 104
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (96 96
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (80 35
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (77 77
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (66 2 (:DEFINITION FUPOL::>-MONOMIO))
 (57 57
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (49 35
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (14 14
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (14 14 (:DEFINITION FUMON::-))
 (14 6
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (8 8 (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (8 2
    (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (7 3
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (6 2
    (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-35|
 (897250 714 (:DEFINITION FUPOL::+-MONOMIO))
 (834172 22139 (:DEFINITION FUPOL::*-MONOMIO))
 (662177 17107 (:DEFINITION FUPOL::POLINOMIOP))
 (657549
   2104
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (650246 2847
         (:REWRITE FUNPOL::|resto -p = - resto p|))
 (536818 365
         (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (449023
    38863
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|))
 (426212 369
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (422270 365
         (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (417061 599
         (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (406700 16289 (:REWRITE FUMON::|a * b = b * a|))
 (387014 369
         (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (379738 33362
         (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (376985
  1497
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (365356 104
         (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (332894 714 (:DEFINITION FUMON::+))
 (330540 328 (:REWRITE FLD::|a + b = b + a|))
 (244442 598
         (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (152136 688
         (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (133335 23
         (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (118358 7811
         (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (117536 18 (:REWRITE FUNPOL::|- p != 0|))
 (112182 18835
         (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (83281 77764 (:REWRITE DEFAULT-CDR))
 (80372 906
        (:REWRITE FUTER::|a < b => ~(b < a)|))
 (74414 70655 (:REWRITE DEFAULT-CAR))
 (66547
  1594
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (64640 1416
        (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (62809 1416
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (58267 735
        (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (52683 8843
        (:REWRITE FUTER::|a < b or b < a or a = b|))
 (49934 1433 (:REWRITE FUMON::TERMINO-MONOMIO))
 (48376 23460 (:REWRITE DEFAULT-UNARY-MINUS))
 (48376 23460 (:REWRITE DEFAULT-+-1))
 (47317 23460 (:REWRITE DEFAULT-+-2))
 (44149 44149
        (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (36216 360
        (:REWRITE FUNPOL::|deg (- p) =e deg p|))
 (34836
    3479
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (33234 16617 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (32710 382
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (32710 382
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (31610 2976
        (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (26742 16434
        (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (25856 220 (:DEFINITION FUPOL::>-MONOMIO))
 (21738 4274
        (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (20562
    713
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|))
 (17887
    767
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (17850 3570
        (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (17590 3518
        (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (17098 17098
        (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (14195 4159 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (13874 13874
        (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (13141 1043 (:REWRITE DEFAULT-<-1))
 (12338 6638
        (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (9406 1082
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8843 8843
       (:REWRITE FUTER::|a < b & b < c => a < c|))
 (6415 3895 (:DEFINITION FUMON::-))
 (6205 4487
       (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (5519 1043 (:REWRITE DEFAULT-<-2))
 (5142 5142
       (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (4660 660
       (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (4058 97
       (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-4|))
 (4000 220
       (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (3841 299
       (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (3780 220
       (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (2900 508
       (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (2704 598
       (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (2657 97
       (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-14|))
 (1099 16
       (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-15|))
 (880 880
      (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (835 3
      (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-5|))
 (678 3
      (:REWRITE FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-17|))
 (657 599
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (371 371 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (311 311 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (140 140 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (129 129
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (105 35
      (:REWRITE FUPOL::ORDENADOP-+-MONOMIO-POLINOMIO-ORDENADO)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2-lemma-36|
 (4467 2 (:DEFINITION FUNPOL::QUOT))
 (1362 4
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (934 32
      (:REWRITE FUNPOL::|resto -p = - resto p|))
 (921 4
      (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (781 8
      (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (658 80
      (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (637 12
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (632
  13
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (583
   10
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (544 6
      (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (451 83
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (355 3
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (355 3
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (355 3
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (355 3
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (337 259 (:REWRITE DEFAULT-CDR))
 (335 8
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (333 146 (:REWRITE DEFAULT-+-1))
 (318 37
      (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (292 146 (:REWRITE DEFAULT-UNARY-MINUS))
 (292 146 (:REWRITE DEFAULT-+-2))
 (287 50
      (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (279 6
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (270
  12
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (259 226 (:REWRITE DEFAULT-CAR))
 (242 11 (:REWRITE FUMON::TERMINO-MONOMIO))
 (232 136
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (222 7 (:DEFINITION FUPOL::>-MONOMIO))
 (212 212
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (210
    21
    (:REWRITE FUNPOL::|primero(m FUPOL::*-monomio p2) FUMON::= primero(p1)|))
 (198 2
      (:REWRITE FUNPOL::|(a + b) = 0 => a +Mo (b +Mo p) = p-lemma-3|))
 (185 37
      (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (180 13
      (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (178 4
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (176 32
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (165 3 (:REWRITE FUNPOL::|- p != 0|))
 (145 43 (:TYPE-PRESCRIPTION FLD::FDP_-))
 (136 136
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (131 131
      (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (120 60
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (102 13
      (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (97 97
     (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (87 10
     (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (86 86
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (83 83
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (80 6 (:REWRITE DEFAULT-<-1))
 (77 17
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (60 2
     (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (59 43
     (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (46 21
     (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (39
    13
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (29 29
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (28 28
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (25 7
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (23 23 (:DEFINITION FUMON::-))
 (18 7
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (12 6 (:REWRITE DEFAULT-<-2))
 (11 5
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (2 2
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (2 2
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (1 1
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::REM)
(FUNPOL::POLINOMIOP-REM
 (15193 8 (:DEFINITION FUNPOL::QUOT))
 (14434 115 (:DEFINITION FUPOL::ORDENADOP))
 (11509 8 (:DEFINITION FUPOL::+-MONOMIO))
 (7932 246 (:DEFINITION FUPOL::POLINOMIOP))
 (7654 74
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (7489 501
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (6178 131
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (5445 298 (:DEFINITION FUPOL::*-MONOMIO))
 (5032 99
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (2945 40
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (2935 110
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (2808 8
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (2710 16
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2590 8 (:DEFINITION FUMON::+))
 (2532 2532 (:REWRITE DEFAULT-CAR))
 (2526 7 (:REWRITE FLD::|a + b = b + a|))
 (2319 255 (:REWRITE FUMON::|a * b = b * a|))
 (1775 1775 (:TYPE-PRESCRIPTION FUNPOL::=))
 (1731 74
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (1530 28
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (1160 83
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1152 214 (:DEFINITION FUMON::NULOP))
 (1025 1025 (:REWRITE DEFAULT-CDR))
 (857 74
      (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (799 106
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (758 37 (:REWRITE FUNPOL::|- p != 0|))
 (739 137
      (:REWRITE FUTER::|a < b or b < a or a = b|))
 (593 122 (:DEFINITION FUNPOL::DEG))
 (570
  10
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (567 189 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (538 99
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (538
   99
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (507 507
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (403 314 (:REWRITE DEFAULT-UNARY-MINUS))
 (403 314 (:REWRITE DEFAULT-+-1))
 (390 8
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (376 41
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (373 373
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (370 74
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (349 35
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (349 35
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (314 314 (:REWRITE DEFAULT-+-2))
 (301 301
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (301 301
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (284 284
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (266 8
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (265 265 (:TYPE-PRESCRIPTION FUTER::<))
 (250 90
      (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (228 12 (:REWRITE FUNPOL::|p + q = q + p|))
 (203 111
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (202 74
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (196 196
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (195 195 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (164 74
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (137 137
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (128 16 (:REWRITE FUMON::TERMINO-MONOMIO))
 (106 53 (:REWRITE DEFAULT-<-2))
 (106 53 (:REWRITE DEFAULT-<-1))
 (88 12 (:REWRITE FUNPOL::|nil + p = p|))
 (83 83 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (74 74
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (42 42
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (42 42
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (32 16 (:DEFINITION FUNPOL::LC))
 (18 18 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (12 12 (:REWRITE FUNPOL::|- nil =e nil|))
 (8 8 (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (2 2
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO)))
(FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|
 (79 8 (:DEFINITION FUPOL::POLINOMIOP))
 (50 10
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (49 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (42 1
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (42
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (39 3 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (37 37 (:REWRITE DEFAULT-CDR))
 (32 10
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (30 30 (:REWRITE DEFAULT-CAR))
 (20 20
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (20 20
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (20 10
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (20 7
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (16 6
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (12 1
     (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (10 10
     (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (4 2 (:DEFINITION FUNPOL::DEG))
 (3 2 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (3 1
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (3 1
    (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|
 (93
  1
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (84 8 (:DEFINITION FUPOL::POLINOMIOP))
 (49 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (45 9
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (42 1
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (42
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (36 36 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (26 2 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (25 9
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (24 12
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (24 12
     (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (18 18
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (18 18
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (18 7
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (14 6
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (9 9
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (3 1
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (3 1
    (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::|p1 = 0 => rem(p1 p2) = 0|
 (61
  1
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (20
   1
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (17 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (13 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (10 2
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (10 1
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (10
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (6 6
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 2
    (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4
    (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (4 4
    (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (4 4 (:TYPE-PRESCRIPTION FUTER::<))
 (4 2
    (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (4 2 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (4 2 (:DEFINITION FUNPOL::DEG))
 (4 1
    (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (3 1
    (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (2 2
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1 (:DEFINITION FUMON::NULOP))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (1 1 (:EQUIVALENCE FLD::EQUIVALENCE-LAW)))
(FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|
 (85 9 (:DEFINITION FUPOL::POLINOMIOP))
 (52
   1
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (49 1
     (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (47
  1
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (42 1
     (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (42
   1
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (40 8
     (:REWRITE FUTER::|a < b or b < a or a = b|))
 (36 36 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE DEFAULT-CAR))
 (24 12
     (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (21 8
     (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (16 16
     (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (16 16
     (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (16 7
     (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (16 7
     (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (13 1 (:REWRITE FUTER::|a < b => ~(b < a)|))
 (8 8 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (8 8
    (:REWRITE FUTER::|a < b & b < c => a < c|))
 (4 2 (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (4 2 (:DEFINITION FUNPOL::DEG))
 (3 1
    (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (1 1
    (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1)))
(FUNPOL::|deg rem(p1 p2) ACL2::< deg p2|
 (20116 46 (:DEFINITION FUNPOL::QUOT))
 (11548 123
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (10745 44
        (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (8975 92
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (7285 211 (:DEFINITION FUPOL::POLINOMIOP))
 (5946 72
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (5183 92
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (3545 92
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (3252 11
       (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (3149 46 (:REWRITE FUNPOL::|- p != 0|))
 (2186 308
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (2099 51
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (2091 111 (:REWRITE DEFAULT-<-1))
 (1982 24
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (1982
  24
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1935 149
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1563 281
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1464 308
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1268 403 (:REWRITE DEFAULT-+-1))
 (1247 211
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (1142 1142 (:REWRITE DEFAULT-CDR))
 (1041 149
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (1041 149
       (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (945 123
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (945
   123
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (887 887 (:REWRITE DEFAULT-CAR))
 (806 403 (:REWRITE DEFAULT-UNARY-MINUS))
 (806 403 (:REWRITE DEFAULT-+-2))
 (732 366
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (721 48
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (721 48
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (637 46
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (637 46
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (606 19 (:DEFINITION FUPOL::>-MONOMIO))
 (578 578
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (578 578
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (556 556
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (527 92
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (516 44
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (447
    149
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (308 308
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (254
  2
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (222 111 (:REWRITE DEFAULT-<-2))
 (165 33
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (136
   2
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (126 57
      (:REWRITE FUPOL::|m FUMON::> n and n >-monomio p => m >-monomio p|))
 (105
  21
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (102 92
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (84 2
     (:REWRITE FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|))
 (76 76
     (:TYPE-PRESCRIPTION FUPOL::>-MONOMIO))
 (69 19
     (:REWRITE FUPOL::|primero p FUMON::< m => >-monomio m p|))
 (50 19
     (:REWRITE FUPOL::|ordenadop p => (primero p) >-monomio (resto p)|))
 (44 44
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (32 32
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (11 11
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (11 11 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (8 8
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (6 2
    (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|)))
(FUNPOL::=-IMPLIES-=-REM-1
 (15248 2 (:DEFINITION FUNPOL::QUOT))
 (13551 235 (:DEFINITION FUPOL::ORDENADOP))
 (11482 2 (:DEFINITION FUPOL::+-MONOMIO))
 (8810 22
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (7880 283 (:DEFINITION FUPOL::POLINOMIOP))
 (6800 501
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (6108 230 (:DEFINITION FUPOL::*-MONOMIO))
 (5810 34
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (4144 14
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (3983 251
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (3060 56
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2906 2
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (2902 2 (:DEFINITION FUMON::+))
 (2886 218 (:REWRITE FUMON::|a * b = b * a|))
 (2884 2 (:REWRITE FLD::|a + b = b + a|))
 (2548 2548
       (:TYPE-PRESCRIPTION FUNPOL::BOOLEANP-POLINOMIOP))
 (2426 2426 (:REWRITE DEFAULT-CAR))
 (1612 106
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1548 345 (:DEFINITION FUMON::NULOP))
 (1474 1474 (:REWRITE DEFAULT-CDR))
 (1404 22
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (1345 253
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1140
  20
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1092 22
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (882 112
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (788 788
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (780 16
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (584 34
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (584
   34
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (568 14 (:REWRITE FUNPOL::|- p != 0|))
 (546 546
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (546 546
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (516 16
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (500 500 (:TYPE-PRESCRIPTION FUTER::<))
 (492 164 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (470 36 (:DEFINITION FUNPOL::DEG))
 (464 225
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (446 446
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (434 236
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (428 16
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (398 10
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (398 10
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (342 234 (:REWRITE DEFAULT-UNARY-MINUS))
 (342 234 (:REWRITE DEFAULT-+-1))
 (337 337 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (253 253
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (250 50
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (248 248
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (234 234 (:REWRITE DEFAULT-+-2))
 (232 22
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (206 4 (:REWRITE FUNPOL::|p + q = q + p|))
 (166 166
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (116 4 (:REWRITE FUNPOL::|nil + p = p|))
 (116 2
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (106 106 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (89
  2
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (89 2
     (:REWRITE FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|))
 (89
   2
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (76 28
     (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (50 22
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (32 16 (:REWRITE DEFAULT-<-2))
 (32 16 (:REWRITE DEFAULT-<-1))
 (32 4 (:REWRITE FUMON::TERMINO-MONOMIO))
 (28 28
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (14 14
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (14 14
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (12 12
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (8 4 (:DEFINITION FUNPOL::LC))
 (6 6 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (6 2
    (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (4 4 (:REWRITE FUNPOL::|- nil =e nil|)))
(FUNPOL::=-IMPLIES-=-REM-2
 (15248 2 (:DEFINITION FUNPOL::QUOT))
 (13416 232 (:DEFINITION FUPOL::ORDENADOP))
 (11482 2 (:DEFINITION FUPOL::+-MONOMIO))
 (8810 22
       (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (7838 280 (:DEFINITION FUPOL::POLINOMIOP))
 (6788 498
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (6108 230 (:DEFINITION FUPOL::*-MONOMIO))
 (5810 34
       (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (4144 14
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (3968 248
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (3060 56
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (2906 2
       (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (2902 2 (:DEFINITION FUMON::+))
 (2886 218 (:REWRITE FUMON::|a * b = b * a|))
 (2884 2 (:REWRITE FLD::|a + b = b + a|))
 (2506 2506
       (:TYPE-PRESCRIPTION FUNPOL::BOOLEANP-POLINOMIOP))
 (2414 2414 (:REWRITE DEFAULT-CAR))
 (1612 106
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1542 342 (:DEFINITION FUMON::NULOP))
 (1456 1456 (:REWRITE DEFAULT-CDR))
 (1404 22
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (1330 250
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1140
  20
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (1092 22
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (882 112
      (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (780 16
      (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (770 770
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (584 34
      (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (584
   34
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (568 14 (:REWRITE FUNPOL::|- p != 0|))
 (540 540
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (540 540
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (516 16
      (:REWRITE FUTER::|a < b => ~(b < a)|))
 (494 494 (:TYPE-PRESCRIPTION FUTER::<))
 (492 164 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (470 36 (:DEFINITION FUNPOL::DEG))
 (452 222
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (446 446
      (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (428 16
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (422 230
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (398 10
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (398 10
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (342 234 (:REWRITE DEFAULT-UNARY-MINUS))
 (342 234 (:REWRITE DEFAULT-+-1))
 (334 334 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (250 250
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (250 50
      (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (248 248
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (234 234 (:REWRITE DEFAULT-+-2))
 (232 22
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (206 4 (:REWRITE FUNPOL::|p + q = q + p|))
 (166 166
      (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (116 4 (:REWRITE FUNPOL::|nil + p = p|))
 (116 2
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (106 106 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (76 28
     (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (50 22
     (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (42
  2
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (42 2
     (:REWRITE FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|))
 (42
   2
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (41 1
     (:REWRITE FUNPOL::|p + r = q + r <=> p = q|))
 (32 16 (:REWRITE DEFAULT-<-2))
 (32 16 (:REWRITE DEFAULT-<-1))
 (32 4 (:REWRITE FUMON::TERMINO-MONOMIO))
 (28 28
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (14 14
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (14 14
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (12 12
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (8 4 (:DEFINITION FUNPOL::LC))
 (6 6 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (4 4 (:REWRITE FUNPOL::|- nil =e nil|))
 (4 2
    (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|)))
(FUNPOL::QUOT-REM-ELIM
 (29222 54 (:DEFINITION FUNPOL::QUOT))
 (19914 143
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (19197
   143
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (12034 108
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (11632 5276
        (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (10616 234 (:DEFINITION FUPOL::POLINOMIOP))
 (9996 90
       (:REWRITE FUNPOL::|resto -p = - resto p|))
 (9198 83
       (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (7156 108
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (4946 108
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (4774 682
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3332 30
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (3332
  30
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (3239 483 (:REWRITE DEFAULT-UNARY-MINUS))
 (3239 483 (:REWRITE DEFAULT-+-1))
 (2456 131 (:REWRITE DEFAULT-<-1))
 (2140 171
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (1902 302
       (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (1824 62
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1648 44 (:REWRITE FUNPOL::|- p != 0|))
 (1608 233
       (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (1510 302
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (1484 131 (:REWRITE DEFAULT-<-2))
 (1449 483 (:REWRITE DEFAULT-+-2))
 (1245 1245 (:REWRITE DEFAULT-CDR))
 (1114 171
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (1114 171
       (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (1082 108
       (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (953 953 (:REWRITE DEFAULT-CAR))
 (816 408
      (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (788 54
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (788 54
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (788 54
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (788 54
      (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (604 604
      (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (604 604
      (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (596 596
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-+))
 (513
    171
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (486 207
      (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (464 41
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (302 302
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (260 108
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (240 48
      (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (163 23
      (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (130
  26
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (126 126
      (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (93
  1
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (82
   1
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (54 54
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (54 54
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (42 1
     (:REWRITE FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|))
 (28 28
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (23 23
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*))
 (12 3
     (:REWRITE
          FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (7 7
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (4 4 (:TYPE-PRESCRIPTION FUNPOL::NULO))
 (3 1
    (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|)))
(FUNPOL::QUOT-REM-REWRITE
 (59936 6 (:DEFINITION FUNPOL::QUOT))
 (51430 706 (:DEFINITION FUPOL::ORDENADOP))
 (47364 98
        (:REWRITE FUNPOL::|p + q = mp(q) +Mo (p + (resto(q))|))
 (45406 6 (:DEFINITION FUPOL::+-MONOMIO))
 (33658 66
        (:REWRITE FUNPOL::|p1 = 0 => quot(p1 p2) =e 0|))
 (29270 826 (:DEFINITION FUPOL::POLINOMIOP))
 (21424 1434
        (:REWRITE FUNPOL::|FUMON::monomiop (primero p)|))
 (18742 644 (:DEFINITION FUPOL::*-MONOMIO))
 (18108 42
        (:REWRITE FUNPOL::|p + q = 0 <=> q = - p|))
 (16584 744
        (:REWRITE FUNPOL::|deg(p + q) ACL2::< deg(p)-lemma-5|))
 (15470 166
        (:REWRITE FUNPOL::|resto -p = - resto p|))
 (11432 5416
        (:TYPE-PRESCRIPTION FUNPOL::NATP-DEG))
 (10424 6 (:DEFINITION FUMON::+))
 (10408 6
        (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-2))
 (10388 6 (:REWRITE FLD::|a + b = b + a|))
 (7734 608 (:REWRITE FUMON::|a * b = b * a|))
 (6554 66
       (:REWRITE FUNPOL::|deg p1 < deq p2 => quot(p1 p2) =e 0|))
 (5776 286
       (:REWRITE FUPOL::|ordenadop p => ordenadop m *M p|))
 (5692
  60
  (:REWRITE
   FUNPOL::|FUMON::termino (primero (- p)) =e FUMON::termino FUMON::- (primero p)|))
 (5012 716
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4816 656 (:REWRITE DEFAULT-UNARY-MINUS))
 (4816 656 (:REWRITE DEFAULT-+-1))
 (4396 4396 (:REWRITE DEFAULT-CDR))
 (4160 66
       (:REWRITE FUNPOL::|~(polinomiop p1) => quot(p1 p2) =e 0|))
 (4086 46
       (:REWRITE FUNPOL::|primero -p FUMON::= FUMON::- primero p|))
 (3954 750
       (:REWRITE FUTER::|a < b or b < a or a = b|))
 (3624 3624 (:REWRITE DEFAULT-CAR))
 (3464 1004 (:DEFINITION FUMON::NULOP))
 (2516 2516
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP))
 (2282 298
       (:REWRITE FUNPOL::|not FUMON::nulop m|))
 (1968 656 (:REWRITE DEFAULT-+-2))
 (1950
    650
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-3|))
 (1778 286
       (:REWRITE FUNPOL::|polinomiop (m FUPOL::*-monomio p2)|))
 (1662 14 (:REWRITE FUNPOL::|- p != 0|))
 (1602 1602
       (:TYPE-PRESCRIPTION FUMON::TERMINOP-TERMINO))
 (1602 1602
       (:TYPE-PRESCRIPTION FUTER::BOOLEANP-TERMINOP))
 (1532 98
       (:REWRITE FUNPOL::|p + q = mp(p) +Mo (resto(p) + q)|))
 (1532
   98
   (:REWRITE FUNPOL::|p + q = mp(p) +Mo (mp(q) +Mo (resto(p) + (resto q)))|))
 (1512 304
       (:REWRITE FUMON::COEFICIENTE-MONOMIO))
 (1480 1480 (:TYPE-PRESCRIPTION FUTER::<))
 (1422 38
       (:REWRITE FUTER::|a < b => ~(b < a)|))
 (1410 688
       (:REWRITE FUNPOL::|not FUMON::nulop (primero p)|))
 (1400 748
       (:TYPE-PRESCRIPTION FUPOL::POLINOMIOP-RESTO))
 (1222 1222
       (:TYPE-PRESCRIPTION FLD::BOOLEANP-FDP))
 (1194 30
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(q)|))
 (1194 30
       (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)|))
 (1194 30
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)-a|))
 (1194 30
       (:LINEAR FUNPOL::|deg(p + q) ACL2::< deg(p)|))
 (1102 176
       (:REWRITE FUNPOL::|m FUPOL::*-monomio p2 != 0|))
 (1072 134
       (:TYPE-PRESCRIPTION FUMON::MONOMIOP-MONOMIO))
 (978 978 (:EQUIVALENCE FLD::EQUIVALENCE-LAW))
 (896 448 (:TYPE-PRESCRIPTION FLD::FDP-*))
 (894
    298
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-4|))
 (894 40 (:REWRITE DEFAULT-<-1))
 (750 750
      (:REWRITE FUTER::|a < b & b < c => a < c|))
 (630 12 (:REWRITE FUNPOL::|p + q = q + p|))
 (484 66
      (:REWRITE FUNPOL::|~(polinomiop p2) => quot(p1 p2) =e 0|))
 (418 14
      (:REWRITE FUNPOL::|- (m FUPOL::*-monomio p2) != 0|))
 (354 40 (:REWRITE DEFAULT-<-2))
 (348 12 (:REWRITE FUNPOL::|nil + p = p|))
 (342 6
      (:REWRITE FUMON::=-IMPLIES-EQUAL-TERMINO-1))
 (286 286 (:TYPE-PRESCRIPTION FUMON::NULOP))
 (230
  46
  (:REWRITE
      FUNPOL::|primero (- (m *-monomio p2)) = - (primero (m *-monomio p2))|))
 (196
  12
  (:REWRITE FUNPOL::|(polinomiop p1) & ~(polinomiop p2) => rem(p1 p2) = p1|))
 (174
   12
   (:REWRITE FUNPOL::|(polinomiop p1) & deg p1 < deq p2 => rem(p1 p2) = p1|))
 (142 66
      (:REWRITE FUNPOL::|p2 = 0 => quot(p1 p2) =e 0|))
 (94 12
     (:REWRITE FUNPOL::|(polinomiop p1) & p2 = 0 => rem(p1 p2) = 0|))
 (90 18
     (:REWRITE FUNPOL::|deg(p + q) =_e deg(p)-lema-4|))
 (82 2
     (:REWRITE FUNPOL::|p1 * p2 = 0 <=> p1 = 0 or p2 = 0|))
 (80 80
     (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP--))
 (60 12 (:REWRITE FUMON::TERMINO-MONOMIO))
 (42 42
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-2-LEMMA-1))
 (42 42
     (:REWRITE FUNPOL::=-IMPLIES-=-QUOT-1-LEMMA-1))
 (36
    12
    (:REWRITE FUNPOL::|deg (quot p1 p2) =e deg(p1) ACL2::- deg(p2)-lemma-5|))
 (24 6
     (:REWRITE
          FUNPOL::|primero (p1 * p2) =e (primero p1) FUMON::* (primero p2)|))
 (18 18 (:REWRITE FUNPOL::POLINOMIOP-QUOT))
 (16 16
     (:TYPE-PRESCRIPTION FUPOL::*-MONOMIO))
 (16 12
     (:REWRITE FUNPOL::|p1 = 0 => rem(p1 p2) = 0|))
 (12 12 (:REWRITE FUNPOL::|- nil =e nil|))
 (6 6
    (:TYPE-PRESCRIPTION FUMON::COEFICIENTEP-COEFICIENTE))
 (6 6 (:REWRITE FUNPOL::POLINOMIOP-REM))
 (4 4
    (:REWRITE FUPOL::POLINOMIOP-*-MONOMIO))
 (2 2
    (:TYPE-PRESCRIPTION FUNPOL::POLINOMIOP-*)))
