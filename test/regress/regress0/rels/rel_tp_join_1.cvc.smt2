; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun b () (Tuple Int Int))
(assert (= b (mkTuple 1 7)))
(declare-fun c () (Tuple Int Int))
(assert (= c (mkTuple 2 3)))
(assert (member b x))
(assert (member c x))
(declare-fun d () (Tuple Int Int))
(assert (= d (mkTuple 7 3)))
(declare-fun e () (Tuple Int Int))
(assert (= e (mkTuple 4 7)))
(assert (member d y))
(assert (member e y))
(assert (member (mkTuple 3 4) z))
(declare-fun a () (Tuple Int Int))
(assert (= a (mkTuple 4 1)))
(assert (= r (join (join x y) z)))
(assert (not (member a (transpose r))))
(check-sat)
