; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)
(set-option :sets-ext true)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun t () (Set (Tuple Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (mkTuple 1 2)))
(declare-fun zt () (Tuple Int Int))
(assert (= zt (mkTuple 2 1)))
(declare-fun v () (Tuple Int Int))
(assert (= v (mkTuple 1 1)))
(declare-fun a () (Tuple Int Int))
(assert (= a (mkTuple 1 5)))
(assert (member (mkTuple 1 7) x))
(assert (member z x))
(assert (member (mkTuple 7 5) y))
(assert (= t (join_image x 2)))
(assert (member (mkTuple 3) (join_image x 2)))
(assert (not (member (mkTuple 1) (join_image x 2))))
(assert (member (mkTuple 4) (join_image x 2)))
(assert (member (mkTuple 1) (join_image x 1)))
(check-sat)
