; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (mkTuple 1 2)))
(declare-fun zt () (Tuple Int Int))
(assert (= zt (mkTuple 2 1)))
(declare-fun v () (Tuple Int Int))
(assert (= v (mkTuple 1 1)))
(declare-fun a () (Tuple Int Int))
(assert (= a (mkTuple 1 5)))
(assert (member (mkTuple 1 7) x))
(assert (member (mkTuple 7 5) y))
(assert (member z x))
(assert (member zt y))
(assert (not (member a (join x y))))
(check-sat)
