; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int Int)))
(declare-fun y () (Set (Tuple Int Int Int)))
(declare-fun z () (Tuple Int Int Int))
(assert (= z (mkTuple 1 2 3)))
(declare-fun zt () (Tuple Int Int Int))
(assert (= zt (mkTuple 3 2 1)))
(assert (member z x))
(assert (not (member zt (transpose x))))
(check-sat)
