; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (Tuple Int Int))
(assert (= ((_ tupSel 0) x) 5))
(check-sat)
