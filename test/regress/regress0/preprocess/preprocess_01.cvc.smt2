; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a0 () Bool)
(declare-fun a1 () Bool)
(declare-fun a2 () Bool)
(declare-fun a3 () Bool)
(declare-fun a4 () Bool)
(declare-fun a5 () Bool)
(declare-fun a6 () Bool)
(declare-fun a7 () Bool)
(declare-fun a8 () Bool)
(declare-fun a9 () Bool)
(assert a5)
(assert (not (or (or (or (or (or (or (or (or (or a0 a1) a2) a3) a4) a5) a6) a7) a8) a9)))
(check-sat)
