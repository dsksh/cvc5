; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))((cons (car tree) (cdr list)) (null))((node (children list)) (leaf (data nat)))))
(declare-fun x1 () nat)
(declare-fun x2 () nat)
(declare-fun x3 () nat)
(declare-fun x4 () nat)
(declare-fun x5 () nat)
(declare-fun x6 () list)
(declare-fun x7 () list)
(declare-fun x8 () list)
(declare-fun x9 () list)
(declare-fun x10 () list)
(declare-fun x11 () tree)
(declare-fun x12 () tree)
(declare-fun x13 () tree)
(declare-fun x14 () tree)
(declare-fun x15 () tree)
(check-sat-assuming ( (not (let ((_let_1 (leaf (ite ((_ is leaf) x13) (data x13) zero)))) (not (and (and ((_ is cons) (ite ((_ is node) _let_1) (children _let_1) null)) (= x15 (node x6))) (not ((_ is cons) x10)))))) ))
