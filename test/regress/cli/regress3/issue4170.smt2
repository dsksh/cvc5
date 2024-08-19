; COMMAND-LINE: -q
(set-logic HO_ALL)
(set-option :sygus-inference true)
(set-info :status sat)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Int)
(declare-fun d () Int)
(assert (distinct a (ite (= d 0) b c)))
(assert (= (a 0) 4))
(check-sat)
