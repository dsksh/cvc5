; COMMAND-LINE: --print-arith-lit-token
(set-logic ALL)
(set-info :status sat)
(define-fun foo () (Array Int Int) ((as const (Array Int Int)) -1))
(assert (= (select foo 0) (- 1)))
(check-sat)
