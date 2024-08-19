; DISABLE-TESTER: cpc
; DISABLE-TESTER: lfsc
; test name: testPullNull
;Translating sql query: SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 7 AND EMP.EMPNO = 10 AND EMP.MGR IS NULL AND EMP.EMPNO = 10
;Translating sql query: SELECT 10 AS EMPNO, EMP0.ENAME, EMP0.JOB, CAST(NULL AS INT) AS MGR, EMP0.HIREDATE, EMP0.SAL, EMP0.COMM, 7 AS DEPTNO, EMP0.SLACKER FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 7 AND EMP0.MGR IS NULL AND EMP0.EMPNO = 10
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)

(declare-const EMP (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const q1 (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const q2 (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const p2 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) Bool))
(declare-const p3 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) Bool))
(declare-const nullableOr (-> (Nullable Bool) (Nullable Bool) (Nullable Bool)))
(declare-const nullableAnd (-> (Nullable Bool) (Nullable Bool) (Nullable Bool)))
(declare-const f4 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(assert (= nullableAnd (lambda ((x (Nullable Bool)) (y (Nullable Bool))) (ite (and (nullable.is_null x) (= y (nullable.some false))) (nullable.some false) (ite (and (= x (nullable.some false)) (nullable.is_null y)) (nullable.some false) (ite (and (nullable.is_null x) (= y (nullable.some true))) (as nullable.null (Nullable Bool)) (ite (and (= x (nullable.some true)) (nullable.is_null y)) (as nullable.null (Nullable Bool)) (nullable.some (and (nullable.val x) (nullable.val y))))))))))
(assert (= nullableOr (lambda ((x (Nullable Bool)) (y (Nullable Bool))) (ite (and (nullable.is_null x) (= y (nullable.some true))) (nullable.some true) (ite (and (= x (nullable.some true)) (nullable.is_null y)) (nullable.some true) (ite (and (nullable.is_null x) (= y (nullable.some false))) (as nullable.null (Nullable Bool)) (ite (and (= x (nullable.some false)) (nullable.is_null y)) (as nullable.null (Nullable Bool)) (nullable.some (or (nullable.val x) (nullable.val y))))))))))
(assert (= p2 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (and (nullable.is_some (nullableAnd (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_975 Int) (BOUND_VARIABLE_976 Int)) (= BOUND_VARIABLE_975 BOUND_VARIABLE_976)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.lift (lambda ((BOUND_VARIABLE_982 Int) (BOUND_VARIABLE_983 Int)) (= BOUND_VARIABLE_982 BOUND_VARIABLE_983)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_991 Int) (BOUND_VARIABLE_992 Int)) (= BOUND_VARIABLE_991 BOUND_VARIABLE_992)) ((_ tuple.select 0) t) (nullable.some 10)))) (nullable.val (nullableAnd (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_975 Int) (BOUND_VARIABLE_976 Int)) (= BOUND_VARIABLE_975 BOUND_VARIABLE_976)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.lift (lambda ((BOUND_VARIABLE_982 Int) (BOUND_VARIABLE_983 Int)) (= BOUND_VARIABLE_982 BOUND_VARIABLE_983)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_991 Int) (BOUND_VARIABLE_992 Int)) (= BOUND_VARIABLE_991 BOUND_VARIABLE_992)) ((_ tuple.select 0) t) (nullable.some 10))))))))
(assert (= p3 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (and (nullable.is_some (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_1022 Int) (BOUND_VARIABLE_1023 Int)) (= BOUND_VARIABLE_1022 BOUND_VARIABLE_1023)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_1032 Int) (BOUND_VARIABLE_1033 Int)) (= BOUND_VARIABLE_1032 BOUND_VARIABLE_1033)) ((_ tuple.select 0) t) (nullable.some 10)))) (nullable.val (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_1022 Int) (BOUND_VARIABLE_1023 Int)) (= BOUND_VARIABLE_1022 BOUND_VARIABLE_1023)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_1032 Int) (BOUND_VARIABLE_1033 Int)) (= BOUND_VARIABLE_1032 BOUND_VARIABLE_1033)) ((_ tuple.select 0) t) (nullable.some 10))))))))
(assert (not (= q1 q2)))
(assert (= (nullable.val (as nullable.null (Nullable Bool))) false))
(assert (= f4 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (tuple (nullable.some 10) ((_ tuple.select 1) t) ((_ tuple.select 2) t) (as nullable.null (Nullable Int)) ((_ tuple.select 4) t) ((_ tuple.select 6) t) ((_ tuple.select 5) t) (nullable.some 7) ((_ tuple.select 8) t)))))
(assert (= q1 ((_ table.project 0 1 2 3 4 5 6 7 8) (bag.filter p2 EMP))))
(assert (= q2 (bag.map f4 (bag.filter p3 EMP))))
(check-sat)
