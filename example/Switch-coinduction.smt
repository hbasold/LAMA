;; Implementation of Switch.lm by hand for exploration
;; Proves the 3 given properties using (0-)coinduction.
;; There are slight variants (commented) of those
;; properties which are incorrect. Those give the
;; expected counterexamples.

;; node Switch
(define-fun Switch_s_def ((on Bool) (off Bool) (s_1 Bool) (s Bool)) Bool
  (= s
     (ite s_1 (not off) on)))
(define-fun Switch_s_1_def ((s Bool) (s_1_next Bool)) Bool
  (= s_1_next
     s ))
(define-fun Switch_so_def ((so Bool) (s Bool)) Bool
  (= so
     s))

;; Global flow
(define-fun Switch_on_def ((Switch_on Bool) (on Bool)) Bool
  (= Switch_on
     on))
(define-fun Switch_off_def ((Switch_off Bool) (off Bool)) Bool
  (= Switch_off
     off))
(define-fun s_def ((Switch_so Bool) (s Bool)) Bool
  (= s
     Switch_so))
(define-fun s_1_def ((s_1_next Bool) (s Bool)) Bool
  (= s_1_next
     s))

;; properties
(define-fun prop1 ((off Bool) (on Bool) (s Bool)) Bool
;  (=> on s))
  (=> (and on (not off)) s))
(define-fun prop2 ((off Bool) (on Bool) (s Bool)) Bool
;  (=> off (not s)))
  (=> (and off (not on)) (not s)))
(define-fun prop3 ((off Bool) (on Bool) (s Bool) (s_1 Bool)) Bool
  (=> (and (not off) (not on)) (= s s_1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Prove that initial state fulfils property

(push)

;; declarations
(declare-fun Switch_on_0 () Bool)
(declare-fun Switch_off_0 () Bool)
(declare-fun Switch_so_0 () Bool)
(declare-fun Switch_s_0 () Bool)
(declare-fun Switch_s_1_0 () Bool)

(declare-fun on_0 () Bool)
(declare-fun off_0 () Bool)
(declare-fun s_0 () Bool)
(declare-fun s_1_0 () Bool)

(declare-fun Switch_s_1_1 () Bool)
(declare-fun s_1_1 () Bool)

;; initialisation
(assert (= Switch_s_1_0 false))
(assert (= s_1_0 false))

(assert (Switch_on_def Switch_on_0 on_0))
(assert (Switch_off_def Switch_off_0 off_0))

(assert (Switch_so_def Switch_so_0 Switch_s_0))
(assert (Switch_s_def Switch_on_0 Switch_off_0 Switch_s_1_0 Switch_s_0))
(assert (Switch_s_1_def Switch_s_0 Switch_s_1_1))

(assert (s_def s_0 Switch_so_0))
(assert (s_1_def s_1_1 s_0))

;(assert (not (prop1 off_0 on_0 s_0)))
(assert (not (prop2 off_0 on_0 s_0)))
;(assert (not (prop3 off_0 on_0 s_0 s_1_0)))

(check-sat)
(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Prove that property is an invariant

;; declarations
(declare-fun Switch_on () Bool)
(declare-fun Switch_off () Bool)
(declare-fun Switch_so () Bool)
(declare-fun Switch_s () Bool)
(declare-fun Switch_s_1 () Bool)

(declare-fun on () Bool)
(declare-fun off () Bool)
(declare-fun s () Bool)
(declare-fun s_1 () Bool)

(declare-fun Switch_s_1_n1 () Bool)
(declare-fun s_1_n1 () Bool)

(declare-fun Switch_on_n1 () Bool)
(declare-fun Switch_off_n1 () Bool)
(declare-fun Switch_so_n1 () Bool)
(declare-fun Switch_s_n1 () Bool)

(declare-fun on_n1 () Bool)
(declare-fun off_n1 () Bool)
(declare-fun s_n1 () Bool)

(declare-fun Switch_s_1_n2 () Bool)
(declare-fun s_1_n2 () Bool)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assume that we start in a state in which the invariant holds

;(assert (prop1 off on s))
(assert (prop2 off on s))
;(assert (prop3 off on s s_1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set up variables in starting state

(assert (Switch_on_def Switch_on on))
(assert (Switch_off_def Switch_off off))

(assert (Switch_so_def Switch_so Switch_s))
(assert (Switch_s_def Switch_on Switch_off Switch_s_1 Switch_s))
(assert (Switch_s_1_def Switch_s Switch_s_1_n1))

(assert (s_def s Switch_so))
(assert (s_1_def s_1_n1 s))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Make transition

(assert (Switch_on_def Switch_on_n1 on_n1))
(assert (Switch_off_def Switch_off_n1 off_n1))

(assert (Switch_so_def Switch_so_n1 Switch_s_n1))
(assert (Switch_s_def Switch_on_n1 Switch_off_n1 Switch_s_1_n1 Switch_s_n1))
(assert (Switch_s_1_def Switch_s_n1 Switch_s_1_n2))

(assert (s_def s_n1 Switch_so_n1))
(assert (s_1_def s_1_n2 s_n1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try to prove that property holds after transition
(push)
;(assert (not (prop1 off_n1 on_n1 s_n1)))
(assert (not (prop2 off_n1 on_n1 s_n1)))
;(assert (not (prop3 off_n1 on_n1 s_n1 s_1_n1)))

(check-sat)
(get-model)
(pop)