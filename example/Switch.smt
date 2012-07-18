;; Implementation of Switch.lm by hand for exploration
;; Proves the 3 given properties using (0-)induction.
;; There are slight variants (commented) of those
;; properties which are incorrect. Those give the
;; expected counterexamples.

(declare-datatypes () ((Nat zero (succ (pred Nat)))))

;; node Switch
(declare-fun Switch_on (Nat) Bool)
(declare-fun Switch_off (Nat) Bool)
(declare-fun Switch_so (Nat) Bool)
(declare-fun Switch_s (Nat) Bool)
(declare-fun Switch_s_1 (Nat) Bool)

(define-fun Switch_s_def ((t Nat)) Bool
  (= (Switch_s t)
     (ite (Switch_s_1 t) (not (Switch_off t)) (Switch_on t))))
(define-fun Switch_s_1_def ((t Nat)) Bool
  (= (Switch_s_1 (succ t))
     (Switch_s t) ))
(define-fun Switch_so_def ((t Nat)) Bool
  (= (Switch_so t)
     (Switch_s t)))

;; initialisation
(assert (= (Switch_s_1 zero) false))

;; Global flow
;; declarations
(declare-fun on (Nat) Bool)
(declare-fun off (Nat) Bool)
(declare-fun s (Nat) Bool)
(declare-fun s_1 (Nat) Bool)

;; definitions
;; connect Switch
(define-fun Switch_on_def ((t Nat)) Bool
  (= (Switch_on t)
     (on t)))
(define-fun Switch_off_def ((t Nat)) Bool
  (= (Switch_off t)
     (off t)))
(define-fun s_def ((t Nat)) Bool
  (= (s t)
     (Switch_so t)))
;; rest
(define-fun s_1_def ((t Nat)) Bool
  (= (s_1 (succ t))
     (s t)))

;; intialisation
(assert (= (s_1 zero) false))

;; properties
(define-fun prop1 ((t Nat)) Bool
;  (=> (on t) (s t)))
  (=> (and (on t) (not (off t))) (s t)))
(define-fun prop2 ((t Nat)) Bool
;  (=> (off t) (not (s t))))
  (=> (and (off t) (not (on t))) (not (s t))))
(define-fun prop3 ((t Nat)) Bool
  (=> (and (not (off t)) (not (on t))) (= (s t ) (s_1 t))))

;; putting it all together
; (declare-fun n () Nat)

;; Induction base
(define-fun n0 () Nat zero)

(assert (Switch_on_def n0))
(assert (Switch_off_def n0))
(assert (Switch_so_def n0))
(assert (Switch_s_def n0))
(assert (Switch_s_1_def n0))

(assert (s_def n0))
(assert (s_1_def n0))

(push)
;(assert (not (prop1 n0)))
;(assert (not (prop2 n0)))
(assert (not (prop3 n0)))

(check-sat)
(get-model)
(pop)

;; Induction hypothesis
(declare-fun n () Nat)

(assert (Switch_on_def n))
(assert (Switch_off_def n))
(assert (Switch_so_def n))
(assert (Switch_s_def n))
(assert (Switch_s_1_def n))

(assert (s_def n))
(assert (s_1_def n))

;(assert (prop1 n))
;(assert (prop2 n))
(assert (prop3 n))

;; Induction step
(assert (Switch_on_def (succ n)))
(assert (Switch_off_def (succ n)))
(assert (Switch_so_def (succ n)))
(assert (Switch_s_def (succ n)))
(assert (Switch_s_1_def (succ n)))

(assert (s_def (succ n)))
(assert (s_1_def (succ n)))

(push)
;(assert (not (prop1 (succ n))))
;(assert (not (prop2 (succ n))))
(assert (not (prop3 (succ n))))

(check-sat)
(get-model)
(pop)