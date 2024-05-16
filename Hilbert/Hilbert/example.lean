
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
#eval 1 + 1

#eval 1 + 1 = 2
#check forall n : Nat, n = n
#eval (fun n:Nat => n) 1

example : 1 + 1 = 2 := by
  simp


example (a : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

example (P : Prop) (ph : P): P ∧ P := by
  constructor
  apply ph
  apply ph

def factorial (n:Nat) :=
  match n with
  | 0   => 1
  | m+1 => (m+1) * factorial m
  #eval factorial 5

#eval factorial 3
example : factorial 3 = 6  := by
  unfold factorial
  unfold factorial
  unfold factorial
  unfold factorial
  simp


example (P : Prop) (p : P): P ∨ ¬ P := by
  constructor
  apply p

example (P Q: Prop) (p:P) (ph : P → Q): Q := by
  apply ph p

example (p q : Prop) (hp : p) (hnp : ¬p) : q := by
  absurd hnp
  apply hp

lemma lemma_ex (a b : Nat) : a ≤ a + b := by
  linarith

axiom false_axiom : ∃ A : Type, ∀ B : Type, A ≠ B
