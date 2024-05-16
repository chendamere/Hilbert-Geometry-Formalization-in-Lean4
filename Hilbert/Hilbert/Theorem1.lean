import Hilbert.Axioms
import Hilbert.Lemmas

open hilbert


theorem Theorem1 (l1 l2: Line) (A B: Point):
  (l1≠l2) → (lies_on_L A l1) → (lies_on_L B l1) → (lies_on_L A l2) → (lies_on_L B l2) → A = B := by
  intro h1 h2 h3 h4 h5
  by_contra h'
  have k : l1=l2 := by
    apply unique_line_from_points h' h2 h3 h4 h5
  exact h1 k
