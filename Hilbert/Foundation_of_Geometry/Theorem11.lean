

import Hilbert.Axioms
import Hilbert.Lemmas

open hilbert
--base angles of isosceles triangle are congruent

theorem Theorem11 (a b c : Point) :
  ¬ collinear a b c →
  cong b a c a →
  congA a b c a c b := by
  intros ncol2 congac'
  apply (@congA5 a b c a c b)
  apply ncol2
  apply non_col_perm2
  apply ncol2
  apply congac'
  apply cong_permute
  apply cong_symm
  apply cong_permute
  apply congac'
  apply non_col_perm1 at ncol2
  apply congA_perm2
  apply angle_comm c a b ncol2
