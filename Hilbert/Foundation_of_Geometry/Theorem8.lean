
-- for any two points on a line there exists infinite number of points
-- another way to say this is for any two points A and B, there exists C between them,
-- and a function that takes A and B and C and returns the existence of another point between AB and between BC or between CA
import Hilbert.Axioms
import Hilbert.Lemmas
import Hilbert.Theorem3
open hilbert


-- Given a line that bisects the plane, for any point not on the line,
-- it determines a point on the plane such that if they are on the same side,
-- there exists a point of intersection between the segment formed from the two points
-- and the bisecting line, and if they are not on the same side, the line and segment
-- do not intersect.


axiom same_side : Point → Prop


--weaker definition of same/different side, it would be hard to prove two points are on the same side
--because parallel line does not intersect l. But this definition satisfies the theorem.
-- we would need some type of function that divides a plane in to two sides such that every point not
-- on the line lies in either point.

def points_same_side (l:Line)(a b: Point) := (∃c, between a b c ∧ lies_on_L c l ∧ ¬ lies_on_L b l ∧ ¬ lies_on_L a l)

theorem Theorem8_same_side (l:Line)(a b: Point): points_same_side l a b -> ¬ intersect_line_segment l a b := by
    intro H nint
    cases' H with c cH
    cases' nint with c' c'H
    cases' cH with left right
    cases' c'H with leftc' rightc'
    cases' rightc' with betac'b nlab
    cases' between_distinct_points left with nab nabcH
    cases' nabcH with nac nbc
    cases' between_line_exists left with labc labcH
    cases' between_line_exists betac'b with labc' labc'H
    have labceqlabc' : labc = labc' := by
      apply unique_line_from_points nab labcH.left labcH.right.left labc'H.left labc'H.right.right
    rw[ne_comm] at nbc
    have ncc' : c ≠ c' := by
      intro contra
      rw[contra] at left
      cases' exist_unique_point_between left with contra1 contra2
      apply contra1 betac'b
    have laceqlacc : labc' = line ncc' := by
      apply same_line
      constructor
      rw[<-labceqlabc']
      apply labcH.right.right
      apply labc'H.right.left
    have lcceqlacc : l = line ncc' := by
      apply same_line
      constructor
      apply right.left
      apply leftc'
    rw[lcceqlacc, <-laceqlacc] at nlab
    apply nlab.left labc'H.left


-- stronger definition
def strong_points_same_side (l:Line)(a b: Point) := ¬ lies_on_L b l ∧ ¬ lies_on_L a l ∧ (forall c: Point, lies_on_L c l → ¬ between a c b )
-- different side is exactly the cases when the line intersect the segmen
def points_different_side (l:Line)(a b: Point) := intersect_line_segment l a b

theorem strong_Theorem8_same_side (l:Line)(a b: Point): strong_points_same_side l a b -> ¬ points_different_side l a b := by
  intro H
  intro f
  unfold strong_points_same_side at H
  unfold points_different_side at f
  cases' f with c cH
  apply ((H.right.right c) cH.left) cH.right.left

theorem Theorem8_different_side (l:Line)(a b: Point): points_different_side l a b -> ¬ strong_points_same_side l a b := by
  intro h
  unfold points_different_side at h
  unfold strong_points_same_side
  push_neg
  unfold intersect_line_segment at h
  cases' h  with c cH
  intros
  use c
  constructor
  apply cH.left
  apply cH.right.left



-- not provable because the parallel case
-- theorem diff_diff_same (l: Line) (a b c: Point) : intersect_line_segment l a b → intersect_line_segment l a c → strong_points_same_side l b c := by
--   intros absame acsame

--   unfold strong_points_same_side
--   unfold intersect_line_segment at absame
--   unfold intersect_line_segment at acsame
--   cases' acsame with x xH
--   cases' absame with y yH
--   constructor
--   apply xH.right.right.right
--   constructor
--   apply yH.right.right.right

--   intros z zonl
--   intro contra
--   sorry
