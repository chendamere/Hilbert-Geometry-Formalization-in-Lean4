import Hilbert.Axioms
open hilbert

lemma lies_onh (y z:Point) (nyz : y ≠ z) : lies_on_L z (line nyz) := by
  have zonlyz : lies_on_L z (line nyz) := by
    cases' line_exists nyz with l lH
    have leqlyz : l = line nyz := by
      apply same_line
      apply lH
    rw[<-leqlyz]
    apply lH.right
  apply zonlyz


lemma lies_onh2 {y z:Point} (nyz : z ≠ y) : lies_on_L z (line nyz) := by
  have zonlyz : lies_on_L z (line nyz) := by
    cases' line_exists nyz with l lH
    have leqlyz : l = line nyz := by
      apply same_line
      apply lH
    rw[<-leqlyz]
    apply lH.left
  apply zonlyz

lemma point_exists : ∃ p : Point, p=p := by
  simp
  cases' non_collinear with a aH
  use a

lemma between_or (a b c : Point) : between a b c ∨ ¬ between a b c := by
  rw [@or_iff_not_imp_left]
  intro nab
  apply nab

lemma collinear_unique_points : ∃(A B C : Point), collinear A B C := by
  cases' non_collinear with X h
  cases' distinct_points X with Y nXY
  cases' between_extend nXY with Z betXYZ
  cases' between_line_exists betXYZ with l lXYZ
  use X
  use Y
  use Z
  rw [collinear]
  use (l)

lemma col_perm1 (A B C: Point) : (collinear A B C) → collinear A C B := by
  intro h
  rw [collinear]
  cases' h with l h
  use l
  constructor
  apply h.left
  constructor
  apply h.right.right
  apply h.right.left

lemma col_perm2 ( A B C: Point) :collinear A B C →  collinear B A C := by
  intro h
  rw [collinear]
  cases' h with l h
  use l
  constructor
  apply h.right.left
  rw[and_comm, and_assoc] at h
  rw[and_comm]
  apply h.right

lemma col_trans {A B C D : Point}(h1 : collinear A B C) (h2 : collinear B C D) (nBC : B ≠ C): collinear A B D ∧ collinear A C D:= by
  constructor
  · rw[collinear]
    cases' h1 with l1 h1
    cases' h2 with l2 h2
    use l1
    constructor
    apply h1.left
    constructor
    apply h1.right.left
    have l2eql1: l2 = line nBC :=by
      apply same_line
      constructor
      apply h2.left
      apply h2.right.left
    have l1eql1 : l1 = line nBC := by
      apply same_line
      apply h1.right
    rw[l1eql1, <-l2eql1]
    apply h2.right.right
  · rw[collinear]
    cases' h1 with l1 h1
    cases' h2 with l2 h2
    use l1
    constructor
    apply h1.left
    constructor
    apply h1.right.right
    have l2eql1: l2 = line nBC :=by
      apply same_line
      constructor
      apply h2.left
      apply h2.right.left
    have l1eql1 : l1 = line nBC := by
      apply same_line
      apply h1.right
    rw[l1eql1, <-l2eql1]
    apply h2.right.right


lemma PtOffLine(l: Line): ∃ D: Point, ¬(lies_on_L D l):= by
  cases' non_collinear with D g
  by_contra h
  push_neg at h
  cases' g with B g
  cases' g with C g
  have h1 : lies_on_L B l ∧ lies_on_L C l ∧ lies_on_L D l := by
    constructor
    apply h
    constructor
    apply h
    apply h
  rw[collinear] at g
  push_neg at g
  have ng : ¬lies_on_L C l :=by
    apply g.right.right.right
    apply h1.right.right
    apply h1.left
  apply ng h1.right.left

theorem unique_int {A B C D X : Point}
  (nAB :A ≠ B)  (nCD : C ≠ D ) (nDX: D ≠ X) (X_on_lAB: lies_on_L X (line nAB))
  (k1: lies_on_L X (line nCD)) (A_non_CD : ¬ lies_on_L A (line nCD))(k : lies_on_L B (line nCD)):
  B = X := by

  cases' line_exists nAB with lAB AB_on_lAB
  cases' line_exists nCD with lCD CD_on_lCD
  have lcdeqlcd: lCD = line nCD := by
    apply same_line
    apply CD_on_lCD
  have labeqlab : lAB = line nAB := by
    apply same_line
    apply AB_on_lAB

  by_contra g
  rw [← ne_eq] at g
  have colAXB : collinear A X B := by
    rw[collinear]
    use (line nAB)
    rw[<-labeqlab]
    rw[<-labeqlab] at X_on_lAB
    constructor
    apply AB_on_lAB.left
    constructor
    apply X_on_lAB
    apply AB_on_lAB.right
  have colDXB : collinear D X B :=by
    rw[collinear]
    use (line nCD)
    rw[<-lcdeqlcd]
    rw[<-lcdeqlcd] at k1
    constructor
    apply CD_on_lCD.right
    constructor
    apply k1
    rw[lcdeqlcd]
    apply k
  have colADX : collinear A D X := by
    have colXBD : collinear X B D := by
      apply col_perm1
      apply col_perm2
      apply colDXB
    have nXB : X ≠ B := by
      rw[ne_comm]
      apply g
    apply col_perm1
    apply (col_trans colAXB colXBD nXB).left
  have colXCD : collinear X C D := by
    rw[collinear]
    use lCD
    constructor
    rw[lcdeqlcd]
    apply k1
    apply CD_on_lCD
  have colADC : collinear A D C := by
    have colDXC : collinear D X C := by
      apply col_perm2
      apply col_perm1
      apply colXCD
    apply (col_trans colADX colDXC nDX).left
  have colACD : collinear A C D :=by
    apply col_perm1
    apply colADC
  rw[collinear] at colACD
  cases' colACD with lCD2 kh
  have lcdeqlcd2 : lCD2 = line nCD := by
    apply same_line
    apply kh.right
  rw[<-lcdeqlcd2] at A_non_CD
  apply A_non_CD kh.left


lemma unique_line_from_points {a b: Point} {l1 l2 : Line}:
  (nab: a ≠ b) → lies_on_L a l1 → lies_on_L b l1 → lies_on_L a l2 → lies_on_L b l2 →  l1 = l2 := by
  intros nab h hh hhh hhhh
  cases' line_exists nab with lab labH
  have gg : l1 = line nab := by
    apply same_line
    constructor
    apply h
    apply hh
  have ggg : l2 = line nab := by
    apply same_line
    constructor
    apply hhh
    apply hhhh
  rw[gg ,ggg]


lemma non_col_perm1 (A B C: Point) : ¬ collinear A B C → ¬ collinear C A B := by
  intro h
  rewrite[collinear]
  push_neg
  intros l lH lHH
  rewrite[collinear] at h
  push_neg at h
  intro hh
  apply h l
  apply lHH
  apply hh
  apply lH

lemma non_col_perm2 (A B C: Point) : ¬ collinear A B C → ¬ collinear A C B := by
  intro h
  rewrite[collinear]
  push_neg
  intros l lH lHH
  rewrite[collinear] at h
  push_neg at h
  intro hh
  apply h l
  apply lH
  apply hh
  apply lHH

lemma col_triv (a b : Point) (nab: a ≠ b) : collinear a a b := by
  unfold collinear
  use line nab
  constructor
  apply lies_onh2
  constructor
  apply lies_onh2
  apply lies_onh

lemma col_triv2 (a : Point) : collinear a a a := by
  unfold collinear
  cases' distinct_points a with b nab
  use line nab
  constructor
  apply lies_onh2
  constructor
  apply lies_onh2
  apply lies_onh2

lemma ncol_dist (a b c : Point) (ncol : ¬ collinear a b c ) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro aeqb
    apply ncol
    rw[aeqb]
    apply col_triv; intro beqc; apply ncol
    rw [aeqb, beqc]; apply col_triv2
  · constructor
    intro aeqc
    apply ncol
    rw[aeqc]
    apply col_perm1; apply col_triv; intro beqc; apply ncol
    rw [aeqc, beqc]; apply col_triv2
    intro aeqc
    apply ncol
    rw[aeqc]
    apply col_perm1; apply col_perm2; apply col_perm1; apply col_triv; intro beqc; apply ncol
    rw [aeqc, beqc]; apply col_triv2


lemma between_collinear {a b c : Point} :
  between a b c ->
  ( a ≠ b ∧  a ≠ c ∧ b ≠ c ∧ collinear a b c )
  := by
  intro betabc
  cases' between_distinct_points betabc with h hh
  unfold collinear
  constructor; apply h; constructor; apply hh.left; constructor;  apply hh.right
  apply between_line_exists betabc

lemma not_collinear_imp_not_between {a b c : Point} :
  ¬collinear a b c -> ¬ between a b c := by
  intro col
  intro bet
  unfold collinear at col
  cases' between_line_exists bet with l lH
  apply col
  use l


---- cong

lemma cong_reflex_weak (a b c d: Point) : cong a b c d → cong c d c d:= by
  intro congH
  apply (cong_transitive1 a b c d c d)
  apply congH
  apply congH

lemma cong_symm (a b c d: Point) : cong a b c d → cong c d a b:= by
  intro congH
  have congcd : cong c d c d := by
    apply cong_reflex_weak a b
    apply congH
  apply (cong_transitive2 c d c d a b)
  apply congcd
  apply congH

lemma cong_reflex (a b: Point)(nab : a ≠ b) : cong a b a b:= by
  rw [ne_comm] at nab
  have lh : lies_on_L a (line nab) := by
    apply (lies_onh b a nab)
  have nab2: a ≠ b := by rw [ne_comm] at nab; apply nab
  cases' cong_exist a b a (line nab) nab2 lh with c lH
  cases' lH with d lH2
  have congabac: cong a b a c := by
    apply lH2.right.right.right.left
  apply cong_symm at congabac
  apply cong_reflex_weak at congabac
  apply congabac

lemma cong_trans ( a b a' b' a'' b'' : Point) :
cong a b a' b' → cong a' b' a'' b'' → cong a b a'' b'' := by
  intros congab congab2
  apply cong_transitive2 a' b'
  apply cong_symm
  apply congab
  apply cong_symm
  apply congab2
