import Hilbert.Axioms
import Hilbert.Lemmas
open hilbert

#check PtOffLine

theorem Theorem3 (A C : Point): A ≠ C → ∃D : Point, between A D C := by

  intro nAC
  -- draw line AC
  cases' (line_exists nAC) with lAC AC_on_lAC
  have A_on_lAC: (lies_on_L A lAC ) := AC_on_lAC.left
  have C_on_lAC: (lies_on_L C lAC ) := AC_on_lAC.right

  --exists third distinct point from AC

  cases' (PtOffLine lAC) with E E_non_lAC
  have nAE: A ≠ E := by
    by_contra g
    have E_on_lAC : lies_on_L E lAC := by
     rw[g] at A_on_lAC
     apply A_on_lAC
    apply E_non_lAC E_on_lAC

  --draw line AE
  cases' (line_exists nAE) with lAE AE_on_lAE

  --extend line AE to F
  cases' between_extend nAE with F bet_AEF
  cases' between_line_exists bet_AEF with lAE2 F_on_lAEF
  have lAE2eqlae: lAE = lAE2 := by
    have t: lAE = line nAE := by
      apply same_line
      apply AE_on_lAE
    have t1: lAE2 = line nAE := by
      apply same_line
      constructor
      apply F_on_lAEF.left
      apply F_on_lAEF.right.left
    rw[t,t1]
  have colAEF : collinear A E F := by
    rw[collinear]
    use lAE
    constructor
    apply AE_on_lAE.left
    constructor
    apply AE_on_lAE.right
    rw[lAE2eqlae]
    apply F_on_lAEF.right.right

  -- F ≠ E
  have nFE : F ≠ E := by
    cases' between_distinct_points bet_AEF with nAE this
    rw [← @ne_comm]
    apply this.right

  -- F ≠ C
  have nCF: C ≠ F := by
    by_contra g
    have betAEC : between A E C := by
      rw[<-g] at bet_AEF
      exact bet_AEF
    have E_on_lAC: (lies_on_L E lAC) := by
      cases' between_line_exists betAEC with l h
      have laceql : l = line  nAC := by
        apply same_line
        constructor
        apply h.left
        apply h.right.right
      have laceqlac : lAC = line  nAC := by
        apply same_line
        apply AC_on_lAC
      rw [laceqlac, <-laceql]
      apply h.right.left
    exact E_non_lAC E_on_lAC

  --extend line CF to point G
  cases' between_extend nCF with G GC_on_lCF
  cases' between_line_exists GC_on_lCF with lFC FGC_on_lFC
  have colCFG : collinear C F G := by
    rw[collinear]
    use lFC

  have nFG: F ≠ G := by
    cases' between_distinct_points GC_on_lCF with nCF nCFG
    apply nCFG.right


  -- G ≠ E
  have nGE : G ≠ E := by
    by_contra g
    have C_on_lFCE : between C F E := by
     rw[g] at GC_on_lCF
     exact GC_on_lCF
    cases' between_line_exists (C_on_lFCE) with lFCE k
    cases' between_line_exists (bet_AEF) with lAFE kk
    have nFE : F ≠ E := by
      apply (between_distinct_points  (C_on_lFCE)).right.right
    have kkk: lAFE = line nFE := by
      apply same_line
      constructor
      apply kk.right.right
      apply kk.right.left
    have kkkk: lFCE = line nFE := by
      apply same_line
      constructor
      exact k.right.left
      exact k.right.right
    rw[<-kkk] at kkkk
    have ACeqlFCE : lFCE = line nAC := by
      apply same_line
      constructor
      rw [kkkk]
      exact kk.left
      exact k.left
    rw[ACeqlFCE] at k
    have ACeqlAC : lAC = line nAC := by
      apply same_line
      constructor
      apply A_on_lAC
      apply C_on_lAC
    rw[<-ACeqlAC] at k
    apply E_non_lAC k.right.right

  -- draw GE
  cases' line_exists nGE with lGE GE_on_lGE


  -- premises for pasche

  -- AFC not collinear
  have ncolAFC : ¬collinear A F C := by
    rw[collinear]
    push_neg
    intro lAF AinlAF FinlAF
    by_contra ng
    have EinlAC : lies_on_L E lAC := by
      cases' between_line_exists bet_AEF with lac2 lach
      have nAF : A ≠ F := by
        apply (between_distinct_points bet_AEF).right.left
      have samelinelac2lAF : lac2 = line nAF:= by
        apply (same_line)
        constructor
        apply lach.left
        apply lach.right.right
      have samelinelaclAF : lAF = line nAC := by
        apply (same_line)
        constructor
        apply AinlAF
        apply ng
      have samelinelAF : lAF = line nAF := by
        apply (same_line)
        constructor
        apply AinlAF
        apply FinlAF
      have samelinelaclac : lAC = lAF := by
        rw[samelinelaclAF]
        apply (same_line)
        apply AC_on_lAC
      have samelinelac2lac : lac2 = lAC := by
        rw[samelinelaclac, samelinelAF, samelinelac2lAF]
      rw[<-samelinelac2lac]
      exact lach.right.left
    apply E_non_lAC EinlAC

  -- lGE intersect A F
  have EintlAF: intersect_line_segment lGE A F:= by
    rw[intersect_line_segment]
    use E
    constructor
    by_contra ng
    apply ng GE_on_lGE.right
    constructor
    apply bet_AEF
    constructor
    · by_contra ng
      have colAGE : collinear A G E := by
        rw[collinear]
        use lGE
      have colAEG : collinear A E G := by
        apply col_perm1 A G E colAGE
      have colGAE : collinear G A E := by
        apply col_perm2
        apply col_perm1
        apply colAEG
      have colGAF : collinear G A F := by
        apply (col_trans colGAE colAEF nAE).left
      have colFGA : collinear F G A := by
        apply col_perm2
        apply col_perm1
        apply colGAF
      have colCFA : collinear C F A := by
        apply (col_trans colCFG colFGA nFG).left
      have colAFC : collinear A F C := by
        apply col_perm2
        apply col_perm1
        apply col_perm2
        apply colCFA
      apply ncolAFC colAFC
    · by_contra ng
      have colFGE : collinear F G E := by
        rw[collinear]
        use lGE
      have colCFE : collinear C F E := by
        apply (col_trans  colCFG colFGE nFG).left
      have colEFC : collinear E F C := by
        apply col_perm2
        apply col_perm1
        apply col_perm2
        apply colCFE
      have colAFC : collinear A F C := by
        rw [ne_comm] at nFE
        apply (col_trans colAEF colEFC nFE).right
      apply ncolAFC colAFC

  -- lGE does not intersect corner of triangle
  have CnlGE : ¬lies_on_L C lGE := by
    by_contra ng
    have colCGE : collinear C G E := by
      rw[collinear]
      use lGE
    have colFCG : collinear F C G := by
      apply col_perm2
      apply colCFG
    have colFEC : collinear F C E :=by
      have nCG : C ≠ G := by
        cases' between_distinct_points GC_on_lCF with nCF nCFG
        apply nCFG.left
      apply (col_trans colFCG colCGE nCG).left
    have colEFC : collinear E F C :=by
      apply col_perm2
      apply col_perm1
      apply colFEC
    have colAFC : collinear A F C :=by
      rw [ne_comm] at nFE
      apply (col_trans colAEF colEFC nFE).right
    apply ncolAFC colAFC

  -- lGE does not intersect lFC
  have nintFC :¬intersect_line_segment lGE F C := by
    rw[intersect_line_segment]
    push_neg
    intro D D_on_lGE betFDC F_non_lGE
    have colDGE : collinear D G E := by
      rw[collinear]
      use lGE
    have colFDC : collinear F D C := by
      rw[collinear]
      use lFC
      constructor
      apply FGC_on_lFC.right.left
      constructor
      cases' between_line_exists betFDC with lFDC FDC_on_lFDC
      have lFDCeqlCF : lFDC = line nCF :=by
        apply same_line
        constructor
        apply FDC_on_lFDC.right.right
        apply FDC_on_lFDC.left
      have lFCeqlCF : lFC = line nCF :=by
        apply same_line
        constructor
        apply FGC_on_lFC.left
        apply FGC_on_lFC.right.left
      rw[lFCeqlCF,<-lFDCeqlCF]
      apply FDC_on_lFDC.right.left
      apply FGC_on_lFC.left
    have colDCF : collinear D C F := by
      apply col_perm1
      apply col_perm2
      apply colFDC
    have colDCG : collinear D C G :=by
      apply (col_trans colDCF colCFG nCF).left
    have colCDG : collinear C D G :=by
      apply col_perm2
      apply colDCG
    have nDG : D ≠ G := by
      by_contra ng2
      have nbetCFD : ¬ between D F C := by
        apply (exist_unique_point_between betFDC).right
      have betGFC : between G F C := by
        apply between_sym
        apply GC_on_lCF
      rw[<-ng2] at betGFC
      apply nbetCFD betGFC
    have colCGE : collinear C G E :=by
      apply (col_trans colCDG colDGE nDG).right
    rw[collinear] at colCGE
    cases' colCGE with lGE2 h3
    have lGE2eqlGE : lGE2 = line nGE :=by
      apply same_line
      apply h3.right
    have lGEeqlGE : lGE = line nGE := by
      apply same_line
      apply GE_on_lGE
    rw[lGEeqlGE, <-lGE2eqlGE]
    apply h3.left

  -- apply Pasch
  rcases Pasch with pasch

  --simple logic
  have intACFC : intersect_line_segment lGE A C ∨ intersect_line_segment lGE F C := by
    apply pasch ncolAFC EintlAF CnlGE
  rw [@or_iff_not_imp_right] at intACFC
  have intGEAC : intersect_line_segment lGE A C := intACFC nintFC
  rw[ intersect_line_segment] at intGEAC
  cases' intGEAC with D h2
  use D
  apply h2.right.left
