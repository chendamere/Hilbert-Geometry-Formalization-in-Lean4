import Hilbert.Axioms
import Hilbert.Lemmas
open hilbert



theorem Theorem4
  ( A B C  : Point)
  (nAB: A ≠ B) (nAC: A ≠ C) (nBC: B ≠ C)
  (colABC: collinear A B C ):
   (between A C B) ∨ (between A B C) ∨ (between B A C) := by

  rw [@or_iff_not_imp_left]
  rw [@or_iff_not_imp_right]
  intro nbetACB nbetBAC

  cases' line_exists nAC with lAC AC_on_lAC

  cases' (PtOffLine lAC) with D D_non_lAC

  have laceqlac: lAC = line nAC := by
    apply same_line
    apply AC_on_lAC

  have nBD: B ≠ D := by
    by_contra g
    rw[g] at colABC
    rw[collinear] at colABC
    cases' colABC with lac2 t
    have laceqlac2 : lac2 = line nAC := by
      apply same_line
      constructor
      apply t.left
      apply t.right.right
    rw [<-laceqlac2] at laceqlac
    rw[laceqlac] at D_non_lAC
    apply D_non_lAC t.right.left
  cases' between_extend nBD with G betBDG

  have colBDG : collinear B D G := by
    apply between_line_exists betBDG

  cases' between_distinct_points betBDG with nBD0 nBDG
  have nBG : B ≠ G := nBDG.left
  have nDG : D ≠ G := nBDG.right
  have nGC : G ≠ C := by
    by_contra g
    have colABG : collinear A B G := by
      rw[<-g] at colABC
      apply colABC
    have colBGD : collinear B G D := by
      apply col_perm1
      exact colBDG
    have colABD : collinear A B D := by
      apply (col_trans colABG colBGD nBG).left
    have colCAB : collinear C A B := by
      apply col_perm2
      apply col_perm1
      exact colABC
    have colACD : collinear A C D :=by
      apply (col_perm2 C A D (col_trans colCAB colABD nAB).left)
    rw[collinear] at colACD
    cases' colACD with lac2 t
    have laceqlac2 : lac2 = line nAC := by
      apply same_line
      constructor
      apply t.left
      apply t.right.left
    rw [<-laceqlac2] at laceqlac
    rw[laceqlac] at D_non_lAC
    apply D_non_lAC t.right.right
  have nAD : A ≠ D := by
    by_contra g
    rw[<-g] at D_non_lAC
    apply D_non_lAC AC_on_lAC.left

  cases' line_exists nAD with lAD AD_on_lAD


  -- premises for pasche BCG lAD
  have ncolBCG : ¬collinear B C G :=by
    by_contra g
    have colABG : collinear A B G :=by
      apply (col_trans colABC g nBC).left
    have colBGC : collinear B G C :=by
      apply col_perm1
      apply g
    have colDAC : collinear A G C :=by
      apply (col_trans colABG colBGC nBG).right
    have colBGD : collinear B G D := by
      apply col_perm1
      apply colBDG
    have colCBG : collinear C B G := by
      apply col_perm2
      apply g
    have colCGD: collinear C G D := by
      apply (col_trans colCBG colBGD nBG).right
    have colCDG : collinear G C D :=by
      apply col_perm2
      apply colCGD
    have colACD : collinear A C D :=by
      apply (col_trans colDAC colCDG nGC).right
    rw[collinear] at colACD
    cases' colACD with lac2 t
    have laceqlac2 : lac2 = line nAC := by
      apply same_line
      constructor
      apply t.left
      apply t.right.left
    rw [<-laceqlac2] at laceqlac
    rw[laceqlac] at D_non_lAC
    apply D_non_lAC t.right.right

  have ncolGBC : ¬ collinear G B C := by
    by_contra g
    have colBCG : collinear B C G := by
      apply col_perm1
      apply col_perm2
      apply g
    apply ncolBCG colBCG

  cases' between_extend nAD with E betADE
  have colADE : collinear A D E := by
    rw[collinear]
    use lAD
    constructor
    apply AD_on_lAD.left
    constructor
    apply AD_on_lAD.right
    cases' between_line_exists betADE with lAD2 temp
    have lADeqlAD2 : lAD2 = line nAD  := by
      apply same_line
      constructor
      apply temp.left
      apply temp.right.left
    have lADeqlAD : lAD = line nAD  := by
      apply same_line
      apply AD_on_lAD
    rw[lADeqlAD, <-lADeqlAD2]
    exact temp.right.right
  have ADeqAD: lAD = line nAD := by
    apply same_line
    apply AD_on_lAD
  have intADBC : intersect_line_segment (line nAD) G B := by
    rw[intersect_line_segment]
    use D
    constructor
    rw[<-ADeqAD]
    apply AD_on_lAD.right
    constructor
    apply between_sym betBDG
    constructor
    · by_contra g
      have colADG : collinear A D G := by
        rw[collinear]
        use lAD
        constructor
        apply AD_on_lAD.left
        constructor
        apply AD_on_lAD.right
        have lADeqlAD : lAD = line nAD := by
          apply same_line
          apply AD_on_lAD
        rw[lADeqlAD]
        apply g
      have colABG : collinear A B G := by
        have colDGB : collinear D G B := by
          apply col_perm1
          apply col_perm2
          apply colBDG
        apply col_perm1 A G B (col_trans colADG colDGB nDG).right
      have colBGC : collinear B G C := by
        have colGAB : collinear G A B := by
          apply col_perm2
          apply col_perm1
          apply colABG
        apply col_perm2 G B C (col_trans colGAB colABC nAB).right
      apply ncolBCG (col_perm1 B G C colBGC)
    · by_contra g
      have colADB : collinear A D B := by
        rw[collinear]
        use lAD
        constructor
        apply AD_on_lAD.left
        constructor
        apply AD_on_lAD.right
        have lADeqlAD : lAD = line nAD := by
          apply same_line
          apply AD_on_lAD
        rw[lADeqlAD]
        apply g
      have colBGC : collinear B G C := by
        have colDAB : collinear D A B := by
          apply col_perm2
          apply colADB
        have colCBD : collinear C B D := by
          apply col_perm1
          apply col_perm2
          apply col_perm1
          apply (col_trans colDAB colABC nAB).right
        apply col_perm1
        apply col_perm2
        apply (col_trans colCBD colBDG nBD).left
      apply ncolBCG (col_perm1 B G C colBGC)


  have CnonAD : ¬lies_on_L C (line nAD) := by
    by_contra g
    have colCAD : collinear C A D := by
      rw[collinear]
      use lAD
      have ladeqlad : lAD = line nAD := by
        apply same_line
        apply AD_on_lAD
      constructor
      rw[ladeqlad]
      apply g
      apply AD_on_lAD

    have colBAD : collinear B A D := by
      have nCA : C ≠ A := by
        rw [← @ne_comm] at nAC
        apply nAC
      have colBCA :  collinear B C A := by
        apply col_perm1
        apply col_perm2
        apply colABC
      apply (col_trans colBCA colCAD nCA).right
    have colADB : collinear A D B := by
      apply col_perm1
      apply col_perm2
      apply colBAD
    have colCBD : collinear C B D := by
      apply col_perm1 C D B (col_trans colCAD colADB nAD).right
    have colBGC : collinear B G C := by
      apply col_perm1
      apply col_perm2
      apply (col_trans colCBD colBDG nBD0).left
    apply ncolBCG (col_perm1 B G C colBGC)

  have intAD_GB_CB : intersect_line_segment (line nAD) G C ∨ intersect_line_segment (line nAD) B C := by
    apply Pasch ncolGBC intADBC CnonAD

  cases' between_distinct_points betADE with nAD3 nADE

  have not_intAD_CB : ¬ intersect_line_segment (line nAD) B C := by
    by_contra g
    rw[intersect_line_segment] at g
    push_neg
    cases' g  with X kk
    cases' between_distinct_points kk.right.left with nBX nBXC

    have colXAD : collinear X A D := by
      rw[collinear]
      use (line nAD)
      constructor
      apply kk.left
      have adeqad: lAD = line nAD:= by
        apply same_line
        apply AD_on_lAD
      rw [<-adeqad]
      apply AD_on_lAD

    cases' between_line_exists kk.right.left with lBX k

    have colBXC : collinear B X C := by
      rw[collinear]
      use lBX

    have colCXA : collinear C X A := by
      apply col_perm1
      apply col_perm2
      apply (col_trans colABC (col_perm1 B X C colBXC) nBC).right
    have colCDA : collinear C A D := by
      have nXA : X ≠ A := by
        by_contra g
        rw[<-g] at nbetBAC
        apply nbetBAC kk.right.left
      apply (col_trans colCXA colXAD nXA).right

    rw[collinear] at colCDA
    cases' colCDA with lAD2 temp

    have lADeqlAD2 : lAD2 = line nAD := by
      apply same_line
      apply temp.right

    rw[lADeqlAD2] at temp
    apply CnonAD temp.left

  have intAD_GC : intersect_line_segment (line nAD) G C := by
    rw [or_iff_not_imp_right] at intAD_GB_CB
    apply intAD_GB_CB not_intAD_CB

  have nGB: G ≠ B := by
    rw [← @ne_comm] at nBG
    apply nBG

  --lAE
  cases' colADE with lAE ADEonlAE
  cases' colBDG with lBG BDG
  have bgeqbg : lBG = line  nBG := by
    apply same_line
    constructor
    apply BDG.left
    apply BDG.right.right
  have colBDG : collinear B D G := by
    rw[ collinear ]
    use lBG

  have C_non_BG : ¬ lies_on_L C (line nBG) := by
    by_contra g
    have colBCG : collinear B C G := by
      rw[collinear]
      use line nBG
      rw[<-bgeqbg]
      constructor
      apply BDG.left
      constructor
      rw[bgeqbg]
      apply g
      apply BDG.right.right
    apply ncolBCG colBCG


  cases' intAD_GC with E Eh
  cases' between_line_exists Eh.right.left with lGC GEC_on_lGC

  have colGQC : collinear G E C := by
    rw[collinear]
    use lGC

  have colQAD : collinear D A E := by
    apply col_perm1
    apply col_perm2

    rw[collinear]
    use line nAD
    constructor
    apply Eh.left
    rw[<-ADeqAD]
    constructor
    apply AD_on_lAD.right
    apply AD_on_lAD.left

  have nAQ : A ≠ E := by
    by_contra AQ
    have colGAC : collinear G A C := by
      rw[collinear]
      use lGC
      rw[AQ]
      apply GEC_on_lGC
    have colACB : collinear A C B :=by
      apply col_perm1
      apply colABC
    have colGBC : collinear G B C := by
      apply col_perm1
      apply (col_trans colGAC colACB nAC).right
    apply ncolGBC colGBC

  have ncol_AQC : ¬ collinear A E C := by
    by_contra g
    have colDAC : collinear D A C := by
      apply (col_trans colQAD g nAQ ).left

    cases' colDAC with lAQ nh
    have adeqad : lAQ = line nAD := by
      apply same_line
      constructor
      apply nh.right.left
      apply nh.left
    rw[adeqad] at nh
    apply CnonAD nh.right.right

  have nCD : C ≠ D := by
    by_contra CeqD
    rw[CeqD] at ncolBCG
    apply ncolBCG colBDG

  cases' between_extend nCD with F' CDF'
  cases' between_line_exists CDF' with lCD lCDh

  have cdeqcd : lCD = line nCD := by
    apply same_line
    constructor
    apply lCDh.left
    apply lCDh.right.left
  have intCDGB : intersect_line_segment (line nCD) G B := by
    rw[intersect_line_segment]
    use D
    have DonCD : lies_on_L D (line nCD) := by
      rw[<-cdeqcd]
      apply lCDh.right.left
    have betGDB : between G D B := by
      apply between_sym
      apply betBDG

    have GnonCD: ¬ lies_on_L G (line nCD) := by
      by_contra ng
      have colGCD : collinear G D C:= by
        rw[collinear]
        use lCD
        constructor
        rw[cdeqcd]
        apply ng
        constructor
        apply lCDh.right.left
        apply lCDh.left

      have colBGD: collinear B G D := by
        apply col_perm1
        apply colBDG
      have nGD : G ≠ D := by
        rw[ne_comm] at nDG
        apply nDG
      have colBCG : collinear B C G := by
        apply col_perm1
        apply (col_trans colBGD colGCD nGD).left
      apply ncolBCG colBCG
    have BnonCD :  ¬lies_on_L B (line nCD) := by
      by_contra ng
      have colBCD : collinear B C D:= by
        apply col_perm1
        rw[collinear]
        use lCD
        constructor
        rw[cdeqcd]
        apply ng
        constructor
        apply lCDh.right.left
        apply lCDh.left
      have colBCG : collinear A C D := by
        apply (col_trans colABC colBCD nBC).right
      have ConlAD : lies_on_L C (line nAD) := by
        cases' colBCG with lAD ADh
        have adeqad: lAD = line nAD := by
          apply same_line
          constructor
          apply ADh.left
          apply ADh.right.right
        rw[<-adeqad]
        apply ADh.right.left
      apply CnonAD ConlAD
    constructor
    apply DonCD
    constructor
    apply betGDB
    constructor
    apply GnonCD
    apply BnonCD

  have ncolGBA : ¬ collinear G B A := by
    by_contra ng
    have colDGB : collinear D G B := by
      apply col_perm1
      apply col_perm2
      apply colBDG
    have colDGA : collinear D G A := by
      apply (col_trans colDGB ng nGB).left
    have GonAD : lies_on_L G (line nAD) := by
      cases' colDGA with lGA GAh
      have gaeqga : lGA = line nAD := by
        apply same_line
        constructor
        apply GAh.right.right
        apply GAh.left
      rw[<-gaeqga]
      apply GAh.right.left
    apply Eh.right.right.left GonAD



  have AnonCD : ¬ lies_on_L A (line nCD) := by
    by_contra ng
    have colACD : collinear A C D :=by
      rw[collinear]
      use lCD
      rw[<-cdeqcd] at ng
      constructor
      apply ng
      constructor
      apply lCDh.left
      apply lCDh.right.left

    have GonCD : lies_on_L C (line nAD) := by

      cases' colACD with lAC2 hhh
      have lac2eqlac : lAC2 = line nAD :=by
        apply same_line
        constructor
        apply hhh.left
        apply hhh.right.right
      rw[<-lac2eqlac]
      apply hhh.right.left
    apply Eh.right.right.right GonCD

  have intCD: intersect_line_segment (line nCD) G A ∨ intersect_line_segment (line nCD) B A := by
    apply Pasch ncolGBA intCDGB AnonCD
  have notintCDAB : ¬ intersect_line_segment (line nCD) B A := by
    by_contra g
    rw[intersect_line_segment] at g
    push_neg
    cases' g  with X kk
    cases' between_distinct_points kk.right.left with nBX nBXC

    have colXAD : collinear X C D := by
      rw[collinear]
      use (line nCD)
      constructor
      apply kk.left
      have cdeqcd : lCD = line nCD:= by
        apply same_line
        constructor
        apply lCDh.left
        apply lCDh.right.left
      rw [<-cdeqcd]
      constructor
      apply lCDh.left
      apply lCDh.right.left

    cases' between_line_exists kk.right.left with lBX k

    have colBXC : collinear X A B:= by
      apply col_perm1
      apply col_perm2
      rw[collinear]
      use lBX

    have colAXC : collinear A X C := by
      apply col_perm2
      apply (col_trans colBXC colABC nAB).left

    have colCDA : collinear C A D := by
      have nXC : X ≠ C := by
        by_contra XeqC
        rw[XeqC] at kk
        have betACB : between A C B := by
          apply between_sym
          apply kk.right.left
        apply nbetACB betACB
      apply col_perm2
      apply (col_trans colAXC colXAD nXC).right

    rw[collinear] at colCDA
    cases' colCDA with lAD2 temp

    have lADeqlAD2 : lAD2 = line nAD := by
      apply same_line
      apply temp.right

    rw[lADeqlAD2] at temp
    apply CnonAD temp.left

  have intCDGA : intersect_line_segment (line nCD) G A := by
    rw [@or_iff_not_imp_right] at intCD
    apply intCD notintCDAB
  cases' intCDGA with F Fh
  cases' between_distinct_points Fh.right.left with nGF nGFA
  cases' between_line_exists Fh.right.left with lFA lFAh
  have nFA : F ≠ A  :=by
    apply nGFA.right

  have colGFA: collinear G F A := by
    rw[collinear]
    use lFA

  have nCF : C ≠ F := by
    by_contra CeqF
    have colGCA: collinear G C A := by
      rw[<-CeqF] at colGFA
      apply colGFA
    have colCAB : collinear C A B :=by
      apply col_perm2
      apply col_perm1
      apply colABC
    have nCA : C ≠ A := by
      rw[ne_comm] at nAC
      apply nAC
    have colGBC :  collinear G B C := by
      apply col_perm1
      apply (col_trans colGCA colCAB nCA).left
    apply ncolGBC colGBC

  cases' between_distinct_points Eh.right.left with nGE nGCE

  have nGE : G ≠ E := by
    apply nGE

  have ncolGAE : ¬ collinear G A E := by
    by_contra colGAE
    have colAGE : collinear A G E :=by
      apply col_perm2
      apply colGAE
    have colAEC : collinear A E C := by
      apply (col_trans colAGE colGQC nGE).right
    apply ncol_AQC colAEC

  cases' line_exists nCF with lCF CFonlCF
  have cfeqcf : lCF = line nCF := by
    apply same_line
    apply CFonlCF

  have colFCD : collinear F C D := by
    rw[collinear]
    use lCD
    constructor
    rw[<-cdeqcd] at Fh
    apply Fh.left
    constructor
    apply lCDh.left
    apply lCDh.right.left

  have intCDGA : intersect_line_segment (line nCF) G A := by
    use F
    constructor
    rw[<-cfeqcf]

    ·
      apply CFonlCF.right
    constructor
    · apply Fh.right.left
    constructor
    · by_contra ng
      have colCGF : collinear C G F :=by
        apply col_perm2
        apply col_perm1
        rw[collinear]
        use line nCF
        constructor
        apply ng
        rw[<-cfeqcf]
        constructor
        apply CFonlCF.right
        apply CFonlCF.left
      have colCAG : collinear C A G := by
        apply col_perm1
        apply (col_trans colCGF colGFA nGF).left
      have colBCA : collinear B C A := by
        apply col_perm1
        apply col_perm2
        apply colABC
      have colGBA : collinear G B A := by
        have nCA : C ≠ A := by
          rw[ne_comm] at nAC
          apply nAC
        apply col_perm2
        apply col_perm1
        apply (col_trans colBCA colCAG nCA).right
      apply ncolGBA colGBA
    · by_contra ng
      have colAFC : collinear A F C :=by
        rw[collinear]
        use line nCF
        constructor
        apply ng
        rw[<-cfeqcf]
        constructor
        apply CFonlCF.right
        apply CFonlCF.left
      have nFC : F ≠ C := by
        rw[ne_comm] at nCF
        apply nCF
      have colCAG : collinear C A D := by
        apply col_perm2
        apply (col_trans colAFC colFCD nFC).right
      cases' colCAG with lAD2 nh
      have adeqad2 : lAD2 = line nAD :=by
        apply same_line
        constructor
        apply nh.right.left
        apply nh.right.right
      rw[adeqad2] at nh
      apply CnonAD nh.left


  have EnonCF : ¬lies_on_L E (line nCF) := by
    by_contra EonCF
    have colEFC : collinear E F C := by
      apply col_perm2
      rw[collinear]
      use lCF
      constructor
      apply CFonlCF.right
      constructor
      rw[<-cfeqcf] at EonCF
      apply EonCF
      apply CFonlCF.left
    have nFC : F ≠ C  := by
      rw[ne_comm] at nCF
      apply nCF
    have colCED : collinear C E D := by
      apply col_perm2
      apply (col_trans colEFC colFCD nFC).right
    have colEDA : collinear E D A := by
      apply col_perm2
      apply col_perm1
      apply colQAD
    have nED : E ≠ D := by
      by_contra EeqD
      have colDFC : collinear D F C := by
        rw[EeqD] at colEFC
        apply colEFC
      have colECF : collinear E C F:= by
        apply col_perm1
        apply colEFC
      have colFCG : collinear F C G := by
        apply col_perm1
        apply col_perm2
        apply col_perm1
        apply (col_trans colGQC colECF nGCE.right).right
      have colGCD : collinear D C G := by
        apply (col_trans colDFC colFCG nFC).right
      cases' colGCD with lCD CDH
      have lcdeqlcd : lCD = line nCD := by
        apply same_line
        constructor
        apply CDH.right.left
        apply CDH.left
      rw[<-lcdeqlcd] at Fh
      apply Fh.right.right.left CDH.right.right

    have CDA : collinear C D A := by
      apply (col_trans colCED colEDA nED).right
    cases' CDA with lCD CDH
    have lcdeqlcd : lCD = line nCD := by
      apply same_line
      constructor
      apply CDH.left
      apply CDH.right.left

    rw[lcdeqlcd] at CDH
    apply Fh.right.right.right CDH.right.right

  have nintCFGE : ¬ intersect_line_segment (line nCF) G E := by
    by_contra ng
    cases' ng with X Xh
    rw[<-cfeqcf] at Xh
    cases' between_line_exists Xh.right.left with lXG XGH
    cases' between_distinct_points Xh.right.left with Xleft Xright
    have nEX : E ≠ X := by
      rw[ne_comm]
      apply Xright.right
    have nFC : F ≠ C := by
      rw[ne_comm]
      apply nCF
    have fceqfc : lCF = line nFC := by
      apply same_line
      constructor
      apply CFonlCF.right
      apply CFonlCF.left
    have XonFC : lies_on_L X (line nFC) := by
      rw[<-fceqfc]
      apply Xh.left
    have XonGE : lies_on_L X (line nGE) := by
      have xgeqge : lXG = line nGE := by
        apply same_line
        constructor
        apply XGH.left
        apply XGH.right.right
      rw[<-xgeqge]
      apply XGH.right.left
    have FnonGE : ¬ lies_on_L F (line nGE) := by
      by_contra FonGE
      have xgeqge : lGC = line nGE := by
        apply same_line
        constructor
        apply GEC_on_lGC.left
        apply GEC_on_lGC.right.left
      rw[<-xgeqge] at FonGE
      have FGC : collinear G F C := by
        rw[collinear]
        use lGC
        constructor
        apply GEC_on_lGC.left
        constructor
        apply FonGE
        apply GEC_on_lGC.right.right

      have GCD : collinear D G C := by
        apply col_perm2
        apply col_perm1
        apply (col_trans FGC colFCD nFC).right
      have BCG : collinear B C G := by
        apply col_perm1
        apply (col_trans colBDG GCD nDG).right
      apply ncolBCG BCG

    have ConGE : lies_on_L C (line nGE) := by
      cases' colGQC with lCG2 CGH
      have cg2eqcg : lCG2 = line (Xright.left) := by
        apply same_line
        constructor
        apply CGH.left
        apply CGH.right.left
      rw[<-cg2eqcg]
      apply CGH.right.right

    have GeqX : C = X := by
      apply unique_int nFC nGE nEX XonFC XonGE FnonGE ConGE

    rw[<-GeqX] at Xh
    cases' exist_unique_point_between Xh.right.left with nbetleft nbetright
    apply nbetleft Eh.right.left

  have intAE: intersect_line_segment (line nCF) G E ∨ intersect_line_segment (line nCF) A E := by
    apply Pasch  ncolGAE intCDGA EnonCF
  have intCFAE : intersect_line_segment (line nCF) A E := by
    rw [@or_iff_not_imp_left] at intAE
    apply intAE nintCFGE


  cases' intCFAE with D' D'h
  have nAF : A ≠ F := by
    rw[ne_comm] at nFA
    apply nFA
  have nFD' : F ≠ D' := by
    by_contra FeqD'
    rw[<-FeqD'] at D'h

    cases' between_line_exists D'h.right.left with lAF AFH

    have colAFE : collinear A F E := by
      rw[collinear]
      use lAF

    have colGAE : collinear G A E := by
      have colGAF : collinear G A F :=by
        apply col_perm1
        apply colGFA
      apply (col_trans  colGAF colAFE nAF).left
    apply ncolGAE colGAE
  have DonFD' : lies_on_L D (line nFD') := by
    have D'CF : collinear D' C F := by
      rw[collinear]
      use line nCF
      constructor
      apply D'h.left
      rw[<-cfeqcf]
      apply CFonlCF
    have CFD : collinear C F D := by
      apply col_perm2
      apply colFCD
    have D'FD: collinear D' F D :=by
      apply (col_trans D'CF CFD nCF).right
    cases' D'FD with lFD FDH
    have fdeqfd : lFD = line nFD' := by
      apply same_line
      constructor
      apply FDH.right.left
      apply FDH.left
    rw[<-fdeqfd]
    apply FDH.right.right

  have nEA : E ≠ A := by
    by_contra EeqA
    cases' between_distinct_points D'h.right.left with left right
    rw[eq_comm] at EeqA
    apply right.left EeqA

  cases' colQAD with lEA DEAH
  have eaeqea : lEA = line nEA := by
    apply same_line
    constructor
    apply DEAH.right.right
    apply DEAH.right.left
  have DonEA : lies_on_L D (line nEA) :=by
    rw[<-eaeqea]
    apply DEAH.left
  have FnonEA : ¬ lies_on_L F (line nEA) := by
    by_contra FEA
    have colFAD : collinear F A D := by
      rw[collinear]
      use lEA
      constructor
      rw[eaeqea]
      apply FEA
      constructor
      apply DEAH.right.left
      apply DEAH.left
    have colGAD : collinear G A D := by
      apply (col_trans colGFA colFAD nFA).right
    have GonAD : lies_on_L G (line nAD) :=by
      cases' colGAD with lAD2 AD2H
      have ad2eqad : lAD2 = line nAD := by
        apply same_line
        constructor
        apply AD2H.right.left
        apply AD2H.right.right
      rw[<-ad2eqad]
      apply AD2H.left
    apply Eh.right.right.left GonAD
  have D'onEA : lies_on_L D' (line nEA) := by
    cases' between_line_exists D'h.right.left with lEA2 EA2H
    have ea2eqea : lEA2 = line nEA := by
      apply same_line
      constructor
      apply EA2H.right.right
      apply EA2H.left
    rw[<-ea2eqea]
    apply EA2H.right.left
  have D'eqD : D' = D  := by
    cases' unique_int nFD' nEA nAD DonFD' DonEA FnonEA D'onEA
    simp

  have betADE : between A D E := by
    rw[D'eqD] at D'h
    apply D'h.right.left

  have intBGAQ : intersect_line_segment (line nBG) A E := by
    rw[intersect_line_segment]
    use D
    constructor
    · rw[<-bgeqbg]
      apply BDG.right.left
    constructor
    · apply betADE
    constructor
    · by_contra BonG
      have colABG : collinear A B G := by
        rw[collinear]
        use lBG
        constructor
        rw[<-bgeqbg] at BonG
        apply BonG
        constructor
        apply BDG.left
        apply BDG.right.right
      have colCAB : collinear C A B := by
        apply col_perm2
        apply col_perm1
        apply colABC
      have colBCG : collinear B C G := by
        apply col_perm2
        apply (col_trans colCAB colABG nAB).right
      apply ncolBCG colBCG
    · by_contra EonBG
      rw[<-bgeqbg] at EonBG
      have colBGE : collinear B G E := by
        apply col_perm2
        rw[collinear]
        use lBG
        constructor
        apply BDG.right.right
        constructor
        apply BDG.left
        apply EonBG

      have colBCG : collinear B C G := by
        apply col_perm1
        apply (col_trans colBGE colGQC nGE).left
      apply ncolBCG colBCG

  have kg : ¬ intersect_line_segment (line nBG) E C → intersect_line_segment (line nBG) A C:= by
    rw [<- or_iff_not_imp_right]
    apply Pasch ncol_AQC intBGAQ C_non_BG

  have not_intAD_CB : ¬ intersect_line_segment (line  nBG) E C := by
    by_contra g
    rw[intersect_line_segment] at g
    push_neg
    cases' g  with X kk

    have nCE : C ≠ E :=by
      rw[ne_comm]
      cases' between_distinct_points kk.right.left with nEX nEXC
      apply nEXC.left
    cases' between_line_exists kk.right.left with lCE CEH
    have ceeqce : lCE = line nCE := by
      apply same_line
      constructor
      apply CEH.right.right
      apply CEH.left
    have XonBG : lies_on_L X (line nBG) := by
      apply kk.left
    have XonCE : lies_on_L X (line nCE) := by

      rw[<-ceeqce]
      apply CEH.right.left
    have BnonCE: ¬ lies_on_L B (line nCE) := by
      rw[<-ceeqce]
      by_contra GonCE
      have colBCE : collinear B C E := by
        rw[ collinear ]
        use lCE
        constructor
        apply GonCE
        constructor
        apply CEH.right.right
        apply CEH.left
      have colCEG : collinear C E G := by
        apply col_perm1
        apply col_perm2
        apply col_perm1
        apply colGQC
      have BCG : collinear B C G :=by
        apply (col_trans colBCE colCEG nCE).left
      apply ncolBCG BCG

    have GonCE: lies_on_L G (line nCE) := by
      cases' colGQC with lCE2 CH
      have ceeqce2 : lCE2 = line nCE := by
        apply same_line
        constructor
        apply CH.right.right
        apply CH.right.left
      rw[<-ceeqce2]
      apply CH.left
    cases' between_distinct_points kk.right.left with nEX nEXC
    have GeqX : G = X := by
      apply unique_int nBG nCE nEX XonBG XonCE BnonCE GonCE
    rw[<-GeqX] at kk
    cases' exist_unique_point_between kk.right.left with nbetleft nbetright
    apply nbetright Eh.right.left

  have fin : intersect_line_segment (line nBG) A C:= by
    apply kg not_intAD_CB

  cases' fin with X finh
  have nCX : C ≠ X := by
    by_contra g
    cases' between_distinct_points finh.right.left with ng ngg
    rw[<-g] at ng
    rw[eq_comm] at g
    apply ngg.right g

  have XonGB : lies_on_L X (line nGB) := by
    cases' line_exists nGB with lGB GBonlGB
    have gbeqgb : lGB = line nGB := by
      apply same_line
      apply GBonlGB
    rw [<-gbeqgb]
    have bgeqbg : lGB = line nBG := by
      apply same_line
      constructor
      apply GBonlGB.right
      apply GBonlGB.left
    rw[bgeqbg]
    apply finh.left
  have XonAC : lies_on_L X (line nAC) := by
    cases' between_line_exists finh.right.left with lAC2 AXConlAC2
    have laceqlac2 : lAC2 = line nAC := by
      apply same_line
      constructor
      apply AXConlAC2.left
      apply AXConlAC2.right.right
    rw[<-laceqlac2]
    apply AXConlAC2.right.left

  have GnonAC : ¬lies_on_L G (line nAC) := by
    by_contra g
    have colACX : collinear A C X := by
      rw[collinear]
      use lAC
      constructor
      apply AC_on_lAC.left
      constructor
      apply AC_on_lAC.right
      rw[laceqlac]
      apply XonAC
    have colGAC : collinear G A C := by
      rw[collinear]
      use line nAC
      constructor
      apply g
      rw[<-laceqlac]
      constructor
      apply AC_on_lAC.left
      apply AC_on_lAC.right
    have colGAX: collinear G A X := by
      apply (col_trans colGAC colACX nAC).left
    have colXGB : collinear X G B := by
      rw[collinear]
      use line nGB
      constructor
      apply XonGB
      cases' colBDG with lGB BGDonlGB
      have gbeqgb : lGB = line nGB := by
        apply same_line
        constructor
        apply BGDonlGB.right.right
        apply BGDonlGB.left
      rw[<-gbeqgb]
      constructor
      apply BGDonlGB.right.right
      apply BGDonlGB.left
    have colAXG : collinear A X G :=by
      apply col_perm1
      apply col_perm2
      apply colGAX

    have nXG : X ≠ G :=by
      by_contra XeqG
      have colACG : collinear A C G := by
        rw[XeqG]at colACX
        apply colACX
      have colBAC : collinear B A C :=by
        apply col_perm2
        apply colABC
      have colBCG : collinear B C G :=by
        apply (col_trans colBAC colACG nAC).right
      apply ncolBCG colBCG
    have colAGB : collinear A G B := by
      apply (col_trans colAXG colXGB nXG).right
    have colGAB : collinear G A B := by
      apply col_perm2
      apply colAGB
    have colGBC : collinear G B C :=by
      apply (col_trans colGAB colABC nAB).right
    apply ncolGBC colGBC

  have BonAC : lies_on_L B (line nAC) := by
    cases' colABC with lAC2 h
    rw[<-laceqlac]
    have laceqlac2 : lAC2 = line nAC := by
      apply same_line
      constructor
      apply h.left
      apply h.right.right
    rw[laceqlac, <-laceqlac2]
    apply h.right.left

  have BeqX : B = X := by
    cases' unique_int nGB nAC nCX XonGB XonAC GnonAC BonAC with h
    simp


  rw[BeqX]
  apply finh.right.left


lemma nbet_imp (a b c : Point )(nab:a≠ b)(nac:a≠ c)(nbc:b≠ c)(colabc:collinear a b c) : ¬ between a b c → between a c b ∨ between c a b := by
  rw [<- @or_iff_not_imp_left]
  apply Theorem4 a c b
  apply nac
  apply nab
  rw[ne_comm]
  apply nbc
  apply col_perm1
  apply colabc

lemma nbet_imp2 (a b c : Point )(nab:a≠ b)(nac:a≠ c)(nbc:b≠ c)(colabc:collinear a b c) : ¬ between a b c → ¬ between a c b → between c a b := by
  rw [<- @or_iff_not_imp_left]
  rw [<- @or_iff_not_imp_left]
  apply Theorem4 a c b
  apply nac
  apply nab
  rw[ne_comm]
  apply nbc
  apply col_perm1
  apply colabc

lemma nbet_perm1 (a b c : Point) : ¬ between a b c → ¬ between c b a := by
  intro nbetabc
  intro fbet
  apply between_sym at fbet
  apply nbetabc fbet



lemma between_equiv_not_or (a b c : Point)(nab:a≠ b)(nac:a≠ c)(nbc:b≠ c)(colabc:collinear a b c):
 between a b c ↔ ¬ (between a c b ∨ between c a b) := by
  constructor
  · intro betabc
    cases' exist_unique_point_between betabc with leftH rightH
    intro n
    cases' n with beth beth
    apply leftH beth
    apply between_sym at beth
    apply rightH beth
  · intro nbet
    push_neg at nbet
    cases' nbet with nbetacb nbetcab
    apply nbet_imp2 b c a
    apply nbc
    rw[ne_comm]
    apply nab
    rw[ne_comm]
    apply nac
    apply col_perm1
    apply col_perm2
    apply colabc
    apply nbet_perm1
    apply nbetacb
    apply nbet_perm1
    apply nbetcab

lemma between_equiv_and (a b c : Point)(nab:a≠ b)(nac:a≠ c)(nbc:b≠ c)(colabc:collinear a b c) :
 between a b c <-> ¬ between a c b ∧ ¬ between c a b := by
  constructor
  intro betabc
  rw [← @not_or]
  rw[<- between_equiv_not_or]
  apply betabc; apply nab; apply nac; apply nbc
  apply colabc
  intro nh
  rw[<- @not_or] at nh
  rw[<- between_equiv_not_or] at nh
  apply nh; apply nab; apply nac; apply nbc
  apply colabc



-- def ray_same_side(o c b :Point) := between o c b ∨ between o b c ∨ ( o ≠ c ∧ c = b)
-- def ray_diff_side(o c b : Point) := between c o b ∨ (c = o ∧ c = b)

-- lemma points_on_line_on_rays (o c b : Point) (h : collinear o c b) : ray_same_side o c b ∨ ray_diff_side o c b := by
--   rw [@or_iff_not_imp_right]
--   intro not_diff
--   unfold ray_diff_side at not_diff
--   push_neg at not_diff
--   unfold ray_same_side
--   rw [@or_iff_not_imp_left]
--   intro nbetocb
--   cases' not_diff with leftH rightH
--   right
--   sorry
