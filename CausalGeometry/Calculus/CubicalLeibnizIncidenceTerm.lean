import CausalGeometry.Calculus.CubicalLeibnizGeometry
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- One common incidence contribution in d(alpha cup beta), indexed by an
ambient face i and a p-subset A of the surviving face axes. -/
def leibnizIncidenceTerm
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) : K :=
  faceSign (K := K) i *
    subsetShuffleSign (K := K) A *
    (alpha ((Q.upperFace i).selectedCube A) *
        beta ((Q.upperFace i).complementCube A)
      -
     alpha ((Q.lowerFace i).selectedCube A) *
        beta ((Q.lowerFace i).complementCube A))

/-- The corresponding local contribution coming from (d alpha) cup beta. -/
def leibnizLeftIncidenceTerm
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) : K :=

  let LA :=
    CausalEventCube.liftFaceSubset i A

  let hi :=
    CausalEventCube.removedAxis_not_mem_liftFaceSubset i A

  let B :=
    CausalEventCube.insertAxisSubset LA i hi

  let j :=
    CausalEventCube.insertedAxisPosition LA i hi

  let hdim :
      (p + 1) + q = p + q + 1 := by
        omega

  subsetShuffleSign
      (K := K)
      (CausalEventCube.specializeAxisSubset hdim B)
    *
  faceSign (K := K) j
    *
  (alpha ((Q.selectedCube B).upperFace j) -
    alpha ((Q.selectedCube B).lowerFace j))
    *
  beta
    (CausalEventCube.complementCubeOfEq
      hdim Q B)

/-- The corresponding local contribution coming from
(-1)^p alpha cup (d beta). -/
def leibnizRightIncidenceTerm
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) : K :=

  let LA :=
    CausalEventCube.liftFaceSubset i A

  let hi :=
    CausalEventCube.removedAxis_not_mem_liftFaceSubset i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
        omega

  let j :=
    CausalEventCube.complementAxisPosition
      hdim LA i hi

  gradedSign (K := K) p
    *
  subsetShuffleSign
      (K := K)
      (CausalEventCube.specializeAxisSubset hdim LA)
    *
  alpha (Q.selectedCube LA)
    *
  faceSign (K := K) j
    *
  (beta
      ((CausalEventCube.complementCubeOfEq
          hdim Q LA).upperFace j)
    -
   beta
      ((CausalEventCube.complementCubeOfEq
          hdim Q LA).lowerFace j))

/-- Termwise graded Leibniz identity on the common incidence index.

All cubical geometry and shuffle signs have already been reduced to this
identity; the final step is the ordinary product-difference rule in K. -/
theorem leibnizIncidenceTerm_eq_left_add_right
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) :
    leibnizIncidenceTerm alpha beta Q i A
      =
    leibnizLeftIncidenceTerm alpha beta Q i A
      +
    leibnizRightIncidenceTerm alpha beta Q i A := by

  let LA :=
    CausalEventCube.liftFaceSubset i A

  let hi :
      i ∉ LA :=
    CausalEventCube.removedAxis_not_mem_liftFaceSubset i A

  let B :=
    CausalEventCube.insertAxisSubset LA i hi

  let jL :=
    CausalEventCube.insertedAxisPosition LA i hi

  let hL :
      (p + 1) + q = p + q + 1 := by
    omega

  let hR :
      p + (q + 1) = p + q + 1 := by
    omega

  let jR :=
    CausalEventCube.complementAxisPosition
      hR LA i hi

  have hcoefL :
      faceSign (K := K) i *
          subsetShuffleSign (K := K) A
        =
      subsetShuffleSign
          (K := K)
          (CausalEventCube.specializeAxisSubset
            hL B)
        *
      faceSign (K := K) jL := by
    simpa [LA, hi, B, jL, hL] using
      leibniz_left_coefficient
        (K := K) (p := p) (q := q)
        i A

  have hcoefR :
      faceSign (K := K) i *
          subsetShuffleSign (K := K) A
        =
      gradedSign (K := K) p *
        subsetShuffleSign
          (K := K)
          (CausalEventCube.specializeAxisSubset
            hR LA)
        *
        faceSign (K := K) jR := by
    simpa [LA, hi, hR, jR] using
      leibniz_right_coefficient
        (K := K) (p := p) (q := q)
        i A

  have hSelU :
      (Q.upperFace i).selectedCube A =
        (Q.selectedCube B).upperFace jL := by
    simpa [LA, hi, B, jL] using
      CausalEventCube
        .upperFace_selectedCube_eq_selectedCube_upperFace
          (p := p) (q := q) Q i A

  have hSelL :
      (Q.lowerFace i).selectedCube A =
        (Q.selectedCube B).lowerFace jL := by
    simpa [LA, hi, B, jL] using
      CausalEventCube
        .lowerFace_selectedCube_eq_selectedCube_lowerFace
          (p := p) (q := q) Q i A

  have hCompU_L :
      (Q.upperFace i).complementCube A =
        CausalEventCube.complementCubeOfEq
          hL Q B := by
    simpa [LA, hi, B, hL] using
      CausalEventCube
        .upperFace_complementCube_eq_insertComplementCube
          (p := p) (q := q) Q i A

  have hSelL_R :
      (Q.lowerFace i).selectedCube A =
        Q.selectedCube LA := by
    simpa [LA] using
      CausalEventCube
        .lowerFace_selectedCube_eq_liftSelectedCube
          (p := p) (q := q) Q i A

  have hCompL_R :
      (Q.lowerFace i).complementCube A =
        (CausalEventCube.complementCubeOfEq
          hR Q LA).lowerFace jR := by
    simpa [LA, hi, hR, jR] using
      CausalEventCube
        .lowerFace_complementCube_eq_liftComplement_lowerFace
          (p := p) (q := q) Q i A

  have hCompU_R :
      (Q.upperFace i).complementCube A =
        (CausalEventCube.complementCubeOfEq
          hR Q LA).upperFace jR := by
    simpa [LA, hi, hR, jR] using
      CausalEventCube
        .upperFace_complementCube_eq_liftComplement_upperFace
          (p := p) (q := q) Q i A

  unfold leibnizIncidenceTerm
    leibnizLeftIncidenceTerm
    leibnizRightIncidenceTerm

  dsimp only

  rw [
    hSelU, hSelL,
    hCompU_L,
    hSelL_R,
    hCompL_R,
    hCompU_R,
    hcoefL
  ]

  have hcoefR' :
      subsetShuffleSign
          (K := K)
          (CausalEventCube.specializeAxisSubset
            hL B)
        *
      faceSign (K := K) jL
        =
      gradedSign (K := K) p *
        subsetShuffleSign
          (K := K)
          (CausalEventCube.specializeAxisSubset
            hR LA)
        *
        faceSign (K := K) jR := by
    rw [← hcoefL, hcoefR]

  rw [hcoefR']

  ring

end CausalCubicalCochain
end CausalGeometry
