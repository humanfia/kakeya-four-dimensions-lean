import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankMatch
import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankSuccess
import Submission.Obl.k4_scalar_candidate_original_return.SplitInterfaces
import Submission.Obl.k4_scalar_candidate_original_return.Coverage.Pigeonhole

/-!
# New labels of the improved family at one stage

On a layer `ℓ`, every plank `i` keeps its posterior record choice `bstarOf i` (from
`plank_success`), its jet bins `binsOf i`, and the new labels are the pairs `(i, b)`.  Each label
has a representative candidate `repOf j`, and lists keep the old terminal list of the parent
plank and the neighbouring bins of the record choice.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

noncomputable section

namespace PreparedData

variable (a : PreparedData) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))

/-- Listed success of plank `i` for a record-to-bin choice. -/
def succSet (i : Fin (a.ls k ℓ).n) (bstar : (Fin 2 → ℤ) × ℤ → (Fin 6 → ℤ)) : Set Inc :=
  ⋃ m, a.cvd π k ℓ i m ∩ a.recordOf π k ⁻¹' {O | Nbr (bstar O) (a.jetBin π k ℓ i m)}

/-- The posterior success inequality of a record choice. -/
def SuccProp (i : Fin (a.ls k ℓ).n) (bstar : (Fin 2 → ℤ) × ℤ → (Fin 6 → ℤ)) : Prop :=
  a.ρ k ((a.ls k ℓ).world i) (a.cov π.θ π.σ k ℓ i) ≤
    a.ρ k ((a.ls k ℓ).world i) (a.succSet π k ℓ i bstar) +
      MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k)

/-- A record choice with the posterior success property, when one exists. -/
def bstarOf (i : Fin (a.ls k ℓ).n) : (Fin 2 → ℤ) × ℤ → (Fin 6 → ℤ) :=
  by
    classical
    exact if h : ∃ b, a.SuccProp π k ℓ i b then Classical.choose h else fun _ _ => 0

/-- The jet bins used by plank `i`. -/
def binsOf (i : Fin (a.ls k ℓ).n) : Finset (Fin 6 → ℤ) :=
  by
    classical
    exact Finset.univ.image (a.jetBin π k ℓ i)

/-- New labels: a plank and one of its jet bins. -/
abbrev NewLabel : Type := Σ i : Fin (a.ls k ℓ).n, ↥(a.binsOf π k ℓ i)

/-- Number of new labels. -/
def nNew : ℕ := Fintype.card (a.NewLabel π k ℓ)

/-- Enumeration of the new labels. -/
def labelEquiv : a.NewLabel π k ℓ ≃ Fin (a.nNew π k ℓ) := Fintype.equivFin _

/-- Parent plank of a new label. -/
def parentOf (j : Fin (a.nNew π k ℓ)) : Fin (a.ls k ℓ).n :=
  ((a.labelEquiv π k ℓ).symm j).1

/-- Jet bin of a new label. -/
def binLabel (j : Fin (a.nNew π k ℓ)) : Fin 6 → ℤ := ((a.labelEquiv π k ℓ).symm j).2.1

/-- New label of a candidate. -/
def binOf (i : Fin (a.ls k ℓ).n) (h : Fin (a.ncand π k ℓ i)) : Fin (a.nNew π k ℓ) :=
  by
    classical
    exact a.labelEquiv π k ℓ
      ⟨i, ⟨a.jetBin π k ℓ i h, Finset.mem_image_of_mem _ (Finset.mem_univ h)⟩⟩

/-- A candidate of the parent plank in the label's bin. -/
def repOf (j : Fin (a.nNew π k ℓ)) : Fin (a.ncand π k ℓ (a.parentOf π k ℓ j)) :=
  by
    classical
    exact Classical.choose (Finset.mem_image.mp ((a.labelEquiv π k ℓ).symm j).2.2)

/-- Representative polynomial of a new label. -/
def Qof (j : Fin (a.nNew π k ℓ)) : Poly := a.cand π k ℓ (a.parentOf π k ℓ j) (a.repOf π k ℓ j)

/-- New lists: old terminal list of the parent and neighbouring bins of its record choice. -/
def listsOf (g : Fin (a.Wk k)) (z : Base × ℤ) : Finset (Fin (a.nNew π k ℓ)) :=
  by
    classical
    exact Finset.univ.filter (fun j =>
      (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
        a.parentOf π k ℓ j ∈ (a.ls k ℓ).lists g z ∧
        Nbr (a.bstarOf π k ℓ (a.parentOf π k ℓ j) (a.recObs π k z)) (a.binLabel π k ℓ j))

end PreparedData

end

end Submission.Obl.k4_scalar_candidate_original_return
