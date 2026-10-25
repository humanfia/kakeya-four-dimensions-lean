/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/PairRepresentatives.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.PairFacts
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Representatives

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Set MeasureTheory
open scoped ENNReal

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)
    {Bin : Type*}

def anchorGood (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (s : Fin p.m) : Prop :=
  ρ ≤ |MvPolynomial.eval (fun i => α i) (disc (p.P s))|

noncomputable def representative (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (b : Fin p.J) (β : Bin) : Option (Fin p.m) :=
  chooseRepresentative p.frame bins (p.anchorGood α ρ) b β

noncomputable def representativeTest (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (b : Fin p.J) (β : Bin) :
    MvPolynomial (Fin 4) ℝ :=
  match p.representative bins α ρ b β with
  | none => 0
  | some r => p.P r

theorem representative_spec (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) {b : Fin p.J} {β : Bin} {r : Fin p.m}
    (hr : p.representative bins α ρ b β = some r) :
    p.frame r = b ∧ β ∈ bins r ∧ p.anchorGood α ρ r :=
  chooseRepresentative_spec p.frame bins (p.anchorGood α ρ) hr

theorem representative_exists (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)
    (s : Fin p.m) (β : Bin) (hβ : β ∈ bins s) (hs : p.anchorGood α ρ s) :
    ∃ r, p.representative bins α ρ (p.frame s) β = some r ∧
      p.frame r = p.frame s ∧ β ∈ bins r ∧ p.anchorGood α ρ r :=
  chooseRepresentative_exists p.frame bins (p.anchorGood α ρ) ⟨s, rfl, hβ, hs⟩

theorem representativeTest_eq (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) {b : Fin p.J} {β : Bin} {r : Fin p.m}
    (hr : p.representative bins α ρ b β = some r) :
    p.representativeTest bins α ρ b β = p.P r := by
  simp only [representativeTest, hr]

def representativeBadSet (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ CD : ℝ) (s : Fin p.m) (β : Bin) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  match p.representative bins α ρ (p.frame s) β with
  | none => ∅
  | some r => {z | ‖z‖ ≤ 1 / 8 ∧
      |MvPolynomial.eval (fun i => z i) (disc (p.P r))| < Nk ^ (-(CD * a))}

theorem measurableSet_representativeBadSet (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ CD : ℝ) (s : Fin p.m) (β : Bin) :
    MeasurableSet (p.representativeBadSet bins α ρ CD s β) := by
  unfold representativeBadSet
  split
  · exact MeasurableSet.empty
  · rename_i r hr
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        |MvPolynomial.eval (fun i => z i) (disc (p.P r))|) :=
      ((MvPolynomial.continuous_eval _).comp (by fun_prop)).abs
    have hn : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => ‖z‖) :=
      continuous_norm.measurable
    change MeasurableSet ({z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ 1 / 8} ∩
      {z | |MvPolynomial.eval (fun i => z i) (disc (p.P r))| < Nk ^ (-(CD * a))})
    exact (measurableSet_le hn measurable_const).inter
      (measurableSet_lt hc.measurable measurable_const)

def sourceBadSet (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ CD : ℝ) (s : Fin p.m) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ β ∈ bins s, p.representativeBadSet bins α ρ CD s β

theorem measurableSet_sourceBadSet (bins : Fin p.m → Finset Bin)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ CD : ℝ) (s : Fin p.m) :
    MeasurableSet (p.sourceBadSet bins α ρ CD s) :=
  Finset.measurableSet_biUnion (bins s) fun β _ =>
    p.measurableSet_representativeBadSet bins α ρ CD s β

end PairData
end Submission.Obl.k4_matched_pair_representative_realization.Selection
