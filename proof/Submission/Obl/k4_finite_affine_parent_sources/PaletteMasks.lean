-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathMass
import Submission.Lib.K4AngularCharge.AngularCharge
import Submission.Lib.K4ExactProblemOps.Coarsening

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge
open scoped ENNReal

noncomputable section

namespace PaletteMasks

/-- All listed labels retain their conditional shares in the unchanged
original law. The number of chart labels does not enter its loss bound. -/
def shares {Ω O ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace O] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (F : ι → Set Ω)
    (θ : ℝ≥0∞) : Set Ω :=
  ⋂ b, (F b)ᶜ ∪ {z | θ ≤ labelShare μ obs (F b) z}

theorem measurableSet_shares {Ω O ι : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace O] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (hobs : Measurable obs)
    (F : ι → Set Ω) (hF : ∀ b, MeasurableSet (F b)) (θ : ℝ≥0∞) :
    MeasurableSet (shares μ obs F θ) :=
  MeasurableSet.iInter fun b => (hF b).compl.union
    (measurableSet_le measurable_const (measurable_labelShare μ hobs (hF b)))

theorem share_of_mem {Ω O ι : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace O] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (F : ι → Set Ω)
    (θ : ℝ≥0∞) {z : Ω} (hz : z ∈ shares μ obs F θ) (b : ι) (hb : z ∈ F b) :
    θ ≤ labelShare μ obs (F b) z := by
  exact (mem_iInter.mp hz b).resolve_left (fun h => h hb)

theorem shares_loss {Ω O ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Ω] [MeasurableSpace O] [MeasurableEq O] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (hobs : Measurable obs)
    (F : ι → Set Ω) (hF : ∀ b, MeasurableSet (F b))
    (lst : O → Finset ι) (hknown : ∀ b, ∀ z ∈ F b, b ∈ lst (obs z))
    (Kc : ℕ) (hKc : ∀ o, (lst o).card ≤ Kc) (θ : ℝ≥0∞) :
    μ (shares μ obs F θ)ᶜ ≤ Kc * θ * μ univ := by
  have heq : (shares μ obs F θ)ᶜ =
      ⋃ b, F b ∩ {z | labelShare μ obs (F b) z < θ} := by
    ext z
    simp [shares, not_le]
  rw [heq]
  exact (measure_iUnion_fintype_le _ _).trans
    (share_pruning μ obs hobs F hF lst hknown Kc hKc θ)

/-- The terminal pure-density floor and finitely many original angular
ceilings are imposed before selecting a parent or changing its palette. -/
def angular {Ω O V ι : Type*} [Fintype ι]
    (obs : Ω → O) (cell : ι → Ω → V) (g : O → ℝ≥0∞)
    (G : ι → O × V → ℝ≥0∞) (α : ι → ℝ≥0∞) (β : ℝ≥0∞) : Set Ω :=
  {z | β ≤ g (obs z)} ∩ ⋂ i, {z | G i (obs z, cell i z) ≤ α i}

theorem measurableSet_angular {Ω O V ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace O] [MeasurableSpace V] [Fintype ι]
    (obs : Ω → O) (hobs : Measurable obs) (cell : ι → Ω → V)
    (hcell : ∀ i, Measurable (cell i)) (g : O → ℝ≥0∞) (hg : Measurable g)
    (G : ι → O × V → ℝ≥0∞) (hG : ∀ i, Measurable (G i))
    (α : ι → ℝ≥0∞) (β : ℝ≥0∞) :
    MeasurableSet (angular obs cell g G α β) :=
  (measurableSet_le measurable_const (hg.comp hobs)).inter
    (MeasurableSet.iInter fun i =>
      measurableSet_le ((hG i).comp (hobs.prodMk (hcell i))) measurable_const)

theorem angular_loss {Ω O V ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (obs : Ω → O) (cell : ι → Ω → V) (g : O → ℝ≥0∞)
    (G : ι → O × V → ℝ≥0∞) (α : ι → ℝ≥0∞) (β : ℝ≥0∞) :
    μ (angular obs cell g G α β)ᶜ ≤ μ {z | g (obs z) < β} +
      ∑ i, μ {z | α i < G i (obs z, cell i z)} := by
  classical
  have heq : (angular obs cell g G α β)ᶜ =
      {z | g (obs z) < β} ∪ ⋃ i, {z | α i < G i (obs z, cell i z)} := by
    ext z
    simp only [angular, mem_compl_iff, mem_inter_iff, mem_setOf_eq, mem_iInter,
      not_and_or, not_forall, not_le, mem_union, mem_iUnion]
  rw [heq]
  exact (measure_union_le _ _).trans
    (add_le_add le_rfl (measure_iUnion_fintype_le _ _))

end PaletteMasks

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- At one actual path level the terminal-observation share mask costs
only the original known-list bound, for every original world law. -/
theorem PathData.Valid.level_share_loss
    (μ : Measure Incidence) [IsFiniteMeasure μ]
    (hNk : 1 ≤ Nk) (i : ℕ) (hri : 0 ≤ p.r i) (hriL : p.r i ≤ L)
    (w : Fin W) (Kc : ℕ) (hKc : p.κ ≤ Kc) (θ : ℝ≥0∞) :
    μ (PaletteMasks.shares μ (obs (B w) (δ Nk L))
      (fun b : {b : Fin p.C // p.lev b = i ∧ p.world b = w} => p.counted b.val) θ)ᶜ ≤
      Kc * θ * μ univ := by
  classical
  let pred := fun b : Fin p.C => p.lev b = i ∧ p.world b = w
  let lst := fun o => (p.terminalLists Nk L i w o).subtype pred
  apply PaletteMasks.shares_loss μ (obs (B w) (δ Nk L))
    (Submission.Lib.K4ExactProblemOps.measurable_obs _ _)
    _ (fun b => hp.counted_measurable b.val) lst ?_ Kc ?_ θ
  · intro b z hz
    apply Finset.mem_subtype.mpr
    change b.val ∈ p.terminalLists Nk L i w (obs (B w) (δ Nk L) z)
    have h := hp.terminal_known hNk b.property.1 hri hriL hz
    rw [b.property.2] at h
    exact h
  · intro o
    rw [Finset.card_subtype]
    apply (Finset.card_filter_le _ _).trans
    exact_mod_cast (hp.terminal_list_bound i w o).trans hKc

end Path

end
end Submission.Obl.k4_finite_affine_parent_sources
