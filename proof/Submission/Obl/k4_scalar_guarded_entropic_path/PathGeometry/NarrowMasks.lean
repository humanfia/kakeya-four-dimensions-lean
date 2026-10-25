/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/NarrowMasks.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidthTails

/-! Original-world exceptional masks for narrow labels of the actual
chosen atlas, and the literal width bound on every surviving label. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting

noncomputable section

def narrowLabels {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) : Finset (Fin Q.n) :=
  Finset.univ.filter (fun i => 4 * (N p k ^ ε * Q.J i) ≤ vwidth / (2 : ℝ) ^ Q.T)

def narrowUnion {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) (g : Fin (W p k)) : Set ((ℕ × ScalarCoeff) × ℝ) :=
  ⋃ i ∈ (narrowLabels Q vwidth).filter (fun i => Q.γ i = g), Q.A i ×ˢ I Q.T (Q.j i)

theorem measurableSet_narrowUnion {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) (g : Fin (W p k)) :
    MeasurableSet (narrowUnion Q vwidth g) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    (Q.hcd.2.2.1 i).1.prod measurableSet_Icc

/-- The exceptional mask is charged to the actual original rectangle
mass, without a packet-count factor. -/
theorem weighted_narrowUnion_le {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) :
    (∑ g, ENNReal.ofReal (ω p k g) * mu p k g (narrowUnion Q vwidth g)) ≤
      narrowMass Q vwidth := by
  classical
  calc
    _ ≤ ∑ g, ENNReal.ofReal (ω p k g) *
        ∑ i ∈ (narrowLabels Q vwidth).filter (fun i => Q.γ i = g),
          mu p k g (Q.A i ×ˢ I Q.T (Q.j i)) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul' le_rfl (measure_biUnion_finset_le _ _)
    _ = ∑ g, ∑ i ∈ (narrowLabels Q vwidth).filter (fun i => Q.γ i = g),
        ENNReal.ofReal (ω p k (Q.γ i)) * mu p k (Q.γ i) (Q.A i ×ˢ I Q.T (Q.j i)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise (narrowLabels Q vwidth) Q.γ _

/-- Common-path deletion may use these ORIGINAL-world masks directly. -/
theorem narrowUnion_powerSmall {p : Code} (hp : Exact p)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (B : ℕ) (h : ℝ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) (hε0 : ∀ k, 0 ≤ ε k)
    (Q : ∀ k, ChartW p B (L p) (L p) (h + ε k) (ε k) true (φ k))
    {u : ℝ} (hu : 0 < u) (huU : u ≤ U p) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ g, ENNReal.ofReal (ω p (φ k) g) *
        mu p (φ k) g (narrowUnion (Q k) (N p (φ k) ^ (-u)) g)) ≤
          ENNReal.ofReal (N p (φ k) ^ (-c)) := by
  obtain ⟨c, hc, hbound⟩ := narrowMass_powerSmall hp φ hφ B h ε hε hε0 Q hu huU
  exact ⟨c, hc, hbound.mono fun k hk => (weighted_narrowUnion_le _ _).trans hk⟩

/- Adapted from same-tree o093/x0535, commit 21cac614, NarrowMasks.lean. -/
/-- Membership keeps the finite original label explicit. -/
theorem mem_narrowUnion {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) (g : Fin (W p k))
    (i : Fin Q.n) (hi : i ∈ narrowLabels Q vwidth) (hg : Q.γ i = g)
    (z : (ℕ × ScalarCoeff) × ℝ) (hz : z ∈ Q.A i ×ˢ I Q.T (Q.j i)) :
    z ∈ narrowUnion Q vwidth g :=
  Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hg⟩, hz⟩

/-- Outside the original narrow mask, any covering selected piece has
a label with the required width. The full assignment stays unchanged. -/
theorem cover_good_of_not_narrow {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) (g : Fin (W p k))
    (z : (ℕ × ScalarCoeff) × ℝ)
    (hcover : ∃ i, Q.γ i = g ∧ z ∈ Q.C i)
    (hnot : z ∉ narrowUnion Q vwidth g) :
    ∃ i, i ∉ narrowLabels Q vwidth ∧ Q.γ i = g ∧ z ∈ Q.C i := by
  obtain ⟨i, hi, hz⟩ := hcover
  refine ⟨i, ?_, hi, hz⟩
  intro hbad
  apply hnot
  apply Set.mem_iUnion₂.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨hbad, hi⟩,
    (Q.hcd.2.2.2.2.1 i hz).2⟩

/-- Deleting the narrow mask preserves current coverage by the good
full original assignments, without renormalizing any prior. -/
theorem support_good_after_narrow_mask {p : Code} {B k : ℕ} {r b h ε : ℝ}
    (Q : ChartW p B r b h ε true k) (vwidth : ℝ) (g : Fin (W p k))
    (σ : Measure ((ℕ × ScalarCoeff) × ℝ))
    (hcover : σ {z | ∃ i, Q.γ i = g ∧ z ∈ Q.C i}ᶜ = 0)
    (hnot : σ (narrowUnion Q vwidth g) = 0) :
    σ {z | ∃ i, i ∉ narrowLabels Q vwidth ∧ Q.γ i = g ∧ z ∈ Q.C i}ᶜ = 0 := by
  apply measure_mono_null _ (measure_union_null hcover hnot)
  intro z hz
  by_cases hold : ∃ i, Q.γ i = g ∧ z ∈ Q.C i
  · by_cases hbad : z ∈ narrowUnion Q vwidth g
    · exact Or.inr hbad
    · exact (hz (cover_good_of_not_narrow Q vwidth g z hold hbad)).elim
  · exact Or.inl hold

/-- A retained label has the required full-block width lower bound. -/
theorem width_lower_of_not_mem {p : Code} {B k : ℕ} {r b h ε u : ℝ}
    (Q : ChartW p B r b h ε true k) (hN : 0 < N p k) (i : Fin Q.n)
    (hi : i ∉ narrowLabels Q (N p k ^ (-u))) :
    ((4 * N p k ^ (ε + u)) * (2 : ℝ) ^ Q.T)⁻¹ ≤ Q.J i := by
  have hnot : ¬4 * (N p k ^ ε * Q.J i) ≤ N p k ^ (-u) / (2 : ℝ) ^ Q.T := by
    intro hbad
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbad⟩)
  have hε : 0 < N p k ^ ε := Real.rpow_pos_of_pos hN _
  have hu : 0 < N p k ^ u := Real.rpow_pos_of_pos hN _
  calc
    _ = (N p k ^ (-u) / (2 : ℝ) ^ Q.T) / (4 * N p k ^ ε) := by
      rw [Real.rpow_add hN, Real.rpow_neg hN.le]
      field_simp
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith [lt_of_not_ge hnot])

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowWidths
