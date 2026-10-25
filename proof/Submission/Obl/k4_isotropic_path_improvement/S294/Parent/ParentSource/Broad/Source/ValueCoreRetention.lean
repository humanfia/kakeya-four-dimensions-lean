-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ValueCoreRetention, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ValueCoreRetention.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ValueCoreRetention.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreSourceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DensePackets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open scoped ENNReal BigOperators

noncomputable section

abbrev ValueBranchData.ActiveValue
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) :=
  {ba : Fin p.C × Fin V.count // p.lev ba.1 = mid ∧ (V.inner ba.1 ba.2).Nonempty}

abbrev ValueBranchData.CoreFamilies
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (θ : ENNReal) :=
  (v : V.ActiveValue) →
    CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p v.1.1 (V.center v.1.2))
      (V.entryLaw v.1.1 v.1.2) (packetNativeCubePoint (d.N k) (d.B k) p v.1.1)
      (V.outer v.1.1 v.1.2) θ

def ValueBranchData.coreRetained
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) {θ : ENNReal}
    (cores : V.CoreFamilies θ) (w : Fin (d.W k)) : Set Event :=
  V.residual w ∩ ⋃ v : V.ActiveValue,
    if p.γ v.1.1 = w then V.inner v.1.1 v.1.2 ∩ ⋃ i, (cores v).kept i else ∅

theorem ValueBranchData.exists_core_families
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (θ : ENNReal) :
    Nonempty (V.CoreFamilies θ) := by
  classical
  have hN : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have hB : ∀ w, 0 < d.B k w := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    intro w
    exact ((hformat k).2.2.2.1 w).2.1
  exact ⟨fun v => Classical.choice (coreEntryData_of_family
    (V.core_entries hp hN hK hκK v.1.1 v.2.1 (hB _) v.1.2 v.2.2 θ))⟩

/-- All coherent core/sign branches are retained simultaneously under
the original global reference budget. The cost has no number of source
packets, inverse packet mass, or later selected-entry denominator. -/
theorem ValueBranchData.core_retention_budget
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {θ : ENNReal} (cores : V.CoreFamilies θ) :
    (∀ w, MeasurableSet (V.coreRetained cores w) ∧ V.coreRetained cores w ⊆ V.residual w) ∧
    (∑ w, ENNReal.ofReal (d.ω k w) *
      ((d.ν k w).prod volume) (V.residual w \ V.coreRetained cores w)) ≤
      ENNReal.ofReal (K ^ 10) * ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ := by
  classical
  letI : Fintype V.ActiveValue := Fintype.ofFinite _
  obtain ⟨hω, hsum, hν⟩ := hd.weights k
  letI : ∀ w, IsProbabilityMeasure (d.ν k w) := hν
  let reference : Fin p.C → ENNReal := fun b =>
    ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) * d.ν k (p.γ b) (p.A b)
  have hN : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have href0 (b : Fin p.C) : reference b ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (hp.assignment_mass_pos hN b).ne'
  have hreftop (b : Fin p.C) : reference b ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hret (v : V.ActiveValue) {z : Event} (hz : z ∈ V.residual (p.γ v.1.1))
      (hzin : z ∈ V.inner v.1.1 v.1.2) (hzcore : z ∈ ⋃ i, (cores v).kept i) :
      z ∈ V.coreRetained cores (p.γ v.1.1) :=
    ⟨hz, mem_iUnion.mpr ⟨v, by rw [ite_eq_left rfl]; exact ⟨hzin, hzcore⟩⟩⟩
  have hmeas (w : Fin (d.W k)) : MeasurableSet (V.coreRetained cores w) := by
    apply (V.residual_measurable w).inter
    apply MeasurableSet.iUnion
    intro v
    split_ifs
    · exact (V.measurable v.1.1 v.1.2).2.inter
        (MeasurableSet.iUnion (fun i => ((cores v).measurable i).2))
    · exact MeasurableSet.empty
  have hcovered (w : Fin (d.W k)) : V.residual w \ V.coreRetained cores w ⊆
      {z | ∃ v : V.ActiveValue, p.γ v.1.1 = w ∧ z ∈ V.inner v.1.1 v.1.2} := by
    intro z hz
    obtain ⟨b, a, hb, hbw, hza⟩ := V.cover w z hz.1
    exact ⟨⟨(b, a), hb, z, hza⟩, hbw, hza⟩
  have hlocal (v : V.ActiveValue) :
      ((d.ν k (p.γ v.1.1)).prod volume)
        ((V.residual (p.γ v.1.1) \ V.coreRetained cores (p.γ v.1.1)) ∩ V.inner v.1.1 v.1.2) ≤
      reference v.1.1 * (ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ) := by
    let E := (⋃ i, (cores v).kept i)ᶜ
    have hE : MeasurableSet E := (MeasurableSet.iUnion (fun i => ((cores v).measurable i).2)).compl
    calc
      _ ≤ ((d.ν k (p.γ v.1.1)).prod volume) (E ∩ V.outer v.1.1 v.1.2) := by
        apply measure_mono
        intro z hz
        exact ⟨fun hc => hz.1.2 (hret v hz.1.1 hz.2 hc), (V.subset v.1.1 v.1.2).1 hz.2⟩
      _ = reference v.1.1 * V.entryLaw v.1.1 v.1.2 E := by
        rw [ValueBranchData.entryLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hE]
        have hden : d.ν k (p.γ v.1.1) (p.A v.1.1) *
            ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) = reference v.1.1 := mul_comm _ _
        rw [hden, ← mul_assoc, ENNReal.mul_inv_cancel (href0 _) (hreftop _), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (cores v).loss
  have hbudget : (∑ v : V.ActiveValue, ENNReal.ofReal (d.ω k (p.γ v.1.1)) * reference v.1.1) ≤
      (V.count : ENNReal) := by
    let g : Fin p.C × Fin V.count → ENNReal := fun ba =>
      if p.lev ba.1 = mid then ENNReal.ofReal (d.ω k (p.γ ba.1)) * reference ba.1 else 0
    calc
      _ ≤ ∑ ba, g ba := by
        apply Finset.sum_le_sum_of_injOn Subtype.val
        · intro v _ v' _ hv
          exact Subtype.val_injective hv
        · exact Finset.subset_univ _
        · intro v _
          simp only [g, ite_eq_left v.2.1]
          exact le_rfl
        · intros
          exact zero_le
      _ = (V.count : ENNReal) * ∑ b : Fin p.C,
          if p.lev b = mid then ENNReal.ofReal (d.ω k (p.γ b)) * reference b else 0 := by
        rw [Fintype.sum_prod_type]
        simp only [g, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
      _ ≤ (V.count : ENNReal) * 1 := mul_le_mul' le_rfl
        (by simpa only [reference, ite_mul, zero_mul] using hp.full_reference_mass_le_one hν hω hsum mid)
      _ = _ := mul_one _
  refine ⟨fun w => ⟨hmeas w, inter_subset_left⟩, ?_⟩
  calc
    _ ≤ ∑ v : V.ActiveValue, ENNReal.ofReal (d.ω k (p.γ v.1.1)) *
        ((d.ν k (p.γ v.1.1)).prod volume)
          ((V.residual (p.γ v.1.1) \ V.coreRetained cores (p.γ v.1.1)) ∩ V.inner v.1.1 v.1.2) :=
      weighted_cover_mass_le (fun w => (d.ν k w).prod volume) (fun w => ENNReal.ofReal (d.ω k w))
        (fun v : V.ActiveValue => p.γ v.1.1) (fun v => V.inner v.1.1 v.1.2)
        (fun w => V.residual w \ V.coreRetained cores w) hcovered
    _ ≤ ∑ v : V.ActiveValue, ENNReal.ofReal (d.ω k (p.γ v.1.1)) *
        (reference v.1.1 * (ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ)) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul' le_rfl (hlocal v))
    _ = (∑ v : V.ActiveValue, ENNReal.ofReal (d.ω k (p.γ v.1.1)) * reference v.1.1) *
        (ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ) := by simp only [Finset.sum_mul, mul_assoc]
    _ ≤ (V.count : ENNReal) * (ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ) :=
      mul_le_mul' hbudget le_rfl
    _ ≤ ENNReal.ofReal (K ^ 10) * ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ := by
      rw [mul_assoc]
      exact mul_le_mul' (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal V.count_le) le_rfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
