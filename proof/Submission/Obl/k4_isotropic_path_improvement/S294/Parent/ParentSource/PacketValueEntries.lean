-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketValueEntries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketValueEntries.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketValueEntries.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketValueEntries.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketValueEntries.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PathEntryPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeCube
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! # Actual original heavy value entries before potential selection -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- Split actual original fine packet incidences by their OWN native
signal, at width K^-6, before any potential or common intercept is chosen.
The finite label count and earlier FULL-original-prior floors are derived.
The retained global mixture pays this original reference budget once. -/
theorem path_heavy_original_value_entries
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {Bv : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev Bv profile κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hweight : ∀ w, 0 ≤ weight w)
    (hsum : ∑ w, weight w = 1)
    (H : Fin W → Set Event) (hH : ∀ w, MeasurableSet (H w))
    (hterminal : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) {K : ℝ} (hK : 2 ≤ K) (hκK : p.κ ≤ K) (θ : ENNReal) :
    ∃ M : ℕ, ∃ center : Fin M → ℝ,
    ∃ U V : Fin p.C → Fin M → Set Event, ∃ H' : Fin W → Set Event,
      (M : ℝ) ≤ K ^ 10 ∧
      (∀ b e, MeasurableSet (U b e) ∧ MeasurableSet (V b e)) ∧
      (∀ b, Pairwise fun e e' => Disjoint (V b e) (V b e')) ∧
      (∀ b e, V b e ⊆ U b e ∧ U b e ⊆ H (p.γ b) ∩ p.F b) ∧
      (∀ b e z, z ∈ U b e → |packetSignal Nk p b z - center e| ≤ (K ^ 6)⁻¹) ∧
      (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ H w) ∧
      (∑ w, ENNReal.ofReal (weight w) * ((ν w).prod volume) (H w \ H' w)) ≤
        ENNReal.ofReal (K ^ 10) * θ ∧
      (∀ b, p.lev b = i → ∀ e, (V b e).Nonempty →
        θ * (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)) ≤
          ((ν (p.γ b)).prod volume) (U b e)) ∧
      ∀ w z, z ∈ H' w → ∃ b e, p.lev b = i ∧ p.γ b = w ∧ z ∈ V b e := by
  classical
  let ε := (K ^ 6)⁻¹
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨Bins, hBins, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hε hKp.le 0
  let label : Fin Bins.card → ℤ := fun e => ((Bins.equivFin).symm e).1
  let center : Fin Bins.card → ℝ := fun e => (label e : ℝ) * ε
  have hcount : (Bins.card : ℝ) ≤ K ^ 10 := by
    have h6 : (6 : ℝ) ≤ K ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 3
      norm_num at hh
      linarith
    calc
      _ ≤ 4 * K / ε + 2 := hBins
      _ = 4 * K ^ 7 + 2 := by dsimp only [ε]; rw [div_inv_eq_mul]; ring
      _ ≤ 6 * K ^ 7 := by have hh := one_le_pow₀ hK1 (n := 7); linarith
      _ ≤ K ^ 3 * K ^ 7 := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = _ := by ring
  let U : Fin p.C → Fin Bins.card → Set Event := fun b e =>
    (H (p.γ b) ∩ p.F b) ∩ {z | ⌊packetSignal Nk p b z / ε⌋ = label e}
  have hU (b : Fin p.C) (e : Fin Bins.card) : MeasurableSet (U b e) := by
    have hm : Measurable (fun z => (⌊packetSignal Nk p b z / ε⌋ : ℤ)) :=
      Int.measurable_floor.comp ((measurable_packetSignal Nk p b).div_const ε)
    exact ((hH _).inter (path_packet_measurable hp b).2).inter (hm (measurableSet_singleton _))
  have hsub (b : Fin p.C) (e : Fin Bins.card) : U b e ⊆ H (p.γ b) ∩ p.F b :=
    fun _ hz => hz.1
  have hfit (b : Fin p.C) (e : Fin Bins.card) (z : Event) (hz : z ∈ U b e) :
      |packetSignal Nk p b z - center e| ≤ ε := by
    have hlo := Int.floor_le (packetSignal Nk p b z / ε)
    have hhi := Int.lt_floor_add_one (packetSignal Nk p b z / ε)
    rw [hz.2] at hlo hhi
    have hlo' := (le_div_iff₀ hε).mp hlo
    have hhi' := (div_lt_iff₀ hε).mp hhi
    dsimp only [center]
    rw [abs_of_nonneg (sub_nonneg.mpr hlo')]
    nlinarith
  have hcovered (b : Fin p.C) (_hb : p.lev b = i) : H (p.γ b) ∩ p.F b ⊆ ⋃ e, U b e := by
    intro z hz
    have hs := path_packet_support hp b hz.2
    have hsig : |packetSignal Nk p b z| ≤ K := by
      rw [packetSignal_eq_normalizedCurve hp]
      exact ((normalizedPacket_native_bounds hp b z.1 hs.2.1 (packetTime p b z)
        (packetTime_unit hp b hz.2)).2.1).trans hκK
    have hin : ⌊packetSignal Nk p b z / ε⌋ ∈ Bins :=
      hcover _ (by simpa only [sub_zero] using hsig)
    let e := Bins.equivFin ⟨_, hin⟩
    refine mem_iUnion.mpr ⟨e, hz, ?_⟩
    change _ = ((Bins.equivFin).symm (Bins.equivFin ⟨_, hin⟩)).1
    simp only [Equiv.symm_apply_apply]
  obtain ⟨V, H', hVm, hVd, hVU, hH', hloss, hfloor, hH'cover⟩ :=
    path_heavy_original_entries hp hν hweight hsum H hH hterminal i hi Bins.card U hU hsub hcovered θ
  refine ⟨Bins.card, center, U, V, H', hcount, fun b e => ⟨hU b e, hVm b e⟩, hVd,
    fun b e => ⟨hVU b e, hsub b e⟩, hfit, hH', hloss.trans ?_, hfloor, hH'cover⟩
  apply mul_le_mul_of_nonneg_right _ zero_le
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcount

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
