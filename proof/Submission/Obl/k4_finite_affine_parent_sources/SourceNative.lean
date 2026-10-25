-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceStage

/-!
# The `NativeSource` certificate of a source stage

`SourceData.nativeSource` proves the frozen `NativeSource` certificate for the model
`SourceData.stage`, from: the numerical schedule, the slack `J`, the prepared set lying in the
residual and in the open parent block, and facts on the old labels behind the model labels
(depth, determinant, residual floors, coefficient budgets). The coordinate equalities
(`st.N`, `st.b`, `st.ν`), the residual domination, worlds, assignments and relative blocks
are discharged here.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface

noncomputable section

namespace PFrame

/-- The tube of a parent chart bounds the normalized base coefficients. -/
theorem eb_coeff_bound (Φ : PFrame) (hq : 0 < Φ.F.q) (l : ℕ × (Fin 6 → ℝ)) (κ : ℝ)
    (htube : ∀ t ∈ Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q),
      ‖Matrix.toEuclideanLin Φ.F.D⁻¹ (gy l t - Φ.F.c - t • Φ.F.u)‖ ≤ κ) :
    |Φ.eb l 0| + |Φ.eb l 1| + |Φ.eb l 3| + |Φ.eb l 4| ≤ 6 * κ := by
  have hq0 : Φ.F.q ≠ 0 := hq.ne'
  have hb0 : Φ.F.t₀ ∈ Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q) := ⟨le_rfl, by linarith⟩
  have hb1 : Φ.F.t₀ + Φ.F.q ∈ Icc Φ.F.t₀ (Φ.F.t₀ + Φ.F.q) := ⟨by linarith, le_rfl⟩
  have h0' := htube _ hb0
  have h1' := htube _ hb1
  rw [Φ.toEuclideanLin_offset hq0] at h0' h1'
  have e0 : (Φ.F.t₀ - Φ.F.t₀) / Φ.F.q = 0 := by simp
  have e1 : (Φ.F.t₀ + Φ.F.q - Φ.F.t₀) / Φ.F.q = 1 := by field_simp; ring
  rw [e0] at h0'; rw [e1] at h1'
  simp only [zero_mul, add_zero, one_mul] at h0' h1'
  have c0 : |Φ.eb l 0| ≤ κ := by
    have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0, Φ.eb l 1]) 0
    simp at hc; linarith
  have c1 : |Φ.eb l 1| ≤ κ := by
    have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0, Φ.eb l 1]) 1
    simp at hc; linarith
  have d0 : |Φ.eb l 0 + Φ.eb l 3| ≤ κ := by
    have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0 + Φ.eb l 3, Φ.eb l 1 + Φ.eb l 4]) 0
    simp at hc; linarith
  have d1 : |Φ.eb l 1 + Φ.eb l 4| ≤ κ := by
    have hc := PiLp.norm_apply_le (WithLp.toLp 2 ![Φ.eb l 0 + Φ.eb l 3, Φ.eb l 1 + Φ.eb l 4]) 1
    simp at hc; linarith
  have e3 : |Φ.eb l 3| ≤ 2 * κ := by
    calc |Φ.eb l 3| = |(Φ.eb l 0 + Φ.eb l 3) - Φ.eb l 0| := by ring_nf
      _ ≤ |Φ.eb l 0 + Φ.eb l 3| + |Φ.eb l 0| := abs_sub _ _
      _ ≤ 2 * κ := by linarith
  have e4 : |Φ.eb l 4| ≤ 2 * κ := by
    calc |Φ.eb l 4| = |(Φ.eb l 1 + Φ.eb l 4) - Φ.eb l 1| := by ring_nf
      _ ≤ |Φ.eb l 1 + Φ.eb l 4| + |Φ.eb l 1| := abs_sub _ _
      _ ≤ 2 * κ := by linarith
  linarith

end PFrame

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

theorem q₀_pos : 0 < D.q₀ := by unfold q₀; positivity

theorem frame_F (Nk : ℝ) (B : Fin W → ℝ) :
    (D.frame Nk B).F = ⟨D.t₀, D.q₀, p.center D.parent, p.velocity D.parent, D.D₀⟩ := rfl

/-- The model coefficients are the frozen affine source coefficients without correction. -/
theorem stage_b (Nk L unit : ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) :
    (D.stage Nk L unit ν B).b = AffineCoefficients D.t₀ D.q₀ (B D.w₀ / δ Nk (p.r D.i₀))
      (p.center D.parent) (p.velocity D.parent) D.D₀ (fun _ => 0) := by
  rw [affineCoefficients_eq_hiddenShear]
  funext l e
  fin_cases e <;>
    simp [stage, frame, hiddenShear, Submission.Lib.K4ContactNormalization.residualCoeff]

/-- The model residual is dominated by the normalized original residual. -/
theorem stage_ρ_le (Nk L unit : ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (H : Fin W → Set Incidence) {J : ℝ} (hJ : 1 ≤ J)
    (hSH : D.S ⊆ H D.w₀ ∩ (p.assigned D.parent ×ˢ Icc D.t₀ (D.t₀ + D.q₀))) :
    (D.stage Nk L unit ν B).ρ ≤ ENNReal.ofReal J •
      ((ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ •
        Measure.map (fun z : Incidence => (z.1, (z.2 - D.t₀) / D.q₀))
          (((ν D.w₀).prod volume).restrict
            (H D.w₀ ∩ (p.assigned D.parent ×ˢ Icc D.t₀ (D.t₀ + D.q₀))))) := by
  have h1 : (D.stage Nk L unit ν B).ρ ≤
      (ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ •
        Measure.map (fun z : Incidence => (z.1, (z.2 - D.t₀) / D.q₀))
          (((ν D.w₀).prod volume).restrict
            (H D.w₀ ∩ (p.assigned D.parent ×ˢ Icc D.t₀ (D.t₀ + D.q₀)))) := by
    show muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S ≤ _
    exact muE_mono (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ hSH
  refine h1.trans ?_
  refine Measure.le_iff'.2 fun s => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  have hJ' : (1 : ENNReal) ≤ ENNReal.ofReal J := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hJ
  exact le_mul_of_one_le_left (zero_le) hJ'

/-- The purely numerical part of the source certificate. -/
structure SourceNumerics (n M : ℕ) (d₁ ℓ ρ gain ε unit Nk L K : ℝ) : Prop where
  two_le_n : 2 ≤ n
  one_le_M : 1 ≤ M
  two_le_Nk : 2 ≤ Nk
  L_pos : 0 < L
  d₁_nonneg : 0 ≤ d₁
  ℓ_pos : 0 < ℓ
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1 / 4
  ε_pos : 0 < ε
  unit_pos : 0 < unit
  unit_n : unit * n ≤ 1 / 8
  gain_pos : 0 < gain
  gain_le : gain ≤ ρ * unit / (1000000 * ((n : ℝ) + 1))
  hundred_le : 100 ≤ Nk ^ (ε / 1000000)
  two_le_Nst : 2 ≤ Nk ^ (unit * L)
  one_le_K : 1 ≤ K
  K_le : K ≤ (Nk ^ (unit * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1)))

/-- **The source certificate.** All coordinate identities, the residual domination and the
label bookkeeping are proved; the remaining label facts are hypotheses on the old labels. -/
theorem nativeSource {n M : ℕ} {d₁ ℓ ρ gain ε unit Nk L : ℝ}
    {ν : Fin W → Measure Trajectory} {B : Fin W → ℝ} (H : Fin W → Set Incidence)
    {m Mp Dp : ℕ} {κ₁ δ₀ σ : ℝ} {ω : Fin W → ℝ} {E : Fin W → Set Incidence}
    {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)
    (hnum : SourceNumerics n M d₁ ℓ ρ gain ε unit Nk L D.K)
    (hνw : IsProbabilityMeasure (ν D.w₀)) (hBw : 0 < B D.w₀) (hD₀ : D.D₀.det ≠ 0)
    (hA₀ : 0 < ν D.w₀ (p.assigned D.parent))
    (J : ℝ) (hJ1 : 1 ≤ J) (hJ2 : J ≤ Nk ^ (ε / 1000000)) (hJκ : 18 * p.κ ≤ J)
    (htube : ∀ l ∈ p.assigned D.parent, ∀ t ∈ Icc D.t₀ (D.t₀ + D.q₀),
      ‖Matrix.toEuclideanLin D.D₀⁻¹ (gy l t - p.center D.parent - t • p.velocity D.parent)‖ ≤
        3 * p.κ)
    (hSH : D.S ⊆ H D.w₀ ∩ (p.assigned D.parent ×ˢ Icc D.t₀ (D.t₀ + D.q₀)))
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hsize : J + Nk ^ (unit * L) + (Nk ^ (unit * L)) ^ ℓ + |δ Nk (p.r D.i₀)| +
      |(δ Nk (p.r D.i₀))⁻¹| + |B D.w₀| + |(B D.w₀)⁻¹| +
      |D.t₀| + |D.q₀| + |D.q₀⁻¹| + ‖p.center D.parent‖ + ‖p.velocity D.parent‖ +
      (∑ e : Fin 4, |(fun _ : Fin 4 => (0 : ℝ)) e|) +
      (∑ e : Fin 2, ∑ e' : Fin 2, (|D.D₀ e e'| + |D.D₀⁻¹ e e'|)) ≤ Nk ^ M)
    (hP : (∑ e ∈ (D.stage Nk L unit ν B).P.support,
      |(D.stage Nk L unit ν B).P.coeff e|) ≤ Nk ^ M)
    (hdepth : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      D.i₀ ≤ D.depth s ∧
      |p.r (D.depth s) - p.r D.i₀ - unit * L * s| ≤ ρ * unit * L / (1000000 * ((n : ℝ) + 1)) ∧
      p.r (D.depth s) ≤ L / 2)
    (hlabel : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      (Nk ^ (unit * L)) ^ (-ℓ * s) / D.K ≤
        |((D.q₀ / (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹)) •
          (D.D₀⁻¹ * p.frame (D.old s i))).det| ∧
      ENNReal.ofReal ((((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹) / J) *
        ν D.w₀ (p.assigned (D.old s i)) ≤
        ((ν D.w₀).prod volume)
          {z | z ∈ H D.w₀ ∧ z.1 ∈ p.assigned (D.old s i) ∧
            z.2 ∈ Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
              (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))} ∧
      ‖p.velocity (D.old s i)‖ +
        (∑ e : Fin 2, ∑ e' : Fin 2,
          (|p.frame (D.old s i) e e'| + |(p.frame (D.old s i))⁻¹ e e'|)) ≤ Nk ^ M ∧
      (∑ e ∈ ((D.stage Nk L unit ν B).F s i).support,
        |((D.stage Nk L unit ν B).F s i).coeff e|) ≤ Nk ^ M) :
    NativeSource n M d₁ ℓ ρ gain ε unit Nk L ν B p H (D.stage Nk L unit ν B) := by
  have hq₀ := D.q₀_pos
  refine ⟨hnum.two_le_n, hnum.one_le_M, hnum.two_le_Nk, hnum.L_pos, hnum.d₁_nonneg,
    hnum.ℓ_pos, hnum.ρ_pos, hnum.ρ_le, hnum.ε_pos, hnum.unit_pos, hnum.unit_n,
    hnum.gain_pos, hnum.gain_le, hnum.hundred_le, rfl, hnum.two_le_Nst, hnum.one_le_K,
    hnum.K_le, ?_⟩
  refine ⟨D.parent, J, D.t₀, D.q₀, p.center D.parent, p.velocity D.parent, D.D₀,
    (fun _ => 0), D.old, hJ1, hJ2, by linarith [hp.one_le_slack], hνw,
    (hp.chart D.parent).2.2.2.2.2.2.1, hA₀, hBw, rfl, rfl, hD₀,
    D.stage_b Nk L unit ν B, rfl, D.stage_ρ_le Nk L unit ν B H hJ1 hSH, ?_, hsize, hP, ?_⟩
  · intro l hl
    have h := (D.frame Nk B).eb_coeff_bound hq₀ l (3 * p.κ) (htube l hl)
    show |(D.frame Nk B).eb l 0| + |(D.frame Nk B).eb l 1| + |(D.frame Nk B).eb l 3| +
      |(D.frame Nk B).eb l 4| ≤ J
    linarith
  · intro s hs1 hs2 i
    obtain ⟨hi₀, hdep, hhalf⟩ := hdepth s hs1 hs2
    obtain ⟨hdet, hfl, hvel, hF⟩ := hlabel s hs1 hs2 i
    obtain ⟨hw, -⟩ := D.old_world s i
    refine ⟨hw, rfl, D.old_assigned_subset hp hSo s hi₀ i,
      (hp.chart (D.old s i)).2.2.2.2.2.2.1, le_rfl, ?_,
      D.old_relBin_mem hp hSo s hi₀ i, ?_, ?_, hdet, hfl, hvel, hF⟩
    · -- positive prior of a met label: from its saturated counted mass
      have hsat := (hp.saturation (D.old s i)).1
      have hdet0 : (p.frame (D.old s i)).det ≠ 0 := (hp.chart (D.old s i)).1
      have hpos : 0 < ((ν (p.world (D.old s i))).prod volume) (p.counted (D.old s i)) := by
        refine lt_of_lt_of_le ?_ hsat
        apply ENNReal.ofReal_pos.mpr
        have := hp.one_le_slack
        have hN0 : 0 < Nk := by linarith [hnum.two_le_Nk]
        apply div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) (abs_pos.mpr hdet0))
        exact mul_pos (by positivity) (by linarith)
      have hsub : p.counted (D.old s i) ⊆ p.packet (D.old s i) := fun z hz =>
        ⟨(hp.counted_support _ z hz).2.1, (hp.counted_support _ z hz).2.2.1⟩
      have hpk := lt_of_lt_of_le hpos (measure_mono hsub)
      rw [PathData.packet, Measure.prod_prod] at hpk
      have hw' : p.world (D.old s i) = p.world D.parent := hw
      rw [← hw']
      exact pos_of_ne_zero (fun h0 => by simp [h0] at hpk)
    · rw [D.old_level s i]; exact hdep
    · rw [D.old_level s i]; exact hhalf

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
