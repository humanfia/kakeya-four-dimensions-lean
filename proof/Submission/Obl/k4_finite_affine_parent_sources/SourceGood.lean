-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceEH3
import Submission.Obl.k4_finite_affine_parent_sources.StageMonotonicity

/-!
# The source stage meets `StageGood` and `NativeSource`

`SourceFacts` lists, for one `SourceData`, every input still needed to certify its model:
the numerical schedule, the slack constants `J, τ`, the prepared set (in the residual, in the
open parent block, terminal, avoiding dyadic endpoints), the parent floor, the depth map, the
coefficient budgets, the floors of the prepared set on the model labels, the model prior
floors, the tracking coefficients, the pure/joint/palette caps `EH2` and the per-label
velocity caps. `SourceFacts.good` proves `StageGood ∧ NativeSource`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- All remaining inputs of one source stage. -/
structure Facts (n M m : ℕ) (d₁ κ₁ ℓ S ρ gain ε unit Nk L J τ : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) (H : Fin W → Set Incidence) : Prop where
  num : SourceNumerics n M d₁ ℓ ρ gain ε unit Nk L D.K
  N_ge : (n : ℝ) + 2 ≤ Nk ^ (unit * L)
  νw : IsProbabilityMeasure (ν D.w₀)
  Bw : 0 < B D.w₀
  π_prob : IsProbabilityMeasure D.π
  frame_eq : D.D₀ = MajorFrame.frame (p.frame D.parent)
  J_one : 1 ≤ J
  J_le : J ≤ Nk ^ (ε / 1000000)
  J_slack : 18 * p.κ ≤ J
  τ_pos : 0 < τ
  J_τ : τ⁻¹ ≤ J
  K_τ : τ⁻¹ ≤ D.K
  K_slack : 18 * p.κ ≤ D.K
  S_meas : MeasurableSet D.S
  S_res : D.S ⊆ H D.w₀
  S_open : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀)
  S_term : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀
  S_end : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
    z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)
  prior_pos : 0 < ν D.w₀ (p.assigned D.parent)
  parent_floor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
    ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent)
  depth_mono : Monotone D.depth
  depth_ge : ∀ s, D.i₀ ≤ D.depth s
  depth_lt : ∀ s, D.depth s < m
  depth_err : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
    |p.r (D.depth s) - p.r D.i₀ - unit * L * s| ≤ ρ * unit * L / (1000000 * ((n : ℝ) + 1))
  depth_half : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → p.r (D.depth s) ≤ L / 2
  size : J + Nk ^ (unit * L) + (Nk ^ (unit * L)) ^ ℓ + |δ Nk (p.r D.i₀)| +
      |(δ Nk (p.r D.i₀))⁻¹| + |B D.w₀| + |(B D.w₀)⁻¹| +
      |D.t₀| + |D.q₀| + |D.q₀⁻¹| + ‖p.center D.parent‖ + ‖p.velocity D.parent‖ +
      (∑ e : Fin 4, |(fun _ : Fin 4 => (0 : ℝ)) e|) +
      (∑ e : Fin 2, ∑ e' : Fin 2, (|D.D₀ e e'| + |D.D₀⁻¹ e e'|)) ≤ Nk ^ M
  P_coeff : (∑ e ∈ (D.stage Nk L unit ν B).P.support,
    |(D.stage Nk L unit ν B).P.coeff e|) ≤ Nk ^ M
  time : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
    (Nk ^ (unit * L)) ^ (κ₁ * s) / D.K ≤ (2 : ℝ) ^ D.relT s ∧
    (2 : ℝ) ^ D.relT s ≤ D.K * (Nk ^ (unit * L)) ^ (κ₁ * s)
  thick : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
    p.κ * (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ D.K * (Nk ^ (unit * L)) ^ (-s) ∧
    p.κ / (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ D.K / (Nk ^ (unit * L)) ^ (-s)
  label : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
    ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i)) ∧
    (Nk ^ (unit * L)) ^ (-ℓ * s) / D.K ≤
      |((D.q₀ / (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹)) •
        (D.D₀⁻¹ * p.frame (D.old s i))).det| ∧
    ‖p.velocity (D.old s i)‖ +
      (∑ e : Fin 2, ∑ e' : Fin 2,
        (|p.frame (D.old s i) e e'| + |(p.frame (D.old s i))⁻¹ e e'|)) ≤ Nk ^ M ∧
    (∑ e ∈ ((D.stage Nk L unit ν B).F s i).support,
      |((D.stage Nk L unit ν B).F s i).coeff e|) ≤ Nk ^ M ∧
    ENNReal.ofReal (((Nk ^ (unit * L)) ^ (-s)) ^ d₁ * ((2 : ℝ) ^ (-(D.relT s : ℤ))) ^ 2 *
        (Nk ^ (unit * L)) ^ (-ℓ * s) / D.K) ≤
      (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) ∧
    (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) ≤
      ENNReal.ofReal (D.K * ((Nk ^ (unit * L)) ^ (-s)) ^ d₁ *
        ((2 : ℝ) ^ (-(D.relT s : ℤ))) ^ 2 * (Nk ^ (unit * L)) ^ (-ℓ * s)) ∧
    (∀ e, |D.c s i e| ≤ D.K) ∧
    (∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
      |(exS (D.stage Nk L unit ν B).b l t) 1 - D.c s i 0 - t * D.c s i 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
      |(exS (D.stage Nk L unit ν B).b l t) 2 - D.c s i 2 - t * D.c s i 3 -
          D.c s i 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ * s) ∧
      |(D.stage Nk L unit ν B).b l 4 - D.c s i 3 - D.c s i 4 * (D.stage Nk L unit ν B).b l 3| ≤
        D.K * (Nk ^ (unit * L)) ^ (-ℓ * s))
  vel : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ (i : Fin (p.activeCount D.Hm (D.depth s)))
      (v : ℝ) (v₀ : ℤ), (n : ℝ)⁻¹ ≤ v → v ≤ n →
    (D.stage Nk L unit ν B).μ {z | z.1 ∈ p.assigned (D.old s i) ∧
        z.2 ∈ IS (D.relT s) (D.relBin s i) ∧
        ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (D.K * (2 : ℝ) ^ (-(D.relT s : ℤ))) *
        (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) *
        D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}
  eh2 : EH2 d₁ S (D.stage Nk L unit ν B) n

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Prepared incidences in the open parent block are counted by the parent. -/
theorem S_counted (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀) :
    D.S ⊆ p.counted D.parent := by
  intro z hz
  obtain ⟨bt, hbt, hbtw, hzbt⟩ := hterm hz
  have hlev : p.lev D.parent ≤ p.lev bt := by
    rw [hbt]; have := hp.label_level D.parent; omega
  have hw : p.world bt = p.world D.parent := hbtw
  have hz' := hSo hz
  have hio : z.2 ∈ Ioo ((p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T (p.lev D.parent))
      (((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev D.parent)) := by
    have h := hz'.2
    rw [D.t₀_add_q₀] at h
    exact h
  have hanc := hp.ancestor_eq_of_interior hlev hw hzbt hz'.1 hio
  have h := (hp.ancestor bt (p.lev D.parent) hlev).2.2 hzbt
  rwa [hanc] at h

omit hp in
/-- The parent floor gives the model residual mass. -/
theorem rho_mass {τ : ℝ} (hτ : 0 < τ) (hKτ : τ⁻¹ ≤ D.K) (unit : ℝ)
    [IsFiniteMeasure (ν D.w₀)] (hA₀ : 0 < ν D.w₀ (p.assigned D.parent))
    (hfloor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent)) :
    ENNReal.ofReal (D.K)⁻¹ ≤ (D.stage Nk L unit ν B).ρ Set.univ := by
  show ENNReal.ofReal (D.K)⁻¹ ≤ muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S Set.univ
  rw [muE_apply _ _ _ _ _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
  have hq₀ := D.q₀_pos
  have hpk : ((ν D.w₀).prod volume) (p.packet D.parent) =
      ν D.w₀ (p.assigned D.parent) * ENNReal.ofReal D.q₀ := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    congr 2
    simp only [q₀, i₀]
    rw [← sub_div]; ring
  have hS : ENNReal.ofReal τ * (ν D.w₀ (p.assigned D.parent) * ENNReal.ofReal D.q₀) ≤
      ((ν D.w₀).prod volume) D.S :=
    (hpk ▸ hfloor).trans (measure_mono Set.inter_subset_left)
  set a₀ := ν D.w₀ (p.assigned D.parent)
  have ha₀ : a₀ ≠ 0 := hA₀.ne'
  have ha₀t : a₀ ≠ ⊤ := measure_ne_top _ _
  have hq0 : ENNReal.ofReal D.q₀ ≠ 0 := by simp [hq₀]
  have hprod0 : ENNReal.ofReal D.q₀ * a₀ ≠ 0 := mul_ne_zero hq0 ha₀
  have hprodt : ENNReal.ofReal D.q₀ * a₀ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha₀t
  calc ENNReal.ofReal (D.K)⁻¹ ≤ ENNReal.ofReal τ := ENNReal.ofReal_le_ofReal (by
        have hK0 : 0 < D.K := lt_of_lt_of_le (inv_pos.mpr hτ) hKτ
        exact (inv_le_comm₀ hK0 hτ).mpr hKτ)
    _ = (ENNReal.ofReal D.q₀ * a₀)⁻¹ * (ENNReal.ofReal τ * (a₀ * ENNReal.ofReal D.q₀)) := by
        rw [show ENNReal.ofReal τ * (a₀ * ENNReal.ofReal D.q₀) =
          (ENNReal.ofReal D.q₀ * a₀) * ENNReal.ofReal τ by ring, ← mul_assoc,
          ENNReal.inv_mul_cancel hprod0 hprodt, one_mul]
    _ ≤ _ := by gcongr

/-- The floor of the prepared set gives the residual floor of the certificate. -/
theorem residual_floor {τ J : ℝ} (hτ : 0 < τ) (hJτ : τ⁻¹ ≤ J) (H : Fin W → Set Incidence)
    (hSH : D.S ⊆ H D.w₀) (b : Fin p.C)
    (hfloor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet b) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted b)) :
    ENNReal.ofReal ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) / J) * ν D.w₀ (p.assigned b) ≤
      ((ν D.w₀).prod volume)
        {z | z ∈ H D.w₀ ∧ z.1 ∈ p.assigned b ∧
          z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
            (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))} := by
  have hpk : ((ν D.w₀).prod volume) (p.packet b) =
      ν D.w₀ (p.assigned b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    congr 2
    rw [← sub_div]; ring
  have hsub : D.S ∩ p.counted b ⊆ {z | z ∈ H D.w₀ ∧ z.1 ∈ p.assigned b ∧
      z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))} := fun z hz =>
    ⟨hSH hz.1, (hp.counted_support b z hz.2).2.1, (hp.counted_support b z hz.2).2.2.1⟩
  refine le_trans ?_ ((hpk ▸ hfloor).trans (measure_mono hsub))
  have hJ0 : 0 < J := lt_of_lt_of_le (inv_pos.mpr hτ) hJτ
  have hqb : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by positivity
  have hle : ENNReal.ofReal ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) / J) ≤
      ENNReal.ofReal τ * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) := by
    rw [← ENNReal.ofReal_mul hτ.le]
    apply ENNReal.ofReal_le_ofReal
    have h1 : J⁻¹ ≤ τ := (inv_le_comm₀ hJ0 hτ).mpr hJτ
    calc ((2 : ℝ) ^ p.T (p.lev b))⁻¹ / J = J⁻¹ * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by ring
      _ ≤ τ * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by gcongr
  calc ENNReal.ofReal ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) / J) * ν D.w₀ (p.assigned b)
      ≤ ENNReal.ofReal τ * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
          ν D.w₀ (p.assigned b) := by gcongr
    _ = _ := by ring

/-- **The source stage is a good finite model with its source certificate.** -/
theorem Facts.good {n M : ℕ} {d₁ S ρ gain ε unit J τ : ℝ} {H : Fin W → Set Incidence}
    (hf : D.Facts n M m d₁ κ₁ ℓ S ρ gain ε unit Nk L J τ ν B H) :
    StageGood d₁ κ₁ ℓ S n (D.stage Nk L unit ν B) ∧
      NativeSource n M d₁ ℓ ρ gain ε unit Nk L ν B p H (D.stage Nk L unit ν B) := by
  have := hf.νw
  have hc := hp.chart D.parent
  have hScount := D.S_counted hp hf.S_open hf.S_term
  have hdet : D.D₀.det ≠ 0 := by rw [hf.frame_eq]; exact MajorFrame.det_ne_zero hc.1
  refine ⟨?_, ?_⟩
  · -- StageGood
    have hNst : (1 : ℝ) ≤ Nk ^ (unit * L) := by linarith [hf.num.two_le_Nst]
    have hKmax : D.K ≤ (Nk ^ (unit * L)) ^ (1 / ((n : ℝ) + 1)) := by
      refine hf.num.K_le.trans (Real.rpow_le_rpow_of_exponent_le hNst ?_)
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ (by positivity) hn0]
      nlinarith [hf.num.ρ_le, hf.num.ρ_pos]
    refine stageGood_of_max_range d₁ κ₁ ℓ S n (D.stage Nk L unit ν B) hf.N_ge
      hf.num.one_le_K hKmax ?_ hf.eh2 ?_ ?_
    · exact D.eh1_stage hp unit hf.νw hf.Bw hf.frame_eq hf.π_prob hf.K_slack hf.S_meas
        hf.S_open hScount hf.prior_pos.ne'
        (D.rho_mass hf.τ_pos hf.K_τ unit hf.prior_pos hf.parent_floor)
    · refine D.eh3_stage hp unit d₁ κ₁ ℓ n hf.τ_pos hf.K_τ (by linarith [hp.one_le_slack, hf.K_slack])
        hf.Bw hf.frame_eq hf.S_meas hf.S_open hf.S_term hf.S_end
        (fun s _ _ => ⟨hf.depth_ge s, by have := hf.depth_lt s; omega, hf.depth_lt s⟩)
        hf.time hf.thick ?_ hf.vel
      intro s hs1 hs2 i
      obtain ⟨hfl, -, -, -, hlo, hup, hcc, htr⟩ := hf.label s hs1 hs2 i
      exact ⟨hfl, hlo, hup, hcc, htr⟩
    · exact D.eh4_stage hp unit hf.depth_mono hf.depth_ge hf.S_open 1 n
  · -- NativeSource
    have hSH : D.S ⊆ H D.w₀ ∩ (p.assigned D.parent ×ˢ Icc D.t₀ (D.t₀ + D.q₀)) := fun z hz =>
      ⟨hf.S_res hz, (hf.S_open hz).1, Ioo_subset_Icc_self (hf.S_open hz).2⟩
    refine D.nativeSource H hp hf.num hf.νw hf.Bw hdet hf.prior_pos J hf.J_one hf.J_le
      hf.J_slack (fun l hl t ht => (D.parent_tube hp hf.frame_eq l hl t ht).1) hSH hf.S_open
      hf.size hf.P_coeff (fun s hs1 hs2 => ⟨hf.depth_ge s, hf.depth_err s hs1 hs2,
        hf.depth_half s hs1 hs2⟩) ?_
    intro s hs1 hs2 i
    obtain ⟨hfl, hdt, hvb, hF, -⟩ := hf.label s hs1 hs2 i
    exact ⟨hdt, D.residual_floor hp hf.τ_pos hf.J_τ H hf.S_res (D.old s i) hfl, hvb, hF⟩

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
