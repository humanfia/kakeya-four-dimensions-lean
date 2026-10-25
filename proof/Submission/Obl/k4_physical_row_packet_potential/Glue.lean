/-
x1077 (o295). The row-packet glue: a qualified row packet gives the frozen
physical potential packet, once the precision exponent `Ep` satisfies the
numerical goal `NumericsGoal` of `GlueNumerics`.

1. `qualified_state_preparation` (x1083): whole states of `Se` with at most
   `1/100` unqualified mass, a measurable qualified set `Q` and the set `E0`.
2. `Cartesian.frozen_field_long_fits` on `E0`, with the line law restricted to
   `A` (so its short-line loss is measured against `ν A`): the field `Tf`, its
   long fit times and the set `S`, each surviving state keeping half its mass.
3. `Switch.PacketSwitching.frozen_packet_final_of_velocity_bins` on `S`: the
   frozen clauses pass from `Se` to `S` (monotone, or per state with factor 2
   through `StateBreadth`), and the numerics close the widths.
-/
import Submission.Obl.k4_physical_row_packet_potential.RowInterface
import Submission.Obl.k4_physical_row_packet_potential.GlueNumerics
import Submission.Obl.k4_physical_row_packet_potential.GlueLemmas
import Submission.Obl.k4_physical_row_packet_potential.Switch.FiniteBinPacketFinal
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.FieldLongFits
import Submission.Obl.k4_physical_row_packet_potential.QualificationPreparation
import Submission.Obl.k4_physical_row_packet_potential.StateBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Glue

open MeasureTheory Set
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal RealInnerProductSpace

noncomputable section

theorem kint_ge (Kc : ℝ) (hK : 1 ≤ Kc) : Kc + 1 ≤ Kint Kc ∧ 8 * Kc ^ 202 ≤ Kint Kc := by
  have h1 : Kc ≤ Kc ^ 202 := by
    calc Kc = Kc ^ 1 := (pow_one Kc).symm
      _ ≤ Kc ^ 202 := pow_le_pow_right₀ hK (by norm_num)
  have h2 : 1 ≤ Kc ^ 202 := one_le_pow₀ hK
  unfold Kint
  constructor <;> nlinarith

theorem c0_bounds : 1 / 2 ≤ c0 ∧ c0 ≤ 1 := by
  unfold c0
  constructor <;> norm_num

set_option maxHeartbeats 8000000 in
/-- **The row-packet glue.** -/
theorem row_packet_potential_of_numerics (M : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e cNorm cCurl : ℕ, ∀ (d₁ : ℝ), d₁ < 1 → ∀ Ep : ℕ,
      NumericsGoal M d₁ C e cNorm cCurl Ep →
      ∀ q : ℕ, 3 * M + 1 ≤ q → ∀ (precision loss Nk L gain κ : ℝ) (ν : Measure Ln) (B r : ℝ)
        (T j : ℕ) (c u : P2) (P : Po) (A : Set Ln) (F H : Set Ev),
        RowPacket M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H →
        PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H := by
  obtain ⟨C, hC, e, hfield⟩ := Cartesian.frozen_field_long_fits M
  obtain ⟨cNorm, cCurl, hfin⟩ :=
    Switch.PacketSwitching.frozen_packet_final_of_velocity_bins (3 * M)
  refine ⟨C, hC, e, cNorm, cCurl, ?_⟩
  intro d₁ hd₁ Ep hnum q hq precision loss Nk L gain κ ν B r T j c u P A F H hRow
  obtain ⟨Kc, ε, pv, θ, Se, Er, st, Gs, pal, hνprob, hPdeg, hAm, hε, hεζ, hεa, ha, haK, hhζ, hζ1,
    hK2, hκK, hKN, hθ, hεθ, hpv, hpvθ, hSem, hSeHF, hSeEr, hSeA, href, hmass, hpts, hceil, hband,
    hcount, hstm, hstfin, hrefine, hstrip, hpalP, hpal, hGs, hgraph, hlists, hqual⟩ := hRow
  have := hνprob
  have := hpalP
  ------------------------------------------------------------------
  -- scales and constants
  ------------------------------------------------------------------
  have hh0 : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hζ0 : 0 < δ Nk (precision * gain * L) := hh0.trans_le hhζ
  have hKc0 : 0 < Kc := by linarith
  have hKc1 : 1 ≤ Kc := by linarith
  obtain ⟨nKf, nKint, nAT, nK101, nbin, neps, nerr⟩ :=
    hnum Kc (δ Nk r) ((2 : ℝ) ^ T)⁻¹ (δ Nk (precision * gain * L)) hK2 ha hh0 haK hζ0 hζ1
  obtain ⟨hKi1', hKi8⟩ := kint_ge Kc hKc1
  have hKi1 : 1 ≤ Kint Kc := by linarith
  have hKcKi : Kc ≤ Kint Kc := by linarith
  have hKi0 : 0 < Kint Kc := by linarith
  have hKie : 1 ≤ Kint Kc ^ e := one_le_pow₀ hKi1
  have hAT1 : 1 ≤ AT C e Kc := by
    unfold AT
    nlinarith
  have hAT0 : 0 ≤ AT C e Kc := by linarith
  obtain ⟨hc0half, hc01⟩ := c0_bounds
  have hc0pos : 0 < c0 := by linarith
  have hKc4 : 1 ≤ Kc ^ 4 := one_le_pow₀ hKc1
  have hKcKf : Kc ≤ Kf M C e Kc := by
    unfold Kf
    have hM : (1 : ℝ) ≤ 3 * (M : ℝ) + 1 := by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    have h1 : Kc ≤ Kc ^ 4 := by
      calc Kc = Kc ^ 1 := (pow_one Kc).symm
        _ ≤ Kc ^ 4 := pow_le_pow_right₀ hKc1 (by norm_num)
    have h2 : Kc ^ 4 ≤ (3 * (M : ℝ) + 1) * Kc ^ 4 := by nlinarith
    have h3 : (3 * (M : ℝ) + 1) * Kc ^ 4 ≤ (3 * (M : ℝ) + 1) * Kc ^ 4 * AT C e Kc := by
      have : 0 ≤ (3 * (M : ℝ) + 1) * Kc ^ 4 := by positivity
      nlinarith
    nlinarith
  have hKf0 : 0 < Kf M C e Kc := by linarith
  have hKf2 : 2 ≤ Kf M C e Kc := by linarith
  have hEp0 : 0 < Kc ^ Ep := by positivity
  have hKcEp : Kc ≤ Kc ^ Ep := by
    have h1 : Kc ≤ Kc ^ 101 := by
      calc Kc = Kc ^ 1 := (pow_one Kc).symm
        _ ≤ Kc ^ 101 := pow_le_pow_right₀ hKc1 (by norm_num)
    nlinarith [pow_pos hKc0 101]
  have hEp1 : 1 ≤ Kc ^ Ep := hKc1.trans hKcEp
  have hah : δ Nk r / ((2 : ℝ) ^ T)⁻¹ ≤ Kc := (div_le_iff₀ hh0).mpr haK
  have hah0 : 0 < δ Nk r / ((2 : ℝ) ^ T)⁻¹ := div_pos ha hh0
  have hζEp : δ Nk (precision * gain * L) ^ Ep ≤ 1 := pow_le_one₀ hζ0.le hζ1
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθKc : θ ≤ Kc / Kc ^ Ep := by
    rw [hθ]
    apply div_le_div_of_nonneg_right _ hEp0.le
    calc δ Nk r / ((2 : ℝ) ^ T)⁻¹ * δ Nk (precision * gain * L) ^ Ep ≤ Kc * 1 :=
          mul_le_mul hah hζEp (by positivity) hKc0.le
      _ = Kc := mul_one Kc
  have hθ1 : θ ≤ 1 := hθKc.trans ((div_le_one hEp0).mpr hKcEp)
  have hεθ' : ε ≤ θ / Kc ^ Ep := by
    rw [le_div_iff₀ hEp0]
    linarith
  have hpvθ' : pv ≤ θ / Kc ^ Ep := by
    rw [le_div_iff₀ hEp0]
    linarith
  have hθratio : θ / Kc ^ Ep =
      δ Nk r / ((2 : ℝ) ^ T)⁻¹ * δ Nk (precision * gain * L) ^ Ep / Kc ^ Ep / Kc ^ Ep := by
    rw [hθ]
  -- the long-line threshold
  have hCcomb : Ccomb C e Kc = Kc ^ 3 / c0 * AT C e Kc := rfl
  have hCcomb1 : 1 ≤ Ccomb C e Kc := by
    rw [hCcomb]
    have h8 : 1 ≤ Kc ^ 3 := one_le_pow₀ hKc1
    have h1 : 1 ≤ Kc ^ 3 / c0 := by
      rw [le_div_iff₀ hc0pos]
      nlinarith
    nlinarith
  have hη0 : 0 < eta C e Kc := by
    unfold eta
    have : 0 < Ccomb C e Kc := by linarith
    positivity
  have hη1 : eta C e Kc ≤ 1 := by
    unfold eta
    rw [div_le_one (by positivity)]
    nlinarith
  have hηC : eta C e Kc * Ccomb C e Kc = 1 / (12 * Kc) := by
    unfold eta
    have : 0 < Ccomb C e Kc := by linarith
    field_simp
  have h4KcC : 4 * Kc * Ccomb C e Kc ≤ Kf M C e Kc := by
    rw [hCcomb]
    unfold Kf
    have hM : (1 : ℝ) ≤ 3 * (M : ℝ) + 1 := by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    have h1 : 4 * Kc * (Kc ^ 3 / c0 * AT C e Kc) = (4 / c0) * (Kc ^ 4 * AT C e Kc) := by
      field_simp
    have h2 : 4 / c0 ≤ 8 := by
      rw [div_le_iff₀ hc0pos]
      linarith
    have h3 : 0 ≤ Kc ^ 4 * AT C e Kc := by positivity
    rw [h1]
    nlinarith
  ------------------------------------------------------------------
  -- the measure, the reference mass and its window
  ------------------------------------------------------------------
  have hSeA' : Se ⊆ A ×ˢ univ := fun p hp => ⟨(hSeA p hp).1, trivial⟩
  have hSewin : Se ⊆ univ ×ˢ Icc (start T j) (start T j + clock T) := by
    intro p hp
    refine ⟨trivial, ?_⟩
    have h1 := (hSeA p hp).2.1
    change p.2 ∈ Icc ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹) ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹)
    exact ⟨h1.1, by linarith [h1.2]⟩
  have hSunitSe : Se ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => ⟨trivial, (hSeA p hp).2.2⟩
  have hμSe_fin : (ν.prod volume) Se ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hSewin)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [Real.volume_Icc])
  haveI : IsFiniteMeasure ((ν.prod volume).restrict Se) :=
    isFiniteMeasure_restrict.mpr hμSe_fin
  have hνA_fin : ν A ≠ ⊤ := measure_ne_top ν A
  have hrefm : ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A =
      ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (ν A).toReal) := by
    rw [ENNReal.ofReal_mul hh0.le, ENNReal.ofReal_toReal hνA_fin]
  have hm0 : 0 < ((2 : ℝ) ^ T)⁻¹ * (ν A).toReal := by
    have : 0 < ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (ν A).toReal) := hrefm ▸ href
    exact ENNReal.ofReal_pos.mp this
  have hSe_real : ((2 : ℝ) ^ T)⁻¹ * (ν A).toReal / Kc ≤ (ν.prod volume).real Se := by
    have h1 : ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (ν A).toReal / Kc) ≤ (ν.prod volume) Se := by
      rw [ENNReal.ofReal_div_of_pos hKc0, ← hrefm]
      simpa only [Measure.restrict_apply_univ] using hmass
    exact (ENNReal.ofReal_le_iff_le_toReal hμSe_fin).mp h1
  ------------------------------------------------------------------
  -- 1. whole qualified states
  ------------------------------------------------------------------
  have hconc : ((ν.prod volume).restrict Se) Seᶜ = 0 := by
    rw [Measure.restrict_apply hSem.compl, compl_inter_self, measure_empty]
  obtain ⟨E0, Q, hE0m, hQm, hE0Se, hQsub, hsat, hhalfE0, -, hqualSt⟩ :=
    qualified_state_preparation ((ν.prod volume).restrict Se) Se hSem hconc st hstm
      {w | Cartesian.QualWitness Er st Gs (start T j) (clock T) M Kc θ (1 / Kc) w} hqual
  have hE0A : E0 ⊆ A ×ˢ univ := hE0Se.trans hSeA'
  have hμsE0 : ((ν.prod volume).restrict Se).restrict E0 = (ν.prod volume).restrict E0 := by
    rw [Measure.restrict_restrict hE0m, inter_eq_left.mpr hE0Se]
  have hν'E0 : ((ν.restrict A).prod volume).restrict E0 = (ν.prod volume).restrict E0 :=
    prod_restrict_line_set_restrict ν hAm hE0A
  have hE0fin : (ν.prod volume) E0 ≠ ⊤ := ne_top_of_le_ne_top hμSe_fin (measure_mono hE0Se)
  have hE0_real : (ν.prod volume).real Se / 2 ≤ (ν.prod volume).real E0 := by
    have h1 : (1 / 2 : ℝ≥0∞) * (ν.prod volume) Se ≤ (ν.prod volume) E0 := by
      have h := hhalfE0
      rwa [Measure.restrict_apply_univ, Measure.restrict_apply hE0m,
        inter_eq_left.mpr hE0Se] at h
    have h2 := ENNReal.toReal_mono hE0fin h1
    rw [ENNReal.toReal_mul] at h2
    have h3 : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
      rw [ENNReal.toReal_div]
      simp
    rw [h3] at h2
    rw [measureReal_def, measureReal_def]
    linarith
  have hE0pos : 0 < (ν.prod volume).real E0 := by
    have : 0 < ((2 : ℝ) ^ T)⁻¹ * (ν A).toReal / Kc := by positivity
    linarith
  have hfloor : ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A ≤
      ENNReal.ofReal (2 * Kc) * (ν.prod volume) E0 := by
    rw [hrefm, ← ENNReal.ofReal_toReal hE0fin, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ((2 : ℝ) ^ T)⁻¹ * (ν A).toReal ≤ Kc * (ν.prod volume).real Se := by
      rw [div_le_iff₀ hKc0] at hSe_real
      linarith
    have h2 : (ν.prod volume).real Se ≤ 2 * ((ν.prod volume) E0).toReal := by
      rw [← measureReal_def]
      linarith
    nlinarith
  ------------------------------------------------------------------
  -- 2. the interpolated field with long fits
  ------------------------------------------------------------------
  obtain ⟨code, hcode⟩ : ∃ code : ℕ → Fin 3 → ℤ,
      ∀ x, code (st x) = fun i => ⌊Cartesian.packetZ T j c u x i / ε⌋ := by
    classical
    refine ⟨fun D => if hD : ∃ y, st y = D then
      (fun i => ⌊Cartesian.packetZ T j c u (Classical.choose hD) i / ε⌋) else 0, ?_⟩
    intro x
    have hD : ∃ y, st y = st x := ⟨x, rfl⟩
    dsimp only
    rw [dif_pos hD]
    have h1 := congrArg Prod.fst (hrefine _ _ (Classical.choose_spec hD))
    exact h1
  have hcz := Cartesian.state_center_of_base_code T j c u st code hε hcode
  set cz : ℕ → Fin 3 → ℝ := fun D i => ε * ((code D i : ℝ) + 1 / 2) with hcz_def
  set Fam : Finset ℕ := hstfin.toFinset with hFam_def
  have hFam : ∀ x ∈ E0, st x ∈ Fam := fun x hx =>
    hstfin.mem_toFinset.mpr ⟨x, hE0Se hx, rfl⟩
  have hFamSe : ∀ D ∈ Fam, ∃ x ∈ Se, st x = D := fun D hD => hstfin.mem_toFinset.mp hD
  have hξ0 : 0 < θ / (30 * Kint Kc ^ 2) := by positivity
  have hξθ : θ / (30 * Kint Kc ^ 2) ≤ θ := by
    apply div_le_self hθ0.le
    nlinarith [one_le_pow₀ (n := 2) hKi1]
  have hθEpξ : θ / Kc ^ Ep ≤ θ / (30 * Kint Kc ^ 2) :=
    div_le_div_of_nonneg_left hθ0.le (by positivity) nKint
  have hCξ : C * Kint Kc ^ e * (θ / (30 * Kint Kc ^ 2)) ≤ 1 := by
    have h1 : C * Kint Kc ^ e = AT C e Kc := rfl
    rw [h1]
    calc AT C e Kc * (θ / (30 * Kint Kc ^ 2)) ≤ AT C e Kc * θ :=
          mul_le_mul_of_nonneg_left hξθ hAT0
      _ ≤ AT C e Kc * (Kc / Kc ^ Ep) := mul_le_mul_of_nonneg_left hθKc hAT0
      _ = AT C e Kc * Kc / Kc ^ Ep := by ring
      _ ≤ 1 := (div_le_one hEp0).mpr nAT
  have hεξ : ε ≤ θ / (30 * Kint Kc ^ 2) := hεθ'.trans hθEpξ
  have hpvξ : pv / 2 ≤ θ / (30 * Kint Kc ^ 2) := by
    have := hpvθ'.trans hθEpξ
    linarith
  have hwv : (Kc ^ (-100 : ℝ)) = (Kc ^ 100)⁻¹ := by
    rw [show (-100 : ℝ) = -((100 : ℕ) : ℝ) by norm_num, Real.rpow_neg hKc0.le,
      Real.rpow_natCast]
  have hwv0 : 0 < Kc ^ (-100 : ℝ) := Real.rpow_pos_of_pos hKc0 _
  have hpvwv : pv ≤ Kc ^ (-100 : ℝ) / 2 := by
    rw [hwv]
    have h1 : pv ≤ Kc / Kc ^ Ep / Kc ^ Ep :=
      hpvθ'.trans (div_le_div_of_nonneg_right hθKc hEp0.le)
    have h2 : Kc / Kc ^ Ep / Kc ^ Ep ≤ (Kc ^ 100)⁻¹ / 2 := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have h3 : 2 * Kc ^ 101 ≤ Kc ^ Ep * Kc ^ Ep := by nlinarith
      have h4 : (Kc ^ 100)⁻¹ / 2 * (Kc ^ Ep * Kc ^ Ep) ≥ (Kc ^ 100)⁻¹ / 2 * (2 * Kc ^ 101) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : (Kc ^ 100)⁻¹ / 2 * (2 * Kc ^ 101) = Kc := by
        field_simp
      linarith
    linarith
  have hpv1 : pv ≤ 1 := by
    have : Kc ^ (-100 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hKc1 (by norm_num)
    linarith
  have hJK : max 1 (Kc + pv) ≤ Kint Kc := by
    apply max_le hKi1
    linarith
  have hAK : 2 * (max 1 (Kc + pv)) ^ 2 / (Kc ^ (-100 : ℝ) / 2) ^ 2 ≤ Kint Kc := by
    have hm1 : max 1 (Kc + pv) = Kc + pv := max_eq_right (by linarith)
    rw [hm1, hwv]
    have h1 : 2 * (Kc + pv) ^ 2 / ((Kc ^ 100)⁻¹ / 2) ^ 2 = 8 * (Kc + pv) ^ 2 * Kc ^ 200 := by
      field_simp
      ring
    rw [h1]
    have h2 : (Kc + pv) ^ 2 ≤ (2 * Kc) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith)
      linarith
    have h3 : 8 * (Kc + pv) ^ 2 * Kc ^ 200 ≤ 8 * (2 * Kc) ^ 2 * Kc ^ 200 := by
      have : 0 ≤ Kc ^ 200 := by positivity
      nlinarith
    have h4 : 8 * (2 * Kc) ^ 2 * Kc ^ 200 = 32 * Kc ^ 202 := by ring
    unfold Kint
    nlinarith [pow_pos hKc0 202]
  have hKd : 8 * Kc * (2 * Kc) * Kc ^ 3 /
      ((1 - 1 / 100) ^ 3 - 2 * (1 / 2000000000000)) ≤ Kint Kc := by
    have hc : ((1 : ℝ) - 1 / 100) ^ 3 - 2 * (1 / 2000000000000) = c0 := by
      unfold c0
      norm_num
    rw [hc, div_le_iff₀ hc0pos]
    have h1 : 8 * Kc * (2 * Kc) * Kc ^ 3 = 16 * Kc ^ 5 := by ring
    have h2 : Kc ^ 5 ≤ Kc ^ 202 := pow_le_pow_right₀ hKc1 (by norm_num)
    rw [h1]
    unfold Kint
    nlinarith [pow_pos hKc0 5]
  have hofps : ENNReal.ofReal (1 / 2000000000000) = (1 / 2000000000000 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have hof100 : ENNReal.ofReal (1 / 100) = (1 / 100 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have hQ : ∀ w ∈ Q, w ∈ Er ∧ start T j ≤ w.2 ∧ w.2 ≤ start T j + clock T ∧
      Cartesian.QualWitness Er st Gs (start T j) (clock T) M (Kint Kc) θ (1 / Kint Kc) w := by
    intro w hw
    have hwE0 := (hQsub hw).1
    have hwSe := hE0Se hwE0
    have hwin := (hSewin hwSe).2
    refine ⟨hSeEr hwSe, hwin.1, hwin.2, ?_⟩
    exact Cartesian.QualWitness.mono hKcKi
      (one_div_le_one_div_of_le hKc0 hKcKi) (hQsub hw).2
  have hvQ : ∀ w ∈ Q, ∀ k, |Cartesian.lineVel w.1 k| ≤ Kc := by
    intro w hw k
    have hwSe := hE0Se (hQsub hw).1
    have hv := (hpts w hwSe).2.1
    have h1 := (PiLp.norm_apply_le (v w.1) k).trans hv
    fin_cases k
    · simpa [Cartesian.lineVel, v] using h1
    · simpa [Cartesian.lineVel, v] using h1
  have hqualE0 : ∀ D ∈ Fam, (((ν.restrict A).prod volume).restrict E0) (st ⁻¹' {D} \ Q) ≤
      ENNReal.ofReal (1 / 100) * (((ν.restrict A).prod volume).restrict E0) (st ⁻¹' {D}) := by
    intro D _
    rw [hν'E0, hof100, ← hμsE0]
    exact hqualSt D
  have hstripE0 : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      (((ν.restrict A).prod volume).restrict E0) (st ⁻¹' {D} ∩
          {x | |⟪n, (WithLp.toLp 2 (Cartesian.lineVel x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤
            Kc ^ (-100 : ℝ)}) ≤
        ENNReal.ofReal (1 / 2000000000000) *
          (((ν.restrict A).prod volume).restrict E0) (st ⁻¹' {D}) := by
    intro D _ n hn s
    rw [hν'E0, hofps]
    apply cap_whole_state (ν.prod volume) st hSem hE0m hE0Se hsat D
    exact hstrip D n s hn
  have hpalE0 : ∀ D ∈ Fam, ∀ b : Fin 2 → ℤ,
      (((ν.restrict A).prod volume).restrict E0)
          ({x | Cartesian.velBinOf pv (Cartesian.lineVel x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤
        ENNReal.ofReal Kc * (((ν.restrict A).prod volume).restrict E0) (st ⁻¹' {D}) * pal {b} := by
    intro D _ b
    rw [hν'E0]
    calc ((ν.prod volume).restrict E0)
          ({x | Cartesian.velBinOf pv (Cartesian.lineVel x.1) = b} ∩ (st ⁻¹' {D} ∩ Q))
        ≤ ((ν.prod volume).restrict E0)
          (st ⁻¹' {D} ∩ {x | Cartesian.velBinOf pv (Cartesian.lineVel x.1) = b}) := by
          apply measure_mono
          rintro x ⟨hxb, hxD, -⟩
          exact ⟨hxD, hxb⟩
      _ ≤ (ENNReal.ofReal Kc * pal {b}) * ((ν.prod volume).restrict E0) (st ⁻¹' {D}) := by
          apply cap_whole_state (ν.prod volume) st hSem hE0m hE0Se hsat D
          have h1 := hpal D b
          calc ((ν.prod volume).restrict Se)
                (st ⁻¹' {D} ∩ {x | Cartesian.velBinOf pv (Cartesian.lineVel x.1) = b})
              ≤ ENNReal.ofReal Kc * ((ν.prod volume).restrict Se) (st ⁻¹' {D}) * pal {b} := h1
            _ = (ENNReal.ofReal Kc * pal {b}) * ((ν.prod volume).restrict Se) (st ⁻¹' {D}) := by
                ring
      _ = ENNReal.ofReal Kc * ((ν.prod volume).restrict E0) (st ⁻¹' {D}) * pal {b} := by ring
  have hczE : ∀ x ∈ Er, ∀ i, |Cartesian.packetZ T j c u x i - cz (st x) i| ≤ ε :=
    fun x _ i => hcz x i
  have hczK : ∀ D ∈ Fam, ∀ i, |cz D i| ≤ Kint Kc := by
    intro D hD i
    obtain ⟨x, hxSe, rfl⟩ := hFamSe D hD
    have h1 := hcz x i
    have h2 : |Cartesian.packetZ T j c u x i| ≤ Kc :=
      (PiLp.norm_apply_le (packetBase T j c u x) i).trans (hpts x hxSe).1
    have h3 : |cz (st x) i| ≤ |Cartesian.packetZ T j c u x i| +
        |Cartesian.packetZ T j c u x i - cz (st x) i| := by
      have := abs_sub_abs_le_abs_sub (cz (st x) i) (Cartesian.packetZ T j c u x i)
      rw [abs_sub_comm (cz (st x) i)] at this
      linarith
    have hε1 : ε ≤ 1 := hεθ'.trans (by
      have : θ / Kc ^ Ep ≤ θ := div_le_self hθ0.le hEp1
      linarith)
    linarith
  have hGK : ∀ D ∈ Fam, ∀ i, |Gs D i| ≤ Kint Kc := fun D _ i => (hGs D i).trans hKcKi
  have hfl : ∀ c' : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ Kint Kc ∧
      ∀ x ∈ Er, (∀ i, |Cartesian.packetZ T j c u x i - c' i| ≤
        30 * Kint Kc ^ 2 * (θ / (30 * Kint Kc ^ 2))) →
        Submission.Lib.K4CommonLocalChoice.cell θ (Gs (st x)) ∈ F := by
    intro c'
    obtain ⟨Fc, hFc, hFcmem⟩ := hlists c'
    refine ⟨Fc, hFc.trans hKcKi, ?_⟩
    intro x hx hbox
    have h30 : 30 * Kint Kc ^ 2 * (θ / (30 * Kint Kc ^ 2)) = θ := by
      field_simp
    rw [h30] at hbox
    exact hFcmem x hx hbox
  have hdens : ∀ (c' : Fin 3 → ℝ) (r' : ℝ), 0 < r' →
      ((ν.restrict A).prod volume).real
          (E0 ∩ {x | ∀ i, |Cartesian.packetZ T j c u x i - c' i| ≤ r'}) ≤
        (8 * Kc * (2 * Kc)) * r' ^ 3 * ((ν.restrict A).prod volume).real E0 := by
    intro c' r' hr'
    rw [prod_restrict_line_set_real ν hAm (inter_subset_left.trans hE0A),
      prod_restrict_line_set_real ν hAm hE0A]
    exact Cartesian.field_density_of_ceiling ν T j c u A hE0Se hKc0.le (by positivity) hceil
      hfloor hE0fin c' r' hr'
  have hE0pos' : 0 < ((ν.restrict A).prod volume).real E0 := by
    rw [prod_restrict_line_set_real ν hAm hE0A]
    exact hE0pos
  have hgraphE0 : ∀ x ∈ E0, |ParentSignal.rate P x.1 x.2 -
      ∑ i : Fin 3, direction x.1 i * Gs (st x) i| ≤ θ := fun x hx => hgraph x (hE0Se hx)
  have hVd : ∀ x ∈ E0, ∀ i, |direction x.1 i| ≤ Kc := by
    intro x hx i
    have hv := (hpts x (hE0Se hx)).2.1
    fin_cases i
    · simp [direction]; exact hKc1
    · have := (PiLp.norm_apply_le (v x.1) 0).trans hv
      simpa [direction, v] using this
    · have := (PiLp.norm_apply_le (v x.1) 1).trans hv
      simpa [direction, v] using this
  obtain ⟨Tf, times, S, hSm, hSE0, hdeg, hcoeffT, htimes, hfitL, hhalfS, hmassF⟩ :=
    hfield (σ := ℕ) (ν.restrict A) T j c u P E0 Er hE0m (hE0Se.trans hSeEr)
      (hE0Se.trans hSewin) st hstm Gs cz Fam hFam Q hQm pal
      (Kint Kc) (θ / (30 * Kint Kc ^ 2)) ε θ θ (1 / 100) (1 / 2000000000000)
      (Kc ^ (-100 : ℝ)) pv Kc Kc (8 * Kc * (2 * Kc)) θ Kc (eta C e Kc)
      hKi1 hξ0 hCξ hε.le hεξ hξθ hθ1 hθ0.le le_rfl hQ hKc0.le hvQ (by norm_num) (by norm_num)
      (by norm_num) hqualE0 hwv0 hpv hpvwv hpvξ hJK hAK hstripE0 hKc0.le hpalE0 hczE hczK hGK
      hfl hdens hKd hE0pos' hgraphE0 hVd hη0.le
  ------------------------------------------------------------------
  -- 3. the frozen packet on `S`
  ------------------------------------------------------------------
  have hSSe : S ⊆ Se := hSE0.trans hE0Se
  have hSA : S ⊆ A ×ˢ univ := hSSe.trans hSeA'
  have hhalfS' : ∀ D, S ∩ st ⁻¹' {D} = ∅ ∨
      (ν.prod volume) (E0 ∩ st ⁻¹' {D}) ≤ 2 * (ν.prod volume) (S ∩ st ⁻¹' {D}) := by
    intro D
    rcases hhalfS D with h0 | h1
    · exact Or.inl h0
    · right
      rwa [prod_restrict_line_set_apply ν hAm (inter_subset_left.trans hE0A),
        prod_restrict_line_set_apply ν hAm (inter_subset_left.trans hSA)] at h1
  have hhalfSe := half_state_thinning_after_whole_states (ν.prod volume) st Se E0 S hE0Se hSE0
    hsat hhalfS'
  -- the mass of `S`
  have hSfin : (ν.prod volume) S ≠ ⊤ := ne_top_of_le_ne_top hμSe_fin (measure_mono hSSe)
  have hmassS : ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A / ENNReal.ofReal (Kf M C e Kc) ≤
      ((ν.prod volume).restrict S) univ := by
    rw [Measure.restrict_apply_univ, hrefm, ← ENNReal.ofReal_div_of_pos hKf0,
      ← ENNReal.ofReal_toReal hSfin]
    apply ENNReal.ofReal_le_ofReal
    rw [prod_restrict_line_set_real ν hAm hE0A, prod_restrict_line_set_real ν hAm hSA,
      Measure.restrict_apply_univ] at hmassF
    have hc : ((1 : ℝ) - 1 / 100) ^ 3 - 2 * (1 / 2000000000000) = c0 := by
      unfold c0
      norm_num
    rw [hc] at hmassF
    have hC' : Kc ^ 3 / c0 * (C * Kint Kc ^ e) = Ccomb C e Kc := rfl
    rw [hC'] at hmassF
    set m := ((2 : ℝ) ^ T)⁻¹ * (ν A).toReal with hm_def
    set μS := (ν.prod volume).real S with hμS_def
    have hclock : clock T = ((2 : ℝ) ^ T)⁻¹ := rfl
    rw [hclock] at hmassF
    have hlow : m / (2 * Kc) ≤ (ν.prod volume).real E0 := by
      have : m / (2 * Kc) = m / Kc / 2 := by field_simp
      rw [this]
      linarith
    have h1 : m / (2 * Kc) ≤ Ccomb C e Kc * μS + 3 * (eta C e Kc * Ccomb C e Kc) * m := by
      have := hlow.trans hmassF
      nlinarith
    rw [hηC] at h1
    have h2 : 3 * (1 / (12 * Kc)) * m = m / (4 * Kc) := by field_simp; ring
    rw [h2] at h1
    have h3 : m / (4 * Kc) ≤ Ccomb C e Kc * μS := by
      have : m / (2 * Kc) = m / (4 * Kc) + m / (4 * Kc) := by field_simp; ring
      linarith
    have h4 : m ≤ 4 * Kc * Ccomb C e Kc * μS := by
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    have hμS0 : 0 ≤ μS := measureReal_nonneg
    rw [div_le_iff₀ hKf0]
    have h5 : 4 * Kc * Ccomb C e Kc * μS ≤ Kf M C e Kc * μS :=
      mul_le_mul_of_nonneg_right h4KcC hμS0
    change m ≤ ((ν.prod volume) S).toReal * Kf M C e Kc
    rw [← measureReal_def]
    linarith
  -- pointwise clauses
  have hptsS : ∀ p ∈ S, ‖packetBase T j c u p‖ ≤ Kf M C e Kc ∧ ‖v p.1‖ ≤ Kf M C e Kc ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ Kf M C e Kc ∧
        |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ Kf M C e Kc * B ∧
        |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
          Kf M C e Kc * B ^ 2) ∧
      B / Kf M C e Kc ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)| := by
    intro p hp
    obtain ⟨hz, hvp, hjets, hB⟩ := hpts p (hSSe hp)
    have hB0 : 0 ≤ B := by
      have h0 := (hjets 0 ⟨le_rfl, zero_le_one⟩).2.1
      have : 0 ≤ Kc * B := (abs_nonneg _).trans h0
      exact nonneg_of_mul_nonneg_right (by linarith) hKc0
    refine ⟨hz.trans hKcKf, hvp.trans hKcKf, ?_, ?_⟩
    · intro t ht
      obtain ⟨h1, h2, h3⟩ := hjets t ht
      refine ⟨h1.trans hKcKf, h2.trans (mul_le_mul_of_nonneg_right hKcKf hB0),
        h3.trans (mul_le_mul_of_nonneg_right hKcKf (by positivity))⟩
    · exact (div_le_div_of_nonneg_left hB0 hKc0 hKcKf).trans hB
  -- strip breadth on `S`
  have hwidth : Kf M C e Kc ^ (-100 : ℝ) ≤ Kc ^ (-100 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hKc0 hKcKf (by norm_num)
  have h2ps : 2 * (1 / 2000000000000 : ℝ≥0∞) = (1 / 1000000000000 : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one, mul_one]
    rw [show (2000000000000 : ℝ≥0∞) = 2 * 1000000000000 by norm_num]
    rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp),
      one_mul]
  have hstripSt : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
      ((ν.prod volume).restrict S) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤
          Kf M C e Kc ^ (-100 : ℝ)} ≤
        (1 / 1000000000000 : ℝ≥0∞) * ((ν.prod volume).restrict S) {p | st p = k} := by
    intro k n t hn
    have h1 := cap_after_half_state_thinning (ν.prod volume) st Se S hSem hSm hSSe hhalfSe
      {p | |inner ℝ n (v p.1) - t| ≤ Kc ^ (-100 : ℝ)} (1 / 2000000000000 : ℝ≥0∞)
      (fun k => hstrip k n t hn) k
    rw [h2ps] at h1
    refine le_trans (measure_mono ?_) h1
    rintro p ⟨hpk, hpw⟩
    exact ⟨hpk, hpw.trans hwidth⟩
  have hstripS : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict S)
          {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k ∧
            |inner ℝ n (v p.1) - t| ≤ Kf M C e Kc ^ (-100 : ℝ)} ≤
        (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S)
          {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k} := by
    intro k n t hn
    have h1 := refining_cap_after_half_state_thinning (ν.prod volume) st hstm
      (physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε) hrefine
      Se S hSem hSm hSSe hhalfSe
      {p | |inner ℝ n (v p.1) - t| ≤ Kc ^ (-100 : ℝ)} (1 / 2000000000000 : ℝ≥0∞)
      (fun k => hstrip k n t hn) k
    rw [h2ps] at h1
    refine le_trans (measure_mono ?_) h1
    rintro p ⟨hpk, hpw⟩
    exact ⟨hpk, hpw.trans hwidth⟩
  -- base ceiling, scalar band cap and census on `S`
  have hceilS : ∀ U : Set P3, MeasurableSet U →
      ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U} ≤
        ENNReal.ofReal (Kf M C e Kc) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) * volume U := by
    intro U hU
    calc ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U}
        ≤ ((ν.prod volume).restrict Se) {p | packetBase T j c u p ∈ U} :=
          Measure.restrict_mono hSSe le_rfl _
      _ ≤ ENNReal.ofReal Kc * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) * volume U := hceil U hU
      _ ≤ _ := by gcongr
  have hbandS : ∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U →
      ∀ f : P3 → ℝ, Measurable f →
      ((ν.prod volume).restrict S)
          {p | packetBase T j c u p ∈ U ∧
            |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w} ≤
        ENNReal.ofReal (Kf M C e Kc * w ^ d₁) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) *
          volume U := by
    intro w hεw hw1 U hU f hf
    have hw0 : 0 ≤ w ^ d₁ := Real.rpow_nonneg (hε.le.trans hεw) d₁
    calc ((ν.prod volume).restrict S)
          {p | packetBase T j c u p ∈ U ∧
            |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w}
        ≤ ((ν.prod volume).restrict Se)
          {p | packetBase T j c u p ∈ U ∧
            |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w} :=
          Measure.restrict_mono hSSe le_rfl _
      _ ≤ ENNReal.ofReal (Kc * w ^ d₁) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) * volume U :=
          hband w hεw hw1 U hU f hf
      _ ≤ _ := by
          gcongr
  have hcountS : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      Kf M C e Kc ^ (100 : ℕ) * ((2 : ℝ) ^ T)⁻¹ * p ≤ δ Nk r * w →
      Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
          ⌊packetSignal P e / δ Nk r / w⌋)) e = k} ∧
      (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
          ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ) ≤
        Kf M C e Kc / (p ^ (3 : ℕ) * w ^ d₁) := by
    intro p w hεp hp1 hεw hw1 hpw
    have hp0 : 0 < p := hε.trans_le hεp
    have hw0 : 0 < w := hε.trans_le hεw
    have hpw' : Kc ^ (100 : ℕ) * ((2 : ℝ) ^ T)⁻¹ * p ≤ δ Nk r * w := by
      refine le_trans ?_ hpw
      have : Kc ^ (100 : ℕ) ≤ Kf M C e Kc ^ (100 : ℕ) := pow_le_pow_left₀ hKc0.le hKcKf 100
      gcongr
    obtain ⟨hfinSe, hcardSe⟩ := hcount p w hεp hp1 hεw hw1 hpw'
    have hsub : {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
          ⌊packetSignal P e / δ Nk r / w⌋)) e = k} ⊆
        {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
          ⌊packetSignal P e / δ Nk r / w⌋)) e = k} := by
      rintro k ⟨x, hx, hxk⟩
      exact ⟨x, hSSe hx, hxk⟩
    refine ⟨hfinSe.subset hsub, ?_⟩
    have hpos : 0 < p ^ (3 : ℕ) * w ^ d₁ := by
      have := Real.rpow_pos_of_pos hw0 d₁
      positivity
    calc (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ)
        ≤ (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub hfinSe
      _ ≤ Kc / (p ^ (3 : ℕ) * w ^ d₁) := hcardSe
      _ ≤ Kf M C e Kc / (p ^ (3 : ℕ) * w ^ d₁) :=
          div_le_div_of_nonneg_right hKcKf hpos.le
  -- palette domination on `S`
  have hbinS : ∀ k β, (ν.prod volume) ({z | st z = k ∧ Switch.PacketSwitching.velBin pv z.1 = β} ∩ S) ≤
      ENNReal.ofReal (2 * Kc) * (ν.prod volume) (st ⁻¹' {k} ∩ S) * pal {β} := by
    intro k β
    have h1 := cap_after_half_state_thinning (ν.prod volume) st Se S hSem hSm hSSe hhalfSe
      {z | Switch.PacketSwitching.velBin pv z.1 = β} (ENNReal.ofReal Kc * pal {β})
      (fun k => by
        have h := hpal k β
        calc ((ν.prod volume).restrict Se) {x | st x = k ∧ x ∈ {z | Switch.PacketSwitching.velBin pv z.1 = β}}
            ≤ ENNReal.ofReal Kc * ((ν.prod volume).restrict Se) {p | st p = k} * pal {β} := h
          _ = (ENNReal.ofReal Kc * pal {β}) * ((ν.prod volume).restrict Se) {x | st x = k} := by
              ring) k
    rw [Measure.restrict_apply' hSm, Measure.restrict_apply' hSm] at h1
    have h2 : ENNReal.ofReal (2 * Kc) = 2 * ENNReal.ofReal Kc := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [h2]
    calc (ν.prod volume) ({z | st z = k ∧ Switch.PacketSwitching.velBin pv z.1 = β} ∩ S)
        ≤ 2 * (ENNReal.ofReal Kc * pal {β}) * (ν.prod volume) ({x | st x = k} ∩ S) := h1
      _ = 2 * ENNReal.ofReal Kc * (ν.prod volume) (st ⁻¹' {k} ∩ S) * pal {β} := by
          rw [show {x | st x = k} = st ⁻¹' {k} from rfl]
          ring
  -- the remaining parameters
  have hbudget : ((3 * M + 1 : ℕ) : ℝ) * 3 * AT C e Kc ≤ Kf M C e Kc := by
    unfold Kf
    push_cast
    have hM : (0 : ℝ) ≤ 3 * (M : ℝ) + 1 := by positivity
    have h1 : 3 ≤ 8 * Kc ^ 4 := by nlinarith
    have h2 : (3 * (M : ℝ) + 1) * 3 * AT C e Kc ≤ (3 * (M : ℝ) + 1) * (8 * Kc ^ 4) * AT C e Kc := by
      apply mul_le_mul_of_nonneg_right _ hAT0
      exact mul_le_mul_of_nonneg_left h1 hM
    linarith
  have hKN' : Kf M C e Kc ≤ Nk ^ (loss * gain * L) := nKf.trans hKN
  have herr0 : 0 ≤ θ + 3 * Kc * (C * Kint Kc ^ e * θ) := by
    have : 0 ≤ C * Kint Kc ^ e := by positivity
    positivity
  have hpvBound : pv ≤ Switch.PacketSwitching.binWidth (3 * M) cNorm cCurl (Kf M C e Kc)
      (2 * Kc) (δ Nk r) (clock T) (δ Nk (precision * gain * L)) d₁ (AT C e Kc) := by
    refine hpvθ'.trans ?_
    rw [hθratio]
    exact nbin
  have hεsmall : ε ≤ Switch.PacketSwitching.packetEpsBound (3 * M) cNorm cCurl (Kf M C e Kc)
      (2 * Kc) (δ Nk r) (clock T) (δ Nk (precision * gain * L)) d₁ (AT C e Kc) := by
    refine hεθ'.trans ?_
    rw [hθratio]
    exact neps
  have herrsmall : θ + 3 * Kc * (C * Kint Kc ^ e * θ) ≤
      Switch.PacketSwitching.packetErrBound (3 * M) cNorm cCurl (Kf M C e Kc) (2 * Kc)
        (δ Nk r) (clock T) (δ Nk (precision * gain * L)) d₁ (eta C e Kc) := by
    have h1 : θ + 3 * Kc * (C * Kint Kc ^ e * θ) =
        δ Nk r / ((2 : ℝ) ^ T)⁻¹ * δ Nk (precision * gain * L) ^ Ep / Kc ^ Ep *
          (1 + 3 * Kc * AT C e Kc) := by
      rw [hθ]
      unfold AT
      ring
    rw [h1]
    exact nerr
  have hSHF : S ⊆ H ∩ F := hSSe.trans hSeHF
  have hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1 := hSSe.trans hSunitSe
  have htimeS : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T) :=
    fun z hz => (hSewin (hSSe hz)).2
  have hDq : 3 * M + 1 ≤ q := hq
  exact hfin q precision loss Nk L d₁ gain κ ν B r T j c u P hPdeg A hAm F H (Kf M C e Kc) ε S
    hε hεζ hεa ha (haK.trans (mul_le_mul_of_nonneg_right hKcKf hh0.le)) hhζ hKf2
    (hκK.trans hKcKf) hKN' hSm hSHF hSA hSunit htimeS href hmassS hptsS hstripS hceilS hbandS
    hcountS st hstm hrefine hstripSt pal (2 * Kc) (by linarith) Tf hdeg hDq (AT C e Kc) hAT0
    hcoeffT hbudget pv hpv hpvBound hbinS times (eta C e Kc)
    (θ + 3 * Kc * (C * Kint Kc ^ e * θ)) hη0 hη1 herr0 htimes hfitL hd₁ hεsmall herrsmall

end

end Submission.Obl.k4_physical_row_packet_potential.Glue
