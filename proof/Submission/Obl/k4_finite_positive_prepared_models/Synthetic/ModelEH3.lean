import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelNum
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.LabelMeasure

/-!
# The true labels `EH3` and their nesting `EH4` for the synthetic stage model

At a scale `s`, the labels of the level `lev s` have prior `2^(-e₁ Gh - T - Ux)`, within the
loss `K = 2^σ` of `N^(-d₁ s) q² N^(-ℓ s)`; their lines stay within `2q` of the label's position
over its block, within `2^(-Ux) ≤ K q N^(-ℓ s)` of its transverse position, and their hidden
coordinate within `2^(-e Gh) ≤ K N^(-s)` of the label's hidden cell. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set MvPolynomial

noncomputable section

namespace Par

variable (p : Par)

theorem stage_q (s : ℝ) : (2 : ℝ) ^ (-(p.stage.T s : ℤ)) = 1 / 2 ^ p.T (p.lev s) := by
  show (2 : ℝ) ^ (-(p.T (p.lev s) : ℤ)) = _
  rw [zpow_neg, zpow_natCast, one_div]

theorem ofReal_inv_two_pow (k : ℕ) : ((2 : ENNReal) ^ k)⁻¹ = ENNReal.ofReal (1 / 2 ^ k) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, one_div]

theorem nu_label (d : ℕ) (hd : d ≤ p.D) (L : p.synth.Label d) :
    p.synth.nu (p.synth.sA d L) =
      ENNReal.ofReal (1 / 2 ^ (p.e₁ * p.Gh d) * (1 / 2 ^ p.T d) * (1 / 2 ^ p.Ux d)) := by
  have h1 : ((idx p.synth.M).prod U) (p.synth.Aidx d L) =
      ((2 : ENNReal) ^ (p.synth.e₁ * p.synth.Gh d))⁻¹ := p.idx_prefix d hd L.2.2.2
  have h2 : U (p.synth.Ax2 d L) = ENNReal.ofReal (1 / 2 ^ p.synth.Ux d) := p.U_x2 d L.2.2.1
  rw [p.synth.nu_sA_eq d hd L, h1, h2, ofReal_inv_two_pow, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  rfl

theorem mass_real (d : ℕ) :
    1 / 2 ^ (p.e₁ * p.Gh d) * (1 / 2 ^ p.T d) * (1 / 2 ^ p.Ux d) =
      (2 : ℝ) ^ (-((p.e₁ : ℝ) * p.Gh d) - p.T d - p.Ux d) := by
  rw [one_div_two_pow, one_div_two_pow, one_div_two_pow, ← Real.rpow_add two_pos,
    ← Real.rpow_add two_pos]
  congr 1
  push_cast
  ring

theorem amass_real (s : ℝ) :
    (p.sN ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.T (p.lev s) : ℤ))) ^ 2 * p.sN ^ (-p.ℓ * s) =
      (2 : ℝ) ^ (p.Λ * -s * p.d₁ - 2 * p.T (p.lev s) + p.Λ * (-p.ℓ * s)) := by
  rw [sN_rpow, sN_rpow, ← Real.rpow_mul (by norm_num), two_zpow_neg, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
  congr 1
  push_cast
  ring

theorem mass_bounds {s : ℝ} (hf : p.LevFacts s) :
    (p.sN ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.T (p.lev s) : ℤ))) ^ 2 * p.sN ^ (-p.ℓ * s) / p.sK ≤
        1 / 2 ^ (p.e₁ * p.Gh (p.lev s)) * (1 / 2 ^ p.T (p.lev s)) * (1 / 2 ^ p.Ux (p.lev s)) ∧
      1 / 2 ^ (p.e₁ * p.Gh (p.lev s)) * (1 / 2 ^ p.T (p.lev s)) * (1 / 2 ^ p.Ux (p.lev s)) ≤
        p.sK * (p.sN ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.T (p.lev s) : ℤ))) ^ 2 *
          p.sN ^ (-p.ℓ * s) := by
  have hfe := p.floor_exps hf
  have hUx : (p.Ux (p.lev s) : ℝ) = p.T (p.lev s) + ⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ := by
    unfold Ux; push_cast; ring
  constructor
  · rw [p.mass_real, p.amass_real, sK_eq, ← Real.rpow_sub two_pos]
    apply two_rpow_le
    rw [hUx]
    linarith [hfe.1]
  · rw [show p.sK * (p.sN ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.T (p.lev s) : ℤ))) ^ 2 *
        p.sN ^ (-p.ℓ * s) = p.sK * ((p.sN ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.T (p.lev s) : ℤ))) ^ 2 *
        p.sN ^ (-p.ℓ * s)) by ring]
    rw [p.mass_real, p.amass_real, sK_eq, ← Real.rpow_add two_pos]
    apply two_rpow_le
    rw [hUx]
    linarith [hfe.2]

theorem x2_bound {s : ℝ} (hf : p.LevFacts s) :
    1 / 2 ^ p.Ux (p.lev s) ≤ p.sK * (1 / 2 ^ p.T (p.lev s)) * p.sN ^ (-p.ℓ * s) := by
  have h := p.x2_exp hf
  rw [one_div_two_pow, one_div_two_pow, sK_eq, sN_rpow, ← Real.rpow_add two_pos,
    ← Real.rpow_add two_pos]
  apply two_rpow_le
  unfold Ux
  push_cast
  linarith

theorem hid_bound {s : ℝ} (hf : p.LevFacts s) :
    1 / 2 ^ (p.e * p.Gh (p.lev s)) ≤ p.sK * p.sN ^ (-s) := by
  have h := p.hid_exp hf
  rw [one_div_two_pow, sK_eq, sN_rpow, ← Real.rpow_add two_pos]
  apply two_rpow_le
  push_cast
  linarith

theorem exS_one (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (exS p.stage.b l t) 1 = l.2 0 + t * (p.synth.β * l.2 3) := rfl

theorem exS_two (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : (exS p.stage.b l t) 2 = l.2 1 + t * 0 := rfl

theorem exS_three (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (exS p.stage.b l t) 3 = hid p.synth.e p.synth.e₁ p.synth.G l.1 (l.2 2) + t * 0 := rfl

theorem b_four (l : ℕ × (Fin 6 → ℝ)) : p.stage.b l 4 = 0 := rfl

theorem c_zero (s : ℝ) (i : Fin (p.stage.nl s)) :
    p.stage.c s i 0 = p.synth.cpos (p.lev s) (p.eqv s i).2.1.1 := rfl

theorem c_one (s : ℝ) (i : Fin (p.stage.nl s)) : p.stage.c s i 1 = 0 := rfl

theorem c_two (s : ℝ) (i : Fin (p.stage.nl s)) :
    p.stage.c s i 2 = (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s) := rfl

theorem c_three (s : ℝ) (i : Fin (p.stage.nl s)) : p.stage.c s i 3 = 0 := rfl

theorem c_four (s : ℝ) (i : Fin (p.stage.nl s)) : p.stage.c s i 4 = 0 := rfl

theorem pderiv_F (s : ℝ) (i : Fin (p.stage.nl s)) : pderiv (3 : Fin 4) (p.stage.F s i) = 1 := by
  show pderiv (3 : Fin 4) (X 3 - C _) = 1
  rw [map_sub, pderiv_X_self, pderiv_C, sub_zero]

theorem pderiv_pderiv_F (s : ℝ) (i : Fin (p.stage.nl s)) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (p.stage.F s i)) = 0 := by
  rw [pderiv_F]
  exact (pderiv 3).map_one_eq_zero

theorem eval_F (s : ℝ) (i : Fin (p.stage.nl s)) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (exS p.stage.b l t) (p.stage.F s i) =
      hid p.synth.e p.synth.e₁ p.synth.G l.1 (l.2 2) -
        (spread p.synth.e p.synth.e₁ (p.synth.Gh (p.lev s)) ((p.eqv s i).2.2.2 : ℕ) : ℝ) /
          2 ^ (p.synth.e * p.synth.Gh (p.lev s)) := by
  show eval (exS p.stage.b l t) (X 3 - C _) = _
  rw [map_sub, eval_X, eval_C, exS_three]
  ring

/-! ### The parts of `EH3` -/

theorem eh3_time {s : ℝ} (hf : p.LevFacts s) :
    p.stage.N ^ (p.κ₁ * s) / p.stage.K ≤ (2 : ℝ) ^ p.stage.T s ∧
      (2 : ℝ) ^ p.stage.T s ≤ p.stage.K * p.stage.N ^ (p.κ₁ * s) :=
  p.time_bounds hf

theorem eh3_meas (s : ℝ) : ∀ i, MeasurableSet (p.stage.A s i) ∧
    MeasurableSet (p.stage.B s i) ∧ p.stage.B s i ⊆ p.stage.A s i :=
  fun _ => ⟨p.synth.measurableSet_sA _ _, p.synth.measurableSet_sA _ _, subset_rfl⟩

theorem eh3_disj (s : ℝ) : ∀ i i', i ≠ i' → p.stage.j s i = p.stage.j s i' →
    Disjoint (p.stage.A s i) (p.stage.A s i') :=
  fun _ _ hne hj => p.synth.sA_disjoint _ _ _ ((p.eqv s).injective.ne hne) hj

theorem eh3_mass {s : ℝ} (hf : p.LevFacts s) (i : Fin (p.stage.nl s)) :
    ENNReal.ofReal ((p.stage.N ^ (-s)) ^ p.d₁ * ((2 : ℝ) ^ (-(p.stage.T s : ℤ))) ^ 2 *
        p.stage.N ^ (-p.ℓ * s) / p.stage.K) ≤ p.stage.ν (p.stage.A s i) ∧
      p.stage.ν (p.stage.A s i) ≤ ENNReal.ofReal (p.stage.K * (p.stage.N ^ (-s)) ^ p.d₁ *
        ((2 : ℝ) ^ (-(p.stage.T s : ℤ))) ^ 2 * p.stage.N ^ (-p.ℓ * s)) := by
  have hν : p.stage.ν (p.stage.A s i) = ENNReal.ofReal (1 / 2 ^ (p.e₁ * p.Gh (p.lev s)) *
      (1 / 2 ^ p.T (p.lev s)) * (1 / 2 ^ p.Ux (p.lev s))) :=
    p.nu_label (p.lev s) (p.lev_le s) (p.eqv s i)
  rw [hν]
  obtain ⟨h1, h2⟩ := p.mass_bounds hf
  exact ⟨ENNReal.ofReal_le_ofReal h1, ENNReal.ofReal_le_ofReal h2⟩

theorem eh3_floor (s : ℝ) (i : Fin (p.stage.nl s)) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(p.stage.T s : ℤ)) / p.stage.K) * p.stage.ν (p.stage.A s i) ≤
      p.stage.μ (p.stage.B s i ×ˢ IS (p.stage.T s) (p.stage.j s i)) := by
  have h := p.synth.floor_label (by have := p.synth_hBD; omega) (p.lev s) (p.lev_le s)
    (p.eqv s i)
  refine le_trans ?_ h
  rw [p.stage_q s]
  have hK := p.two_le_sK
  have hq0 : (0 : ℝ) ≤ 1 / 2 ^ p.T (p.lev s) := by positivity
  have h1 : ENNReal.ofReal (1 / 2 ^ p.T (p.lev s) / p.sK) ≤
      1 / 2 * ENNReal.ofReal (1 / 2 ^ p.T (p.lev s)) := by
    calc ENNReal.ofReal (1 / 2 ^ p.T (p.lev s) / p.sK)
        ≤ ENNReal.ofReal (1 / 2 ^ p.T (p.lev s) / 2) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hq0 two_pos hK)
      _ = 1 / 2 * ENNReal.ofReal (1 / 2 ^ p.T (p.lev s)) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul,
            one_div (2 : ENNReal)]
  calc ENNReal.ofReal (1 / 2 ^ p.T (p.lev s) / p.stage.K) * p.stage.ν (p.stage.A s i)
      ≤ 1 / 2 * ENNReal.ofReal (1 / 2 ^ p.T (p.lev s)) *
          p.synth.nu (p.synth.sA (p.lev s) (p.eqv s i)) := mul_le_mul_left h1 _
    _ = 1 / 2 * p.synth.nu (p.synth.sA (p.lev s) (p.eqv s i)) *
          ENNReal.ofReal (1 / 2 ^ p.synth.T (p.lev s)) := by
        rw [mul_right_comm]
        rfl

theorem eh3_c (s : ℝ) (i : Fin (p.stage.nl s)) : ∀ e, |p.stage.c s i e| ≤ p.stage.K := by
  have hK : (1 : ℝ) ≤ p.stage.K := p.one_le_sK
  have hb := p.synth.valid_bounds _ _ (p.eqv s i).2.1.2
  have hβ := p.synth.β_pos
  have hq := p.synth.q_pos (p.lev s)
  have hU : (0 : ℝ) < 2 ^ p.synth.Ux (p.lev s) := by positivity
  have hi2 : (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s) ≤ 1 := by
    rw [div_le_one hU]
    exact_mod_cast (p.eqv s i).2.2.1.2.le
  intro e
  fin_cases e
  · show |p.stage.c s i 0| ≤ _
    rw [c_zero, abs_of_nonneg (by linarith)]
    linarith
  · show |p.stage.c s i 1| ≤ _
    rw [c_one, abs_zero]
    linarith
  · show |p.stage.c s i 2| ≤ _
    rw [c_two, abs_of_nonneg (by positivity)]
    linarith
  · show |p.stage.c s i 3| ≤ _
    rw [c_three, abs_zero]
    linarith
  · show |p.stage.c s i 4| ≤ _
    rw [c_four, abs_zero]
    linarith

theorem eh3_deg (s : ℝ) (i : Fin (p.stage.nl s)) : (p.stage.F s i).totalDegree ≤ 2 := by
  show (X 3 - C _ : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 2
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_X, totalDegree_C]
  norm_num

theorem eh3_geom {s : ℝ} (hf : p.LevFacts s) (i : Fin (p.stage.nl s)) :
    ∀ l ∈ p.stage.A s i, ∀ t ∈ IS (p.stage.T s) (p.stage.j s i),
      |(exS p.stage.b l t) 1 - p.stage.c s i 0 - t * p.stage.c s i 1| ≤
          p.stage.K * (2 : ℝ) ^ (-(p.stage.T s : ℤ)) ∧
        |(exS p.stage.b l t) 2 - p.stage.c s i 2 - t * p.stage.c s i 3 -
            p.stage.c s i 4 * (exS p.stage.b l t) 1| ≤
          p.stage.K * (2 : ℝ) ^ (-(p.stage.T s : ℤ)) * p.stage.N ^ (-p.ℓ * s) ∧
        |p.stage.b l 4 - p.stage.c s i 3 - p.stage.c s i 4 * p.stage.b l 3| ≤
          p.stage.K * p.stage.N ^ (-p.ℓ * s) := by
  intro l hl t ht
  obtain ⟨hx, hu3, hb1, -, -, -⟩ := hl
  have hK : (2 : ℝ) ≤ p.stage.K := p.two_le_sK
  have hN : 0 < p.stage.N ^ (-p.ℓ * s) := by
    show 0 < p.sN ^ (-p.ℓ * s)
    unfold sN
    positivity
  rw [p.stage_q s, exS_one, exS_two, b_four, c_zero, c_one, c_two, c_three, c_four]
  refine ⟨?_, ?_, ?_⟩
  · -- the position stays within `2q` of the label's position over the block
    have hβ := p.synth.β_pos
    have hβ2 := p.synth.β_le_half
    have hp : (0 : ℝ) < 2 ^ p.T (p.lev s) := by positivity
    set j : ℝ := (((p.eqv s i).1 : ℕ) : ℝ)
    set w := p.synth.β * l.2 3 with hw
    have hw0 : 0 ≤ w := mul_nonneg hβ.le hu3.1
    have hw1 : w ≤ 1 := by nlinarith [hu3.2]
    have hq : p.synth.q (p.lev s) = 1 / 2 ^ p.T (p.lev s) := rfl
    obtain ⟨hx1, hx2⟩ := hx
    rw [hq] at hx2
    obtain ⟨ht1, ht2⟩ := ht
    have ht1' : j / 2 ^ p.T (p.lev s) ≤ t := ht1
    have ht2' : t ≤ j / 2 ^ p.T (p.lev s) + 1 / 2 ^ p.T (p.lev s) := by
      have : t ≤ (j + 1) / 2 ^ p.T (p.lev s) := ht2
      rwa [add_div] at this
    have hmul : (t - j / 2 ^ p.T (p.lev s)) * w ≤ 1 / 2 ^ p.T (p.lev s) * 1 :=
      mul_le_mul (by linarith) hw1 hw0 (by positivity)
    have hmul0 : 0 ≤ (t - j / 2 ^ p.T (p.lev s)) * w := mul_nonneg (by linarith) hw0
    have hx1' : p.synth.cpos (p.lev s) (p.eqv s i).2.1.1 ≤ l.2 0 + j / 2 ^ p.T (p.lev s) * w :=
      hx1
    have hx2' : l.2 0 + j / 2 ^ p.T (p.lev s) * w <
        p.synth.cpos (p.lev s) (p.eqv s i).2.1.1 + 1 / 2 ^ p.T (p.lev s) := hx2
    have hsplit : l.2 0 + t * w - p.synth.cpos (p.lev s) (p.eqv s i).2.1.1 - t * 0 =
        (l.2 0 + j / 2 ^ p.T (p.lev s) * w - p.synth.cpos (p.lev s) (p.eqv s i).2.1.1) +
          (t - j / 2 ^ p.T (p.lev s)) * w := by ring
    rw [hsplit, abs_of_nonneg (by linarith)]
    nlinarith
  · -- the transverse position stays in the label's transverse cell
    have hU : (0 : ℝ) < 2 ^ p.synth.Ux (p.lev s) := by positivity
    obtain ⟨h1, h2⟩ := hb1
    have h2' : l.2 1 < (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s) +
        1 / 2 ^ p.synth.Ux (p.lev s) := by rwa [add_div] at h2
    have hxb := p.x2_bound hf
    have e : l.2 1 + t * 0 - (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s) - t * 0 -
        0 * (l.2 0 + t * (p.synth.β * l.2 3)) =
        l.2 1 - (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s) := by ring
    rw [e, abs_of_nonneg (by linarith)]
    have : 1 / 2 ^ p.synth.Ux (p.lev s) ≤ p.sK * (1 / 2 ^ p.T (p.lev s)) * p.sN ^ (-p.ℓ * s) :=
      hxb
    show _ ≤ p.sK * (1 / 2 ^ p.T (p.lev s)) * p.sN ^ (-p.ℓ * s)
    linarith
  · have e : (0 : ℝ) - 0 - 0 * p.stage.b l 3 = 0 := by ring
    rw [e, abs_zero]
    have : (0 : ℝ) < p.stage.K := by linarith
    positivity

theorem eh3_fit {s : ℝ} (hf : p.LevFacts s) (i : Fin (p.stage.nl s)) :
    ∀ l ∈ p.stage.B s i, fitS p.stage.b p.stage.K (p.stage.N ^ (-s)) (p.stage.F s i) l
      (IS (p.stage.T s) (p.stage.j s i)) := by
  intro l hl t _
  obtain ⟨-, -, -, hu2, -, hpre⟩ := hl
  have hK : (1 : ℝ) ≤ p.stage.K := p.one_le_sK
  have ha : 0 < p.stage.N ^ (-s) := by
    show 0 < p.sN ^ (-s)
    unfold sN
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_F]
    have hc := hid_mem_cell p.synth.he (p.synth.hGhG _ (p.lev_le s)) l.1 hu2
    rw [hpre] at hc
    have hb := p.hid_bound hf
    have hb' : ((spread p.synth.e p.synth.e₁ (p.synth.Gh (p.lev s)) ((p.eqv s i).2.2.2 : ℕ) : ℝ) +
        1) / 2 ^ (p.synth.e * p.synth.Gh (p.lev s)) =
        (spread p.synth.e p.synth.e₁ (p.synth.Gh (p.lev s)) ((p.eqv s i).2.2.2 : ℕ) : ℝ) /
          2 ^ (p.synth.e * p.synth.Gh (p.lev s)) + 1 / 2 ^ (p.synth.e * p.synth.Gh (p.lev s)) :=
      add_div _ _ _
    have hb2 : 1 / (2 : ℝ) ^ (p.synth.e * p.synth.Gh (p.lev s)) ≤ p.stage.K * p.stage.N ^ (-s) :=
      hb
    rw [abs_of_nonneg (by linarith [hc.1])]
    linarith [hc.2]
  · rw [pderiv_F, map_one, abs_one]
    exact hK
  · rw [pderiv_pderiv_F, map_zero, abs_zero]
    have : (0 : ℝ) < p.stage.K := by linarith
    positivity

theorem eh3_aederiv (s : ℝ) (i : Fin (p.stage.nl s)) :
    ∀ᵐ x ∂p.stage.μ, x.1 ∈ p.stage.B s i → x.2 ∈ IS (p.stage.T s) (p.stage.j s i) →
      (p.stage.K)⁻¹ ≤ |eval (exS p.stage.b x.1 x.2) (pderiv (3 : Fin 4) (p.stage.F s i))| := by
  refine Filter.Eventually.of_forall fun x _ _ => ?_
  rw [pderiv_F, map_one, abs_one]
  exact inv_le_one_of_one_le₀ p.one_le_sK

theorem eh3_cover (s : ℝ) :
    ∀ᵐ x ∂p.stage.μ, ∃ i, x.1 ∈ p.stage.B s i ∧ x.2 ∈ IS (p.stage.T s) (p.stage.j s i) := by
  have h := p.synth.cover_label (p.lev s) (p.lev_le s)
  refine h.mono fun x hx => ?_
  obtain ⟨L, h1, h2⟩ := hx
  refine ⟨(p.eqv s).symm L, ?_, ?_⟩
  · show x.1 ∈ p.synth.sA (p.lev s) (p.eqv s ((p.eqv s).symm L))
    rw [Equiv.apply_symm_apply]
    exact h1
  · show x.2 ∈ Synth.blockI (p.synth.T (p.lev s)) (p.eqv s ((p.eqv s).symm L)).1
    rw [Equiv.apply_symm_apply]
    exact h2

theorem eh3_cap (s : ℝ) (i : Fin (p.stage.nl s)) (v : ℝ) (v₀ : ℤ) :
    p.stage.μ {x | x.1 ∈ p.stage.B s i ∧ x.2 ∈ IS (p.stage.T s) (p.stage.j s i) ∧
        ⌊p.stage.b x.1 3 / (p.stage.N ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.stage.K * (2 : ℝ) ^ (-(p.stage.T s : ℤ))) * p.stage.ν (p.stage.A s i) *
        p.stage.π {w : ℝ | ⌊w / (p.stage.N ^ (-v))⌋ = v₀} := by
  have hV : MeasurableSet {w : ℝ | ⌊w / (p.sN ^ (-v))⌋ = v₀} :=
    measurableSet_eq_fun (Int.measurable_floor.comp (measurable_id.div_const _)) measurable_const
  have h := p.synth.cap_label (p.lev s) (p.lev_le s) (p.eqv s i) hV
  refine le_trans h ?_
  have hK : (1 : ℝ) ≤ p.sK := p.one_le_sK
  have hle : ENNReal.ofReal (1 / 2 ^ p.synth.T (p.lev s)) ≤
      ENNReal.ofReal (p.stage.K * (2 : ℝ) ^ (-(p.stage.T s : ℤ))) := by
    rw [p.stage_q s]
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (by positivity) hK
  exact mul_le_mul_left (mul_le_mul_left hle _) _

/-- **`EH3`.** -/
theorem eh3 (R : ℝ) (hR : 1 < R) (hRn : R ≤ p.n) : EH3 p.d₁ p.κ₁ p.ℓ 1 1 p.stage R := by
  intro s hs1 hs2
  have h1 : 1 / (p.n : ℝ) ≤ s := by
    refine le_trans ?_ hs1
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) hRn
  have hf := p.levFacts h1 hs2
  exact ⟨(p.eh3_time hf).1, (p.eh3_time hf).2, p.eh3_meas s, p.eh3_disj s,
    fun i => ⟨(p.eh3_mass hf i).1, (p.eh3_mass hf i).2, p.eh3_floor s i, p.eh3_c s i,
      p.eh3_deg s i, p.eh3_geom hf i, p.eh3_fit hf i, p.eh3_aederiv s i,
      fun h => absurd h Bool.false_ne_true⟩,
    p.eh3_cover s, fun i v v₀ _ _ => p.eh3_cap s i v v₀⟩

/-- **`EH4`.** -/
theorem eh4 (R : ℝ) : EH4 1 p.stage R := by
  intro s t _ hst _ i
  obtain ⟨L', h1, h2⟩ := p.synth.anc_exists (p.lev_mono hst.le) (p.lev_le t) (p.eqv t i)
  refine ⟨(p.eqv s).symm L', ?_, ?_⟩
  · show p.synth.sA (p.lev t) (p.eqv t i) ⊆ p.synth.sA (p.lev s) (p.eqv s ((p.eqv s).symm L'))
    rw [Equiv.apply_symm_apply]
    exact h1
  · show Synth.blockI (p.synth.T (p.lev t)) (p.eqv t i).1 ⊆
      Synth.blockI (p.synth.T (p.lev s)) (p.eqv s ((p.eqv s).symm L')).1
    rw [Equiv.apply_symm_apply]
    exact h2

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
