-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.ScaleParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Budget
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PowerDepth

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

lemma inverse_error_pow {δ s : ℝ} (hδ : 0 < δ) (k : ℕ) :
    1 / (δ ^ (-s)) ^ k = δ ^ ((k : ℝ) * s) := by
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_div, Real.log_one, Real.log_pow, Real.log_rpow]
  ring

structure AssemblyParameters (ε ω ηf ηc df dc dn δ s : ℝ) (K Kc : ℕ) : Prop where
  fineScale : δ ≤ df
  coarseScale : δ ≤ dc
  numberScale : δ ≤ dn
  largeBudget : 512 ≤ δ ^ (-s)
  regularizationDepth : 0 < K
  regularizationBudget : 224 * (K : ℝ) ≤ δ ^ (-s)
  logarithmicBudget : (10 : ℝ) ^ (16 : ℕ) * (Kc + 1 : ℕ) ≤ δ ^ (-s)
  bottomScale : (1 / 2 : ℝ) ^ Kc ≤ δ / 16
  fineDensity : δ ^ ηf ≤ 1 / (δ ^ (-s)) ^ (3 : ℕ)
  coarseDensity : δ ^ ηc ≤ 1 / (δ ^ (-s)) ^ (19 : ℕ)
  finalError : δ ^ ε ≤ δ ^ (2 * (ε / 4)) / (δ ^ (-s)) ^ (45 : ℕ)
  regularizationCut : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 8 →
    432 * (1 / δ ^ (-s)) ^ K * a * b ≤ (1 / (δ ^ (-s)) ^ (2 : ℕ)) * δ ^ 2 / 2
  smallBox : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 8 →
    δ ^ (-(ε / 2)) < (b / a) ^ ω → a ≤ 1 / 100

set_option maxHeartbeats 800000 in
lemma choose_assembly_parameters {ε ω ηf ηc df dc dn : ℝ} (hε : 0 < ε) (hω : ω ≤ 1)
    (hηf : 0 < ηf) (hηc : 0 < ηc) (hdf : 0 < df) (hdc : 0 < dc) (hdn : 0 < dn) :
    ∃ s d : ℝ, 0 < s ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
      ∃ K Kc : ℕ, AssemblyParameters ε ω ηf ηc df dc dn δ s K Kc := by
  let s := min (min (ε / 100) (1 / 4)) (min (ηf / 4) (ηc / 20))
  have hs : 0 < s := by dsimp [s]; positivity
  have hsdata : (s ≤ ε / 100 ∧ s ≤ 1 / 4) ∧ (s ≤ ηf / 4 ∧ s ≤ ηc / 20) := by
    have hh : s ≤ min (min (ε / 100) (1 / 4)) (min (ηf / 4) (ηc / 20)) := le_refl s
    simpa only [le_min_iff] using hh
  obtain ⟨K, hKgt⟩ := exists_nat_gt (4 / s)
  have hKreal : (0 : ℝ) < K := (by positivity : 0 < 4 / s).trans hKgt
  have hK : 0 < K := by exact_mod_cast hKreal
  have hsK : 4 ≤ s * K := by have hh := (div_lt_iff₀ hs).mp hKgt; nlinarith
  obtain ⟨dl, hdl, _, Hl⟩ := WangZahlLot.Obl.wz_regular_transverse_affine_cells.dyadic_depth_with_power_budget
    2 s ((10 : ℝ) ^ (16 : ℕ)) (by norm_num) hs (by positivity)
  let C : ℝ := 1000000 * (K + 1 : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  let dreg := (1 / C) ^ s⁻¹
  let dflat := (1 / 800 : ℝ) ^ (ε / 2)⁻¹
  let d := min (min (min df dc) (min dl dn)) (min dreg (min dflat (1 / 55296)))
  have hd : 0 < d := by dsimp [d, dreg, dflat]; positivity
  refine ⟨s, d, hs, hd, ?_⟩
  intro δ hδ hδ100 hδd
  have hδ1 : δ ≤ 1 := by linarith
  have hddata : ((δ ≤ df ∧ δ ≤ dc) ∧ (δ ≤ dl ∧ δ ≤ dn)) ∧
      (δ ≤ dreg ∧ δ ≤ dflat ∧ δ ≤ 1 / 55296) := by
    simpa only [d, le_min_iff] using hδd
  have hsmall : δ ^ s ≤ 1 / C :=
    (Real.le_rpow_inv_iff_of_pos hδ.le (by positivity : 0 ≤ 1 / C) hs).mp hddata.2.1
  have hDinv : δ ^ (-s) = 1 / δ ^ s := by rw [Real.rpow_neg hδ.le, one_div]
  have hCbudget : C ≤ δ ^ (-s) := by
    rw [hDinv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ s)).mpr
    have hh := (le_div_iff₀ hC).mp hsmall
    nlinarith only [hh]
  have hDpos : 0 < δ ^ (-s) := Real.rpow_pos_of_pos hδ _
  have h512 : 512 ≤ δ ^ (-s) := by
    apply le_trans _ hCbudget
    dsimp [C]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  have h224 : 224 * (K : ℝ) ≤ δ ^ (-s) := by
    apply le_trans _ hCbudget
    dsimp [C]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  obtain ⟨Kc, hKc, hlog⟩ := Hl δ hδ hddata.1.2.1
  have hlog' : (10 : ℝ) ^ (16 : ℕ) * (Kc + 1 : ℕ) ≤ δ ^ (-s) := by
    rw [hDinv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ s)).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hlog
  have hbottom : (1 / 2 : ℝ) ^ Kc ≤ δ / 16 := by
    rw [Real.rpow_ofNat] at hKc
    exact hKc.trans (by nlinarith)
  refine ⟨K, Kc, ⟨hddata.1.1.1, hddata.1.1.2, hddata.1.2.2, h512, hK, h224,
    hlog', hbottom, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [inverse_error_pow hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    norm_num only [Nat.cast_ofNat]
    linarith [hsdata.2.1]
  · rw [inverse_error_pow hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    norm_num only [Nat.cast_ofNat]
    linarith [hsdata.2.2]
  · have he : δ ^ (2 * (ε / 4)) / (δ ^ (-s)) ^ (45 : ℕ) = δ ^ (2 * (ε / 4) + 45 * s) := by
      rw [div_eq_mul_inv, ← one_div, inverse_error_pow hδ, ← Real.rpow_add hδ]
      norm_num
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [hsdata.1.1])
  · intro a b ha hab hb8
    have hb : 0 < b := ha.trans_le hab
    have hab64 : a * b ≤ 64 := by
      nlinarith only [mul_le_mul (hab.trans hb8) hb8 hb.le (by norm_num : (0 : ℝ) ≤ 8)]
    have hinv : 1 / δ ^ (-s) = δ ^ s := by rw [hDinv]; simp
    have hpower : (1 / δ ^ (-s)) ^ K ≤ δ ^ (4 : ℕ) := by
      rw [hinv, ← Real.rpow_mul_natCast hδ.le, ← Real.rpow_ofNat]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hsK
    have hδs : δ ≤ δ ^ (2 * s) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        (show 2 * s ≤ 1 by linarith [hsdata.1.2])
    rw [inverse_error_pow hδ]
    norm_num only [Nat.cast_ofNat]
    calc
      _ ≤ 27648 * δ ^ (4 : ℕ) := by
        have hh := mul_le_mul hpower hab64 (mul_pos ha hb).le (by positivity : 0 ≤ δ ^ (4 : ℕ))
        nlinarith only [hh]
      _ ≤ δ ^ (3 : ℕ) / 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hddata.2.2.2 (by positivity : 0 ≤ δ ^ (3 : ℕ))]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hδs (sq_nonneg δ)]
  · intro a b ha hab hb8 hflat
    have hpw : (b / a) ^ ω ≤ b / a := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        ((one_le_div ha).mpr hab) hω
    have hh : a * δ ^ (-(ε / 2)) < b := by
      have hh := (lt_div_iff₀ ha).mp (hflat.trans_le hpw)
      nlinarith only [hh]
    have hh' := (lt_div_iff₀ (Real.rpow_pos_of_pos hδ (-(ε / 2)))).mpr hh
    rw [Real.rpow_neg hδ.le, div_inv_eq_mul] at hh'
    have hδflat : δ ^ (ε / 2) ≤ 1 / 800 :=
      (Real.le_rpow_inv_iff_of_pos hδ.le (by norm_num : (0 : ℝ) ≤ 1 / 800)
        (by positivity : 0 < ε / 2)).mp hddata.2.2.1
    have hh'' := mul_le_mul hb8 hδflat (Real.rpow_nonneg hδ.le _) (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith only [hh', hh'']

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
