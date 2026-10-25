import Submission.Obl.k4_narrow_projected_row_parents.RowDiagonal
import Submission.Obl.k4_scalar_grid_cartesian_field.Growth
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal

variable {α : Type} [MeasurableSpace α]

/-- Palette control may increase arbitrarily slowly while dominating the
existing losses. This supplies the separated witness velocities used in Row. -/
theorem exists_palette_control (cfg : Model α) (hv : Model.Valid cfg)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k) (hMsub : Model.Subpow cfg.N M)
    {aξ : ℝ} (haξ : 0 < aξ) :
    ∃ C : ℕ → ℝ, (∀ k, 1 ≤ C k) ∧ Model.Subpow cfg.N C ∧
      ∀ᶠ k in atTop, M k + 1 ≤ C k ∧ 4 * C k * cfg.N k ^ (-aξ) ≤ 1 ∧
        ∀ x : ℝ, cfg.π k (Icc (x - 2 / C k) (x + 2 / C k)) ≤
          ENNReal.ofReal (1 / (36 * M k * cfg.K k)) := by
  have hN : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hv.scale k]
  have hNp : ∀ k, 0 < cfg.N k := fun k => by linarith [hv.scale k]
  let R : ℕ → ℝ := fun k => max (M k) (cfg.K k)
  have hR : ∀ k, 1 ≤ R k := fun k => (hM k).trans (le_max_left _ _)
  have hRsub : Model.Subpow cfg.N R := by
    intro ε hε
    filter_upwards [hMsub ε hε, hv.subpower.2 ε hε] with k hk hKk
    exact max_le hk hKk
  let P : ℝ → ℕ → Prop := fun t k =>
    M k + 1 ≤ cfg.N k ^ min (aξ / 2) t ∧
    4 * cfg.N k ^ min (aξ / 2) t * cfg.N k ^ (-aξ) ≤ 1 ∧
    ∀ x : ℝ, cfg.π k (Icc (x - 2 / cfg.N k ^ min (aξ / 2) t)
        (x + 2 / cfg.N k ^ min (aξ / 2) t)) ≤
      ENNReal.ofReal (1 / (36 * M k * cfg.K k))
  have hP : ∀ t : ℝ, 0 < t → ∀ᶠ k in atTop, P t k := by
    intro t ht
    let q : ℝ := min (aξ / 2) t
    have hq : 0 < q := lt_min (by positivity) ht
    have hqaξ : q < aξ := (min_le_left _ _).trans_lt (by linarith)
    have hη : 0 < q * cfg.S / 2 := by positivity [hv.palette_pos]
    have hA := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hv.scale_limit hM hMsub 1 (a := 0) (b := q) hq (A := 2) (by norm_num)
    have hB := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      hv.scale_limit (a := q - aξ) (b := 0) (by linarith) 4
    have hC := palette_interval_eventually cfg hv haξ hη
    have hD := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hv.scale_limit hR hRsub 2 (a := -(q * cfg.S / 2)) (b := 0)
      (by linarith) (A := 36 * (2 : ℝ) ^ cfg.S) (by positivity)
    filter_upwards [hA, hB, hC, hD] with k hAk hBk hCk hDk
    simp only [Real.rpow_zero, mul_one, pow_one] at hAk hBk hDk
    have hMpos : 0 < M k := lt_of_lt_of_le zero_lt_one (hM k)
    have hKpos : 0 < cfg.K k := lt_of_lt_of_le zero_lt_one (hv.subpower.1 k)
    have hpow : 0 < cfg.N k ^ q := Real.rpow_pos_of_pos (hNp k) _
    have hMc : M k + 1 ≤ cfg.N k ^ q := by linarith [hM k]
    refine ⟨hMc, ?_, ?_⟩
    · calc 4 * cfg.N k ^ q * cfg.N k ^ (-aξ)
          = 4 * cfg.N k ^ (q - aξ) := by
            rw [mul_assoc, ← Real.rpow_add (hNp k)]
            congr 2
        _ ≤ 1 := hBk.le
    · intro x
      have hlo : cfg.N k ^ (-aξ) ≤ 2 / cfg.N k ^ q := by
        calc cfg.N k ^ (-aξ) ≤ cfg.N k ^ (-q) :=
              Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
          _ = 1 / cfg.N k ^ q := by rw [Real.rpow_neg (hNp k).le, one_div]
          _ ≤ 2 / cfg.N k ^ q := div_le_div_of_nonneg_right (by norm_num) hpow.le
      have hup : 2 / cfg.N k ^ q ≤ 1 := (div_le_one hpow).mpr (by linarith [hM k])
      refine (hCk x _ hlo hup).trans (ENNReal.ofReal_le_ofReal ?_)
      have hid : cfg.N k ^ (q * cfg.S / 2) * (2 / cfg.N k ^ q) ^ cfg.S =
          (2 : ℝ) ^ cfg.S * cfg.N k ^ (-(q * cfg.S / 2)) := by
        rw [Real.div_rpow (by norm_num) hpow.le, ← Real.rpow_mul (hNp k).le,
          Real.rpow_neg (hNp k).le]
        have hsplit : cfg.N k ^ (q * cfg.S) =
            cfg.N k ^ (q * cfg.S / 2) * cfg.N k ^ (q * cfg.S / 2) := by
          rw [← Real.rpow_add (hNp k)]; congr 1; ring
        rw [hsplit]
        have hp : cfg.N k ^ (q * cfg.S / 2) ≠ 0 := (Real.rpow_pos_of_pos (hNp k) _).ne'
        field_simp
      rw [hid]
      apply (le_div_iff₀ (show 0 < 36 * M k * cfg.K k by positivity)).mpr
      calc ((2 : ℝ) ^ cfg.S * cfg.N k ^ (-(q * cfg.S / 2))) * (36 * M k * cfg.K k)
          = (36 * (2 : ℝ) ^ cfg.S) * (M k * cfg.K k) * cfg.N k ^ (-(q * cfg.S / 2)) := by ring
        _ ≤ (36 * (2 : ℝ) ^ cfg.S) * R k ^ 2 * cfg.N k ^ (-(q * cfg.S / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hNp k).le _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (mul_le_mul (le_max_left _ _) (le_max_right _ _) hKpos.le
            (le_trans hMpos.le (le_max_left _ _))).trans_eq (pow_two _).symm
        _ ≤ 1 := hDk.le
  obtain ⟨t, ht, htlim, htsub, htgood⟩ :=
    Submission.Obl.k4_scalar_grid_cartesian_field.exists_subpower_accuracy hN P hP
  refine ⟨fun k => cfg.N k ^ min (aξ / 2) (t k), ?_, ?_, htgood⟩
  · intro k
    exact Real.one_le_rpow (hN k) (lt_min (by positivity) (ht k)).le
  · intro ε hε
    filter_upwards [htsub.2 ε hε] with k hk
    exact (Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_right _ _)).trans hk

end Submission.Obl.k4_narrow_projected_row_parents
