import Submission.Obl.k4_finite_row_graph_assembly.FiniteInput

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/DirectionCap.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Ratios

namespace Submission.Obl.k4_finite_row_graph_assembly

theorem selected_ratio_cap {h K R s : ℝ} (f : FiniteIncidenceData h K R s)
    (hh : 0 < h) (hK : 1 ≤ K) (hR : 2 ≤ R) (hKR : K ≤ R) (hs : 0 ≤ s)
    {d₁ d₂ : ℤ} (hd₁ : d₁ ∈ f.directions) (hd₂ : d₂ ∈ f.directions)
    (hsep : 1 / R ≤ |f.velocity d₂ - f.velocity d₁|)
    (D : Finset ℤ) (hD : D ⊆ f.directions) (hDne : D.Nonempty)
    (hcard : (f.directions.card : ℝ) / (512 * K ^ 9) ≤ (D.card : ℝ))
    (hseparated : ∀ d ∈ D, 1 / R ≤ |f.velocity d - f.velocity d₂|)
    (x r : ℝ) (hr : h ≤ r) (hr1 : r ≤ 1) :
    ((D.filter (fun d => ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d) ∈
      Set.Icc x (x + r))).card : ℝ) / D.card ≤
      (512 * K ^ 10 * (R ^ 6) ^ s) * r ^ s := by
  classical
  have hKpos : 0 < K := by linarith
  have hRpos : 0 < R := by linarith
  have hrpos : 0 < r := hh.trans_le hr
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hDne.card_pos
  have hM : (f.directions.card : ℝ) ≤ 512 * K ^ 9 * D.card := by
    have := (div_le_iff₀ (show 0 < 512 * K ^ 9 by positivity)).mp hcard
    nlinarith
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ (by linarith : 1 ≤ R)
  have hC : 1 ≤ 512 * K ^ 10 := by
    have ht : 1 ≤ K ^ 10 := one_le_pow₀ hK
    linarith
  let Q := D.filter (fun d => ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d) ∈
    Set.Icc x (x + r))
  change (Q.card : ℝ) / D.card ≤ _
  by_cases hscale : R ^ 6 * r ≤ 1
  · by_cases hQ : Q.Nonempty
    · obtain ⟨d₀, hd₀⟩ := hQ
      obtain ⟨hd₀D, hd₀I⟩ := Finset.mem_filter.mp hd₀
      have hd₀dir := hD hd₀D
      have hden (d : ℤ) (hd : d ∈ D) : f.velocity d₂ - f.velocity d ≠ 0 := by
        have hp := (one_div_pos.mpr hRpos).trans_le (hseparated d hd)
        exact sub_ne_zero.mpr (sub_ne_zero.mp (abs_pos.mp hp)).symm
      let a := f.velocity d₀ - R ^ 6 * r / 2
      have hQsub : Q ⊆ f.directions.filter
          (fun d => f.velocity d ∈ Set.Icc a (a + R ^ 6 * r)) := by
        intro d hd
        obtain ⟨hdD, hdI⟩ := Finset.mem_filter.mp hd
        have hdiff : |ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d) -
            ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d₀)| ≤ r := by
          rw [abs_le]
          constructor <;> linarith [hdI.1, hdI.2, hd₀I.1, hd₀I.2]
        have hvel := ratio_inverse_lipschitz (by linarith : 1 ≤ R)
          ((f.velocity_bound d₁ hd₁).trans hKR) ((f.velocity_bound d₂ hd₂).trans hKR)
          ((f.velocity_bound d (hD hdD)).trans hKR)
          ((f.velocity_bound d₀ hd₀dir).trans hKR) hsep (hden d hdD) (hden d₀ hd₀D)
        have h8 : (8 : ℝ) ≤ R ^ 3 := by
          have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR 3
          norm_num at ht
          exact ht
        have hcoef : 4 * R ^ 3 ≤ R ^ 6 / 2 := by
          have ht := mul_le_mul_of_nonneg_right h8 (show 0 ≤ R ^ 3 by positivity)
          nlinarith [show R ^ 3 * R ^ 3 = R ^ 6 by ring]
        have hclose : |f.velocity d - f.velocity d₀| ≤ R ^ 6 * r / 2 := by
          calc
            _ ≤ 4 * R ^ 3 * |ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d) -
                ratio (f.velocity d₁) (f.velocity d₂) (f.velocity d₀)| := hvel
            _ ≤ (R ^ 6 / 2) * r :=
              mul_le_mul hcoef hdiff (abs_nonneg _) (by positivity)
            _ = _ := by ring
        rw [abs_le] at hclose
        exact Finset.mem_filter.mpr ⟨hD hdD, by dsimp [a]; constructor <;> linarith⟩
      have hcap : (Q.card : ℝ) ≤ K * (R ^ 6 * r) ^ s * f.directions.card :=
        (Nat.cast_le.mpr (Finset.card_le_card hQsub)).trans
          (f.direction_cap a (R ^ 6 * r) (by nlinarith) hscale)
      rw [div_le_iff₀ hDpos]
      calc
        (Q.card : ℝ) ≤ K * (R ^ 6 * r) ^ s * f.directions.card := hcap
        _ ≤ K * (R ^ 6 * r) ^ s * (512 * K ^ 9 * D.card) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        _ = (512 * K ^ 10 * (R ^ 6) ^ s) * r ^ s * D.card := by
          rw [Real.mul_rpow (by positivity) hrpos.le]
          ring
    · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      simp only [he, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  · have hscale' : 1 ≤ R ^ 6 * r := (lt_of_not_ge hscale).le
    have hp : 1 ≤ (R ^ 6) ^ s * r ^ s := by
      rw [← Real.mul_rpow (by positivity) hrpos.le]
      exact Real.one_le_rpow hscale' hs
    calc
      (Q.card : ℝ) / D.card ≤ 1 := by
        rw [div_le_one hDpos]
        exact_mod_cast Finset.card_filter_le D _
      _ ≤ (512 * K ^ 10) * ((R ^ 6) ^ s * r ^ s) := by
        nlinarith
      _ = _ := by ring

end Submission.Obl.k4_finite_row_graph_assembly
