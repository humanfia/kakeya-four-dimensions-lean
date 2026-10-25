import Submission.Obl.k4_oss_weighted_level_transfer.Integration
import Submission.Obl.k4_oss_weighted_level_transfer.LevelFamily
import Submission.Obl.k4_oss_weighted_level_transfer.PairBound
import Submission.Obl.k4_oss_weighted_level_transfer.Parameters

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable
attribute [local instance] counting_finite atomic_finite ofReal_dirac_finite

/-- Transfer the uniform finite gain to arbitrary finite nonnegative weights. -/
theorem finite_transfer_of_gain (s γ : ℝ) (hs : 0 < s) (hγ : 0 < γ)
    (hgain : ∃ θ r₀ : ℝ, 0 < θ ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < r₀ → FiniteGain s γ θ δ) : FiniteTransfer s γ := by
  obtain ⟨θ, r₀, hθ, hr₀, hr₀1, hfinite⟩ := hgain
  obtain ⟨a, r, M, ha, haθ, haγ, ha1, hr, hr1, hrr₀, hMa, hscale⟩ :=
    exists_transfer_parameters hθ hγ hr₀
  refine ⟨a, a, r, ha, ha, hr, hr1, ?_⟩
  intro δ hδ hδr S p Q hp hsep habs hcard hmass hcap hsquare hQ ν hνprob hν hνcap
  letI : IsProbabilityMeasure ν := hνprob
  have hδ1 : δ < 1 := hδr.trans_le hr1
  have hQ0 : 0 ≤ Q := (Real.rpow_pos_of_pos hδ _).le.trans hQ
  have hδQ : δ ≤ Q := by
    apply le_trans _ hQ
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (show 1 - γ ≤ 1 by linarith)
  have hG : FiniteGain s γ θ δ := hfinite δ hδ (hδr.trans_le hrr₀)
  have hn : 1 ≤ (M : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hn4 : 1 ≤ ((M : ℝ) + 1) ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 4
  have hC4 : 4 ≤ 390 * ((M : ℝ) + 1) ^ 4 := by linarith
  have hsmall4 : 4 * δ ^ a ≤ 1 :=
    (mul_le_mul_of_nonneg_right hC4 (Real.rpow_pos_of_pos hδ a).le).trans (hscale δ hδ hδr)
  have hsmall2 : 2 * δ ^ a ≤ 1 := by nlinarith [Real.rpow_pos_of_pos hδ a]
  have hδa : δ ≤ δ ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (show a ≤ 1 by linarith)
  have hsmallδ : 4 * δ ≤ 1 := (mul_le_mul_of_nonneg_left hδa (by norm_num)).trans hsmall4
  let b := δ ^ a
  have hb : 0 < b := Real.rpow_pos_of_pos hδ _
  have hb1 : b ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le ha.le
  have hbinv : 1 / b = δ ^ (-a) := by simp only [one_div, b, Real.rpow_neg hδ.le]
  have hqdiv : Q / b ^ 2 = (δ ^ (-a)) ^ 2 * Q := by
    rw [← hbinv]
    field_simp <;> ring
  have htailw : b ^ M ≤ δ ^ 3 := by
    dsimp only [b]
    rw [← Real.rpow_mul_natCast hδ.le a M]
    have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le hMa
    rw [show δ ^ (3 : ℝ) = δ ^ (3 : ℕ) from Real.rpow_natCast δ 3] at hh
    exact hh
  have htail : b ^ M * (S.card : ℝ) ≤ δ := by
    calc
      _ ≤ δ ^ 3 * (4 / δ) := mul_le_mul htailw hcard (by positivity) (by positivity)
      _ = 4 * δ ^ 2 := by field_simp <;> ring
      _ ≤ δ := by nlinarith [mul_le_mul_of_nonneg_right hsmallδ hδ.le]
  let I := Option (Fin M)
  let A : I → Finset ℝ := levelSet S p b M
  let B : I → Finset ℝ := fun i => reflectSet (A i)
  let w : I → ℝ := levelWeight b M
  have hw (i : I) : 0 ≤ w i := levelWeight_nonneg hb.le M i
  have hAS (i : I) : A i ⊆ S := levelSet_subset S p b M i
  have hsepA (i : I) : ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hxy => hsep x (hAS i hx) y (hAS i hy) hxy
  have hsepB (i : I) : ∀ x ∈ B i, ∀ y ∈ B i, x ≠ y → δ ≤ dist x y :=
    reflectSet_separated hδ.le (hsepA i)
  have hmA (i : I) : w i * (A i).card ≤ δ ^ (-a) :=
    (level_family_mass hb hb1 (fun x hx => hp x) hmass hδ1.le M htail i).trans_eq hbinv
  have hqA (i : I) : w i ^ 2 * (A i).card ≤ (δ ^ (-a)) ^ 2 * Q :=
    (level_family_square hb hb1 hδ.le hδQ hsquare M htail i).trans_eq hqdiv
  have hcapA (i : I) (hm : δ ^ (10 * a) < w i * (A i).card) :
      ∀ x u : ℝ, δ ≤ u → ((A i).filter (fun y => dist y x ≤ u)).card ≤
        δ ^ (-θ) * u ^ (s / 2) * ((A i).card : ℝ) :=
    level_family_frostman hδ hδ1.le ha (by linarith) hs.le (by linarith) hsmall2
      (fun x hx => hp x) hcap M htail i hm
  have hmB (i : I) : w i * (B i).card ≤ δ ^ (-a) := by
    simpa only [B, reflectSet_card] using hmA i
  have hqB (i : I) : w i ^ 2 * (B i).card ≤ (δ ^ (-a)) ^ 2 * Q := by
    simpa only [B, reflectSet_card] using hqA i
  have hcapB (i : I) (hm : δ ^ (10 * a) < w i * (B i).card) :
      ∀ x u : ℝ, δ ≤ u → ((B i).filter (fun y => dist y x ≤ u)).card ≤
        δ ^ (-θ) * u ^ (s / 2) * ((B i).card : ℝ) := by
    have hm' : δ ^ (10 * a) < w i * (A i).card := by simpa only [B, reflectSet_card] using hm
    exact reflectSet_frostman (hcapA i hm')
  have hνθ := direction_cap_of_small_power hδ hδ1.le hs.le (show 2 * a ≤ θ by linarith)
    hsmall4 ν hνcap
  have hpair (i j : I) : w i ^ 2 * w j ^ 2 * averageEnergy δ ν (A i) (B j) ≤
      130 * δ ^ (6 * a) * Q :=
    weighted_pair_bound hδ hδ1 ha (by linarith) (by linarith) hγ hG hQ ν hν hνθ
      (A i) (B j) (w i) (w j) (hw i) (hw j) (hsepA i) (hsepB j)
      (hmA i) (hmB j) (hqA i) (hqB j) (hcapA i) (hcapB j)
  have hsum : (∑ i : I, ∑ j : I, w i ^ 2 * w j ^ 2 * averageEnergy δ ν (A i) (B j)) ≤
      ((M : ℝ) + 1) ^ 2 * (130 * δ ^ (6 * a) * Q) := by
    calc
      _ ≤ ∑ _i : I, ∑ _j : I, 130 * δ ^ (6 * a) * Q :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i j))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, I, Fintype.card_option,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
  have hp6 : δ ^ (6 * a) = δ ^ a * δ ^ (5 * a) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have htotal : 3 * (Fintype.card I : ℝ) * (Fintype.card I : ℝ) *
      (∑ i : I, ∑ j : I, w i ^ 2 * w j ^ 2 * averageEnergy δ ν (A i) (B j)) ≤ δ ^ a * Q := by
    calc
      _ ≤ 3 * (Fintype.card I : ℝ) * (Fintype.card I : ℝ) *
          (((M : ℝ) + 1) ^ 2 * (130 * δ ^ (6 * a) * Q)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (390 * ((M : ℝ) + 1) ^ 4 * δ ^ a) * δ ^ (5 * a) * Q := by
        simp only [I, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        rw [hp6]
        ring
      _ ≤ 1 * δ ^ (5 * a) * Q := by gcongr; exact hscale δ hδ hδr
      _ ≤ δ ^ a * Q := by
        simp only [one_mul]
        apply mul_le_mul_of_nonneg_right _ hQ0
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
  letI (i : I) : IsFiniteMeasure (ENNReal.ofReal (w i) • counting (A i)) :=
    (counting (A i)).smul_finite ENNReal.ofReal_ne_top
  letI (i : I) : IsFiniteMeasure (ENNReal.ofReal (w i) • counting (B i)) :=
    (counting (B i)).smul_finite ENNReal.ofReal_ne_top
  have hdom : atomic S p ≤ ∑ i, ENNReal.ofReal (w i) • counting (A i) :=
    atomic_le_level_sum S p A w hw hAS
      (fun x hx => level_family_cover hb.le (fun x hx => hp x) hmass M hx)
  have hdomB : (atomic S p).map (fun x : ℝ => -2 * x) ≤
      ∑ i, ENNReal.ofReal (w i) • counting (B i) := by
    rw [← map_reflect_level_sum A w]
    exact Measure.map_mono hdom (by fun_prop)
  calc
    _ ≤ ∫⁻ t, collision (16 * δ)
        (projected t (∑ i, ENNReal.ofReal (w i) • counting (A i))
          (∑ j, ENNReal.ofReal (w j) • counting (B j))) ∂ν := by
      apply lintegral_mono
      intro t
      exact (collisionSum_le_projected S p hp hδ t).trans
        (collision_mono (projected_mono t hdom hdomB) (16 * δ))
    _ ≤ ENNReal.ofReal (3 * (Fintype.card I : ℝ) * (Fintype.card I : ℝ) *
        ∑ i : I, ∑ j : I, w i ^ 2 * w j ^ 2 * averageEnergy δ ν (A i) (B j)) :=
      averaged_level_sum_real_le hδ ν A B w w hw hw hsepA
    _ ≤ _ := ENNReal.ofReal_le_ofReal htotal

end Submission.Obl.k4_oss_weighted_level_transfer
