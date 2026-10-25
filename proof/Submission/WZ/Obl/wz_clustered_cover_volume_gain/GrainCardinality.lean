-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainCardinality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseFactorInput

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal

lemma sum_mass_le_fiber_bound {L N : ℕ} (γ : Fin L → Fin N) (H : Fin L → Set V)
    (hHm : ∀ j, MeasurableSet (H j))
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (U : Set V) (hHU : ∀ j, H j ⊆ U) {B : ℝ} (hB : 0 ≤ B)
    (hUB : volume U ≤ ENNReal.ofReal B) :
    (∑ j, volume (H j)) ≤ ENNReal.ofReal (N * B) := by
  have hfibm := measurable_assignedFiber γ hHm
  calc
    _ = ∫⁻ p, ENNReal.ofReal (bodyCount H p) := (lintegral_bodyCount hHm).symm
    _ = ∫⁻ p, ENNReal.ofReal (bodyCount (assignedFiber γ H) p) := by
      congr 1
      funext p
      rw [bodyCount_assignedFiber γ H hdisj]
    _ = ∑ k, volume (assignedFiber γ H k) := lintegral_bodyCount hfibm
    _ ≤ ∑ _k : Fin N, ENNReal.ofReal B := by
      apply Finset.sum_le_sum
      intro k _
      apply (measure_mono ?_).trans hUB
      rintro p ⟨j, _, hp⟩
      exact hHU j hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

lemma admissible_count_eight {δ h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) :
    (n : ℝ) * δ ^ 2 ≤ 8 * δ ^ (-h) := by
  have hh := hA.2.2.2.2.1 (ball (0 : V) 1) (convex_ball _ _)
  have hset : {i : Fin n | T δ (x i) (v i) ⊆ ball (0 : V) 1} = univ :=
    Set.eq_univ_iff_forall.mpr fun i => (hA.2.1 i).2.1
  have hv : volume (ball (0 : V) 1) ≤ ENNReal.ofReal 8 := by
    apply (measure_mono ball_subset_closedBall).trans
    simpa using closedBall_volume_upper (0 : V) (by norm_num : (0 : ℝ) ≤ 1)
  have hle : ENNReal.ofReal ((n : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (8 * δ ^ (-h)) := by
    calc
      _ = O (q n {i | T δ (x i) (v i) ⊆ ball (0 : V) 1} * δ ^ 2) := by
        rw [hset]
        simp [q]
      _ ≤ _ := hh
      _ ≤ O (δ ^ (-h)) * ENNReal.ofReal 8 := mul_le_mul' le_rfl hv
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

/-- The frozen average grain density and disjointness within parents prevent
an uncontrolled number of grains, even if some grain shadings are empty. -/
lemma frozen_grain_cardinality {δ h ρ a c : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (H : Fin L → Set V) (γ : Fin L → Fin N)
    (hδa : δ ≤ a) (hac : a ≤ ρ * c) (hρcc : ρ * c ≤ c)
    (hHm : ∀ j, MeasurableSet (H j))
    (hHU : ∀ j, H j ⊆ P a (ρ * c) c (z j) (e j))
    (hUT : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)))
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (hdense : O (δ ^ h * L * a * (ρ * c) * c) ≤ ∑ j, volume (H j)) :
    (L : ℝ) ≤ 4096 * δ ^ (-(2 * h + 5)) := by
  have hN : N ≤ n := Parent.Interfaces.c_coarse_count_le hδ hA hC
  have hTball := (Parent.Interfaces.c_factor_family hδ hδρ hρ1 hA hC).inBall
  have hmass : (∑ j, volume (H j)) ≤ O (512 * n) := by
    apply (sum_mass_le_fiber_bound γ H hHm hdisj (ball (0 : V) 4)
      (fun j => (hHU j).trans ((hUT j).trans (hTball (γ j)))) (by norm_num : (0 : ℝ) ≤ 512)
      ((measure_mono ball_subset_closedBall).trans (by
        convert closedBall_volume_upper (0 : V) (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> norm_num))).trans
    apply ENNReal.ofReal_le_ofReal
    have hN' : (N : ℝ) ≤ n := Nat.cast_le.mpr hN
    nlinarith
  have hmassR : δ ^ h * L * (a * (ρ * c) * c) ≤ 512 * n := by
    have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 512 * n)).mp (hdense.trans hmass)
    nlinarith
  have hn := admissible_count_eight hδ hA
  have hw : δ ^ 3 ≤ a * (ρ * c) * c := by
    have hc : δ ≤ c := hδa.trans (hac.trans hρcc)
    have hρc : δ ≤ ρ * c := hδa.trans hac
    calc
      _ = δ * δ * δ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hδa hρc hδ.le (hδ.trans_le hδa).le) hc hδ.le
        (mul_nonneg (hδ.trans_le hδa).le (hδ.trans_le hρc).le)
  have hlow : δ ^ h * L * δ ^ 3 ≤ 512 * n :=
    (mul_le_mul_of_nonneg_left hw (by positivity)).trans hmassR
  have hscale : δ ^ h * L * δ ^ 5 ≤ 4096 * δ ^ (-h) := by
    have hh := mul_le_mul_of_nonneg_right hlow (sq_nonneg δ)
    nlinarith
  have hpow : δ ^ h * δ ^ 5 = δ ^ (h + 5) := by rw [Real.rpow_add hδ, Real.rpow_ofNat]
  have hdiv : (L : ℝ) ≤ (4096 * δ ^ (-h)) / δ ^ (h + 5) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
    nlinarith [hpow]
  apply hdiv.trans_eq
  rw [div_eq_mul_inv, ← Real.rpow_neg hδ.le, mul_assoc, ← Real.rpow_add hδ]
  congr 2
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
