-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.TransverseDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BadIncidences
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineFillingDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPrism

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

def transverseDensity (a b lam h s : ℝ) : ℝ :=
  ((lam / 2 / (Scale.dyExp 1 (s / 2) + 1 : ℕ) / 16000) ^ 2 * h ^ 2 /
    (52428800000000 * (257 ^ 4 : ℕ) * (1 + Real.log (b / a))))

lemma transverseDensity_pos {a b lam h s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlam : 0 < lam) (hh : 0 < h) :
    0 < transverseDensity a b lam h s := by
  have hlog : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  unfold transverseDensity
  positivity

/-- Transverse incidences force a large common physical ball density;
otherwise a half-mass refinement is pointwise narrow. -/
theorem regular_prism_transverse_or_narrow {n : ℕ} {a b lam h s r L J lamBall : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hlam : 0 < lam) (hh : 0 < h) (hs : 0 < s) (hs1 : s ≤ 1)
    (has : a ≤ s * b) (hr : 0 < r) (hL : 0 ≤ L)
    (hLr : L * r ≤ (s / 2) * b) (hJ : 0 < J) (hlamBall : 0 ≤ lamBall)
    (f : V ≃ᵃ[ℝ] V) (c : Fin n → V)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (H : Fin n → Set V) (Z U : Set V)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hHm : ∀ i, MeasurableSet (H i)) (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hHZ : ∀ i, f '' H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hdense : ∀ i, O lam * μ (prism a b (c i) (u i)) ≤ μ (H i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lamBall * r ^ 3)) :
    transverseDensity a b lam h s ≤ 46080 * lamBall ∨
    ∃ G : Fin n → Set V,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 2 : ℝ≥0∞) * volume (H i) ≤ volume (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → pd (u i 0) (u j 0) ≤ s := by
  have hb0 : 0 < b := ha.trans_le hab
  have hfin (i : Fin n) : volume (H i) ≠ ⊤ :=
    ne_top_of_le_ne_top (prism_totallyBounded a b (c i) (u i).orthonormal).isBounded.measure_lt_top.ne
      (measure_mono (hHU i))
  have hthreshold (i : Fin n) :
      O (lam / 2) * μ (prism a b (c i) (u i)) ≤ (1 / 2 : ℝ≥0∞) * μ (H i) := by
    calc
      _ = (1 / 2 : ℝ≥0∞) * (O lam * μ (prism a b (c i) (u i))) := by
        rw [← mul_assoc]
        congr 1
        change ENNReal.ofReal (lam / 2) = _
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num [O]
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ _ := mul_le_mul' le_rfl (hdense i)
  rcases remove_bad_incidences volume H (fun i j => s < pd (u j 0) (u i 0))
      (fun i => O (lam / 2) * μ (prism a b (c i) (u i))) hHm hfin hthreshold with hbad | hgood
  · obtain ⟨i, A, hAm, hAH, hden, htrans⟩ := hbad
    obtain ⟨t, hst, ht1, hfill⟩ := transverse_global_filling ha hab hb hh (half_pos hlam)
      hs hs1 c (fun i => u i) H (c i) (u i) A (fun i => (u i).orthonormal) hHm hHU hregular
      (u i).orthonormal hAm (hAH.trans (hHU i)) hden
      (fun p hp => by obtain ⟨j, hj, hpj⟩ := htrans p hp; exact ⟨j, hpj, hj.le⟩)
    let F := {p | |inner ℝ (u i 0) (p - c i)| ≤ 3 * a + 2 * t * b} ∩
      (cTube b (c i) (u i) ∩ ⋃ j, H j)
    have ht : 0 < t := (half_pos hs).trans_le hst
    have haθ : a ≤ 2 * t * b := by nlinarith [mul_le_mul_of_nonneg_right hst hb0.le]
    have hFZ : f '' F ⊆ Z := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2.2
      exact hHZ j ⟨p, hj, rfl⟩
    left
    apply affine_filling_forces_ball_density ha.le hb0 (hb.trans (by norm_num)) ht ht1 haθ
      (transverseDensity_pos ha hab hlam hh).le hlamBall hr hL
      (hLr.trans (mul_le_mul_of_nonneg_right hst hb0.le)) hJ f (c i) (u i) F U hvol hLip
      ?_ (hFZ.trans hZU) hUball ?_ (fun p hp => hupper p (hFZ hp))
    · intro p hp j
      have hcoord := cTube_coordinate_bounds (u i).orthonormal hp.2.1
      fin_cases j
      · exact hp.1
      · exact hcoord.1 1 (by decide)
      · calc
          _ ≤ ‖u i 2‖ * ‖p - c i‖ := abs_real_inner_le_norm _ _
          _ = ‖p - c i‖ := by rw [(u i).orthonormal.1 2, one_mul]
          _ ≤ 4 * b + 1 / 2 := hcoord.2
          _ ≤ 1 := by linarith
    · convert hfill using 1
      congr 1
      dsimp [transverseDensity]
      ring
  · obtain ⟨G, hG, hrel⟩ := hgood
    right
    refine ⟨G, hG, ?_⟩
    intro i j p hi hj
    exact le_of_not_gt (hrel j i p hj hi)

 /-- The regularity hypothesis in the dichotomy can be obtained from
 individual average density, at the cost of another half of the mass. -/
 theorem prism_transverse_or_narrow {n : ℕ} {a b lam s r L J lamBall : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hlam : 0 < lam) (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * b)
    (hr : 0 < r) (hL : 0 ≤ L) (hLr : L * r ≤ (s / 2) * b)
    (hJ : 0 < J) (hlamBall : 0 ≤ lamBall)
    (f : V ≃ᵃ[ℝ] V) (c : Fin n → V)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (H : Fin n → Set V) (Z U : Set V)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hHm : ∀ i, MeasurableSet (H i)) (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hHZ : ∀ i, f '' H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hdense : ∀ i, O lam * μ (prism a b (c i) (u i)) ≤ μ (H i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lamBall * r ^ 3)) :
    transverseDensity a b (lam / 2) (lam / 16000) s ≤ 46080 * lamBall ∨
    ∃ G : Fin n → Set V,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 4 : ℝ≥0∞) * volume (H i) ≤ volume (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → pd (u i 0) (u j 0) ≤ s := by
  choose H' hHm' hsub hmass hreg using fun i =>
    prism_regular_subshading hlam.le (ha.trans_le hab) (c i) (u i) (u i).orthonormal
      (H i) (hHm i) (hHU i) (hdense i)
  have hdense' (i : Fin n) : O (lam / 2) * μ (prism a b (c i) (u i)) ≤ μ (H' i) := by
    calc
      _ = (1 / 2 : ℝ≥0∞) * (O lam * μ (prism a b (c i) (u i))) := by
        rw [← mul_assoc]
        congr 1
        change ENNReal.ofReal (lam / 2) = _
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num [O]
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ (1 / 2 : ℝ≥0∞) * μ (H i) := mul_le_mul' le_rfl (hdense i)
      _ ≤ _ := hmass i
  rcases regular_prism_transverse_or_narrow ha hab hb (half_pos hlam) (by positivity)
    hs hs1 has hr hL hLr hJ hlamBall f c u H' Z U hvol hLip hHm'
    (fun i => (hsub i).trans (hHU i)) (fun i => (image_mono (hsub i)).trans (hHZ i))
    hZU hUball hdense' hreg hupper with hd | href
  · exact Or.inl hd
  · obtain ⟨G, hG, hnarrow⟩ := href
    right
    refine ⟨G, fun i => ⟨(hG i).1, (hG i).2.1.trans (hsub i), ?_⟩, hnarrow⟩
    calc
      _ = (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * volume (H i)) := by
        rw [← mul_assoc]
        congr 1
        rw [one_div, one_div, ← ENNReal.mul_inv] <;> norm_num
      _ ≤ (1 / 2 : ℝ≥0∞) * volume (H' i) := mul_le_mul' le_rfl (hmass i)
      _ ≤ volume (G i) := (hG i).2.2

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
