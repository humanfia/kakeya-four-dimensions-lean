-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismAdjacency.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file PrismAdjacency.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma prism_axis_mem {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : |t| ≤ 1)
    {c e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    c + t • e₃ ∈ Prism a b c e₁ e₂ e₃ := by
  have h₁ : inner ℝ e₁ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (0 : Fin 3) 2
  have h₂ : inner ℝ e₂ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (1 : Fin 3) 2
  have h₃ : inner ℝ e₃ e₃ = 1 := by
    simpa using orthonormal_iff_ite.mp he (2 : Fin 3) 2
  simpa only [Prism, mem_ofPred_eq, add_sub_cancel_left, inner_smul_right,
    h₁, h₂, h₃, mul_zero, mul_one, abs_zero] using And.intro ha (And.intro hb ht)

lemma thickening_projection_lt {r s : ℝ} {S : Set Space} {e c y : Space}
    (he : ‖e‖ = 1) (hS : ∀ z ∈ S, |inner ℝ e (z - c)| ≤ s)
    (hy : y ∈ Metric.thickening r S) : |inner ℝ e (y - c)| < s + r := by
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp hy
  have hi : |inner ℝ e (y - z)| < r :=
    (abs_real_inner_le_norm _ _).trans_lt (by simpa [he, ← dist_eq_norm] using hyz)
  have hadd : inner ℝ e (y - c) = inner ℝ e (y - z) + inner ℝ e (z - c) := by
    simp only [inner_sub_right]
    ring
  rw [hadd]
  exact (abs_add_le _ _).trans_lt (by linarith [hS z hz])

lemma axis_projection_lt {r s : ℝ} {S : Set Space} {e c z v : Space}
    (he : ‖e‖ = 1) (hS : ∀ y ∈ S, |inner ℝ e (y - c)| ≤ s)
    (hplus : z + v ∈ Metric.thickening r S)
    (hminus : z - v ∈ Metric.thickening r S) : |inner ℝ e v| < s + r := by
  have hp := thickening_projection_lt he hS hplus
  have hm := thickening_projection_lt he hS hminus
  simp only [inner_sub_right, inner_add_right] at hp hm
  rw [abs_lt] at hp hm ⊢
  constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

/-- Small components in the two transverse frame directions force a unit vector
close to one of the two orientations of the long frame direction. -/
lemma unit_axis_close_of_transverse {e₁ e₂ e₃ v : Space} {q : ℝ}
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) (hv : ‖v‖ = 1)
    (h₁ : |inner ℝ e₁ v| ≤ q) (h₂ : |inner ℝ e₂ v| ≤ q) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖v - s • e₃‖ ≤ 2 * q := by
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := basis_of_frame he
  have hnorm : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  have hq : 0 ≤ q := (abs_nonneg _).trans h₁
  have hsquares : (inner ℝ e₁ v) ^ 2 + (inner ℝ e₂ v) ^ 2 +
      (inner ℝ e₃ v) ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three, hB₁, hB₂, hB₃, hv, one_pow] using
      B.sum_sq_inner_right v
  have hsq₁ : (inner ℝ e₁ v) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq).mpr (by simpa only [abs_of_nonneg hq] using h₁)
  have hsq₂ : (inner ℝ e₂ v) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq).mpr (by simpa only [abs_of_nonneg hq] using h₂)
  have h₃ : |inner ℝ e₃ v| ≤ 1 := by
    simpa only [hnorm, hv, mul_one] using abs_real_inner_le_norm e₃ v
  rcases le_total 0 (inner ℝ e₃ v) with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul]
    have hc : inner ℝ e₃ v ≤ 1 := (le_abs_self _).trans h₃
    have hgamma : (inner ℝ e₃ v) ^ 2 ≤ inner ℝ e₃ v := by nlinarith
    have hdist : ‖v - e₃‖ ^ 2 = 2 - 2 * inner ℝ e₃ v := by
      rw [norm_sub_sq_real, hv, hnorm, real_inner_comm v e₃]
      ring
    nlinarith [norm_nonneg (v - e₃)]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_smul, sub_neg_eq_add]
    have hc : -1 ≤ inner ℝ e₃ v := (abs_le.mp h₃).1
    have hgamma : (inner ℝ e₃ v) ^ 2 ≤ -inner ℝ e₃ v := by nlinarith
    have hdist : ‖v + e₃‖ ^ 2 = 2 + 2 * inner ℝ e₃ v := by
      rw [norm_add_sq_real, hv, hnorm, real_inner_comm v e₃]
      ring
    nlinarith [norm_nonneg (v + e₃)]

/-- Nearby congruent-length prisms have nearby unoriented long axes. -/
theorem prism_axes_close_of_subset_thickening
    {a b a' b' r : ℝ} (hab : a ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    {c e₁ e₂ e₃ c' f₁ f₂ f₃ : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hf : Orthonormal ℝ ![f₁, f₂, f₃])
    (hsub : Prism a' b' c' f₁ f₂ f₃ ⊆ Metric.thickening r (Prism a b c e₁ e₂ e₃)) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖f₃ - s • e₃‖ ≤ 2 * (b + r) := by
  have hp : c' + f₃ ∈ Metric.thickening r (Prism a b c e₁ e₂ e₃) :=
    hsub (by simpa using prism_axis_mem ha' hb' (show |(1 : ℝ)| ≤ 1 by norm_num) hf)
  have hm : c' - f₃ ∈ Metric.thickening r (Prism a b c e₁ e₂ e₃) :=
    hsub (by simpa only [neg_one_smul, ← sub_eq_add_neg] using
      prism_axis_mem ha' hb' (show |(-1 : ℝ)| ≤ 1 by norm_num) hf)
  have h₁ : |inner ℝ e₁ f₃| < a + r := axis_projection_lt
    (by simpa using he.norm_eq_one (0 : Fin 3)) (fun _ h => h.1) hp hm
  have h₂ : |inner ℝ e₂ f₃| < b + r := axis_projection_lt
    (by simpa using he.norm_eq_one (1 : Fin 3)) (fun _ h => h.2.1) hp hm
  exact unit_axis_close_of_transverse he (by simpa using hf.norm_eq_one (2 : Fin 3))
    (h₁.le.trans (by linarith)) h₂.le

/-- Literal thickening containment also controls the longitudinal displacement
of congruent-length prisms, not just their transverse position and axis. -/
theorem prism_centers_close_of_subset_thickening
    {a b a' b' : ℝ} (hab : a ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hb1 : b ≤ 1)
    {c e₁ e₂ e₃ c' f₁ f₂ f₃ : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hf : Orthonormal ℝ ![f₁, f₂, f₃])
    (hsub : Prism a' b' c' f₁ f₂ f₃ ⊆ Metric.thickening b (Prism a b c e₁ e₂ e₃)) :
    ‖c' - c‖ ≤ 10 * b := by
  have hc' : c' ∈ Metric.thickening b (Prism a b c e₁ e₂ e₃) :=
    hsub (by simpa using prism_axis_mem ha' hb' (show |(0 : ℝ)| ≤ 1 by norm_num) hf)
  have h₁ : |inner ℝ e₁ (c' - c)| < a + b := thickening_projection_lt
    (by simpa using he.norm_eq_one (0 : Fin 3)) (fun _ h => h.1) hc'
  have h₂ : |inner ℝ e₂ (c' - c)| < 2 * b := by
    simpa only [two_mul] using thickening_projection_lt
      (by simpa using he.norm_eq_one (1 : Fin 3)) (fun _ h => h.2.1) hc'
  have hb : 0 ≤ b := by linarith [abs_nonneg (inner ℝ e₂ (c' - c))]
  have hp : c' + f₃ ∈ Metric.thickening b (Prism a b c e₁ e₂ e₃) :=
    hsub (by simpa using prism_axis_mem ha' hb' (show |(1 : ℝ)| ≤ 1 by norm_num) hf)
  have hm : c' - f₃ ∈ Metric.thickening b (Prism a b c e₁ e₂ e₃) :=
    hsub (by simpa only [neg_one_smul, ← sub_eq_add_neg] using
      prism_axis_mem ha' hb' (show |(-1 : ℝ)| ≤ 1 by norm_num) hf)
  have he₃ : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  have hf₃ : ‖f₃‖ = 1 := by simpa using hf.norm_eq_one (2 : Fin 3)
  have hp' := thickening_projection_lt he₃ (fun _ h => h.2.2) hp
  have hm' := thickening_projection_lt he₃ (fun _ h => h.2.2) hm
  have hlong : |inner ℝ e₃ (c' - c)| + |inner ℝ e₃ f₃| ≤ 1 + b := by
    simp only [inner_sub_right, inner_add_right] at hp' hm' ⊢
    have hp'' := abs_le.mp hp'.le
    have hm'' := abs_le.mp hm'.le
    rcases le_total 0 (inner ℝ e₃ c' - inner ℝ e₃ c) with hcpos | hcneg <;>
      rcases le_total 0 (inner ℝ e₃ f₃) with hfpos | hfneg
    · rw [abs_of_nonneg hcpos, abs_of_nonneg hfpos]
      linarith
    · rw [abs_of_nonneg hcpos, abs_of_nonpos hfneg]
      linarith
    · rw [abs_of_nonpos hcneg, abs_of_nonneg hfpos]
      linarith
    · rw [abs_of_nonpos hcneg, abs_of_nonpos hfneg]
      linarith
  obtain ⟨s, hs, haxis⟩ := prism_axes_close_of_subset_thickening hab ha' hb' he hf hsub
  have hangle : 1 - |inner ℝ e₃ f₃| ≤ 8 * b ^ 2 := by
    rcases hs with rfl | rfl
    · simp only [one_smul] at haxis
      have hsq := (sq_le_sq₀ (norm_nonneg (f₃ - e₃)) (by positivity : 0 ≤ 2 * (b + b))).mpr haxis
      rw [norm_sub_sq_real, hf₃, he₃, ← real_inner_comm f₃ e₃] at hsq
      nlinarith [le_abs_self (inner ℝ e₃ f₃)]
    · simp only [neg_one_smul, sub_neg_eq_add] at haxis
      have hsq := (sq_le_sq₀ (norm_nonneg (f₃ + e₃)) (by positivity : 0 ≤ 2 * (b + b))).mpr haxis
      rw [norm_add_sq_real, hf₃, he₃, ← real_inner_comm f₃ e₃] at hsq
      nlinarith [neg_le_abs (inner ℝ e₃ f₃)]
  have h₃ : |inner ℝ e₃ (c' - c)| ≤ 9 * b := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hb1)]
  have hsq₁ : (inner ℝ e₁ (c' - c)) ^ 2 ≤ (2 * b) ^ 2 :=
    (sq_le_sq).mpr (by rw [abs_of_nonneg (by positivity : 0 ≤ 2 * b)]; linarith)
  have hsq₂ : (inner ℝ e₂ (c' - c)) ^ 2 ≤ (2 * b) ^ 2 :=
    (sq_le_sq).mpr (by simpa only [abs_of_nonneg (by positivity : 0 ≤ 2 * b)] using h₂.le)
  have hsq₃ : (inner ℝ e₃ (c' - c)) ^ 2 ≤ (9 * b) ^ 2 :=
    (sq_le_sq).mpr (by simpa only [abs_of_nonneg (by positivity : 0 ≤ 9 * b)] using h₃)
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := basis_of_frame he
  have hnorm := B.sum_sq_inner_right (c' - c)
  simp only [Fin.sum_univ_three, hB₁, hB₂, hB₃] at hnorm
  nlinarith [norm_nonneg (c' - c)]

/-- The corresponding spatial criterion preserves labels even when separation
comes from longitudinal position rather than the direction of the long axis. -/
theorem prism_neighbor_same_spatial_label {I : Type*} {p : ℕ} {a b r : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (c e₁ e₂ e₃ : Fin p → Space)
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) (label : Fin p → I) (z : I → Space)
    (hcenter : ∀ j, dist (c j) (z (label j)) ≤ r)
    (hsep : ∀ j j', label j ≠ label j' → 2 * r + 10 * b < dist (z (label j)) (z (label j')))
    {j j' : Fin p}
    (hnear : Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
      Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))) :
    label j = label j' := by
  by_contra hne
  have hc := prism_centers_close_of_subset_thickening hab ha (ha.trans hab) hb1
    (he j) (he j') hnear
  have hcc : dist (c j) (c j') ≤ 10 * b := by
    simpa only [dist_eq_norm, norm_sub_rev] using hc
  have hdist : dist (z (label j)) (z (label j')) ≤ 2 * r + 10 * b := by
    calc
      _ ≤ dist (z (label j)) (c j) + dist (c j) (z (label j')) := dist_triangle _ _ _
      _ ≤ dist (z (label j)) (c j) + (dist (c j) (c j') + dist (c j') (z (label j'))) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ ≤ _ := by
        rw [dist_comm (z (label j)) (c j)]
        linarith [hcenter j, hcenter j']
  exact (hsep j j' hne).not_ge hdist

/-- Direction-separated labels give the cross-parent exclusion needed to apply
a parentwise Katz--Tao estimate to all neighboring prisms. -/
theorem prism_neighbor_same_label {I : Type*} {p : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (c e₁ e₂ e₃ : Fin p → Space)
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) (label : Fin p → I)
    (hsep : ∀ j j', label j ≠ label j' → ∀ s : ℝ, s = 1 ∨ s = -1 →
      4 * b < ‖e₃ j' - s • e₃ j‖)
    {j j' : Fin p}
    (hnear : Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
      Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))) :
    label j = label j' := by
  by_contra hne
  obtain ⟨s, hs, hdist⟩ := prism_axes_close_of_subset_thickening hab ha (ha.trans hab)
    (he j) (he j') hnear
  have hfar := hsep j j' hne s hs
  linarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
