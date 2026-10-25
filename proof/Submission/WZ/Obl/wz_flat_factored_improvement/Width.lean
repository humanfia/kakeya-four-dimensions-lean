-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Width.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Geometry
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ConvexBox

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

/-- Every linear projection has a fibre of diameter at least `b` in the body.
This is a convenient intrinsic lower bound on its middle width. -/
def WideSection (U : Set Space) (b : ℝ) : Prop :=
  ∀ ℓ : Space →ₗ[ℝ] ℝ, ∃ p ∈ U, ∃ q ∈ U, ℓ (p - q) = 0 ∧ b ≤ dist p q

theorem WideSection.mono {U W : Set Space} {b : ℝ}
    (h : WideSection U b) (hUW : U ⊆ W) : WideSection W b := by
  intro ℓ
  obtain ⟨p, hp, q, hq, hz, hd⟩ := h ℓ
  exact ⟨p, hUW hp, q, hUW hq, hz, hd⟩

/-- Affine normalization preserves a lower middle-width bound quantitatively. -/
theorem WideSection.preimage {U : Set Space} {b L : ℝ}
    (h : WideSection U b) (f : Space ≃ᵃ[ℝ] Space) (hL : 0 < L)
    (hLip : ∀ p q, dist (f p) (f q) ≤ L * dist p q) :
    WideSection (f ⁻¹' U) (b / L) := by
  intro ℓ
  obtain ⟨p, hp, q, hq, hz, hd⟩ := h (ℓ.comp f.symm.linear.toLinearMap)
  refine ⟨f.symm p, by simpa, f.symm q, by simpa, ?_, ?_⟩
  · have he : f.symm p - f.symm q = f.symm.linear (p - q) := by
      have hh := f.symm.map_vadd q (p - q)
      simp only [vadd_eq_add, sub_add_cancel] at hh
      exact sub_eq_iff_eq_add.mpr hh
    rw [he]
    exact hz
  · apply (div_le_iff₀ hL).mpr
    have hh := hLip (f.symm p) (f.symm q)
    simp only [f.apply_symm_apply] at hh
    nlinarith only [hd, hh]

/-- The middle half-width of any ordered outer box controls every fibre diameter. -/
theorem middle_width_lower {U : Set Space} {b : ℝ} (h : WideSection U b)
    (w : Fin 3 → ℝ) (c : Space) (u : OrthonormalBasis (Fin 3) ℝ Space)
    (hw : ∀ i, 0 ≤ w i) (horder : Antitone w)
    (hbox : U ⊆ orthogonalBox w c u) : b ≤ 4 * w 1 := by
  obtain ⟨p, hp, q, hq, hz, hd⟩ := h (innerSL ℝ (u 0)).toLinearMap
  have hp' := hbox hp
  have hq' := hbox hq
  have hw1 := hw 1
  have hcoord (i : Fin 3) : |u.repr (p - q) i| ≤ 2 * w 1 := by
    rw [OrthonormalBasis.repr_apply_apply]
    by_cases hi : i = 0
    · subst i
      change inner ℝ (u 0) (p - q) = 0 at hz
      rw [hz, abs_zero]
      positivity
    · have hwi : w i ≤ w 1 := horder (by fin_cases i <;> simp_all)
      have he : inner ℝ (u i) (p - q) =
          inner ℝ (u i) (p - c) - inner ℝ (u i) (q - c) := by
        rw [← inner_sub_right]
        congr 1
        abel
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hp' i, hq' i])
  have hn := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
    (by positivity : 0 ≤ 2 * w 1) hcoord
  rw [u.repr.norm_map] at hn
  rw [dist_eq_norm] at hd
  linarith

/-- A two-dimensional diamond in a body supplies a wide section for every projection. -/
theorem wideSection_of_diamond {U : Set Space} {r : ℝ} (hr : 0 ≤ r)
    (c e f : Space) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    (hdiamond : ∀ s t : ℝ, |s| + |t| ≤ r → c + s • e + t • f ∈ U) :
    WideSection U (r / 2) := by
  intro ℓ
  have hc : c ∈ U := by simpa using hdiamond 0 0 (by simpa using hr)
  have hselfe : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hselff : inner ℝ f f = 1 := by rw [real_inner_self_eq_norm_sq, hf]; norm_num
  have hfe : inner ℝ f e = 0 := by rwa [real_inner_comm]
  have hcase (e f : Space) (he : ‖e‖ = 1) (hef : inner ℝ e f = 0)
      (hself : inner ℝ e e = 1)
      (hdiamond : ∀ s t : ℝ, |s| + |t| ≤ r → c + s • e + t • f ∈ U)
      (hcmp : |ℓ e| ≤ |ℓ f|) :
      ∃ p ∈ U, ∃ q ∈ U, ℓ (p - q) = 0 ∧ r / 2 ≤ dist p q := by
    by_cases hz : ℓ f = 0
    · have hz' : ℓ e = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hz] using hcmp) (abs_nonneg _))
      refine ⟨c + (r / 2) • e, ?_, c, hc, ?_, ?_⟩
      · simpa using hdiamond (r / 2) 0 (by rw [abs_of_nonneg (by positivity)]; simp; linarith)
      · simp [hz']
      · simp [dist_eq_norm, norm_smul, he, abs_of_nonneg hr]
    · let t : ℝ := -(r / 2) * (ℓ e / ℓ f)
      have ht : |t| ≤ r / 2 := by
        have hh : |ℓ e / ℓ f| ≤ 1 := by
          rw [abs_div, div_le_one (abs_pos.mpr hz)]
          exact hcmp
        calc
          |t| = (r / 2) * |ℓ e / ℓ f| := by
            rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
          _ ≤ (r / 2) * 1 := mul_le_mul_of_nonneg_left hh (by positivity)
          _ = _ := mul_one _
      let p := c + (r / 2) • e + t • f
      have hp : p ∈ U := hdiamond _ _ (by rw [abs_of_nonneg (by positivity)]; linarith)
      have hdiff : p - c = (r / 2) • e + t • f := by dsimp [p]; abel
      refine ⟨p, hp, c, hc, ?_, ?_⟩
      · rw [hdiff, map_add, map_smul, map_smul]
        dsimp [t]
        field_simp
        ring
      · have hh := abs_real_inner_le_norm e (p - c)
        rw [hdiff, inner_add_right, inner_smul_right, inner_smul_right,
          hself, hef, mul_one, mul_zero, add_zero, abs_of_nonneg (by positivity), he, one_mul] at hh
        simpa only [dist_eq_norm, hdiff] using hh
  rcases le_total |ℓ e| |ℓ f| with hcmp | hcmp
  · exact hcase e f he hef hselfe hdiamond hcmp
  · apply hcase f e hf hfe hselff _ hcmp
    intro s t hst
    simpa only [add_assoc, add_left_comm, add_comm] using
      hdiamond t s (by simpa only [add_comm] using hst)

/-- Standard prisms have a middle-width lower bound, independently of their thickness. -/
theorem standardPrism_wideSection {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb2 : b ≤ 2) :
    WideSection (StandardPrism a b) (b / 2) := by
  let u := EuclideanSpace.basisFun (Fin 3) ℝ
  apply wideSection_of_diamond hb 0 (u 1) (u 2) (u.norm_eq_one _) (u.norm_eq_one _)
    (by simpa using u.orthonormal.2 (by decide : (1 : Fin 3) ≠ 2))
  intro s t hst
  have hs : |s| ≤ b := by linarith [abs_nonneg t]
  have ht : |t| ≤ 2 := by linarith [abs_nonneg s]
  simpa [StandardPrism, u, EuclideanSpace.basisFun_apply, ha, hs, ht]

end WangZahlLot.Obl.wz_flat_factored_improvement
