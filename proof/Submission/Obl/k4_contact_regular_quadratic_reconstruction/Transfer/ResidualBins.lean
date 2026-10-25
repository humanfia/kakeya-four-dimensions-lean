/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/ResidualBins.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
/- Adapted from this LOT tree, obligation o200, session x0829,
   commit a965423f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ResidualBinCaps.lean.
   The final adapter below uses fixed-power-small sources uniformly. -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.FineNativeTransfer

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

def offsetAffine (L : Fin 4 → ℝ) (a : ℝ) : Fin 4 → ℝ :=
  ![L 0 + a, L 1, L 2, L 3]

theorem eval_offsetAffine (L : Fin 4 → ℝ) (a : ℝ) (x : Fin 4 → ℝ) :
    eval x (affineBase (offsetAffine L a)) = eval x (affineBase L) + a := by
  simp [affineBase, offsetAffine]
  ring

theorem offsetAffine_fit_of_floor {a : ℝ} (ha : 0 < a) (L : Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (j : ℤ)
    (hbin : ⌊(x 3 - eval x (affineBase L)) / a⌋ = j) :
    |eval x (affineBase (offsetAffine L (a * (j : ℝ)))) - x 3| ≤ a := by
  have hl := Int.floor_le ((x 3 - eval x (affineBase L)) / a)
  have hu := Int.lt_floor_add_one ((x 3 - eval x (affineBase L)) / a)
  rw [hbin] at hl hu
  have hlo := (le_div_iff₀ ha).mp hl
  have hup := (div_lt_iff₀ ha).mp hu
  rw [eval_offsetAffine]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Every residual bin is controlled by a uniform affine band cap. Large
bins are covered by the parent band. For a small occupied bin, an actual
good witness bounds its offset before the shifted predictor is used. -/
theorem affine_residual_bin_cap_of_band_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 4 → ℝ) (event : Set Ω) (L : Fin 4 → ℝ)
    {a : ℝ} (ha : 0 < a)
    (hparent : ∀ᵐ p ∂μ, |eval (x p) (affineBase L) - x p 3| ≤ 1 / 4)
    (C : ENNReal)
    (hband : ∀ L' : Fin 4 → ℝ,
      (∀ᵐ p ∂μ, |eval (x p) (affineBase L') - x p 3| ≤ 1) →
      μ {p | p ∈ event ∧ |eval (x p) (affineBase L') - x p 3| ≤ a} ≤ C)
    (j : ℤ) :
    μ {p | p ∈ event ∧ ⌊(x p 3 - eval (x p) (affineBase L)) / a⌋ = j} ≤ C := by
  by_cases hlarge : 1 / 2 ≤ a
  · apply (show μ _ ≤ μ {p | p ∈ event ∧ |eval (x p) (affineBase L) - x p 3| ≤ a} from ?_).trans
      (hband L (hparent.mono fun p hp => hp.trans (by norm_num)))
    apply measure_mono_ae
    filter_upwards [hparent] with p hp he
    exact ⟨he.1, hp.trans (by linarith)⟩
  let source : Set Ω := {p | p ∈ event ∧ ⌊(x p 3 - eval (x p) (affineBase L)) / a⌋ = j}
  by_cases hz : μ source = 0
  · change μ source ≤ C
    rw [hz]
    exact zero_le
  obtain ⟨p0, hp0, hp0parent⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hz
    (ae_restrict_of_ae hparent)
  have hp0fit := offsetAffine_fit_of_floor ha L (x p0) j hp0.2
  have hoffset : |a * (j : ℝ)| ≤ a + 1 / 4 := by
    have he : a * (j : ℝ) =
        (eval (x p0) (affineBase (offsetAffine L (a * (j : ℝ)))) - x p0 3) -
          (eval (x p0) (affineBase L) - x p0 3) := by rw [eval_offsetAffine]; ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hp0fit hp0parent)
  have hshifted : ∀ᵐ p ∂μ,
      |eval (x p) (affineBase (offsetAffine L (a * (j : ℝ)))) - x p 3| ≤ 1 := by
    filter_upwards [hparent] with p hp
    rw [eval_offsetAffine]
    calc
      _ = |(eval (x p) (affineBase L) - x p 3) + a * (j : ℝ)| := by congr 1; ring
      _ ≤ |eval (x p) (affineBase L) - x p 3| + |a * (j : ℝ)| := abs_add_le _ _
      _ ≤ 1 := by linarith [hp, hoffset]
  apply (show μ source ≤ μ {p | p ∈ event ∧
    |eval (x p) (affineBase (offsetAffine L (a * (j : ℝ)))) - x p 3| ≤ a} from ?_).trans
      (hband _ hshifted)
  apply measure_mono
  intro p hp
  exact ⟨hp.1, offsetAffine_fit_of_floor ha L (x p) j hp.2⟩


/-- The affine residual's floor bins inherit the ORIGINAL native-signal cap.
The original base state and every extra velocity condition stay in G. -/
theorem fine_original_residual_bin_transfer {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ k in atTop, ∀ (τ : Measure (α × ℝ)), τ ≤ D.μ k →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ τ univ → ∀ L : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ 1 / 4) →
      ∀ r s : ℝ, 0 ≤ s → s + (6 * B + 2) ≤ r →
      ∀ (G : Set (α × ℝ)) (q : Fin 3 → ℤ) (C : ENNReal),
      (∀ j : ℤ, D.μ k {x | x ∈ G ∧ D.z k (D.N k) r x = q ∧
        ⌊eval (D.x k x.1 x.2) (D.P k) / D.N k ^ (-s)⌋ = j} ≤ C) →
      ∀ j : ℤ, τ {x | x ∈ G ∧ D.z k (D.N k) r x = q ∧
        ⌊((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) / D.N k ^ (-s)⌋ = j} ≤
        ENNReal.ofReal (6 * D.K k + 5) * C := by
  filter_upwards [fine_original_native_transfer D p h1 h2 hB] with k hk
  intro τ hτ hmass L hparent r s hs hrs G q C hcap j
  have hN : 0 < D.N k := by linarith [p.scale k]
  have hh := affine_residual_bin_cap_of_band_caps τ (fun x => D.x k x.1 x.2)
    {x | x ∈ G ∧ D.z k (D.N k) r x = q} L (Real.rpow_pos_of_pos hN _) hparent
    (ENNReal.ofReal (6 * D.K k + 5) * C)
    (fun L' hfit => by
      have hm := hk τ hτ hmass L' hfit r s hs hrs G q C hcap
      simpa only [mem_setOf_eq, and_assoc] using hm) j
  simpa only [mem_setOf_eq, and_assoc] using hh

end
end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
