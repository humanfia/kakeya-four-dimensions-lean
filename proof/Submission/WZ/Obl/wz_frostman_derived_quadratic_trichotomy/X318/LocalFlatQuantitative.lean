-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatQuantitative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatAssembly
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.RefinementExits

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalFlatQuantitative.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

def localFlatLoss : ℝ := 2 * localContributorLoss +
  16 * localNeighborLoss * localContributorLoss + 32 * localContributorLoss ^ 2

lemma local_factor_error_bounds {δ ν ζ ζ₃ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hsmall : localFlatLoss * δ ^ (ζ₃ - ζ - 4 * ν) ≤ 1) :
    localContributorLoss * (2 * δ ^ (-ν)) ≤ δ ^ (-ζ₃) ∧
    localNeighborLoss * ((2 * δ ^ (-ν)) *
      (8 * (localContributorLoss * δ ^ (-ν)) * (δ ^ (-ν)) ^ 2)) ≤ δ ^ (-ζ₃) ∧
    (2 * δ ^ (-ζ)) * (localContributorLoss * (2 * δ ^ (-ν))) *
      (8 * (localContributorLoss * δ ^ (-ν)) * (δ ^ (-ν)) ^ 2) ≤ δ ^ (-ζ₃) := by
  let r := δ ^ (-ν)
  let k := δ ^ (-ζ)
  have hr : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hν)
  have hk : 1 ≤ k := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hζ)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have hC : 0 ≤ localFlatLoss := by
    norm_num [localFlatLoss, localContributorLoss, localNeighborLoss]
  have hC₁ : 2 * localContributorLoss ≤ localFlatLoss := by
    norm_num [localFlatLoss, localContributorLoss, localNeighborLoss]
  have hC₂ : 16 * localNeighborLoss * localContributorLoss ≤ localFlatLoss := by
    norm_num [localFlatLoss, localContributorLoss, localNeighborLoss]
  have hC₃ : 32 * localContributorLoss ^ 2 ≤ localFlatLoss := by
    norm_num [localFlatLoss, localContributorLoss, localNeighborLoss]
  have hpow : k * r ^ 4 = δ ^ (-ζ - 4 * ν) := by
    dsimp [k, r]
    rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
    congr 1
    ring
  have hbound : localFlatLoss * (k * r ^ 4) ≤ δ ^ (-ζ₃) := by
    rw [hpow]
    apply mul_rpow_le_of_absorbed hδ
    convert hsmall using 1 <;> congr 2 <;> ring
  have hkr : r ^ 4 ≤ k * r ^ 4 := le_mul_of_one_le_left (by positivity) hk
  have hrk : r ≤ k * r ^ 4 := (le_self_pow₀ hr (by norm_num : (4 : ℕ) ≠ 0)).trans hkr
  refine ⟨?_, ?_, ?_⟩
  · change localContributorLoss * (2 * r) ≤ _
    calc
      _ = (2 * localContributorLoss) * r := by ring
      _ ≤ localFlatLoss * r := mul_le_mul_of_nonneg_right hC₁ hr0
      _ ≤ localFlatLoss * (k * r ^ 4) := mul_le_mul_of_nonneg_left hrk hC
      _ ≤ _ := hbound
  · change localNeighborLoss * ((2 * r) * (8 * (localContributorLoss * r) * r ^ 2)) ≤ _
    calc
      _ = (16 * localNeighborLoss * localContributorLoss) * r ^ 4 := by ring
      _ ≤ localFlatLoss * r ^ 4 := mul_le_mul_of_nonneg_right hC₂ (by positivity)
      _ ≤ localFlatLoss * (k * r ^ 4) := mul_le_mul_of_nonneg_left hkr hC
      _ ≤ _ := hbound
  · change (2 * k) * (localContributorLoss * (2 * r)) *
      (8 * (localContributorLoss * r) * r ^ 2) ≤ _
    calc
      _ = (32 * localContributorLoss ^ 2) * (k * r ^ 4) := by ring
      _ ≤ localFlatLoss * (k * r ^ 4) := mul_le_mul_of_nonneg_right hC₃ (by positivity)
      _ ≤ _ := hbound

/-- A local factor certificate before exact prism normalization. -/
def LocalFactor (ν δ τ a b : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ δ ^ ν * n ≤ k ∧
    ∃ (q : ℕ) (z w : Fin q → Space), (∀ l, ‖w l‖ = 1) ∧
      Distinct (fun l => Tube τ (z l) (w l)) ∧
      ∃ κ : ℝ, 0 < κ ∧
        (∀ l U, Convex ℝ U →
          ENNReal.ofReal ((ncard {i | A (g i) ⊆ Tube τ (z l) (w l) ∧ A (g i) ⊆ U} : ℝ) * δ ^ 2) ≤
            ENNReal.ofReal κ * volume U) ∧
        ∃ (p : ℕ) (W : Fin p → Set Space) (label : Fin p → Fin q)
          (c e₁ e₂ e₃ : Fin p → Space),
          (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
          (∀ j, W j ⊆ Tube τ (z (label j)) (w (label j)) ∩
            {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b}) ∧
          (∀ i, ∃ j, A (g i) ⊆ W j) ∧
          (∀ i, (ncard {j | A (g i) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
          (∀ j, δ ^ ν * κ * (8 * a * b) ≤
            (contained (fun i => A (g i)) (W j) : ℝ) * δ ^ 2)

theorem flat_refinement_of_local_factor {n : ℕ} (x v : Fin n → Space)
    {ν δ τ ζ ζ₂ ζ₃ θ a b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hδa : δ ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b)
    (herror : localFlatLoss * δ ^ (ζ₃ - ζ - 5 * ν) ≤ 1)
    (hretain : 2 * δ ^ (θ - ν) ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1)
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)))
    (hfactor : LocalFactor ν δ τ a b (fun i => Tube δ (x i) (v i))) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
      FlatPrisms ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
  obtain ⟨k, g, hg, hk, hsize, q, z, w, hw, hsep, κ, hκ, hparent,
    p, W, label, c, e₁, e₂, e₃, he, hshape, hcover, hdegree, hsat⟩ := hfactor
  have hFg := hF.restrict_power hδ g hg hsize
  have hprod : δ ^ (-ν) * δ ^ ν = 1 := by rw [← Real.rpow_add hδ]; simp
  have hsat' (j) : κ * (8 * a * b) ≤ δ ^ (-ν) *
      (contained (fun i => Tube δ (x (g i)) (v (g i))) (W j) : ℝ) * δ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hsat j) (Real.rpow_nonneg hδ.le (-ν))
    simpa only [← mul_assoc, hprod, one_mul] using hh
  have herr : localFlatLoss * δ ^ (ζ₃ - (ζ + ν) - 4 * ν) ≤ 1 := by
    convert herror using 1 <;> congr 2 <;> ring
  obtain ⟨hE₁, hE₂, hE₃⟩ := local_factor_error_bounds hδ hδ1 hν (add_nonneg hζ hν) herr
  obtain ⟨m, f, hf, hmass, hC⟩ := flat_refinement_of_local_saturated_cover
    hδ hτ hτhalf hδa hab hbτ hflat hκ (Real.rpow_pos_of_pos hδ _)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hν))
    (Real.rpow_nonneg hδ.le _) hk (x ∘ g) (v ∘ g) (fun i => hv (g i)) hFg
    z w hw hsep W label c e₁ e₂ e₃ he hshape hcover hdegree hparent hsat' hE₁ hE₂ hE₃
  refine ⟨m, g ∘ f, hg.comp hf, ?_, hC⟩
  have hp : 2 * δ ^ θ ≤ δ ^ ν := mul_rpow_le_of_absorbed hδ hretain
  have hh := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n)
  nlinarith only [hh, hsize, hmass]

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
