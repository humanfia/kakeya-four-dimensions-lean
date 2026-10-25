-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/QuantitativeLocalization.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/QuantitativeLocalization.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/QuantitativeLocalization.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_lifted_plank_cap_saturation.Bins

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MeasureTheory Metric Set

/-- Three-dimensional Euclidean distance in one coefficient bin is at
most twice its width. The coordinate estimate is the accepted local-choice
cell lemma. -/
theorem coefficient_bin_dist_le {p : ℝ} (hp : 0 < p)
    {x y : EuclideanSpace ℝ (Fin 3)}
    (hbin : ∀ i, ⌊x i / p⌋ = ⌊y i / p⌋) : dist x y ≤ 2 * p := by
  have hcell : Submission.Lib.K4CommonLocalChoice.cell p (fun i => x i) =
      Submission.Lib.K4CommonLocalChoice.cell p (fun i => y i) := by
    funext i
    exact hbin i
  have hsup := Submission.Lib.K4CommonLocalChoice.norm_sub_lt_of_cell_eq hp hcell
  have hcoord (i : Fin 3) : |x i - y i| ≤ p := by
    have hh := (norm_le_pi_norm ((fun j => x j) - (fun j => y j)) i).trans hsup.le
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hh
  have hsq : ‖x - y‖ ^ 2 ≤ 3 * p ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, p ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := (sq_le_sq₀ (abs_nonneg (x i - y i)) hp.le).mpr (hcoord i)
        simpa only [sq_abs, PiLp.sub_apply] using hh
      _ = 3 * p ^ 2 := by simp
  rw [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * p)).mp
  nlinarith [sq_nonneg p]

/-- Localization at a small ball costs a fixed power of the inverse radius.
The center is the image of an original retained label, and the original
unnormalized measure supplies both sides of the inequality. -/
theorem bounded_image_mass_localization {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (G : Set α)
    (hGne : G.Nonempty) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hbound : ∀ l ∈ G, a l ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hfin : μ G ≠ ⊤) :
    ∃ l₀ ∈ G, μ G ≤ ENNReal.ofReal (2 * (4 * R / (r / 4) + 2) ^ 3) *
      μ {l | l ∈ G ∧ a l ∈ ball (a l₀) r} := by
  classical
  by_cases hzero : μ G = 0
  · obtain ⟨l₀, hl₀⟩ := hGne
    exact ⟨l₀, hl₀, by simp [hzero]⟩
  let p := r / 4
  let K := (4 * R / p + 2) ^ 3
  let T := (μ G).toReal / (2 * K)
  have hp : 0 < p := by dsimp [p]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hmassreal : 0 < (μ G).toReal := ENNReal.toReal_pos hzero hfin
  have hT : 0 < T := div_pos hmassreal (by positivity)
  have hKT : K * T = (μ G).toReal / 2 := by
    dsimp [T]
    field_simp [ne_of_gt hK]
  have hGeq : {l | a l ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R ∧ l ∈ G} = G := by
    ext l
    exact ⟨And.right, fun hl => ⟨hbound l hl, hl⟩⟩
  have hmass : ENNReal.ofReal (K * T) <
      μ {l | a l ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R ∧ l ∈ G} := by
    rw [hGeq, hKT]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin).mpr (half_lt_self hmassreal)
  obtain ⟨q, hqmass⟩ := k4_lifted_plank_cap_saturation.exists_heavy_coefficient_bin
    μ a G 0 hR hp hT.le hmass
  have hbinne : {l | (∀ i : Fin 3, ⌊a l i / p⌋ = q i) ∧ l ∈ G}.Nonempty := by
    by_contra hempty
    have he := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [he, measure_empty] at hqmass
    exact not_le_of_gt (ENNReal.ofReal_pos.mpr hT) hqmass
  obtain ⟨l₀, hl₀⟩ := hbinne
  have hsub : {l | (∀ i : Fin 3, ⌊a l i / p⌋ = q i) ∧ l ∈ G} ⊆
      {l | l ∈ G ∧ a l ∈ ball (a l₀) r} := by
    intro l hl
    refine ⟨hl.2, ?_⟩
    have hd := coefficient_bin_dist_le hp (fun i => (hl.1 i).trans (hl₀.1 i).symm)
    rw [mem_ball]
    exact hd.trans_lt (by dsimp [p]; linarith)
  have hnear := hqmass.trans (measure_mono hsub)
  have h2KT : (2 * K) * T = (μ G).toReal := by nlinarith [hKT]
  refine ⟨l₀, hl₀.2, ?_⟩
  calc
    μ G = ENNReal.ofReal ((2 * K) * T) := by rw [h2KT, ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (2 * K) * ENNReal.ofReal T := ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (2 * K) * μ {l | l ∈ G ∧ a l ∈ ball (a l₀) r} :=
      mul_le_mul_of_nonneg_left hnear (by positivity)

/-- For power-sized data and a power-small radius, the original-law mass
loss is a fixed power of the same parameter. -/
theorem power_bounded_image_mass_localization {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (G : Set α)
    (hGne : G.Nonempty) {A : ℝ} (hA : 2 ≤ A) (s m : ℕ)
    (hbound : ∀ l ∈ G, a l ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (A ^ s))
    (hfin : μ G ≠ ⊤) :
    ∃ l₀ ∈ G, μ G ≤ ENNReal.ofReal (A ^ (3 * (s + m) + 14)) *
      μ {l | l ∈ G ∧ a l ∈ ball (a l₀) (A ^ m)⁻¹} := by
  have hApos : 0 < A := by linarith
  obtain ⟨l₀, hl₀, hmass⟩ := bounded_image_mass_localization μ a G hGne
    (by positivity : 0 ≤ A ^ s) (by positivity : 0 < (A ^ m)⁻¹) hbound hfin
  have hratio : 4 * A ^ s / ((A ^ m)⁻¹ / 4) + 2 = 16 * A ^ (s + m) + 2 := by
    rw [pow_add]
    field_simp [ne_of_gt hApos]
    ring
  have hone : 1 ≤ A ^ (s + m) := one_le_pow₀ (by linarith : 1 ≤ A)
  have hinside : 16 * A ^ (s + m) + 2 ≤ 18 * A ^ (s + m) := by linarith
  have hconstant : (11664 : ℝ) ≤ A ^ 14 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA 14
    norm_num at hh
    linarith
  have hcost : 2 * (4 * A ^ s / ((A ^ m)⁻¹ / 4) + 2) ^ 3 ≤
      A ^ (3 * (s + m) + 14) := by
    rw [hratio]
    calc
      2 * (16 * A ^ (s + m) + 2) ^ 3 ≤ 2 * (18 * A ^ (s + m)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinside 3) (by norm_num)
      _ = 11664 * A ^ (3 * (s + m)) := by
        rw [Nat.mul_comm 3 (s + m), pow_mul]
        ring
      _ ≤ A ^ 14 * A ^ (3 * (s + m)) := mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = A ^ (3 * (s + m) + 14) := by rw [pow_add]; ring
  refine ⟨l₀, hl₀, hmass.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcost) (by positivity)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
