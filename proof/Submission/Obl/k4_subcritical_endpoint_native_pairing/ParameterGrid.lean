/- Adapted from this LOT tree, obligation o249, session x0876, commit 62801b543db15394ef6e0ef94c4a2e234b73e26a,
   Submission/Obl/k4_horizontal_endpoint_three_projections/ParameterGrid.lean.
   Original attributions are retained below. -/
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-! Count the original static parameter cells meeting one true horizontal label.
The tilted transverse side is kept; an axis-aligned bounding rectangle would
lose a power of the horizontal scale. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set
open Submission.Lib.K4MovingMeshBoxes
open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error)

noncomputable section

/-- Two-dimensional ordinary cells meeting a tilted rectangle have the expected
area count, with only a shear-dependent constant. -/
theorem tilted_parameter_mesh_cover {D B C : ℝ} (hD : 0 < D)
    (hDB : D ≤ B) (hDC : D ≤ C) (p₀ q₀ τ : ℝ) :
    ∃ F : Finset (Fin 2 → ℤ),
      (F.card : ℝ) * D ^ 2 ≤ 60 * (1 + |τ|) * B * C ∧
      ∀ p q : ℝ, |p - p₀| ≤ B → |q - q₀ - τ * (p - p₀)| ≤ C →
        ![⌊p / D⌋, ⌊q / D⌋] ∈ F := by
  classical
  have hB : 0 ≤ B := hD.le.trans hDB
  have hC : 0 ≤ C := hD.le.trans hDC
  obtain ⟨Fp, hFp, hpcover⟩ := interval_mesh_cover hD hB p₀
  choose Fq hFq hqcover using fun i : ℤ =>
    interval_mesh_cover hD (show 0 ≤ C + |τ| * D by positivity)
      (q₀ + τ * ((i : ℝ) * D - p₀))
  let F := Fp.biUnion (fun i => (Fq i).image (fun j => (![i, j] : Fin 2 → ℤ)))
  have hpcount : (Fp.card : ℝ) ≤ 6 * B / D := hFp.trans (by
    apply (le_div_iff₀ hD).mpr
    field_simp
    nlinarith)
  have hqcount (i : ℤ) : ((Fq i).card : ℝ) ≤ 10 * (1 + |τ|) * C / D := by
    apply (hFq i).trans
    apply (le_div_iff₀ hD).mpr
    field_simp
    have hcτ := mul_le_mul_of_nonneg_left hDC (abs_nonneg τ)
    nlinarith [abs_nonneg τ]
  have hc : (F.card : ℝ) ≤ (6 * B / D) * (10 * (1 + |τ|) * C / D) := by
    calc
      _ ≤ ∑ i ∈ Fp, (((Fq i).image (fun j => (![i, j] : Fin 2 → ℤ))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Fp, ((Fq i).card : ℝ) := by
        exact_mod_cast Finset.sum_le_sum (fun i _ => Finset.card_image_le)
      _ ≤ ∑ _i ∈ Fp, 10 * (1 + |τ|) * C / D :=
        Finset.sum_le_sum (fun i _ => hqcount i)
      _ = (Fp.card : ℝ) * (10 * (1 + |τ|) * C / D) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpcount (by positivity)
  refine ⟨F, ?_, ?_⟩
  · calc
      _ ≤ ((6 * B / D) * (10 * (1 + |τ|) * C / D)) * D ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = _ := by field_simp; ring
  · intro p q hp hq
    have hp' : |p - (⌊p / D⌋ : ℝ) * D| ≤ D := by
      simpa only [mul_comm] using floor_scaled_error hD p
    have hq' : |q - (q₀ + τ * (((⌊p / D⌋ : ℝ)) * D - p₀))| ≤ C + |τ| * D := by
      have hid : q - (q₀ + τ * (((⌊p / D⌋ : ℝ)) * D - p₀)) =
          (q - q₀ - τ * (p - p₀)) + τ * (p - (⌊p / D⌋ : ℝ) * D) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add hq (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hp' (abs_nonneg _)))
    exact Finset.mem_biUnion.mpr ⟨⌊p / D⌋, hpcover p hp,
      Finset.mem_image.mpr ⟨⌊q / D⌋, hqcover _ q hq', rfl⟩⟩

/-- True label geometry at its time midpoint gives a thin tilted range of static
parameters after fixing the ORIGINAL velocity bin. -/
theorem native_static_parameter_rectangle (b : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    {t v K q g χ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (hτ : |c 4| ≤ K) (hv : |b 3 - v| ≤ χ) (hd : |b 4 + b 0| ≤ χ)
    (hZ : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hY : |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g) :
    |b 0 - (c 0 + t * (c 1 - v))| ≤ K * q + χ ∧
    |b 1 - (c 2 + t * c 3 + c 4 * t * v) - (t + c 4) * b 0| ≤
      K * q * g + (K + 1) * χ := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hv
  constructor
  · have heq : b 0 - (c 0 + t * (c 1 - v)) =
        (b 0 + t * b 3 - c 0 - t * c 1) - t * (b 3 - v) := by ring
    rw [heq]
    refine (abs_sub _ _).trans (add_le_add hZ ?_)
    rw [abs_mul]
    exact (mul_le_mul ht1 hv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · have heq : b 1 - (c 2 + t * c 3 + c 4 * t * v) - (t + c 4) * b 0 =
        (b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)) -
          t * (b 4 + b 0) + c 4 * t * (b 3 - v) := by ring
    rw [heq]
    have htχ : |t * (b 4 + b 0)| ≤ χ := by
      rw [abs_mul]
      exact (mul_le_mul ht1 hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hvχ : |c 4 * t * (b 3 - v)| ≤ K * χ := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        ((mul_le_mul hτ ht1 (abs_nonneg _) hK).trans_eq (mul_one _)) hv (abs_nonneg _) hK
    exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      ((add_le_add (add_le_add hY htχ) hvχ).trans_eq (by ring))

/-- One true native label, at one fixed original velocity bin, meets only the
expected number of static parameter cells. The constant is uniform in the bin. -/
theorem native_parameter_mesh_cover (c : Fin 5 → ℝ) {D K q g χ t : ℝ}
    (hD : 0 < D) (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1)
    (hDK : D ≤ K * q * g) (hχ : χ ≤ q * g)
    (ht : t ∈ Icc (0 : ℝ) 1) (hc : |c 4| ≤ K) (v : ℝ) :
    ∃ F : Finset (Fin 2 → ℤ),
      (F.card : ℝ) * D ^ 2 ≤ 4096 * K ^ 5 * q ^ 2 * g ∧
      ∀ b : Fin 6 → ℝ, |b 3 - v| ≤ χ → |b 4 + b 0| ≤ χ →
        |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q →
        |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g →
        ![⌊b 0 / D⌋, ⌊b 1 / D⌋] ∈ F := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hqg : q * g ≤ q := by nlinarith
  let p₀ := c 0 + t * (c 1 - v)
  let q₀ := c 2 + t * c 3 + c 4 * t * v + (t + c 4) * p₀
  have hB : D ≤ 4 * K ^ 2 * q := hDK.trans (by nlinarith [mul_le_mul_of_nonneg_left hqg hK0])
  have hC : D ≤ 4 * K ^ 2 * q * g := hDK.trans (by
    nlinarith [mul_nonneg (show 0 ≤ 4 * K ^ 2 - K by nlinarith) (mul_nonneg hq.le hg.le)])
  obtain ⟨F, hF, hcover⟩ := tilted_parameter_mesh_cover hD hB hC p₀ q₀ (t + c 4)
  refine ⟨F, hF.trans ?_, ?_⟩
  · have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hτ : 1 + |t + c 4| ≤ 3 * K := by
      have hh := (abs_add_le t (c 4)).trans (add_le_add ht1 hc)
      linarith
    calc
      _ ≤ 60 * (3 * K) * (4 * K ^ 2 * q) * (4 * K ^ 2 * q * g) := by gcongr
      _ = 2880 * K ^ 5 * q ^ 2 * g := by ring
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hK0 5) (mul_nonneg (sq_nonneg q) hg.le)]
  · intro b hv hd hZ hY
    obtain ⟨hp, hr⟩ := native_static_parameter_rectangle b c ht hK0 hc hv hd hZ hY
    apply hcover
    · apply hp.trans
      have hχq : χ ≤ q := hχ.trans hqg
      have hh : (K + 1) * q ≤ 4 * K ^ 2 * q := by gcongr; nlinarith
      nlinarith
    · have heq : b 1 - q₀ - (t + c 4) * (b 0 - p₀) =
          b 1 - (c 2 + t * c 3 + c 4 * t * v) - (t + c 4) * b 0 := by
        dsimp [q₀]; ring
      rw [heq]
      apply hr.trans
      have hh : (2 * K + 1) * (q * g) ≤ (4 * K ^ 2) * (q * g) := by
        gcongr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hχ (show 0 ≤ K + 1 by linarith)]

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing
