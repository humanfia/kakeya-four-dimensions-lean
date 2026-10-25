-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/Numerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from LOT tree g-oai-074, obligation o194, session x0672,
-- commit c10e54a1, Submission/Obl/k4_greedy_cover_graph_atlas/Numerics.lean.
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Interface
import Submission.Obl.k4_profile_density_bounds.Common

/-!
# Numerics of the per-sample construction

Generic exponent bookkeeping used to choose the per-sample scales: the dyadic thickness ratio
`δ(N, r) / δ(N, r + u) ≍ N^u`, a dyadic subdivision count between `X` and `2X`, absorption of a
fixed constant by a positive power gap, and the choice of `θ` and of the slack ratio `ϖ`.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Submission.Lib.K4XInterface

theorem gδ_two_sided {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  Submission.Obl.k4_profile_density_bounds.width_bounds hN r

/-- The dyadic thickness ratio over a depth increment `u` is `N^u` up to a factor two. -/
theorem gδ_ratio_bounds {N : ℝ} (hN : 0 < N) (r u : ℝ) :
    N ^ u / 2 ≤ δ N r / δ N (r + u) ∧ δ N r / δ N (r + u) ≤ 2 * N ^ u := by
  obtain ⟨h1, h2⟩ := gδ_two_sided hN r
  obtain ⟨h3, h4⟩ := gδ_two_sided hN (r + u)
  have hpos : 0 < δ N (r + u) := gδ_pos N (r + u)
  have hNr : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  have hsplit : N ^ (-r) = N ^ u * N ^ (-(r + u)) := by
    rw [← Real.rpow_add hN]; ring_nf
  have hNru : 0 < N ^ (-(r + u)) := Real.rpow_pos_of_pos hN _
  constructor
  · rw [le_div_iff₀ hpos]
    calc N ^ u / 2 * δ N (r + u) ≤ N ^ u / 2 * (2 * N ^ (-(r + u))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = N ^ (-r) := by rw [hsplit]; ring
      _ ≤ δ N r := h1
  · rw [div_le_iff₀ hpos]
    calc δ N r ≤ 2 * N ^ (-r) := h2
      _ = 2 * N ^ u * N ^ (-(r + u)) := by rw [hsplit]; ring
      _ ≤ 2 * N ^ u * δ N (r + u) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)

/-- A dyadic count between `X` and `2 X`. -/
theorem exists_two_pow_between {X : ℝ} (hX : 1 ≤ X) :
    ∃ s₀ : ℕ, X ≤ (2 : ℝ) ^ s₀ ∧ (2 : ℝ) ^ s₀ ≤ 2 * X := by
  classical
  have hex : ∃ s : ℕ, X ≤ (2 : ℝ) ^ s :=
    (pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; linarith
  · have hlt := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    have hlt' : (2 : ℝ) ^ (Nat.find hex - 1) < X := lt_of_not_ge hlt
    have he : (2 : ℝ) ^ Nat.find hex = 2 * (2 : ℝ) ^ (Nat.find hex - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [he]
    linarith

/-- A fixed constant is absorbed by a power gap once `N ≥ K₀^(1/ξ)`. -/
theorem rpow_absorb {N K₀ ξ a b : ℝ} (hN : 1 ≤ N) (hK₀ : 1 ≤ K₀) (hξ : 0 < ξ)
    (hNK : K₀ ^ (1 / ξ) ≤ N) (hab : a + ξ ≤ b) : K₀ * N ^ a ≤ N ^ b := by
  have hN0 : 0 < N := by linarith
  have hK : K₀ ≤ N ^ ξ := by
    calc K₀ = (K₀ ^ (1 / ξ)) ^ ξ := by
          rw [← Real.rpow_mul (by linarith)]; field_simp; simp
      _ ≤ N ^ ξ := Real.rpow_le_rpow (by positivity) hNK hξ.le
  calc K₀ * N ^ a ≤ N ^ ξ * N ^ a := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = N ^ (a + ξ) := by rw [← Real.rpow_add hN0]; ring_nf
    _ ≤ N ^ b := Real.rpow_le_rpow_of_exponent_le hN hab

/-- The output precision exponent: a fixed fraction of the matching exponent, at most `1/4`. -/
noncomputable def thetaOf (εm : ℝ) : ℝ := min (1 / 4) (εm / 4)

theorem thetaOf_pos {εm : ℝ} (hεm : 0 < εm) : 0 < thetaOf εm :=
  lt_min (by norm_num) (by positivity)

theorem thetaOf_le_quarter (εm : ℝ) : thetaOf εm ≤ 1 / 4 := min_le_left _ _

theorem thetaOf_le (εm : ℝ) : thetaOf εm ≤ εm / 4 := min_le_right _ _

/-- The slack ratio: all slack exponents, multiplied by a fixed construction constant `Λ`, stay
below a fixed fraction of both the matching exponent and the short-time budget `κ₁ θ`. -/
noncomputable def varpiOf (εm κ₁ θ Λ : ℝ) : ℝ := min εm (κ₁ * θ) / (16 * Λ)

theorem varpiOf_pos {εm κ₁ θ Λ : ℝ} (hεm : 0 < εm) (hκ₁ : 0 < κ₁) (hθ : 0 < θ) (hΛ : 0 < Λ) :
    0 < varpiOf εm κ₁ θ Λ := by
  unfold varpiOf
  exact div_pos (lt_min hεm (mul_pos hκ₁ hθ)) (by positivity)

theorem varpiOf_mul_le_eps {εm κ₁ θ Λ : ℝ} (hΛ : 0 < Λ) :
    16 * Λ * varpiOf εm κ₁ θ Λ ≤ εm := by
  unfold varpiOf
  rw [mul_div_cancel₀ _ (by positivity : (16 * Λ) ≠ 0)]
  exact min_le_left _ _

theorem varpiOf_mul_le_time {εm κ₁ θ Λ : ℝ} (hΛ : 0 < Λ) :
    16 * Λ * varpiOf εm κ₁ θ Λ ≤ κ₁ * θ := by
  unfold varpiOf
  rw [mul_div_cancel₀ _ (by positivity : (16 * Λ) ≠ 0)]
  exact min_le_right _ _

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
