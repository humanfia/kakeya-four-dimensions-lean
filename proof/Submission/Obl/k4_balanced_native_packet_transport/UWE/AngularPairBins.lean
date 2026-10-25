/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/AngularPairBins.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_balanced_native_packet_transport.UWE).
-/
import Submission.Lib.K4VelocityStrips.StripIntersections
import Submission.Lib.K4QuadraticSublevel
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_balanced_native_packet_transport.UWE.Interface

noncomputable section

namespace Submission.Obl.k4_balanced_native_packet_transport.UWE

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips

/-- A bounded-diameter planar set meets a uniformly bounded collection of
angular bins. The set may be arbitrary, and its law is not conditioned. -/
theorem planar_diameter_bins (S : Set (EuclideanSpace ℝ (Fin 2)))
    {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ L) :
    ∃ V : Finset (Fin 2 → ℤ),
      (V.card : ℝ) ≤ (2 * L / δ + 2) ^ 2 ∧
      ∀ x ∈ S, (fun i => ⌊x i / δ⌋) ∈ V := by
  classical
  have hcoord (i : Fin 2) : ∀ x ∈ ((fun z : EuclideanSpace ℝ (Fin 2) => z i) '' S),
      ∀ y ∈ ((fun z : EuclideanSpace ℝ (Fin 2) => z i) '' S), dist x y ≤ L := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc
      dist (x i) (y i) ≤ dist x y := by
        simpa only [dist_eq_norm, PiLp.sub_apply] using PiLp.norm_apply_le (x - y) i
      _ ≤ L := hdiam x hx y hy
  have hbin (i : Fin 2) := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    ((fun z : EuclideanSpace ℝ (Fin 2) => z i) '' S) hL hδ 0 (hcoord i)
  let V : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun i => (hbin i).1.toFinset)
  refine ⟨V, ?_, ?_⟩
  · have hcard : ∀ i : Fin 2, (((hbin i).1.toFinset).card : ℝ) ≤ 2 * L / δ + 2 := by
      intro i
      rw [← Set.ncard_eq_toFinset_card _ (hbin i).1]
      exact (hbin i).2
    have heq : (V.card : ℝ) = ∏ i : Fin 2, (((hbin i).1.toFinset).card : ℝ) := by
      simp only [V, Fintype.card_piFinset, Nat.cast_prod]
    rw [heq, Fin.prod_univ_two, pow_two]
    exact mul_le_mul (hcard 0) (hcard 1) (by positivity) (by positivity)
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    apply (hbin i).1.mem_toFinset.mpr
    exact ⟨x i, ⟨x, hx, rfl⟩, by simp⟩

theorem unit_normals_min_distance_le {n m : StripSpace} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) :
    min ‖n - m‖ ‖n + m‖ ≤ 2 * |stripWedge n m| := by
  by_cases hinner : 0 ≤ inner ℝ n m
  · exact (min_le_left _ _).trans (unit_normals_dist_le_wedge hn hm hinner)
  · have hinner' : 0 ≤ inner ℝ n (-m) := by rw [inner_neg_right]; linarith only [hinner]
    have h := unit_normals_dist_le_wedge hn (by simpa only [norm_neg] using hm) hinner'
    have hw : stripWedge n (-m) = -stripWedge n m := by
      simp only [stripWedge, PiLp.neg_apply]
      ring
    rw [sub_neg_eq_add, hw, abs_neg] at h
    exact (min_le_right _ _).trans h

/-- Nonparallel occurrences on one trajectory permit at most sixteen
coarser angular bins for each pair of chart labels. This is the finite
geometric input to the original-law angular pairing estimate. -/
theorem nonparallel_velocity_bins {n m : StripSpace} {b c K g H δ : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hK : 0 ≤ K)
    (hg : 0 < g) (hH : 0 < H) (hδ : 0 < δ)
    (hangle : g * H < min ‖n - m‖ ‖n + m‖) (hscale : 16 * K ≤ H * δ) :
    ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ 16 ∧
      ∀ v : StripSpace, |inner ℝ n v - b| ≤ K * g → |inner ℝ m v - c| ≤ K * g →
        (fun i => ⌊v i / δ⌋) ∈ V := by
  have hd : 0 < g * H / 2 := by positivity
  have hdet : g * H / 2 ≤ |stripWedge n m| := by
    have h := unit_normals_min_distance_le hn hm
    linarith only [hangle, h]
  let S := affineStrip n b (K * g) ∩ affineStrip m c (K * g)
  let L : ℝ := 8 * (K * g) / (g * H / 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLδ : L ≤ δ := by
    have heq : L = 16 * K / H := by dsimp [L]; field_simp; ring
    rw [heq]
    exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hscale)
  obtain ⟨V, hV, hmem⟩ := planar_diameter_bins S hL hδ (by
    intro x hx y hy
    exact strip_intersection_diameter hn hm hd hdet hx.1 hx.2 hy.1 hy.2)
  refine ⟨V, hV.trans ?_, ?_⟩
  · have hratio : 0 ≤ 2 * L / δ + 2 := by positivity
    have hratio4 : 2 * L / δ + 2 ≤ 4 := by
      have h := (div_le_one hδ).mpr hLδ
      rw [show 2 * L / δ + 2 = 2 * (L / δ) + 2 by ring]
      linarith only [h]
    nlinarith only [hratio, hratio4]
  · intro v hvn hvm
    apply hmem v
    constructor <;> change |inner ℝ v _ - _| ≤ _
    · simpa only [real_inner_comm] using hvn
    · simpa only [real_inner_comm] using hvm

/-- In each fixed exact problem the sixteen-bin scale condition holds
eventually at the original dyadic angular depth `u / 2`, uniformly in the
chart widths and labels. -/
theorem eventually_angular_pair_scale {N K : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)
    {u : ℝ} (hu : 0 < u) :
    ∀ᶠ k in Filter.atTop, 16 * K k ≤ N k ^ u * δ (N k) (u / 2) := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => show 1 ≤ N k by linarith only [hN k]) hNt hK hsub 1
    (show (0 : ℝ) < u / 2 by linarith only [hu]) (show (0 : ℝ) ≤ 16 by norm_num)
  filter_upwards [hsmall] with k hk
  simp only [pow_one, Real.rpow_zero, mul_one] at hk
  have hNpos : 0 < N k := by linarith only [hN k]
  have hw := (Submission.Obl.k4_profile_density_bounds.width_bounds hNpos (u / 2)).1
  change N k ^ (-(u / 2)) ≤ δ (N k) (u / 2) at hw
  apply hk.le.trans
  calc
    N k ^ (u / 2) = N k ^ u * N k ^ (-(u / 2)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

end Submission.Obl.k4_balanced_native_packet_transport.UWE
