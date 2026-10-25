-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.PlaneCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CoarseCover
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RadiusTransfer
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Zoom

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

/-- A plane ball admits a finer cover with the expected quadratic cost. -/
theorem plane_closedBall_radius_cover {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ n : ℕ, (n : ℝ) ≤ 9 * (R / r) ^ 2 ∧
      ∀ c : Plane, ∃ d : Fin n → Plane, Covers r (Metric.closedBall c R) d := by
  classical
  let B : ℝ := 9 * (R / r) ^ 2
  refine ⟨Nat.floor B, Nat.floor_le (by dsimp [B]; positivity), ?_⟩
  intro c
  obtain ⟨m, f, hball, hsep, hcov⟩ :=
    exists_separated_cover (isCompact_closedBall c R).totallyBounded hr
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, dist_self] at h
    exact (not_lt_of_ge hr.le) h
  let S := Finset.univ.image f
  have hScard : S.card = m := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hSball : ∀ x ∈ S, dist x c ≤ R := by
    rintro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hball i
  have hSsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y := by
    rintro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact (hsep i j (fun hij => hxy (congrArg f hij))).le
  have hpack := separated_card_mul_radius_sq_le hr (hr.le.trans hrR) S c hSball hSsep
  rw [hScard] at hpack
  have hm : (m : ℝ) ≤ B := by
    dsimp [B]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  have hmn : m ≤ Nat.floor B := Nat.le_floor hm
  exact hcov.extend hmn

theorem Covers.refine_plane_radius {r R : ℝ} {S : Set Plane} (hr : 0 < r) (hrR : r ≤ R)
    {m : ℕ} {c : Fin m → Plane} (h : Covers R S c) :
    ∃ (n : ℕ) (d : Fin n → Plane), Covers r S d ∧
      (n : ℝ) ≤ (m : ℝ) * (9 * (R / r) ^ 2) := by
  obtain ⟨k, hk, hcover⟩ := plane_closedBall_radius_cover hr hrR
  choose d hd using fun i : Fin m => hcover (c i)
  refine ⟨m * k, _, h.refine d hd, ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg m)

theorem CoverLower.coarsen_plane {r R N : ℝ} {S : Set Plane}
    (h : CoverLower r S N) (hr : 0 < r) (hrR : r ≤ R) :
    CoverLower R S (N / (9 * (R / r) ^ 2)) := by
  intro m c hc
  obtain ⟨n, d, hd, hn⟩ := hc.refine_plane_radius hr hrR
  have hR : 0 < R := hr.trans_le hrR
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * (R / r) ^ 2)).mpr
    ((h n d hd).trans hn)

theorem CoverLower.of_zoom_image {r N k : ℝ} {S : Set Plane} (b : Plane)
    (h : CoverLower r (zoom b k '' S) N) (hk : 0 < k) :
    CoverLower (r / k) S N := by
  intro m c hc
  apply h m (fun i => zoom b k (c i))
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change dist (zoom b k x) (zoom b k (c i)) ≤ r
  rw [zoom_dist b hk.le]
  have hdist : dist x (c i) ≤ r / k := hi
  nlinarith [(le_div_iff₀ hk).mp hdist]

/-- Pull a cover lower bound back through an expanding zoom, restoring the
original radius at the quadratic packing cost. -/
theorem CoverLower.pullback_expanding_zoom {r N k : ℝ} {S T : Set Plane} (b : Plane)
    (h : CoverLower r T N) (hr : 0 < r) (hk : 1 ≤ k) (hTS : T ⊆ zoom b k '' S) :
    CoverLower r S (N / (9 * k ^ 2)) := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hs := (h.mono_set hTS).of_zoom_image b hkpos
  have hrk : r / k ≤ r := (div_le_iff₀ hkpos).mpr (by nlinarith)
  have hcoarse := hs.coarsen_plane (div_pos hr hkpos) hrk
  have hratio : r / (r / k) = k := by field_simp
  simpa only [hratio] using hcoarse

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
