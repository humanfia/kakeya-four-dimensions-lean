-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SpatialPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GridPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

local instance spatialPacketsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Spatial grid packets in each angular frame. At a point their number is
bounded by the number of active angular classes and a universal constant. -/
theorem spatial_grid_partition {n N M K : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c)
    (g : Fin n → Fin N) (long : Fin n → Fin M)
    (u : Fin N → OrthonormalBasis (Fin 3) ℝ V) (ν z : Fin n → V)
    (Y : Fin n → Set V) (F : V → V)
    (hframe : ∀ i, ‖u (g i) 0 - ν i‖ ≤ s / 100)
    (hsource : ∀ i p, p ∈ Y i →
      ‖F p - z i‖ ≤ 25 * c ∧ |inner ℝ (ν i) (F p - z i)| ≤ s * c)
    (hactive : ∀ p, ((Finset.univ.filter fun i => p ∈ Y i).image g).card ≤ K) :
    ∃ L : ℕ, ∃ f : Fin n → Fin L, ∃ ref : Fin L → Fin n,
      (∀ k, f (ref k) = k) ∧
      (∀ i j, f i = f j → g i = g j ∧ long i = long j ∧
        ‖z i - z j‖ ≤ c / 100 ∧ |inner ℝ (ν j) (z i - z j)| ≤ s * c / 100) ∧
      (∀ p, ((Finset.univ.filter fun i => p ∈ Y i).image f).card ≤ K * 50003 ^ 3 * M) := by
  classical
  let w : Fin 3 → ℝ := ![s * c / 1000, c / 1000, c / 1000]
  have hw (j : Fin 3) : 0 < w j := by fin_cases j <;> dsimp [w] <;> positivity
  let x : Fin n → Fin 3 → ℝ := fun i j => inner ℝ (u (g i) j) (z i)
  let spatial : Fin n → Fin 3 → ℤ := fun i j => ⌊x i j / w j⌋
  let code := fun i => (g i, (spatial i, long i))
  obtain ⟨L, f, ref, href, heq⟩ := finite_code_partition code
  refine ⟨L, f, ref, href, ?_, ?_⟩
  · intro i j hij
    have he := (heq i j).mp hij
    have hg : g i = g j := congrArg Prod.fst he
    have hsp : spatial i = spatial j := congrArg (fun q => q.2.1) he
    have hlong : long i = long j := congrArg (fun q => q.2.2) he
    have hcoord (k : Fin 3) : |inner ℝ (u (g i) k) (z i - z j)| ≤ w k := by
      have hh := (abs_sub_lt_of_floor_eq (hw k) (congrFun hsp k)).le
      dsimp only [x] at hh
      rw [← hg, ← inner_sub_right] at hh
      exact hh
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    change |inner ℝ (u (g i) 0) (z i - z j)| ≤ s * c / 1000 at h0
    change |inner ℝ (u (g i) 1) (z i - z j)| ≤ c / 1000 at h1
    change |inner ℝ (u (g i) 2) (z i - z j)| ≤ c / 1000 at h2
    have hsc : s * c ≤ c := by nlinarith
    have hnorm : ‖z i - z j‖ ≤ c / 100 := by
      have hh := norm_le_coord_sum ((u (g i)).repr (z i - z j))
      simp only [LinearIsometryEquiv.norm_map, OrthonormalBasis.repr_apply_apply] at hh
      linarith
    refine ⟨hg, hlong, hnorm, ?_⟩
    have hh := abs_inner_le_projective (ν j) (u (g i) 0) (z i - z j)
    have hang : min ‖ν j - u (g i) 0‖ ‖ν j + u (g i) 0‖ ≤ s / 100 := by
      apply (min_le_left _ _).trans
      rw [hg, norm_sub_rev]
      exact hframe j
    have hm := mul_le_mul hang hnorm (norm_nonneg _) (by positivity : 0 ≤ s / 100)
    nlinarith [mul_pos hs hc]
  · intro p
    let S := Finset.univ.filter fun i => p ∈ Y i
    rw [partition_image_card code f ref href heq]
    have hspatial (k : Fin N) : ((S.filter fun i => g i = k).image spatial).card ≤ 50003 ^ 3 := by
      have hb : ∀ i ∈ S.filter (fun i => g i = k), ∀ j,
          |x i j - inner ℝ (u k j) (F p)| ≤ (25000 : ℕ) * w j := by
        intro i hi j
        obtain ⟨hiS, hg⟩ := Finset.mem_filter.mp hi
        have hip : p ∈ Y i := (Finset.mem_filter.mp hiS).2
        obtain ⟨hn, ht⟩ := hsource i p hip
        have hx : x i j - inner ℝ (u k j) (F p) = -inner ℝ (u k j) (F p - z i) := by
          dsimp [x]
          rw [hg, inner_sub_right]
          ring
        rw [hx, abs_neg]
        have hbroad : |inner ℝ (u k j) (F p - z i)| ≤ 25 * c := by
          have hh := abs_real_inner_le_norm (u k j) (F p - z i)
          rw [(u k).norm_eq_one, one_mul] at hh
          exact hh.trans hn
        fin_cases j
        · have hh := abs_inner_le_projective (u k 0) (ν i) (F p - z i)
          have hang : min ‖u k 0 - ν i‖ ‖u k 0 + ν i‖ ≤ s / 100 := by
            apply (min_le_left _ _).trans
            simpa only [hg] using hframe i
          have hm := mul_le_mul hang hn (norm_nonneg _) (by positivity : 0 ≤ s / 100)
          change |inner ℝ (u k 0) (F p - z i)| ≤ (25000 : ℝ) * (s * c / 1000)
          nlinarith [mul_pos hs hc]
        · change |inner ℝ (u k 1) (F p - z i)| ≤ (25000 : ℝ) * (c / 1000)
          change |inner ℝ (u k 1) (F p - z i)| ≤ 25 * c at hbroad
          linarith
        · change |inner ℝ (u k 2) (F p - z i)| ≤ (25000 : ℝ) * (c / 1000)
          change |inner ℝ (u k 2) (F p - z i)| ≤ 25 * c at hbroad
          linarith
      simpa only [spatial, show 2 * (25000 + 1) + 1 = 50003 by norm_num] using
        grid_image_card_le (S.filter fun i => g i = k) x
          (fun j => inner ℝ (u k j) (F p)) w hw hb
    have hpairs (k : Fin N) :
        ((S.filter fun i => g i = k).image fun i => (spatial i, long i)).card ≤ 50003 ^ 3 * M := by
      have hlcard : ∀ q ∈ (S.filter fun i => g i = k).image spatial,
          (((S.filter fun i => g i = k).filter fun i => spatial i = q).image long).card ≤ M := by
        intro q _
        simpa only [Fintype.card_fin] using Finset.card_le_univ
          (((S.filter fun i => g i = k).filter fun i => spatial i = q).image long)
      exact (pair_image_card_le _ spatial long hlcard).trans (Nat.mul_le_mul_right M (hspatial k))
    have hall := pair_image_card_le S g (fun i => (spatial i, long i)) (fun k _ => hpairs k)
    have hk : (S.image g).card ≤ K := hactive p
    exact hall.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (50003 ^ 3 * M) hk)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
