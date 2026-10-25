/-
Adapted from: here:o222 (x0774), MeshProjection.lean, commit 4d22216c.
-/
import Submission.Lib.K4QuadraticSublevel

/-! Integrating a fine three-dimensional cell cap over a moving box. -/

namespace Submission.Lib.K4MovingMeshBoxes

open MeasureTheory Set

noncomputable section

theorem interval_mesh_cover {delta radius : ℝ} (hd : 0 < delta) (hr : 0 ≤ radius)
    (center : ℝ) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 4 * radius / delta + 2 ∧
      ∀ x : ℝ, |x - center| ≤ radius → ⌊x / delta⌋ ∈ F := by
  classical
  let S := {x : ℝ | |x - center| ≤ radius}
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * radius := by
    intro x hx y hy
    rw [Real.dist_eq]
    calc
      |x - y| = |(x - center) - (y - center)| := by ring_nf
      _ ≤ |x - center| + |y - center| := abs_sub _ _
      _ ≤ 2 * radius := by dsimp [S] at hx hy; linarith
  obtain ⟨hfinite, hcard⟩ :=
    Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      S (by positivity : 0 ≤ 2 * radius) hd 0 hdiam
  let F := hfinite.toFinset
  refine ⟨F, ?_, ?_⟩
  · have heq : (2 : ℝ) * (2 * radius) / delta + 2 = 4 * radius / delta + 2 := by ring
    simpa only [F, Set.ncard_eq_toFinset_card _ hfinite, heq] using hcard
  · intro x hx
    apply hfinite.mem_toFinset.mpr
    exact ⟨x, hx, by simp⟩

def baseMesh (delta : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊z i / delta⌋

def movingBox (time radius : ℝ) (center velocity width : Fin 2 → ℝ) : Set (Fin 3 → ℝ) :=
  {z | |z 0 - time| ≤ radius ∧
    ∀ i : Fin 2, |z i.succ - (center i + z 0 * velocity i)| ≤ width i}

theorem movingBox_mesh_cover {delta radius L : ℝ} (hd : 0 < delta)
    (hr : 0 ≤ radius) (hL : 0 ≤ L) (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hw : ∀ i, 0 ≤ width i) :
    ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) ≤ (4 * radius / delta + 2) *
        ∏ i : Fin 2, (4 * (width i + L * delta) / delta + 2) ∧
      ∀ z ∈ movingBox time radius center velocity width, baseMesh delta z ∈ F := by
  classical
  obtain ⟨Ft, hFt, htime⟩ := interval_mesh_cover hd hr time
  have hwidth (i : Fin 2) : 0 ≤ width i + L * delta :=
    add_nonneg (hw i) (mul_nonneg hL hd.le)
  choose Fs hFs hspace using fun (q : ℤ) (i : Fin 2) =>
    interval_mesh_cover hd (hwidth i) (center i + ((q : ℝ) * delta) * velocity i)
  let Q (q : ℤ) : Finset (Fin 2 → ℤ) := Fintype.piFinset (Fs q)
  let insertTime (q : ℤ) (z : Fin 2 → ℤ) : Fin 3 → ℤ := Fin.cons q z
  let F := Ft.biUnion (fun q => (Q q).image (insertTime q))
  refine ⟨F, ?_, ?_⟩
  · calc
      (F.card : ℝ) ≤ ∑ q ∈ Ft, (((Q q).image (insertTime q)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Ft, ((Q q).card : ℝ) := by
        exact_mod_cast Finset.sum_le_sum (fun q hq => Finset.card_image_le)
      _ ≤ ∑ _q ∈ Ft, ∏ i : Fin 2, (4 * (width i + L * delta) / delta + 2) := by
        apply Finset.sum_le_sum
        intro q hq
        simp only [Q, Fintype.card_piFinset, Nat.cast_prod]
        exact Finset.prod_le_prod₀ (fun i hi => Nat.cast_nonneg _)
          (fun i hi => hFs q i)
      _ = (Ft.card : ℝ) * ∏ i : Fin 2, (4 * (width i + L * delta) / delta + 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hFt (Finset.prod_nonneg (by
        intro i hi
        have := hwidth i
        positivity))
  · intro z hz
    let q : ℤ := ⌊z 0 / delta⌋
    have hqt : q ∈ Ft := htime (z 0) hz.1
    have htd : |z 0 - (q : ℝ) * delta| ≤ delta := by
      have hfloor := Int.floor_le (z 0 / delta)
      have hlt := Int.lt_floor_add_one (z 0 / delta)
      have hlo : (q : ℝ) * delta ≤ z 0 := (le_div_iff₀ hd).mp hfloor
      have hhi : z 0 < ((q : ℝ) + 1) * delta := (div_lt_iff₀ hd).mp hlt
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      linarith
    have hspace' (i : Fin 2) : ⌊z i.succ / delta⌋ ∈ Fs q i := by
      apply hspace q i
      calc
        _ = |(z i.succ - (center i + z 0 * velocity i)) +
            (z 0 - (q : ℝ) * delta) * velocity i| := by ring_nf
        _ ≤ |z i.succ - (center i + z 0 * velocity i)| +
            |(z 0 - (q : ℝ) * delta) * velocity i| := abs_add_le _ _
        _ ≤ width i + delta * L := by
          rw [abs_mul]
          exact add_le_add (hz.2 i)
            (mul_le_mul htd (hv i) (abs_nonneg _) hd.le)
        _ = _ := by ring
    have hQ : (fun i : Fin 2 => ⌊z i.succ / delta⌋) ∈ Q q := by
      exact Fintype.mem_piFinset.mpr hspace'
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hqt, Finset.mem_image.mpr ⟨_, hQ, ?_⟩⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Once the base mesh resolves every side and its motion, the number of
cells has the expected volume bound. -/
theorem movingBox_mesh_volume {delta radius L : ℝ} (hd : 0 < delta)
    (hdr : delta ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, delta ≤ width i)
    (hmove : ∀ i, L * delta ≤ width i) :
    ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) * delta ^ 3 ≤ 600 * radius * width 0 * width 1 ∧
      ∀ z ∈ movingBox time radius center velocity width, baseMesh delta z ∈ F := by
  have hr : 0 ≤ radius := hd.le.trans hdr
  have hw (i : Fin 2) : 0 ≤ width i := hd.le.trans (hdw i)
  obtain ⟨F, hF, hcover⟩ := movingBox_mesh_cover hd hr hL time center velocity width hv hw
  have ht : 4 * radius / delta + 2 ≤ 6 * radius / delta := by
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith
  have hs (i : Fin 2) :
      4 * (width i + L * delta) / delta + 2 ≤ 10 * width i / delta := by
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith [hmove i, hdw i]
  have hcard : (F.card : ℝ) ≤
      (6 * radius / delta) * ((10 * width 0 / delta) * (10 * width 1 / delta)) := by
    apply hF.trans
    apply mul_le_mul ht _ (Finset.prod_nonneg (by
      intro i hi
      have := hw i
      positivity)) (by positivity)
    simpa only [Fin.prod_univ_two] using Finset.prod_le_prod₀
      (s := Finset.univ) (f := fun i : Fin 2 => 4 * (width i + L * delta) / delta + 2)
      (fun i hi => by have := hw i; positivity) (fun i hi => hs i)
  refine ⟨F, ?_, hcover⟩
  calc
    (F.card : ℝ) * delta ^ 3 ≤
        ((6 * radius / delta) * ((10 * width 0 / delta) * (10 * width 1 / delta))) *
          delta ^ 3 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 600 * radius * width 0 * width 1 := by field_simp; ring

/-- The joint cell cap can be integrated over a moving box while retaining
any additional incidence condition, for example a fixed velocity bin. -/
theorem measure_movingBox_of_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {delta radius L C : ℝ} (hd : 0 < delta) (hdr : delta ≤ radius)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, delta ≤ width i)
    (hmove : ∀ i, L * delta ≤ width i)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * delta ^ 3)) :
    μ {p | z p ∈ movingBox time radius center velocity width ∧ condition p} ≤
      ENNReal.ofReal (600 * C * radius * width 0 * width 1) := by
  classical
  obtain ⟨F, hF, hcover⟩ := movingBox_mesh_volume hd hdr hL time center velocity width hv hdw hmove
  have hsub : {p | z p ∈ movingBox time radius center velocity width ∧ condition p} ⊆
      ⋃ q ∈ F, {p | baseMesh delta (z p) = q ∧ condition p} := by
    intro p hp
    exact mem_iUnion.mpr ⟨baseMesh delta (z p), mem_iUnion.mpr ⟨hcover _ hp.1, rfl, hp.2⟩⟩
  calc
    _ ≤ μ (⋃ q ∈ F, {p | baseMesh delta (z p) = q ∧ condition p}) := measure_mono hsub
    _ ≤ ∑ q ∈ F, μ {p | baseMesh delta (z p) = q ∧ condition p} :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _q ∈ F, ENNReal.ofReal (C * delta ^ 3) := Finset.sum_le_sum (fun q hq => hcap q)
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * delta ^ 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left hF hC]

end

end Submission.Lib.K4MovingMeshBoxes
