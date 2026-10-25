import Mathlib

/-!
Endpoint and angular selection for a two-parameter density profile.
-/

namespace Submission.Obl.k4_profile_endpoint_crop

/-- The two coordinate increment bounds of the joint density profile. -/
def JointIncrements (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ 1 → 0 ≤ u → u ≤ 4 →
    0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧
  (∀ r u u' : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ u' → u' ≤ 4 →
    0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ 2 * (u' - u))

lemma profile_dist_r {F : ℝ → ℝ → ℝ} (hF : JointIncrements F)
    {r s u : ℝ} (hr : r ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc 0 4) : |F r u - F s u| ≤ |r - s| := by
  rcases le_total r s with hrs | hsr
  · rcases hF.1 r s u hr.1 hrs hs.2 hu.1 hu.2 with ⟨h0, h1⟩
    rw [abs_of_nonpos (by linarith : F r u - F s u ≤ 0),
      abs_of_nonpos (by linarith : r - s ≤ 0)]
    linarith
  · rcases hF.1 s r u hs.1 hsr hr.2 hu.1 hu.2 with ⟨h0, h1⟩
    rw [abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr hsr)]
    exact h1

lemma profile_dist_u {F : ℝ → ℝ → ℝ} (hF : JointIncrements F)
    {r u v : ℝ} (hr : r ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 4)
    (hv : v ∈ Set.Icc 0 4) : |F r u - F r v| ≤ 2 * |u - v| := by
  rcases le_total u v with huv | hvu
  · rcases hF.2 r u v hr.1 hr.2 hu.1 huv hv.2 with ⟨h0, h1⟩
    rw [abs_of_nonpos (by linarith : F r u - F r v ≤ 0),
      abs_of_nonpos (by linarith : u - v ≤ 0)]
    linarith
  · rcases hF.2 r v u hr.1 hr.2 hv.1 hvu hu.2 with ⟨h0, h1⟩
    rw [abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact h1

lemma profile_continuousOn {F : ℝ → ℝ → ℝ} (hF : JointIncrements F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Icc 0 1 ×ˢ Set.Icc 0 4) := by
  apply LipschitzOnWith.continuousOn (K := 3)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hr := profile_dist_r hF hp.1 hq.1 hp.2
  have hu := profile_dist_u hF hq.1 hp.2 hq.2
  have htri := abs_sub_le (F p.1 p.2) (F q.1 p.2) (F q.1 q.2)
  have hfirst : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsecond : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  linarith

/-- A positive gap at `(1,0)` yields an interior endpoint and angular growth.
The endpoint deficit and the angular growth can use the same explicit constant. -/
theorem exists_profile_endpoint {F : ℝ → ℝ → ℝ} {σ : ℝ}
    (hF : JointIncrements F) (hσ : 0 < σ)
    (h10 : F 1 0 ≤ 1 - σ) (h00 : 0 ≤ F 0 0)
    (hlower : ∀ r u : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 →
      2 * u - 2 ≤ F r u) :
    ∃ L u d S η : ℝ,
      0 < L ∧ L ≤ 1 ∧ 0 ≤ u ∧ u < 4 ∧
      0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧
      u + η * L < 4 ∧ σ / 2 ≤ L - F L u ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ L → F L u - F r u ≤ d * (L - r)) ∧
      (∀ v : ℝ, 0 ≤ v → v ≤ η * L → S * v ≤ F L (u + v) - F L u) := by
  have h01 := hF.1 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hσ1 : σ ≤ 1 := by linarith [h01.1]
  let R : ℝ := σ / 20
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R]; linarith
  let Φ : ℝ × ℝ → ℝ := fun p => p.1 - F p.1 p.2 - R * p.1 + R * p.2
  have hcont : ContinuousOn Φ (Set.Icc 0 1 ×ˢ Set.Icc 0 4) :=
    (((continuous_fst.continuousOn.sub (profile_continuousOn hF)).sub
      (continuous_const.mul continuous_fst).continuousOn).add
      (continuous_const.mul continuous_snd).continuousOn)
  have hbase : (1, 0) ∈ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 4) := by
    norm_num
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(1, 0), hbase⟩ hcont
  have hval := hmax hbase
  dsimp [Φ] at hval
  have hL : 0 < p.1 := by
    by_contra h
    have hp0 : p.1 = 0 := le_antisymm (le_of_not_gt h) hp.1.1
    have hnonneg := hF.2 0 0 p.2 (by norm_num) (by norm_num)
      (by norm_num) hp.2.1 hp.2.2
    rw [hp0] at hval
    dsimp [R] at hval
    nlinarith [hnonneg.1, hp.2.2]
  have hu : p.2 < 4 := by
    by_contra h
    have hp4 : p.2 = 4 := le_antisymm hp.2.2 (le_of_not_gt h)
    have hlow := hlower p.1 4 hp.1.1 hp.1.2 (by norm_num) (by norm_num)
    rw [hp4] at hval
    dsimp [R] at hval
    nlinarith [mul_nonneg hR.le hp.1.1, hp.1.2]
  have hgap : σ / 2 ≤ p.1 - F p.1 p.2 := by
    have hRp : 0 ≤ R * p.1 := mul_nonneg hR.le hp.1.1
    have hRu : R * p.2 ≤ R * 4 := mul_le_mul_of_nonneg_left hp.2.2 hR.le
    dsimp [R] at hRp hRu hval
    linarith
  let η : ℝ := (4 - p.2) / (2 * p.1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηL : η * p.1 = (4 - p.2) / 2 := by
    dsimp [η]
    field_simp
  refine ⟨p.1, p.2, 1 - R, R, η, hL, hp.1.2, hp.2.1, hu,
    sub_pos.mpr hR1, by linarith, hR, hη, ?_, hgap, ?_, ?_⟩
  · rw [hηL]
    linarith
  · intro r hr0 hrL
    have hmem : (r, p.2) ∈ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 4) :=
      ⟨⟨hr0, hrL.trans hp.1.2⟩, hp.2⟩
    have hm := hmax hmem
    dsimp [Φ] at hm
    nlinarith
  · intro v hv0 hv
    have hmem : (p.1, p.2 + v) ∈
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 4) := by
      refine ⟨hp.1, add_nonneg hp.2.1 hv0, ?_⟩
      rw [hηL] at hv
      linarith
    have hm := hmax hmem
    dsimp [Φ] at hm
    nlinarith

end Submission.Obl.k4_profile_endpoint_crop
