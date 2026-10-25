import Submission.Obl.k4_scalar_noisy_block_packets.DirectAngular
import Submission.Obl.k4_profile_endpoint_crop.Endpoint

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_noisy_block_packets

open Set

/-- Rescale to the accepted unit-rectangle continuity lemma. -/
theorem shape_continuousOn {d s m S U C₀ : ℝ} {angular : Bool} {F : ℝ → ℝ → ℝ}
    (hs : 0 < s) (hV : 0 < 4 * (m + s + 1))
    (hF : ProfileShape d s m S U C₀ angular F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc 0 s ×ˢ Icc 0 (4 * (m + s + 1))) := by
  let V := 4 * (m + s + 1)
  let A := s + V
  have hA : 0 < A := by dsimp [A, V]; linarith
  let F' : ℝ → ℝ → ℝ := fun r u => F (s * r) (V * u / 4) / A
  have hinc : k4_profile_endpoint_crop.JointIncrements F' := by
    constructor
    · intro r r' u hr hrr' hr' hu hu'
      have hsr : 0 ≤ s * r := mul_nonneg hs.le hr
      have hsrr : s * r ≤ s * r' := mul_le_mul_of_nonneg_left hrr' hs.le
      have hsr' : s * r' ≤ s := by nlinarith
      have hvu : 0 ≤ V * u / 4 := by positivity
      have hvu' : V * u / 4 ≤ V := by dsimp [V] at *; nlinarith
      obtain ⟨h0, h1⟩ := hF.1 (s * r) (s * r') (V * u / 4) hsr hsrr hsr' hvu hvu'
      change 0 ≤ F (s * r') (V * u / 4) / A - F (s * r) (V * u / 4) / A ∧ _
      rw [← sub_div]
      refine ⟨div_nonneg h0 hA.le, (div_le_iff₀ hA).2 ?_⟩
      have hAV : s ≤ A := by dsimp [A, V]; linarith
      have := mul_le_mul_of_nonneg_right hAV (sub_nonneg.2 hrr')
      nlinarith
    · intro r u u' hr hr' hu huu' hu'
      have hsr : 0 ≤ s * r := mul_nonneg hs.le hr
      have hsr' : s * r ≤ s := by nlinarith
      have hvu : 0 ≤ V * u / 4 := by positivity
      have hvuu : V * u / 4 ≤ V * u' / 4 := by dsimp [V] at *; nlinarith
      have hvu' : V * u' / 4 ≤ V := by dsimp [V] at *; nlinarith
      obtain ⟨h0, h1⟩ := hF.2.1 (s * r) (V * u / 4) (V * u' / 4) hsr hsr' hvu hvuu hvu'
      change 0 ≤ F (s * r) (V * u' / 4) / A - F (s * r) (V * u / 4) / A ∧ _
      rw [← sub_div]
      refine ⟨div_nonneg h0 hA.le, (div_le_iff₀ hA).2 ?_⟩
      have hAV : V / 4 ≤ 2 * A := by dsimp [A, V]; linarith
      have := mul_le_mul_of_nonneg_right hAV (sub_nonneg.2 huu')
      nlinarith
  have hc := k4_profile_endpoint_crop.profile_continuousOn hinc
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1 / s, 4 * p.2 / V))
      (Icc 0 s ×ˢ Icc 0 V) (Icc 0 1 ×ˢ Icc 0 4) := by
    intro p hp
    refine ⟨⟨div_nonneg hp.1.1 hs.le, (div_le_one hs).2 hp.1.2⟩,
      ⟨div_nonneg (by linarith [hp.2.1]) hV.le, (div_le_iff₀ hV).2 ?_⟩⟩
    linarith [hp.2.2]
  have hcomp := hc.comp (by fun_prop : ContinuousOn
    (fun p : ℝ × ℝ => (p.1 / s, 4 * p.2 / V)) (Icc 0 s ×ˢ Icc 0 V)) hmap
  have hcont := (continuous_const : Continuous (fun _ : ℝ × ℝ => A)).continuousOn.mul hcomp
  apply hcont.congr
  intro p hp
  symm
  change A * (F (s * (p.1 / s)) (V * (4 * p.2 / V) / 4) / A) = F p.1 p.2
  have hr : s * (p.1 / s) = p.1 := by field_simp [hs.ne']
  have hu : V * (4 * p.2 / V) / 4 = p.2 := by field_simp [show V ≠ 0 from hV.ne']
  rw [hr, hu]
  field_simp [hA.ne']

/-- The near-terminal scalar optimizer, with the exact endpoint bounds required for
cropping. This contains no measure-theoretic assumptions. -/
theorem scalar_profile_selection
    (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hsm : s < m)
    (hS : 0 < S) (hU : 0 < U) (hUm : U < m)
    (hF : ProfileShape d s m S U C₀ angular F) (η : ℝ) (hη : 0 < η) :
    ∃ L u₀ d' S' U' : ℝ,
      0 < L ∧ L ≤ s ∧ 0 ≤ u₀ ∧ u₀ ≤ m + η ∧
      0 ≤ d' ∧ d' < 1 ∧ 0 < S' ∧ 0 < U' ∧
      u₀ + U' ≤ 4 * (m + s + 1) ∧
      s - L ≤ η ∧ F L u₀ ≤ d * s - C₀ + η ∧
      (angular = true → u₀ = 0) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ L → F L u₀ - F r u₀ ≤ d' * (L - r)) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ U' → F L u₀ + S' * u ≤ F L (u₀ + u)) := by
  have hm : 0 < m := lt_trans hs hsm
  have hV : 0 < 4 * (m + s + 1) := by linarith
  by_cases hang : angular = true
  · refine ⟨s, 0, d, S, U, hs, le_rfl, le_rfl, by linarith, hd, hd1, hS, hU,
      by linarith, by linarith, ?_, (fun _ => rfl), ?_, ?_⟩
    · rw [hF.2.2.1]
      linarith
    · intro r hr hrs
      exact profile_endpoint_cap hF hr hrs hV.le
    · intro u hu huU
      simpa only [zero_add] using hF.2.2.2.2 hang u hu huU
  let V := 4 * (m + s + 1)
  let R := (1 - d) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hdR : d = 1 - 2 * R := by dsimp [R]; ring
  have hsmall : (0 : ℝ) < min (1 / 2)
      (min (η / (m + η + 1)) (min (η / V) (min (η * R / V) (s * R / (2 * V))))) := by
    positivity
  obtain ⟨θ, hθ, hθsmall⟩ := exists_between hsmall
  rcases lt_min_iff.1 hθsmall with ⟨hθhalf, hθsmall⟩
  rcases lt_min_iff.1 hθsmall with ⟨hθm, hθsmall⟩
  rcases lt_min_iff.1 hθsmall with ⟨hθη, hθsmall⟩
  rcases lt_min_iff.1 hθsmall with ⟨hθηR, hθsR⟩
  have hθV : θ * V ≤ η := (le_div_iff₀ hV).1 hθη.le
  have hθVR : θ * V ≤ η * R := (le_div_iff₀ hV).1 hθηR.le
  have hθVs : θ * (2 * V) < s * R := (lt_div_iff₀ (by positivity)).1 hθsR
  have hθm' : θ * (m + η + 1) < η := (lt_div_iff₀ (by positivity)).1 hθm
  let Φ : ℝ × ℝ → ℝ := fun p => (1 - R) * p.1 - F p.1 p.2 + θ * p.2
  have hcont : ContinuousOn Φ (Icc 0 s ×ˢ Icc 0 V) :=
    (((continuous_const.mul continuous_fst).continuousOn.sub
      (shape_continuousOn hs hV hF)).add (continuous_const.mul continuous_snd).continuousOn)
  have hbase : (s, 0) ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V :=
    ⟨⟨hs.le, le_rfl⟩, ⟨le_rfl, hV.le⟩⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(s, 0), hbase⟩ hcont
  have hval := hmax hbase
  dsimp [Φ] at hval
  have hval' : C₀ + R * s ≤ (1 - R) * p.1 - F p.1 p.2 + θ * p.2 := by
    rw [hF.2.2.1, hdR] at hval
    nlinarith
  have hlo := hF.2.2.2.1 p.1 p.2 hp.1.1 hp.1.2 hp.2.1 hp.2.2
  have hlo0 : (1 - 2 * R) * p.1 - C₀ ≤ F p.1 p.2 := by
    rw [hdR] at hlo
    have := le_max_left (0 : ℝ) (p.2 - m)
    linarith
  have hlom : (1 - 2 * R) * p.1 - C₀ + p.2 - m ≤ F p.1 p.2 := by
    rw [hdR] at hlo
    have := le_max_right (0 : ℝ) (p.2 - m)
    linarith
  have hθu : θ * p.2 ≤ θ * V := mul_le_mul_of_nonneg_left hp.2.2 hθ.le
  have hnear : s - p.1 ≤ η := by
    apply (mul_le_mul_iff_right₀ hR).1
    nlinarith only [hval', hlo0, hθu, hθVR]
  have hL : 0 < p.1 := by
    by_contra hn
    have hRL : R * p.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR.le (le_of_not_gt hn)
    have hRs : 0 < R * s := mul_pos hR hs
    nlinarith only [hval', hlo0, hθu, hθVs, hRL, hRs]
  have hucontrol : (1 - θ) * p.2 ≤ m := by
    have hRle := mul_le_mul_of_nonneg_left hp.1.2 hR.le
    nlinarith only [hRle, hval', hlom]
  have hum : p.2 ≤ m + η := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1 - θ by linarith only [hθhalf])).1
    nlinarith only [hucontrol, hθm', hθ]
  have hu2m : p.2 ≤ 2 * m := by
    have hmul := mul_le_mul_of_nonneg_right hθhalf.le hp.2.1
    nlinarith only [hucontrol, hmul]
  have huV : p.2 + s ≤ V := by dsimp [V]; linarith only [hu2m, hm, hs]
  have hFval : F p.1 p.2 ≤ d * s - C₀ + η := by
    have hRle := mul_le_mul_of_nonneg_left hp.1.2 (sub_nonneg.mpr hR1.le)
    rw [hF.2.2.1] at hval
    nlinarith only [hval, hRle, hθu, hθV]
  refine ⟨p.1, p.2, 1 - R, θ, s, hL, hp.1.2, hp.2.1, hum,
    by linarith only [hR1], by linarith only [hR], hθ, hs, huV, hnear, hFval, (fun h => (hang h).elim), ?_, ?_⟩
  · intro r hr hrL
    have hmem : (r, p.2) ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V :=
      ⟨⟨hr, hrL.trans hp.1.2⟩, hp.2⟩
    have hh := hmax hmem
    dsimp [Φ] at hh
    nlinarith only [hh]
  · intro u hu hus
    have hmem : (p.1, p.2 + u) ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V :=
      ⟨hp.1, ⟨by linarith [hp.2.1], by linarith⟩⟩
    have hh := hmax hmem
    dsimp [Φ] at hh
    nlinarith only [hh]

end Submission.Obl.k4_scalar_noisy_block_packets
