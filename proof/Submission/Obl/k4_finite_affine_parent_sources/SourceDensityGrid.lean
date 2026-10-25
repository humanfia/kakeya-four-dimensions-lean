import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityMasks
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample
import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleDepths

/-!
# The fixed density grid at intermediate path depths

Choose every cleaning depth from the already supplied original grid. The same grid also
enumerates the pure-cap mask; neither construction changes the original density law.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open Set MeasureTheory

noncomputable section

/-- Two endpoint profile errors control every increment between them. -/
theorem profile_increment_lower {f : ℝ → ℝ} {L d δ₀ r s : ℝ}
    (hprof : ∀ t : ℝ, 0 ≤ t → t ≤ L → |f t - f 0 - d * t| ≤ δ₀ * L)
    (hr : 0 ≤ r) (hrL : r ≤ L) (hs : 0 ≤ s) (hsL : s ≤ L) :
    f r + d * (s - r) - 2 * (δ₀ * L) ≤ f s := by
  have h₁ := (abs_le.mp (hprof r hr hrL)).2
  have h₂ := (abs_le.mp (hprof s hs hsL)).1
  linarith

/-- Rounding a real depth upwards by at most `h` costs at most `2 N^h` in dyadic width. -/
theorem density_grid_width_ratio {Nk r s h : ℝ} (hNk : 1 < Nk) (hrs : s ≤ r + h) :
    δ Nk r ≤ 2 * Nk ^ h * δ Nk s := by
  have hNk0 : 0 < Nk := zero_lt_one.trans hNk
  have hpow : Nk ^ (-r) ≤ Nk ^ h * Nk ^ (-s) := by
    rw [← Real.rpow_add hNk0]
    exact Real.rpow_le_rpow_of_exponent_le hNk.le (by linarith)
  calc δ Nk r ≤ 2 * Nk ^ (-r) := (δ_bounds hNk r).2.le
    _ ≤ 2 * (Nk ^ h * Nk ^ (-s)) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 2 * Nk ^ h * δ Nk s := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (δ_bounds hNk s).1
        (show 0 ≤ 2 * Nk ^ h by positivity)

/-- The actual density grid supplies one depth for each intermediate path level. -/
theorem group_density_depths {Nk L d δ₀ hd : ℝ} {f : ℝ → ℝ}
    (hNk : 1 < Nk) (hd₁ : 0 ≤ d) (Qd : Finset ℝ)
    (hQd : ∀ r ∈ Qd, 0 ≤ r ∧ r ≤ L)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ L → ∃ r ∈ Qd, t ≤ r ∧ r ≤ t + hd)
    (hprof : ∀ t : ℝ, 0 ≤ t → t ≤ L → |f t - f 0 - d * t| ≤ δ₀ * L)
    (J : ℕ) (depth : ℕ → ℝ) (hdepth : ∀ i < J, 0 ≤ depth i ∧ depth i ≤ L) :
    ∃ rq : ℕ → ℝ,
      (∀ i < J, rq i ∈ Qd) ∧
      (∀ i < J, depth i ≤ rq i ∧ rq i ≤ depth i + hd) ∧
      (∀ i < J, δ Nk (depth i) ≤ 2 * Nk ^ hd * δ Nk (rq i)) ∧
      (∀ i < J, f (depth i) - 2 * (δ₀ * L) ≤ f (rq i)) := by
  classical
  have hex : ∀ i : Fin J, ∃ r ∈ Qd, depth i ≤ r ∧ r ≤ depth i + hd :=
    fun i => hcover (depth i) (hdepth i i.isLt).1 (hdepth i i.isLt).2
  choose r hr using hex
  let rq : ℕ → ℝ := fun i => if hi : i < J then r ⟨i, hi⟩ else 0
  have hspec : ∀ i (hi : i < J), rq i ∈ Qd ∧ depth i ≤ rq i ∧ rq i ≤ depth i + hd := by
    intro i hi
    simpa only [rq, dif_pos hi] using hr ⟨i, hi⟩
  refine ⟨rq, fun i hi => (hspec i hi).1, fun i hi => (hspec i hi).2, ?_, ?_⟩
  · intro i hi
    exact density_grid_width_ratio hNk (hspec i hi).2.2
  · intro i hi
    have hp := profile_increment_lower hprof (hdepth i hi).1 (hdepth i hi).2
      (hQd _ (hspec i hi).1).1 (hQd _ (hspec i hi).1).2
    have hinc : 0 ≤ d * (rq i - depth i) := mul_nonneg hd₁ (by linarith [(hspec i hi).2.1])
    linarith

/-- Enumerate the original density grid without losing any of its depths. -/
theorem density_grid_enumeration (Qd : Finset ℝ) :
    ∃ r : Fin Qd.card → ℝ,
      (∀ j, r j ∈ Qd) ∧ (∀ q ∈ Qd, ∃ j, r j = q) := by
  classical
  refine ⟨fun j => (Qd.equivFin.symm j).val, fun j => (Qd.equivFin.symm j).property, ?_⟩
  intro q hq
  refine ⟨Qd.equivFin ⟨q, hq⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]

/-- Covering depths in the original finite set are also present in its fixed enumeration. -/
theorem density_grid_indexed_cover {L hd : ℝ} (Qd : Finset ℝ)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ L → ∃ q ∈ Qd, t ≤ q ∧ q ≤ t + hd)
    {G : ℕ} (r : Fin G → ℝ) (hr : ∀ q ∈ Qd, ∃ j, r j = q) :
    ∀ t : ℝ, 0 ≤ t → t ≤ L → ∃ j, t ≤ r j ∧ r j ≤ t + hd := by
  intro t ht htL
  obtain ⟨q, hq, hlo, hhi⟩ := hcover t ht htL
  obtain ⟨j, hj⟩ := hr q hq
  exact ⟨j, by simpa only [hj] using hlo, by simpa only [hj] using hhi⟩

/-- The enumerated grid covers every composed native depth and gives its pure-cap profile. -/
theorem density_grid_native_cover {L d δ₀ r₀ unit T hd : ℝ} {f : ℝ → ℝ}
    {G : ℕ} (r : Fin G → ℝ)
    (hr : ∀ j, 0 ≤ r j ∧ r j ≤ L)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ L → ∃ j, t ≤ r j ∧ r j ≤ t + hd)
    (hprof : ∀ t : ℝ, 0 ≤ t → t ≤ L → |f t - f 0 - d * t| ≤ δ₀ * L)
    (hr₀ : 0 ≤ r₀) (hr₀L : r₀ ≤ L) (huL : 0 ≤ unit * L)
    (hroom : r₀ + unit * L * T ≤ L) :
    ∀ s : ℝ, 0 ≤ s → s ≤ T → ∃ j,
      r₀ + unit * L * s ≤ r j ∧ r j ≤ r₀ + unit * L * s + hd ∧
      f r₀ + d * (r j - r₀) - 2 * (δ₀ * L) ≤ f (r j) := by
  intro s hs hsT
  have ht0 : 0 ≤ r₀ + unit * L * s := add_nonneg hr₀ (mul_nonneg huL hs)
  have htL : r₀ + unit * L * s ≤ L :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsT huL)).trans hroom
  obtain ⟨j, hj₁, hj₂⟩ := hcover _ ht0 htL
  exact ⟨j, hj₁, hj₂, profile_increment_lower hprof hr₀ hr₀L (hr j).1 (hr j).2⟩

/-- A selected set satisfies the density mask at every enumerated original depth. -/
theorem selectionMask_subset_densMask {Nk L S τd τa Bw : ℝ} {f : ℝ → ℝ}
    {g : ℝ → Observation → ENNReal}
    {Ga : ℝ → Observation × (Fin 2 → ℤ) → ENNReal} {Qd Qa : Finset ℝ}
    {H E : Set Incidence} (hHE : H ⊆ E)
    (hmask : ∀ z ∈ H, SelectionMask Nk L S τd τa f Bw g Ga Qd Qa z)
    {G : ℕ} (r : Fin G → ℝ) (hr : ∀ j, r j ∈ Qd) :
    H ⊆ E ∩ densMask g Bw Nk τd f r := by
  intro z hz
  refine ⟨hHE hz, mem_iInter.mpr fun j => ?_⟩
  exact (hmask z hz).1 (r j) (hr j)

/-- The half-window decay gives the exact parent-to-middle width ordering used by groups. -/
theorem group_width_order_of_scale_decay {N T a b : ℝ}
    (hN : 2 ≤ N) (hT : 1 ≤ T) (hb : 0 < b)
    (hdecay : a / b ≤ 2 * N ^ (-100 * T)) : a ≤ b := by
  have hN0 : 0 < N := by linarith
  have hp : N ^ (-100 * T) ≤ N ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hh : 2 * N ^ (-100 * T) ≤ 1 := by
    calc 2 * N ^ (-100 * T) ≤ 2 * N ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 2 / N := by rw [Real.rpow_neg_one]; rfl
      _ ≤ 1 := (div_le_one hN0).mpr hN
  exact (div_le_one hb).mp (hdecay.trans hh)

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Choose the actual intermediate cleaning depths and all four density inputs of
`selection_construct`, using the sample's original grid and window schedule. -/
theorem sample_q_density_inputs {n : ℕ} {unit T mesh hd d₁ : ℝ}
    (hNk : 1 < Nk) (hL : 0 < L) (hd₁ : 0 ≤ d₁) (hn : 2 ≤ n)
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hu : 0 < unit) (hu1 : unit ≤ 1 / 64)
    (hδ0 : 0 ≤ δ₀) (hδu : δ₀ ≤ unit) (hδ1 : δ₀ ≤ 1 / 64)
    (hmesh : mesh ≤ unit) (hnT : (n : ℝ) < T) (hTu : unit * T ≤ 1 / 64)
    (hNative : 2 ≤ Nk ^ (unit * L))
    (q : TangentWindows m sg (selectionLookahead κ₁ T) unit mesh)
    (hstrict : StrictMonoOn sg (Iio m))
    (Qd : Finset ℝ) (hQd : ∀ r ∈ Qd, 0 ≤ r ∧ r ≤ L)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ L → ∃ r ∈ Qd, t ≤ r ∧ r ≤ t + hd)
    (hprof : ∀ t : ℝ, 0 ≤ t → t ≤ L → |f t - f 0 - d₁ * t| ≤ δ₀ * L) :
    ∃ rq : ℕ → ℝ,
      (∀ i < q.count, rq i ∈ Qd) ∧
      (∀ i < q.count, p.r (q.middle i) ≤ rq i ∧ rq i ≤ p.r (q.middle i) + hd) ∧
      (∀ i < q.count, δ Nk (p.r (q.middle i)) ≤ 2 * Nk ^ hd * δ Nk (rq i)) ∧
      (∀ i < q.count, f (p.r (q.middle i)) - 2 * (δ₀ * L) ≤ f (rq i)) ∧
      (∀ i < q.count, δ Nk (p.r (q.middle i)) ≤ δ Nk (p.r (q.level i))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hdepth : ∀ i < q.count, 0 ≤ p.r (q.middle i) ∧ p.r (q.middle i) ≤ L := by
    intro i hi
    exact (sample_window_depth_room hp q hstrict hL.le hu.le hu1 hδ1 hT0 hTu hi).1
  obtain ⟨rq, hmem, hrq, hratio, hprofile⟩ := group_density_depths hNk hd₁ Qd hQd
    hcover hprof q.count (fun i => p.r (q.middle i)) hdepth
  refine ⟨rq, hmem, hrq, hratio, hprofile, ?_⟩
  intro i hi
  obtain ⟨_, _, _, _, _, hdecay⟩ := source_window_scale_decay hp hn hκ hκ1 hu hnT hmesh
    hδ0 hδu hNk.le hL.le q i hi
  have hδpos : 0 < δ Nk (p.r (q.level i)) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hNk) _).trans_le (δ_bounds hNk _).1
  exact group_width_order_of_scale_decay hNative hT1 hδpos hdecay

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
