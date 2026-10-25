/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/MovingDepths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CriticalNode

/-!
Actual critical depths for families whose individual lengths vary. Scaling
is used only to choose numerical depths; every resulting chart and
refinement remains on the original exact problem.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Choose tilted endpoints on varying actual lengths. The profile error
is measured in the original exponent units throughout. -/
theorem exists_fractional_critical_depths (hcalc : Calculus)
    (p : ℕ → Code) (dstar θ lengthLimit : ℝ) (buffer : ℕ → ℝ)
    (hp : ∀ i, Exact (p i)) (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hlength : 0 < lengthLimit)
    (hLlim : Tendsto (fun i => L (p i)) atTop (𝓝 lengthLimit))
    (hbuffer : ∀ i, 0 < buffer i)
    (hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) (L (p i)),
      |f (p i) s - f (p i) 0 - dstar * s| ≤ ε * buffer i) :
    ∃ depth : ℕ → ℝ,
      (∀ i, depth i ∈ Icc 0 (θ * L (p i))) ∧
      (∀ i, depth i < L (p i)) ∧
      Tendsto depth atTop (𝓝 (θ * lengthLimit)) ∧
      (∀ᶠ i in atTop, 0 < depth i) ∧
      (∀ i s, s ∈ Icc 0 (depth i) →
        f (p i) (depth i) - f (p i) s ≤
          (dstar + buffer i / 2) * (depth i - s)) := by
  classical
  have hLp (i : ℕ) : 0 < L (p i) := exact_length_pos (hp i)
  have hchoose (i : ℕ) := hcalc.1 (p i) (L (p i)) (hp i) (hLp i)
  choose q hq hqL hqd hqS hqU hqH hqf using hchoose
  have hunit (i : ℕ) : L (q i) = 1 := by
    rw [hqL i, div_self (hLp i).ne']
  have hqscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      |f (q i) s - f (q i) 0 - dstar * s| ≤ ε * buffer i := by
    intro ε hε
    have hlarge : ∀ᶠ i in atTop, lengthLimit / 2 ≤ L (p i) :=
      (hLlim.eventually (Ioi_mem_nhds (show lengthLimit / 2 < lengthLimit by
        linarith))).mono fun _ hi => hi.le
    filter_upwards [hscaled (ε * lengthLimit / 2) (by positivity), hlarge]
      with i hi hlen s hs
    have hsL : L (p i) * s ∈ Icc 0 (L (p i)) :=
      ⟨mul_nonneg (hLp i).le hs.1, by
        simpa using mul_le_mul_of_nonneg_left hs.2 (hLp i).le⟩
    rw [hqf i s hs.1 (by simpa only [hunit i] using hs.2)]
    have halgebra : (f (p i) (L (p i) * s) - f (p i) 0) / L (p i) - dstar * s =
        (f (p i) (L (p i) * s) - f (p i) 0 - dstar * (L (p i) * s)) / L (p i) := by
      field_simp [(hLp i).ne']
    rw [halgebra, abs_div, abs_of_pos (hLp i)]
    apply (div_le_iff₀ (hLp i)).2
    have hmul := mul_le_mul_of_nonneg_left hlen
      (mul_nonneg hε.le (hbuffer i).le)
    nlinarith [hi _ hsL]
  obtain ⟨τ, hτ, hτlim, hτpos, hcap, hstrict⟩ := exists_actual_critical_nodes
    q dstar θ buffer hq hunit hstar₀ hstar₁ hθ₀ hθ₁ hbuffer hqscaled
  let depth := fun i => L (p i) * τ i
  have hdepth (i : ℕ) : depth i ∈ Icc 0 (θ * L (p i)) := by
    refine ⟨mul_nonneg (hLp i).le (hτ i).1, ?_⟩
    simpa only [depth, mul_comm] using mul_le_mul_of_nonneg_left (hτ i).2 (hLp i).le
  refine ⟨depth, hdepth, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hdepth i).2.trans_lt (by nlinarith [hLp i])
  · simpa only [depth, mul_comm] using hLlim.mul hτlim
  · exact hτpos.mono fun i hi => mul_pos (hLp i) hi
  · intro i s hs
    have hsτ : s / L (p i) ∈ Icc 0 (τ i) :=
      ⟨div_nonneg hs.1 (hLp i).le, (div_le_iff₀ (hLp i)).2 (by
        simpa only [depth, mul_comm] using hs.2)⟩
    have hsunit : s / L (p i) ≤ L (q i) := by
      rw [hunit i]
      exact hsτ.2.trans ((hτ i).2.trans hθ₁.le)
    have heqt := hqf i (τ i) (hτ i).1 (by
      rw [hunit i]
      exact (hτ i).2.trans hθ₁.le)
    have heqs := hqf i (s / L (p i)) hsτ.1 hsunit
    have hcancel : L (p i) * (s / L (p i)) = s := by
      field_simp [(hLp i).ne']
    rw [hcancel] at heqs
    have hdiff : f (q i) (τ i) - f (q i) (s / L (p i)) =
        (f (p i) (depth i) - f (p i) s) / L (p i) := by
      calc
        _ = (f (q i) (τ i) - f (q i) 0) -
            (f (q i) (s / L (p i)) - f (q i) 0) := by ring
        _ = _ := by rw [heqt, heqs]; dsimp only [depth]; ring
    have hc := mul_le_mul_of_nonneg_left (hcap i _ hsτ) (hLp i).le
    rw [hdiff] at hc
    have hleft : L (p i) * ((f (p i) (depth i) - f (p i) s) / L (p i)) =
        f (p i) (depth i) - f (p i) s := by field_simp [(hLp i).ne']
    have hright : L (p i) * ((dstar + buffer i / 2) * (τ i - s / L (p i))) =
        (dstar + buffer i / 2) * (depth i - s) := by
      dsimp only [depth]
      field_simp [(hLp i).ne']
    rwa [hleft, hright] at hc

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
