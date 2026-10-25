import Mathlib

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

def countingResolution (K H : ℝ) : ℝ := K^100 + 3*H + 3

def physicalCountingMesh (a h w K H : ℝ) : ℝ :=
  min w ((a/h)*w/countingResolution K H)

/-- One explicit mesh simultaneously resolves the original state floor,
the physical support census, and the physical potential's Lipschitz envelope. -/
theorem physical_counting_mesh_spec {a h w K H ε ζ : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hε : 0 < ε) (hζ : 0 < ζ)
    (hεζ : ε ≤ ζ) (hεclock : ε ≤ (a/h)*ζ)
    (hresolve : countingResolution K H * ζ ≤ w) :
    let p := physicalCountingMesh a h w K H
    0 < p ∧ ε ≤ p ∧ p ≤ w ∧ p ≤ 1 ∧ ε ≤ w ∧ ζ ≤ w ∧
      (H*h/a)*p ≤ w ∧ K^100*h*p ≤ a*w ∧
      (3+3*H)*ζ ≤ 2*w := by
  let D := countingResolution K H
  have hKpow : 0 ≤ K^100 := pow_nonneg hK _
  have hD : 0 < D := by dsimp [D, countingResolution]; positivity
  have hDone : 1 ≤ D := by dsimp [D, countingResolution]; linarith
  have hHD : H ≤ D := by dsimp [D, countingResolution]; linarith
  have hKD : K^100 ≤ D := by dsimp [D, countingResolution]; linarith
  have hζD : ζ ≤ w/D := (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hresolve)
  have hζw : ζ ≤ w := by
    exact (le_mul_of_one_le_left hζ.le hDone).trans hresolve
  have hew : ε ≤ w := hεζ.trans hζw
  have heclock : ε ≤ (a/h)*w/D := by
    calc
      _ ≤ (a/h)*ζ := hεclock
      _ ≤ (a/h)*(w/D) := mul_le_mul_of_nonneg_left hζD (by positivity)
      _ = _ := by ring
  have hp0 : 0 < physicalCountingMesh a h w K H := by
    unfold physicalCountingMesh
    exact lt_min hw (by dsimp only [D] at hD; positivity)
  have hεp : ε ≤ physicalCountingMesh a h w K H := le_min hew heclock
  have hpw : physicalCountingMesh a h w K H ≤ w := min_le_left _ _
  have hpD : physicalCountingMesh a h w K H ≤ (a/h)*w/D := min_le_right _ _
  have hLipp : (H*h/a)*physicalCountingMesh a h w K H ≤ w := by
    calc
      _ ≤ (H*h/a)*((a/h)*w/D) :=
        mul_le_mul_of_nonneg_left hpD (by positivity)
      _ = H*w/D := by field_simp
      _ ≤ D*w/D := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHD hw.le) hD.le
      _ = w := mul_div_cancel_left₀ _ hD.ne'
  have hphysp : K^100*h*physicalCountingMesh a h w K H ≤ a*w := by
    calc
      _ ≤ K^100*h*((a/h)*w/D) :=
        mul_le_mul_of_nonneg_left hpD (mul_nonneg hKpow hh.le)
      _ = K^100*(a*w)/D := by field_simp
      _ ≤ D*(a*w)/D := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKD (by positivity)) hD.le
      _ = a*w := mul_div_cancel_left₀ _ hD.ne'
  have hsmall : (3+3*H)*ζ ≤ 2*w := by
    have hHDD : 3+3*H ≤ D := by dsimp [D, countingResolution]; linarith
    exact ((mul_le_mul_of_nonneg_right hHDD hζ.le).trans hresolve).trans (by linarith)
  exact ⟨hp0, hεp, hpw, hpw.trans hw1, hew, hζw, hLipp, hphysp, hsmall⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates
