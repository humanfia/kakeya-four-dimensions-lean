import Submission.Obl.k4_narrow_projected_row_parents.Growth
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ParentNativeSheets
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_narrow_projected_row_parents.ComparisonFrame

open Filter
open Cmp.SheetComparison

noncomputable section

def nativeBound (K : ℝ) (n : ℕ) : ℝ := (884736 * K ^ 7) ^ n

def stableDivisor (K : ℝ) (n : ℕ) : ℝ := 10000 * nativeBound K n

def chartBound (C K H : ℝ) (n : ℕ) : ℝ := 4 * (C * H ^ 3 + nativeBound K n + 1)

def errorMultiplier (K H : ℝ) : ℝ := 128 * ((2 * K) ^ 9 + H)

def errorScale (N C K H s : ℝ) : ℝ := errorMultiplier K H * N ^ (-s)

def zoomMesh (N C K H s : ℝ) (n : ℕ) : ℝ :=
  errorScale N C K H s / (12 * chartBound C K H n)

theorem nativeBound_eq (K : ℝ) (n : ℕ) :
    nativeBound K n = (2 * K * parentBinCap K) ^ n := by
  unfold nativeBound
  congr 1
  unfold parentBinCap
  ring

theorem nativeBound_one {K : ℝ} (hK : 1 ≤ K) (n : ℕ) : 1 ≤ nativeBound K n := by
  unfold nativeBound
  apply one_le_pow₀
  have hK7 : 1 ≤ K ^ 7 := one_le_pow₀ hK
  linarith

theorem stableDivisor_bounds {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    1 ≤ stableDivisor K n ∧ 10000 ≤ stableDivisor K n * (nativeBound K n)⁻¹ := by
  have hV := nativeBound_one hK n
  have hVp : 0 < nativeBound K n := zero_lt_one.trans_le hV
  constructor
  · unfold stableDivisor
    linarith
  · unfold stableDivisor
    rw [mul_assoc, mul_inv_cancel₀ hVp.ne', mul_one]

theorem chartBound_bounds {C K H : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) (hH : 1 ≤ H) (n : ℕ) :
    2 ≤ chartBound C K H n ∧ 4 * nativeBound K n ≤ chartBound C K H n ∧
      4 * (C * H ^ 3) ≤ chartBound C K H n := by
  have hV := nativeBound_one hK n
  have hCH : 0 ≤ C * H ^ 3 := mul_nonneg hC (pow_nonneg (zero_le_one.trans hH) _)
  unfold chartBound
  exact ⟨by linarith, by linarith, by linarith⟩

theorem errorMultiplier_bounds {K H : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H) :
    1 ≤ errorMultiplier K H ∧ 128 * (2 * K) ^ 9 ≤ errorMultiplier K H ∧
      4 * H ≤ errorMultiplier K H := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hpow : 0 ≤ (2 * K) ^ 9 := by positivity
  unfold errorMultiplier
  exact ⟨by linarith, by linarith, by linarith⟩

theorem errorScale_bounds {N C K H s : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hH : 1 ≤ H) :
    N ^ (-s) ≤ errorScale N C K H s ∧
      32 * (2 * K) ^ 9 * N ^ (-s) ≤ errorScale N C K H s / 4 ∧
      4 * (H * N ^ (-s)) ≤ errorScale N C K H s := by
  obtain ⟨hA, hnative, hproj⟩ := errorMultiplier_bounds hK hH
  have hw : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN.le _
  unfold errorScale
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hA) hw]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hnative) hw]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hproj) hw]

/-- Every coefficient budget used by the actual frame choice is subpower. -/
theorem subpower_budgets {N K H : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k)
    (hKsub : Model.Subpow N K) (hHsub : Model.Subpow N H)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    Model.Subpow N (fun k => nativeBound (K k) n) ∧
      Model.Subpow N (fun k => stableDivisor (K k) n) ∧
      Model.Subpow N (fun k => chartBound C (K k) (H k) n) ∧
      Model.Subpow N (fun k => errorMultiplier (K k) (H k)) := by
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hH0 : ∀ k, 0 ≤ H k := fun k => zero_le_one.trans (hH k)
  have hc (c : ℝ) : Model.Subpow N (fun _ => c) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt c
  have hm {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
      (hf : Model.Subpow N f) (hg : Model.Subpow N g) :
      Model.Subpow N (fun k => f k * g k) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNp hf0 hg0 hf hg
  have hp {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Model.Subpow N f) (j : ℕ) :
      Model.Subpow N (fun k => f k ^ j) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN hf0 hf j
  have hK7 := hp hK0 hKsub 7
  have hbase := hm (fun _ => by norm_num) (fun k => pow_nonneg (hK0 k) _)
    (hc 884736) hK7
  have hV : Model.Subpow N (fun k => nativeBound (K k) n) :=
    hp (fun k => by positivity [hK0 k]) hbase n
  have hR : Model.Subpow N (fun k => stableDivisor (K k) n) :=
    hm (fun _ => by norm_num) (fun k => zero_le_one.trans (nativeBound_one (hK k) n))
      (hc 10000) hV
  have hH3 := hp hH0 hHsub 3
  have hCH := hm (fun _ => hC) (fun k => pow_nonneg (hH0 k) _) (hc C) hH3
  have hsum := (hCH.add hNp hNt hV).add hNp hNt (hc 1)
  have hchart : Model.Subpow N (fun k => chartBound C (K k) (H k) n) :=
    hm (fun _ => by norm_num) (fun k => by positivity [hH0 k, nativeBound_one (hK k) n])
      (hc 4) hsum
  have h2K := hm (fun _ => by norm_num) hK0 (hc 2) hKsub
  have h2K9 := hp (fun k => by positivity [hK0 k]) h2K 9
  have hsumA := h2K9.add hNp hNt hHsub
  have hA : Model.Subpow N (fun k => errorMultiplier (K k) (H k)) :=
    hm (fun _ => by norm_num) (fun k => by positivity [hK0 k, hH0 k]) (hc 128) hsumA
  exact ⟨hV, hR, hchart, hA⟩

/-- The comparison zoom mesh is small enough for the finite mesh constructor,
and has a fixed power lower bound for the physical-mesh resolution. -/
theorem eventually_zoomMesh_bounds {N K H : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k)
    (hKsub : Model.Subpow N K) (hHsub : Model.Subpow N H)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, 0 < zoomMesh (N k) C (K k) (H k) s n ∧
      zoomMesh (N k) C (K k) (H k) s n ≤ 1 / 24 ∧
      N k ^ (-(s + 1)) ≤ zoomMesh (N k) C (K k) (H k) s n ∧
      2 * chartBound C (K k) (H k) n * (3 * zoomMesh (N k) C (K k) (H k) s n) ≤
        errorScale (N k) C (K k) (H k) s / 2 := by
  obtain ⟨_, _, hchart, hA⟩ := subpower_budgets hN hNt hK hH hKsub hHsub C hC n
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt (fun k => (errorMultiplier_bounds (hK k) (hH k)).1) hA
    1 (a := -s) (b := 0) (by linarith) (A := 1) (by norm_num)
  have hden := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt (fun k => (by linarith [(chartBound_bounds hC (hK k) (hH k) n).1] :
      1 ≤ chartBound C (K k) (H k) n)) hchart
    1 (a := 0) (b := 1) (by norm_num) (A := 12) (by norm_num)
  filter_upwards [hsmall, hden] with k hk hd
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hchart2 := (chartBound_bounds hC (hK k) (hH k) n).1
  have hchartp : 0 < chartBound C (K k) (H k) n := by linarith
  have hscale := (errorScale_bounds (C := C) (s := s) hNp (hK k) (hH k)).1
  have hscalep : 0 < errorScale (N k) C (K k) (H k) s :=
    (Real.rpow_pos_of_pos hNp _).trans_le hscale
  have hscale1 : errorScale (N k) C (K k) (H k) s ≤ 1 := by
    simpa only [errorScale, pow_one, one_mul, Real.rpow_zero] using hk.le
  have hdenN : 12 * chartBound C (K k) (H k) n ≤ N k := by
    simpa only [pow_one, Real.rpow_zero, mul_one, Real.rpow_one] using hd.le
  refine ⟨div_pos hscalep (by positivity), ?_, ?_, ?_⟩
  · unfold zoomMesh
    rw [div_le_iff₀ (by positivity : 0 < 12 * chartBound C (K k) (H k) n)]
    nlinarith
  · calc N k ^ (-(s + 1)) = N k ^ (-s) / N k := by
           rw [show -(s + 1) = -s - 1 by ring, Real.rpow_sub hNp, Real.rpow_one]
         _ ≤ N k ^ (-s) / (12 * chartBound C (K k) (H k) n) :=
           div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) (by positivity) hdenN
         _ ≤ zoomMesh (N k) C (K k) (H k) s n :=
           div_le_div_of_nonneg_right hscale (by positivity)
  · unfold zoomMesh
    apply le_of_eq
    field_simp
    ring

end

end Submission.Obl.k4_narrow_projected_row_parents.ComparisonFrame
