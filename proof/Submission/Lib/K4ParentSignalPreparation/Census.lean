/-
Adapted from: here:o265
Original proofs by x1027.
-/
import Mathlib

/-!
# Changing the height unit of the parent signal

The physical source uses height `P/a`; the velocity-row model can use `P/h`.
The exact change of bins preserves the joint census with a factor `(a/h)^d`.
There is no inverse power of this ratio in the count. All mesh floors and the
upper height range remain explicit.
-/

namespace Submission.Lib.K4ParentSignalPreparation.Census

open Set

noncomputable section

variable {Ω : Type*} {n : ℕ}

def gridCode (z : Ω → Fin n → ℝ) (X : Ω → ℝ) (p w : ℝ) (x : Ω) :
    (Fin n → ℤ) × ℤ := (fun i => ⌊z x i / p⌋, ⌊X x / w⌋)

def occupied (E : Set Ω) (z : Ω → Fin n → ℝ) (X : Ω → ℝ) (p w : ℝ) :
    Set ((Fin n → ℤ) × ℤ) := {k | ∃ x ∈ E, gridCode z X p w x = k}

lemma gridCode_scale (z : Ω → Fin n → ℝ) (X : Ω → ℝ) {θ w : ℝ}
    (hθ : 0 < θ) (hw : 0 < w) (p : ℝ) (x : Ω) :
    gridCode z (fun x => θ * X x) p w x = gridCode z X p (w / θ) x := by
  unfold gridCode
  congr 1
  congr 1
  field_simp

lemma occupied_scale (E : Set Ω) (z : Ω → Fin n → ℝ) (X : Ω → ℝ) {θ w : ℝ}
    (hθ : 0 < θ) (hw : 0 < w) (p : ℝ) :
    occupied E z (fun x => θ * X x) p w = occupied E z X p (w / θ) := by
  simp only [occupied, gridCode_scale z X hθ hw p]

/-- The joint census transfers to the rescaled signal on the exact admissible height
range. The base mesh floor stays `epsilon`, while the height floor becomes `theta*epsilon`. -/
theorem rescale_census (E : Set Ω) (z : Ω → Fin n → ℝ) (X : Ω → ℝ)
    {ε θ K d : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K ^ (100 : ℕ) * p ≤ θ * w →
      (occupied E z X p w).Finite ∧
      ((occupied E z X p w).ncard : ℝ) ≤ K / (p ^ n * w ^ d))
    {p w : ℝ} (hp : ε ≤ p) (hp1 : p ≤ 1) (hw : θ * ε ≤ w) (hwθ : w ≤ θ)
    (hmesh : K ^ (100 : ℕ) * p ≤ w) :
    (occupied E z (fun x => θ * X x) p w).Finite ∧
      ((occupied E z (fun x => θ * X x) p w).ncard : ℝ) ≤
        K * θ ^ d / (p ^ n * w ^ d) := by
  have hp0 : 0 < p := hε.trans_le hp
  have hw0 : 0 < w := (mul_pos hθ hε).trans_le hw
  have hwFloor : ε ≤ w / θ := (le_div_iff₀ hθ).mpr (by nlinarith)
  have hwUpper : w / θ ≤ 1 := (div_le_one hθ).mpr hwθ
  have hcondition : K ^ (100 : ℕ) * p ≤ θ * (w / θ) := by
    simpa only [mul_div_cancel₀ _ hθ.ne'] using hmesh
  obtain ⟨hfinite, hcount⟩ := hcensus p (w / θ) hp hp1 hwFloor hwUpper hcondition
  rw [occupied_scale E z X hθ hw0 p]
  refine ⟨hfinite, hcount.trans_eq ?_⟩
  rw [Real.div_rpow hw0.le hθ.le]
  have hwd : 0 < w ^ d := Real.rpow_pos_of_pos hw0 _
  have hθd : 0 < θ ^ d := Real.rpow_pos_of_pos hθ _
  field_simp

/-- A bounded height conversion costs at most one further envelope factor for dimensions
between zero and one. In particular a conversion at most one has no extra count loss. -/
theorem rescale_census_envelope (E : Set Ω) (z : Ω → Fin n → ℝ) (X : Ω → ℝ)
    {ε θ K d : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hK : 1 ≤ K)
    (hθK : θ ≤ K) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K ^ (100 : ℕ) * p ≤ θ * w →
      (occupied E z X p w).Finite ∧
      ((occupied E z X p w).ncard : ℝ) ≤ K / (p ^ n * w ^ d))
    {p w : ℝ} (hp : ε ≤ p) (hp1 : p ≤ 1) (hw : θ * ε ≤ w) (hwθ : w ≤ θ)
    (hmesh : K ^ (100 : ℕ) * p ≤ w) :
    (occupied E z (fun x => θ * X x) p w).Finite ∧
      ((occupied E z (fun x => θ * X x) p w).ncard : ℝ) ≤
        K ^ (2 : ℕ) / (p ^ n * w ^ d) := by
  obtain ⟨hfinite, hcount⟩ := rescale_census E z X hε hθ hcensus hp hp1 hw hwθ hmesh
  have hθd : θ ^ d ≤ K := by
    by_cases hθ1 : θ ≤ 1
    · exact (Real.rpow_le_one hθ.le hθ1 hd0).trans hK
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hθ1) hd1).trans hθK
  have hp0 : 0 < p := hε.trans_le hp
  have hw0 : 0 < w := (mul_pos hθ hε).trans_le hw
  refine ⟨hfinite, hcount.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hθd (zero_le_one.trans hK)]

/-- In physical units the changed height bin has width `h*w/a`. -/
theorem parent_time_gridCode (z : Ω → Fin n → ℝ) (P : Ω → ℝ)
    {a h w : ℝ} (ha : 0 < a) (hh : 0 < h) (hw : 0 < w) (p : ℝ) (x : Ω) :
    gridCode z (fun x => P x / h) p w x =
      gridCode z (fun x => P x / a) p (h * w / a) x := by
  unfold gridCode
  congr 1
  congr 1
  field_simp

end

end Submission.Lib.K4ParentSignalPreparation.Census
