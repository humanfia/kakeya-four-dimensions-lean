import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartFacts
import Submission.Obl.k4_crop_angular_finite_tail.Transfer

/-!
# Weighted density tails of a normalized family through its Refinement certificate

At every index `k` of `q`, with `Z` the Refinement normalizer and `λ_i = J_i / ν(A_i)`:

* `RefData.weighted_upper`: the weighted `q`-mass where the depth-`s` density exceeds
  `λ_i 4 θ'` is at most `8 Z⁻¹` times the weighted `p`-mass at index `φ k` where the
  depth-`(r+s)` density exceeds `θ'`;
* `RefData.weighted_lower`: for `r + s ≥ b`, the weighted `q`-mass where the depth-`s`
  density is below `λ_i ε' δ X` is at most `Z⁻¹ (4 ε' + 2 N^ε δ + 2 ⋯)`, the last term being the
  weighted `p`-mass where the depth-`(r+s)` density is below `X`;
* `RefData.weighted_angular`: the analogue of the upper estimate for joint densities.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

/-- Weighted sums over labels regroup by their original world. -/
lemma sum_by_world {n m : ℕ} (γ : Fin n → Fin m) (w : Fin m → ℝ≥0∞) (F : Fin n → ℝ≥0∞)
    (G : Fin m → ℝ≥0∞) (hF : ∀ a, ∑ i ∈ Finset.univ.filter (fun i => γ i = a), F i ≤ G a) :
    ∑ i, w (γ i) * F i ≤ ∑ a, w a * G a := by
  rw [← Finset.sum_fiberwise Finset.univ γ (fun i => w (γ i) * F i)]
  apply Finset.sum_le_sum
  intro a _
  calc ∑ i ∈ Finset.univ.filter (fun i => γ i = a), w (γ i) * F i
      = ∑ i ∈ Finset.univ.filter (fun i => γ i = a), w a * F i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
    _ = w a * ∑ i ∈ Finset.univ.filter (fun i => γ i = a), F i := by rw [Finset.mul_sum]
    _ ≤ w a * G a := by gcongr; exact hF a

variable {p q : Code} {r b h : ℝ}

/-- Selected world laws have mass at most one. -/
lemma mu_univ_le_one (hp : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) : p.mu k a univ ≤ 1 := by
  have := RawScalar.ν_prob hp k a
  calc p.mu k a univ = ((p.ν k a).prod volume) (p.E k a) := by
        rw [Measure.restrict_apply_univ]
    _ ≤ ((p.ν k a).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
        measure_mono (RawScalar.E_time hp k a)
    _ = 1 := by
        rw [Measure.prod_prod, measure_univ, Real.volume_Icc, one_mul]
        simp

lemma mu_isFinite (hp : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    IsFiniteMeasure (p.mu k a) :=
  ⟨(mu_univ_le_one hp k a).trans_lt ENNReal.one_lt_top⟩

namespace RefData

variable (R : RefData p q r b h)

/-- Block length. -/
def dt (k : ℕ) : ℝ := ((2 : ℝ) ^ R.T k)⁻¹
/-- Block start. -/
def t0 (k : ℕ) (i : Fin (q.1 k)) : ℝ := (((R.j k i : Fin (2 ^ R.T k)) : ℕ) : ℝ) * R.dt k
/-- Assigned prior mass. -/
def νA (k : ℕ) (i : Fin (q.1 k)) : ℝ≥0∞ := p.ν (R.φ k) (R.γ k i) (R.A k i)
/-- Normalization of a selected law. -/
def c (k : ℕ) (i : Fin (q.1 k)) : ℝ≥0∞ := (ENNReal.ofReal (R.dt k) * R.νA k i)⁻¹
/-- The Refinement normalizer. -/
def Z (k : ℕ) : ℝ := ∑ i : Fin (q.1 k), p.ω (R.φ k) (R.γ k i) * R.dt k * (R.νA k i).toReal
/-- The density factor `J / ν(A)` of a label. -/
def lam (k : ℕ) (i : Fin (q.1 k)) : ℝ := R.J k i / (R.νA k i).toReal

lemma dt_pos (k : ℕ) : 0 < R.dt k := by unfold dt; positivity

lemma Z_pos' (k : ℕ) : 0 < R.Z k := R.Z_pos k

lemma J_pos (k : ℕ) (i : Fin (q.1 k)) : 0 < R.J k i := ChartData.J_pos (R.chart k) i

lemma νA_ne_top (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (q.1 k)) : R.νA k i ≠ ∞ := by
  have := RawScalar.ν_prob hp (R.φ k) (R.γ k i)
  exact measure_ne_top _ _

lemma νA_ne_zero (k : ℕ) (i : Fin (q.1 k)) : R.νA k i ≠ 0 := by
  intro h0
  have hle := ChartData.mu_le (R.chart k) i univ
  have hpos := ChartData.mu_pos (R.chart k) i
  rw [inter_univ] at hle
  have h0' : p.ν (R.φ k) (R.γ k i) (R.A k i) = 0 := h0
  rw [h0', zero_mul] at hle
  exact (lt_irrefl (0 : ℝ≥0∞)) (hpos.trans_le hle)

lemma c_ne_zero (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (q.1 k)) : R.c k i ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.νA_ne_top hp k i))

lemma c_ne_top (k : ℕ) (i : Fin (q.1 k)) : R.c k i ≠ ∞ :=
  ENNReal.inv_ne_top.mpr (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (R.dt_pos k))
    (R.νA_ne_zero k i))

lemma mu_eq' (k : ℕ) (i : Fin (q.1 k)) :
    q.mu k i = R.c k i • ((p.mu (R.φ k) (R.γ k i)).restrict (R.C k i)).map
      (normInc (R.t0 k i) (R.dt k) (R.θ k i)) := R.mu_eq k i

lemma θ_y' (k : ℕ) (i : Fin (q.1 k)) : ∀ l t, Spec.y (R.θ k i l) ((t - R.t0 k i) / R.dt k) =
    (Spec.y l t - R.u k i - t * R.v k i) / R.J k i := R.θ_y k i

lemma θ_x' (k : ℕ) (i : Fin (q.1 k)) : ∀ l t, Spec.x (R.θ k i l) ((t - R.t0 k i) / R.dt k) =
    (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] (R.P k i)) / p.N (R.φ k) ^ (-r) :=
  R.θ_x k i

lemma qN_eq (k : ℕ) : q.N k = p.N (R.φ k) := R.N_eq k

/-- Weights times normalizations are the original weights over `Z`. -/
lemma weight_mul_c (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (q.1 k)) :
    ENNReal.ofReal (q.ω k i) * R.c k i =
      ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * ENNReal.ofReal (R.Z k)⁻¹ := by
  have hω : q.ω k i = p.ω (R.φ k) (R.γ k i) * R.dt k * (R.νA k i).toReal / R.Z k := R.ω_eq k i
  have hω0 := RawScalar.ω_nonneg hp (R.φ k) (R.γ k i)
  have hdt := R.dt_pos k
  have hZ := R.Z_pos' k
  have hA0 := R.νA_ne_zero k i
  have hAT := R.νA_ne_top hp k i
  rw [hω, c, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hω0, ENNReal.ofReal_toReal hAT]
  have hdt0 : ENNReal.ofReal (R.dt k) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdt
  have hcancel : ENNReal.ofReal (R.dt k) * R.νA k i * (ENNReal.ofReal (R.dt k) * R.νA k i)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (mul_ne_zero hdt0 hA0) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAT)
  calc ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * ENNReal.ofReal (R.dt k) * R.νA k i *
        ENNReal.ofReal (R.Z k)⁻¹ * (ENNReal.ofReal (R.dt k) * R.νA k i)⁻¹
      = ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * ENNReal.ofReal (R.Z k)⁻¹ *
          (ENNReal.ofReal (R.dt k) * R.νA k i * (ENNReal.ofReal (R.dt k) * R.νA k i)⁻¹) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The density factor of a label. -/
lemma c_mul_dtJ (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (q.1 k)) :
    R.c k i * ENNReal.ofReal (R.dt k * R.J k i) = ENNReal.ofReal (R.lam k i) := by
  have hdt := R.dt_pos k
  have hJ := R.J_pos k i
  have hA0 := R.νA_ne_zero k i
  have hAT := R.νA_ne_top hp k i
  have hdt0 : ENNReal.ofReal (R.dt k) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdt
  rw [c, lam, ENNReal.ofReal_mul hdt.le, ENNReal.mul_inv (Or.inr hAT) (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hA0 hAT), ENNReal.ofReal_toReal hAT]
  calc (ENNReal.ofReal (R.dt k))⁻¹ * (R.νA k i)⁻¹ * (ENNReal.ofReal (R.dt k) * ENNReal.ofReal (R.J k i))
      = ((ENNReal.ofReal (R.dt k))⁻¹ * ENNReal.ofReal (R.dt k)) *
          (ENNReal.ofReal (R.J k i) * (R.νA k i)⁻¹) := by ring
    _ = ENNReal.ofReal (R.J k i) / R.νA k i := by
        rw [ENNReal.inv_mul_cancel hdt0 ENNReal.ofReal_ne_top, one_mul, div_eq_mul_inv]

lemma lam_pos (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (q.1 k)) : 0 < R.lam k i :=
  div_pos (R.J_pos k i) (ENNReal.toReal_pos (R.νA_ne_zero k i) (R.νA_ne_top hp k i))

/-- The normalizer is at least the chart's retained mass. -/
lemma Z_ge (hp : Spec.RawScalar p) (k : ℕ) : p.N (R.φ k) ^ (-R.ε k) ≤ R.Z k := by
  classical
  have hmass := ChartData.mass (R.chart k)
  have hdt := R.dt_pos k
  have hsum : ∑ a : Fin (p.1 (R.φ k)), ENNReal.ofReal (p.ω (R.φ k) a) *
      p.mu (R.φ k) a {z | ∃ i, R.γ k i = a ∧ z ∈ R.C k i} ≤ ENNReal.ofReal (R.Z k) := by
    have hle : ∀ a, p.mu (R.φ k) a {z | ∃ i, R.γ k i = a ∧ z ∈ R.C k i} ≤
        ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), R.νA k i * ENNReal.ofReal (R.dt k) := by
      intro a
      calc p.mu (R.φ k) a {z | ∃ i, R.γ k i = a ∧ z ∈ R.C k i}
          ≤ p.mu (R.φ k) a (⋃ i ∈ Finset.univ.filter (fun i => R.γ k i = a), R.C k i) := by
            apply measure_mono
            rintro z ⟨i, hi, hz⟩
            exact mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) hz
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), p.mu (R.φ k) a (R.C k i) :=
            measure_biUnion_finset_le _ _
        _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            have hγ := (Finset.mem_filter.mp hi).2
            have := ChartData.mu_le (R.chart k) i univ
            rw [inter_univ] at this
            rw [← hγ]
            exact this
    calc ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
          p.mu (R.φ k) a {z | ∃ i, R.γ k i = a ∧ z ∈ R.C k i}
        ≤ ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
          ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), R.νA k i * ENNReal.ofReal (R.dt k) := by
          gcongr with a
          exact hle a
      _ = ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * (R.νA k i * ENNReal.ofReal (R.dt k)) := by
          rw [← Finset.sum_fiberwise Finset.univ (R.γ k)
            (fun i => ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * (R.νA k i * ENNReal.ofReal (R.dt k)))]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
      _ = ENNReal.ofReal (R.Z k) := by
          rw [Z, ENNReal.ofReal_sum_of_nonneg (fun i _ => by
            have := RawScalar.ω_nonneg hp (R.φ k) (R.γ k i)
            have := R.dt_pos k
            positivity)]
          apply Finset.sum_congr rfl
          intro i _
          have hω0 := RawScalar.ω_nonneg hp (R.φ k) (R.γ k i)
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hω0,
            ENNReal.ofReal_toReal (R.νA_ne_top hp k i)]
          ring
  have := hmass.trans hsum
  exact (ENNReal.ofReal_le_ofReal_iff (R.Z_pos' k).le).mp this

end RefData

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
