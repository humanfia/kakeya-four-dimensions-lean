import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSlices
import Submission.Obl.k4_general_wide_layer_offset_comparison.SourceResolution
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparisonBandCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The actual original code places every source in one physical moving
box, independently of which projected label will be queried. -/
theorem comparisonCode_movingBox {k : ℕ} {m h g b : ℝ}
    (hN : 0 < p.N k) (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g ≤ b)
    {ω : α × ℝ} (hω : ω ∈ p.baseGood k) (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ)
    (hc : p.comparisonCode k m h g b ω = (tag, D)) :
    ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
      Submission.Lib.K4MovingMeshBoxes.movingBox (domainTime h D) h
        ![(tag 1 : ℝ) * p.N k ^ (-m), domainIntercept h g b D]
        ![(tag 0 : ℝ) * p.N k ^ (-m), domainVelocity g D]
        ![2 * p.N k ^ (-m), 2 * b] := by
  have hdomain : p.domainCode k h g b ω = D := congrArg Prod.snd hc
  have hz : ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1 := congrArg (fun c => c.1 1) hc
  have hv : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0 := congrArg (fun c => c.1 0) hc
  obtain ⟨ht, hy⟩ := moving_domain_geometry hh hg hb (p.b k ω.1 1) (p.b k ω.1 4) ω.2
  change |ω.2 - ((p.domainCode k h g b ω).1 : ℝ) * h| ≤ h at ht
  change |(p.x k ω.1 ω.2) 2 -
    (((p.domainCode k h g b ω).2.2 : ℝ) * b +
      (ω.2 - ((p.domainCode k h g b ω).1 : ℝ) * h) *
        (((p.domainCode k h g b ω).2.1 : ℝ) * g))| ≤ b + h * g at hy
  rw [hdomain] at ht hy
  refine ⟨ht, ?_⟩
  intro i
  fin_cases i
  · exact intercept_velocity_bin_tube (Real.rpow_pos_of_pos hN _) hz hv hω.1
  · change |(p.x k ω.1 ω.2) 2 - (domainIntercept h g b D + ω.2 * domainVelocity g D)| ≤ 2 * b
    convert hy.trans (by linarith : b + h * g ≤ 2 * b) using 1 <;>
      dsimp [domainIntercept, domainTime, domainVelocity] <;> congr 1 <;> ring

/-- A whole original-code band. The query polynomial can come from either
color; no surviving individual pair mass enters its definition. -/
def comparisonBand (k : ℕ) (m h g b : ℝ) (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ)
    (G : MvPolynomial (Fin 2) ℝ) (Δ : ℝ) : Set (α × ℝ) :=
  {ω | ω ∈ p.baseGood k ∧ p.comparisonCode k m h g b ω = (tag, D) ∧
    |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2] G| ≤ Δ}

theorem measurableSet_comparisonBand (hbase : p.Basic) (k : ℕ) (m h g b : ℝ)
    (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ) (G : MvPolynomial (Fin 2) ℝ) (Δ : ℝ) :
    MeasurableSet (p.comparisonBand k m h g b tag D G Δ) := by
  have hb' := (hbase k).1
  have hsignal : Measurable (fun ω : α × ℝ => eval (p.x k ω.1 ω.2) (p.P k)) := by
    apply (MvPolynomial.continuous_eval _).measurable.comp
    unfold Submission.Obl.k4_critical_intercept_concentration.Data.x
    fun_prop
  have hpredictor : Measurable (fun ω : α × ℝ => eval ![ω.2, (p.x k ω.1 ω.2) 2] G) := by
    apply (MvPolynomial.continuous_eval _).measurable.comp
    unfold Submission.Obl.k4_critical_intercept_concentration.Data.x
    fun_prop
  exact (Basic.measurableSet_baseGood p hbase k).inter
    ((measurableSet_eq_fun (p.measurable_comparisonCode hbase k m h g b) measurable_const).inter
      (measurableSet_le (hsignal.sub hpredictor).abs measurable_const))

/-- Native primitive caps bound the entire original-code band at every
real thickness above the fixed resolution. This is the whole-law ceiling
needed by multiscale discrepancy matching. -/
theorem comparisonBand_cap (hbase : p.Basic)
    {k : ℕ} {m h g b r smax Δ B V : ℝ}
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d) (hsmax : 0 ≤ smax)
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    (hmove : h * g ≤ b) (hV : 0 ≤ V)
    (hdtime : p.N k ^ (-r) ≤ h)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m)) (hdb : p.N k ^ (-r) ≤ 2 * b)
    (hmχ : V * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hmb : V * p.N k ^ (-r) ≤ 2 * b)
    (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ)
    (hv₀ : |(tag 0 : ℝ) * p.N k ^ (-m)| ≤ V) (hv : |domainVelocity g D| ≤ V)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (hcoeff : ∀ e, |G.coeff e| ≤ B)
    (hresolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-smax))
    (hΔ : 0 < Δ) (hmin : p.N k ^ (-smax) ≤ Δ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ smax → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁}) :
    σ (p.comparisonBand k m h g b tag D G Δ) ≤
      ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * Δ ^ p.d) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = tag 0} := by
  have hc := p.native_band_box_cap hbase hN hK hd hsmax hΔ hmin hdtime hV
    (domainTime h D) ![(tag 1 : ℝ) * p.N k ^ (-m), domainIntercept h g b D]
    ![(tag 0 : ℝ) * p.N k ^ (-m), domainVelocity g D] ![2 * p.N k ^ (-m), 2 * b]
    (by intro i; fin_cases i; exact hv₀; exact hv)
    (by intro i; fin_cases i; exact hdχ; exact hdb)
    (by intro i; fin_cases i; exact hmχ; exact hmb)
    (tag 0) (fun x => eval ![x 0, x 2] G) σ hσ
    (p.comparisonBand k m h g b tag D G Δ)
    (fun ω hω => p.comparisonCode_movingBox (zero_lt_one.trans hN) hh hg hb hmove hω.1 tag D hω.2.1)
    (fun _ hω => congrArg (fun c => c.1 0) hω.2.1)
    (fun _ hω => hω.2.2)
    (fun ω hω y hy => p.projected_variation_on_good hN.le hK hr hB G hG hcoeff
      hresolution hω.1 y hy) hcap
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  convert hc using 1 <;> congr 2 <;> ring

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
