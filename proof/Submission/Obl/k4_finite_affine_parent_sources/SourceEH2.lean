-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourcePureCaps

/-!
# `EH2` from raw observation ceilings

`EH2` of a model index reduces to three inputs:
* the palette bins;
* at every hidden scale `s`, a raw ceiling `D s` of the model's observation `obsS b (N^-s)`;
* at every hidden scale `s` and velocity bin, a raw ceiling of the model restricted to that
  velocity bin (the conditional raw ceiling).
Both observables (`h = false`: the raw hidden coordinate; `h = true`: the quadratic test) are
then capped cell by cell (`pure_cap_hidden`, `pure_cap_signal`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial

noncomputable section

/-- The velocity bin event of a model. -/
def velBin {α : Type} (b : α → Fin 6 → ℝ) (w : ℝ) (v₀ : ℤ) : Set (α × ℝ) :=
  {p | ⌊b p.1 3 / w⌋ = v₀}

theorem measurableSet_velBin {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (w : ℝ) (v₀ : ℤ) : MeasurableSet (velBin b w v₀) :=
  measurableSet_eq_fun (Int.measurable_floor.comp
    ((((measurable_pi_apply 3).comp hb).comp measurable_fst).div_const w)) measurable_const

/-- A cell of `EH2`, either observable, from a raw ceiling. -/
theorem cell_cap_of_ceiling {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {κ : ℝ} (hκ : 1 ≤ κ)
    (hder : ∀ᵐ p ∂μ, κ⁻¹ ≤ |eval (exS b p.1 p.2) (pderiv (3 : Fin 4) P)|)
    {a : ℝ} (ha : 0 < a) (D : ENNReal)
    (hceil : μ.map (obsS b a) ≤ D • (volume.prod Measure.count))
    {Nk r : ℝ} (hε : 0 < Nk ^ (-r)) (h : Bool) (q : Fin 3 → ℤ) (a₀ : ℤ) :
    μ {p | zS b Nk r p = q ∧
        ⌊(if h then eval (exS b p.1 p.2) P else (exS b p.1 p.2) 3) / a⌋ = a₀} ≤
      D * (ENNReal.ofReal ((Nk ^ (-r)) ^ 3) * ENNReal.ofReal (16 * (1 + κ ^ 2))) := by
  cases h
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine (pure_cap_hidden μ hb D hceil hε q a₀).trans ?_
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (16 * (1 + κ ^ 2)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc D * ENNReal.ofReal ((Nk ^ (-r)) ^ 3)
        = D * (ENNReal.ofReal ((Nk ^ (-r)) ^ 3) * 1) := by rw [mul_one]
      _ ≤ D * (ENNReal.ofReal ((Nk ^ (-r)) ^ 3) * ENNReal.ofReal (16 * (1 + κ ^ 2))) := by
          gcongr
  · simp only [↓reduceIte]
    exact pure_cap_signal μ hb ha D hceil P hP hκ hder hε q a₀

/-- **`EH2` from palette bins, raw ceilings and velocity-restricted raw ceilings.** -/
theorem eh2_of_ceilings {α : Type} [MeasurableSpace α] (d S : ℝ) (st : EStage α) (R : ℝ)
    (hb : Measurable st.b) (hN : 0 < st.N) (hP : st.P.totalDegree ≤ 2) {κ : ℝ} (hκ : 1 ≤ κ)
    (hder : ∀ᵐ p ∂st.μ, κ⁻¹ ≤ |eval (exS st.b p.1 p.2) (pderiv (3 : Fin 4) st.P)|)
    (hpal : ∀ v : ℝ, R⁻¹ ≤ v → v ≤ R → ∀ a : ℤ,
      st.π {w : ℝ | ⌊w / (st.N ^ (-v))⌋ = a} ≤ ENNReal.ofReal (st.K * st.N ^ (-S * v)))
    (Dp : ℝ → ENNReal)
    (hpure : ∀ s : ℝ, 0 ≤ s → s ≤ R →
      st.μ.map (obsS st.b (st.N ^ (-s))) ≤ Dp s • (volume.prod Measure.count))
    (hDp : ∀ r s : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      Dp s * (ENNReal.ofReal ((st.N ^ (-r)) ^ 3) * ENNReal.ofReal (16 * (1 + κ ^ 2))) ≤
        ENNReal.ofReal (st.K * st.N ^ (-3 * r - d * s)))
    (Dj : ℝ → ℝ → ℤ → ENNReal)
    (hjoint : ∀ s v : ℝ, 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → ∀ v₀ : ℤ,
      (st.μ.restrict (velBin st.b (st.N ^ (-v)) v₀)).map (obsS st.b (st.N ^ (-s))) ≤
        Dj s v v₀ • (volume.prod Measure.count))
    (hDj : ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → ∀ v₀ : ℤ,
      Dj s v v₀ * (ENNReal.ofReal ((st.N ^ (-r)) ^ 3) * ENNReal.ofReal (16 * (1 + κ ^ 2))) ≤
        ENNReal.ofReal (st.K * st.N ^ (-3 * r - d * s)) *
          st.π {w : ℝ | ⌊w / (st.N ^ (-v))⌋ = v₀}) :
    EH2 d S st R := by
  intro r s v hr1 hr2 hs1 hs2 hv1 hv2
  have hε : 0 < st.N ^ (-r) := Real.rpow_pos_of_pos hN _
  have ha : 0 < st.N ^ (-s) := Real.rpow_pos_of_pos hN _
  refine ⟨hpal v hv1 hv2, ?_, ?_⟩
  · intro h q a
    exact (cell_cap_of_ceiling st.μ hb st.P hP hκ hder ha (Dp s) (hpure s hs1 hs2) hε h q a).trans
      (hDp r s hr1 hr2 hs1 hs2)
  · intro h q a v₀
    have hV := measurableSet_velBin hb (st.N ^ (-v)) v₀
    have hset : {p | zS st.b st.N r p = q ∧
        ⌊(if h then eval (exS st.b p.1 p.2) st.P else (exS st.b p.1 p.2) 3) /
          (st.N ^ (-s))⌋ = a ∧ ⌊st.b p.1 3 / (st.N ^ (-v))⌋ = v₀} =
        {p | zS st.b st.N r p = q ∧
          ⌊(if h then eval (exS st.b p.1 p.2) st.P else (exS st.b p.1 p.2) 3) /
            (st.N ^ (-s))⌋ = a} ∩ velBin st.b (st.N ^ (-v)) v₀ := by
      ext p
      simp only [mem_setOf_eq, mem_inter_iff, velBin, and_assoc]
    rw [hset, ← Measure.restrict_apply' hV]
    exact (cell_cap_of_ceiling (st.μ.restrict (velBin st.b (st.N ^ (-v)) v₀)) hb st.P hP hκ
      (ae_restrict_of_ae hder) ha (Dj s v v₀) (hjoint s v hs1 hs2 hv1 hv2 v₀) hε h q a).trans
      (hDj r s v hr1 hr2 hs1 hs2 hv1 hv2 v₀)

end

end Submission.Obl.k4_finite_affine_parent_sources
