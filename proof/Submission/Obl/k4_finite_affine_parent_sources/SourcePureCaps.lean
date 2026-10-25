-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.NativeCaps
import Submission.Obl.k4_finite_affine_parent_sources.SignalMenus
import Submission.Obl.k4_finite_affine_parent_sources.ObservationCoarsening

/-!
# Pure caps of a model from a raw observation ceiling

A model whose observation `obsS b a` (exact base, raw hidden bin of width `a`) has density at
most `D` against `volume × count` gives every cell of `EH2` (base cube of side `ε`, hidden bin
of width `a`) mass at most `D ε³`, for the raw hidden coordinate (`h = false`) and, through the
accepted regular-fiber count (`quadratic_signal_cap`), for a quadratic signal with
`|∂₃ P| ≥ κ⁻¹` (`h = true`, factor `16 (1 + κ²)`).

For a parent-normalised model (`muE` of a `PFrame`), such a ceiling at width `a` follows from an
original raw ceiling on the prepared set at any finer original width `fine ≤ δ a`
(`NativeCaps.muE_observation_cap` after `ObservationCoarsening.observation_cap_coarsen`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- The base cube of a model cell: side `ε`, integer corner `q`. -/
def baseCube (ε : ℝ) (q : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun e => Ico ((q e : ℝ) * ε) ((q e : ℝ) * ε + ε))

theorem measurableSet_baseCube (ε : ℝ) (q : Fin 3 → ℤ) : MeasurableSet (baseCube ε q) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

theorem volume_baseCube {ε : ℝ} (hε : 0 < ε) (q : Fin 3 → ℤ) :
    volume (baseCube ε q) = ENNReal.ofReal (ε ^ 3) := by
  rw [baseCube, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow hε.le]

theorem floor_div_eq_iff_mem {x ε : ℝ} (hε : 0 < ε) (z : ℤ) :
    ⌊x / ε⌋ = z ↔ x ∈ Ico ((z : ℝ) * ε) ((z : ℝ) * ε + ε) := by
  rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hε, div_lt_iff₀ hε]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem zS_eq_iff {α : Type} (b : α → Fin 6 → ℝ) {Nk r : ℝ} (hε : 0 < Nk ^ (-r)) (a : ℝ)
    (p : α × ℝ) (q : Fin 3 → ℤ) :
    zS b Nk r p = q ↔ (obsS b a p).1 ∈ baseCube (Nk ^ (-r)) q := by
  simp only [baseCube, obsS, mem_preimage, WithLp.ofLp_toLp, mem_univ_pi]
  rw [funext_iff]
  refine forall_congr' fun e => ?_
  exact floor_div_eq_iff_mem hε _

theorem measurable_exS {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => exS b p.1 p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i <;> simp [exS] <;> fun_prop

/-- **Raw hidden pure cap** (`h = false`). -/
theorem pure_cap_hidden {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
    {b : α → Fin 6 → ℝ} (hb : Measurable b) {a : ℝ} (D : ENNReal)
    (hcap : μ.map (obsS b a) ≤ D • (volume.prod Measure.count))
    {Nk r : ℝ} (hε : 0 < Nk ^ (-r)) (q : Fin 3 → ℤ) (a₀ : ℤ) :
    μ {p | zS b Nk r p = q ∧ ⌊(exS b p.1 p.2) 3 / a⌋ = a₀} ≤
      D * ENNReal.ofReal ((Nk ^ (-r)) ^ 3) := by
  have hO := measurable_obsS hb a
  have hset : {p | zS b Nk r p = q ∧ ⌊(exS b p.1 p.2) 3 / a⌋ = a₀} =
      obsS b a ⁻¹' (baseCube (Nk ^ (-r)) q ×ˢ {a₀}) := by
    ext p
    simp only [mem_setOf_eq, mem_preimage, mem_prod, mem_singleton_iff,
      zS_eq_iff b hε a p q]
    rfl
  rw [hset]
  calc μ (obsS b a ⁻¹' (baseCube (Nk ^ (-r)) q ×ˢ {a₀}))
      ≤ μ.map (obsS b a) (baseCube (Nk ^ (-r)) q ×ˢ {a₀}) :=
        Measure.le_map_apply hO.aemeasurable _
    _ ≤ (D • (volume.prod Measure.count)) (baseCube (Nk ^ (-r)) q ×ˢ {a₀}) :=
        Measure.le_iff'.1 hcap _
    _ = D * ENNReal.ofReal ((Nk ^ (-r)) ^ 3) := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, volume_baseCube hε,
          Measure.count_singleton, mul_one]

theorem signalObservation_exS {α : Type} (b : α → Fin 6 → ℝ) (a : ℝ) :
    signalObservation (fun p : α × ℝ => exS b p.1 p.2) a = obsS b a := by
  funext p
  apply Prod.ext
  · simp only [signalObservation, obsS]
    congr 1
    funext j
    fin_cases j <;> rfl
  · rfl

/-- **Quadratic signal pure cap** (`h = true`). -/
theorem pure_cap_signal {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
    {b : α → Fin 6 → ℝ} (hb : Measurable b) {a : ℝ} (ha : 0 < a) (D : ENNReal)
    (hcap : μ.map (obsS b a) ≤ D • (volume.prod Measure.count))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {κ : ℝ} (hκ : 1 ≤ κ)
    (hder : ∀ᵐ p ∂μ, κ⁻¹ ≤ |eval (exS b p.1 p.2) (pderiv (3 : Fin 4) P)|)
    {Nk r : ℝ} (hε : 0 < Nk ^ (-r)) (q : Fin 3 → ℤ) (a₀ : ℤ) :
    μ {p | zS b Nk r p = q ∧ ⌊eval (exS b p.1 p.2) P / a⌋ = a₀} ≤
      D * (ENNReal.ofReal ((Nk ^ (-r)) ^ 3) * ENNReal.ofReal (16 * (1 + κ ^ 2))) := by
  have hpt := measurable_exS hb
  have hsig := signalObservation_exS b a
  set c : ℝ := ((a₀ : ℝ) + 1 / 2) * a with hc
  have hP' : (P - C c).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le hP ?_)
    rw [totalDegree_C]
    norm_num
  have hev : Measurable (fun p : α × ℝ => eval (exS b p.1 p.2) P) :=
    (MvPolynomial.continuous_eval P).measurable.comp hpt
  have hE : MeasurableSet {p : α × ℝ | zS b Nk r p = q ∧ ⌊eval (exS b p.1 p.2) P / a⌋ = a₀} := by
    have h1 : {p : α × ℝ | zS b Nk r p = q} =
        obsS b a ⁻¹' (baseCube (Nk ^ (-r)) q ×ˢ univ) := by
      ext p
      simp only [mem_setOf_eq, mem_preimage, mem_prod, mem_univ, and_true,
        zS_eq_iff b hε a p q]
    have h2 : MeasurableSet {p : α × ℝ | ⌊eval (exS b p.1 p.2) P / a⌋ = a₀} :=
      measurableSet_eq_fun (Int.measurable_floor.comp (hev.div_const a)) measurable_const
    have h1m : MeasurableSet {p : α × ℝ | zS b Nk r p = q} := by
      rw [h1]
      exact (measurable_obsS hb a) ((measurableSet_baseCube _ _).prod MeasurableSet.univ)
    exact h1m.inter h2
  have hcap' : μ.map (signalObservation (fun p : α × ℝ => exS b p.1 p.2) a) ≤
      D • (volume.prod Measure.count) := by
    rw [hsig]
    exact hcap
  have hκ0 : 0 < κ := by linarith
  refine (quadratic_signal_cap μ (fun p => exS b p.1 p.2) hpt (P - C c) hP'
    (baseCube (Nk ^ (-r)) q) (measurableSet_baseCube _ _) _ hE a κ D ha hκ0 hcap' ?_ ?_).trans ?_
  · intro p hp
    rw [hsig]
    exact (zS_eq_iff b hε a p q).1 hp.1
  · filter_upwards [hder] with p hp hpE
    have hfl := hpE.2
    rw [floor_div_eq_iff_mem ha] at hfl
    refine ⟨?_, ?_⟩
    · rw [map_sub, eval_C, hc]
      rw [abs_le]
      obtain ⟨h1, h2⟩ := hfl
      constructor <;> nlinarith
    · rwa [map_sub, pderiv_C, sub_zero]
  · rw [volume_baseCube hε]

/-- **Transport of a raw ceiling to a parent-normalised model.** An original raw ceiling on
the prepared set at a width `fine` gives the model ceiling at any model width `a` with
`0 < δ a`. -/
theorem muE_raw_ceiling (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (δ B a : ℝ) (hδ : δ ≠ 0) (hsc : Φ.sc = B / δ) (hδa : 0 < δ * a)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (A₀ : Set (ℕ × (Fin 6 → ℝ)))
    (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) {fine : ℝ} (hfine : 0 < fine) (M : ENNReal)
    (hcap : (((ν.prod volume).restrict S).map (obs B fine)) ≤
      M • (volume.prod Measure.count)) :
    (muE ν A₀ Φ.F.t₀ Φ.F.q S).map (obsS Φ.eb a) ≤
      ((ν A₀)⁻¹ * ENNReal.ofReal |Φ.F.D.det| *
        (ENNReal.ofReal (2 * (δ * a) / fine + 2) * M)) • (volume.prod Measure.count) := by
  have hbase : Measurable (fun z : (ℕ × (Fin 6 → ℝ)) × ℝ => (obs B fine z).1) :=
    measurable_fst.comp (measurable_obs B fine)
  have hval : Measurable (fun z : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      B * graphPoint z.1 z.2 3) := by
    have : Measurable (fun z : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        graphPoint z.1 z.2 3) := by
      simp only [graphPoint]
      fun_prop
    exact this.const_mul B
  have hcoarse := observation_cap_coarsen ((ν.prod volume).restrict S)
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (fun z => (obs B fine z).1)
    (fun z => B * graphPoint z.1 z.2 3)
    hbase hval hfine hδa M hcap
  exact Φ.muE_observation_cap hq hD δ B a hδ hsc ν A₀ S _ hcoarse

end

end Submission.Obl.k4_finite_affine_parent_sources
