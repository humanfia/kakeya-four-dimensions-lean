import Submission.Obl.k4_crop_base_finite_tail.FiniteTail
import Submission.Obl.k4_crop_base_finite_tail.BaseTransport
import Submission.Obl.k4_crop_base_finite_tail.Geometry

namespace Submission.Obl.k4_crop_base_finite_tail.Assembly

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws

/-- The crop argument only needs the positivity of the scale; the restrictions
on the dyadic parameters in the frozen statement are therefore unnecessary here. -/
theorem base_tail (N : ℕ → ℝ) (k : ℕ) (r u : ℝ)
    (ν₀ : Measure Line) (hprob : IsProbabilityMeasure ν₀) (E₀ : Set Inc)
    (hE₀ : MeasurableSet E₀) (htime : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (w : ℕ) (p : Fin w → ℝ) (q : Fin w → Fin 4 → ℤ)
    (ν : Fin w → Measure Line) (E : Fin w → Set Inc)
    (g : Fin w → Base → ENNReal) (H : Joint → ENNReal)
    (hq : Function.Injective q)
    (hcrop : ∀ γ, 0 < p γ ∧
      ν γ = (ENNReal.ofReal (p γ))⁻¹ •
        (ν₀.restrict (Cell (Scale N k u) (q γ))).map (Crop (Scale N k u) (q γ)) ∧
      E γ = CropInc (Scale N k u) (q γ) '' (E₀ ∩ (Cell (Scale N k u) (q γ) ×ˢ univ)))
    (hH : Measurable H)
    (hHlaw : (Selected ν₀ E₀).map (JointObs N k r u) = JointRef.withDensity H)
    (hg : ∀ γ, Measurable (g γ) ∧
      (Selected (ν γ) (E γ)).map (Obs N k r) = BaseRef.withDensity (g γ))
    (lo hi δ : ℝ) (_hlo : 0 < lo) (hhi : 0 < hi) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (∑ γ, ENNReal.ofReal (p γ) *
      Selected (ν γ) (E γ)
        {x | g γ (Obs N k r x) < ENNReal.ofReal ((Scale N k u ^ 2 / p γ) * δ * lo) ∨
          ENNReal.ofReal ((Scale N k u ^ 2 / p γ) * hi / δ) < g γ (Obs N k r x)}) ≤
      Selected ν₀ E₀ {x | H (JointObs N k r u x) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (JointObs N k r u x)} + ENNReal.ofReal (32 * δ) := by
  classical
  letI : IsProbabilityMeasure ν₀ := hprob
  let a := Scale N k u
  have ha : 0 < a := scale_pos N k u
  let μ := Selected ν₀ E₀
  let S : Fin w → Set Inc := fun γ => Cell a (q γ) ×ˢ univ
  let Q := JointObs N k r u
  let v : Fin w → Fin 2 → ℤ := fun γ j => q γ (j.natAdd 2)
  let raw : Fin w → Base → ENNReal := fun γ z =>
    (ENNReal.ofReal (p γ) / ENNReal.ofReal (a^2)) *
      g γ (BaseTransport.obsEquiv a ha (q γ) z)
  let D : Fin w → Joint → ENNReal := fun γ =>
    {z | z.2 = v γ}.indicator (fun z => raw γ z.1)
  let C : Fin w → Set Joint := fun γ => Geometry.compatibleCrop a (q γ)
  let : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
  let : SigmaFinite JointRef := by unfold JointRef; infer_instance
  have hS (γ : Fin w) : MeasurableSet (S γ) :=
    (measurableSet_Cell _ _).prod MeasurableSet.univ
  have hQ : Measurable Q := measurable_JointObs N k r u
  have hraw (γ : Fin w) : Measurable (raw γ) :=
    measurable_const.mul ((hg γ).1.comp (BaseTransport.obsEquiv a ha (q γ)).measurable)
  have hD (γ : Fin w) : Measurable (D γ) :=
    ((hraw γ).comp measurable_fst).indicator
      (measurableSet_eq_fun measurable_snd measurable_const)
  have hconst (γ : Fin w) : ∀ᵐ x ∂μ.restrict (S γ), (Q x).2 = v γ := by
    filter_upwards [ae_restrict_mem (hS γ)] with x hx
    funext j
    fin_cases j
    · simpa [Q, JointObs, v] using hx.1.2.2.1
    · simpa [Q, JointObs, v] using hx.1.2.2.2
  have hrawlaw (γ : Fin w) :
      (μ.restrict (S γ)).map (Obs N k r) = BaseRef.withDensity (raw γ) := by
    have htrans : Selected (ν γ) (E γ) =
        (ENNReal.ofReal (p γ))⁻¹ • (μ.restrict (S γ)).map
          (BaseTransport.stateEquiv a ha (q γ)) := by
      rw [(hcrop γ).2.1, (hcrop γ).2.2]
      exact BaseTransport.selected_transport a ha (q γ) ν₀ E₀ _
    apply BaseTransport.raw_density_law a ha (q γ) N k r (p γ) (hcrop γ).1
      (μ.restrict (S γ)) (g γ) (hg γ).1
    rw [← htrans]
    exact (hg γ).2
  have hDlaw (γ : Fin w) : (μ.restrict (S γ)).map Q = JointRef.withDensity (D γ) := by
    exact map_pair_const_label BaseRef (measurable_Obs N k r) (v γ)
      (hconst γ) (hraw γ) (hrawlaw γ)
  have hDeval (γ : Fin w) :
      ∀ᵐ x ∂μ.restrict (S γ), D γ (Q x) = raw γ (Obs N k r x) := by
    filter_upwards [hconst γ] with x hx
    change ({z : Joint | z.2 = v γ}.indicator (fun z => raw γ z.1)) (Q x) = _
    exact Set.indicator_of_mem (s := {z : Joint | z.2 = v γ}) (a := Q x) hx _
  have hsupp (γ : Fin w) : ∀ᵐ x ∂μ.restrict (S γ), Q x ∈ C γ := by
    have he : ∀ᵐ x ∂μ, x ∈ E₀ := ae_restrict_mem hE₀
    filter_upwards [ae_restrict_mem (hS γ), ae_restrict_of_ae he] with x hx hxe
    exact Geometry.cell_jointObs_compatible ha N k r u rfl hx.1 (htime hxe).2
  have hdisj : Pairwise fun γ γ' => Disjoint (S γ) (S γ') := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp (Geometry.cell_disjoint a (hq.ne hne)) hx.1 hx'.1
  have hleft (γ : Fin w) :
      ENNReal.ofReal (p γ) * Selected (ν γ) (E γ)
        {x | g γ (Obs N k r x) < ENNReal.ofReal ((a^2 / p γ) * δ * lo) ∨
          ENNReal.ofReal ((a^2 / p γ) * hi / δ) < g γ (Obs N k r x)} =
      μ (S γ ∩ {x | D γ (Q x) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal (hi / δ) < D γ (Q x)}) := by
    rw [(hcrop γ).2.1, (hcrop γ).2.2,
      BaseTransport.crop_bad_mass_eq a ha (q γ) N k r (p γ) (hcrop γ).1 ν₀ E₀]
    have hset : MeasurableSet {x | D γ (Q x) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal (hi / δ) < D γ (Q x)} :=
      (measurableSet_lt ((hD γ).comp hQ) measurable_const).union
        (measurableSet_lt measurable_const ((hD γ).comp hQ))
    rw [inter_comm (S γ), ← Measure.restrict_apply hset]
    apply measure_congr
    filter_upwards [hDeval γ] with x hx
    simp only [hx, raw, ENNReal.ofReal_mul hδ.le]
  have htail := finite_density_tail JointRef μ Q hQ H hH hHlaw S hS hdisj
    D hD hDlaw C (fun γ => Geometry.measurableSet_compatibleCrop a (q γ)) hsupp 4
    (Geometry.compatibleCrop_overlap q hq a)
    (ENNReal.ofReal lo) (ENNReal.ofReal hi) (ENNReal.ofReal (hi / δ)) (ENNReal.ofReal δ)
    (ENNReal.ofReal_le_ofReal ((le_div_iff₀ hδ).mpr (by nlinarith)))
  have hmass : μ univ ≤ 1 := by
    calc
      μ univ = (ν₀.prod volume) E₀ := Measure.restrict_apply_univ E₀
      _ ≤ (ν₀.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono htime
      _ = 1 := by rw [Measure.prod_prod]; simp
  calc
    _ = ∑ γ, μ (S γ ∩ {x | D γ (Q x) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal (hi / δ) < D γ (Q x)}) := Finset.sum_congr rfl fun γ _ => hleft γ
    _ ≤ μ {x | H (Q x) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < H (Q x)} +
        4 * ENNReal.ofReal δ * μ univ := htail
    _ ≤ μ {x | H (Q x) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < H (Q x)} +
        ENNReal.ofReal (32 * δ) := by
      gcongr
      calc
        4 * ENNReal.ofReal δ * μ univ ≤ 4 * ENNReal.ofReal δ * 1 := mul_le_mul' le_rfl hmass
        _ = ENNReal.ofReal (4 * δ) := by rw [mul_one, ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal (32 * δ) := ENNReal.ofReal_le_ofReal (by nlinarith)

end Submission.Obl.k4_crop_base_finite_tail.Assembly
