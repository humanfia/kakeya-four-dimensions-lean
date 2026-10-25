import Submission.Obl.k4_dyadic_crop_worlds.CroppedFormat
import Submission.Lib.K4ModelReduction.NativeBounds

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set
noncomputable section

/-- The native a.e. trajectory bound, with its two hidden coefficients unchanged by crops. -/
def NativeBound (K : ℝ) (l : Line) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
      ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ K ∧
      |l.2 2 + t * l.2 5| ≤ K

lemma nativeBound_crop {a K₀ K : ℝ} {q : Label} {l : Line}
    (hl : l ∈ cell a q) (hK : NativeBound K₀ l) (hK₀ : K₀ ≤ K) (hK6 : 6 ≤ K) :
    NativeBound K (cropLine a q l) := by
  have hcoord (j : Fin 4) : |cropCoeff a q l.2 (planarCoord j)| ≤ 1 := by
    have h := cropCoeff_planar_mem hl j
    rw [abs_of_nonneg h.1]
    exact h.2.le
  intro t ht
  have h0 := Lib.K4ModelReduction.raw_affine_coordinate_bound (hcoord 0) (hcoord 2) ht
  have h1 := Lib.K4ModelReduction.raw_affine_coordinate_bound (hcoord 1) (hcoord 3) ht
  have hb := Lib.K4ModelReduction.norm_pair_le_two_bound (by norm_num : (0 : ℝ) ≤ 2) (by simpa only [mul_one] using h0) (by simpa only [mul_one] using h1)
  have hv := Lib.K4ModelReduction.norm_pair_le_two_bound (by norm_num : (0 : ℝ) ≤ 1) (hcoord 2) (hcoord 3)
  constructor
  · change ‖(WithLp.toLp 2 ![cropCoeff a q l.2 0 + t * cropCoeff a q l.2 3,
      cropCoeff a q l.2 1 + t * cropCoeff a q l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![cropCoeff a q l.2 3, cropCoeff a q l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ K
    exact (add_le_add hb hv).trans (by linarith)
  · change |l.2 2 + t * l.2 5| ≤ K
    exact (hK t ht).2.trans hK₀

lemma cropPrior_nativeBound {a K₀ K : ℝ} (ν : Measure Line)
    (ha : a ≠ 0) (q : Label) (p : ℝ) (hK : ∀ᵐ l ∂ν, NativeBound K₀ l)
    (hK₀ : K₀ ≤ K) (hK6 : 6 ≤ K) :
    ∀ᵐ l ∂cropPrior ν a q p, NativeBound K l := by
  unfold cropPrior
  apply Measure.ae_smul_measure
  apply (lineHomeomorph ha q).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [ae_restrict_of_ae hK, ae_restrict_mem (measurable_cell a q)] with l hl hm
  exact nativeBound_crop hm hl hK₀ hK6

/-- The fixed-scale one-world crop interface, including its exact mass law. -/
lemma cropped_world {R K₀ K δ a p : ℝ} {D : ℕ} (ν : Measure Line)
    [IsProbabilityMeasure ν] (E : Set Incident) (q : Label)
    (hR : 1 ≤ R) (hν : PriorFormat R D ν) (hE : EventFormat R D E)
    (hK : ∀ᵐ l ∂ν, NativeBound K₀ l) (hK₀ : K₀ ≤ K) (hK6 : 6 ≤ K)
    (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : δ ≤ p)
    (heq : p = (ν (cell a q)).toReal) :
    IsProbabilityMeasure (cropPrior ν a q p) ∧
    PriorFormat ((R + 8) / δ) (max D 1) (cropPrior ν a q p) ∧
    EventFormat (R + 8) (max D 1) (cropEvent E a q) ∧
    (∀ᵐ l ∂cropPrior ν a q p, NativeBound K l) ∧
    ((cropPrior ν a q p).prod volume) (cropEvent E a q) =
      (ENNReal.ofReal p)⁻¹ * (ν.prod volume) (E ∩ (cell a q ×ˢ univ)) := by
  refine ⟨cropPrior_probability ν a q (hδ.trans_le hp) heq,
    cropPrior_format hR hν ha ha1 hδ hδ1 hp q, cropEvent_format hR hE ha.ne' q,
    cropPrior_nativeBound ν ha.ne' q p hK hK₀ hK6, ?_⟩
  simpa only [Measure.restrict_apply_univ] using cropPrior_incidence_mass ν ha.ne' q p hE.1

end
end Submission.Obl.k4_dyadic_crop_worlds
