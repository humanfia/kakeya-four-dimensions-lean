import Mathlib

/- Developed in this workspace by x0047 for o015 and its endpoint-volume child. -/

/-!
# Quantitative local injectivity

A lower bound for the derivative, together with a modulus for its variation,
gives an injectivity radius. This lets the matching proof use a polynomial
number of small injective pieces rather than a semialgebraic fiber theorem.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set
open scoped NNReal

/-- The mean value inequality gives injectivity when the derivative stays
closer to one linear map than that map's lower norm bound. -/
lemma injOn_of_fderiv_close
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) (A : E →L[ℝ] F)
    {ε δ : ℝ} (hεδ : ε < δ)
    (hA : ∀ v : E, δ * ‖v‖ ≤ ‖A v‖)
    (hclose : ∀ x ∈ S, ‖fderiv ℝ f x - A‖ ≤ ε) : InjOn f S := by
  intro x hx y hy hxy
  have hmv := hS.norm_image_sub_le_of_norm_fderiv_le' hf hclose hx hy
  have hu : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    simpa only [hxy, sub_self, zero_sub, norm_neg] using hmv
  have hlo := hA (y - x)
  have hn : ‖y - x‖ = 0 := by
    have hnonneg := norm_nonneg (y - x)
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

lemma injOn_closedBall_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {r δ : ℝ} (L : ℝ≥0)
    (hf : ∀ y ∈ Metric.closedBall x r, DifferentiableAt ℝ f y)
    (hlip : LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall x r))
    (hr : 0 ≤ r) (hsmall : (L : ℝ) * r < δ)
    (hlower : ∀ v : E, δ * ‖v‖ ≤ ‖fderiv ℝ f x v‖) :
    InjOn f (Metric.closedBall x r) := by
  apply injOn_of_fderiv_close (convex_closedBall x r) hf (fderiv ℝ f x) hsmall hlower
  intro y hy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr
  have hbound := hlip.norm_sub_le hy hx
  have hy' : ‖y - x‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hy
  exact hbound.trans (mul_le_mul_of_nonneg_left hy'
    (show (0 : ℝ) ≤ L from L.coe_nonneg))

/-- The same quantitative radius separates distinct points of every regular fiber. -/
lemma fiber_separation_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S T : Set E} (hS : Convex ℝ S) (hTS : T ⊆ S)
    (L : ℝ≥0) {r δ : ℝ} (hr : 0 ≤ r) (hsmall : (L : ℝ) * r < δ)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hlip : LipschitzOnWith L (fderiv ℝ f) S)
    (hlower : ∀ x ∈ T, ∀ v : E, δ * ‖v‖ ≤ ‖fderiv ℝ f x v‖)
    {x y : E} (hx : x ∈ T) (hy : y ∈ T) (hne : x ≠ y) (heq : f x = f y) :
    r < dist x y := by
  by_contra hdist
  have hdist' : dist y x ≤ r := by simpa only [dist_comm] using le_of_not_gt hdist
  have hinj : InjOn f (S ∩ Metric.closedBall x r) := by
    apply injOn_of_fderiv_close (hS.inter (convex_closedBall x r))
      (fun z hz => hf z hz.1) (fderiv ℝ f x) hsmall (hlower x hx)
    intro z hz
    have hb := hlip.norm_sub_le hz.1 (hTS hx)
    have hz' : ‖z - x‖ ≤ r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz.2
    exact hb.trans (mul_le_mul_of_nonneg_left hz' L.coe_nonneg)
  exact hne (hinj ⟨hTS hx, Metric.mem_closedBall_self hr⟩ ⟨hTS hy, hdist'⟩ heq)

/-- A finite cover by injectivity sets bounds all fiber cardinalities, whether
or not the domain or cover sets are measurable. -/
lemma finite_fiber_of_finite_injective_cover
    {E F ι : Type*} (S : Set E) (f : E → F) (U : ι → Set E) (I : Finset ι)
    (hcover : S ⊆ ⋃ i ∈ I, U i) (hinj : ∀ i ∈ I, InjOn f (U i)) (y : F) :
    {x : E | x ∈ S ∧ f x = y}.Finite ∧ {x : E | x ∈ S ∧ f x = y}.ncard ≤ I.card := by
  classical
  let T := {x : E | x ∈ S ∧ f x = y}
  have hex : ∀ x : T, ∃ i : I, (x : E) ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.2.1)
    obtain ⟨hiI, hxi⟩ := mem_iUnion.mp hi
    exact ⟨⟨i, hiI⟩, hxi⟩
  choose tag htag using hex
  have htag_inj : Function.Injective tag := by
    intro x z hxz
    apply Subtype.ext
    apply hinj (tag x) (tag x).2 (htag x)
    · simpa only [hxz] using htag z
    · exact x.2.2.trans z.2.2.symm
  haveI : Finite T := Finite.of_injective tag htag_inj
  refine ⟨Set.toFinite T, ?_⟩
  have hc := Nat.card_le_card_of_injective tag htag_inj
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

end Submission.Obl.k4_matching_endpoint_volume
