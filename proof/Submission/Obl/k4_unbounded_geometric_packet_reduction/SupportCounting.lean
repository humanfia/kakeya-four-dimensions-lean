import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

noncomputable section

/-- Oscillation on each cell, earlier label and partition piece produces a
finite occupied grid support.  The count uses labels per cell, rather than
the total number of earlier labels in the system. -/
theorem finite_support_of_colored_oscillation {Q : Type*} {J : ℕ}
    (cells : Finset Q) (tags : Q → Finset (Fin J)) (n : Fin J → ℕ)
    (values : (q : Q) → (e : Fin J) → Fin (n e) → Set ℝ)
    {H G L δ : ℝ} (hH : 0 ≤ H) (hG : 0 ≤ G) (hL : 0 ≤ L) (hδ : 0 < δ)
    (origin : ℝ) (htags : ∀ q ∈ cells, ((tags q).card : ℝ) ≤ H)
    (hparts : ∀ e, (n e : ℝ) ≤ G)
    (hosc : ∀ q e i, ∀ x ∈ values q e i, ∀ y ∈ values q e i, dist x y ≤ L) :
    ∃ F : Finset (Q × ℤ),
      (F.card : ℝ) ≤ (cells.card : ℝ) * H * G * (2 * L / δ + 2) ∧
      ∀ q ∈ cells, ∀ e ∈ tags q, ∀ i, ∀ x ∈ values q e i,
        (q, ⌊(x - origin) / δ⌋) ∈ F := by
  classical
  have hbins q e i := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (values q e i) hL hδ origin (hosc q e i)
  let B (q : Q) (e : Fin J) (i : Fin (n e)) : Finset ℤ := (hbins q e i).1.toFinset
  let U (q : Q) (e : Fin J) : Finset ℤ := Finset.univ.biUnion (B q e)
  let V (q : Q) : Finset ℤ := (tags q).biUnion (U q)
  let F : Finset (Q × ℤ) := cells.biUnion (fun q => (V q).image (Prod.mk q))
  have hC : 0 ≤ 2 * L / δ + 2 := by positivity
  have hB q e i : ((B q e i).card : ℝ) ≤ 2 * L / δ + 2 := by
    have hh := (hbins q e i).2
    rw [Set.ncard_eq_toFinset_card _ (hbins q e i).1] at hh
    exact hh
  have hU q e : ((U q e).card : ℝ) ≤ G * (2 * L / δ + 2) := by
    calc
      _ ≤ ∑ i : Fin (n e), ((B q e i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          (U q e).card ≤ ∑ i : Fin (n e), (B q e i).card)
      _ ≤ ∑ _i : Fin (n e), (2 * L / δ + 2) :=
        Finset.sum_le_sum (fun i _ => hB q e i)
      _ = (n e : ℝ) * (2 * L / δ + 2) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hparts e) hC
  have hV q (hq : q ∈ cells) : ((V q).card : ℝ) ≤ H * G * (2 * L / δ + 2) := by
    calc
      _ ≤ ∑ e ∈ tags q, ((U q e).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : (V q).card ≤ ∑ e ∈ tags q, (U q e).card)
      _ ≤ ∑ _e ∈ tags q, G * (2 * L / δ + 2) :=
        Finset.sum_le_sum (fun e _ => hU q e)
      _ = ((tags q).card : ℝ) * (G * (2 * L / δ + 2)) := by simp
      _ ≤ H * (G * (2 * L / δ + 2)) :=
        mul_le_mul_of_nonneg_right (htags q hq) (mul_nonneg hG hC)
      _ = _ := by ring
  refine ⟨F, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ cells, (((V q).image (Prod.mk q)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          F.card ≤ ∑ q ∈ cells, ((V q).image (Prod.mk q)).card)
      _ ≤ ∑ q ∈ cells, ((V q).card : ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        exact_mod_cast (Finset.card_image_le : ((V q).image (Prod.mk q)).card ≤ (V q).card)
      _ ≤ ∑ _q ∈ cells, H * G * (2 * L / δ + 2) := Finset.sum_le_sum hV
      _ = _ := by simp; ring
  · intro q hq e he i x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, Finset.mem_image.mpr ⟨⌊(x - origin) / δ⌋, ?_, rfl⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩⟩
    change ⌊(x - origin) / δ⌋ ∈ (hbins q e i).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨x, hx, rfl⟩

open MeasureTheory

/-- Global domination of the tagged pushed-forward laws pays all exceptions
before conditioning on any one packet.  No factor for the number of packets
or the number of earlier labels is introduced. -/
theorem weighted_tagged_exception_le
    {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype I] [Fintype E]
    (μ : I → Measure X) (Λ : E → Measure Y) (R : I → ENNReal) (w : E → ENNReal)
    (A : I → Set X) (tag : I → X → E) (z : I → E → X → Y)
    (hz : ∀ i e, Measurable (z i e)) (bad : E → Set Y)
    (hbad : ∀ e, MeasurableSet (bad e)) (δ : ENNReal)
    (hw : ∑ e, w e ≤ 1) (hδ : ∀ e, Λ e (bad e) ≤ δ)
    (hdom : ∀ e, (∑ i, R i • Measure.map (z i e)
      ((μ i).restrict {x | x ∈ A i ∧ tag i x = e})) ≤ w e • Λ e) :
    (∑ i, R i * μ i {x | x ∈ A i ∧ z i (tag i x) x ∈ bad (tag i x)}) ≤ δ := by
  classical
  let D (i : I) (e : E) : Set X := {x | x ∈ A i ∧ tag i x = e ∧ z i e x ∈ bad e}
  have hcover i : {x | x ∈ A i ∧ z i (tag i x) x ∈ bad (tag i x)} = ⋃ e, D i e := by
    ext x
    constructor
    · rintro ⟨hx, hbx⟩
      exact Set.mem_iUnion.mpr ⟨tag i x, hx, rfl, hbx⟩
    · intro hx
      obtain ⟨e, hAx, he, hbx⟩ := Set.mem_iUnion.mp hx
      exact ⟨hAx, by simpa only [he] using hbx⟩
  have hlocal i : μ i {x | x ∈ A i ∧ z i (tag i x) x ∈ bad (tag i x)} ≤
      ∑ e, μ i (D i e) := by
    rw [hcover]
    simpa only [tsum_fintype] using (measure_iUnion_le (fun e => D i e) :
      μ i (⋃ e, D i e) ≤ ∑' e, μ i (D i e))
  have hgroup e : (∑ i, R i * μ i (D i e)) ≤ w e * δ := by
    calc
      _ = (∑ i, R i • Measure.map (z i e)
          ((μ i).restrict {x | x ∈ A i ∧ tag i x = e})) (bad e) := by
        symm
        rw [Measure.finsetSum_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hz i e) (hbad e),
          Measure.restrict_apply ((hbad e).preimage (hz i e))]
        apply congrArg (fun s : Set X => R i * μ i s)
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, D]
        tauto
      _ ≤ w e * Λ e (bad e) := by
        simpa only [Measure.smul_apply, smul_eq_mul] using hdom e (bad e)
      _ ≤ w e * δ := mul_le_mul_of_nonneg_left (hδ e) zero_le
  calc
    _ ≤ ∑ i, R i * ∑ e, μ i (D i e) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlocal i) zero_le)
    _ = ∑ e, ∑ i, R i * μ i (D i e) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ e, w e * δ := Finset.sum_le_sum (fun e _ => hgroup e)
    _ = δ * ∑ e, w e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hw zero_le
    _ = δ := mul_one _


end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
