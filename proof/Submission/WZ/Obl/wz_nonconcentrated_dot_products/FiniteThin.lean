-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.FiniteThin.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinTubes
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.GoodRow
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinDotProducts

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Extend a relation on finite subtype indices to ambient plane points. -/
theorem IndexedThinTubes.to_finite {S T : Finset Plane} {δ σ K c : ℝ}
    (h : IndexedThinTubes δ σ K c (fun x : S => (x : Plane)) (fun y : T => (y : Plane))) :
    ∃ R : Plane → Plane → Prop,
      (((S ×ˢ T).filter (fun p => ¬R p.1 p.2)).card : ℝ) ≤ c * (S.card : ℝ) * (T.card : ℝ) ∧
      ∀ b ∈ S, ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
        ((T.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card : ℝ) ≤
          K * r ^ σ * (T.card : ℝ) := by
  classical
  obtain ⟨R₀, hbad, hthin⟩ := h
  let R (b x : Plane) : Prop := if hb : b ∈ S then if hx : x ∈ T then R₀ ⟨b, hb⟩ ⟨x, hx⟩ else False else False
  have hbad_eq : (Finset.univ.filter (fun p : S × T => ¬R₀ p.1 p.2)).card =
      ((S ×ˢ T).filter (fun p => ¬R p.1 p.2)).card := by
    calc (Finset.univ.filter (fun p : S × T => ¬R₀ p.1 p.2)).card =
        (Finset.univ.filter (fun p : S × T => ¬R p.1 p.2)).card := by
          congr 1
          ext p
          simp [R, p.1.property, p.2.property]
      _ = _ := by
        convert indexed_pair_filter_card S T (fun p => ¬R p.1 p.2) using 1 <;>
          congr 1 <;> ext p <;> simp
  refine ⟨R, ?_, ?_⟩
  · have hb' : (((S ×ˢ T).filter (fun p => ¬R p.1 p.2)).card : ℝ) ≤
        c * (S.card : ℝ) * (T.card : ℝ) := by
      simpa only [hbad_eq, Fintype.card_coe] using hbad
    convert hb' using 1 <;> congr 2 <;> ext p <;> simp
  · intro b hb u r hu hr
    have hrow_eq : (Finset.univ.filter (fun x : T => R₀ ⟨b, hb⟩ x ∧
        |inner ℝ ((x : Plane) - b) u| < r)).card =
        (T.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card := by
      calc (Finset.univ.filter (fun x : T => R₀ ⟨b, hb⟩ x ∧
          |inner ℝ ((x : Plane) - b) u| < r)).card =
            (Finset.univ.filter (fun x : T => R b x ∧ |inner ℝ ((x : Plane) - b) u| < r)).card := by
              congr 1
              ext x
              simp [R, hb]
        _ = _ := by
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          exact Finset.sum_coe_sort T (fun x => if R b x ∧ |inner ℝ (x - b) u| < r then (1 : ℕ) else 0)
    have hr' : ((T.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card : ℝ) ≤
        K * r ^ σ * (T.card : ℝ) := by
      simpa only [hrow_eq, Fintype.card_coe] using hthin ⟨b, hb⟩ u r hu hr
    convert hr' using 1 <;> congr 2 <;> ext p <;> simp

theorem thin_dot_count_of_indexed_tubes (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ K c d : ℝ) (F G₁ G₂ : Finset Plane) (H : Finset Triple),
      0 < δ → δ ≤ δ₀ → 1 ≤ K → 0 < d - c → ClosedFiniteFrostman δ K F →
      H ⊆ F ×ˢ (G₁ ×ˢ G₂) → H.Nonempty →
      (∀ b ∈ G₁, ∀ x ∈ G₂, 1 / 4 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8) →
      IndexedThinTubes δ 1 K c (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane)) →
      d * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ) ≤ (H.card : ℝ) →
      ∀ (m : ℕ) (cc : Fin m → ℝ), Covers δ (DotSet (↑H : Set Triple)) cc →
        (d - c) ^ 4 * δ ^ (ε - 1) ≤ K ^ 2 * (m : ℝ) := by
  obtain ⟨δ₀, hδ₀, hcount⟩ := thin_dot_projection_count ε hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ K c d F G₁ G₂ H hδ hsmall hK hdc hF hH hHne hsep hthin hdensity
  obtain ⟨R, hbad, hrows⟩ := hthin.to_finite
  apply hcount δ K c d F G₁ G₂ H R hδ hsmall hK hdc hF hH hHne hsep ?_ hbad hdensity
  intro b hb u r hu hr
  simpa only [Real.rpow_one] using hrows b hb u r hu hr

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
