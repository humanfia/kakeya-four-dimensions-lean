import Submission.Obl.k4_retained_edge_planar_rigidity.StripFit

/-!
# The uniform law on original retained edges

Restricting the original graph changes the rectangle cap only by the ratio of graph sizes.
The first-coordinate marginal follows by summing over the second endpoint set.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

noncomputable section

/-- The uniform law on a finite set turns an indicator sum into a relative cardinality. -/
theorem uniform_edge_mass {α : Type*} (R : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ e : R, (1 / (R.card : ℝ)) * (if P e then 1 else 0)) =
      ((R.filter P).card : ℝ) / R.card := by
  classical
  rw [Finset.sum_coe_sort R (fun e => (1 / (R.card : ℝ)) * (if P e then (1 : ℝ) else 0)),
    ← Finset.mul_sum, Finset.sum_boole]
  ring

theorem uniform_edge_sum {α : Type*} {R : Finset α} (hR : R.Nonempty) :
    (∑ _e : R, 1 / (R.card : ℝ)) = 1 := by
  have hR0 : (R.card : ℝ) ≠ 0 := by exact_mod_cast hR.card_ne_zero
  simp [hR0]

/-- A positive fraction of the uniform retained-edge law is the same fraction of original edges. -/
theorem retained_edge_card_of_mass {α : Type*} {R : Finset α} (hR : R.Nonempty)
    (P : α → Prop) [DecidablePred P] {p : ℝ}
    (hmass : p ≤ ∑ e : R, (1 / (R.card : ℝ)) * (if P e then 1 else 0)) :
    p * (R.card : ℝ) ≤ (R.filter P).card := by
  rw [uniform_edge_mass R P] at hmass
  exact (le_div_iff₀ (by exact_mod_cast hR.card_pos : (0 : ℝ) < R.card)).mp hmass

/-- The original rectangle cap implies a marginal cap for a retained subgraph.
`Q` bounds the loss in passing from the original graph to its retained edges. -/
theorem retained_edge_marginal
    {h K Q : ℝ} (hh : 0 < h) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    {B : Finset (ℝ × ℝ)} {G R : Finset ((ℝ × ℝ) × (ℝ × ℝ))}
    (hR : R.Nonempty) (hRG : R ⊆ G) (hGB : ∀ e ∈ G, e.2 ∈ B)
    (hBcard : (B.card : ℝ) * h ≤ K) (hGcard : (G.card : ℝ) ≤ Q * R.card)
    (hcap : ∀ x y : ℝ, (((G.filter (fun e =>
      e.1.1 ∈ Set.Ico x (x + h) ∧ e.2.1 ∈ Set.Ico y (y + h))).card : ℝ)) ≤
        K * h ^ 2 * G.card)
    (x r : ℝ) (hr : 0 ≤ r) :
    (∑ e : R, (1 / (R.card : ℝ)) * (if |e.val.1.1 - x| ≤ r then 1 else 0)) ≤
      2 * K ^ 2 * Q * (r + h) := by
  classical
  have hR0 : 0 < (R.card : ℝ) := by exact_mod_cast hR.card_pos
  have hu : ∀ _e : R, 0 ≤ 1 / (R.card : ℝ) := fun _ => by positivity
  have hrect : ∀ x y : ℝ, (∑ e : R, (1 / (R.card : ℝ)) *
      (if e.val.1.1 ∈ Set.Ico x (x + h) ∧ e.val.2.1 ∈ Set.Ico y (y + h) then 1 else 0)) ≤
        K * Q * h ^ 2 := by
    intro x y
    rw [uniform_edge_mass R (fun e =>
      e.1.1 ∈ Set.Ico x (x + h) ∧ e.2.1 ∈ Set.Ico y (y + h)), div_le_iff₀ hR0]
    have hsub : R.filter (fun e => e.1.1 ∈ Set.Ico x (x + h) ∧ e.2.1 ∈ Set.Ico y (y + h)) ⊆
        G.filter (fun e => e.1.1 ∈ Set.Ico x (x + h) ∧ e.2.1 ∈ Set.Ico y (y + h)) :=
      Finset.filter_subset_filter _ hRG
    have hc : ((R.filter (fun e => e.1.1 ∈ Set.Ico x (x + h) ∧
        e.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤
      ((G.filter (fun e => e.1.1 ∈ Set.Ico x (x + h) ∧
        e.2.1 ∈ Set.Ico y (y + h))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    calc _ ≤ K * h ^ 2 * G.card := hc.trans (hcap x y)
      _ ≤ K * h ^ 2 * (Q * R.card) := mul_le_mul_of_nonneg_left hGcard (by positivity)
      _ = K * Q * h ^ 2 * R.card := by ring
  have hmesh : ∀ x : ℝ, (∑ e : R, (1 / (R.card : ℝ)) *
      (if e.val.1.1 ∈ Set.Ico x (x + h) then 1 else 0)) ≤ (K ^ 2 * Q) * h := by
    intro x
    have hmarg := marginal_cap_of_rectangle hu (fun e => e.val.1.1) (fun e => e.val.2.1)
      hh (B.image Prod.fst) (fun e => Finset.mem_image.mpr ⟨e.val.2, hGB e.val (hRG e.property), rfl⟩)
      hrect x
    have hT : ((B.image Prod.fst).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_image_le
    calc _ ≤ (B.image Prod.fst).card * (K * Q * h ^ 2) := hmarg
      _ ≤ B.card * (K * Q * h ^ 2) := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ((B.card : ℝ) * h) * (K * Q * h) := by ring
      _ ≤ K * (K * Q * h) := mul_le_mul_of_nonneg_right hBcard (by positivity)
      _ = (K ^ 2 * Q) * h := by ring
  simpa only [mul_assoc] using
    interval_cap_of_mesh hu (fun e => e.val.1.1) hh (by positivity) hmesh x r hr

/-- A fitted event in the uniform retained-edge law selects that many original edges, also after
undoing the second-endpoint dilation. -/
theorem retained_edges_of_fit
    {R : Finset ((ℝ × ℝ) × (ℝ × ℝ))} (hR : R.Nonempty)
    {κ ℓ c₁ c₂ K L E p : ℝ} (hK : 1 ≤ K) (hκ : κ ≠ 0) (hκinv : |κ⁻¹| ≤ K)
    (hcoeff : |ℓ| + |c₁| + |c₂| ≤ L)
    (hmass : p ≤ ∑ e : R, (1 / (R.card : ℝ)) *
      (if |e.val.1.2 - ℓ * e.val.1.1 - c₁| +
        |κ * e.val.2.2 - ℓ * (κ * e.val.2.1) - c₂| ≤ E then 1 else 0)) :
    ∃ G' : Finset ((ℝ × ℝ) × (ℝ × ℝ)), G' ⊆ R ∧ p * (R.card : ℝ) ≤ G'.card ∧
      ∃ c₂' : ℝ, |ℓ| + |c₁| + |c₂'| ≤ K * L ∧ ∀ e ∈ G',
        |e.1.2 - ℓ * e.1.1 - c₁| + |e.2.2 - ℓ * e.2.1 - c₂'| ≤ K * E := by
  classical
  let P : ((ℝ × ℝ) × (ℝ × ℝ)) → Prop := fun e =>
    |e.1.2 - ℓ * e.1.1 - c₁| + |κ * e.2.2 - ℓ * (κ * e.2.1) - c₂| ≤ E
  have hcard := retained_edge_card_of_mass hR P hmass
  have hfit := unscale_parallel_fit (fun e : ((ℝ × ℝ) × (ℝ × ℝ)) => e.1)
    (fun e => e.2) P hK hκ hκinv hcoeff (fun _ he => he)
  exact ⟨R.filter P, Finset.filter_subset _ _, hcard, c₂ / κ, hfit.1,
    fun e he => hfit.2 e (Finset.mem_filter.mp he).2⟩

end

end Submission.Obl.k4_retained_edge_planar_rigidity
