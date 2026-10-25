import Submission.Obl.k4_narrow_projected_row_parents.ComparedOfOutput
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedComparisonDeletion

/-!
# The comparison record at one index

`compared_at`: at one index `k`, a dense current law `ζ ≤ ρ_k` covered by a (refined)
projected layer `L` whose assignments lie in the original slice's assignments `Cold`, together
with the hypotheses of the single-index comparison `prepared_comparison_at`, a native exception
`E` of small mass and the budget conditions, gives `Compared` for the original slice.

The native exception is deleted first (`comparison_source_outside_exception`), the comparison
is run on the rest, its mass budget is charged before the deletion
(`PreparedComparison.mass_budget_before_deletion`), and the output is read as `Compared`
(`compared_of_output`) and collapsed to the original labels (`Compared.map_projected`).
All hypotheses are explicit at the index; nothing is asymptotic.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

/-- **The comparison record at one index.** -/
theorem compared_at {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R s H La q χ m : ℝ} {k : ℕ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    {n : ℕ} (Cold : Fin n → Set α)
    (L : ProjLayer α) (toOld : Fin L.n → Fin n) (hLC : ∀ i, L.C i ⊆ Cold (toOld i))
    (hL : L.Good (p.N k) H p.d p.ell La s χ (a.b k) (a.P k) (a.pi k) (a.rho k))
    (hH : 1 ≤ H) (hq : 0 < q) (hqQ : q ≤ a.q k s) (hχ : 0 < χ)
    (hχQ : χ ≤ a.q k s) (hχQg : χ ≤ a.q k s * PreparedModel.narrow p k s)
    (hm : 0 < m) (hmQg : m ≤ a.q k s * PreparedModel.narrow p k s) (hmβ : m ≤ L.β)
    (hqg : q * PreparedModel.narrow p k s ≤ m)
    {aTable Fprune Llist ε C Λ r v S σ : ℝ} (haTable : 0 < aTable)
    (Kchart : NNReal) (hKchart : 4 * (projectedSheetConstant * H ^ 3) ≤ Kchart)
    (hprojerr : 4 * (H * PreparedModel.width p k s) ≤ aTable)
    (E : Set (α × ℝ)) (hEm : MeasurableSet E) (assign : α × ℝ → Fin (a.n k s))
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hfactory : TrueSourceFactory p a k s q χ m aTable Kchart E assign g)
    (hχeq : χ = p.N k ^ (-v)) (hS : 0 ≤ S) (haMin : p.N k ^ (-S) ≤ aTable)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 24)
    (hδq : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * q * σ)
    (hδχ : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * χ * σ)
    (hδm : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * m * σ)
    (hmesh : 2 * (Kchart : ℝ) * (3 * σ) ≤ aTable / 2)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ S → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀})
    (hFprune : 0 < Fprune) (hLlist : 1 ≤ Llist)
    (hLfloor : 14 * commonNativeCapConstant (p.K k) * Fprune ≤ Llist)
    (Match : ComparisonEstimate 4 p.d ε C) (hC : 0 ≤ C)
    (hΛ : C * Llist ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (ζ : Measure (α × ℝ)) [IsFiniteMeasure ζ] (hζρ : ζ ≤ a.rho k)
    (hcovered : ∀ᵐ z ∂ζ, z ∈ L.covered)
    {H₀ nativeLoss M : ℝ} (hH₀ : 0 < H₀) (hζmass : ENNReal.ofReal H₀⁻¹ ≤ ζ univ)
    (hnl : 0 ≤ nativeLoss) (hnative : ζ E ≤ ENNReal.ofReal nativeLoss)
    (hμE : a.mu k E < ζ univ)
    (hloss : nativeLoss + commonComparisonReference p k s H aTable / Fprune +
      C * (6 * commonNativeCapConstant (p.K k)) * Λ ^ (-ε) *
        commonComparisonReference p k s H aTable ≤ (2 * H₀)⁻¹)
    (hM : 2 * H₀ ≤ M) (hMcard : 2 * (Llist * Λ ^ p.d) ≤ M) :
    Nonempty (Compared a k s Cold q χ (PreparedModel.narrow p k s) m M) := by
  classical
  have hρμ : a.rho k ≤ a.mu k := (hcommon k).2.2.2.2.1
  have hb : Measurable (a.b k) := (hcommon k).1
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  -- delete the native exception
  obtain ⟨hζ'μ, hζ'pos, hζ'E⟩ := comparison_source_outside_exception (hζρ.trans hρμ) hEm hμE
  -- the comparison
  obtain ⟨P⟩ := prepared_comparison_at p hp a hcommon hs hatlas L hL hH hq hqQ hχ hχQ hχQg hm
    hmQg hmβ hqg haTable Kchart hKchart hprojerr E assign g hfactory hχeq hS haMin hσ hσsmall
    hδq hδχ hδm hmesh hcap hFprune hLlist hLfloor Match hC hΛ hΛ1 (ζ.restrict Eᶜ) hζ'μ hζ'pos
    hζ'E (ae_restrict_of_ae hcovered)
  obtain ⟨hlawζ, hbudget⟩ := P.mass_budget_before_deletion hEm hnative
  -- the mass floor
  have href0 : 0 ≤ commonComparisonReference p k s H aTable := by
    unfold commonComparisonReference
    have hw : 0 < PreparedModel.width p k s := Real.rpow_pos_of_pos hN _
    have hK0 : 0 ≤ p.K k := by linarith
    exact mul_nonneg (Real.rpow_nonneg (div_pos haTable hw).le _) (by positivity)
  have hcap0 : 0 ≤ commonNativeCapConstant (p.K k) := by
    unfold commonNativeCapConstant
    have hK0 : 0 ≤ p.K k := by linarith
    positivity
  have hX : 0 ≤ nativeLoss + commonComparisonReference p k s H aTable / Fprune :=
    add_nonneg hnl (div_nonneg href0 hFprune.le)
  have hY : 0 ≤ C * (6 * commonNativeCapConstant (p.K k)) * Λ ^ (-ε) *
      commonComparisonReference p k s H aTable :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity))
      (Real.rpow_nonneg (by linarith) _)) href0
  have hbudget' : ζ univ ≤ P.law univ +
      ENNReal.ofReal (nativeLoss + commonComparisonReference p k s H aTable / Fprune) +
      ENNReal.ofReal (C * (6 * commonNativeCapConstant (p.K k)) * Λ ^ (-ε) *
        commonComparisonReference p k s H aTable) := by
    rw [ENNReal.ofReal_add hnl (div_nonneg href0 hFprune.le)]
    calc ζ univ ≤ _ := hbudget
      _ = _ := by ac_rfl
  have hlawmass := law_mass_of_budget hH₀ hζmass hbudget' hloss hX hY
  have hM0 : 0 < M := by linarith
  have hmassM : ENNReal.ofReal M⁻¹ ≤ P.law univ := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlawmass
    exact inv_anti₀ (by positivity) hM
  -- read the output as `Compared` for the refined layer, then collapse
  obtain ⟨-, -, -, hLm, hLdisj, -⟩ := hL
  have hW : ∀ Q, MeasurableSet (a.B k s Q ×ˢ a.block k s Q) := fun Q =>
    ((hatlas.2.2.1 Q).2.1).prod measurableSet_Icc
  obtain ⟨cmp⟩ := compared_of_output L.C hLm (fun i j hij => hLdisj i j hij) hb hW ζ P.law hζρ
    hlawζ hmassM hM0 P.tru P.measurable_tru P.lab P.partners
    (fun i c => (P.card_partners i c).trans hMcard) (by
      filter_upwards [P.source] with z hz
      exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1⟩)
  exact ⟨cmp.map_projected toOld hLC⟩

end Submission.Obl.k4_narrow_projected_row_parents
