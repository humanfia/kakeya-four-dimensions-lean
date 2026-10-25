import Submission.Obl.k4_narrow_projected_row_parents.NarrowReduction
import Submission.Obl.k4_narrow_projected_row_parents.NativeSheetsEventually
import Submission.Obl.k4_narrow_projected_row_parents.NaturalComparisonMesh
import Submission.Obl.k4_narrow_projected_row_parents.ComparisonParameters
import Submission.Obl.k4_narrow_projected_row_parents.NativeSheetBudgets
import Submission.Obl.k4_narrow_projected_row_parents.MatchEstimate
import Submission.Obl.k4_narrow_projected_row_parents.ComparedOfOutput
import Submission.Obl.k4_narrow_projected_row_parents.WithLoss
import Submission.Obl.k4_narrow_projected_row_parents.SliceLayer
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.FactoryOfNative
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedComparisonDeletion
import Submission.Obl.k4_narrow_projected_row_parents.ComparedAt
import Submission.Obl.k4_narrow_projected_row_parents.CompareSeqOfRefined
import Submission.Obl.k4_narrow_projected_row_parents.OutputBudget
import Submission.Obl.k4_narrow_projected_row_parents.ComparisonReferenceGrowth

/-!
# The comparison along a narrow sequence

`narrowComparison` proves `NarrowComparison`: along the normalized narrow sequence, the
true labels at depth `s` and the narrow projected layer are compared at every large index
(paper, Lemma 8.3), giving `CompareSeq`.

At each index:
* the original loss is enlarged to `H₂ = 4 H²` (`Parameters.withLoss`), the loss of the
  refined layer, so the native exceptional mass `≤ 1/(10000 H₂)` is negligible;
* the true native sheets of all parents at depth `s` (`eventually_all_parents_native_sheets`
  with `A = 1`) give the true source factory (`exists_true_source_factory_of_native`);
* the layer is refined to the natural major width `min(N^(-m), a_s q_s g_s)/stableDivisor`
  (`refined_layers_at_width`), and `natural_comparison_mesh` supplies the time/area scales,
  the physical mesh, the exact major mesh exponent and the native caps;
* `prepared_comparison_at` (o200, x0934) compares the families on the source outside the
  native exception; `compared_of_output` and `map_projected` give the `Compared` record on
  the original assignments.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open ComparisonFrame
open Cmp.SheetComparison

noncomputable section

/-- A larger budget keeps a comparison record. -/
def Compared.mono {α : Type} [MeasurableSpace α] {a : PreparedModel α} {k : ℕ} {s : ℝ}
    {n : ℕ} {C : Fin n → Set α} {q χ g m M M' : ℝ} (cmp : Compared a k s C q χ g m M)
    (hM : 0 < M) (hMM : M ≤ M') : Compared a k s C q χ g m M' :=
  { cmp with
    mass := le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ hM hMM)) cmp.mass
    partners_card := fun Q c => (cmp.partners_card Q c).trans hMM }

theorem narrowComparison : NarrowComparison := by
  intro hMatch α _ cfg hv L₀ a₀ s hL ha₀ has hs2 hsU H ρ' β n' C tag u v G hw B hB hBA hfit
  classical
  have hs : 0 < s := ha₀.trans_le has
  have hmOld : 0 < (L₀ + 1) * a₀ := mul_pos (by linarith) ha₀
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hv.scale k]
  have hN0 : ∀ k, 0 < cfg.N k := fun k => by linarith [hv.scale k]
  have hNt := hv.scale_limit
  -- S0: the enlarged loss `H₂ = 4 H²` of the refined layer
  have hH1 : ∀ k, 1 ≤ H k := fun k => (hw.loss k).1
  let H₂ : ℕ → ℝ := fun k => 4 * H k ^ 2
  have hH₂1 : ∀ k, 1 ≤ H₂ k := fun k => by
    have := hH1 k; show 1 ≤ 4 * H k ^ 2; nlinarith
  have hH₂0 : ∀ k, 0 ≤ H₂ k := fun k => zero_le_one.trans (hH₂1 k)
  have hKH₂ : ∀ k, cfg.K k ≤ H₂ k := fun k => by
    have h1 := hH1 k
    have h2 : cfg.K k ≤ H k := (hw.loss k).2
    show cfg.K k ≤ 4 * H k ^ 2; nlinarith
  have hH₂sub : Model.Subpow cfg.N H₂ := (hw.refined_layers hv ((L₀ + 1) * a₀) le_rfl).1
  have hv₂ : Model.Valid (cfg.withLoss H₂) := hv.withLoss hKH₂ hH₂sub
  let p := Model.parameters (cfg.withLoss H₂)
  let a := Model.prepared (cfg.withLoss H₂)
  have hp : p.Valid := Model.parameters_valid hv₂
  obtain ⟨hcommon, hcaps, hatl, -⟩ := Model.prepared_valid hv₂
  have hd0 : 0 ≤ p.d := hp.2.2.2.1
  have hd1 : p.d < 1 := hp.2.2.2.2.1
  -- S1: true native sheets of all parents, `A = 1`
  obtain ⟨αc, βc, -, hnative⟩ :=
    eventually_all_parents_native_sheets 1 p hp a hcommon hcaps hatl hs hsU
  let n : ℕ := αc * 1 + βc
  -- S2: the matching estimate and the comparison budgets
  obtain ⟨ε, hε, Cm, hCm, hEst⟩ := comparison_estimate_of_match hMatch 4 (by norm_num) p.d hd0 hd1
  have hCproj : 0 ≤ projectedSheetConstant := projectedSheetConstant_pos.le
  obtain ⟨hVsub, hRstsub, -, hAsub⟩ :=
    subpower_budgets hN1 hNt hH₂1 hH₂1 hH₂sub hH₂sub projectedSheetConstant hCproj n
  let aT : ℕ → ℝ := fun k => errorScale (cfg.N k) projectedSheetConstant (H₂ k) (H₂ k) s
  let Bc : ℕ → ℝ := fun k => commonNativeCapConstant (H₂ k)
  let Rc : ℕ → ℝ := fun k => commonComparisonReference p k s (H₂ k) (aT k)
  obtain ⟨hBc1, hBcsub⟩ := common_native_cap_subpow hN1 hNt hH₂1 hH₂sub
  obtain ⟨hRc1, hRcsub⟩ := common_comparison_reference_subpow_of_factor (K := H₂) (H := H₂)
    (A := fun k => errorMultiplier (H₂ k) (H₂ k)) (width := fun k => PreparedModel.width p k s)
    (aTable := aT) hN1 hNt hH₂1 hH₂1 (fun k => (errorMultiplier_bounds (hH₂1 k) (hH₂1 k)).1)
    hH₂sub hH₂sub hAsub hd0 hd1.le (fun k => Real.rpow_pos_of_pos (hN0 k) _) (fun k => rfl)
  obtain ⟨bud⟩ := exists_comparison_budgets cfg.N Bc H₂ Rc hN1 hNt hBc1 hH₂1 hRc1 hBcsub
    hH₂sub hRcsub hε hCm
  -- S3: the natural major target and the refined layers
  let Rst : ℕ → ℝ := fun k => stableDivisor (H₂ k) n
  have hRst1 : ∀ k, 1 ≤ Rst k := fun k => (stableDivisor_bounds (hH₂1 k) n).1
  have hRst0 : ∀ k, 0 < Rst k := fun k => zero_lt_one.trans_le (hRst1 k)
  let nat : ℕ → ℝ := fun k =>
    min (cfg.N k ^ (-((L₀ + 1) * a₀))) (PreparedModel.width p k s * a.q k s * narrow p k s)
  have hnat : ∀ k, 0 < nat k := by
    intro k
    have hq : 0 < a.q k s := by unfold PreparedModel.q; positivity
    have hw0 : 0 < PreparedModel.width p k s := Real.rpow_pos_of_pos (hN0 k) _
    have hg0 : 0 < narrow p k s := Real.rpow_pos_of_pos (hN0 k) _
    exact lt_min (Real.rpow_pos_of_pos (hN0 k) _) (by positivity)
  let ξ : ℕ → ℝ := fun k => nat k / Rst k
  have hξ : ∀ k, 0 < ξ k := fun k => div_pos (hnat k) (hRst0 k)
  have hξold : ∀ k, ξ k ≤ cfg.N k ^ (-((L₀ + 1) * a₀)) := fun k =>
    (div_le_self (hnat k).le (hRst1 k)).trans (min_le_left _ _)
  obtain ⟨-, Lf, ζf, toOld, hLf⟩ := hw.refined_layers_at_width hv ξ hξ hξold
  let χ : ℕ → ℝ := fun k => cfg.N k ^ (-((L₀ + 1) * a₀)) /
    MajorRefinement.factor (cfg.N k ^ (-((L₀ + 1) * a₀))) (ξ k)
  have hχband : ∀ k, nat k / (2 * Rst k) ≤ χ k ∧ χ k ≤ nat k / Rst k := by
    intro k
    obtain ⟨-, -, -, -, -, -, hlo, hhi⟩ := hLf k
    refine ⟨?_, hhi⟩
    calc nat k / (2 * Rst k) = ξ k / 2 := by
          show nat k / (2 * Rst k) = nat k / Rst k / 2
          rw [div_div, mul_comm]
      _ ≤ χ k := hlo
  have hχ0 : ∀ k, 0 < χ k := fun k =>
    (div_pos (hnat k) (mul_pos two_pos (hRst0 k))).trans_le (hχband k).1
  -- S4: the natural common scales, the physical mesh and the native caps
  let R₀ : ℝ := 1 + s⁻¹
  have hR₀ : 1 < R₀ := by have := inv_pos.mpr hs; show 1 < 1 + s⁻¹; linarith
  have hR₀s : R₀⁻¹ ≤ s := by
    have h1 : s⁻¹ ≤ R₀ := by show s⁻¹ ≤ 1 + s⁻¹; linarith
    calc R₀⁻¹ ≤ s⁻¹⁻¹ := inv_anti₀ (inv_pos.mpr hs) h1
      _ = s := inv_inv s
  have hatlasEv : ∀ᶠ k in atTop, a.AtlasAt p R₀ k s :=
    (hatl R₀ hR₀).mono fun k hk => hk s hR₀s hsU
  have hβ0 : ∀ k, 0 < β k s := fun k => by
    have h := (hLf k).2.2.2.1.1
    rwa [(hLf k).2.2.1] at h
  have hβlower : ∀ᶠ k in atTop, p.N k ^ (-B - 1) ≤ β k s :=
    (hfit 1 one_pos).mono fun k hk => hk.1
  obtain ⟨sc, r, -, hmesh⟩ := natural_comparison_mesh p hp a hcaps hs hmOld hatlasEv H₂
    (fun k => β k s) χ hH₂1 hH₂sub hβ0 hβlower projectedSheetConstant hCproj n hχband
  have hzoom := eventually_zoomMesh_bounds hN1 hNt hH₂1 hH₂1 hH₂sub hH₂sub
    projectedSheetConstant hCproj n hs
  -- S5: the output budget
  let M : ℕ → ℝ := fun k => outputBudget (H₂ k) (Rst k) (bud.list k) (bud.discrepancy k)
  have hlist0 : ∀ k, 0 ≤ bud.list k := fun k => zero_le_one.trans (bud.list_one k)
  have hΛ0 : ∀ k, 0 ≤ bud.discrepancy k := fun k => zero_le_one.trans (bud.discrepancy_one k)
  have hM1 : ∀ k, 1 ≤ M k := fun k =>
    one_le_outputBudget (hH₂0 k) (hRst0 k).le (hlist0 k) (hΛ0 k)
  have hMsub : Model.Subpow cfg.N M :=
    subpow_outputBudget hN1 hNt hH₂0 (fun k => (hRst0 k).le) hlist0 hΛ0 hH₂sub hRstsub
      bud.list_subpow bud.discrepancy_subpow
  -- S6: package
  refine compareSeq_of_refined cfg s ((L₀ + 1) * a₀) (fun k => β k s) χ
    (fun k => (nativeBound (H₂ k) n)⁻¹) Rst M (fun k => n' k s) (fun k => (Lf k).n)
    (fun k => C k s) (fun k => (Lf k).C) toOld (fun k i => ((hLf k).2.2.2.2.1 i).1)
    hM1 hMsub hRst0 sc ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun k => ⟨hχ0 k, ?_⟩
    have e : PreparedModel.width p k s * a.q k s * narrow p k s =
        cfg.N k ^ (-s) * ((Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s)) :=
      mul_assoc _ _ _
    rw [← e]
    exact (hχband k).1
  · exact Filter.Eventually.of_forall fun k =>
      stable_le_outputBudget (hH₂0 k) (hlist0 k) (hΛ0 k)
  · filter_upwards [hatlasEv, hnative, hmesh, hzoom] with k hat hnat hmk hzk
    obtain ⟨Rel, g, E, hRel, hE, hEmass, hsheet⟩ := hnat
    obtain ⟨v₀, hχeq, hδq, hδχ, hδm, hcap⟩ := hmk
    obtain ⟨hσ, hσsmall, -, hmeshk⟩ := hzk
    have hK1 : 1 ≤ p.K k := hH₂1 k
    have hH₂pos : 0 < H₂ k := zero_lt_one.trans_le (hH₂1 k)
    have hNk : 0 < p.N k := hN0 k
    obtain ⟨haMin, herr, hprojerr⟩ :=
      errorScale_bounds (C := projectedSheetConstant) (s := s) hNk hK1 hK1
    obtain ⟨hchart2, hchartV, hchartC⟩ := chartBound_bounds hCproj hK1 hK1 n
    let Kc : NNReal := ⟨chartBound projectedSheetConstant (H₂ k) (H₂ k) n, zero_le_two.trans hchart2⟩
    have hV1 := nativeBound_one hK1 n
    have hρ : 0 < (nativeBound (H₂ k) n)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hV1)
    have haT : 0 < aT k := (Real.rpow_pos_of_pos hNk _).trans_le haMin
    -- the true source factory from the native sheets
    obtain ⟨assign, -, hfactory⟩ := exists_true_source_factory_of_native p hp a hcommon hs.le hat
      Rel g E hE hRel (by intro i; rw [nativeBound_eq]; exact hsheet i) (aT k) Kc
      (zero_le_one.trans hV1 : 0 ≤ nativeBound (H₂ k) n) hchartV herr (sc k).q_pos (hχ0 k)
      (sc k).major_one (sc k).major_minor (sc k).m_pos (sc k).area.le hρ (sc k).q_small
      (sc k).major_small (sc k).minor_small
    -- the current law and the native exception
    have hζρ : ζf k ≤ a.rho k := (hLf k).1.trans (hw.retained k).1
    have hζμ : ζf k ≤ a.mu k := hζρ.trans (hcommon k).2.2.2.2.1
    have : IsFiniteMeasure (ζf k) := ⟨lt_of_le_of_lt (Measure.le_iff'.mp hζρ univ)
      ((PreparedModel.rho_univ_le p a hcommon k).trans_lt ENNReal.ofReal_lt_top)⟩
    have hw0 : 0 < PreparedModel.width p k s := Real.rpow_pos_of_pos hNk _
    have hw1 : PreparedModel.width p k s ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
    have hbad := native_parent_sheet_bad_budget (K := p.K k) hK1 hw0 hw1
    simp only [pow_one] at hEmass
    have hEμ : a.mu k E ≤ ENNReal.ofReal (1 / (10000 * H₂ k)) :=
      hEmass.trans (ENNReal.ofReal_le_ofReal hbad)
    have hsmall : 1 / (10000 * H₂ k) < (H₂ k)⁻¹ := by
      rw [one_div]
      exact inv_strictAnti₀ hH₂pos (by linarith)
    have hμE : a.mu k E < ζf k univ := by
      refine lt_of_le_of_lt hEμ (lt_of_lt_of_le ?_ (hLf k).2.1)
      exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hH₂pos)).mpr hsmall
    have hnativeζ : ζf k E ≤ ENNReal.ofReal (1 / (10000 * H₂ k)) :=
      (Measure.le_iff'.mp hζμ E).trans hEμ
    -- the mass budget
    have hloss : 1 / (10000 * H₂ k) + Rc k / bud.floor k +
        Cm * (6 * Bc k) * bud.discrepancy k ^ (-ε) * Rc k ≤ (2 * H₂ k)⁻¹ := by
      have h1 := bud.error k
      have h2 : 1 / (10000 * H₂ k) + 1 / (32 * H₂ k) ≤ (2 * H₂ k)⁻¹ := by
        rw [div_add_div _ _ (by positivity) (by positivity), inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (H₂ k)]
      linarith
    have hMmass : 2 * H₂ k ≤ M k := by
      have := mass_le_outputBudget (H := H₂ k) (hRst0 k).le (hlist0 k) (hΛ0 k)
      show 2 * H₂ k ≤ outputBudget (H₂ k) (Rst k) (bud.list k) (bud.discrepancy k)
      linarith [hH₂0 k]
    have hmβ : (sc k).m ≤ (Lf k).β := by
      rw [(hLf k).2.2.1]
      exact (sc k).m_beta
    exact compared_at p hp a hcommon hs.le hat (Lf k).C (Lf k) id (fun i => subset_rfl)
      (hLf k).2.2.2.1 (hH₂1 k) (sc k).q_pos (sc k).q_parent (hχ0 k) (sc k).major_parent
      (sc k).major_area (sc k).m_pos (sc k).minor_area hmβ (sc k).area.le haT Kc hchartC
      hprojerr E hE assign g hfactory hχeq hs.le haMin hσ hσsmall hδq hδχ hδm hmeshk hcap
      (bud.floor_pos k) (bud.list_one k) (bud.list_floor k) hEst (by linarith) (bud.threshold k)
      (bud.discrepancy_one k) (ζf k) hζρ (hLf k).2.2.2.2.2.1 hH₂pos (hLf k).2.1
      (by positivity) hnativeζ hμE hloss hMmass
      (card_le_outputBudget (hH₂0 k) (hRst0 k).le (hlist0 k) (bud.discrepancy_one k) hd0 hd1.le)

end

end Submission.Obl.k4_narrow_projected_row_parents
