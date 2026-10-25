-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/ProjectedSourceFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedSourceFamilies.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ProjectedCommonPolynomial
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetAffine
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.FiniteOriginalAssignments
import Submission.Obl.k4_general_parent_projected_layers.Layers

/-! Actual projected-label sheet families on a literal common domain. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

def projectedCandidate (G : MvPolynomial (Fin 2) ℝ) (q g m : ℝ) (D : CommonDomain.Code) :
    EuclideanSpace ℂ (Fin 3) → ℂ := cev (CommonDomain.projectedCommonPolynomial G q g m D)

theorem projectedCandidate_at_source (G : MvPolynomial (Fin 2) ℝ)
    {q χ g m : ℝ} (hq : q ≠ 0) (hχ : χ ≠ 0) (hm : m ≠ 0)
    (D : CommonDomain.Code) (x : Fin 3 → ℝ) :
    projectedCandidate G q g m D (emb (WithLp.toLp 2 (CommonDomain.coords q χ g m D x))) =
      ((eval ![x 0, x 2] G : ℝ) : ℂ) := by
  rw [projectedCandidate, cev_emb]
  congr 1
  exact CommonDomain.projectedCommonPolynomial_at_source G hq hχ hm D x

theorem projectedCandidate_sheet {G : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (q g m : ℝ) (D : CommonDomain.Code) :
    IsSheet 4 (projectedCandidate G q g m D) := by
  obtain ⟨P, hP, hdeg, hhol, hrel, hreal⟩ :=
    isSheet_cev ((CommonDomain.projectedCommonPolynomial_degree G q g m D).trans hG)
  exact ⟨P, hP, hdeg.trans (by norm_num), hhol, hrel, hreal⟩

/-- A projected layer gives canonical polynomial sheets on every actual common
domain. Its old assignments stay measurable and disjoint before floor pruning. -/
theorem exists_projected_source_family_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type} [MeasurableSpace α]
      (L : ProjLayer α) (N H d ell La s χ q m aTable : ℝ)
      (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
      (π : Measure ℝ) (ρ μ : Measure (α × ℝ)),
      L.Good N H d ell La s χ b P π ρ → 0 < N → 1 ≤ H →
      0 < χ → 0 < q → q ≤ 1 → 0 < m → q * N ^ (-ell * s) ≤ m → m ≤ L.β →
      (K : NNReal) → 4 * (C * H ^ 3) ≤ K → 4 * (H * N ^ (-s)) ≤ aTable →
      μ univ ≠ 0 → (D : CommonDomain.Code) → (G : Set (α × ℝ)) → MeasurableSet G →
      (∀ z ∈ G, z.2 ∈ Icc (0 : ℝ) 1 ∧ CommonDomain.code q χ (N ^ (-ell * s)) m (b z.1) z.2 = D) →
      (∀ᵐ z ∂μ, z ∈ G ∧ z ∈ L.covered) →
      ∃ F : OriginalSheetFamily μ 4 aTable K
        (fun z => WithLp.toLp 2 (CommonDomain.coords q χ (N ^ (-ell * s)) m D
          (CommonDomain.point (b z.1) z.2)))
        (fun z => eval (Submission.Lib.K4ContactNormalization.point (b z.1) z.2) P),
        F.n = L.n ∧ ∃ decode : Fin F.n → Fin L.n, Function.Injective decode ∧
          (∀ i z, z ∈ F.witness i → z ∈ G ∧ z.1 ∈ L.C (decode i)) ∧
          (∀ i, (F.witness i).Nonempty →
            F.f i = projectedCandidate (L.G (decode i)) q (N ^ (-ell * s)) m D) := by
  obtain ⟨C, hC, hbound⟩ := CommonDomain.exists_projected_common_bound
  refine ⟨C, hC, ?_⟩
  intro α _ L N H d ell La s χ q m aTable b P π ρ μ hgood hN hH hχ hq hq1 hm hqg hmβ
    K hK herr hμ D G hG hsource hcovered
  let g := N ^ (-ell * s)
  have hg : 0 < g := Real.rpow_pos_of_pos hN _
  let W : Fin L.n → Set (α × ℝ) := fun i => G ∩ (L.C i ×ˢ univ)
  have hW (i : Fin L.n) : MeasurableSet (W i) :=
    hG.inter ((hgood.2.2.2.1 i).prod MeasurableSet.univ)
  have hcover : ∀ᵐ z ∂μ, ∃ i, z ∈ W i := by
    filter_upwards [hcovered] with z hz
    obtain ⟨i, hi⟩ := hz.2
    exact ⟨i, hz.1, hi, mem_univ _⟩
  obtain ⟨index, hindex, hassigned, -⟩ := exists_original_first_assignment μ hμ W hW hcover
  let V := firstAssignment W
  have hmember (i : Fin L.n) (z : α × ℝ) (hz : z ∈ V i) : z ∈ G ∧ z.1 ∈ L.C i :=
    ⟨hz.1.1, hz.1.2.1⟩
  let base : α × ℝ → EuclideanSpace ℝ (Fin 3) := fun z =>
    WithLp.toLp 2 (CommonDomain.coords q χ g m D (CommonDomain.point (b z.1) z.2))
  let signal : α × ℝ → ℝ := fun z => eval (Submission.Lib.K4ContactNormalization.point (b z.1) z.2) P
  have hnorm (i : Fin L.n) (z : α × ℝ) (hz : z ∈ V i) : ‖base z‖ ≤ 1 / 8 := by
    obtain ⟨ht, hc⟩ := hsource z (hmember i z hz).1
    dsimp only [base, g]
    rw [← hc]
    exact CommonDomain.coords_norm_le hq hχ hg hm hqg (b z.1) ht
  let candidate := fun i : Fin L.n => projectedCandidate (L.G i) q g m D
  have hrule (i : Fin L.n) (z₀ : α × ℝ) (hz₀ : z₀ ∈ V i) :
      IsSheet 4 (candidate i) ∧
      LipschitzOnWith K (fun x => candidate i (emb x)) (closedBall 0 (1 / 2)) ∧
      ∀ z ∈ V i, ‖(signal z : ℂ) - candidate i (emb (base z))‖ ≤ aTable / 4 := by
    have hGdeg := (hgood.2.2.2.2.2 i).2.1
    have hstrip := (hgood.2.2.2.2.2 i).2.2.1
    have hfit := (hgood.2.2.2.2.2 i).2.2.2.1
    have hsheet : IsSheet 4 (candidate i) := projectedCandidate_sheet hGdeg q g m D
    have hbd : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, ‖candidate i z‖ ≤ C * H ^ 3 := by
      intro z hz
      have ht := (hsource z₀ (hmember i z₀ hz₀).1).1
      have hc := (hsource z₀ (hmember i z₀ hz₀).1).2
      change CommonDomain.code q χ g m (b z₀.1) z₀.2 = D at hc
      have hfull := (hfit z₀.1 (hmember i z₀ hz₀).2).2.2
      have hb := hbound (L.G i) hGdeg H L.β q χ g m z₀.2 (L.u i) (L.v i)
        hH hgood.1 hq hq1 hg hm hqg hmβ (b z₀.1) ht
        (fun r hr => by simpa [Submission.Lib.K4ContactNormalization.point] using (hfull r hr).1)
        hstrip z (by
          have hz' : ‖z‖ < 4 := by simpa only [mem_ball, dist_zero_right] using hz
          exact hz'.le)
      rw [hc] at hb
      exact hb
    have hlip := lipschitz_of_bounded (by positivity : 0 ≤ C * H ^ 3)
      hsheet.choose_spec.2.2.1 hbd
    refine ⟨hsheet, hlip.weaken (show (⟨4 * (C * H ^ 3), by positivity⟩ : NNReal) ≤ K from hK), ?_⟩
    intro z hz
    have hmz := hmember i z hz
    have ht := (hsource z hmz.1).1
    have hf := ((hfit z.1 hmz.2).2.2 z.2 ht).2
    have hid := projectedCandidate_at_source (L.G i) (g := g) hq.ne' hχ.ne' hm.ne' D
      (CommonDomain.point (b z.1) z.2)
    change ‖(signal z : ℂ) - projectedCandidate (L.G i) q g m D (emb (base z))‖ ≤ _
    rw [hid, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hf.trans (by linarith only [herr])
  let F := originalSheetFamilyOfPointRules μ (by norm_num : 1 ≤ 4) aTable K base signal
    index hindex V (measurableSet_firstAssignment W hW) (firstAssignment_disjoint W)
    hassigned hnorm candidate hrule
  refine ⟨F, rfl, id, Function.injective_id, hmember, ?_⟩
  intro i hi
  obtain ⟨z, hz⟩ := hi
  exact witnessCandidate_eq V candidate hz

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
