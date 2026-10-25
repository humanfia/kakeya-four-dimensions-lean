/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/PreparedTerminalSupport.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentWorldSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentSupportBudget
import Submission.Obl.k4_general_parent_projected_layers.Support.ScalarGoodCrop
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! A finite original-world terminal support after a power-small incidence deletion. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial

noncomputable section

def terminalBudgetConstant (K : ℝ) : ℝ :=
  (10 * K) * (180 * K ^ 2) * terminalAreaConstant K

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem finite_mesh_prepared_terminal_support (A : ℕ) :
    ∃ J C : ℕ, 1 ≤ C ∧ ∀ (p : Parameters), p.Valid →
      ∀ a : PreparedModel α, a.Common p → ∀ (R : ℝ) (k : ℕ) (s : ℝ), 0 ≤ s →
        a.AtlasAt p R k s → ∀ delta sigma chi : ℝ,
          0 < delta → 0 < sigma → 0 < chi → sigma ≤ a.q k s → chi ≤ a.q k s →
          chi ≤ a.q k s * narrow p k s →
          sigma ≤ (parentFilling (p.K k) (width p k s) ^ J)⁻¹ →
          (∀ i e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * delta) ≤ sigma) →
          parentFilling (p.K k) (width p k s) ^ C *
            (24 * p.K k ^ 2 * (sigma + chi) / (a.q k s * narrow p k s)) ≤ width p k s →
          (∀ q : Fin 3 → ℤ,
            a.mu k {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q} ≤
              ENNReal.ofReal ((4 * p.K k + 2) * p.K k * delta ^ 3)) →
          ∀ Q : Finset (Fin 4 → ℤ),
            (∀ l ∈ a.scalarGoodLabels p k, projectedWorldTag chi (narrow p k s) (a.b k l) ∈ Q) →
            ∃ (E : Set (α × ℝ)) (F : (Fin 4 → ℤ) → Finset ((Fin 2 → ℤ) × ℤ)),
              MeasurableSet E ∧
              a.mu k Eᶜ ≤ ENNReal.ofReal (p.K k) *
                ENNReal.ofReal ((parentFilling (p.K k) (width p k s) ^ A)⁻¹) ∧
              (∑ u ∈ Q, (chi * narrow p k s *
                (a.pi k {v | ⌊v / chi⌋ = u 0}).toReal) * ((F u).card * sigma ^ 2)) ≤
                  terminalBudgetConstant (p.K k) * p.K k / (width p k s) ^ p.d ∧
              ∀ u z, z ∈ E → projectedWorldTag chi (narrow p k s) (a.b k z.1) = u →
                u ∈ Q ∧
                (projectedCell sigma (narrow p k s)
                  (projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 2)
                  (projectedWorldRepresentatives (p.K k) chi (narrow p k s) u 3) (a.b k z.1) z.2,
                  ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋) ∈ F u := by
  classical
  obtain ⟨J, C, hC, hpart⟩ := finite_mesh_prepared_parent_support (α := α) A
  refine ⟨J, C, hC, ?_⟩
  intro p hp a hcommon R k s hs hatlas delta sigma chi hd hσ hchi hσq hchiq hchiqg
    hσJ hresolve hsmall hcap Q hQ
  have hK : 0 ≤ p.K k := (zero_le_one : (0 : ℝ) ≤ 1).trans (hp.2.2.1.1 k)
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have hH : 0 ≤ parentFilling (p.K k) (width p k s) := by unfold parentFilling; positivity
  have hgood := a.measurableSet_scalarGoodLabels p k (hcommon k).1
  have haegood := a.ae_scalarGoodLabels p hcommon k
  choose E₀ hE₀m hE₀parent hE₀disj hE₀loss hE₀osc using fun i =>
    hpart p hp a hcommon R k s hs hatlas i delta sigma hd hσ hσJ (hresolve i) hcap
  let E₁ (i : Fin (a.n k s)) (e : Fin 2) := E₀ i e ∩ {z | z.1 ∈ a.scalarGoodLabels p k}
  have hE₁m (i : Fin (a.n k s)) (e : Fin 2) : MeasurableSet (E₁ i e) :=
    (hE₀m i e).inter (hgood.preimage measurable_fst)
  have hE₁parent (i : Fin (a.n k s)) (e : Fin 2) : E₁ i e ⊆ a.parentSet k s i :=
    fun _ hz => hE₀parent i e hz.1
  have hE₁loss (i : Fin (a.n k s)) : a.mu k (a.parentSet k s i \ ⋃ e, E₁ i e) ≤
      a.mu k (a.parentSet k s i) *
        ENNReal.ofReal ((parentFilling (p.K k) (width p k s) ^ A)⁻¹) := by
    have hsub : a.parentSet k s i \ ⋃ e, E₁ i e ≤ᵐ[a.mu k]
        a.parentSet k s i \ ⋃ e, E₀ i e := by
      filter_upwards [haegood] with z hz
      rintro ⟨hzparent, hznot⟩
      refine ⟨hzparent, ?_⟩
      intro he
      obtain ⟨e, he⟩ := mem_iUnion.mp he
      exact hznot (mem_iUnion.mpr ⟨e, he, hz⟩)
    exact (measure_mono_ae hsub).trans (hE₀loss i)
  have hfamily (i : Fin (a.n k s)) := a.parent_world_terminal_support p hp hs hatlas
    (hcommon k).2.2.1 i (E₁ i) (hE₁parent i)
    (fun e z hz => hz.2.1) (pow_nonneg hH C) hσ hσq hchi hchiq hchiqg hsmall
    (fun e z hz w hw => hE₀osc i e z hz.1 w hw.1) Q
  choose F₀ hF₀budget hF₀cover using hfamily
  let F (u : Fin 4 → ℤ) := Finset.univ.biUnion (fun i => F₀ i u)
  let E := ⋃ i, ⋃ e, E₁ i e
  have hE : MeasurableSet E := MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (hE₁m i))
  have hloss : a.mu k Eᶜ ≤ ENNReal.ofReal (p.K k) *
      ENNReal.ofReal ((parentFilling (p.K k) (width p k s) ^ A)⁻¹) := by
    apply finite_parent_loss_union (a.mu k) (fun i => a.parentSet k s i)
      (fun i => ⋃ e, E₁ i e) _ _
    · exact hatlas.2.2.2.2.2.1
    · exact a.sum_original_parent_mass_le p hp hcommon hatlas
    · exact hE₁loss
  have hCbudget : 0 ≤ terminalBudgetConstant (p.K k) := by
    unfold terminalBudgetConstant terminalAreaConstant
    positivity
  have hbudget := a.weighted_terminal_support_budget p hp hcommon hatlas hCbudget
    (fun i => ∑ u ∈ Q, (chi * narrow p k s * (a.pi k {v | ⌊v / chi⌋ = u 0}).toReal) *
      ((F₀ i u).card * sigma ^ 2))
    (fun i => by simpa only [terminalBudgetConstant, mul_assoc] using hF₀budget i)
  have hsum := weighted_union_terminal_card Q F₀
    (fun u => chi * narrow p k s * (a.pi k {v | ⌊v / chi⌋ = u 0}).toReal)
    (sigma := sigma) (by intro u hu; unfold narrow; positivity)
  refine ⟨E, F, hE, hloss, hsum.trans hbudget, ?_⟩
  intro u z hz htag
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  obtain ⟨e, hz⟩ := mem_iUnion.mp hzi
  have hu : u ∈ Q := by simpa only [htag] using hQ z.1 hz.2
  refine ⟨hu, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hF₀cover i u hu e z hz htag⟩

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
