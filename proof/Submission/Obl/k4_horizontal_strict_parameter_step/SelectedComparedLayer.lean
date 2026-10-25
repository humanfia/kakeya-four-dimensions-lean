import Submission.Obl.k4_horizontal_strict_parameter_step.ComparedLayer
import Submission.Obl.k4_horizontal_strict_parameter_step.LayerLoss
import Submission.Obl.k4_horizontal_strict_parameter_step.SelectedChart
import Submission.Obl.k4_horizontal_strict_parameter_step.SelectedEvents
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeDepthGrid
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeSelectedRows

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- Assemble the comparison half from actual native block selection and a
finite original depth grid. The chart events record every null exception;
their whole trajectory assignments retain the original floors. -/
theorem comparedLayer_of_selected {δ E M cutoff : ℝ}
    (parent : cfg.AssignmentLevel k s) (g : NativeDepthGrid (cfg.N k) s E)
    (child : ∀ j, cfg.AssignmentLevel k (g.depth j))
    (L : ∀ j, NativeAffineTable cfg k (g.depth j))
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (hchoice : ∀ h block i, choice h block = some i →
      c.paired M cutoff h i ∧ cfg.j k s i = block)
    (G : Set (α × ℝ)) (hG : MeasurableSet G)
    (hGprop : ∀ p ∈ G, ∀ j,
      (∃ i, p.1 ∈ cfg.B k (g.depth j) i ∧
        p.2 ∈ Data.I (cfg.T k (g.depth j)) (cfg.j k (g.depth j) i)) ∧
      ∀ block block' : Fin (2 ^ cfg.T k (g.depth j)),
        p.2 ∈ Data.I (cfg.T k (g.depth j)) block →
        p.2 ∈ Data.I (cfg.T k (g.depth j)) block' → block = block')
    (hnest : ∀ j (i : Fin (cfg.n k (g.depth j))), ∃ a : Fin (cfg.n k s),
      cfg.A k (g.depth j) i ⊆ cfg.A k s a ∧
      Data.I (cfg.T k (g.depth j)) (cfg.j k (g.depth j) i) ⊆
        Data.I (cfg.T k s) (cfg.j k s a))
    (ρ τ : Measure (α × ℝ)) (hσρ : σ ≤ ρ) (hτ : τ ≤ σ)
    (hτmass : ENNReal.ofReal (cfg.N k ^ (-δ)) ≤ τ univ)
    (hτG : ∀ᵐ p ∂τ, p ∈ G)
    (hτcover : ∀ᵐ p ∂τ, ∃ h i, p.1 ∈ c.AH h ∧ p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ choice h (cfg.j k s i) = some i)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 2 ≤ cfg.N k) (hK : 3 ≤ cfg.K k)
    (hd : 0 ≤ cfg.d) (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ)
    (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s) (ha : c.a = cfg.N k ^ (-s))
    (hM : c.M = 8 * cfg.K k ^ 4) (hεδ : c.ε ≤ δ)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hlarge : 69120 * cfg.K k ^ 8 ≤ cfg.N k)
    (hDq : ∀ j, c.D ≤ cfg.timeLength k (g.depth j) ^ 2)
    (hcap : ∀ j, ∀ u ∈ ({s, g.depth j} : Set ℝ), ∀ (Q : Fin 3 → ℤ) (a : ℤ),
      cfg.μ k {ω | cfg.z k (cfg.N k) (g.depth j + 2) ω = Q ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-u)⌋ = a} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * (g.depth j + 2) - cfg.d * u)))
    (hcontactBudget : ∀ j, 16 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤
      cfg.N k ^ (-g.depth j))
    (hroom : ∀ j, 14155776 * cfg.K k ^ 10 * c.D ≤
      (cfg.N k ^ (-g.depth j) / cfg.N k ^ (-s)) * cfg.timeLength k (g.depth j) ^ 2)
    (hMp : 0 ≤ M) (hprod : NativeProductComparison c M)
    (hrow : 4 * (M / c.a) ≤ cfg.N k ^ δ)
    (hcount : 6 * (811008 * cfg.K k ^ 12) ≤ cfg.N k ^ δ) :
    Nonempty (ComparedLayer cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ρ δ c.D c.a
      (cfg.N k ^ (-E))) := by
  have hNp : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hap : 0 < c.a := by rw [ha]; exact Real.rpow_pos_of_pos hNp _
  let Ev := fun h => c.selectedEvent choice G h
  have hsupp (h : Fin c.m) : ∀ t w : ℝ, cfg.N k ^ (-E) ≤ w → w ≤ 1 →
      ∃ C : Finset ℤ, (C.card : ℝ) ≤ 6 * (811008 * cfg.K k ^ 12) * w ^ (-cfg.d) ∧
        ∀ l, (l, t) ∈ Ev h →
          ⌊FirstJet.scal ((c.selectedChart choice Ev h).y (cfg.b k) (cfg.N k ^ (-s)) c.D)
            ((c.selectedChart choice Ev h).β (cfg.b k) (cfg.N k ^ (-s)) c.D)
            ((c.selectedChart choice Ev h).γ (cfg.b k) (cfg.N k ^ (-s)) c.D)
            (c.selectedF choice h) l t / w⌋ ∈ C := by
    apply g.scalar_support hNp (by positivity : 0 ≤ 811008 * cfg.K k ^ 12) hd
      (Ev h) _
    intro t j
    apply c.selectedChart_support_at_child parent (child j) (L j) choice Ev h
      (fun p hp => hp.2) (fun p hp => (hGprop p hp.1 j).1)
      (fun p hp => (hGprop p hp.1 j).2) (hnest j) hν hN hK hℓ hκ hκ1
      (hs.trans (g.depth_mem j).1) (g.depth_mem j).1 ha hM hdom hlarge (hDq j)
      (hcap j) (hcontactBudget j) (hroom j)
  refine ⟨{
    ρH := σ
    ρH_le := hσρ
    n := c.m
    A := c.AH
    q := c.group
    h := c.hH
    layer := c.layer.mono_loss hN1 hap.le hεδ
    σ := τ
    σ_le := hτ
    σ_mass := hτmass
    F := c.selectedF choice
    E := Ev
    measurable_F := c.measurable_selectedF choice
    bound_F := fun h t e => (c.selectedF_bound hap hMp hprod choice hchoice h t e).trans hrow
    measurableSet_E := c.measurable_selectedEvent parent choice G hG
    E_sub := c.selectedEvent_subset choice G
    conull := c.selectedEvent_conull choice G τ hτ hτG hτcover
    support := ?_ }⟩
  intro h t w hw hw1
  obtain ⟨C, hC, hcov⟩ := hsupp h t w hw hw1
  refine ⟨C, hC.trans (mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by
    have := (Real.rpow_pos_of_pos hNp (-E)).trans_le hw
    positivity) _)), ?_⟩
  simpa only [ha, selectedChart] using hcov

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
