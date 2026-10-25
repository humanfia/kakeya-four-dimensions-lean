import Submission.Obl.k4_general_parent_projected_layers.Support.TerminalMeshConditions
import Submission.Obl.k4_general_parent_projected_layers.Support.TerminalBudgetPowers

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial
open NativeMesh

noncomputable section

/-- Original-law terminal tables, before any conditioning on a coefficient group. -/
structure TerminalTables {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s M m B : ℝ) where
  worlds : Finset (Fin 4 → ℤ)
  retained : Set (α × ℝ)
  tables : (Fin 4 → ℤ) → Finset ((Fin 2 → ℤ) × ℤ)
  measurable : MeasurableSet retained
  cover : ∀ l ∈ a.scalarGoodLabels p k,
    projectedWorldTag (p.N k ^ (-m)) (PreparedModel.narrow p k s) (a.b k l) ∈ worlds
  loss : a.mu k retainedᶜ ≤ ENNReal.ofReal (PreparedModel.width p k s)
  budget : (∑ u ∈ worlds,
    ((p.N k ^ (-m)) * PreparedModel.narrow p k s *
      (a.pi k {v | ⌊v / (p.N k ^ (-m))⌋ = u 0}).toReal) *
      (((tables u).card : ℝ) * (p.N k ^ (-M)) ^ 2) *
        (PreparedModel.width p k s) ^ p.d) ≤ B
  support : ∀ u z, z ∈ retained →
    projectedWorldTag (p.N k ^ (-m)) (PreparedModel.narrow p k s) (a.b k z.1) = u →
      u ∈ worlds ∧
      (projectedCell (p.N k ^ (-M)) (PreparedModel.narrow p k s)
        (projectedWorldRepresentatives (p.K k) (p.N k ^ (-m)) (PreparedModel.narrow p k s) u 2)
        (projectedWorldRepresentatives (p.K k) (p.N k ^ (-m)) (PreparedModel.narrow p k s) u 3)
        (a.b k z.1) z.2, ⌊eval (a.x k z.1 z.2) (a.P k) / PreparedModel.width p k s⌋) ∈ tables u

theorem parentFilling_loss_le {K a : ℝ} (hK : 1 ≤ K) (ha : 0 < a) :
    K * (parentFilling K a)⁻¹ ≤ a := by
  have hK0 : 0 < K := by linarith
  have hpow : K ≤ K ^ 20 := by
    simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 20)
  have hden : 0 < 3000000 * K ^ 20 := by positivity
  calc
    _ = (K / (3000000 * K ^ 20)) * a := by
      unfold parentFilling
      field_simp <;> ring
    _ ≤ 1 * a := mul_le_mul_of_nonneg_right ((div_le_one hden).mpr (by nlinarith)) ha.le
    _ = a := one_mul _

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- The terminal mesh depends on the prepared geometry and positive depth
interval, and is fixed before any later Scalar output tolerance is chosen. -/
theorem eventually_terminal_tables (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p) (hcaps : a.Caps p) (hatlases : a.Atlases p) :
    ∃ L : ℝ, 4 < L ∧ ∀ a₀ m : ℝ, 0 < a₀ → L * a₀ < m →
      ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, ∀ s : ℝ,
        a₀ ≤ s → s ≤ 2 * a₀ → s ≤ p.U →
          Nonempty (TerminalTables p a k s (L * a₀ / 2) m (p.N k ^ ξ)) := by
  classical
  obtain ⟨J, C, hC, hsupport⟩ := finite_mesh_prepared_terminal_support (α := α) 1
  let L := projectionMeshExponent J C p.kappa p.ell
  have hL : 4 < L := by
    dsimp [L, projectionMeshExponent]
    have hk : 0 < p.kappa := hp.2.2.2.2.2.1
    have hl : 0 < p.ell := hp.2.2.2.2.2.2.2.1
    nlinarith [Nat.cast_nonneg (α := ℝ) J, Nat.cast_nonneg (α := ℝ) C]
  refine ⟨L, hL, ?_⟩
  intro a₀ m ha₀ hm ξ hξ
  obtain ⟨r, hr, Hmesh⟩ := eventually_terminal_mesh_conditions p hp a J C ha₀ hm
  let R := max (max 2 r) (max r⁻¹ a₀⁻¹) + 1
  have hR : 1 < R := by
    dsimp [R]
    linarith [le_max_left (2 : ℝ) r, le_max_left (max (2 : ℝ) r) (max r⁻¹ a₀⁻¹)]
  have hRr : r ≤ R := by
    dsimp [R]
    linarith [le_max_right (2 : ℝ) r, le_max_left (max (2 : ℝ) r) (max r⁻¹ a₀⁻¹)]
  have hir : R⁻¹ ≤ r := by
    have hri : r⁻¹ ≤ R := by
      dsimp [R]
      linarith [le_max_left r⁻¹ a₀⁻¹, le_max_right (max (2 : ℝ) r) (max r⁻¹ a₀⁻¹)]
    have hh := inv_anti₀ (inv_pos.mpr hr) hri
    simpa only [inv_inv] using hh
  have hia : R⁻¹ ≤ a₀ := by
    have hai : a₀⁻¹ ≤ R := by
      dsimp [R]
      linarith [le_max_right r⁻¹ a₀⁻¹, le_max_right (max (2 : ℝ) r) (max r⁻¹ a₀⁻¹)]
    have hh := inv_anti₀ (inv_pos.mpr ha₀) hai
    simpa only [inv_inv] using hh
  filter_upwards [Hmesh, a.eventually_pure_base_caps p hp hcommon hcaps hR,
    hatlases R hR, eventually_terminalBudget_le p hp hξ] with k hkmesh hkcap hkatlas hkbudget
  intro s hslo hshi hsU
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 ≤ p.K k := by linarith [hp.2.2.1.1 k]
  have hs : 0 ≤ s := ha₀.le.trans hslo
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have had : 0 < (width p k s) ^ p.d := Real.rpow_pos_of_pos ha _
  have hσ : 0 < p.N k ^ (-(L * a₀ / 2)) := Real.rpow_pos_of_pos hN _
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hatlas : a.AtlasAt p R k s := hkatlas s (hia.trans hslo) hsU
  have hmsh := hkmesh R s hslo hshi hatlas
  obtain ⟨Q, _, hQ⟩ := finite_projected_worlds (a.scalarGoodLabels p k) (a.b k) hK hχ hg
    (fun l hl => hl.1)
  obtain ⟨E, F, hE, hloss, hbudget, htable⟩ := hsupport p hp a hcommon R k s hs hatlas
    (p.N k ^ (-r)) (p.N k ^ (-(L * a₀ / 2))) (p.N k ^ (-m))
    (Real.rpow_pos_of_pos hN _) hσ hχ hmsh.sigma_le_time hmsh.major_le_time
    hmsh.major_le_packet hmsh.root_small hmsh.resolution hmsh.oscillation
    (hkcap r hir hRr) Q hQ
  refine ⟨⟨Q, E, F, hE, hQ, ?_, ?_, htable⟩⟩
  · apply hloss.trans
    rw [pow_one, ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (parentFilling_loss_le (hp.2.2.1.1 k) ha)
  · rw [← Finset.sum_mul]
    calc
      _ ≤ (terminalBudgetConstant (p.K k) * p.K k / (width p k s) ^ p.d) *
          (width p k s) ^ p.d := mul_le_mul_of_nonneg_right hbudget had.le
      _ = terminalBudgetConstant (p.K k) * p.K k := div_mul_cancel₀ _ had.ne'
      _ ≤ _ := hkbudget

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
