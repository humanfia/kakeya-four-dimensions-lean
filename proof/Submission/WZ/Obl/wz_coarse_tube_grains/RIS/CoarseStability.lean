-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoarseStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.WeightedStability
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoverMass
import Submission.WZ.Obl.wz_concentrated_convex_factorization.TubeBounds

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Finset
open wz_concentrated_convex_factorization (Upper coefficient)

/-- The variational coefficient is bounded uniformly on nonempty subfamilies, without
requiring the coarse tubes to lie in the unit ball. -/
theorem coarse_coefficient_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space)
    (R : Finset (Fin N)) (hR : R.Nonempty) :
    1 ≤ coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) R ∧
      coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) R ≤ N / ρ := by
  have hcard : (1 : ℝ) ≤ R.card := by exact_mod_cast card_pos.mpr hR
  have hc : 1 ≤ (R.card : ℝ) / ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hupper := wz_concentrated_convex_factorization.tube_family_upper hρ y w R
  refine ⟨wz_concentrated_convex_factorization.one_le_coefficient hc hupper, ?_⟩
  exact (wz_concentrated_convex_factorization.coefficient_le hc hupper).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast (show R.card ≤ N from by simpa using R.card_le_univ)) hρ.le)

/-- Mass-regularized stable selection for an arbitrary family of coarse tubes.
The selected tubes need not be contained in the unit ball. -/
theorem stable_coarse_tubes {ρ U θ r η : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space)
    (S : Finset (Fin N)) (a : Fin N → ℝ)
    (hU : 0 < U) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r)
    (ha : ∀ k ∈ S, a k ≤ U) (hmass : 0 < ∑ k ∈ S, a k)
    (htail : θ * U * S.card ≤ (∑ k ∈ S, a k) / 2)
    (q p : ℕ) (hp : 0 < p) (hgrid : 2 ≤ θ * r ^ q) (hη : 0 ≤ η)
    (hsmall : η ^ p * (N / ρ) ≤ 1) :
    ∃ Q : Finset (Fin N), Q ⊆ S ∧ Q.Nonempty ∧
      η * (∑ k ∈ S, a k) ≤ 2 * r * (q + 1 : ℝ) * ∑ k ∈ Q, a k ∧
      (∀ k ∈ Q, ∀ k' ∈ Q, a k ≤ r * a k') ∧
      (∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
        coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) Q ≤
          2 ^ p * coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) R) := by
  exact weighted_stable_subfamily S a
    (coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2)) hU hθ hθ1 hr ha hmass htail
    q p hp hgrid hη (fun R _ hR => coarse_coefficient_bounds hρ hρ1 y w R hR) hsmall

namespace Interfaces

/-- A convex-count upper estimate on a selected set gives `K` on any injective enumeration. -/
theorem k_of_upper {ρ c : ℝ} {N M : ℕ} {y w : Fin N → V} {Q : Finset (Fin N)}
    (hupper : Upper (fun k => T ρ (y k) (w k)) (ρ ^ 2) Q c)
    (e : Fin M → Fin N) (he : Function.Injective e) (heQ : ∀ k, e k ∈ Q) :
    K ρ c M (y ∘ e) (w ∘ e) := by
  classical
  intro W hW
  apply le_trans _ (hupper W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ρ)
  apply Nat.cast_le.mpr
  have hh := Set.ncard_le_ncard_of_injOn e
    (s := {k | T ρ (y (e k)) (w (e k)) ⊆ W})
    (t := {k | k ∈ Q ∧ T ρ (y k) (w k) ⊆ W})
    (fun k hk => ⟨heQ k, hk⟩) he.injOn (Set.toFinite _)
  simpa only [Function.comp_apply, ← Finset.coe_filter, Set.ncard_coe_finset,
    wz_concentrated_convex_factorization.count] using hh

/-- The small-coefficient branch of the stable coarse selection gives the exact refined
alternative. This is the refinement branch of Step 1 in the corrected gain argument. -/
theorem refined_of_small_coefficient {ζ δ ρ η h τ m l : ℝ} {n N M : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hτζ : τ ≤ ζ) (hhζ : h ≤ ζ)
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (Q : Finset (Fin N)) (hQ : Q.Nonempty) (hM : 0 < M)
    (e : Fin M → Fin N) (he : Function.Injective e) (heQ : ∀ k, e k ∈ Q)
    (hsmall : coefficient (fun k => T ρ (y k) (w k)) (ρ ^ 2) Q ≤ δ ^ (-ζ))
    (hbudget : 384 * δ ^ (-(τ + η + 2 * h)) ≤ δ ^ (-ζ))
    (hkeep : o (δ ^ τ) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S with f i ∈ Set.range e, μ (Z i)) :
    Refined ζ δ ρ n x v Y S Z := by
  have hcard : (1 : ℝ) ≤ Q.card := by exact_mod_cast Finset.card_pos.mpr hQ
  have hc : 1 ≤ (Q.card : ℝ) / ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hupper := wz_concentrated_convex_factorization.coefficient_upper (sq_nonneg ρ) hc
    (wz_concentrated_convex_factorization.tube_family_upper hρ y w Q)
  exact refined_of_retained_cover hδ hδ1 hτζ hhζ hA hC hM e he
    (k_of_upper (hupper.mono hsmall) e he heQ) hbudget hkeep

end Interfaces

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
