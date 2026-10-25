-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.ResidualPrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.ResidualPreparation
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.EnlargedInput

/-! A local enlarged prism in every substantial residual shading. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Residual preparation and brush selection, assembled with explicit numerical
budgets for the later power bookkeeping. -/
theorem residual_enlarged_prism {n N J : ℕ} {d h ρ a c b g m₀ lam m r ω ζ τ L R : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hm : 0 < m) (hdr : d ≤ r) (hrρ : r ≤ ρ) (hL : 100000000*c ≤ L)
    (hLpos : 0 < L) (hL1 : L/8 ≤ 1) (hdL : d ≤ L/64) (hdR : d ≤ R)
    (hLR : 4*L ≤ R) (hendpoint : 4608*R ≤ lam)
    (hretaincost : 32 ≤ d^(-τ)) (hsmallcap : d^(-(h+τ))*(r/ρ)^(ω*ζ/100) ≤ 1/2)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (hTI : ∀ i, T d (x i) (v i) ⊆ ball (0:V) 1)
    (S : Finset (Fin n)) (Z Y : Fin n → Set V) (f : Fin n → Fin N)
    (y w : Fin N → V) (z : Fin J → V) (e : Fin J → V ≃ₗᵢ[ℝ] V)
    (G : Fin J → Set V) (γ : Fin J → Fin N)
    (hHB : HB d h n x v S Z ρ N y w f a c b g J z e G γ m₀)
    (hZS : ∀ i, i ∉ S → Z i = ∅)
    (hZm : ∀ i, MeasurableSet (Z i)) (hYm : ∀ i, MeasurableSet (Y i))
    (hZT : ∀ i, Z i ⊆ T d (x i) (v i)) (hYZ : ∀ i, Y i ⊆ Z i)
    (hretain : (1/2 : ENNReal) * (∑ i, volume (Z i)) ≤ ∑ i, volume (Y i))
    (hmin : O (32*lam*(n : ℝ)*d^2) ≤ ∑ i, volume (Z i))
    (hBr : Broad ω ζ d h ρ n N v S Z f)
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ))
    (hcoarse : ∀ i ∈ S, T d (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) :
    ∃ (k : Fin N) (z' : V) (e' : V ≃ₗᵢ[ℝ] V) (F : Finset (Fin n)) (Q : Fin n → Set V),
      F.Nonempty ∧ lam*m*c*r ≤ 320000000000000000000*d*(L/c)^3*(F.card : ℝ) ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope (ρ*c) c*L ∧
      10000*enlargedSlope (ρ*c) c*L ≤ L ∧
      (∀ i, MeasurableSet (Q i) ∧ Q i ⊆ Y i ∩
        P (10000*a) (10000*enlargedSlope (ρ*c) c*L) L z' e' ∧ Q i ⊆ ball z' (L/2)) ∧
      (∀ i p, p ∈ Q i → R < dist p (x i) ∧ R < dist p (x i+v i)) ∧
      (∀ i, i ∉ F → Q i = ∅) ∧
      ∀ i ∈ F, O (lam*L*d^2/256) ≤ volume (Q i) ∧
        T d (x i) (v i) ⊆ T ρ (y k) (w k) ∧
        Crosses d (10000*a) (10000*enlargedSlope (ρ*c) c*L) L (x i) (v i) z' e' := by
  obtain ⟨U, W, hU, hW, hends, hreg, hmass, hcount⟩ := prepare_dense_residual
    hd hLpos hL1 hdL hdR hendpoint hlam x v hv f Z Y hZm hYm hZT hYZ hretain hmin
  have hWZ (i) : W i ⊆ Z i := (hW i).2.trans ((hU i).2.trans (hYZ i))
  obtain ⟨hBrW, hlevelW⟩ := retained_broad_and_level hd hZS hWZ hBr hlevel hcount hretaincost
  obtain ⟨k, z', e', F, Q, hF, hcard, hdA, hAB, hBL, hQ, hzero, hgood⟩ :=
    enlarged_input_of_prepared hn hd hlam hlam1 (by positivity : 0 < m/32) hdr hrρ hL
      x v hv hTI S Z W U f y w z e G γ hHB hZS hWZ (fun i => (hW i).2)
      (fun i => (hU i).1) (fun i => (hW i).1) (fun i => (hU i).2.trans ((hYZ i).trans (hZT i)))
      hmass hBrW hsmallcap hlevelW (fun i p hp => ⟨hLR.trans (hends i p hp).1.le,
        hLR.trans (hends i p hp).2.le⟩) hreg hcoarse
  refine ⟨k, z', e', F, Q, hF, ?_, hdA, hAB, hBL, ?_, ?_, hzero, hgood⟩
  · linarith
  · intro i
    exact ⟨(hQ i).1, fun p hp => ⟨(hU i).2 ((hQ i).2.1 hp).1, ((hQ i).2.1 hp).2⟩, (hQ i).2.2⟩
  · intro i p hp
    exact hends i p ((hQ i).2.1 hp).1

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
