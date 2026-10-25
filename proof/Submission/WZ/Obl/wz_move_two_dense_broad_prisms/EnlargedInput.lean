-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.EnlargedInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.GrainRefinement
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.EnlargedShading

/-! From a prepared residual to a locally dense enlarged prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- The geometric part of Step 3, through selection of the initial enlarged
prism, with all quantitative factors explicit. -/
theorem enlarged_input_of_prepared {n N J : ℕ} {d h ρ a c b g m₀ lam m r ω ζ h' L : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hm : 0 < m) (hdr : d ≤ r) (hrρ : r ≤ ρ) (hL : 100000000*c ≤ L)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (hTI : ∀ i, T d (x i) (v i) ⊆ ball (0:V) 1)
    (S : Finset (Fin n)) (Z W U : Fin n → Set V) (f : Fin n → Fin N)
    (y w : Fin N → V) (z : Fin J → V) (e : Fin J → V ≃ₗᵢ[ℝ] V)
    (G : Fin J → Set V) (γ : Fin J → Fin N)
    (hHB : HB d h n x v S Z ρ N y w f a c b g J z e G γ m₀)
    (hZS : ∀ i, i ∉ S → Z i = ∅) (hWZ : ∀ i, W i ⊆ Z i)
    (hWU : ∀ i, W i ⊆ U i) (hUm : ∀ i, MeasurableSet (U i))
    (hWm : ∀ i, MeasurableSet (W i)) (hUT : ∀ i, U i ⊆ T d (x i) (v i))
    (hmass : O (lam*(n : ℝ)*d^2) ≤ ∑ i, volume (W i))
    (hBr : Broad ω ζ d h' ρ n N v S W f)
    (hsmallcap : d^(-h')*(r/ρ)^(ω*ζ/100) ≤ 1/2)
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ W i}.ncard : ℝ))
    (hends : ∀ i p, p ∈ U i → 4*L ≤ dist p (x i) ∧ 4*L ≤ dist p (x i+v i))
    (hreg : ∀ i p, p ∈ U i → O (lam*L*d^2/256) ≤ volume (U i ∩ ball p (L/8)))
    (hcoarse : ∀ i ∈ S, T d (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) :
    ∃ (k : Fin N) (z' : V) (e' : V ≃ₗᵢ[ℝ] V) (F : Finset (Fin n)) (Q : Fin n → Set V),
      F.Nonempty ∧ lam*m*c*r ≤ 10000000000000000000*d*(L/c)^3*(F.card : ℝ) ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope (ρ*c) c*L ∧
      10000*enlargedSlope (ρ*c) c*L ≤ L ∧
      (∀ i, MeasurableSet (Q i) ∧ Q i ⊆ U i ∩
        P (10000*a) (10000*enlargedSlope (ρ*c) c*L) L z' e' ∧ Q i ⊆ ball z' (L/2)) ∧
      (∀ i, i ∉ F → Q i = ∅) ∧
      ∀ i ∈ F, O (lam*L*d^2/256) ≤ volume (Q i) ∧
        T d (x i) (v i) ⊆ T ρ (y k) (w k) ∧
        Crosses d (10000*a) (10000*enlargedSlope (ρ*c) c*L) L (x i) (v i) z' e' := by
  have hc : 0 < c := hd.trans_le (hHB.1.trans (hHB.2.1.trans hHB.2.2.1))
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hc).mp (by simpa using hHB.2.2.1)
  obtain ⟨hWS, hGP, hcover, hcross⟩ := refined_grain_geometry hHB hZS hWZ
  obtain ⟨j, H, hH, hHcard, hHgood⟩ := exists_populated_crossed_grain hn hd hc hHB.2.2.2.1
    hHB.2.1 hHB.2.2.1 hlam hlam1 hm hdr hrρ hρ1 x v hv S W f hWm
    (fun i => (hWU i).trans (hUT i)) (fun i => (hWU i).trans ((hUT i).trans (hTI i))) hWS
    hmass hBr hsmallcap hlevel z e G γ hGP hcover hcross
  obtain ⟨F, e', Q, hF, hFH, hFcard, hdA, hAB, hBL, hQ, hzero, hgood⟩ :=
    enlarged_shading_selection hd hHB.1 hHB.2.1 hHB.2.2.1 hHB.2.2.2.1 hL
      (show 0 < lam*d^2 by positivity) x v hv (z j) (e j) H hH U hUm hUT
      (fun i hi => (hHgood i hi).2.2.2) (fun i hi => by
        obtain ⟨p, hpW, hpG⟩ := (hHgood i hi).2.2.1
        exact ⟨p, ⟨hWU i hpW, hGP j hpG⟩, hends i p (hWU i hpW)⟩)
      (fun i p hp => by convert hreg i p hp using 1 <;> congr 1 <;> ring)
  refine ⟨γ j, z j, e', F, Q, hF, ?_, hdA, hAB, hBL, hQ, hzero, ?_⟩
  · calc
      _ ≤ 10000000000*d*(H.card : ℝ) := hHcard
      _ ≤ 10000000000*d*(1000000000*(L/c)^3*(F.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hFcard (by positivity)
      _ = _ := by ring
  · intro i hi
    have hgi := hgood i hi
    have hHi := hHgood i (hFH hi)
    refine ⟨?_, ?_, hgi.2⟩
    · convert hgi.1 using 1 <;> congr 1 <;> ring
    · simpa only [hHi.2.1] using hcoarse i hHi.1

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
