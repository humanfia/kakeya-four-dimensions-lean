-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.NonconcentratedFromStep
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SetThinTubes
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nonconcentrated_dot_products`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nonconcentrated_dot_products/`
belong to this obligation.
-/

open WangZahlLot.Obl.wz_nonconcentrated_dot_products in
theorem WangZahlLot.wz_nonconcentrated_dot_products : (∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C d : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ C → 0 < d → ∀ (F Λ : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), F.Finite → Λ.Finite → (∀ θ ∈ Λ, ‖θ‖ = 1) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((F ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * F.ncard ∧ ((Λ ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * Λ.ncard) → H ⊆ Λ ×ˢ F → H.Nonempty → d * Λ.ncard * F.ncard ≤ H.ncard → ∃ θ ∈ Λ, ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ a, (θ, a) ∈ H ∧ t = inner ℝ θ a} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → d ^ 3 * δ ^ (ε - 1) ≤ C ^ 2 * m) → (∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ TT, TT = (fun (δ σ K c : ℝ) (G G' : Set (EuclideanSpace ℝ (Fin 2))) => ∃ T : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), T ⊆ G ×ˢ G' ∧ (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) ∧ ∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r → ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ M δ₀ : ℝ, 0 < τ ∧ 1 ≤ M ∧ 0 < δ₀ ∧ ∀ δ σ c K C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C → ∀ G G' : Set (EuclideanSpace ℝ (Fin 2)), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → TT δ σ K c G G' → TT δ σ K c G' G → TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G G' ∧ TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G' G) → ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-κ)) F → Fr δ (δ ^ (-κ)) G → Fr δ (δ ^ (-κ)) G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → (∀ (e : EuclideanSpace ℝ (Fin 2)) (c r : ℝ), ‖e‖ = 1 → δ ≤ r → ({b ∈ G | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G.ncard ∧ ({b ∈ G' | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G'.ncard) → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ α * F.ncard * G.ncard * G'.ncard ≤ H.ncard → ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → δ ^ (ε - 1) ≤ (m : ℝ) := by
  classical
  intro _kaufman osw Fr hFr ε hε hε1
  subst Fr
  obtain ⟨τ, M, dO, hτ, hM, hdO, hstep⟩ :=
    osw BoundedSetFrostman rfl SetThinTubes rfl (ε / 100) (by positivity)
  obtain ⟨κ, hκ, hnc⟩ := nonconcentrated_dot_products_of_step hε hε1.le hτ hM
  refine ⟨κ, hκ, ?_⟩
  intro ζ hζ hζ1
  obtain ⟨α, dN, hα, hdN, hN⟩ := hnc ζ hζ hζ1.le
  refine ⟨α, min dN (min dO 1), hα, by positivity, ?_⟩
  intro δ hδ hsmall F G U H hF hG hU hsep hline hH hHne hden
  change BoundedSetFrostman δ (δ ^ (-κ)) F at hF
  change BoundedSetFrostman δ (δ ^ (-κ)) G at hG
  change BoundedSetFrostman δ (δ ^ (-κ)) U at hU
  have hδN : δ ≤ dN := hsmall.trans (min_le_left _ _)
  have hδO : δ ≤ dO := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hC : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hHfin : H.Finite := (hF.1.prod (hG.1.prod hU.1)).subset hH
  let Ff := hF.1.toFinset
  let Gf := hG.1.toFinset
  let Uf := hU.1.toFinset
  let Hf := hHfin.toFinset
  have hFf : (↑Ff : Set Plane) = F := hF.1.coe_toFinset
  have hGf : (↑Gf : Set Plane) = G := hG.1.coe_toFinset
  have hUf : (↑Uf : Set Plane) = U := hU.1.coe_toFinset
  have hHf : (↑Hf : Set Triple) = H := hHfin.coe_toFinset
  have hFc : Ff.card = F.ncard := (Set.ncard_eq_toFinset_card F hF.1).symm
  have hGc : Gf.card = G.ncard := (Set.ncard_eq_toFinset_card G hG.1).symm
  have hUc : Uf.card = U.ncard := (Set.ncard_eq_toFinset_card U hU.1).symm
  have hHc : Hf.card = H.ncard := (Set.ncard_eq_toFinset_card H hHfin).symm
  have hFrostF : ClosedFiniteFrostman δ (δ ^ (-κ)) Ff := by
    simpa only [ClosedFiniteFrostman, hFf, hFc] using hF.2.2
  have hFrostG : ClosedFiniteFrostman δ (δ ^ (-κ)) Gf := by
    simpa only [ClosedFiniteFrostman, hGf, hGc] using hG.2.2
  have hFrostU : ClosedFiniteFrostman δ (δ ^ (-κ)) Uf := by
    simpa only [ClosedFiniteFrostman, hUf, hUc] using hU.2.2
  have hLineG : IndexedLineFrostman δ (δ ^ (-κ)) ζ (fun b : Gf => (b : Plane)) := by
    apply indexedLineFrostman_iff_ncard.mpr
    simpa only [hGf] using fun e c r he hr => (hline e c r he hr).1
  have hLineU : IndexedLineFrostman δ (δ ^ (-κ)) ζ (fun b : Uf => (b : Plane)) := by
    apply indexedLineFrostman_iff_ncard.mpr
    simpa only [hUf] using fun e c r he hr => (hline e c r he hr).2
  have hSep : ∀ b ∈ Gf, ∀ x ∈ Uf, 1 / 4 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8 := by
    intro b hb x hx
    have hb' : b ∈ G := hGf ▸ hb
    have hx' : x ∈ U := hUf ▸ hx
    refine ⟨by simpa only [dist_eq_norm] using hsep b hb' x hx', ?_⟩
    exact (norm_sub_le b x).trans (by linarith [(hG.2.1 b hb').1, (hU.2.1 x hx').1])
  have hSub : Hf ⊆ Ff ×ˢ (Gf ×ˢ Uf) := by
    intro p hp
    have hp' : p ∈ H := hHf ▸ hp
    have hp'' := hH hp'
    simpa only [← hFf, ← hGf, ← hUf, Set.mem_prod, Finset.mem_coe, Finset.mem_product] using hp''
  have hNe : Hf.Nonempty := by simpa only [← hHf, Finset.coe_nonempty] using hHne
  have hDensity : δ ^ α * (Gf.card : ℝ) * (Uf.card : ℝ) * (Ff.card : ℝ) ≤ (Hf.card : ℝ) := by
    rw [hFc, hGc, hUc, hHc]
    convert hden using 1 <;> ring
  have hBoot : ∀ σ K c : ℝ, 1 / 4 ≤ σ → σ ≤ 1 - ε / 100 → 1 ≤ K → 0 < c → c < 1 / 10 →
      SymmetricThinTubes δ σ K c (fun b : Gf => (b : Plane)) (fun x : Uf => (x : Plane)) →
      SymmetricThinTubes δ (σ + τ) ((δ ^ (-κ) * K / c) ^ M) (4 * c)
        (fun b : Gf => (b : Plane)) (fun x : Uf => (x : Plane)) := by
    intro σ K c hσ hσε hK hc hc1 ht
    have htG : SetThinTubes δ σ K c G U := by simpa only [hGf, hUf] using ht.1.to_set
    have htU : SetThinTubes δ σ K c U G := by simpa only [hGf, hUf] using ht.2.to_set
    have hs := hstep δ σ c K (δ ^ (-κ)) hδ hδO hσ hσε hc hc1 hK hC
      G U hG hU hsep htG htU
    have hsG : SetThinTubes δ (σ + τ) ((δ ^ (-κ) * K / c) ^ M) (4 * c)
        (↑Gf : Set Plane) (↑Uf : Set Plane) := by simpa only [hGf, hUf] using hs.1
    have hsU : SetThinTubes δ (σ + τ) ((δ ^ (-κ) * K / c) ^ M) (4 * c)
        (↑Uf : Set Plane) (↑Gf : Set Plane) := by simpa only [hGf, hUf] using hs.2
    exact ⟨hsG.to_indexed, hsU.to_indexed⟩
  have hresult := hN δ hδ hδN Ff Gf Uf Hf hFrostF hFrostG hFrostU
    hLineG hLineU hSep hSub hNe hDensity hBoot
  simpa only [CoverLower, Covers, DotSet, hHf] using hresult
