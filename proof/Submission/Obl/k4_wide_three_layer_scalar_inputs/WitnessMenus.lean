import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses
import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyMenus

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory Finset
open Inherited.Native Inherited.Core

noncomputable section

open scoped Classical

variable {α : Type} [MeasurableSpace α] (W : Context α)

/-- Earlier heavy coarse predictors near the graph of the fixed true
block, over an actual key in the bounded key box. -/
def coarseCandidates (key : Fin 3 → ℤ) : Finset (Fin (W.layers.np 0)) :=
  if key ∈ W.KB then Finset.univ.filter fun j =>
    pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ 0 j
      (W.cfg.j W.k W.s W.i) key ∧
    ∀ e, |sheetKeyCoeff (W.layers.G 0 j) W.a W.χ W.m W.q W.t₀ key e -
      blockKeyCoeff (W.cfg.F W.k W.s W.i) W.a W.χ W.m W.q W.t₀ key e| ≤ W.Mst
  else ∅

theorem coarse_mem_candidates (γ : W.Coarse) :
    W.coarseIndex γ ∈ W.coarseCandidates (W.key γ) := by
  have hk : W.key γ ∈ W.KB := γ.1.1.2
  rw [coarseCandidates, if_pos hk, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, γ.2.1, ?_⟩
  intro e
  rw [abs_sub_comm]
  exact (lt_of_not_ge (fun h => γ.2.2.1 ⟨e, h⟩)).le

/-- Only a bounded transverse menu of short keys can meet a fixed true
block inside one fixed original chart. -/
theorem coarse_key_menu {R' : ℝ}
    (hB : BlocksAt W.cfg.comparisonData W.k W.s R')
    (hK : 1 ≤ W.cfg.K W.k) (hN : 0 < W.cfg.N W.k)
    (hχ : 0 < W.χ) (hχm : W.χ ≤ W.m) (z3 z0 : ℤ) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 14 * W.cfg.K W.k ∧
      ∀ γ : W.Coarse, W.chart γ = (z3, z0) → W.key γ 2 ∈ F := by
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hg : 0 < W.g := Real.rpow_pos_of_pos hN _
  have hm : 0 < W.m := mul_pos hq hg
  have hK0 : 0 ≤ W.cfg.K W.k := by linarith
  have hu : 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 :=
    slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  have ht₀ : W.t₀ ∈ Icc (0 : ℝ) 1 := ⟨hu.1, by linarith [hu.2]⟩
  obtain ⟨F₁, F₂, -, hF₂, hcover⟩ := true_key_menus hK0 hq hg hχ hm ht₀
    (W.cfg.c W.k W.s W.i) (hB.c_bd W.i 4) {z3}
  refine ⟨F₂ z3 z0, ?_, ?_⟩
  · calc ((F₂ z3 z0).card : ℝ) ≤ 4 *
          (W.cfg.K W.k * W.q * W.g + 2 * W.cfg.K W.k * W.χ) / W.m + 2 := hF₂ z3 z0
      _ ≤ 4 * (3 * W.cfg.K W.k * W.m) / W.m + 2 := by
        gcongr
        dsimp only [m] at *
        nlinarith [mul_le_mul_of_nonneg_left hχm hK0]
      _ = 12 * W.cfg.K W.k + 2 := by field_simp; ring
      _ ≤ 14 * W.cfg.K W.k := by linarith
  · intro γ hchart
    obtain ⟨l, hlB, hlC, hk, -⟩ := γ.2.2.2
    have h0 : W.key γ 0 = z3 := congrArg Prod.fst hchart
    have h1 : W.key γ 1 = z0 := congrArg Prod.snd hchart
    have ht : W.t₀ ∈ W.cfg.comparisonData.I
        (W.cfg.comparisonData.T W.k W.s) (W.cfg.comparisonData.j W.k W.s W.i) := by
      rw [I_eq_slot]
      exact ⟨le_rfl, le_add_of_nonneg_right hq.le⟩
    obtain ⟨hZ, hY, -⟩ := hB.geom W.i l ((hB.sets W.i).2.2 hlB) W.t₀ ht
    have hv : ⌊W.cfg.b W.k l 3 / W.χ⌋ ∈ ({z3} : Finset ℤ) := by
      rw [Finset.mem_singleton]
      exact (congrFun hk 0).trans h0
    have hc := hcover (W.cfg.b W.k l) hv hZ hY
    change slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l ∈ keyBox {z3} F₁ F₂ at hc
    rw [hk] at hc
    obtain ⟨⟨v, z, y⟩, hmem, heq⟩ := Finset.mem_image.mp hc
    simp only [Finset.mem_sigma] at hmem
    have hv' : v = z3 := (congrFun heq 0).trans h0
    have hz' : z = z0 := (congrFun heq 1).trans h1
    have hy' : y = W.key γ 2 := congrFun heq 2
    simpa only [hv', hz', hy'] using hmem.2.2

/-- Sum the actual per-key coefficient counts over that transverse menu.
There is no count of velocity bins or long-strip labels here. -/
theorem coarse_menu_of_key_counts {R' C : ℝ}
    (hB : BlocksAt W.cfg.comparisonData W.k W.s R')
    (hK : 1 ≤ W.cfg.K W.k) (hN : 0 < W.cfg.N W.k)
    (hχ : 0 < W.χ) (hχm : W.χ ≤ W.m) (hC : 0 ≤ C)
    (hcount : ∀ key ∈ W.KB, ((W.coarseCandidates key).card : ℝ) ≤ C)
    (z3 z0 : ℤ) :
    ∃ G : Finset W.Coarse, (G.card : ℝ) ≤ 14 * W.cfg.K W.k * C ∧
      ∀ γ, W.chart γ = (z3, z0) → γ ∈ G := by
  obtain ⟨F, hF, hkeys⟩ := W.coarse_key_menu hB hK hN hχ hχm z3 z0
  let G : Finset W.Coarse := Finset.univ.filter fun γ => W.chart γ = (z3, z0)
  let T : Finset (Σ _y : ℤ, Fin (W.layers.np 0)) :=
    F.sigma fun y => W.coarseCandidates ![z3, z0, y]
  let f : W.Coarse → Σ _y : ℤ, Fin (W.layers.np 0) :=
    fun γ => ⟨W.key γ 2, W.coarseIndex γ⟩
  have hrepr : ∀ γ ∈ G, (![z3, z0, W.key γ 2] : Fin 3 → ℤ) = W.key γ := by
    intro γ hγ
    have hc := (Finset.mem_filter.mp hγ).2
    have h0 : W.key γ 0 = z3 := congrArg Prod.fst hc
    have h1 : W.key γ 1 = z0 := congrArg Prod.snd hc
    funext e
    fin_cases e <;> simp [h0, h1]
  have hmap : (G : Set W.Coarse).MapsTo f T := by
    intro γ hγ
    apply Finset.mem_sigma.mpr
    refine ⟨hkeys γ (Finset.mem_filter.mp hγ).2, ?_⟩
    change W.coarseIndex γ ∈ W.coarseCandidates ![z3, z0, W.key γ 2]
    rw [hrepr γ hγ]
    exact W.coarse_mem_candidates γ
  have hinj : (G : Set W.Coarse).InjOn f := by
    intro γ hγ γ' hγ' heq
    apply W.coarse_eq
    · rw [← hrepr γ hγ, ← hrepr γ' hγ']
      exact congrArg (fun y => ![z3, z0, y]) (congrArg Sigma.fst heq)
    · exact congrArg (fun x : Σ _y : ℤ, Fin (W.layers.np 0) => x.2) heq
  have hcard : (G.card : ℝ) ≤ T.card := by
    exact_mod_cast Finset.card_le_card_of_injOn f hmap hinj
  have hcand : ∀ key, ((W.coarseCandidates key).card : ℝ) ≤ C := by
    intro key
    by_cases hk : key ∈ W.KB
    · exact hcount key hk
    · simpa [coarseCandidates, hk] using hC
  have hT : (T.card : ℝ) ≤ (F.card : ℝ) * C := by
    simp only [T, Finset.card_sigma, Nat.cast_sum]
    calc (∑ y ∈ F, ((W.coarseCandidates ![z3, z0, y]).card : ℝ))
        ≤ ∑ _y ∈ F, C := Finset.sum_le_sum fun y _ => hcand _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨G, hcard.trans (hT.trans (mul_le_mul_of_nonneg_right hF hC)), ?_⟩
  intro γ hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
